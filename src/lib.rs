use rev_buf_reader::RevBufReader;
use std::fmt;
use std::{
    collections::{HashMap, HashSet},
    io::{self, BufRead, Lines, Read, Seek, Write},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum TrimmerError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Expected line to start with `{expected}`, got `{found}`")]
    UnexpectedLineStart { expected: String, found: String },

    #[error("Missing or malformed constraint ID in line: {0}")]
    MalformedConstraintId(String),

    #[error("Unknown rule encountered: {0}")]
    UnknownRule(String),

    #[error("Internal logic error: {0}")]
    Internal(String),

    #[error("Missing proof conclusion")]
    MissingConclusion,
}

#[derive(Default)]
pub struct TrimmerConfig {
    pub eager_deletion: bool,
    pub stats: bool,
}

#[derive(Default, Clone)]
pub struct ProofFileStats {
    pub total_lines: u64,
    pub pol_lines: u64,
    pub a_lines: u64,
    pub del_lines: u64,
    pub a_lines_by_name: HashMap<String, u64>,
}

static ALLOWED_RULES: [&str; 3] = ["a", "pol", "p"];

pub struct Trimmer<R, W> {
    marked_for_output: HashSet<String>,
    marked_for_deletion: HashSet<String>,
    lines: Lines<RevBufReader<R>>,
    out: W,
    config: TrimmerConfig,
    input_stats: ProofFileStats,
    output_stats: ProofFileStats,
}

impl<R: Read + Seek, W: Write> Trimmer<R, W> {
    pub fn new(input: R, out: W) -> Self {
        Self::with_config(input, out, TrimmerConfig::default())
    }

    pub fn with_config(input: R, out: W, config: TrimmerConfig) -> Self {
        let rev_reader = RevBufReader::new(input);
        Self {
            marked_for_output: HashSet::<String>::new(),
            marked_for_deletion: HashSet::<String>::new(),
            lines: rev_reader.lines(),
            out,
            config,
            input_stats: ProofFileStats::default(),
            output_stats: ProofFileStats::default(),
        }
    }

    pub fn trim(&mut self) -> Result<Option<(ProofFileStats, ProofFileStats)>, TrimmerError> {
        let mut current_line = self.next_line().unwrap().unwrap();

        if current_line.starts_with("end pseudo-Boolean") {
            // Write end pseudo-Boolean proof
            self.write_line(&current_line)?;

            // Write UNSAT conclusion
            current_line = self.next_line().unwrap().unwrap();
            self.assert_starts_with(&current_line, "conclusion UNSAT")?;
            self.write_line(&current_line)?;

            // Mark the contradicting constraint ID
            let contr_id = current_line
                .split(":")
                .nth(1)
                .unwrap()
                .split(";")
                .nth(0)
                .unwrap()
                .trim()
                .to_string();
            self.marked_for_output.insert(contr_id);

            // Write output (hopefully NONE)
            current_line = self.next_line().unwrap().unwrap();
            self.assert_starts_with(&current_line, "output")?;
            self.write_line(&current_line)?;
        } else {
            // Don't trim proofs that don't end (TODO?)
            return Err(TrimmerError::MissingConclusion);
        }

        while let Some(current_line) = self.next_line() {
            let current_line = current_line.unwrap();
            if current_line.starts_with("@") {
                let mut split_line = current_line.split(" ");
                let id = split_line.next().unwrap();
                if self.marked_for_output.contains(id) {
                    let rule = split_line.next().unwrap();
                    assert!(ALLOWED_RULES.contains(&rule));
                    if rule == "pol" || rule == "p" {
                        for term in split_line {
                            if term == "+" || term == "s" || term == ";" {
                                continue;
                            } else {
                                assert!(term.starts_with("@"), "{term:?}");
                                if !self.marked_for_output.contains(term) {
                                    if self.config.eager_deletion
                                        || self.marked_for_deletion.contains(term)
                                    {
                                        // We haven't marked this yet, so it's the last time
                                        // this ID is needed in the proof, hence delete it
                                        let _ = self.write_line(&format!("del id {term} ;"));
                                    }
                                    self.marked_for_output.insert(term.to_string());
                                }
                            }
                        }
                    }
                    // Write out the needed constraint
                    self.write_line(&current_line)?;
                } else {
                    // Not marked, ignore
                    continue;
                }
            } else if current_line.starts_with("f") || current_line.starts_with("pseudo-Boolean") {
                self.write_line(&current_line)?;
            } else if !self.config.eager_deletion && current_line.starts_with("del id") {
                let mut id = current_line.split(" ").nth(2).unwrap();
                id = if id.ends_with(";") {
                    &id[..id.len() - 2]
                } else {
                    id
                };
                // We will delete this if anyone uses it
                self.marked_for_deletion.insert(id.to_string());
            } else {
                // Something else ? Ignore ;-)
                continue;
            }
        }
        if self.config.stats {
            Ok(Some((self.input_stats.clone(), self.output_stats.clone())))
        } else {
            Ok(None)
        }
    }

    fn next_line(&mut self) -> Option<Result<String, io::Error>> {
        let line = self.lines.next();
        if self.config.stats {
            if let Some(line) = line.as_ref() {
                let line = line.as_ref().unwrap();
                self.input_stats.record_line(&line);
            }
        }
        line
    }

    fn write_line(&mut self, content: &str) -> io::Result<()> {
        if self.config.stats {
            self.output_stats.record_line(&content);
        }
        writeln!(self.out, "{content}")
    }

    fn assert_starts_with(&self, line: &String, pattern: &str) -> Result<(), TrimmerError> {
        if !line.starts_with(pattern) {
            return Err(TrimmerError::UnexpectedLineStart {
                expected: pattern.into(),
                found: line.clone(),
            });
        };
        Ok(())
    }
}

impl ProofFileStats {
    fn record_line(&mut self, line: &str) {
        self.total_lines += 1;
        let mut split_line = line.split(" ");
        let mut rule = split_line.next().unwrap();
        if rule.starts_with("@") {
            rule = split_line.next().unwrap()
        }
        match rule {
            "a" => self.record_assertion(line),
            "pol" | "p" => self.pol_lines += 1,
            "del" => self.del_lines += 1,
            _ => (),
        };
    }

    fn record_assertion(&mut self, line: &str) {
        self.a_lines += 1;
        let mut split_line = line.split(":");

        match split_line.nth(2) {
            Some(name) => {
                *self
                    .a_lines_by_name
                    .entry(name.trim().trim_matches(';').to_string())
                    .or_insert(0) += 1;
            }
            None => (),
        }
    }
}

impl fmt::Display for ProofFileStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Total lines: {}", self.total_lines)?;
        writeln!(f, "Assertion lines: {}", self.a_lines)?;
        writeln!(f, "Pol lines: {}", self.pol_lines)?;
        writeln!(f, "Del lines: {}", self.del_lines)?;
        writeln!(f, "Assertion lines by name:")?;
        for (name, count) in &self.a_lines_by_name {
            writeln!(f, " ∟ `{}`: {}", name, count)?;
        }
        Ok(())
    }
}

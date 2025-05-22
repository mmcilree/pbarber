use rev_buf_reader::RevBufReader;
use std::{
    collections::HashSet,
    io::{self, BufRead, Lines, Read, Seek, Write},
};

use crate::{
    ALLOWED_RULES, FORWARD_LIT_DEF_PREFIX, PBarberError, ProofFileStats, ProofProcessor,
    REVERSE_LIT_DEF_PREFIX, TrimmerConfig,
};

pub struct Trimmer<R: Read + Seek, W> {
    marked_for_output: HashSet<String>,
    marked_for_deletion: HashSet<String>,
    lits_seen: HashSet<String>,
    lines: Lines<RevBufReader<R>>,
    out: W,
    config: TrimmerConfig,
    input_stats: ProofFileStats,
    output_stats: ProofFileStats,
}

impl<R: Read + Seek, W: Write> ProofProcessor<W> for Trimmer<R, W> {
    fn lines_next(&mut self) -> Option<Result<String, io::Error>> {
        self.lines.next()
    }

    fn has_stats(&self) -> bool {
        self.config.stats
    }

    fn input_stats_mut(&mut self) -> &mut ProofFileStats {
        &mut self.input_stats
    }

    fn output_stats_mut(&mut self) -> &mut ProofFileStats {
        &mut self.output_stats
    }

    fn out_mut(&mut self) -> &mut W {
        &mut self.out
    }
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
            lits_seen: HashSet::<String>::new(),
            lines: rev_reader.lines(),
            out,
            config,
            input_stats: ProofFileStats::default(),
            output_stats: ProofFileStats::default(),
        }
    }

    pub fn trim(&mut self) -> Result<Option<(ProofFileStats, ProofFileStats)>, PBarberError> {
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
            return Err(PBarberError::MissingConclusion);
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
                                self.assert_starts_with(&term.to_string(), "@")?;
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
                    } else if self.config.lit_deletion && rule == "a" {
                        let split_line = current_line.split(" ");
                        for token in split_line {
                            if token == ">=" {
                                break;
                            }
                            let mut lit = token;

                            if lit.starts_with("~") {
                                lit = &lit[1..];
                            }
                            if !lit.starts_with("x") || self.lits_seen.contains(lit) {
                                continue;
                            }

                            self.lits_seen.insert(lit.to_string());
                            for prefix in [FORWARD_LIT_DEF_PREFIX, REVERSE_LIT_DEF_PREFIX] {
                                self.write_line(&format!("del id @{}{}", prefix, &lit))?;
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
}

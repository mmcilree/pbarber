pub mod justifier;
pub mod trimmer;

use clap::Args;
use std::fmt;
use std::io::Write;
use std::{collections::HashMap, io};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum PBarberError {
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

#[derive(Default, Args)]
pub struct TrimmerConfig {
    #[arg(
        short,
        long,
        help = "Add all possible deletions for logged constraints when trimming."
    )]
    pub eager_deletion: bool,

    #[arg(short, long, help = "Record and print trimming statistics.")]
    pub stats: bool,

    #[arg(
        short,
        long,
        help = "Add deletions for potential literal definitions at trimming phase."
    )]
    pub lit_deletion: bool,
}

#[derive(Default)]
pub struct JustifierConfig {
    pub read_forwards: bool,
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

pub struct ProofFileStatsComparison<'a> {
    current: &'a ProofFileStats,
    reference: &'a ProofFileStats,
}

pub trait ProofProcessor<W: Write> {
    fn lines_next(&mut self) -> Option<Result<String, io::Error>>;
    fn has_stats(&self) -> bool;
    fn input_stats_mut(&mut self) -> &mut ProofFileStats;
    fn output_stats_mut(&mut self) -> &mut ProofFileStats;
    fn out_mut(&mut self) -> &mut W;

    fn next_line(&mut self) -> Option<Result<String, io::Error>> {
        let line = self.lines_next();
        if self.has_stats() {
            if let Some(line) = line.as_ref() {
                let line = line.as_ref().unwrap();
                self.input_stats_mut().record_line(&line);
            }
        }
        line
    }

    fn write_line(&mut self, content: &str) -> io::Result<()> {
        if self.has_stats() {
            self.output_stats_mut().record_line(&content);
        }
        writeln!(self.out_mut(), "{}", content)
    }

    fn assert_starts_with(&self, line: &String, pattern: &str) -> Result<(), PBarberError> {
        if !line.starts_with(pattern) {
            return Err(PBarberError::UnexpectedLineStart {
                expected: pattern.into(),
                found: line.clone(),
            });
        };
        Ok(())
    }
}

static ALLOWED_RULES: [&str; 3] = ["a", "pol", "p"];
static FORWARD_LIT_DEF_PREFIX: &str = "lf";
static REVERSE_LIT_DEF_PREFIX: &str = "lr";

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

    pub fn compared_to<'a>(&'a self, other: &'a ProofFileStats) -> ProofFileStatsComparison<'a> {
        ProofFileStatsComparison {
            current: self,
            reference: other,
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

impl fmt::Display for ProofFileStatsComparison<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let percent = |current, reference| {
            if reference == 0 {
                return "N/A".to_string();
            }
            let change = 100.0 * (current as f64 - reference as f64) / reference as f64;
            if change == 0.0 {
                format!("No change")
            } else {
                format!("{}{:.1}%", if change >= 0.0 { "+" } else { "" }, change)
            }
        };

        writeln!(
            f,
            "Total lines: {} ({})",
            self.current.total_lines,
            percent(self.current.total_lines, self.reference.total_lines)
        )?;
        writeln!(
            f,
            "Assertion lines: {} ({})",
            self.current.a_lines,
            percent(self.current.a_lines, self.reference.a_lines)
        )?;
        writeln!(
            f,
            "Pol lines: {} ({})",
            self.current.pol_lines,
            percent(self.current.pol_lines, self.reference.pol_lines)
        )?;
        writeln!(
            f,
            "Del lines: {} ({})",
            self.current.del_lines,
            percent(self.current.del_lines, self.reference.del_lines)
        )?;

        writeln!(f, "Assertion lines by name:")?;
        for (name, count) in &self.current.a_lines_by_name {
            let ref_count = self
                .reference
                .a_lines_by_name
                .get(name)
                .copied()
                .unwrap_or(0);
            writeln!(
                f,
                " ∟ `{}`: {} ({})",
                name,
                count,
                percent(*count, ref_count)
            )?;
        }

        Ok(())
    }
}

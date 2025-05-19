use clap::{Args, Parser, Subcommand};
use colored::Colorize;
use pbarber::{ProofFileStats, Trimmer, TrimmerConfig, TrimmerError};
use rev_buf_reader::RevBufReader;
use std::fs::{File, rename};
use std::{fs::OpenOptions, io::BufRead, io::Write, path::PathBuf};

#[derive(Parser)]
#[command(
    name = "pbarber",
    about = "A tool for trimming and expanding ('styling') proof logs produced by a CP solver."
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Trim a proof log
    Trim {
        #[clap(flatten)]
        io: IOPaths,
        #[clap(flatten)]
        trimmer_config: TrimmerConfig,
    },

    /// (Default) Trim a proof log and justify assertions
    TrimAndStyle {
        #[clap(flatten)]
        io: IOPaths,
        #[clap(flatten)]
        trimmer_config: TrimmerConfig,
        // TODO: additional justifier options
    },

    /// Justify assertions only
    Style {
        #[clap(flatten)]
        io: IOPaths,
        // TODO: additional justifier options
    },

    /// Future concept: help tools for debugging a failing proof
    Advise {
        #[arg(value_name = "INPUT_FILE", help = "Input file.")]
        input_path: PathBuf,
    },
}

#[derive(Args)]
struct IOPaths {
    #[arg(value_name = "INPUT_FILE", help = "Input file.")]
    input_path: PathBuf,

    #[arg(
        value_name = "OUTPUT_FILE",
        help = "Optional output file. Defaults to <INPUT_FILE>.smol.pbp."
    )]
    output_path: Option<PathBuf>,
}

impl IOPaths {
    fn resolved_output_path(&self) -> PathBuf {
        self.output_path.clone().unwrap_or_else(|| {
            let mut path = self.input_path.clone();
            path.set_extension("smol.pbp");
            path
        })
    }
}

#[derive(Args)]
struct InputPathOnly {
    #[arg(value_name = "INPUT_FILE", help = "Input file.")]
    input_path: PathBuf,
}

fn main() -> Result<(), TrimmerError> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Trim { io, trimmer_config } => {
            let output_path = io.resolved_output_path();
            let (input_file, output_file) = open_files(&io.input_path, &output_path);
            let trimmer_config = if trimmer_config.lit_deletion {
                println!(
                    "Warning: ignoring `--lit-deletion` as it would produce invalid proofs without expanding assertions."
                );
                TrimmerConfig {
                    lit_deletion: false,
                    ..trimmer_config
                }
            } else {
                trimmer_config
            };
            let mut trimmer = Trimmer::with_config(input_file, output_file, trimmer_config);
            let trim_result = trimmer.trim()?;
            print_trim_result(
                io.input_path.to_str().unwrap(),
                output_path.to_str().unwrap(),
                trim_result,
            );
            reverse_file(output_path)?;
        }
        Commands::TrimAndStyle { io, trimmer_config } => {
            let output_path = io.resolved_output_path();
            let (input_file, output_file) = open_files(&io.input_path, &output_path);
            println!("`style` not yet implemented. Trimming only...");
            let mut trimmer = Trimmer::with_config(input_file, output_file, trimmer_config);
            let trim_result = trimmer.trim()?;
            print_trim_result(
                io.input_path.to_str().unwrap(),
                output_path.to_str().unwrap(),
                trim_result,
            );
        }
        Commands::Style { io: _ } => {
            // let output_path = io.resolved_output_path();
            // let (input_file, output_file) = open_files(&io.input_path, &output_path);
            println!("`style` not yet implemented.");
        }
        Commands::Advise { input_path: _ } => {
            // let input_file = OpenOptions::new()
            //     .read(true)
            //     .open(input_path)
            //     .expect("Failed to open input file.");

            println!("`advise` not yet implemented.");
        }
    }

    Ok(())
}

fn reverse_file(output_path: PathBuf) -> Result<(), TrimmerError> {
    let file_to_reverse = OpenOptions::new()
        .read(true)
        .open(&output_path)
        .expect("Failed to re-poen output file for reversal");
    let rev_reader = RevBufReader::new(file_to_reverse);

    // Open temporary file to write the reversed file into
    let temp_path = output_path.with_extension("tmp");
    let mut final_output_file = match OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(temp_path.as_path())
    {
        Ok(output_file) => output_file,
        Err(e) => {
            panic!("Failed to open temp file {}", e.to_string());
        }
    };

    //  Rewrite lines in correct order
    for line in rev_reader.lines() {
        writeln!(final_output_file, "{}", line.unwrap())?;
    }

    // Replace the output file with the reversed file
    rename(temp_path.as_path(), output_path)?;

    Ok(())
}
fn open_files(input_path: &PathBuf, output_path: &PathBuf) -> (File, File) {
    // Open input file and read from end
    let input_file = OpenOptions::new()
        .read(true)
        .open(&input_path)
        .expect("Failed to open input file.");

    // Open and truncate output file.
    let output_file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(output_path.as_path())
        .expect("Failed to open output file.");

    (input_file, output_file)
}

fn print_trim_result(
    input_path: &str,
    output_path: &str,
    trim_result: Option<(ProofFileStats, ProofFileStats)>,
) {
    if let Some(stats) = trim_result {
        println!("{}", format!("Input file ({}) stats:", input_path).yellow());
        println!("{}", stats.0);
        println!(
            "{}",
            format!("Output file ({}) stats:", output_path).yellow()
        );
        println!("{}", stats.1.compared_to(&stats.0));
    }
}

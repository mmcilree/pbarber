use clap::Parser;
use colored::Colorize;
use pbarber::{Trimmer, TrimmerConfig, TrimmerError};
use rev_buf_reader::RevBufReader;
use std::fs::rename;
use std::{fs::OpenOptions, io::BufRead, io::Write, path::PathBuf};

#[derive(Parser)]
struct Cli {
    input_path: PathBuf,
    #[arg(value_name = "FILE")]
    output_path: Option<PathBuf>,
    #[arg(short, long)]
    eager_deletion: bool,
    #[arg(short, long)]
    stats: bool,
}

fn main() -> Result<(), TrimmerError> {
    let args = Cli::parse();

    let output_path = args.output_path.unwrap_or_else(|| {
        let mut output_path = args.input_path.clone();
        output_path.set_extension("smol.pbp");
        output_path
    });
    // Open input file and read from end
    let input_file = OpenOptions::new()
        .read(true)
        .open(&args.input_path)
        .expect("Failed to open input file.");

    // Open and truncate output file.
    let output_file = match OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(output_path.as_path())
    {
        Ok(output_file) => output_file,
        Err(e) => {
            panic!("Failed to open output file {}", e.to_string());
        }
    };

    let trimmer_config = TrimmerConfig {
        eager_deletion: args.eager_deletion,
        stats: args.stats,
    };

    let mut trimmer = Trimmer::with_config(input_file, output_file, trimmer_config);
    let trim_result = trimmer.trim()?;
    if let Some(stats) = trim_result {
        println!(
            "{}",
            format!("Input file ({}) stats:", args.input_path.to_str().unwrap(),).yellow()
        );
        println!("{}", stats.0);
        println!(
            "{}",
            format!("Output file ({}) stats:", output_path.to_str().unwrap(),).yellow()
        );
        println!("{}", stats.1);
    }
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

use clap::Parser;
use rev_buf_reader::RevBufReader;
use std::collections::HashSet;
use std::fs::rename;
use std::{fs::OpenOptions, io::BufRead, io::Write, path::PathBuf};

#[derive(Parser)]
struct Cli {
    input_path: PathBuf,
}
fn main() -> std::io::Result<()> {
    let args = Cli::parse();

    let mut output_path = args.input_path.clone();
    let _ = output_path.set_extension("smol.pbp");

    // Open input file and read from end
    let input_file = OpenOptions::new()
        .read(true)
        .open(&args.input_path)
        .expect("Failed to open input file.");
    let rev_reader = RevBufReader::new(input_file);

    // Open and truncate output file.
    let mut output_file = match OpenOptions::new()
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

    let mut marked = HashSet::new();
    let mut lines = rev_reader.lines();

    let mut current_line = lines.next().unwrap().unwrap();

    if current_line.starts_with("end pseudo-Boolean") {
        // Write end pseudo-Boolean proof
        writeln!(output_file, "{current_line}")?;

        // Write UNSAT conclusion
        current_line = lines.next().unwrap().unwrap();
        assert!(&current_line.starts_with("conclusion UNSAT"));
        writeln!(output_file, "{current_line}")?;

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
        marked.insert(contr_id);

        // Write output (hopefully NONE)
        current_line = lines.next().unwrap().unwrap();
        assert!(current_line.starts_with("output"));
        writeln!(output_file, "{}", &current_line)?;
    } else {
        // Triming from last constraint: write it out and mark it
        assert!(current_line.starts_with("@"));
        writeln!(output_file, "{current_line}")?;
        let last_id = current_line.split(" ").nth(0).unwrap().trim().to_string();
        marked.insert(last_id);
    }

    let allowed_rules: [&str; 3] = ["a", "pol", "p"];

    while let Some(current_line) = lines.next() {
        let current_line = current_line.unwrap();
        if current_line.starts_with("@") {
            let mut split_line = current_line.split(" ");
            let id = split_line.next().unwrap();
            if marked.contains(id) {
                // We need to keep this constraint
                let rule = split_line.next().unwrap();
                assert!(allowed_rules.contains(&rule));
                if rule == "pol" || rule == "p" {
                    for term in split_line {
                        if term == "+" || term == "s" || term == ";" {
                            continue;
                        } else {
                            assert!(term.starts_with("@"), "{term:?}");
                            if !marked.contains(term) {
                                // We haven't marked this yet, so it's the last time
                                // this ID is needed in the proof, hence delete it
                                let _ = writeln!(output_file, "del id {term} ;");
                                marked.insert(term.to_string());
                            }
                        }
                    }
                }
                // Write out the needed constraint
                writeln!(output_file, "{current_line}")?;
            } else {
                // Not marked, ignore
                continue;
            }
        } else if current_line.starts_with("f") || current_line.starts_with("pseudo-Boolean") {
            writeln!(output_file, "{current_line}")?;
        } else {
            // Some other kind of rule/comment, ignore :D
            continue;
        }
    }

    let file_to_reverse = OpenOptions::new()
        .read(true)
        .open(&output_path)
        .expect("Failed to repoen output file for reversal");
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

//! Filter program that converts UUID strings to Uuid25 (and vice versa)

use std::{env, io, io::Write, process::ExitCode};
use uuid25::Uuid25;

fn main() -> io::Result<ExitCode> {
    let format = {
        let mut args = env::args();
        let program = args.next().unwrap_or_else(|| "uuid25-filter".to_owned());
        match parse_args(args) {
            Ok(opt) => opt.unwrap_or(Format::Uuid25),
            Err(message) => {
                eprintln!("Error: {}", message);
                eprintln!(
                    "Usage: {} [--to uuid25|hex|hyphenated|braced|urn] [< lines-of-uuid-strings]",
                    program
                );
                return Ok(ExitCode::FAILURE);
            }
        }
    };

    let mut exit_code = ExitCode::SUCCESS;

    let mut line_no = 0usize;
    let mut buffer = String::with_capacity(64);
    let mut stdout = io::BufWriter::new(io::stdout());
    while {
        line_no += 1;
        buffer.clear();
        io::stdin().read_line(&mut buffer)? > 0
    } {
        let trimmed = buffer.trim();
        let Ok(x) = trimmed.parse::<Uuid25>() else {
            exit_code = ExitCode::FAILURE;
            eprintln!("Error: could not parse line {}: {}", line_no, trimmed);
            continue;
        };

        match format {
            Format::Uuid25 => stdout.write_all(x.as_bytes())?,
            Format::Hex => stdout.write_all(x.to_hex().as_bytes())?,
            Format::Hyphenated => stdout.write_all(x.to_hyphenated().as_bytes())?,
            Format::Braced => stdout.write_all(x.to_braced().as_bytes())?,
            Format::Urn => stdout.write_all(x.to_urn().as_bytes())?,
        };
        stdout.write_all(b"\n")?;
    }

    Ok(exit_code)
}

#[derive(Debug)]
enum Format {
    Uuid25,
    Hex,
    Hyphenated,
    Braced,
    Urn,
}

impl Format {
    fn from_arg(arg: &str) -> Result<Self, ()> {
        match arg {
            "uuid25" => Ok(Format::Uuid25),
            "hex" => Ok(Format::Hex),
            "hyphenated" => Ok(Format::Hyphenated),
            "braced" => Ok(Format::Braced),
            "urn" => Ok(Format::Urn),
            _ => Err(()),
        }
    }
}

fn parse_args(mut args: impl Iterator<Item = String>) -> Result<Option<Format>, String> {
    let mut format = None;
    while let Some(arg) = args.next() {
        if arg != "--to" {
            return Err(format!("unrecognized argument '{}'", arg));
        }
        if format.is_some() {
            return Err("option 'to' given more than once".to_owned());
        }
        let Some(to_arg) = args.next() else {
            return Err("argument to option 'to' missing".to_owned());
        };
        let Ok(f) = Format::from_arg(&to_arg) else {
            return Err(format!("invalid argument to option 'to': '{}'", to_arg));
        };
        format.replace(f);
    }
    Ok(format)
}

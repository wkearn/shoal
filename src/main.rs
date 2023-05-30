use clap::Parser;
use shoal;

#[derive(Parser, Debug)]
struct Args {
    path: std::path::PathBuf,
}

fn main() -> Result<(), shoal::error::Error> {
    let args = Args::parse();
    let source = std::fs::read_to_string(args.path)?;
    shoal::run(&source)
}

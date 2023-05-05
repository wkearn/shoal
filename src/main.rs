use clap::Parser;
use sisal;

#[derive(Parser, Debug)]
struct Args {
    path: std::path::PathBuf,
}

fn main() -> Result<(), sisal::error::Error> {
    //let args = Args::parse();
    //let source = std::fs::read_to_string(args.path)?;
    sisal::run()
}

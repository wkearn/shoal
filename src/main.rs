use clap::Parser;
use shoal;

#[derive(Parser, Debug)]
struct Args {
    path: Option<std::path::PathBuf>,
}

fn main() -> Result<(), shoal::error::Error> {
    let args = Args::parse();
    match args.path {
	Some(path) => {
	    let source = std::fs::read_to_string(path)?;
	    shoal::run(&source)
	}
	None => {
	    shoal::repl()
	}
    }
}

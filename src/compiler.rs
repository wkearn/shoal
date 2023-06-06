pub mod alphatize;
pub mod anormalizer;

use crate::error::Error;
use crate::parser::Program;

pub fn compile<T>(_: &Program<T>) -> Result<Program<T>, Error> {
    // Type inference and annotation

    // Overloading resolution

    // Alpha renaming

    // A-normalization
    
    Err(Error::CompileError(
        "Compiler pass not yet implemented".into(),
    ))
}

pub mod stats;

pub mod terms;

pub mod statements;

pub mod flatzinc;

pub mod writer;

use std::io;

use thiserror::Error;

#[derive(Debug, Error)]

pub enum PBarberError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Unsupported error: `{0}` not yet supported.")]
    Unsupported(String),

    #[error("Unexpected error: `{0}`.")]
    Unexpected(String),

    #[error("FlatZinc read error: expected `{expected}`, got `{found}`")]
    FlatZinc { expected: String, found: String },

    #[error("Parse error: expected `{expected}`, got `{found}`")]
    Parse { expected: String, found: String },
}

pub type Result<T> = std::result::Result<T, PBarberError>;

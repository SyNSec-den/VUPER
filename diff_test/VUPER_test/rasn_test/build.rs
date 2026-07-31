// build.rs build script
use std::path::PathBuf;
use rasn_compiler::prelude::*;

// Initialize the compiler with the rust/rasn backend.
fn main() {
    match Compiler::<RasnBackend, _>::new()
        // add a single ASN1 source file
        .add_asn_by_path(PathBuf::from("./test.asn1"))
        // set an output path for the generated rust code
        .set_output_path(PathBuf::from("./src/foo.rs"))
        .compile() {
        Ok(warnings) => {
            if !warnings.is_empty() {
                println!("cargo:warning=ASN.1 compilation completed with {} warning(s):", warnings.len());
                for warning in warnings {
                    println!("cargo:warning={}", warning);
                }
            } else {
                println!("cargo:warning=ASN.1 compilation completed successfully");
            }
        }
        Err(error) => {
            eprintln!("ASN.1 compilation failed: {}", error);
            std::process::exit(1);
        }
    }
}
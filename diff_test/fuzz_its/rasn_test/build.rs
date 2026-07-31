use std::path::PathBuf;
use rasn_compiler::prelude::*;

fn main() {
    match Compiler::<RasnBackend, _>::new()
        .add_asn_by_path(PathBuf::from("/fuzz_its/ESTI_ITS.asn1"))
        .set_output_path(PathBuf::from("./src/its.rs"))
        .compile()
    {
        Ok(warnings) => {
            for w in &warnings {
                println!("cargo:warning={}", w);
            }
        }
        Err(e) => {
            eprintln!("ASN.1 compilation failed: {}", e);
            std::process::exit(1);
        }
    }
}

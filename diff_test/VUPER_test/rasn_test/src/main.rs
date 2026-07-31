use std::io::{self, Read};

mod foo;
use foo::foo::S1;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Read input from stdin
    let mut buffer = Vec::new();
    io::stdin().read_to_end(&mut buffer)?;
    
    // Decode from UPER
    let decoded: S1 = rasn::uper::decode(&buffer)?;
    // println!("Decoded: {:?}", decoded);
    
    // Encode to JER
    let jer_encoded = rasn::jer::encode(&decoded)?;
    
    // println!("JER encoded:");
    println!("{}", jer_encoded);
    
    Ok(())
}

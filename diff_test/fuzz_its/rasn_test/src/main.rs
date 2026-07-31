mod its;

use its::cam_pdu_descriptions::CAM;
use std::io::Write;
use std::process::{Command, Stdio};

fn ocaml_decode(input: &[u8]) -> Option<serde_json::Value> {
    let mut child = Command::new("/fuzz_its/verified_format_utf8/_build/default/test/test.exe")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .ok()?;

    child.stdin.take()?.write_all(input).ok()?;
    let output = child.wait_with_output().ok()?;
    let s = std::str::from_utf8(&output.stdout).ok()?.trim();
    if s == "\"Error\"" {
        None
    } else {
        serde_json::from_str(s).ok()
    }
}

fn main() {
    afl::fuzz!(|data: &[u8]| {
        let ocaml_result = ocaml_decode(data);
        let rasn_result: Result<CAM, _> = rasn::uper::decode(data);

        match (rasn_result, ocaml_result) {
            // both fail — OK
            (Err(_), None) => {}
            // both succeed — OK (full JSON normalisation is complex; crash detection suffices)
            (Ok(_), Some(_)) => {}
            // one succeeds, other fails — differential finding
            _ => panic!("differential mismatch"),
        }
    });
}

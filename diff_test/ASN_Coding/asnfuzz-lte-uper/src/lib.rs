
#![allow(non_camel_case_types)]

mod lte; // generated module

use std::slice;
use std::os::raw::c_char;
use asnfuzzgen_codecs::uper::UperCodec;
use entropic::prelude::*;

/// An invalid argument was supplied to the function.
const ASNFUZZGEN_ERR_ARGS: isize = -1;

/// Structuring failed due to insufficent bytes.
const ASNFUZZGEN_ERR_ENTROPIC: isize = -2;

/// Failed to convert bytes to or from ASN.1 wire format.
const ASNFUZZGEN_ERR_ENCODING: isize = -3;

/// The resulting bytes could not fit within the provided buffer.
const ASNFUZZGEN_ERR_TRUNCATED: isize = -4;

#[no_mangle]
pub unsafe extern "C" fn uper_lte_structure(buf_in: *mut c_char, in_len: isize, buf_out: *mut c_char, out_max: isize) -> isize {
    let in_len: usize = match in_len.try_into() {
        Ok(l) => l,
        Err(_) => return ASNFUZZGEN_ERR_ARGS,
    };

    let out_max: usize = match out_max.try_into() {
        Ok(l) => l,
        Err(_) => return ASNFUZZGEN_ERR_ARGS,
    };

    let in_slice = slice::from_raw_parts(buf_in as *const u8, in_len);
    let out_slice = slice::from_raw_parts_mut(buf_out as *mut u8, out_max);

    let in_iter = in_slice.iter().chain(std::iter::repeat(&0u8).take(200_000 - in_slice.len())); // Cap total entropy to 200,000 bytes for performance

    let Ok(message) = lte::DL_DCCH_Message::from_entropy::<_, entropic::scheme::DefaultEntropyScheme>(in_iter) else {
        return ASNFUZZGEN_ERR_ENTROPIC
    };

    let mut encoded = asnfuzzgen_codecs::PerCodecData::new_uper();
    match message.uper_encode(&mut encoded) {
        Ok(()) => (),
        _ => return ASNFUZZGEN_ERR_ENCODING // If the encoding isn't successful, short-circuit this test
    }

    let output_bytes = encoded.into_bytes();
    let output_slice = output_bytes.as_slice();
    if output_slice.len() > out_max {
        return ASNFUZZGEN_ERR_TRUNCATED
    }

    out_slice[..output_slice.len()].copy_from_slice(output_slice);

    match output_slice.len().try_into() {
        Ok(l) => l,
        Err(_) => ASNFUZZGEN_ERR_TRUNCATED
    }
}

#[no_mangle]
pub unsafe extern "C" fn uper_lte_destructure(buf_in: *mut c_char, in_len: isize, buf_out: *mut c_char, out_max: isize) -> isize {
    let in_len: usize = match in_len.try_into() {
        Ok(l) => l,
        Err(_) => return ASNFUZZGEN_ERR_ARGS,
    };

    let out_max: usize = match out_max.try_into() {
        Ok(l) => l,
        Err(_) => return ASNFUZZGEN_ERR_ARGS,
    };

    let in_slice = slice::from_raw_parts(buf_in as *const u8, in_len);
    let out_slice = slice::from_raw_parts_mut(buf_out as *mut u8, out_max);

    let mut packet = asnfuzzgen_codecs::PerCodecData::from_slice_uper(in_slice);
    let Ok(pdu) = lte::DL_DCCH_Message::uper_decode(&mut packet) else {
        return ASNFUZZGEN_ERR_ENCODING
    };

    let mut output = [0u8; 2_000_000];

    let Ok(output_len) = pdu.to_entropy::<_, DefaultEntropyScheme>(&mut output) else {
        return ASNFUZZGEN_ERR_ENTROPIC
    };
    
    let output_slice = &output[..output_len];
    if output_slice.len() > out_max {
        return ASNFUZZGEN_ERR_TRUNCATED
    }

    out_slice[..output_slice.len()].copy_from_slice(output_slice);

    match output_slice.len().try_into() {
        Ok(l) => l,
        Err(_) => ASNFUZZGEN_ERR_TRUNCATED
    }
}

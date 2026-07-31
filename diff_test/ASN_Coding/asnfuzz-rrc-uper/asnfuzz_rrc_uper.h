
#ifndef ASNFUZZ_RRC_UPER_H
#define ASNFUZZ_RRC_UPER_H

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/// An invalid argument was supplied to the function.
const long ASNFUZZGEN_ERR_ARGS = -1;

/// Structuring failed due to insufficent bytes.
const long ASNFUZZGEN_ERR_ENTROPIC = -2;

/// Failed to convert bytes to or from ASN.1 wire format.
const long ASNFUZZGEN_ERR_ENCODING = -3;

/// The resulting bytes could not fit within the provided buffer.
const long ASNFUZZGEN_ERR_TRUNCATED = -4;

/// Converts unstructured bytes into a structured ASN.1 message.
/// Returns a the length of the structured bytes written to `buf_out`, or
/// a negative error code on failure.
long uper_rrc_structure(char *buf_in, long in_len, char *buf_out, long out_max);

/// Converts a structured ASN.1 message into unstructured bytes.
/// Returns a the length of the unstructured bytes written to `buf_out`, or
/// a negative error code on failure.
long uper_rrc_destructure(char *buf_in, long in_len, char *buf_out, long out_max);

#ifdef __cplusplus
}
#endif // __cplusplus

#endif // ASNFUZZ_RRC_UPER_H

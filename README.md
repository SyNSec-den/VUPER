# VUPER — Verified ASN.1 UPER Parser

VUPER is a formally verified parser for ASN.1 **Unaligned Packed Encoding Rules** (UPER), the
encoding used by 3GPP for 5G NR-RRC and LTE signalling and by ETSI for ITS messages. The parser
and its correctness proofs are written in Coq, extracted to OCaml, and then differentially tested
against the ASN.1 decoders that real deployments rely on.

This repository holds the two halves of the paper's artifact:

| Directory | What it is |
| --- | --- |
| [`parser_artifact/`](parser_artifact/) | The main contribution: the verified parser library, the ASN.1-to-Coq compiler, and the supporting OCaml code. |
| [`diff_test/`](diff_test/) | The differential testing campaign: AFL++ harnesses that cross-check third-party ASN.1 decoders against the verified reference. |

Each directory has its own README with full detail. Start here for orientation and the fastest
path to a working setup.

---

## Part 1 — The verified parser

See **[`parser_artifact/README.md`](parser_artifact/README.md)** for the formal development: the
format combinators, the array/bitstream abstraction, the compiler from ASN.1 definitions to Coq,
and the extraction to OCaml.

Requires **Coq 8.20** and **OCaml 4.14**. The exact opam environment is pinned in the repository:

```bash
cd parser_artifact
opam switch import vuper_env.export
cd Compile && dune build
```

Checking the proofs and regenerating the Coq sources from a 3GPP ASN.1 module is covered
step-by-step in that README.

---

## Part 2 — Differential testing

See **[`diff_test/README.md`](diff_test/README.md)** for the full fuzzing guide.

Every harness follows the same shape: AFL++ supplies a UPER-encoded blob, a third-party decoder
parses it, the verified OCaml decoder parses the same bytes, and the harness aborts — which AFL
records as a crash — whenever the two disagree about whether the input is valid.

Everything runs inside one Docker image:

```bash
cd diff_test
docker build -t afl_ocaml_c_fuzz .

docker run -d --name asn1_fuzz_work \
  -v $(pwd)/fuzz:/fuzz \
  -v $(pwd)/fuzz_its:/fuzz_its \
  -v $(pwd)/fuzz_lte:/fuzz_lte \
  -v $(pwd)/VUPER_test:/VUPER_test \
  afl_ocaml_c_fuzz tail -f /dev/null

docker exec -it asn1_fuzz_work bash
```

The image ships AFL++, an OCaml 4.14 opam switch, pycrate, asn1tools, `cargo-afl`, and both
ASNFuzzGen structure-aware mutators pre-built. It does **not** ship the compiled reference
decoders or harnesses — those live on the mounted volumes and are built once inside the container.
Follow the prerequisites section of the `diff_test` README before running any fuzzer.

### Targets under test

| Protocol | Message | Decoders cross-checked |
| --- | --- | --- |
| 5G NR-RRC (Rel 16.3.1) | `DL-DCCH-Message`, `UL-DCCH-Message` | asn1c, pycrate, srsRAN |
| LTE EUTRA-RRC (TS 36.331) | `DL-DCCH-Message` | asn1c, pycrate, srsRAN 4G |
| ETSI ITS (EN 302 637-2) | `CAM` | asn1c, pycrate, asn1tools, rasn, TITAN |

---

## Status

Ten of the eleven harnesses have been built and run end-to-end from a clean image; each agrees
with the verified reference on its seed inputs. Both ASNFuzzGen mutators load and drive AFL++.

| Harness | Status |
| --- | --- |
| 5G asn1c / pycrate / srsRAN | working |
| LTE asn1c / pycrate / srsRAN 4G | working |
| ITS asn1c / pycrate / asn1tools / rasn | working |
| ITS TITAN | **not buildable — see below** |

### Known limitations

**ITS TITAN cannot be built from this repository.** The harness sources in
`diff_test/fuzz_its/titan_asn1/test_its/` are present, but the TITAN runtime SDK that provides
`TTCN3.hh` is not redistributed here, so the build fails with `fatal error: 'TTCN3.hh' file not
found`. Install the TITAN SDK separately to use this harness.

**The ITS and LTE `asn1c` harnesses are compiled with AddressSanitizer** (`-fsanitize=address` in
their Makefiles; the 5G harness has it commented out). On Linux 6.x kernels, ASan's shadow-memory
mapping intermittently fails at process startup because of the increased ASLR entropy, producing a
SIGSEGV *before `main` runs*. AFL++ records those as crashes, so a fraction of reported findings
from these two harnesses can be startup noise rather than genuine decoder disagreements. Mitigate
by disabling ASLR for the target — run the container with `--security-opt seccomp=unconfined` and
launch through `setarch $(uname -m) -R` — or by lowering `vm.mmap_rnd_bits` to `28` on the host.

**Reference decoders are not pre-compiled.** A harness whose reference binary is missing does not
fail cleanly. The `rasn` harness in particular treats a failed subprocess spawn exactly like a
decoder rejection and will report `differential mismatch` on entirely valid input. Build all six
reference decoders first, as described in the `diff_test` README.

---

## Repository size

The tree is large (~235 MB) because it vendors the third-party decoders under test and the
asn1c-generated C sources for the full 3GPP schemas. Build outputs — `_build/`, `target/`, CMake
directories, AFL `output_dir/` findings — are excluded by `diff_test/.gitignore` and should never
be committed.

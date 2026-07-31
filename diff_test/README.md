# ASN.1 Fuzzing Docker

Differential fuzzing framework for ASN.1 parsers used in 5G (NR-RRC) and ITS (ETSI CAM) message decoding.
The fuzzer cross-checks multiple parser implementations against a verified OCaml reference decoder;
a crash is logged whenever two implementations disagree on the same input.

## Architecture

Each fuzzer harness follows the same pattern:
1. AFL++ provides a UPER-encoded binary blob via stdin.
2. The target parser decodes it (asn1c, pycrate, srsRAN, etc.).
3. A verified OCaml reference decoder also decodes the same input.
4. If both parsers agree (both succeed or both fail), execution continues.
5. If they disagree, the harness calls `abort()` — AFL records it as a crash.

---

## Docker Setup

The Docker image `afl_ocaml_c_fuzz` contains AFL++, an OCaml 4.14 opam switch (`vuper`), pycrate,
asn1tools, `cargo-afl`, and both pre-built ASNFuzzGen mutators.

### Start the container

Run as a long-lived container so you can exec into it repeatedly:

```bash
docker run -d \
  --name asn1_fuzz_work \
  -v $(pwd)/fuzz:/fuzz \
  -v $(pwd)/fuzz_its:/fuzz_its \
  -v $(pwd)/fuzz_lte:/fuzz_lte \
  -v $(pwd)/VUPER_test:/VUPER_test \
  afl_ocaml_c_fuzz \
  tail -f /dev/null
```

Then open a shell inside it:

```bash
docker exec -it asn1_fuzz_work bash
```

To stop and remove the container when done:

```bash
docker stop asn1_fuzz_work && docker rm asn1_fuzz_work
```

### Rebuild the image from scratch

```bash
docker build -t afl_ocaml_c_fuzz .
```

---

## Prerequisites — build the OCaml reference decoders (one-time, in container)

**Every** fuzzer compares its target parser against a verified OCaml reference decoder, and
**none** of these are pre-compiled in the image — they live on the mounted volumes, so they must
be built once after starting the container. A harness whose reference is missing does not fail
cleanly: the `rasn` harness in particular reports a spurious `differential mismatch` on perfectly
valid input, because a failed subprocess spawn is indistinguishable from a decoder rejection.

```bash
docker exec -it asn1_fuzz_work bash

for d in /fuzz/ocaml_test \
         /fuzz/ocaml_test_ul_srs \
         /fuzz/pycrate_dir/ocaml_test \
         /fuzz_its/verified_format \
         /fuzz_its/verified_format_utf8 \
         /fuzz_lte/verified_format ; do
    ( cd "$d" && dune build ) || echo "FAILED: $d"
done
```

| Directory | Used by |
| --- | --- |
| `/fuzz/ocaml_test` | 5G asn1c (DL-DCCH) |
| `/fuzz/ocaml_test_ul_srs` | 5G srsRAN (UL-DCCH) |
| `/fuzz/pycrate_dir/ocaml_test` | 5G pycrate — a *separate* decoder variant, resolved as `./../ocaml_test` relative to `/fuzz/pycrate_dir/pycrate_test`; not the same tree as `/fuzz/ocaml_test` |
| `/fuzz_its/verified_format` | ITS asn1c, ITS TITAN |
| `/fuzz_its/verified_format_utf8` | ITS pycrate, ITS asn1tools, ITS RASN |
| `/fuzz_lte/verified_format` | LTE asn1c, LTE pycrate, LTE srsRAN 4G |

> **Note:** these builds need OCaml **4.14** (`verified_format_utf8` uses `String.is_valid_utf_8`)
> and an unlimited stack (the generated NR/EUTRA format modules overflow the default 8 MB stack
> when compiled to native code). The image's `vuper` opam switch and the `ulimit -s unlimited` in
> `/root/.bashrc` handle both, so no manual `export PATH` or `ulimit` is needed — but if you invoke
> `dune` from a shell that does not source `/root/.bashrc`, set `ulimit -s unlimited` yourself.

---

## ASNFuzzGen Custom Mutator

Both the 5G and LTE fuzzers can use **ASNFuzzGen** as an AFL++ custom mutator for
structure-aware fuzzing. The mutator works by:
1. **Destructuring** the current input from UPER wire bytes into unstructured bytes.
2. **Mutating** those bytes with Radamsa (a general-purpose byte mutator).
3. **Restructuring** the mutated bytes back into a valid UPER-encoded ASN.1 message.

This produces mutations that are structurally valid ASN.1 messages rather than random
byte sequences, which significantly improves coverage compared to plain AFL mutations.

The pre-built `.so` libraries are baked into the image at:
- **5G NR**: `/AFLplusplus/custom_mutators/asnfuzz-rrc-uper/libasnfuzz_rrc_uper.so`
- **LTE**: `/AFLplusplus/custom_mutators/asnfuzz-lte-uper/libasnfuzz_lte_uper.so`

To use them, set `AFL_CUSTOM_MUTATOR_LIBRARY` before running `afl-fuzz`:

```bash
# 5G NR example
AFL_CUSTOM_MUTATOR_LIBRARY=/AFLplusplus/custom_mutators/asnfuzz-rrc-uper/libasnfuzz_rrc_uper.so \
afl-fuzz -i /fuzz/input_dir -o /fuzz/output_dir/asn1c \
         -- /fuzz/asn1c_test/main-test

# LTE example
AFL_CUSTOM_MUTATOR_LIBRARY=/AFLplusplus/custom_mutators/asnfuzz-lte-uper/libasnfuzz_lte_uper.so \
afl-fuzz -i /fuzz_lte/input_dir -o /fuzz_lte/output_dir/asn1c \
         -- /fuzz_lte/asn1c_test/main-test
```

The custom mutator works with any of the fuzzers below (asn1c, pycrate, srsRAN) — just prepend
the environment variable to the `afl-fuzz` or `py-afl-fuzz` command.

### Building ASNFuzzGen from Source

> **Note:** Nothing needs to be pre-built on the host. The Dockerfile `COPY`s the whole
> `ASN_Coding/` tree into the image and builds both mutators there, using the Rust toolchain
> that already ships in the `aflplusplus` base image. No `.a` files are committed.

`ASN_Coding/` contains three crates:

| Path | Role |
| --- | --- |
| `asnfuzzgen/` | The ASNFuzzGen codecs library (`codecs` + `codecs_derive`). Both mutators depend on it by relative path, so it **must** be present for the image to build. |
| `asnfuzz-rrc-uper/` | 5G NR mutator. `src/rrc.rs` is the generated 3GPP NR-RRC schema. |
| `asnfuzz-lte-uper/` | LTE mutator. `src/lte.rs` is the generated EUTRA-RRC schema. |

To rebuild after changing any of them, just rebuild the image:

```bash
docker build -t afl_ocaml_c_fuzz .
```

The Dockerfile runs, for each crate:

```bash
cargo build --release   # produces target/release/libasnfuzz_<rrc|lte>_uper.a
make mutator            # links the .a + libradamsa.a into libasnfuzz_<rrc|lte>_uper.so
```

The two Rust builds take roughly 40 s and 50 s respectively, and are cached by Docker as long as
`ASN_Coding/` is unchanged.

#### Updating only `asn_mutator.c` (without rebuilding Rust)

If you only changed the C wrapper, copy it into the running container and relink:

```bash
# From the project root on the host:
docker cp ASN_Coding/asnfuzz-rrc-uper/asn_mutator.c \
    asn1_fuzz_work:/AFLplusplus/custom_mutators/asnfuzz-rrc-uper/asn_mutator.c
docker cp ASN_Coding/asnfuzz-lte-uper/asn_mutator.c \
    asn1_fuzz_work:/AFLplusplus/custom_mutators/asnfuzz-lte-uper/asn_mutator.c
```

Then inside the container, relink the `.so`:

```bash
# 5G NR
gcc -Wall -O2 -funroll-loops -shared \
    /AFLplusplus/custom_mutators/asnfuzz-rrc-uper/asn_mutator.c \
    /AFLplusplus/custom_mutators/asnfuzz-rrc-uper/target/release/libasnfuzz_rrc_uper.a \
    /AFLplusplus/custom_mutators/radamsa/libradamsa.a \
    -fPIC -I/AFLplusplus/include \
    -I/AFLplusplus/custom_mutators/asnfuzz-rrc-uper \
    -I/AFLplusplus/custom_mutators/radamsa \
    -ldl -lpthread \
    -o /AFLplusplus/custom_mutators/asnfuzz-rrc-uper/libasnfuzz_rrc_uper.so

# LTE
gcc -Wall -O2 -funroll-loops -shared \
    /AFLplusplus/custom_mutators/asnfuzz-lte-uper/asn_mutator.c \
    /AFLplusplus/custom_mutators/asnfuzz-lte-uper/target/release/libasnfuzz_lte_uper.a \
    /AFLplusplus/custom_mutators/radamsa/libradamsa.a \
    -fPIC -I/AFLplusplus/include \
    -I/AFLplusplus/custom_mutators/asnfuzz-lte-uper \
    -I/AFLplusplus/custom_mutators/radamsa \
    -ldl -lpthread \
    -o /AFLplusplus/custom_mutators/asnfuzz-lte-uper/libasnfuzz_lte_uper.so
```

---

## 5G (NR-RRC) Fuzzers

All 5G fuzzers operate on `DL-DCCH-Message` (downlink) from 3GPP Release 16.3.1.
Seed inputs live in `/fuzz/input_dir/` (25 DL-DCCH binary seeds).

### 1. asn1c_test

**Source:** `/fuzz/asn1c_test/`

The C code was auto-generated from `nr.asn1` using asn1c with UPER-only flags. The harness in
`main.c` decodes the input with `asn_DEF_DL_DCCH_Message`, then compares the JER output against
`/fuzz/ocaml_test/_build/default/test/test.exe`.

#### Compile

```bash
docker exec -it asn1_fuzz_work bash
cd /fuzz/asn1c_test
make -j$(nproc)
```

This produces `/fuzz/asn1c_test/main-test`, compiled with `afl-clang-fast`.

To regenerate the C sources from scratch (not needed if already present):

```bash
asn1c -pdu=all -fcompound-names -gen-UPER \
      -no-gen-BER -no-gen-XER -no-gen-OER -no-gen-APER \
      -no-gen-example -findirect-choice nr.asn1
```

#### Run the fuzzer

```bash
mkdir -p /fuzz/output_dir/asn1c
afl-fuzz -i /fuzz/input_dir -o /fuzz/output_dir/asn1c \
         -- /fuzz/asn1c_test/main-test
```

With ASNFuzzGen structure-aware mutations (recommended):

```bash
AFL_CUSTOM_MUTATOR_LIBRARY=/AFLplusplus/custom_mutators/asnfuzz-rrc-uper/libasnfuzz_rrc_uper.so \
afl-fuzz -i /fuzz/input_dir -o /fuzz/output_dir/asn1c \
         -- /fuzz/asn1c_test/main-test
```

#### Test a single input manually

```bash
cat /fuzz/input_dir/test1 | /fuzz/asn1c_test/main-test
echo $?   # 0 = agree, non-zero = disagree (crash)
```

---

### 2. pycrate_dir (pycrate fuzzer)

**Source:** `/fuzz/pycrate_dir/pycrate_test/`

#### Run the fuzzer

```bash
cd /fuzz/pycrate_dir/pycrate_test
mkdir -p /fuzz/output_dir/pycrate

py-afl-fuzz -i /fuzz/input_dir -o /fuzz/output_dir/pycrate \
            -- python3 main_test.py
```

#### Test a single input manually

```bash
cd /fuzz/pycrate_dir/pycrate_test
cat /fuzz/input_dir/test1 | python3 main_test.py
```

---

### 3. srsRAN_asn1
 Tests `UL-DCCH-Message` (uplink) using srsRAN's native ASN.1 stack.

**Source:** `/fuzz/srsRAN_asn1/tests/unittests/asn1/main_test.cpp`

#### First-time build (inside the container)

```bash
cd /fuzz/srsRAN_asn1/build
rm -f CMakeCache.txt
cmake /fuzz/srsRAN_asn1 \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=afl-clang-fast \
      -DCMAKE_CXX_COMPILER=afl-clang-fast++
make main_test -j$(nproc)
```

This produces `/fuzz/srsRAN_asn1/build/tests/unittests/asn1/main_test`.

#### Run the fuzzer

```bash
mkdir -p /fuzz/output_dir/srsran
afl-fuzz -i /fuzz/input_dir -o /fuzz/output_dir/srsran \
         -- /fuzz/srsRAN_asn1/build/tests/unittests/asn1/main_test
```


#### Test a single input manually

```bash
cat /fuzz/input_dir/test1 | /fuzz/srsRAN_asn1/build/tests/unittests/asn1/main_test
echo $?   # 0 = agree, non-zero = disagree (crash)
```
---

---

## ITS Fuzzers

All ITS fuzzers operate on `CAM` (Cooperative Awareness Message) from ETSI EN 302 637-2.
The ETSI ASN.1 schema lives at `/fuzz_its/ESTI_ITS.asn1`.
Seed inputs live in `/fuzz_its/input_dir/`.


---

### 1. ITS asn1c

**Source:** `/fuzz_its/asn1c_test/`

The C harness (`main.c`) decodes the input with `asn_DEF_CAM`, encodes the result as JER,
then compares against the output of the binary OCaml reference.

#### Compile

```bash
docker exec -it asn1_fuzz_work bash
cd /fuzz_its/asn1c_test
make -j$(nproc)
```

#### Run the fuzzer

```bash
mkdir -p /fuzz_its/output_dir/asn1c
afl-fuzz -i /fuzz_its/input_dir -o /fuzz_its/output_dir/asn1c \
         -- /fuzz_its/asn1c_test/main-test
```

#### Test a single input manually

```bash
cat /fuzz_its/input_dir/input1 | /fuzz_its/asn1c_test/main-test
echo $?   # 0 = agree, non-zero = disagree (crash)
```

---

### 2. ITS pycrate

**Source:** `/fuzz_its/pycrate_test/main_test.py`

#### Run the fuzzer

```bash
cd /fuzz_its/pycrate_test
mkdir -p /fuzz_its/output_dir/pycrate

py-afl-fuzz -i /fuzz_its/input_dir -o /fuzz_its/output_dir/pycrate \
            -- python3 main_test.py
```


#### Test a single input manually

```bash
cd /fuzz_its/pycrate_test
cat /fuzz_its/input_dir/input1 | python3 main_test.py
```

---

### 3. ITS asn1tools

**Source:** `/fuzz_its/asn1tool_test/main_test.py`

#### Run the fuzzer

```bash
cd /fuzz_its/asn1tool_test
mkdir -p /fuzz_its/output_dir/asn1tools

py-afl-fuzz -i /fuzz_its/input_dir -o /fuzz_its/output_dir/asn1tools \
            -- python3 main_test.py
```

The first run will populate the on-disk caches at `/fuzz_its/asn1tool_test/uper_cache` and
`/fuzz_its/asn1tool_test/jer_cache`. Subsequent runs reuse these caches and start faster.

#### Test a single input manually

```bash
cd /fuzz_its/asn1tool_test
cat /fuzz_its/input_dir/input1 | python3 main_test.py
```

---

### 4. ITS TITAN

**Source:** `/fuzz_its/titan_asn1/test_its/`

> **Requires the TITAN SDK, which is not included in this repository.** Only the harness sources
> are tracked here; the TITAN runtime headers and libraries (`TTCN3.hh`, `libttcn3.a`, …) are not
> redistributed. Without them the build fails immediately with:
>
> ```
> ./CAM_PDU_Descriptions.hh:24:10: fatal error: 'TTCN3.hh' file not found
> ```
>
> Install Eclipse TITAN (`ttcn3-11.0.0-linux64-gcc11-ubuntu_22.04.4_lts_foss`) into
> `/fuzz_its/titan_asn1/` so that `include/` and `lib/` sit alongside `test_its/`, then compile as
> below. Every other ITS fuzzer works without it.

#### Compile

```bash
docker exec -it asn1_fuzz_work bash
cd /fuzz_its/titan_asn1/test_its
make -j$(nproc)
```

This produces `/fuzz_its/titan_asn1/test_its/main-test`, compiled with `afl-clang-fast++`.

#### Run the fuzzer

```bash
mkdir -p /fuzz_its/output_dir/titan
afl-fuzz -i /fuzz_its/input_dir -o /fuzz_its/output_dir/titan \
         -- /fuzz_its/titan_asn1/test_its/main-test
```

#### Test a single input manually

```bash
cat /fuzz_its/input_dir/input1 | /fuzz_its/titan_asn1/test_its/main-test
echo $?   # 0 = agree, non-zero = disagree (crash)
```

---

### 5. ITS RASN (Rust)


**Source:** `/fuzz_its/rasn_test/`

#### Compile

```bash
docker exec -it asn1_fuzz_work bash
cd /fuzz_its/rasn_test
cargo afl build
```

This produces `/fuzz_its/rasn_test/target/debug/rasn_its_fuzz`.

On the first build, `build.rs` compiles `ESTI_ITS.asn1` and writes `src/its.rs`.
Subsequent builds skip this step if the ASN.1 file has not changed.

#### Run the fuzzer

```bash
mkdir -p /fuzz_its/output_dir/rasn
cd /fuzz_its/rasn_test
cargo afl fuzz -i /fuzz_its/input_dir -o /fuzz_its/output_dir/rasn \
               -- ./target/debug/rasn_its_fuzz
```

#### Test a single input manually

```bash
cat /fuzz_its/input_dir/input1 | /fuzz_its/rasn_test/target/debug/rasn_its_fuzz
echo $?   # 0 = agree, 6 (SIGABRT) = disagree (panic = differential mismatch)
```

---

## Interpreting Fuzzer Output

AFL stores findings in the output directory:
- `default/crashes/` — inputs where the two parsers disagreed (candidate differential findings)
- `default/queue/` — all interesting inputs found so far
- `default/fuzzer_stats` — live statistics (exec/s, corpus size, crash count)

To replay an ITS crash (example for asn1c):

```bash
cat /fuzz_its/output_dir/asn1c/default/crashes/id:000000,* | /fuzz_its/asn1c_test/main-test
```

A genuine differential exits with **SIGABRT (134)** — the harness reaching its `abort()` — or, for
the Rust `rasn` harness, a panic. Always confirm a replay before counting a finding.

### Two ways to get crashes that are not differentials

**AddressSanitizer startup failures.** The ITS and LTE `asn1c` harnesses enable
`-fsanitize=address` (the 5G harness has it commented out). On Linux 6.x, ASan's shadow mapping
intermittently collides with the kernel's increased ASLR entropy and the process dies with
**SIGSEGV (139) before `main` runs** — on roughly one launch in five, on identical input. AFL logs
these as crashes. A replay under `gdb` shows the giveaway backtrace:

```
#4 __asan::Allocator::InitLinkerInitialized(...)
#5 __asan::AsanInitInternal()
#6 /lib64/ld-linux-x86-64.so.2
```

To avoid it, disable ASLR for the target — start the container with
`--security-opt seccomp=unconfined` and launch through `setarch $(uname -m) -R` — or set
`vm.mmap_rnd_bits=28` on the host. (Docker's default seccomp profile blocks the `personality`
syscall, so `setarch` fails with `Operation not permitted` without that flag.) Alternatively, drop
`-fsanitize=address` from the harness Makefile, at the cost of losing memory-error detection.

**A missing reference decoder.** If a reference binary has not been built, the harnesses do not
fail cleanly — they report disagreements. `rasn` is the worst case: `ocaml_decode` discards the
spawn error and returns `None`, so every successful decode of a *valid* message looks like a
mismatch. If a fuzzer starts finding crashes immediately and constantly, verify the reference
binary exists before believing any of it.

---

## LTE Fuzzers

All LTE fuzzers operate on `DL-DCCH-Message` (downlink) from 3GPP TS 36.331 (EUTRA RRC).
The LTE ASN.1 schema lives at `/fuzz_lte/asn1c_test/lte.asn1`.
Seed inputs live in `/fuzz_lte/input_dir/`.

The OCaml reference decoder is at `/fuzz_lte/verified_format/_build/default/test/test.exe`.
It is **not** pre-compiled in the image — build it (along with the other reference decoders) as
described in [Prerequisites — build the OCaml reference decoders](#prerequisites--build-the-ocaml-reference-decoders-one-time-in-container).

---

### 1. LTE asn1c

**What it does:** Differential test between the asn1c C decoder and the OCaml EUTRA reference.

**Source:** `/fuzz_lte/asn1c_test/`

The C harness (`main.c`) decodes the input with `asn_DEF_DL_DCCH_Message`, encodes the result
as JER, then compares the inner `message` field against the OCaml reference output.
The comparison strips the outer `{"message":…}` wrapper (11-byte prefix + trailing `}`) before
comparing, since the OCaml decoder outputs just the message content.

asn1c C sources were auto-generated from `lte.asn1` (EUTRA-RRC-Definitions, 3GPP TS 36.331).

#### Compile

```bash
docker exec -it asn1_fuzz_work bash
cd /fuzz_lte/asn1c_test
make -j$(nproc)
```

This produces `/fuzz_lte/asn1c_test/main-test`, compiled with `afl-clang-fast`.

To regenerate the C sources from scratch (not needed if already present):

```bash
asn1c -pdu=all -fcompound-names -gen-UPER \
      -no-gen-BER -no-gen-XER -no-gen-OER -no-gen-APER \
      -no-gen-example -findirect-choice lte.asn1
```

#### Run the fuzzer

```bash
mkdir -p /fuzz_lte/output_dir/asn1c
afl-fuzz -i /fuzz_lte/input_dir -o /fuzz_lte/output_dir/asn1c \
         -- /fuzz_lte/asn1c_test/main-test
```

With ASNFuzzGen structure-aware mutations (recommended):

```bash
AFL_CUSTOM_MUTATOR_LIBRARY=/AFLplusplus/custom_mutators/asnfuzz-lte-uper/libasnfuzz_lte_uper.so \
afl-fuzz -i /fuzz_lte/input_dir -o /fuzz_lte/output_dir/asn1c \
         -- /fuzz_lte/asn1c_test/main-test
```

#### Test a single input manually

```bash
cat /fuzz_lte/input_dir/input1 | /fuzz_lte/asn1c_test/main-test
echo $?   # 0 = agree, non-zero = disagree (crash)
```

---

### 2. LTE pycrate


**Source:** `/fuzz_lte/pycrate_test/`

#### Run the fuzzer

```bash
cd /fuzz_lte/pycrate_test
mkdir -p /fuzz_lte/output_dir/pycrate

py-afl-fuzz -i /fuzz_lte/input_dir -o /fuzz_lte/output_dir/pycrate \
            -- python3 main_test.py
```

#### Test a single input manually

```bash
cd /fuzz_lte/pycrate_test
cat /fuzz_lte/input_dir/input1 | python3 main_test.py
```

---

### 3. LTE srsRAN 4G

**Source:** `/fuzz_lte/srsRAN_4G_test/srsRAN_4G/lib/test/asn1/main_test.cc`


#### First-time build (inside the container)

Requires `libfftw3-dev` and `libboost-program-options-dev` (see Prerequisites above).
Only needed once — subsequent `make main_test` calls reuse the build cache.

```bash
docker exec -it asn1_fuzz_work bash

mkdir -p /fuzz_lte/srsRAN_4G_test/srsRAN_4G/build
cd /fuzz_lte/srsRAN_4G_test/srsRAN_4G/build
cmake /fuzz_lte/srsRAN_4G_test/srsRAN_4G \
      -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=afl-clang-fast \
      -DCMAKE_CXX_COMPILER=afl-clang-fast++ \
      -DCMAKE_EXE_LINKER_FLAGS="-latomic"
make main_test -j$(nproc)
```

This produces `/fuzz_lte/srsRAN_4G_test/srsRAN_4G/build/lib/test/asn1/main_test`.


#### Run the fuzzer

```bash
mkdir -p /fuzz_lte/output_dir/srsran4g
afl-fuzz -i /fuzz_lte/input_dir -o /fuzz_lte/output_dir/srsran4g \
         -- /fuzz_lte/srsRAN_4G_test/srsRAN_4G/build/lib/test/asn1/main_test
```

#### Test a single input manually

```bash
cat /fuzz_lte/input_dir/input1 | \
    /fuzz_lte/srsRAN_4G_test/srsRAN_4G/build/lib/test/asn1/main_test
echo $?   # 0 = agree, non-zero = disagree (crash)
```

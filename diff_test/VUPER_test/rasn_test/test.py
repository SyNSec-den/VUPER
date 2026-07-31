#!/usr/bin/env python
import os, subprocess

os.system("cargo build")

test = b"\xe0\x30\x10\x00\x00\x00"

result = subprocess.run(
        "./target/debug/rasn_test",
        input=test,
        capture_output=True,
    )
print('\n')
print(result.stderr)
print(result.stdout)
#!/usr/bin/env python
import os, subprocess

os.system("make clean")
os.system("../ttcn3/bin/compiler --asn1enc test.asn1")
os.system("make")

test =  b"\x80\x01\x80"

result = subprocess.run(
        "./main-test",
        input=test,
        capture_output=True,
    )
print('\n')
print(result.stderr)
print(result.stdout)
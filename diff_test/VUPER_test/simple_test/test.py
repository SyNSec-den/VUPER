#!/usr/bin/env python
import os, subprocess

os.system("make clean")
os.system("../asn1c-v790/bin/asn1c test.asn1 -c -jer -uper -genMake")
os.system("make")

test = b"\x80\x01\x80"

result = subprocess.run(
        "./main-test",
        input=test,
        capture_output=True,
    )
print('\n')
print(result.stderr)
print(result.stdout)
#!/usr/bin/env python
import asn1tools

test = '''
    Foo DEFINITIONS AUTOMATIC TAGS ::=

    BEGIN

    S1 ::= INTEGER


    END
'''

asn1_uper = asn1tools.compile_string(test, codec='uper')
asn1_jer = asn1tools.compile_string(test, codec='jer')

encoded = b'\x02\x00\x0a'
z = asn1_uper.decode('S1', encoded)
print(asn1_jer.encode('S1', z).decode("utf-8", errors='replace'))
  

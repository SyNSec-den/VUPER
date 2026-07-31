# how to use

To compile rust, run 

```cargo build --release``` 

To compile C, run 
```gcc -o test test.c -Ltarget/release -lasnfuzz_rrc_uper -ldl -lpthread -static```

To run it with the OCaml code, simply use
```./test | ../../narcissus_asn1/ExtrTest/_build/default/src/test.exe```
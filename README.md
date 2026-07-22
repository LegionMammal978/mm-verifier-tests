# mm-verifier-tests

This repo contains a set of edge-case tests for Metamath verifiers: it is meant to supplement testing with common valid databases such as `set.mm`. In `verify-tests/`, each test database `test*.mm` is marked `$( should verify $)` (the database should successfully verify) or `$( should error $)` (the database should fail to verify). In `unknown-tests/`, each test database `test*.mm` is marked `$( should warn $)` (if the verifier supports unknown proofs, then the database should produce a warning).

This repo also contains `mmreference.py`, a simple Metamath verifier designed with clarity and conformance in mind. Its performance for large databases is roughly on par with `mmverify.py`. It may be used for differential testing of verifier implementations.

All files in this repo are marked [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/). See `COPYING` for more information.

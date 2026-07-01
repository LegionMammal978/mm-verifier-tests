# mm-verifier-tests

This repo contains a set of edge-case tests for Metamath verifiers: it is meant to supplement testing with common valid databases such as `set.mm`. In `verify-tests/`, each test database `test*.mm` is marked `$( should verify $)` (the database should successfully verify) or `$( should error $)` (the database should fail to verify). In `unknown-tests/`, each test database `test*.mm` is marked `$( should warn $)` (if the verifier supports unknown proofs, then the database should produce a warning).

All files in this repo are marked [CC0 1.0](https://creativecommons.org/publicdomain/zero/1.0/). See `COPYING` for more information.

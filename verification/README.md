# Verification

Lean checks the formal statements and their proof dependencies. It does not determine whether a definition captures the intended interpretation of an informal source.

## Compilation and axiom checks

From the checkout directory:

```sh
./REPRODUCE.sh
```

The command builds the registered modules, validates complete `#print axioms` records, compares them with the expected output, and checks the prohibited-token inventory. Success ends with `ALL CHECKS PASSED`.

The permitted dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Five imported files contain placeholders; none occurs in the checked theorem dependencies. The [placeholder inventory](../expected/forbidden_tokens.expected.txt) identifies those files. Importing a file containing a placeholder is distinct from using that placeholder in a proof.

With an existing compatible mathlib installation:

```sh
PACKAGES_FROM=/path/to/compatible/.lake/packages ./REPRODUCE.sh
```

Memory and concurrency controls are documented in the script. The output validator can be tested separately:

```sh
python3 -m unittest discover -s tools/tests -v
```

## Recorded evidence

The recorded compilation and axiom checks passed for 2,782 modules and 573 axiom records.

- [Verification summary](summary.json).
- [Compilation and comparison results](reproduction-summary.txt).
- [Complete compiler output](checks/).
- [Axiom dependencies](axioms-main.txt) and [additional dependencies](axioms-r7.txt).
- [Output-validator tests](validator-tests.txt).
- [File checksums](FILES.sha256).

The recorded run reused build caches. It is not an independent cold rebuild, and the complete network-install path has not been tested. The checks do not certify every supplementary argument or numerical calculation.

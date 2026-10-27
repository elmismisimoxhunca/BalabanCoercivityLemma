# Evidence for the guarded all-plaquette investigation

The retained results concern explicit matrix algebra and conditional reductions. They do not establish the physical operator identification, a nonzero area seed, or the proposed counterexample.

## Compilation evidence

- [`TIMEOUT_AUDIT.json`](TIMEOUT_AUDIT.json) records complete axiom lists, source/log hashes, source locations, compiler errors, and a forbidden-token scan. [`SUMMARY.json`](SUMMARY.json) summarizes it.
- The selected files contain **101 distinct declarations with retained compilation and axiom evidence**. Their dependencies are subsets of `{propext, Classical.choice, Quot.sound}`.
- These are labelled **B** in the blueprint: evidence from the recorded compilation, **not an independent replay**. No additional Lean compilation is certified by this static audit.
- The six corresponding local/shared source pairs match byte-for-byte. One regenerated source matches its retained source hash and reconstruction; a copied compilation log is counted once, not as a second verification.
- `KData.lean` provides four explicit-matrix lemmas, `q1B00_inv`, `q1_schurA`, `q1_schurB`, and `q1_schurC`. They do not identify the matrices with the physical operator.

## Files not certified

`dictionary/r2/Stencil.lean` has a stale zero exit marker and a newer incomplete log containing a syntax error. It is **not accepted**. `Support.lean`, `DeepCollar.lean`, `Transport.lean`, and the larger vector assembly also lack acceptable current whole-file evidence.

A few printed axiom lists, or a zero marker detached from the source and log, cannot certify an entire file. No physical-row identity is inferred from these attempts.

## Numerical scope and open conclusion

The archive includes exact arithmetic checks of 336 transcribed character blocks and high-precision leading-area calculations for \(q=1,2,4\), with even \(R=18,\ldots,40\). The held-out \(q=1,R=42\) computations succeeded; the incomplete \(q=2,R=42\) computation is excluded.

The first-inverse-only all-plaquette formulation is **numerically strongly disfavoured / conjectured false**, not formally refuted. The physical dictionary, nonzero same-generator area seed, and cofinal argument remain open. The full-guard theorem and the main coercivity theorem are separate proved results.

[`BLUEPRINT_VALIDATION.json`](BLUEPRINT_VALIDATION.json) checks the blueprint’s source/axiom citations and document structure. It is not a Lean or TeX build.

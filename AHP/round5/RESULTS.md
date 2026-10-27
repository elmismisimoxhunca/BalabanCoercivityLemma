# Round 5 judgement

| Item | Status | Decisive result |
|---|---|---|
| Guarded all-plaquette reading | **open** | No verified declaration proves either pinned positive goal or either pinned negative goal without an unproved extra premise. |
| S-3 raw constraint | **closed-holds** | `AdalyFormal.Round3.S3Rest.goalPos1_proved` proves exactly the pinned `GoalPos1`, with an independent successful replay. |

## Guarded item: open

The unchanged targets are `GuardPencilT` and the equivalent `P428Target8SG selAll selAll`, as pinned in `AHP/round3/guarded/pin/Statement.lean`. No declaration settles them in this run. In particular, a theorem concluding `GoalNeg2` **from an unproved realization or sign hypothesis** is not a proof of `GoalNeg2`.

Write A for the actual all-plaquette carrier operator, B for the localized carrier, and D for the genuine assembled localized correction. The unresolved question is whether the carrier guard forces A minus D to be invertible throughout the eventual class. A counterexample family must retain all class, geometry, cap and positive-energy competitor conditions, with cofinal scales and radii and the radius chosen before each cap. Neither a small matrix model nor one finite numerical sample supplies that family.

### IVT track

**Verified partial result:** `AHP/round5/guarded/ivt-r2/Attempt.lean:2382`, `AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control`. Its successful wrapper log records, with line wrapping removed:

```text
'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file's exit is 0, with no warnings or errors. It proves an exact negative endpoint for the actual curved path and derives the first carrier crossing, including the preceding full-carrier guard, from initial positivity and invertibility. It also retains the exact class and cofinal bookkeeping.

**Obstacle:** `InitialKernelControl` is not proved. Initial carrier positivity/invertibility, initial corrected positivity, and a strictly positive genuine D-pairing on an exact singular-carrier kernel remain obligations. They must hold at arbitrarily small amplitudes after the scale and radius are fixed. Nontrivial holonomy does not establish the correction sign.

The two-sided radius-six diagnostic has positive projected correction values around 4.28e-18 and 1.26e-17, but its carrier residual is about 2.49e-14. No rigorous subspace/error bound transfers those signs to the exact crossing kernel. This variant is not the original single-defect path, and this sample also falls below the reduction's room threshold. The radius-two small-amplitude sample is likewise not an arbitrary-cap certificate. Pass 2 improves pass 1's conditional crossing route but closes no goal.

### Exact-kernel / Schur track

**Verified partial result:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2608`, `AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation`:

```text
'AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final path has exit 0, with no warnings or errors. `kernel-r2/Inherited.lean` also compiled successfully, recovering the previously interrupted conditional draft and repaired matrix models. The new theorem reconstructs a full-carrier kernel, including eliminated components, and proves the carrier unit **assuming** exact Schur-block identities and units of both complementary blocks. The cofinal conclusion still assumes the unproved `DilSchurRealisation`.

**Obstacle:** no actual lattice-coordinate decomposition, exterior field, or exact effective-block calculation realizes this separation, even at one admissible instance. The older two-mode ansatz needs full-vector identities and complementary injectivity, not just compressed matrix entries. The newer Schur route must account for eliminated components and both complementary inverses. A single selected Fourier sector cannot establish a full-carrier unit.

A positive genuine correction/source pairing remains unproved. The compiled exterior-independence theorem establishes that B and D stay fixed when only the exterior field changes at fixed interior parameters; exterior tuning cannot repair that missing interior calculation. The eventual spectral realization must also work cofinally with fixed positive mass parameter and radius before every cap. Abstract matrix countermodels do not refute the pinned lattice statement.

### Structural / observed-transfer track

**Verified prior partial result:** `AHP/round5/guarded/structural-r1/Attempt.lean:1101`, `AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed`:

```text
'AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The pass-1 file has exit 0, with no warnings or errors. It gives an inverse-relative estimate under localized inverse guards, the carrier guard and an observation estimate. The headline implication still assumes the unproved class-wide `GShape CObservedGuardSmall`.

**Obstacle:** the proposed exact invisibility mechanism is unsupported by the numerical tests. At radius 18, which meets the room condition, the observed-transfer lower-bound diagnostic grows from about 2.32e-10 to 2.39e-5 as the crossing offset shrinks from 1e-2 to 1e-7. This is pole-like growth with a tiny observed tail, not an exact unboundedness theorem. The scale and cap remain fixed; there is no validated error enclosure or formal operator/Fourier dictionary. A nonzero observation of a mode does not prove that D acts nontrivially or positively on it. No exact carrier-unit/corrected-nonunit separation follows.

**Compilation limitation:** `structural-r2/Attempt.lean` is byte-identical to pass 1, but its fresh wrapper invocation timed out and still has no `.exit`. It was not relaunched. Its reported `exitCode: -1` denotes missing evidence, not an observed Lean failure code. Only the pass-1 compilation is counted. Completed pass-2 numerical tests do not replace that missing compilation.

### What the guarded work does not show about inverses

**No guarded refutation closed.** Therefore this run establishes neither failure with every printed inverse existing nor failure at an actual totalized-inverse witness.

The proposed carrier-unit/corrected-nonunit refutation would, if realized cofinally, necessarily make the corrected covariance inverse totalized: A minus D would be singular. That would refute this guarded formal reading, not demonstrate a failing printed quadratic form at a point where every ordinary inverse exists. No such realized witness is claimed here, and no earlier lost compilation is accepted as verification.

## S-3 raw constraint: closed-holds

**Settling declaration:** `AHP/round5/s3-raw/s3raw-r1/Attempt.lean:1488`:

```lean
theorem goalPos1_proved : GoalPos1 :=
  GoalPos1_iff_GoalPos2.mpr goalPos2_proved
```

Its full name and dependency record are:

```text
'AdalyFormal.Round3.S3Rest.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is exactly the pinned raw comparison, without an extra corridor-invertibility premise. It retains both H/C conventions, every pinned depth and field domain, the original inverse guards, scale constant **1**, and the mass parameter **unchanged everywhere**. It covers the separate terms, reconstructed independent-variable map, whole form and instance inequality—not just the already-known first term.

The proof establishes unrestricted raw/normalized equivalence and applies the verbatim normalized proof. The raw constraint, remainder and corridor matrix carry the same nonzero scalar. The inverse scalar in the corridor lift cancels it. Nonzero scaling preserves unit status; in the singular case both totalized corridor inverses are zero. Thus the comparison also covers those extensions, **without asserting that an ordinary inverse exists at a singular corridor**.

### Verification evidence

- Original `Attempt.lean.exit`: **0**.
- Independent byte-identical `Attempt.verify.lean.exit`: **0**, produced through `AHP/round3/lean1.sh`.
- Both logs: zero errors, 28 inherited warnings, and all 161 dependency records restricted to the permitted axioms.
- The complete 26,607-byte pin and the entire normalized attempt are unchanged prefixes. Sole import: frozen `ZT5A`. No forbidden source tokens were found.
- Original and replay source SHA256: `33ce45abad8892fc2c522708add52f2121b07f647b8e4953b00b7a74fe3ad9e1`.
- Independent report: `AHP/round5/s3-raw/s3raw-r1/Attempt.VERIFY.md`. Replay log SHA256: `bdade3583f20d55d7b4a62c62e3b796413a01578c7d63f9ed5425b374ab528e4`.

**Scope limits:** no obstacle remains for this exact pinned raw normalization goal. This does not prove inverse existence from regularity, positivity, uniform coercivity, or the guarded all-plaquette headline. The CMP99b-only specification of the nonlinear remainder remains a reading question; the pin uses the disclosed CMP109 supplement. Its coupled-corridor realization, selector/class choices, global support/constraint parametrization and other analytic qualifications are unchanged.

## Judge's evidence audit

This judgement inspected the actual source statements, pins, notes, audit reports, logs and exit files. A separate read-only check confirmed current source hashes, unchanged pin prefixes, frozen-only imports, absence of forbidden tokens/errors, source/log/exit ordering, and permitted dependencies matched to print commands. It also confirmed the raw replay's byte identity and the absence of a fresh structural-pass-2 exit. No new compilation or numerical experiment was run by the judge; the independent raw replay is the verifier's existing run.

One harmless audit-count correction: the kernel pass-2 final log contains **199** dependency records, and its inherited log **177**, rather than the reported 198 and 176. The earlier parser omitted the apostrophe-bearing frozen name `AdalyFormal.NonVac.pcd_self'`; its dependency set is only `[propext]`. The corrected read-only scan matched every print and found no disallowed dependency. The IVT pass-2 log has 156 records and structural pass 1 has 86. This count correction changes neither verdict; the earlier audit files were not edited.

Only this report was written. The guarded item remains open; the exact S-3 raw comparison is closed-holds.

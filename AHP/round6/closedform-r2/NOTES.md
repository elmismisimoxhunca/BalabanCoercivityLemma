# Round 6 closed-form track, pass 2

**closedGoal: `none`. No new compiled partial result in this pass.**

Final attempted source: `AHP/round6/closedform-r2/Attempt.lean`.
The new appendix has elaboration errors, and the wrapper invocation timed out without writing an `.exit` file. It was **not relaunched**. The source is retained as the actual failed attempt, not presented as a verified theorem file.

## Contract and reading

Read the round-5 `RESULTS.md` and the complete NOTES of `ivt-r1`, `ivt-r2`, `kernel-r2`, `structural-r1`, and `structural-r2`, the round-3 pin, round-6 `probe/PROBE.md`, and pass-1 closed-form NOTES. Inspected the pass-1 symmetry appendix and frozen gradient, plaquette bilinear form, localization, and projection definitions.

The complete round-3 pin, round-5 `ivt-r2/Attempt.lean`, and round-6 `closedform-r1/Attempt.lean` are unchanged byte prefixes of this attempt. Thus the unchanged bridge remains at line 2382 and the previous main partial remains at line 2643. Only frozen `DrEquiv` is imported; no AHP file is imported. No pinned goal, class condition, quantifier, selector, mass parameter, or amplitude requirement was changed.

## Furthest verified partial: PRIOR PASS ONLY

`AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry`

Prior successful dependency record:

```text
'AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Its verified source is `AHP/round6/closedform-r1/Attempt.lean:2643`, whose existing wrapper exit is 0. It is copied unchanged at the same line here. This theorem constructs the orthogonal two-site translation action on the complete touching-bond carrier and proves actual background and plaquette-holonomy invariance. Supporting results prove composition, commutativity, and displacement period 4q.

This is **not** A/B/D commutation, Fourier block diagonalisation, a crossing calculation, or a positive correction estimate. The existing whole-kernel negative-remainder obstruction is also conditional: no exact leading coefficient or remainder estimate has been supplied.

The current incomplete log repeats the 186 inherited allowed-axiom records, but those records do not establish success of the current file. No new `ClosedFormR2` dependency record was reached. `CHECKS.json` deliberately distinguishes prior verified evidence from the incomplete new attempt.

## What was attempted, but NOT verified

The appendix namespace starts at line 2740. It attempts to extend the physical translation dictionary to:

1. site and plaquette pullback isometries;
2. a generic adjoint-intertwining identity;
3. the frozen covariant gradient, divergence, and full site Laplacian;
4. the actual covariant curl and all thirteen atoms of the transported plaquette bilinear form;
5. permutation invariance of the finite plaquette sum, preserving both symmetrisation and source normalization;
6. commutation of the **undressed** localized Hessian `deltaKLocCLM` for a translation-invariant selector and background.

The last item would still only concern an ingredient of A and B, not either assembled carrier and certainly not the genuine nonlinear correction D. No replacement block, compressed inverse, or invented correction is used. The relevant frozen definitions are:

- `lean/src/R2Ops1.lean:75,84,108`: `gradL2`, `gradAdj`, `lapFull`;
- `lean/src/AdalyFormal/Balaban/CovariantOperators.lean:301,315`: covariant gradient and curl values;
- `lean/src/ZLocOps.lean:101-199`: localized bilinear form, normalization, and `deltaKLocCLM`;
- `lean/src/AdalyFormal/Balaban/DeltaPrimeOperator.lean:362-434`: actual per-plaquette bilinear atoms and their evaluation formulas.

**These new identities are draft proof attempts, not results.** The first concrete failure is that the section assumption `hU` is used only in proof bodies and was not explicitly included in theorem binders. Lean therefore reports `Unknown identifier hU` at line 2803 and subsequent lines. There is also a downstream type-inference failure at line 2828, and unsolved goals. The invariant-selector assumption `hP` likewise needs explicit inclusion where required. The interrupted log ends before the entire appendix is checked, so these are not claimed to be the only repairs needed. No repaired version is represented as compiled.

## Compilation evidence and stop condition

Only this compiler command was run, directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round6/closedform-r2/Attempt.lean
```

The bash call timed out after **1200 seconds**. Subsequent polls found no `.exit`; process inspection found no surviving wrapper or Lean command for this file. The retained log has **20 recorded errors**, zero recorded warnings, and terminates during a diagnostic. The compile was not relaunched and no alternative filename was used to retry it.

The structured result's `exitCode: -1` means **no recorded wrapper exit**, not an observed Lean exit code. In particular this is not a successful compile with a harmless missing status file: the log contains actual elaboration failures.

Artifact-only audit:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 AHP/round6/closedform-r2/audit.py
```

It checks exact prefixes, sole frozen import, absence of prohibited source constructs, current and prior hashes, the prior successful record, and the current incomplete/error status. Its successful execution is **not** a Lean test pass.

Source SHA256:

```text
82b69540a99a5d98ef1a206119a2790f62f985002adda9f47f808f2c9b62f405
```

Log SHA256:

```text
79c6a9b50f80ce79d29d340adeae43644965baf70701bdc0ec6ed52948bf41fc
```

## Mathematical obstruction to the requested closure

Even successful primitive equivariance would leave the substantive obligations unresolved:

- equivariance of site averaging, the support projections, W, mass, constrained H, localized source, and the raw second jet;
- full A/B/D commutation and a complete real/complex Fourier dictionary;
- identification of the first crossing across **all** characters, with the complementary carrier unit proved;
- the finite-volume kernel and constrained-source pairing, including the extremely small left/right splitting;
- initial positivity and an exact amplitude expansion with the requested parametric remainder control;
- or a different cofinal separating witness satisfying the unchanged cap and radius order.

The supplied probe reports a negative first-kernel correction at q=2, R=18, epsilon=10^-100, and a negative fixed-radius leading coefficient approximately -1.8124681040894914e-70. These are external numerical evidence, not formal facts proved here. They oppose the requested positive-leading-sign theorem for the unchanged all-q route. The positive requested grid is pre-asymptotic and cannot justify arbitrarily small amplitudes. A single finite negative sample also does not formally negate the existential cofinal amplitude premise; a whole-kernel expansion is still needed.

The same-kernel pre-crossing alternative has positive corrected form in the probe's decisive tiny-amplitude case. That does not rule out every other vector, later separating point, or family. No such alternative has been constructed here. Neither pinned positive nor pinned negative goal is established.

## Hygiene

All authored files are under `AHP/round6/closedform-r2/`. No numerical job was run. No protected source, earlier attempt, olean, build configuration, paper, notes directory, expected output, or extras was edited. No direct Lean/Lake command, reproduction script, dependency update, BB terminal, commit, or push was used. The duplicate assembly fragment was removed only inside this attempt directory; the actual attempted source and incomplete log are retained.

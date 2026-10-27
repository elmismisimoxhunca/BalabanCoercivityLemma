# Judgement — S-3 first-term normalization

**Status: `closed-holds`, exactly as pinned.**

Both supported first-term comparisons are proved and independently verified. This closes the round-two pin, **not the entire term-by-term fidelity checklist in `paper/OPEN_ITEMS.md` S-3**.

## What is now proved

Under the unchanged inverse guards, the frozen first term equals the independently assembled physical-unit first term, with scalar **\(c(\ell,k)=1\)**. This holds for both linked H/C conventions offered on p.421, at every pinned depth, for actual frozen averaging jets and the background-derived J. It is not restricted to flat backgrounds, full support, depth one, or top-only second jets.

All declaration names below have prefix `AdalyFormal.Round2.S3Pin`.

| Pinned goal | Accepted result | Location |
|---|---|---|
| `GoalPos1` (plain H) | `goalPos1_proved : GoalPos1` | `r1-prove/Attempt.lean:822` |
| `GoalPos2` (dimensionless H with its linked C scaling) | `goalPos2_proved : GoalPos2` | `r1-prove/Attempt.lean:831` |
| `GoalNeg1`, `GoalNeg2` | No negative witness; each is excluded by its accepted positive theorem and the corresponding compiled negative-to-negation helper | `pin/Statement.lean:310,315` |

The stronger theorem `firstTerm_eq_printed` (`r1-prove/Attempt.lean:816`) needs only `InversesExist P .plainH`, not `AdmissibleConfiguration` or `AdmissibleB`. It proves equality for every unit-bond field B of the given `IngrBParams`. The alternative-reading identities transfer this result to dimensionless H. Thus the proof does not obtain equality by exploiting contradictory class or test-field assumptions. It does **not** independently establish that the inverse guards are inhabited.

The negative goals are alternative outcomes, not additional positive obligations: their absence does not make the pin only partly closed. The accepted result is stronger than a mere reduction, so `closed-reduced` would also understate it. No new standalone theorem of `¬ GoalNeg1` or `¬ GoalNeg2` was added by this judgement.

## Why eta and tau-star are accounted for

The proof follows the actual operator construction:

- `PrintedGp_scale` and `PrintedW_eq` (lines 443 and 462) handle the padded Dirichlet inverse on its supported solutions; the exterior identity padding is not incorrectly rescaled.
- `PrintedC_plain_eq` (line 494) identifies the actual plain-H C with eta times the frozen C at every level. `PrintedHC_readings` (line 502) keeps the two H/C changes linked.
- The Q/adjoint, mass, G/H and J comparisons (lines 533–664), followed by `PrintedG1inv_scale` (line 695), identify the physical G1 construction rather than replacing it by an arbitrary matrix.
- `PrintedN_scale` (line 722) and `physical_schur_scale` (line 733) give, with \(W_F=\operatorname{diag}((\ell^j\eta)^3)\),

  \[
  N_{\mathrm{phys}}=\eta^{-1}N_{\mathrm{body}}W_F,
  \qquad
  W_F N_{\mathrm{phys}}^{-1}f=\eta N_{\mathrm{body}}^{-1}f.
  \]

  The physical pairing therefore yields exactly the frozen external eta.
- `PrintedB_eq_tau_adjoint` (line 760) identifies the explicit top-level insertion with tau-star without a full-support premise or extra scalar.

The inverse is taken on the whole multilevel space before evaluating on the inserted field. There is **no interchange of inversion and compression**.

The inspected page images `pin/renders/p393.png`, `p421.png` and `p428.png` support the key reading: (3.14) evaluates C at \(\ell^j\eta A\); p.421 links the H and C conventions; (3.156) itself contains neither an external eta nor tau. Tracking both arguments of the quadratic jet gives \(C_j^{(2)}(A)=\ell^{-2j}\mathrm{raw}_j(A)\), so the plain-H input is \(\eta\ell^{-j}\mathrm{raw}_j(A)\). This corrects, rather than confirms, the earlier Stage-A power count. Source interpretation remains subject to the pin's disclosed conventions.

## Evidence accepted and checked

The decisive independent report is [`r1-prove/Attempt.VERIFY.md`](r1-prove/Attempt.VERIFY.md), verdict `closes-goal`. Its completed recompilation is recorded in [`Attempt.verify.log`](r1-prove/Attempt.verify.log) and [`Attempt.verify.exit`](r1-prove/Attempt.verify.exit), exit **0**. Interrupted verification runs are not counted.

This judgement re-read the pin, both attempts' `NOTES.md`, the existing verification report, the proof bodies, and the historical S-3 design/attack/decision and Stage-B material. There is **no independent VERIFY.md for the refutation attempt**. A fresh read-only text/hash/log audit of the current files established:

- The entire 16,414-byte, 357-line pin is a byte-identical prefix of each attempt. Both have sole import `ZT5A`.
- The positive attempt has exactly the explicit unchanged goal types at lines 822 and 831, without additional theorem premises or local goal replacements.
- The positive independent log contains **59/59** requested dependency records, **27** nonfatal warnings and **0** errors. All dependency lists contain only `propext`, `Classical.choice`, `Quot.sound`; neither goal print is missing.
- Raw forbidden-token scans of both attempt sources found no prohibited construct, including no opaque stand-in.
- The current positive source and complete independent log hashes match the verifier's recorded hashes:

  ```text
  pin/Statement.lean
  9133de3969b6a26d2f6c373d4bb56c1d0ce6d545bd161b69a851e6af2416962c
  r1-prove/Attempt.lean
  67908d7b3f5a0b882fdbf32376f130e800709d78e1747b43ad6cfaa116d5aa47
  r1-prove/Attempt.verify.log
  5c6c392d4679225a0cbaf8165cd390e9c92b79bbb2bfb93f332214d998622d99
  ```

The main verified records are:

```text
'AdalyFormal.Round2.S3Pin.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.S3Pin.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This judge ran **no additional Lean compilation or numerical experiment**. Acceptance rests on the independent successful compilation of the unchanged artifact, with its identity checked again here. No build, reproduction script or dependency update was run.

## Disposition of the refutation attempt

`r1-refute/Attempt.lean:420` proves `GoalNeg1 ↔ GoalNeg2`; line 410 equates the two printed first terms; line 427 gives the corrected actual-jet C scaling. None proves a negative goal or compares the full frozen/printed inverse chains. Its own successful log has 64 permitted dependency records and no warnings/errors; this judgement checked that log but does not relabel it an independent recompilation.

Its numerical scale/Schur diagnostics are explicitly abstract, not realized lattice witnesses, and are not closure evidence. The older Stage-A counterexample also remains rejected: it used an impossible nonzero level-zero second jet and mishandled the C argument scaling. The refutation notes' remaining dictionary work is now supplied by the independently verified positive attempt; it is no longer an open obligation of this pin.

## What remains open or outside this closure

1. **The other terms of (3.156):** common units for the mass subtraction, final unit nonlinear J term and `bondEnergy` are not established here. Mass/J comparisons *inside G1* do not certify those separate summands. Broader OPEN_ITEMS S-3 therefore remains only partially discharged.
2. **Analytic existence and positivity:** all inverse guards are retained. No proof derives them from printed small-field regularity, supplies the source's thresholds, or proves positivity or a guarded non-vacuity witness.
3. **S-1 localization and S-2 source-class fidelity:** touching bond carriers, inside-plaquette Delta/J, both-endpoint cube regularity and frozen coverage/geometry are retained, not identified with all printed conventions. The specialization remains dimension 3, SU(2), finite periodic tori and the pinned chart/trace conventions.
4. **Primitive analytic identification:** scaling is proved for the genuine frozen componentwise averaging jets and actual background source. Their complete identification with the source's analytic averaging maps on the printed class remains inherited work.
5. **The rest of the coercivity/covariance construction:** no Cop support/axial/global-Q1 transfer, full C-parametrization or Gaussian covariance theorem follows. The all-B equality avoids needing these constraints for this first summand only. No inverse/compression identity is asserted.

**Approved plain-language conclusion:** In the pinned guarded encoding, both supported H/C conventions give exactly the same first summand as the frozen expression; its eta and tau-star are explained by the physical pairing/inverse scaling and top-level insertion. This is not a certification of the whole printed coercivity lemma.

Only this `JUDGEMENT.md` was written by the judge. The pin, attempts, existing evidence, protected sources and manuscript files were left unchanged; no commit or push was made.

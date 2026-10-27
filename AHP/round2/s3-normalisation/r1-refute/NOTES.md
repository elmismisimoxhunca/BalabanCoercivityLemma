# S-3, round 1 — refutation attempt

## Outcome

**closedGoal: `none`.** Neither `GoalNeg1` nor `GoalNeg2` is proved. No pinned goal was weakened or replaced.

Main partial declaration: `AdalyFormal.Round2.S3Pin.negative_goals_equivalent`, `Attempt.lean:420`. It proves exactly `GoalNeg1 ↔ GoalNeg2`, not either proposition. The stronger operator-level reason is `linked_firstTerm_eq` at line 410: the two pinned **printed** first terms agree on every field, at every depth, for every `IngrBParams`. This does **not** compare either printed expression with frozen `GenP.firstTerm`.

A second useful partial result is `plain_C_eq_mesh_C2full`, line 427:

```lean
PrintedC P .plainH A =
  mesh P • C2fullOf P.G P.U (PrintedW P (iE P.G A))
```

It uses actual `D2B` and `C2rawB` and is valid at every depth. It does not assume that the jets are nonzero, insert a level-zero jet, or replace the background by free coefficients. It does not identify `PrintedW` with frozen `Wop`.

## Source reading and attack route

Read the handoff, OPEN_ITEMS, Stage B report, previous S-3 design/attack/decision and comparison file, the round-2 pin, CMP99b pages 393–396 and 421–428, and the pin's page renders for (3.24), (3.119), (3.122), (3.126)–(3.129), (3.136), (3.156), (3.157). Also checked the p.393 render for the argument in (3.14).

The relevant page evidence is consistent with the pin, not with the old Stage-A recipe:

- p.393:28, (3.14), evaluates `C_j` on `ell^j eta A`.
- p.421:28 links the change of H input scale to the change of C argument/output. These cannot be varied independently.
- p.422:92, (3.136), starts at level 1 and has exponent `d+1`.
- p.428:32,35, (3.156), has no explicit eta/tau and imposes support, axial, and global Q1 constraints on B; (3.157) does not permit inverting a compressed multilevel covariance.

Both linked readings remain source-supported as documented by the pin. The previous `eta^2 raw` input to **plain** H is not retained as an additional supported reading.

With `s_j = ell^j eta`, the corrected coefficient is

\[
s_j\ell^{-2j}=\eta\ell^{-j},\qquad
s_j^{-1}(s_j^2\ell^{-2j})=\eta\ell^{-j}.
\]

The second formula is the dimensionless-H convention after its matching H input factor. Thus turning on a genuine lower-level jet cannot, merely through these coefficients, recover the old alleged discrepancy.

## Numerics first

`scale_probe.py` ran before any new comparison proof was written. Output: `scale_probe.json`; process output and exit: `scale_probe.log`, `scale_probe.exit` (0). The script cites the Lean file/line for every assembled formula.

This was deliberately a **scale/Schur diagnostic, not a lattice counterexample search with certified configuration hypotheses**. It does not realize `LinkCfg`, the tower, W, or admissible test fields. Independent finite arrays stand in for the raw linear/bilinear maps, source and base quadratic operator; the level-zero second jet is set to zero. Such arrays cannot close the negative goals. They were used only to test whether the old coefficient mechanism survives the corrected pin before undertaking a genuine realization.

Results:

- 100 exact rational coefficient checks: ell = 2,3,5,13; depth 2 through 6; every level. All corrected plain/dimensionless coefficients equal `eta * ell^(-j)`.
- 45 abstract multilevel matrix cases: ell = 2,3,5; depth = 2,3,4; five deterministic seeds per pair. Lower-level nonzero jets, level-weighted adjoint/mass/pairing, and inversion on **all rows** before testing top fields.
- Maximum corrected frozen/printed ratio error from 1: `7.216449660063518e-15`.
- The deliberately incorrect old plain-H recipe produces ratio spreads up to `5.4732812629687544e-05`, demonstrating diagnostic sensitivity. That control is not a pinned goal or source reading.
- Address-space cap: 4,000,000,000 bytes. Peak reported RSS: 36,516 KiB. Single BLAS/OMP thread, no package installation, run through `"$BB_CLI" heavy run --`.

No genuine numerical counterexample candidate emerged from this route; no full admissible nonlinear-lattice numerical solve was performed. Numerical agreement is not used as a proof of either positive goal.

## Compiled partial results

All names below are in `AdalyFormal.Round2.S3Pin`.

| Declaration | Attempt.lean line | Exact scope |
|---|---:|---|
| `mesh_ne_zero` | 370 | Nonzero mesh from the positive ell stored in P. |
| `spacing_ne_zero` | 373 | Nonzero spacing at every level. |
| `linked_C_cancel` | 380 | Applying the inverse-spacing diagonal to dimensionless C gives plain C, as actual bilinear maps evaluated on arbitrary A,B. |
| `linked_HC_eq` | 390 | The two linked H/C contractions agree. |
| `linked_KBil_eq` | 397 | Their complete physical bilinear forms agree. |
| `linked_G1inv_eq` | 402 | Their physical G1 inverse operators agree. |
| `linked_N_eq` | 406 | Their multilevel N operators agree. |
| `linked_firstTerm_eq` | 410 | Their printed first terms agree for all B, without inverse guards. |
| `linked_inverses_iff` | 414 | The two complete pinned inverse guards are equivalent. |
| `negative_goals_equivalent` | 420 | The two unchanged negative propositions are equivalent. |
| `plain_C_eq_mesh_C2full` | 427 | Correct all-depth scale relation for the actual raw jets, retaining PrintedW. |

The last theorem proves the corrected coefficient relation rather than the outdated Stage-A relation. It does not assume a new comparison predicate or substitute a new printed first term.

## Why the attempt stops

The tested refutation mechanism disappears under the corrected pin, and the actual-jet Lean result explains why. I have no actual depth-at-least-two configuration satisfying `AdmissibleConfiguration` and all ten inverse clauses, with two nonzero `AdmissibleB` fields and unequal nonzero-denominator ratios. In particular, neither the old arbitrary-jet witness nor its wrong-weight control can be promoted to such a configuration.

A complete frozen/printed comparison still needs the actual padded-site inverse/projection/W dictionary, the G/H/J scale comparisons, the top insertion versus tau adjoint, and the full multilevel inverse/pairing cancellation. These were not proved here. A genuine refuter would need a failure in that remaining dictionary realized on the constrained field space; a nonzero lower-level second jet alone no longer supplies one. I do not claim a no-counterexample theorem or closure of S-3.

## Verification and write scope

`Attempt.lean` begins with a byte-for-byte copy of the entire pinned `Statement.lean`, including all goal definitions. Sole import: frozen `ZT5A`. All additions follow that prefix. No AHP imports.

Final serial command:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s3-normalisation/r1-refute/Attempt.lean > ../AHP/round2/s3-normalisation/r1-refute/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/s3-normalisation/r1-refute/Attempt.lean.exit
```

Final exit **0**, no warnings or errors. All 64 local declaration audit records are present: 63 use exactly `propext, Classical.choice, Quot.sound`; `Reading` uses none. Every new helper and every named local definition has a print. Main record:

```text
'AdalyFormal.Round2.S3Pin.negative_goals_equivalent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Attempt.lean` SHA-256: `ee3361385ffb1a42ecb00fd47d56c880f4c9849b901fc739ba9d3f50ca1a106f`.

Only files under `AHP/round2/s3-normalisation/r1-refute/` were written. No `lake build`, reproduction, update, commit, push, deletion, or edit of a frozen/protected path was performed. Initial development compile failures were corrected; only the final successful compilation is claimed.

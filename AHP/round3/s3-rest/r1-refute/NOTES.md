# S3-rest, round 1, negative attack

**Requested negative closure: `none`. Final compilation: exit 0. Both pinned negative goals are proved impossible, rather than proved.**

## What was tried

Read the handoff, OPEN_ITEMS B/K–N/R/S, Stage-B and round-two results, round-two S3 pin/judgement/positive attempt, and the current S3-rest pin. Read CMP99b corpus pp.421–428 and inspected all eight saved round-two images (392,393,394,419,420,421,422,428), plus the pin's CMP109 p.267 render. The source-supported unit remainder is the lifted raw second coefficient. The normalized representation divides **both** its constraint and remainder by ell.

`scale_search.py` ran before writing the Lean proof. It is a bounded scalar/trace prefilter, **not** a realized lattice/background search. It tests 32 linked scale combinations, ell in {2,3,5,13}, depth in {2,3,5,12}, both unit readings, with exact rational scalar arithmetic. Every predicted mass/energy/nonlinear ratio is 1. A 1000-sample actual su(2) trace-pair check has maximum floating error 3.552713678800501e-15. Dividing only the remainder would produce a mismatch by ell, but is not either pinned reading. The script cites Lean file/line locators for every scalar or pairing it models. It allocates no fine lattice or large matrices and uses constant memory.

No actual nonzero-J depth-two numerical candidate was found or certified; the prefilter does not establish admissibility, class membership, inverse guards, or actual H1 equality. No abstract matrix or free jet is offered as a witness.

## Why the attack changed to a no-go check

The definitions suggest exact cancellation, not a counterexample:

1. Printed trace is exactly the shipped su(2) inner product, so mass and independent energy coincide without any configuration hypotheses.
2. Printed raw Q is ell times the frozen Q1. Writing q = unitConstraintScale * ell, its dropped-variable matrix is q H0.
3. For bijective H0, the printed corridor inverse is q^-1 H0inv. Multiplication by the linked remainder scale leaves exactly ell^-1 times the frozen lift, as in D2in.
4. The already-established physical inverse-chain dictionary gives printed H1 = frozen H1 on the supported carrier. The extra dimensionless-H factor is 1 at the inserted top level.
5. Fine volume eta^3 cancels the eta^-3 in the actual background-derived J.

`Attempt.lean` has the **entire current pin as a byte-identical prefix**. The round-two first-term comparison helpers are copied verbatim (not imported). The new actual-operator identities compiled: the lift, D2in, H1, final J term, mass and energy. The final result `negative_goals_impossible` rules out the pinned ratio certificates, and therefore both strong negative goals. It is not a proof of either negative goal and is returned with `closedGoal: none`.

All following declarations are in namespace `AdalyFormal.Round3.S3Rest.RefuteR1`:

| Declaration | Attempt.lean line | Precisely established |
|---|---:|---|
| `mass_eq` | 1111 | Frozen/printed mass equality for every P and B |
| `energy_eq` | 1115 | Frozen/printed independent energy equality for every P and Bt |
| `PrintedDtilde_eq` | 1180 | Both linked unit remainders equal actual D2in whenever frozen H0 is bijective |
| `PrintedUnitC_eq` | 1188 | Both printed parametrizations equal actual genC under that same bijectivity guard |
| `PrintedH1For_insert` | 1239 | Both H/C readings agree with frozen H1 on inserted unit fields under the original inverse guards |
| `nonlinear_eq` | 1261 | Actual final nonlinear summands equal for all B, both H/C and unit readings, under original inverse guards and H0 bijectivity |
| `scaleWitness_impossible` | 1270 | No pinned ScaleWitness exists, for any of the four reading combinations |
| `negative_goals_impossible` | 1277 | **`¬ GoalNeg1 ∧ ¬ GoalNeg2`** |

The concrete obstruction is the witness's `ratio_ne`: both its nonzero-denominator ratios equal 1. This is now a kernel-checked obstruction, not merely unsuccessful numerics. The proof never needs to assume admissibility, depth two, support, or a free choice of jets. It uses the actual `C2tilde`, actual `H1in`, and actual background-derived `Jf`. The extra `NoGammaMassRepair` condition is not reached: the ratio certificate is already inconsistent.

## Boundaries

- Nothing is obtained by weakening or redefining a pinned goal.
- The nonlinear comparison uses the original InversesExist guards and the bijectivity half of the negative witness's corridor guard. It need not use its additional printed matrix guard.
- No unrestricted positive goal is submitted: singular-corridor totalizations are not addressed by the new proof.
- No source analytic identification, inverse existence, small-field threshold, positivity, global-Q1 transfer, or Gaussian integral is established.
- CMP99b p.427 alone underdetermines Dtilde; the pin's CMP109 p.267 supplement remains a source-reading qualification.

## Verification status

Compilation was only through `AHP/round3/lean1.sh`. The first streamed invocation ended while waiting for the lock: empty log and no exit record, so it is not a compilation result. A persistent BB terminal then preserved the shared lock/heavy-slot queue. The first actual compilation failed on proof-script/API details (over-eager linear-map extensionality, scalar multiplication order, and the E-carrier inner-product rewrite). It is retained as `compile1.failed.log/.exit`, not accepted evidence. After correcting those proofs, the final invocation was:

```sh
LEAN_NUM_THREADS=1 AHP/round3/lean1.sh AHP/round3/s3-rest/r1-refute/Attempt.lean
```

Final `Attempt.lean.exit`: **0**. `Attempt.lean.log` contains **144/144** requested dependency records; every one is a subset of `propext`, `Classical.choice`, `Quot.sound`, with no missing record or error. There are **29 nonfatal warnings** (27 in the verbatim inherited proof, two in the new proof). `audit.py` checks the byte-identical pin prefix, sole frozen import ZT5A, raw forbidden-token absence, complete dependency records and current hashes; `AUDIT.json` reports `passed: true`.

Main axiom record, line wrapping normalized:

```text
'AdalyFormal.Round3.S3Rest.RefuteR1.negative_goals_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

SHA-256:
- Attempt.lean: `1ea8051e8ccf17a60d23443cf1d5bfe35aeab8266c63906656302fed7895d894`
- Attempt.lean.log: `948d6d6ab341090b406d27a5ec8aefbdec0aa2bce8e1cb9e671d0938dec14395`
- Pin: `799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b`

No independent verifier replay is claimed. Both created terminals are closed and the temporary proof-body assembly file was removed.

No protected file or other AHP path was edited. No build, dependency update, reproduction command, commit or push was run.

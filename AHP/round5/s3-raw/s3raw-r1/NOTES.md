# S-3 raw constraint — round-five attempt 1

## Result

**Closed `GoalPos1`, exactly as pinned.**

- Main declaration: `AdalyFormal.Round3.S3Rest.goalPos1_proved : GoalPos1`, [`Attempt.lean:1488`](Attempt.lean).
- Exact logical reduction: `GoalPos1_iff_GoalPos2`, line 1484.
- Stronger pointwise result: `restComparison_raw`, line 1479, requires only the original `InversesExist P r` and not `AdmissibleConfiguration`.
- Unrestricted representation equivalence: `restComparison_raw_iff_normalized`, line 1472, requires neither configuration nor inverse guards.

The main proof applies the exact goal equivalence to the verbatim copied `goalPos2_proved`. It does not add a corridor-invertibility assumption, change the independent-field domain, weaken an equality to an inequality, or change the candidate scale. Both pinned H/C conventions, every pinned depth, every unit field, every independent field, and every real gamma are retained. The scale remains **1**, with **a unchanged everywhere**.

## Verbatim reuse and imports

Read the round-three S-3 rest `JUDGEMENT.md`, `pin/PIN.md`, `pin/Statement.lean`, and positive attempt `NOTES.md` and proof.

The entire 61,934-byte round-three positive attempt is a byte-identical prefix of the new file. Thus the 26,607-byte pin, all round-two comparison helpers, and the full normalized proof are unchanged. New proofs begin after that prefix. The sole import is frozen `ZT5A`; there are no AHP imports.

## Reduction, including singular corridors

Writing the two readings as raw and norm, the actual pinned definitions give

\[
Q_{\mathrm{raw}}=\ell Q_{\mathrm{norm}},\qquad
R_{\mathrm{raw}}=\ell R_{\mathrm{norm}},\qquad
M_{\mathrm{raw}}=\ell M_{\mathrm{norm}}.
\]

Here the matrix is the actual coupled dropped-bond matrix, and the remainder is the actual background-derived second coefficient. No freely chosen matrix or jet is substituted. Nonvanishing of the real scalar ell follows from the existing `P.hell` field alone.

| Lines | Declaration / step |
|---|---|
| 1370–1374 | `linear_isUnit_smul_iff`: multiplication of a real-linear endomorphism by a nonzero scalar preserves unit status, including the zero-module case. |
| 1376–1387 | `linear_inverse_smul_total`: the totalized inverse of `c • A` is `c⁻¹ • Ring.inverse A`, without an `IsUnit A` assumption. The unit branch checks both products; the nonunit branch proves both inverses zero. |
| 1392–1409 | Exact raw/normalized scalar identities for Q, remainder and constraint matrix. |
| 1411–1426 | Corridor unit-status equivalence and `PrintedConstraintMatrix_inverses_singular`: if frozen H0 is not bijective, both printed matrix inverses are zero. Uses the copied normalized-matrix identification and `Module.End.isUnit_iff`. |
| 1429–1436 | The raw corridor lift is ell inverse times the normalized lift, including singular totalizations. |
| 1439–1455 | `PrintedDtilde_raw_eq_normalized` and `PrintedUnitC_raw_eq_normalized`: cancellation of the lift's inverse scalar against the matching remainder or Q scalar. |
| 1457–1476 | Equality of final nonlinear terms and whole forms; equivalence of complete instance inequalities and complete `RestComparison` predicates. No inverse guard is used in these raw/normalized identities. |
| 1479–1489 | Transfer the copied normalized comparison and exact pinned positive goal. |

In particular,

\[
h_{\mathrm{raw}}R_{\mathrm{raw}}=h_{\mathrm{norm}}R_{\mathrm{norm}},\qquad
I-h_{\mathrm{raw}}Q_{\mathrm{raw}}=I-h_{\mathrm{norm}}Q_{\mathrm{norm}}.
\]

This closes the precise unrestricted raw-operator comparison left open in the round-three judgement. At singular corridors it compares totalized extensions; it does **not** assert that an ordinary inverse exists there.

## Compilation and audit

Both compiler invocations were direct bash calls to the authorized wrapper:

```sh
AHP/round3/lean1.sh AHP/round5/s3-raw/s3raw-r1/Attempt.lean
```

The first diagnostic compile exposed two scalar-cancellation tactic goals: simplification produced ell times ell inverse, rather than the reverse order. Using the matching cancellation lemma resolved them. No statement or hypothesis was changed. The second, final current-source invocation completed successfully without timing out.

**Final evidence:** `Attempt.lean.exit` is **0**; the log has **0 errors**, **28 inherited warnings**, and **161/161 dependency records**, all subsets of `propext`, `Classical.choice`, `Quot.sound`. This includes every local declaration, the 18 new helpers/theorems, and the main theorem.

```text
'AdalyFormal.Round3.S3Rest.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`audit.py` checks the current source and log: byte-identical pin and entire normalized-attempt prefixes, sole frozen import, exact main header, forbidden-token absence, a dependency print for every declaration, a log record for every print, allowed dependencies, errors and exit status. It passes and writes `AUDIT.json`. Run:

```sh
python3 AHP/round5/s3-raw/s3raw-r1/audit.py
```

Final SHA-256 hashes:

```text
Attempt.lean      33ce45abad8892fc2c522708add52f2121b07f647b8e4953b00b7a74fe3ad9e1
Attempt.lean.log  2fd4c78194bdcf1875a0c5f22ca814c0c4158d94a31b937437ce4d82004e8b16
pin/Statement    799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b
copied attempt   9aa7238ddbff572aea7b0f0394eb22325280451f46087ec6e99da0f3518ae6a2
```

This is fresh builder compilation, not an independent verifier replay. No numerical experiment was necessary or run. No terminal, direct Lean/build/reproduction/dependency-update command, commit or push was used. All authored files are under `AHP/round5/s3-raw/s3raw-r1/`; protected files and earlier rounds were not edited.

## Remaining scope limits

No obstacle remains to the requested pinned `GoalPos1`. The proof does not resolve the pin's separate source-reading and analytic qualifications: CMP99b-only Dtilde coefficients, the use of the CMP109 supplement, local versus coupled solving, global support/Ax/Q1 parametrization, class and selector fidelity, inverse existence from regularity, guarded non-vacuity, positivity, uniform coercivity thresholds, Gaussian integration or covariance. Those are not consequences of this normalization identity.

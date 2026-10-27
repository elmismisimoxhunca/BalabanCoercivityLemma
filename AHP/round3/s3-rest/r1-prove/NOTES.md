# S-3 rest — positive attempt, round 1

## Result

**Closed `GoalPos2`, exactly as pinned.**

- Main: `AdalyFormal.Round3.S3Rest.goalPos2_proved : GoalPos2`, [`Attempt.lean:1268`](Attempt.lean).
- Stronger pointwise result: `restComparison_normalized`, line 1252. It requires only `InversesExist P r`; it does not use `AdmissibleConfiguration`. The main theorem retains the exact pinned configuration and inverse guards.
- Both linked p.421 H/C conventions, all pinned depths, every unit field B and every independent field Bt are covered. The full `InstIneq` equivalence holds for every real gamma, with the pinned positive constant \(c(\ell,k)=1\) and **a unchanged everywhere**.
- This attempt does not prove `GoalPos1` (raw unit constraint), or construct a negative witness. It stops because the requested one-positive-goal obligation is closed, not because of a remaining proof obstacle.

## Proof route and reuse

The whole round-three `pin/Statement.lean` is a **byte-identical prefix** of `Attempt.lean`. No pinned definition or goal was changed. The sole import is frozen `ZT5A`; there are no AHP imports.

The round-two proof block from `r1-prove/Attempt.lean:359-820`, through `firstTerm_eq_printed`, is copied verbatim in its original namespace (41 lemmas/theorems). The previous first-term goals are not copied or used as replacements for the new goals. Its inverse helpers reuse the frozen `NsCvOS4` argument. For the new comparisons:

| Location in Attempt.lean | Checked step |
|---|---|
| 1100–1115 | The normalized trace pairing is the frozen SU(2) inner product; unit pairing is the PiLp pairing; the separate mass subtraction and independent-field bond energy agree. Uses frozen `SuTwoInner.inner_eq_trace`, not a new norm convention. |
| 1117–1125 | The independently assembled **normalized** unit first jet equals P.Q1; its remainder is ell inverse times the actual frozen C2tilde. |
| 1128–1140 | The frozen conditional `H0inv` equals the independently used `Ring.inverse`. In the bijective branch the proof follows frozen `ZXR2Unit2.H0_H0inv` via `LinearEquiv.ofBijective`; in the non-bijective branch both definitions are zero. Thus no corridor invertibility premise is silently added. |
| 1142–1160 | The normalized corridor matrix, lift, lifted second coefficient Dtilde, and C agree with H0, hLift, P.D2in, and GenP.genC respectively. Moving the same ell inverse through the linear lift gives the D2 identity. |
| 1163–1188 | `PrintedH1_eq` reuses the round-two `PrintedH_eq` proof pattern with G1 and the full constraint covariance N. The physical metric/scalar cancels through the **full-space inverse**. No compression is inverted. |
| 1190–1219 | Top spacing is one, so the additional diagonal factor for dimensionless H acts identically on the explicit top insertion. Both H conventions therefore give the frozen H1 action on unit fields. |
| 1221–1233 | The physical source contributes eta inverse-cubed, canceled by the fine eta-cubed pairing. The adjoint identity for iE/pE then gives the actual final nonlinear term, including its factor 2. |
| 1235–1249 | Assemble the copied first-term identity, separate mass identity and final nonlinear identity into equality of the whole genForm. |
| 1252–1270 | Transfer the unchanged C and independent-field energy through the exact universally quantified instance inequality; conclude the exact pinned `GoalPos2`. |

The proof compares genuine jets/backgrounds throughout. There are no numerical matrices, arbitrary second jets or freely assigned sources.

## Source reading and limits

Read HANDOFF, OPEN_ITEMS B/K–N/R/S, Stage-B and round-two results, the round-two S-3 pin/judgement/proof, and the new pin. Read CMP99b pp.421–428 in `sources/corpus/pages/`, and inspected all eight saved round-two renders (392,393,394,419,420,421,422,428). Also inspected the new pin's CMP109 p.267 render.

The scale choices are those already pinned:

- CMP99b p.392 fixes normalized trace and the lattice-volume pairing in (3.11). The unit lattice on p.427 has volume one, so neither the mass subtraction nor independent-field energy acquires eta cubed.
- p.393 (3.14) supports dividing **both** the unit constraint and its remainder by ell; (3.16) uses constant a, unlike the separate site recursion on p.394 (3.24).
- p.421 (3.128)–(3.129) and p.422 distinguish the linked H/C conventions and define H1 using the full covariance inverse. Top spacing is one in either convention.
- p.428 (3.156) contains the separate mass and final J subtractions; (3.157) and the lower-bound paragraph refer to energy of Bt, not of C Bt.
- CMP99b p.427 alone leaves the coefficients of Dtilde underdetermined. The concrete lifted-remainder reading uses **CMP109 p.267**, whose displayed linearization, relation L Qtilde h = I, and (2.11) identify the lifted quadratic remainder and explicitly cite (3.156). The proof does not resolve the CMP99b-only reading question without that supplement.

All other pin disclosures remain: finite periodic dimension-three SU(2) geometry, retained touching bond carriers but inside-plaquette Delta/J selectors, frozen coverage/class conventions, genuine componentwise jets, and the coupled dropped-bond system. Equality of the coupled inverses does not prove the source's one-variable equations decouple. The unchanged independent-field domain is compared; no new global-Q1/support/Ax parametrization theorem is asserted.

At a singular corridor matrix, equality concerns the two totalized extensions, **not** existence of a printed inverse. No proof derives inverse guards or positivity from small-field regularity, and no guarded non-vacuity witness or new coercivity threshold is supplied. This closes the pinned normalization comparison, not all printed-statement fidelity questions.

## Compilation and audit

Compilation used only:

```sh
AHP/round3/lean1.sh AHP/round3/s3-rest/r1-prove/Attempt.lean
```

The shared wrapper was run in a persistent bb terminal after an initial foreground wait was interrupted. Long shared-lock/heavy-slot waits were allowed to finish; no parallel Lean process was launched by this attempt.

The first completed diagnostic run found two local elaboration problems (three errors): broad extensionality descended into field coordinates instead of stopping at the linear map, and the generic scalar-inner rewrite did not match the E-carrier instance. They were fixed with explicit `LinearMap.ext` and the already-proved round-two `e_inner_smul_right`. No mathematical statement or premise changed.

**Final current-source run:** exit **0**, **0 errors**, **143/143 requested dependency records**, all subsets of `propext`, `Classical.choice`, `Quot.sound`. There are 28 nonfatal warnings: the 27 inherited round-two warnings and one additional deprecated-lemma warning in the reused H1 proof pattern.

```text
'AdalyFormal.Round3.S3Rest.restComparison_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.S3Rest.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Evidence: `Attempt.lean.log`, `Attempt.lean.exit`, and `AUDIT.json`. `audit.py` checks the byte-identical pin prefix, unchanged copied round-two proof block, sole import, exact main header, all local declaration prints and corresponding log records, axiom allowlist, forbidden raw tokens, errors and exit code. It is a text/log audit, not a numerical operator model or substitute for the Lean check. Run it with `python3 AHP/round3/s3-rest/r1-prove/audit.py`.

Final hashes:

```text
Attempt.lean      9aa7238ddbff572aea7b0f0394eb22325280451f46087ec6e99da0f3518ae6a2
Attempt.lean.log  52ec1e17af570e49ac1a7a63577c41d768238408a071e7f7207f6c1991628115
pin/Statement    799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b
```

No numerical experiment, direct Lean invocation, build, reproduction, dependency update, commit or push was run. All authored files are under `AHP/round3/s3-rest/r1-prove/`; protected sources and other workers' files were not changed. Independent verifier recompilation remains a separate workflow step.

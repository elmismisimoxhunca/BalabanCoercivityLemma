# S-3, round 1, positive attempt

## Result

**Both positive goals are proved exactly as pinned.**

- `AdalyFormal.Round2.S3Pin.goalPos1_proved : GoalPos1` — `Attempt.lean:822`.
- `AdalyFormal.Round2.S3Pin.goalPos2_proved : GoalPos2` — `Attempt.lean:831`.
- Stronger intermediate theorem `firstTerm_eq_printed` — `Attempt.lean:816`: for every actual `IngrBParams P`, every unit-bond field B, and the unchanged `InversesExist P .plainH` guard, the frozen first term equals the pinned printed first term. Neither the configuration predicate nor the test-subspace predicate is needed for this algebraic identity.

The constant is exactly \(c(\ell,k)=1\). There is no restriction to depth one, flat U, full support, or a top-only second jet. No proposed goal was weakened or redefined.

The complete original `pin/Statement.lean` is a **byte-identical prefix** of `Attempt.lean`, including its definitions, goal statements, comments and logical helpers. Its opening “PIN ONLY” comment describes that retained prefix; the new proofs follow it. The sole import remains frozen `ZT5A`; no AHP import was added.

## Proof route and reuse

Started from the actual frozen construction rather than the rejected Stage-A matrices:

1. Reused the proof scripts of `ring_inverse_eq_of_mul` and `inverse_smul'` from frozen `lean/src/NsCvOS4.lean:16–18,35–40`, verbatim except for the enclosing namespace and the added explanatory comments. No import of that lane was necessary.
2. Used frozen `Gp_spec` (`ZR2Ops2.lean:130`) to compare the Dirichlet inverses by their equations and support. This avoids the incorrect step of scaling the exterior identity padding along with the interior Laplacian.
3. Used frozen `Submodule.map_smul` for equality of the Laplacian-image subspaces, hence equality of the R projections.
4. Used frozen `symm_unique`, `symmOp_symm`, `inner_symmOp_diag` and `P.G1inv_spec` (`R2Algebra.lean`, `ZXR2Wire2.lean`) to identify the actual chosen G1 inverse from its symmetric quadratic form. No arbitrary Hessian was substituted.
5. Proved the adjoint of top-row extraction by finite sums, without the full-support premise of the older `ZGU1D.tau_adj_apply` theorem.

All newly declared proof helpers have their own `#print axioms` command.

## Established dictionary

Here \(\eta=\mathrm{mesh}\,P\), \(s_j=\ell^j\eta\), and \(M_F=\operatorname{diag}(s_j^3)\). “Body” means the genuine frozen construction with the same U, geometry, support selectors and raw composite jets.

| Comparison | Declaration in `Attempt.lean` |
|---|---|
| D* = eta^-1 times body D*; Laplacian, site mass and Dirichlet site operator = eta^-2 times their bodies | `PrintedDs_scale`, `PrintedLap_scale`, `PrintedQpa_scale`, `PrintedDelp_scale` |
| R unchanged; G' = eta^2 times body on the Dirichlet support; W unchanged | `PrintedR_eq`, `PrintedGp_scale`, `PrintedW_eq` |
| Actual plain-H C = eta times the frozen C, at **every** level | `PrintedC_plain_eq`, line 494 |
| Linked dimensionless-H/C and plain-H/C contributions agree | `PrintedHC_readings`, line 502 |
| Q unchanged; physical Q* = eta^-3 Q_body* M_F | `PrintedQ_eq`, `PrintedQs_scale` |
| T = eta^-1 T_body; Delta-pi and bond mass = eta^-2 times bodies | `PrintedT_scale`, `PrintedDpi_scale`, `PrintedMass_scale` |
| G = eta^2 G_body; H unchanged | `PrintedG_scale`, `PrintedH_eq`, line 618 |
| J = eta^-3 J_body, including the chart minus sign | `PrintedJ_scale` |
| Physical bilinear form on the diagonal = eta times frozen K | `PrintedKBil_diag_scale`, line 674 |
| G1 inverse = eta^-2 G1inv_body; G1 = eta^2 G1_body | `PrintedG1inv_scale`, line 695; `PrintedG1_scale` |
| N_phys = eta^-1 N_body M_F, with N acting on all levels | `PrintedN_scale` |
| Physical pairing after the full inverse = eta times the unweighted body pairing | `physical_schur_scale`, line 733 |
| Explicit `PrintedB` insertion = tau* B, without a support premise or scalar | `PrintedB_eq_tau_adjoint`, line 760 |
| The two pinned first terms and inverse guards coincide | `PrintedFirstTerm_readings`, `InversesExist_readings` |

The final cancellation does **not** exchange inverse and compression. For any multilevel f, the equation for \(N_{phys}^{-1}f\) gives

\[
M_F N_{phys}^{-1}f=\eta N_{body}^{-1}f.
\]

Taking the pinned physical pairing yields the frozen external eta. Substituting the separately proved `PrintedB = tau* B` closes the first-term comparison.

## Source interpretation retained

The prescribed corpus pages 393–396 and 421–428 and required equation renders were inspected. The scale citations and departures are copied unchanged from the pin; in particular:

- p.393:28, (3.14): the argument is \(C_j(U,\ell^j\eta A)\). Undoing this quadratic argument rescaling gives \(C_j^{(2)}(A)=\ell^{-2j}\mathrm{raw}_j(A)\).
- p.421:28: plain H is paired with \(s_j C_j^{(2)}(A)\); the alternative scales the two C inputs by \(s_j\) and the H input by \(s_j^{-1}\). `PrintedHC_readings` verifies their equivalence on the actual jets.
- p.394:66–85, (3.24): the site mass keeps recursive a_j and Dirichlet padding. The bond mass instead keeps constant a, as in p.393:57, (3.16).
- p.419, (3.119); p.420, (3.122)/(3.126); p.421, (3.128)/(3.129): the full inverse chain is rebuilt before its comparison with the frozen objects.
- p.422:92, (3.136): the exponent d+1 is consistent with the level metric and the additional plain-H C factor; no additional independent factor is introduced.
- p.428:32–43, (3.156)/(3.157): no eta or tau is inserted into the printed definition. Their appearance on the frozen side is accounted for by the proved metric/inverse and insertion identities.

The old `SPEC.md`/`ATTACK.md` matrix prediction is not used. Its unphysical level-zero jet and its lost C-argument rescaling were already rejected in `DECISION.md`. The existing Stage-B depth-one comparison does not prove this result; the new all-level C comparison uses the corrected pinned definition.

## Verification

Executed serially from the frozen project, exactly in the prescribed form:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s3-normalisation/r1-prove/Attempt.lean > ../AHP/round2/s3-normalisation/r1-prove/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/s3-normalisation/r1-prove/Attempt.lean.exit
```

**Final exit: 0.** No errors. All **59** printed dependency records (15 retained from the pin plus 44 new declarations) list exactly `propext`, `Classical.choice`, `Quot.sound`. Both goal theorem lines are present. The log contains 27 nonfatal deprecation/style/unused-tactic warnings; these are not hidden or counted as failures.

Two earlier final-audit command attempts timed out while waiting for the machine's occupied heavy slots; the successful final run supersedes those incomplete logs. Earlier development compilations were used to repair tactic elaboration, finite-sum dependent rewriting, and scalar/inner-product instance matching. No failed proof body remains.

Mechanical checks on the final files:

- Pin prefix byte identity: true.
- Sole import: `ZT5A`.
- Every new declaration has an axiom print: 44/44.
- Forbidden-token scan: no hits.
- `Statement.lean` SHA-256: `9133de3969b6a26d2f6c373d4bb56c1d0ce6d545bd161b69a851e6af2416962c`.
- `Attempt.lean` SHA-256: `67908d7b3f5a0b882fdbf32376f130e800709d78e1747b43ad6cfaa116d5aa47`.
- `Attempt.lean.log` SHA-256: `b5657e917d1309905ad04fd5d4cf74ed36e73bf20b8b525c5c06f1fed14592ff`.

No numerical model was run or introduced. No build, reproduction script, dependency update, commit or push was performed. This attempt wrote only `Attempt.lean`, its `.log`/`.exit`, and this note under `AHP/round2/s3-normalisation/r1-prove/`.

## Why work stopped / remaining scope

Stopped because **both exact positive goals compiled with the permitted axioms**. No mathematical obstacle remains for these pinned goals; independent workflow verification is still appropriate.

This is a first-summand normalization result under the pinned inverse guards and source reading. It does not prove those guards from small-field regularity, change the retained S-1 localization conventions, certify the other summands of (3.156), or establish that the C-parametrization has every printed support/constraint property. All departures listed in `pin/PIN.md` remain disclosed. It is not a new proof of the whole printed coercivity inequality.

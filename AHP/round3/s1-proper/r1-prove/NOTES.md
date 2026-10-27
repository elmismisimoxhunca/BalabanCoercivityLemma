# S-1 proper domains, round 1, positive attempt

## Verdict

**No pinned goal closed by this positive attempt.** `GoalPos1` and `GoalNeg1` are copied without modification. The main partial declaration is `Round3.S1Proper.goalPos1_iff_twoUnits` (`Attempt.lean:542`). An equivalence with an unproved residual is not a proof of either pinned goal.

The final locked compilation exited **0**, with **no warnings or errors**, and all **69** dependency records permitted. The source audit passes. The positive search stopped at a concrete carrier obstruction, described below; the parallel refuter independently reports an exact compiled negative goal, not recompiled by this attempt.

## Frozen proof reused and the remaining question

I read the required handoff/status documents, the round-2 S-1 pin/proof and S-2 pin/non-vacuity/saturation proofs, the Stage-B class-inclusion proof, and the actual frozen `RI6`, `D1Lit`, `D1Final`, `GdGen5`–`GdGen7`, `GdR5a` and associated support lemmas. No AHP file is imported.

1. **Class transfer** (`Attempt.lean:385`). The Stage-B product-box helpers and regularity transfer are copied verbatim. They prove `ClassCoupledFour → ClassCoupled` in the current pin's namespace. This does not transfer the changed operators by itself.
2. **Actual complete form comparison** (`corner_form_eq_frozen`, line 411). Frozen `GdGen5.genFormS_eq_loc` works for any selectors containing `plaqIn`, not merely `selAll`. Corner selection contains `plaqIn`. Consequently the corner and frozen complete forms agree for **every B**, under `Admissible`, positive ell, depth at least one, derived room `17 ell ≤ RM`, and `WellDefAt` on both sides. This includes the nonlinear J term. No raw-Delta monotonicity is asserted.
3. **Necessary inverse conditions** (`wellDefAt_of_corner_ineq`, line 423). With positive coercivity constant, nonnegative mass parameter and one positive-energy admissible free input, the corner inequality forces `WellDefAt`. If any of its three units fails, the actual totalized full form collapses to the negative mass term, contradicting the inequality. This is not a claim that all primitive inverses exist.
4. **Only two units remain** (`corner_ineq_iff_two_units`, line 460). Given the frozen instance inequality and room, the corner inequality is equivalent to the following: whenever a positive-energy admissible free input exists, both the selected carrier `dataS.Ginv` and the selected corrected operator `G1invS` are units. The unit of `NmatS` is derived by the existing transfer theorem. In a zero test space the inequality is automatic, without unit assumptions.
5. **Exact headline reduction** (`TouchFourUnits`, line 480; `goalPos1_iff_twoUnits`, line 542). The residual has precisely the pin's threshold order, smallness cap, admissibility, Lambda and four-bond class. It requires the two units unconditionally, not merely a carrier-unit-to-corrected-unit implication. The forward implication extracts the existing constants. The reverse implication reuses `RI6.p428Target8`, takes maxima of the two scale/radius thresholds, raises the existential radius threshold to at least 18, and takes the minimum of the two positive caps. Gamma comes from the frozen theorem. The room bound is derived, not added to the pin.

Thus the missing positive step is not an estimate of the complete form under existing inverses. It is unconditional eventual invertibility on the actual four-bond class. Neither the full-guard literal theorem nor the guarded all-plaquette residual supplies this.

## Concrete obstruction to the proposed positivity route

Further operator calculations are in the final source:

- `Delta_corner_eq_all_on_support` (line 576): at every background, applying the corner and all-plaquette Delta operators to a touching-supported field gives the same result. A plaquette omitted by corner selection has no touching boundary edge, so the field vanishes on all four edges; the genuine frozen `deltaK_set_congr` applies.
- `Dpi_corner_eq_all` (line 588): the actual W sandwich, compressed to the actual carrier, is identical. Frozen `D2Lit.Wop_mem_bondSupp` proves that W preserves touching support, including under its totalized inverse convention.
- **`corner_Ginv_eq_all` (line 600)**: the actual corner carrier equals the all-plaquette carrier at **every** `IngrBParams`, for any choice of the all-plaquette current selector. No class or inverse assumptions. J does not enter this carrier.
- `exists_nonunit_corner_carrier` (line 614): directly transfers frozen `D1Literal.exists_nonunit_Ginv` to the corner carrier along `Uth`, at a supplied slab boundary point, with the original admissibility/room and `0 ≤ a < 4` hypotheses. This is an actual non-unit crossing, not just an indefinite direction or numerical evidence.
- `perCubeRegularTouch_of_one_on_touch` (line 630) and `perCubeRegularTouch_Uth` (line 661): every positive alpha and mesh satisfy **all three** touching regularity bounds on the exterior path. The proof takes gauge one and matrix logarithm zero on every guarded bond, using that each class cube is inside the base domain. The path changes only bonds with neither endpoint in the base. Thus the small-phase cap for controlled links does not restrict its exterior theta.

The last two theorems do not by themselves package common four-bond coverage, torus compatibility, Lambda, capped alpha, a positive-energy competitor and cofinal thresholds into one failure family. I did not claim `GoalNeg1`. The positive carrier-invertibility route has a concrete obstruction, not merely a missing generic matrix estimate. The round-2 slab's `slabNv_coversFour` is the relevant geometry helper for the parallel refutation attempt, to which the carrier transfer was communicated.

While the final compile was waiting, the parallel refuter reported completing precisely that assembly as `Round3.S1Proper.goalNeg1_proved : GoalNeg1` at `../r1-refute/Attempt.lean:354`. I read its `NOTES.md`; it reports exit 0 and permitted axioms. That separate closure is not credited to this attempt and is subject to its own independent verification. Our results are compatible: the residual is an equivalent obstruction, not a proof that the units hold.

Limits: there is no asserted equality with frozen inside Delta, no whole-space equality of the two uncompressed Delta maps, no unguarded identification of the complete forms, and no assertion that an indefinite operator is singular. No numerical script was needed or run.

## Pin versus Balaban's print

These disclosures are inherited from `../pin/PIN.md`, not newly authenticated page-image readings. They are retained unchanged by the partial proof:

1. Site coverage and four-touch-edge common-box coverage are added hypotheses; four-touch coverage is not one-corner coverage and does not cover every operator-selected plaquette.
2. Delta/J use the CMP102 p.277 one-corner interpretation on the base Dirichlet domain, rather than the frozen inside selector or the displayed whole-torus CMP99 sums. A background link on an opposite edge can lie outside all touching class bonds.
3. The class uses at-least-one-endpoint bonds, but difference and curl-of-curl conditions still require every stencil edge in each guard to touch the cube. This interpretation supplies no far-edge bound.
4. Gauges and Hermitian traceless logarithms are existential per cube, not one common global gauge.
5. The class cubes remain aligned periodic product boxes, two-stratum/unique-index cubes, one common factor 12, not arbitrary unions or per-cube factors. The altered level-zero class is not substituted.
6. Dimension is three and gauge group SU(2), not the print's generality.
7. The finite periodic rectangular torus, side-minus-one extents, scaling map, eta, divisibility/size assumptions and periodic l1 distance remain frozen conventions.
8. The tower uses strict collars, aligned half-open blocks, padding and the exact p.396 base-block construction under reading A, not an arbitrary thinner layer, reading B or two-domain construction. The p.408 third-enlargement clause is absent.
9. Lambda uses the frozen unit-lattice block union, block-sum condition and strict same-R collar; it may be empty. The common-radius identification remains a reading.
10. The parameter range is all natural ell at least two, all a>0 and k≥1, M=ell^m and natural R. Odd ell>11 and R restricted to powers of ell are not imposed.
11. The exact frozen thresholds/constants order explicates and strengthens aspects of the print's informal uniformity: R0 follows m; a0 and gamma follow ell,a,m,R and precede all instance data. No Total-style stronger order is inserted.
12. Class norms remain full Frobenius, test energy trace-normalized; strict differential powers and the actual curl-adjoint-curl `ddA` remain. No explicit smallness cap is prescribed.
13. Actual frozen averaging jets, weighted mass, site inverse, projection, W, multilevel Q, second jets and C are retained; their entire printed dictionary is not rederived.
14. Actual touching support, selected `CRowIn`, axial/dropped-bond constraints and `genC` remain. The joint constraint solution and singular fallback are retained; no alternate input kernel is imposed.
15. Eta/tau-star, mass subtraction, nonlinear J summand and bond energy stay frozen. Round-2 normalization of the inside first term does not identify all changed-operator printed units.
16. Inverses remain totalized with no well-definedness premise/conclusion in the pin. The residual is an equivalence established beside it, not an added inverse premise disguised as a positive proof.
17. No fixed room or R≥18 premise is in the pin. The reduction chooses larger existential thresholds and derives its proof-local room.

This attempt does not certify the unqualified printed assertion or identify the full printed class.

## Verification

Final command (in persistent terminal `term_zypvphmywb`):

```sh
AHP/round3/lean1.sh AHP/round3/s1-proper/r1-prove/Attempt.lean
```

The terminal exited 0, and `Attempt.lean.exit` records **0**. `Attempt.lean.log` has **69** dependency records, no warnings/errors, and every dependency list is a subset of `propext`, `Classical.choice`, `Quot.sound`. All **52** local definitions/theorems have explicit print commands and dependency records. Direct frozen proof helpers are printed separately as well. Main line:

```text
'Round3.S1Proper.goalPos1_iff_twoUnits' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`python3 AHP/round3/s1-proper/r1-prove/audit.py` passes. `AUDIT.json` records all ten pin declarations byte-for-byte, all three direct imports resolving under `lean/src`, no raw forbidden tokens, all local prints, compiler exit and log freshness, and permitted dependency records.

- Final source SHA-256: `86a1c2e204a291061632202377375c7d19e14508cf207e6cce9f79f7c35fcc00`.
- Final log SHA-256: `2f33ea448b02b72cad70be05e5c7f5ed646a4b2dc8cca60a1a1238affdb7bf1c`.

All intentional workspace writes are confined to `AHP/round3/s1-proper/r1-prove/`. No protected file, Lake configuration, other item, commit or remote was changed. Only the supplied wrapper invokes Lean, with its shared lock and heavy slot. Queued foreground invocations were interrupted without fresh exit records; the persistent final retry waited for the lock/heavy slot and completed. A prior completed elaboration failed only on equality transport in `corner_of_touch_boundary`; rewriting the hypotheses before inserting them into the corner disjunction fixed it. Only the final successful source/log is accepted evidence. No independent recompile is claimed here.

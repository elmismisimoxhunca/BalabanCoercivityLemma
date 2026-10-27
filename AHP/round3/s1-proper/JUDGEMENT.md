# Round 3 judgement — S-1 on proper domains

## Verdict: `closed-fails` for the exact formal pin

**The unguarded four-bond touching-class headline with corner-selected Delta and J is false.** The independently verified refutation proves the exact negative goal, not a weaker instance or a raw-Hessian obstruction:

- File: `AHP/round3/s1-proper/r1-refute/Attempt.lean:354`.
- Declaration: `Round3.S1Proper.goalNeg1_proved : Round3.S1Proper.GoalNeg1`.
- Independent copy: `r1-refute/Attempt.verify.lean:354`, byte-identical to the current attempt.

```text
'Round3.S1Proper.goalNeg1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The pin defines `GoalPos1 := P428TouchFour` at `pin/Statement.lean:98` and `GoalNeg1 := ¬ GoalPos1` at line 101. These are opposing answers to one question, not two independent obligations. Thus the negative closure settles the item: **GoalNeg1 is proved and GoalPos1 is ruled out. Neither remains undecided.** This is not merely `closed-reduced` or `partly-closed`.

This verdict does **not** refute Balaban's unqualified printed lemma, a version presupposing inverse existence, or an invertibility-guarded target.

## What is now proved, in plain words

The proof constructs proper nonempty depth-two slabs, not the empty/whole-torus cases that settled round 2. On these slabs the background is the identity on every endpoint-touching bond, so all three touching-regularity bounds hold at every positive cap. Bonds completely outside the base domain can nevertheless carry a phase. The corner-selected operators still read some of those exterior background links.

The actual corner carrier becomes singular along that exterior path. At the singular point the frozen totalized-inverse convention makes the **complete** selected form nonpositive on a genuine admissible competitor, while its proposed positive lower bound is strictly positive. This defeats every proposed threshold and positive coercivity constant in the pin.

### Proof chain checked against the current files

| Step | Declaration/location in `r1-refute/Attempt.lean` | Scope |
|---|---|---|
| Omitted corner plaquettes have zero field values on all boundary edges | `edge_not_touch_of_not_corner`, 142; `deltaKLocCLM_corner_eq`, 203 | Corner Delta equals all-plaquette Delta **on touching-supported fields**, at every background. Not equality with inside Delta or on arbitrary unsupported fields. |
| Actual carrier comparison | `corner_Dpi_eq_all`, 212; `corner_Ginv_eq_all`, 222 | Frozen W preserves touching support; equality survives W and Dirichlet compression. No inverse or class premise is needed. |
| Actual four-bond coverage | `slabNv_coversFour`, 285 | On this slab, the four-touch-edge antecedent forces inside plaquettes. Frozen slab coverage supplies the required common class cube. |
| Arbitrarily small class caps | `perCubeRegularTouch_of_one_on_touch`, 295; `Uth_perCubeRegularTouch`, 330 | Gauge one and logarithm zero prove all three strict regularity bounds. Exterior phases are not bounded by this touching class. |
| Actual singular carrier | `exists_nonunit_corner_Ginv`, 338 | Transfers `lean/src/D1Main.lean:141`, the genuine continuous-path non-unit crossing, to both pinned corner selectors. Not an inference from numerical negativity. |
| Exact headline contradiction | `goalNeg1_proved`, 354–407 | Supplies torus, admissibility, Lambda, coverage, cap, class membership and both test-field predicates, with the required cofinal order. |

The last step fixes \(\ell=2\), \(a=1\), takes the candidate exponent \(m=m_0\), and chooses \(R=\max(R_0,18)\) **before** receiving either positive constant. It then uses \(M=2^m\), the frozen slab and Lambda, and
\[
\alpha_0=\tfrac12\min\bigl(a_0/(12M),1\bigr)>0,
\qquad 12M\alpha_0\le a_0.
\]
`SlabNv_bdpt`, used at line 379, supplies an inside site and an adjacent outside site; the base is genuinely nonempty and proper. `BseedNv_props`, used at line 404, supplies a positive-energy field satisfying both `OnLambdaTildeIn` and `OnLambdaT`.

The final application is the actual `lean/src/D1Collapse.lean:74`, `not_InstIneqS_of_not_unit`, with **both** selectors `selCorner`. Its underlying identity at line 57 gives
\[
\operatorname{GenS.genFormS}_{\mathrm{corner}}(C\widetilde B)
=-a\langle C\widetilde B,C\widetilde B\rangle\le0
<\gamma_0\operatorname{bondEnergy}(\widetilde B).
\]
Thus the corrected inverse, first term and nonlinear J term are accounted for. No unproved comparison of full forms is used in the refutation.

The proof uses boundary squares with two adjacent inside corners. The suggested one-corner search was not a pinned requirement; this does not weaken the exact negative goal. Neither kind of boundary square is automatically covered by the four-touch-edge antecedent.

## Disposition of both attempts

- **`r1-refute`: accepted as closing GoalNeg1.** Its [independent verification](r1-refute/Attempt.VERIFY.md) reports `closes-goal`, with successful locked recompilation and exact statement/definition checks. The judge's current-file checks confirm the recorded evidence below.
- **`r1-prove`: useful partial results, no positive closure.** `goalPos1_iff_twoUnits` at `r1-prove/Attempt.lean:542` reduces the exact headline to eventual carrier and corrected-operator invertibility whenever a positive-energy admissible test exists. It does not prove those unit conditions. Its guarded complete-form equality at line 411 and unconditional corner/all carrier equality at line 600 explain the obstruction. There is no separate `VERIFY.md` or independent recompile for this attempt; none is represented as present. The negative verdict does not depend on crediting its reduction as independently verified closure.

The two attempts are compatible. A reduction to unit conditions is not evidence that those conditions hold; the refuter supplies the cofinal singular family that the positive attempt did not assemble.

## Evidence audit by this judge

I read the pin/PIN, both attempts' `NOTES.md`, the existing refutation `Attempt.VERIFY.md`, the required handoff/status reports and relevant round-2 source passages. I checked the current negative proof and the frozen selected-form, crossing and collapse declarations. A read-only source/log check established:

- Current attempt and independently compiled copy are byte-identical.
- The entire shared options/open/namespace/variable/definition/check block is byte-identical to the pin, including all ten definitions and the exact goal pairing. The main theorem has no added hypotheses.
- The three round-2 coverage helpers are copied byte-for-byte.
- Every hash recorded in the verifier's audit matches the current files; that audit records `pass: true`.
- The pin, positive attempt, negative attempt and independent negative copy each have exit **0**, no compiler warnings/errors, and respectively **10, 69, 44, 44** dependency records. All records use only permitted axioms, including two axiom-free positive-attempt helpers. Every local declaration has its dependency record.
- The current sources contain none of the forbidden whole-word constructs, even before stripping comments; direct imports resolve only under `lean/src`.

Decisive hashes:

| File | SHA-256 |
|---|---|
| `pin/Statement.lean` | `dff1d868790779a2def248238b348234402a065760bdb0d0c9b675136fe7cf9f` |
| `r1-refute/Attempt.lean` and `Attempt.verify.lean` | `a114b3d28b83d02b8d38df0f26cfac3d1485bb4cb72bdcd0150bd392e79a0280` |
| `r1-refute/Attempt.verify.lean.log` | `fb72117ac68c0ad97b024c2bcc461adea36b2e07cd1faf9e8b3e090137849b40` |

Independent compilation evidence is `r1-refute/Attempt.verify.lean.log` and `.lean.exit`; the definition/source audit is `r1-refute/Attempt.verify.audit.json`. The verifier compiled exclusively through `AHP/round3/lean1.sh`. **This judgement pass did not run another Lean compilation, build, reproduction script, dependency update or numerical experiment.** The recorded numerical reconnaissance is not needed for closure. No fresh source-page inspection by this judge is claimed.

## Pin versus print; what remains open

All departures in [pin/PIN.md](pin/PIN.md) remain disclosures. In particular:

1. **Inverse existence:** the contradiction uses a non-unit carrier and totalized inverses. It is not an invertible negative-energy witness, does not settle an inverse-guarded corner formulation, and supplies no closure of the separate `P428Target8SG`/`GuardPencilT` item.
2. **Printed boundary operators:** selecting corner plaquettes while retaining their full background products can read exterior links. The endpoint/corner convention alone does not establish that this is CMP99's Dirichlet/locality prescription. The verifier independently inspected ten other page images but could not obtain CMP102 p.277; that quotation remains inherited evidence. A fully source-identified non-collapsing boundary formulation is still unresolved.
3. **Added coverage and class interpretation:** site coverage and common-cube four-touch-edge coverage are added. They do not cover every selected corner plaquette. Endpoint-touching regularity retains guarded derivative stencils and separate per-cube gauges/logarithms. Replacing this class by the collapsing corner class or the stronger shell class changes the question; shell coercivity is not settled here.
4. **Geometry and parameter restrictions:** the pin retains three-dimensional SU(2), finite periodic rectangular tori, aligned factor-12 product boxes with unique indices/two-stratum containment, strict collars, padding and the exact reading-A base layer. The frozen Lambda/support/constraint conventions and common radius remain. Non-box unions, per-cube factors, thinner/two-domain formulations and the third-enlargement condition are not supplied. The contradiction fixes blocking factor two, so it does **not** decide the later odd-\(L>11\) convention.
5. **Remaining dictionaries:** the explicit threshold order, natural-radius range, full-Frobenius class norm versus trace-normalized test energy, curl-adjoint-curl expression, actual averaging jets/site operators/C and eta/tau-star conventions remain those of the pin. This proof does not identify their complete printed dictionary or resolve broader S-3 normalization questions.

**No question within this exact positive/negative pin remains open. The broader printed S-1 question remains qualified by the issues above.** The frozen inside-operator theorem and the round-2 corner-coverage collapse are not contradicted: this item changes the operators and uses the non-collapsing four-bond class.

Only `AHP/round3/s1-proper/JUDGEMENT.md` was written by this judgement pass. Existing sources, compiler records, verification reports and protected files were left unchanged; no deletion, commit or push was performed.

# Round 7 / s1-odd — every-blocking-factor touching refutation

**Pinned and proved for every natural \(\ell\ge2\) and every real \(0<a<4\).** This includes every odd \(\ell>11\). The range \(a\ge4\) is not decided. This is a refutation of the **unguarded formal slice**, not of a statement presupposing existence of the printed inverses.

## Files and exact goals

- [Statement.lean](Statement.lean): the **complete round-3 pin is an unchanged byte prefix**, including its historical comments and old `GoalPos1`/`GoalNeg1`. Those comments describe the old pinning stage, not the current proof status. New definitions start in namespace `Round7.S1Odd` after that prefix.
- `P428TouchFourAt` (line 142): the fixed-\(\ell,a\) slice, with precisely the original remaining binders, hypotheses and conclusion.
- `def Goal1 : Prop` (line 157): for **every** \(\ell\ge2\), and **every** \(0<a<4\), this slice is false.
- `def Goal2 : Prop` (line 163): the same slice refutation for every **odd** \(\ell>11\) and every \(0<a<4\).
- [../proof/Attempt.lean](../proof/Attempt.lean): `not_touchFour_every_ell` at line 422 proves the individual slice negation; `goal1_proved : Goal1` at line 477 and `goal2_proved : Goal2` at line 480 prove both exact targets.

In plain words: at each such blocking factor and mass, there is **no** exponent threshold, then radius threshold depending on the exponent, then positive smallness cap and positive coercivity constant depending on the radius, that make the complete corner-selected inequality hold on the four-bond touching class.

The slice retains the order

\[
\exists m_0\ge1\;\forall m\ge m_0\;\exists R_0\;\forall R\ge R_0:
\quad\mathrm{SidePow6}(\ell,\ell^m,a)\ \land\
\exists a_0>0\;\exists\gamma_0>0\;\forall k\ge1,L_u,\alpha_0,S,\Lambda,U.
\]

Here \(M=\ell^m\), \(\eta=\ell^{-k}\), and \(0<\alpha_0\), \(12M\alpha_0\le a_0\), `TorusOK`, `Admissible`, `LambdaOK2` and `ClassCoupledFour` are the unchanged premises. The conclusion is genuine `InstIneqS selCorner selCorner`, including the full selected form and all its admissible test fields. There is no extra inverse guard or geometric premise. Properness is supplied by the construction, not inserted as a new hypothesis.

`headline_iff_slices` (proof line 415) is proved by **`Iff.rfl`**:

```lean
P428TouchFour ↔ ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
  P428TouchFourAt ell hell a
```

The source audit independently checks that the expanded slice body equals the old headline body after removing only its outer \(\ell,\mathrm{hell},a,0<a\) binders, modulo whitespace. The mass window belongs to the **negative goal**, not to a changed class or changed instance conclusion.

## Strengthening over round 3

`Round3.S1Proper.goalNeg1_proved` refuted a universally quantified headline using only \(\ell=2,a=1\). That alone says nothing about any individual odd blocking factor. `Goal1` instead refutes **each** slice, keeping \(\ell\) and \(a\) arbitrary throughout the construction. `Goal2` therefore addresses the later-paper odd-\(L>11\) range; oddness is not used in its proof. The old negative goal is recovered separately at proof line 485 and is **not** offered as the new target.

The supported mass range is exactly \(0<a<4\), matching `D1PGen.not_literal_every_ell`. The crossing theorem bounds the positive mass contribution by \(a\langle X,X\rangle\) and supplies a negative boundary contribution \(-4\langle X,X\rangle\). This gives the stated strict window, not a proof that \(4\) is sharp and not an all-positive-mass theorem.

## Actual proof and quantifier audit

The proof uses the frozen general-\(\ell\) family behind `lean/src/D1PGen.lean`, **not** that theorem as an implication about different classes.

1. Given the supposed slice thresholds, take \(m=m_0\), \(M=\ell^{m_0}\), and \(R=\max(R_0,18)\). Thus \(\ell\mid M\), \(M\ge\ell\) and \(RM\ge17\ell\). The radius is fixed **before** receiving \(a_0,\gamma_0\), and before choosing the small field parameter.
2. Use the depth-two `SlabNv ell M R` on `scaleUp ell 2 (nvLu M R)` and `LamN M R`. The frozen theorems prove torus compatibility, admissibility, Lambda compatibility and factor-12 coverage for symbolic \(\ell\), with no parity assumption.
3. The copied `slabNv_coversFour` upgrades that slab's coverage to the exact four-touch-edge requirement. Transverse invariance makes four touching edges imply four both-endpoint edges on this particular slab; no universal replacement of the coverage definitions is claimed.
4. Along `Uth`, all endpoint-touching bonds are identity. The copied `Uth_perCubeRegularTouch` supplies the actual three strict regularity inequalities with the zero logarithm, for **every** positive \(\alpha_0\).
5. The copied `corner_Ginv_eq_all` identifies the actual corner carrier with the all-plaquette carrier on the full touching-supported space, after the genuine W sandwich and Dirichlet compression. This is not equality with the frozen inside selector and not a J-operator identification.
6. The frozen crossing theorem plus that identity gives a corner carrier non-unit at some \(0\le\theta<\pi\), for every \(0<a<4\). The endpoint negative direction and the intermediate singular point are different configurations; indefiniteness is not equated with singularity.
7. Set \(\alpha_0=\tfrac12\min(a_0/(12M),1)\). It is strictly positive and satisfies the prescribed cap. The crossing path is in `ClassCoupledFour` at this cap, with the actual coverage and no shell assumption.
8. `BseedNv_props` supplies both `OnLambdaTildeIn` and `OnLambdaT`, positive energy and nonzero input. At the non-unit carrier, `not_InstIneqS_of_not_unit` applies the complete selected-form collapse, not just a raw-Hessian calculation, and contradicts every \(\gamma_0>0\).

`SlabNv_bdpt` gives a site inside the base with its outgoing neighbor outside: the construction has a **proper nonempty base** at every blocking factor in the theorem. The proof discards the `SidePow6` conjunct of the supposed slice because the analytic conclusion itself leads to contradiction; it does not refute the slice by a side-condition failure.

### Copy/import provenance

The local definitions come from the unchanged round-3 pin. The entire helper block from `AHP/round3/s1-proper/r1-refute/Attempt.lean`, beginning at `/-! ## Locality: corner and all selectors` and ending immediately before `/-- Exact pinned negative goal.`, is copied **verbatim** into the proof. It contains the corner/carrier comparison, slab four-bond coverage, touching regularity and corner crossing transfer. No old ell-two headline proof is copied as the new proof.

Frozen ingredients read and used:

| Ingredient | Frozen source |
|---|---|
| General-ell cofinal template | `lean/src/D1PGen.lean:24`, imports `D1Cons`, then `D1Final` |
| Slab definitions and admissibility | `NV1.lean:20,95`, `NV2.lean:14,22` |
| Factor-12 coverage | `NV5.lean:52`, `NV7.lean:27` |
| Torus, Lambda, positive-energy competitor | `NV6.lean:56,185,203` |
| `SlabNv` and proper boundary point | `D1Final.lean:75,78` |
| Exterior path and its touching identity | `D1Path.lean:25,46` |
| Genuine carrier crossing | `D1Main.lean:141` |
| Full-form collapse and contradiction | `D1Collapse.lean:57,74` |
| Selected operators and full instance | `D1Lit.lean:39–101` |

Direct imports are `D1Lit` for the pin; `D1Final`, `GdPlaq`, `D1Lit` for the proof. All resolve under frozen `lean/src`. No AHP file is imported; the proof embeds the entire new pin verbatim after its two additional import lines. `D1PGen`/`RI6` need not be imported merely to copy the cofinal proof pattern.

## Departures from Balaban's print and retained readings

The target is exactly the round-3 formal convention with fixed parameters, not a fresh identification of Balaban's printed operators. The following are inherited choices and source-fidelity limits. The CMP102 p.277 touching quotation and CMP109 p.251 odd-\(L\) quotation are inherited page-reading evidence; this pass did not reread page images.

| Topic | Pinned choice and limit |
|---|---|
| Coverage | Added site coverage and **four-touch-edge common-cube coverage**, coupled to regularity at factor 12. These are not supplied merely by the p.396 no-constraints-outside sentence. Four-touch coverage is not one-corner coverage. Not every selected corner plaquette is covered. |
| Delta/J and boundary interpretation | Both Delta and J use the at-least-one-corner selector attributed to CMP102 p.277, applied to the p.394 Dirichlet base. CMP99 p.392 displays whole-torus sums. The retained background products can read far links with neither endpoint inside; endpoint selection is not a theorem of dependence only on endpoint-touching backgrounds. |
| Class bonds and derivative guards | Use at-least-one-endpoint bonds, rather than frozen both-endpoint bonds. Difference and curl-of-curl guards require the entire read stencil to touch the cube. This remains a boundary interpretation of regularity “on the cube”; no bound is added on all opposite edges of corner plaquettes. |
| Gauges | Separate existential gauges and Hermitian-traceless logarithms for each class cube; globally typed functions are constrained only on the guarded bonds. No one-global-gauge or cross-cube compatibility condition. |
| Cubes and index | Frozen aligned periodic product boxes, two-stratum containment, unique index and common factor 12. The p.396 unions of several big blocks and cube-attached O(1) are not the same definition. The p.408 altered level-zero class is not substituted. |
| Dimension and group | Dimension three and SU(2), not general dimension or gauge group. |
| Lattice, mesh and distance | Finite periodic rectangular tori, side-minus-one extents, `scaleUp`, \(\eta=\ell^{-k}\), periodic l1 distance, and `TorusOK` divisibility/strict-size requirements. These are retained formal conventions, not all clauses of the p.428 sentence. |
| Tower/base | Exact frozen p.396 RM base-block layer under reading A, strict collars, aligned half-open tiling and empty padding. Not the arbitrary thinner p.394 layer, reading B or two-domain class/operator construction. The additional p.408 third-enlargement condition is not imposed. |
| Lambda | Frozen unit-lattice block union, block-sum condition and strict RM collar with the same R as the tower; empty Lambda is allowed in the target. The witness has the compatible `LamN`; no new source proof of the common-radius choice. |
| Parameters and parity | Slice keeps natural \(R\), \(M=\ell^m\), \(m,k\ge1\). Goal1 treats every \(\ell\ge2\); Goal2 restricts to the later odd-\(L>11\) range but does not impose every other condition of that paper. The p.408 restriction that R also be a power of L is not added. Only \(0<a<4\) is proved here; the old copied headline itself still quantifies all \(a>0\). |
| Thresholds and uniformity | R0 is chosen after m; a0 and gamma0 after ell,a,m,R, before depth, torus, small field, domains, background and tests. Smallness is \(12M\alpha_0\le a_0\). This is the frozen explication of “sufficiently” and the extent of uniformity, not the stronger Total threshold order. |
| Norms and differential expression | Full Frobenius norm in class bounds (sqrt2 times the trace-normalized matrix norm), strict derivative powers, frozen curl-adjoint-curl `ddA`, and trace-normalized SU(2) test energy. No explicit numerical cap or componentwise-Laplacian replacement. |
| Averaging and corrections | Keep the actual local componentwise averaging jets, weighted mass, site inverse, projections, W, multilevel Q, second jets and C. Their complete printed dictionary is not rederived. No stand-in matrix, arbitrary jet or inverse/compression interchange. |
| Support and constraints | Frozen touching `OnLambdaT`, selected coarse `CRowIn` rows, axial staircase, dropped bonds and `OnLambdaTildeIn`, with `genC` applied to the independent input. The joint constrained solve and singular fallback remain, not a new identification with the printed local single-variable solve or explicit global-Q1 parametrization. |
| Eta/tau-star and summands | Keep explicit eta/tau-star, mass subtraction, nonlinear J and bond energy. Round-5 S-3 closes the disclosed raw/normalized comparison for the localized pin under inverse guards, using the CMP109 supplement; it does not by itself identify this changed corner-selector construction with print. |
| Inverses | Totalized inverse, zero at non-units, with no existence hypothesis or conclusion. The constructed carrier is singular, so its ordinary covariance inverse does **not** exist. This neither refutes a fully inverse-presupposing statement nor settles `P428Target8SG`, `GuardPencilT`, or a guarded corner assertion. |
| Proof-local room and witness scope | No added room condition in the slice. The proof derives \(RM\ge17\ell\) from its cofinal choices. Witnesses are depth-two slabs with flat touching interior and exterior phases, not all-depth or non-flat-interior richness. Shell coercivity is not addressed. |

In particular, the result closes the **odd-blocking-factor omission of this unguarded four-bond/corner encoding**, not the sites-only coverage cell of OPEN_ITEMS M, the guarded all-plaquette question, or Balaban's unqualified printed lemma.

## Verification

Only the supplied serial wrapper was used, directly in bash:

```sh
AHP/round3/lean1.sh AHP/round7/s1-odd/pin/Statement.lean
AHP/round3/lean1.sh AHP/round7/s1-odd/proof/Attempt.lean
python3 AHP/round7/s1-odd/audit.py
```

| File | Exit | Warnings/errors | Printed dependency records |
|---|---:|---:|---:|
| `pin/Statement.lean` | 0 | 0 / 0 | 13 |
| `proof/Attempt.lean` | 0 | 0 / 0 | 41 |

All records use a subset of `propext`, `Classical.choice`, `Quot.sound`. The decisive lines are:

```text
'Round7.S1Odd.not_touchFour_every_ell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Logs and exits are adjacent to each Lean source (`.lean.log`, `.lean.exit`). [../audit.json](../audit.json) records source/log hashes, frozen direct-import hashes, all dependency records, raw forbidden-token checks, compile freshness, exact copy checks and the unchanged slice-body check. The pin's dependency lines certify only well-formed definitions; the proof's named theorems certify the goals.

These are fresh **builder compilations**, not an independent reviewer replay or a whole-project rebuild. No numerics were needed. No protected tree, earlier AHP round, Lake configuration, paper or statement sheet was edited; no commit, push, direct Lean/Lake invocation, reproduction script, dependency update or deletion was performed. Deliberate writes are confined to `AHP/round7/s1-odd/`.

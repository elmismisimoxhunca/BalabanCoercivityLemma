# S-1 proper domains — round 3 statement pin

**Pin compiled; neither goal is proved.** This is the changed-operator question on `ClassCoupledFour`, not another inclusion or non-vacuity result.

- Lean file: [Statement.lean](Statement.lean), namespace `Round3.S1Proper`.
- Positive: `GoalPos1` (line 98) is `P428TouchFour` (line 83).
- Negative: `GoalNeg1` (line 101) is **exactly `¬ GoalPos1`**, hence exactly the negation of `P428TouchFour` after unfolding.
- Sole import: frozen `lean/src/D1Lit.lean`. No AHP imports or surrogate operators.

## The goals in plain words

**GoalPos1:** prove the full p.428-style lower-bound headline, with the frozen quantifier order, for the four-bond touching class, while using every plaquette with at least one corner in the base domain in **both Delta and J**.

**GoalNeg1:** refute that same headline by genuine in-class data and an admissible test field defeating its constants and thresholds. A negative raw-Delta direction, failed proof attempt, or fixed small-torus example does not establish this goal.

“Proper domains” names the unresolved case motivating this item. **No extra properness or nonemptiness premise is inserted into the headline.** It quantifies over all admissible towers, as requested; its class admits proper nonempty domains instead of excluding them by corner coverage. There is no restriction to slabs, flat backgrounds, depth two, or extreme base domains.

### Exact class and selector

`ClassCoupledFour` (line 73) is the conjunction of:

1. Frozen `CoversOm0c`: every base-domain site belongs to a class cube.
2. `CoversPlaqFour` (line 43): **if all four boundary edges of a plaquette touch the base domain**, there is **one common class cube** that all four edges touch.
3. `PerCubeRegularTouch` (line 53): the three frozen strict regularity bounds, with endpoint-touching bonds in the pointwise and difference guards and `CurlReadsTouch` in both curl guards. The gauge and logarithm remain existential separately for each cube. The actual `ddA`, exponential, norm and powers are unchanged.

The same factor **12** is used for coverage and regularity. A cube's sites and its index are still those of frozen `IsClassCube`; they are not enlarged beyond the base domain.

`plaqCorner` (line 30) selects a plaquette when **any one** of its four corners is in the given site set. `selCorner` (line 77) applies it to the actual geometry's `Om0`. The conclusion is

```lean
InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U
```

The operator selector and coverage antecedent are intentionally **different**. In particular, a square with exactly one corner in the base belongs to the operator selector but not to the four-bond coverage antecedent; its two far edges have neither endpoint in the base. Nothing in this pin replaces four-bond coverage by the stronger common-cube corner coverage. This gap is precisely the proposed analytic obstruction to investigate, not a hidden coverage repair.

### Quantifier and constants order

The expanded order is that of `lean/src/ZT5A.lean:291`, through `P428Genuine8` (229), `P428Core8At` (170), and `CoercG8At` (89):

\[
\forall\ell\ge2\;\forall a>0\;\exists m_0\ge1\;\forall m\ge m_0\;
\exists R_0\;\forall R\ge R_0\;\exists a_0>0\;\exists\gamma_0>0\;
\forall k\ge1, L_u,\alpha_0>0,S,\Lambda,U.
\]

Here \(M=\ell^m\), \(\eta=(\ell^k)^{-1}\), and \(12M\alpha_0\le a_0\). `SidePow6` remains a conjunct before the constants block. `TorusOK`, `Admissible`, `LambdaOK2`, and class membership are the original ordered premises, except for the requested replacement of the class. The inequality then quantifies all `Bt` satisfying `OnLambdaTildeIn` **and** `OnLambdaT`.

The constants may depend on \(\ell,a,m,R\), but not on depth, torus, alpha, tower, Lambda, background or test field. No extra room bound, numerical radius threshold, inverse guard, nonzero-test premise, shell regularity, or global gauge is added.

### Actual form, not raw Delta

All operators are the genuine frozen implementations, used through `D1Lit`:

| Ingredient | Frozen source |
|---|---|
| `DeltaS`, chosen plaquette Hessian | `lean/src/D1Lit.lean:39` |
| `DpiFullS`, the actual W sandwich | `lean/src/D1Lit.lean:43` |
| `JfS`, chosen plaquette current | `lean/src/D1Lit.lean:56` |
| `dataS`, selected data assembly | `lean/src/D1Lit.lean:60` |
| `G1invS`, chosen symmetric corrected operator | `lean/src/D1Lit.lean:71` |
| `H1inS`, selected minimizer/embedding | `lean/src/D1Lit.lean:77` |
| `GenS.NmatS`, multilevel constrained covariance | `lean/src/D1Lit.lean:85` |
| `GenS.firstTermS`, eta-weighted inverse pairing | `lean/src/D1Lit.lean:88` |
| `GenS.genFormS`, first term minus mass and nonlinear J term | `lean/src/D1Lit.lean:92` |
| `InstIneqS`, actual `genC` and constrained input field | `lean/src/D1Lit.lean:96` |

`G1invS` is the corrected operator, not an assertion that its inverse exists. `Ring.inverse` remains totalized. Site operators, W, Q and its actual jets, C, support/constraint predicates, and the mass parameter remain frozen; only the selected Delta/J inputs and their downstream selected operator chain change. No inversion/compression interchange is assumed.

## Why round 2 does not settle this question

- `AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean:268`, `properFourAt_two`, supplies **flat** proper nonempty four-bond instances with compatible Lambda and positive-energy admissible test fields for every \(m\ge1\), \(R\ge18\), and positive cap, at \(\ell=k=2\). Its `goalPos1_proved` is at line 293. These are prior compiled non-vacuity results, not changed-operator inequalities; they were read, not recompiled here.
- `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean:418`, `ClassCoupledFour.toFrozen`, transfers the class. Its `targetFour_of_frozen` (line 493) retains **inside** operators. It does not prove this pin's corner-operator conclusion.
- Round-2 `ClassCoupledCorner` collapses the base to empty/whole torus (`AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean:506,519`). The round-2 S-1 proof uses that stronger coverage (`AHP/round2/s1-touching/r1-prove/Attempt.lean:501,575,689`). Those proofs cannot be applied by substituting `CoversPlaqFour` for `CoversPlaqCorner`.

The goals therefore remain the real open headline and its negation. No already-proved comparison, saturation package, shell fallback, or non-vacuity question is offered as an alternative closure.

## Acceptance contract and suggested approaches

### Positive direction

Use the frozen headline plus the known four-bond-to-frozen class inclusion if possible. The missing step must control the **complete selected form** on all admissible inputs, uniformly with the pinned constants order. Nonnegativity or domination of extra corner contributions is a suggested route, not an assumption or result. Raw-Delta monotonicity alone need not propagate through J, corrected inverses, the constrained covariance, and the nonlinear term.

### Negative direction

A sufficient explicit refutation family has one fixed allowed \(\ell\ge2\), \(a>0\), and the following order:

1. Given any candidate \(m_0\ge1\), choose \(m\ge m_0\).
2. Given its candidate \(R_0\), choose \(R\ge R_0\) **before receiving the caps/constants**.
3. For every \(a_0>0\), \(\gamma_0>0\), construct \(k,L_u,\alpha_0,S,\Lambda,U,\widetilde B\) satisfying all headline hypotheses, actual four-bond coverage and all three regularity bounds, and
   \[
   \operatorname{GenS.genFormS}_{\rm corner}(C\widetilde B)
   <\gamma_0\operatorname{bondEnergy}(\widetilde B).
   \]
   Supply the actual support and dropped/axial-bond constraints; a positive-energy admissible competitor avoids zero-field vacuity.

The slab construction and threshold handling at `lean/src/D1Final.lean:118–168` are templates. `not_P428Target8Literal` at line 169 refutes **selAll with the frozen class**, not this headline. Its unit-crossing mechanism must be proved anew for corner selection and the four-bond class; simply citing that theorem or a nonpositive raw Hessian is insufficient. A non-unit point may be used since this pin is unguarded, but its actual totalized full form must violate the inequality. Such a result would refute this encoding, not automatically an existence-presupposing printed theorem.

The supplied earlier numerics report a slab corner raw-Delta value \(-4\) at \(\theta=\pi\), and phase-limited searches with no accepted small-phase full-headline counterexample. These experiments were **not rerun here**, and neither positivity in the samples nor raw negativity proves either goal. In a controlled diagonal representative in the **local regularity gauge**, pointwise smallness implies

\[
|\phi_e|<\frac{12M\alpha_0}{\sqrt2\,\ell^j}
\le\frac{a_0}{\sqrt2\,\ell^j}.
\]

This is not a gauge-invariant bound on arbitrary input coordinates and does not control far bonds outside every touching cube. A large phase on a controlled link cannot defeat every positive cap. Prior pi/4 Cartan observations were model- and guard-dependent, not a general non-Abelian theorem.

Prioritize one-corner squares and their uncontrolled far edges, as requested. Boundary squares with two adjacent corners also need not satisfy the four-touch antecedent; the pin does not prohibit investigating them or the existing slab path. `Zb`/`Uth` (`lean/src/D1Path.lean:25,46`) change only bonds with neither endpoint in the base, so they suggest a way to leave touching regularity intact. **Actual in-class membership and the full operator failure must still be proved**, not inferred from the old frozen-class example or flat non-vacuity theorem.

## Departures from Balaban's print and retained readings

This lists the changes and retained formal conventions of the complete target, not only its difference from frozen Lean. References: statement sheet A1–A13 and `paper/OPEN_ITEMS.md` B, K–N, R, S. The CMP102 p.277 endpoint/corner quotation is inherited from the supplied source reading; no fresh page-image verification is claimed here.

| Topic | Pinned choice and source-fidelity limit |
|---|---|
| **Coverage (D2)** | Retain added site coverage; use added **four-touch-edge** common-cube coverage, coupled to regularity at factor 12. Neither clause follows merely from p.396's sentence about no constraints outside the domain. Four-touch coverage is **not** the one-corner plaquette convention. Unlike round 2, not every operator-selected plaquette is required to have all its edges touching one cube. |
| **Delta/J selection (D1)** | Both use the one-corner selector from CMP102 p.277, applied to the p.394 Dirichlet domain. This changes frozen `plaqIn`, but remains a boundary interpretation: the displayed CMP99 p.392 formulas (3.10)/(3.11) sum over the whole torus. There is no claim that this pin reproduces the unrestricted sums or depends only on endpoint-touching background links. |
| **Class bonds and stencil guards** | Replace both-endpoint bonds by at-least-one-endpoint bonds, matching the supplied CMP96 p.224 / CMP102 p.277 convention. Difference and curl-of-curl guards require all read bonds to touch the cube; this boundary treatment of “on the cube” is retained as an interpretation. No bound on every opposite edge of every corner plaquette is added. |
| **Gauge quantification (N6)** | Separate existential gauge and Hermitian traceless logarithm per class cube, not one global gauge. Their functions are globally typed but constrained only where guards hold. This follows the per-cube reading of (3.35); no additional consistency between cube gauges is imposed. |
| **Cubes, indices and factors (D3)** | Frozen aligned periodic product boxes, two-stratum containment and unique index, one common factor 12. The print p.396 describes unions of several big blocks and cube-attached O(1) at least 10; p.409 supplies 12 in its application. Per-cube factors, non-box unions, and the p.408 altered level-zero class are not substituted. |
| **Dimension/group** | Three dimensions and SU(2), not an arbitrary-dimensional or general-group theorem. |
| **Lattice, mesh, distance (N4, D7)** | Finite periodic rectangular tori; extents store side minus one; `scaleUp` and eta equal to ell to minus k; periodic l1 distance; `TorusOK` divisibility and strict-size requirements. These are the frozen finite-lattice conventions, not all stated in the p.428 sentence. |
| **Tower/base domain (N3/N4)** | Frozen strict collars, aligned half-open block tiling, empty padding, and exact p.396 RM base-block layer under reading A (fine lattice in its own units). Not the p.394 arbitrary thinner layer, reading B, or a two-domain class/operator construction. The additional p.408 third-enlargement condition is not imposed. |
| **Lambda (N2)** | Frozen unit-lattice block union, block-sum condition, and strict RM collar using the same R as the tower. Empty Lambda is allowed. The common-radius identification is inherited as a reading, not newly established. |
| **Parameter ranges (D5/D6/D8/N5)** | All natural ell at least 2, all real a>0, k at least 1, M=ell^m with m at least 1; natural R, not only powers of ell. CMP109 p.251's odd L>11 and the p.408 powers-of-L restriction for R are not imposed. |
| **Constants/uniformity (D4)** | Exact frozen threshold order: R0 after m, a0 and gamma0 after ell,a,m,R but before depth, torus, alpha, geometry and fields. Smallness is 12M alpha0 <= a0. This explicates “sufficiently” and extends the displayed “independent of k and U” to those further objects; no Total-style stronger uniformity is silently substituted. |
| **Norms/differential expression (sqrt2, D9)** | Full Frobenius norm for the class logarithm (sqrt2 times the trace-normalized matrix norm), strict derivative powers, frozen `ddA` curl-adjoint-curl rather than a componentwise Laplacian. Test energy uses the frozen trace-normalized SU(2) norm. The norm factor can be accommodated in an existential cap; no numerical cap is prescribed. |
| **Averaging/site operators/corrections (D10/D11)** | Frozen actual local per-component jets, weighted mass, site inverse, projection, W, multilevel Q, second jets, and C construction are retained. Their detailed printed dictionary is not rederived; no toy maps or arbitrary jets are substituted. |
| **Support/constraints (N1)** | Frozen touching `OnLambdaT`, coarse `CRowIn`, axial staircase, selected dropped bonds and `OnLambdaTildeIn`. `genC` is applied to the free input, not a separately imposed Q1-kernel condition on that input. The joint constraint solution and its singular fallback remain; no new full support/constraint identification is claimed. |
| **Eta/tau-star and all summands (S-3)** | Retain the explicit eta and tau-star in `firstTermS`, and frozen mass subtraction, nonlinear J term and bond energy. Round 2 identifies the frozen inside-selector first term under inverse guards and its linked H/C conventions. That does not establish the changed corner-selector dictionary or common printed units for the remaining summands. |
| **Inverses** | Totalized inverse conventions, including zero at non-units, without a well-definedness premise or conclusion. This differs from a formulation presupposing existence of all printed inverses. Neither the guarded all-plaquette target nor its already-proved full-guard version is the goal here. |
| **Proof-local room (D12)** | No extra room premise such as 17 ell <= RM and no fixed R>=18 appear in the headline. A proof may choose large existential thresholds and must justify any derived room condition. |

A proof or refutation closes this **explicit formal pin**, not every printed-statement reading above. In particular, replacing the four-bond class by the collapsing corner class, or by the stronger read-bond shell, changes the question and is not acceptable.

## Copy provenance and verification

All seven local dependency declarations are copied verbatim, including the declaration bodies and their implicit extent context:

| Local declaration | Source declaration |
|---|---|
| `TouchBond` (40) | `AHP/round2/s2-nonvacuity/pin/Statement.lean:41` |
| `CoversPlaqFour` (43) | same file, line 44 |
| `CurlReadsTouch` (48) | same file, line 59 |
| `PerCubeRegularTouch` (53) | same file, line 64 |
| `ClassCoupledFour` (73) | same file, line 84 |
| `plaqCorner` (30) | `AHP/round2/s1-touching/pin/Statement.lean:33` |
| `selCorner` (77) | same file, line 79 |

`P428TouchFour` is the round-2 S-1 expanded `P428TouchConsistent` declaration with **only** its name and `ClassCoupledCorner` replaced. The fresh negative wrapper is the exact negation of the fresh positive wrapper. Frozen ingredients are imported as their real definitions; no other AHP definition is needed.

Compilation, using the supplied single-process lock wrapper only:

```sh
AHP/round3/lean1.sh AHP/round3/s1-proper/pin/Statement.lean
```

Evidence: [compiler log](Statement.lean.log), [exit record](Statement.lean.exit), [source audit](audit.json), reproducible by `python3 AHP/round3/s1-proper/pin/audit.py`.

- Exit **0**, no warnings or errors.
- **10** local definitions, **10** `#check` commands, **10** dependency records, all subsets of `propext`, `Classical.choice`, `Quot.sound`.
- All seven verbatim copies and the headline-only name/class replacement checked textually against current round-2 sources.
- Sole direct import resolves to frozen `lean/src/D1Lit.lean`; no forbidden tokens in the pin.
- Source SHA-256: `dff1d868790779a2def248238b348234402a065760bdb0d0c9b675136fe7cf9f`.
- Log SHA-256: `56ace50794b6845104c39852e8277768a7696d866815b4cf67721dd7b00fea98`.

The goal definition dependency records are:

```text
'Round3.S1Proper.GoalPos1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round3.S1Proper.GoalNeg1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are **definitions of propositions**, not proofs of either proposition. Later attempts must copy the needed pin declarations verbatim, prove an exact goal, compile only through the round-3 wrapper, and print the proof dependencies.

No numerical experiment, direct Lean/Lake invocation, full build, reproduction run, dependency update, deletion, commit or push was performed. Deliberate writes are confined to `AHP/round3/s1-proper/pin/`. No protected source, paper, statement sheet or other item's file was edited.

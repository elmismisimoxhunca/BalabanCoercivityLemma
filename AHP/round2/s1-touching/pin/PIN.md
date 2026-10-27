# S-1 round 2: statement pin

## Status and scope

`Statement.lean` compiles, exit **0**, with no warnings. It defines questions; it proves **none** of them. All 22 dependency prints are subsets of `propext`, `Classical.choice`, `Quot.sound`. Definition-dependency checks are not proofs of the propositions defined.

Namespace: `Round2.S1`. Imports: only `ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, `D1Lit` from the frozen `lean/src/` tree. No other AHP module is imported. No numerical experiment was run in this pin pass.

The primary statement consistently uses the CMP102 p.277 endpoint/corner convention **within an explicitly coverage-repaired formalisation**. It is not certified to be Balaban's unmodified printed theorem. In particular, the common-cube coverage below is additional, and it appears to collapse the base domain to empty or whole torus. The reduced goal makes that issue a theorem obligation rather than silently assuming it away.

## Exactly what is pinned

### Primary statement — `P428TouchConsistent` (Statement.lean:84)

- `TouchBond sites e` means at least one endpoint belongs to the cube's **site** set.
- `plaqCorner Omega` means at least one of the four corners belongs to Omega.
- `PerCubeRegularTouch` is frozen `PerCubeRegular2` with `CubeBond` replaced by `TouchBond` in the pointwise and both forward-difference guards, and with `CurlReadsTouch` in every backward/forward curl guard of the third bound. `ddA`, its signs and powers, strict inequalities, matrix exponential, and the per-cube existential gauge remain unchanged.
- `ClassCoupledCorner` means **site coverage AND `CoversPlaqCorner` AND touching regularity**, all at the same cube factor.
- **Coverage choice, unambiguously:** every plaquette with **one corner** in `S.Om 0` must have **all four boundary bonds touching one common frozen class cube**. This is not merely the condition that the plaquette has one corner in a cube, and it is not the weaker `CoversPlaqFour` antecedent. The latter would not cover all plaquettes selected by the pinned operators. Site coverage is unchanged; no separate bond-cover predicate is necessary because covering a site covers every incident bond in the touching sense.
- The conclusion is the actual `D1Literal.InstIneqS` with both selectors equal to `selCorner`. Thus Delta **and** J change. No raw-Delta surrogate, added gauge penalty, arbitrary matrix, or invented inverse is substituted.
- Fine-field support already uses touching bonds (`ZXR2Ops3.lean:26–34`). `OnLambdaT` (`ZR2A.lean:121`), `CRowIn` (`ZStatementP428.lean:211`), `OnLambdaTildeIn`, `LambdaOK2`, and `genC` stay frozen. They are not switched to both-endpoint support.

All binder order is the expanded frozen `P428Target8` order:

\[
\forall\ell\ge2,\ a>0,\quad
\exists m_0\ge1,\ \forall m\ge m_0,\quad
\exists R_0,\ \forall R\ge R_0,\quad
\exists a_0>0,\ \exists\gamma_0>0,\quad
\forall k\ge1,\ L_u,\ \alpha_0>0,\ S,\ \Lambda,\ U.
\]

The `SidePow6` conjunct stays in its original place. The cap is \(12\ell^m\alpha_0\le a_0\), \(M=\ell^m\), \(\eta=(\ell^k)^{-1}\). Torus compatibility, admissibility, Lambda compatibility and class membership are required. The final inequality still universally quantifies the actual admissible test field in `InstIneqS` (`D1Lit.lean:96–101`). Constants cannot depend on that field, depth, torus, tower, region, configuration, or alpha.

### Goal pairs

| Positive goal | Plain meaning | Exact negative goal |
|---|---|---|
| `GoalPos1` (line 99) | Prove `P428TouchConsistent`, with the full quantifier order, class and changed operators above. | `GoalNeg1 := ¬ GoalPos1` (line 101). |
| `GoalPos2` (line 134), **preferred reduced route** | Prove **both** `TouchCoverageCollapse` in headline geometry and `P428TouchConsistent ↔ P428Target8Extreme`. The latter is the frozen headline restricted to towers whose **base** is empty or whole torus. | `GoalNeg2 := ¬ GoalPos2` (line 137). This refutes the reduction package, not automatically the primary headline. |
| `GoalPos3` (line 190), **separate shell fallback** | Prove the exact `P428Target8Shell` from the Stage-A SPEC: frozen coverage, `ReadBond` regularity, and both corner selectors. | `GoalNeg3 := ¬ GoalPos3` (line 192). This concerns the fallback only. |

`P428Target8Extreme` (line 108) uses the **frozen `ClassCoupled` and frozen `InstIneq`**, with only the extra `ExtremeBase S` premise after admissibility. It does not quietly rename a touching-class version as the frozen statement. No condition makes the higher domains constant. `TouchCoverageCollapse` (line 125) is a conclusion to establish from corner coverage and headline geometry, not an extra assumption in `P428TouchConsistent`.

The primary goal is not a re-export of Stage B: Stage B kept the frozen operators in its touching-class headlines. The new reduction also is not an existing Stage-B result: neither universal saturation nor the changed-operator headline equivalence was established there. A theorem of `GoalPos2`, together with the already proved frozen headline restricted to extreme towers, supplies `GoalPos1`. A bare class inclusion or equality of selectors in a specially chosen example does not satisfy any positive goal here.

**Shell fallback limit:** its regularity hypotheses are stronger than the printed endpoint convention, because `ReadBond` includes opposite edges with neither endpoint in the cube. Its coverage remains frozen and allows proper nonempty base domains. Consequently the shell and the primary corner-coverage classes are not asserted to be nested as whole classes; “fallback” is not a proved logical implication between these two headlines. Closing it alone does not close the printed touching reading.

## Why reduction is needed: coverage saturation

The pinned common-cube corner coverage **does collapse the geometry at the level of the following mathematical argument**. This pass does not claim a compiled proof of that argument; the universal theorem is expressly part of `GoalPos2`.

1. Every frozen class cube is a product box (`DescribedAt`, `ZStatementP428.lean:131`). With nested domains its sites lie in `S.Om 0` (`D1Final.classCube_sub_om0`, `D1Final.lean:36`).
2. If each boundary edge of a unit square touches a product box, the square's vertices inside the box contain a vertex cover of the four-cycle. Such a cover includes one diagonal pair. Coordinate-product membership then puts **all four vertices** in the box. This exact local step is the Stage-B `touchCover_all_corners` / `touchCover_cubeBond` argument in `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean:256–288`.
3. `CoversPlaqCorner` therefore forces all corners of every plaquette having any corner in Omega0 to lie in Omega0. In three dimensions every directed nearest-neighbour bond is on a plaquette with its base as a corner. Membership in Omega0 propagates under every positive coordinate shift.
4. Positive coordinate shifts connect every site of a finite periodic rectangular lattice to every other site. Hence nonempty Omega0 is the whole torus; otherwise it is empty.

This argument uses product boxes and common-cube coverage. It is **not** a consequence of Balaban's endpoint/corner convention alone. Do not infer that his printed domain must be empty or full. Do not repair the collapse silently by moving cubes outside Omega0, replacing coverage by one-corner-in-one-cube coverage, changing to unions, or dropping coverage; each is a different statement requiring another pin.

On the two resulting base domains, `plaqCorner` and frozen `plaqIn` select the same plaquettes (empty or all, respectively). A proof must propagate that fact through the genuine D1Lit operator chain, including the selected J, corrected inverse and full form, and handle the headline hypotheses/quantifiers. Whole-torus Omega0 does **not** make every individual class cube the whole torus; touching and frozen regularity are not asserted equivalent on individual cubes. The reduction is a headline equivalence, not a pointwise equality of the two classes. Its reverse implication may use the already established frozen theorem; no new reverse class inclusion is demanded or implied.

This excludes the familiar proper slab from the primary class, independent of its link angles. The flat proper slab from `Fidelity.S1.shell_slab_nonvacuous` belongs to the **shell** class, not this corner-coverage class.

## Refutation contract and phase restrictions

To close `GoalNeg1`, produce a Lean proof of the negation of the **entire** primary headline, not one bad raw quadratic direction. A sufficient explicit construction follows `D1Final.lean:118–167`:

- Fix an allowed \(\ell\ge2\) and \(a>0\).
- Against every candidate \(m_0\ge1\), choose \(m\ge m_0\); against every subsequent \(R_0\), choose \(R\ge R_0\).
- After those choices, defeat **every** positive \(a_0,\gamma_0\) by actual \(k\ge1,L_u,\alpha_0,S,\Lambda,U,\widetilde B\) satisfying torus compatibility, admissibility, Lambda compatibility, the cap, `ClassCoupledCorner`, `OnLambdaTildeIn`, and `OnLambdaT`, with the strict reverse of the claimed `InstIneqS` inequality. In particular the test field must be nonzero.
- A fixed small torus or a fixed large phase does not defeat the outer thresholds and arbitrarily small caps. Invertibility is **not** added as a premise to this pin; a singular-value construction must still fail the actual totalised full form with all displayed hypotheses.

For a diagonal representative **in its local regularity gauge**, the pointwise bound gives

\[
 |\phi_e| < \frac{12M\alpha_0}{\sqrt{2}\,\ell^j}
 \le \frac{a_0}{\sqrt{2}\,\ell^j}.
\]

This is a restriction on controlled links in a chosen logarithm/gauge, not a gauge-invariant restriction on arbitrary input link coordinates. The derivative and third bounds must also hold in that same cube gauge. Prior Cartan cap experiments did not test the full headline. Their non-Abelian raw-Delta negativity also occurred for the frozen selector and is not a separating counterexample.

Large phases on links invisible to touching regularity are a legitimate candidate mechanism **only after geometry and coverage are checked**. `Uth` is flat on all bonds touching Omega0 but changes bonds outside it (`D1Path.lean:25,46`). It can leave touching-only regularity satisfied on a proper slab, yet the slab fails this pin's corner coverage. On whole-torus Omega0, site coverage makes every bond visible to some cube; on empty Omega0, admissibility and Lambda containment leave no nonzero supported test field. Thus the saturation issue must be resolved before spending effort on slab phase scans for `GoalNeg1`.

Citation correction to the shorthand brief: `not_P428Target8Literal` at `D1Final.lean:169` has the **all-plaquette `selAll`** headline as its type, not this pin's `selCorner` headline. The old raw touching Delta value at the slab boundary is evidence for a mechanism; it is not already a theorem of `GoalNeg1`.

## Departures from the print and retained readings

The source convention is CMP102 p.277, quoted in `paper/OPEN_ITEMS.md` S-1. The catalogue below also retains the disclosures of the statement sheet A1–A13 and `OPEN_ITEMS` R/S. These are source-reading records, not newly proved identifications with page images.

| Place | Pinned choice / departure | Why retained; limit |
|---|---|---|
| **Coverage (D2), principal new risk** | Site coverage retained; each one-corner plaquette must have four touching bonds in **one** class cube, with the same factor 12 as regularity. | Explicit consistent coverage-repaired test. CMP99 p.396 says no constraints outside Omega0, but does **not** state this common-cube coverage. It imposes saturation, not a property supplied by the quoted convention. |
| Delta and J (D1) | `DeltaS selCorner` and `JfS selCorner`, via `InstIneqS`; `D1Lit.lean:39,56,96`. | Applies CMP102's plaquette convention to the domain in the p.394 Dirichlet reading. The displayed (3.10)/(3.11), CMP99 p.392, sum over all torus plaquettes/bonds; a corner-domain selector is still an interpretation of the boundary prescription, not their literal unrestricted sum. |
| Cube bonds / derivative guards | Endpoint-touching for all class guards; curl-of-curl evaluated only when every bond it reads is touching. | Removes frozen both-endpoint choice. The stencil-interior guards remain the formal treatment of “on the cube”; no boundary extension law is supplied by the print quotation. A cube-specific global extension of g and A is existential, with bounds only at guarded locations. |
| Cubes and factors (D3) | Frozen aligned periodic product boxes, unique index, sites inside adjacent strata; one global factor 12. | Keeps the audited fixed-factor problem. Print p.396 describes unions of several big blocks and a cube-attached O(1) at least 10; p.409 mentions 12. Per-cube factors, non-box unions and altered zero-level class are not substituted. The product-box restriction is material to the collapse argument. |
| Dimension / gauge group | Three dimensions and SU(2). | Frozen model, not a theorem for general dimension/group. |
| Lattice and distance (N4, D7) | Periodic rectangular tori, extents storing side minus one, `TorusOK`, eta equal to ell to minus k, periodic l1 distance. | Finite frozen setting and blocking compatibility. Periodic wrap and divisibility are formal conventions, not supplied by the local p.428 sentence. |
| Tower and Omega0 (N3/N4) | Frozen `Admissible`: strict collars, aligned half-open block unions, tiling, empty padding above k, p.396 exact RM block layer at level zero. Reading A: T1 is the fine lattice in its own unit spacing. | Keeps geometry fixed while testing S-1. The p.394 thinner-layer option and alternative reading B are not included. Third-enlargement p.408 conditions are not added. |
| Parameters (D5/D6/D8/N5) | All natural ell at least 2; all a>0; k at least 1; M=ell^m, m at least 1; natural R above threshold, not restricted to powers of ell. | Exactly frozen quantifiers as requested. CMP109's odd L>11 restriction and p.408 R-powers reading are not imposed; this pin does not settle those source questions. |
| Constants / order (D4) | R0 chosen after m; a0 and gamma0 after ell,a,m,R, before depth, torus, alpha, geometry, fields; cap 12M alpha0. | Formalises “sufficiently large/small” and “independent of k and U” as the frozen statement does. Stronger Total/uniform variants are not silently substituted. |
| Norms and differential expression (D9, sqrt2) | Full Frobenius norm for class A; trace-normalised SU(2) bond energy for the inequality; frozen `ddA` exterior curl-of-curl. | Norm factor sqrt2 is absorbed in the existential cap. Keeps frozen differential convention, not a componentwise vector Laplacian; no new printed-units theorem is claimed. |
| Q, jets, C, nonlinear correction (D10/D11) | Frozen actual per-component local one-step/composite jets, weights, constraint construction, and top-level placement. | Avoids arbitrary ingredient surrogates. Their detailed printed dictionary remains inherited, not re-derived here. C's singular constraint fallback is retained. |
| Eta / tau-star (S-3) | Retains `GenS.firstTermS = eta * <tau* B, inverse(NmatS)(tau* B)>`, `D1Lit.lean:88–94`, with frozen mass and nonlinear terms. | Isolates S-1. The printed (3.156) displays neither eta nor tau-star; full normalisation fidelity remains unresolved, not settled by this pin. |
| Inverses / domain | Uses frozen totalised `Ring.inverse`, zero when not invertible; no well-definedness guard and no new invertibility conclusion. | Same headline as requested. A failure at an undefined printed inverse refutes this encoding, not necessarily the existence-presupposing printed theorem. No identification of inverse-of-compression with compression-of-inverse is assumed. |
| Lambda and test-field support (N1/N2) | Touching `OnLambdaT`, touching coarse rows, frozen axial/dropped-bond conditions, block-union Lambda, same R in its collar; empty Lambda allowed. | Already uses the requested endpoint convention. Common-radius matching and the full printed support/operator identification remain source readings. |
| Shell fallback only | Bounds on `ReadBond`, including edges with neither endpoint in the cube; **frozen** site/inside-plaquette coverage. | Stronger regularity than the print, used to control every edge read by corner operators without excluding proper domains. Not claimed faithful or equivalent to the primary class. |

The proof-local room condition \(17\ell\le RM\) (D12) is **not** an extra hypothesis in any pinned headline. No bound such as R>=18 is silently inserted. A later proof may choose a sufficiently large existential threshold and must justify that choice.

## Copy provenance, build and acceptance

Verbatim local definition copies:

- `TouchBond`, `plaqCorner`, `ReadBond`, `CurlReadsRead`, `PerCubeRegularShell`, `ClassCoupledShell`: `AHP/fidelity/s1-touching/lean/ShellComparison.lean`.
- `CoversPlaqCorner`, `CurlReadsTouch`, `PerCubeRegularTouch`, `ClassCoupledCorner`: `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`, retaining its implicit `L` context.
- `selCorner`, `P428Target8Shell`: the Lean block in `AHP/fidelity/s1-touching/SPEC.md`.

Other ingredients are imported genuine frozen definitions, not copied or altered implementations. New definitions are the primary headline, the extreme-domain restriction, the collapse obligation and the six goal wrappers.

Compilation performed, one file only:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s1-touching/pin/Statement.lean > ../AHP/round2/s1-touching/pin/Statement.lean.log 2>&1
echo $? > ../AHP/round2/s1-touching/pin/Statement.lean.exit
```

Evidence: `Statement.lean.log` and `Statement.lean.exit`. The six goal definitions each print exactly `[propext, Classical.choice, Quot.sound]`; their `#check` types are `Prop`. Every local definition has a dependency print. The declaration `ExtremeBase` has no dependencies; some selectors/guards use only two of the permitted axioms. None of these commands proves a goal.

Post-compilation audit against the current files: all 12 copied definitions above are byte-identical to their source declaration blocks; the primary headline differs from the SPEC shell headline only by its name and class predicate; all three negative definitions are exactly the negation of their paired positive definition. The whole-file forbidden-token scan has zero hits. Source SHA-256: `0ad24d3129dc87c72d1fdc8281a9f7f08a66526a17ef2a697431b8ad8be5ea7c`. Log SHA-256: `3d9cf85d31d219a363943db5853ff2b8f189d5a06c0cfd8a9f658f9c139224ef`.

A successful attack must copy the pin's needed definitions and goal **verbatim** into its own standalone file, prove that goal, compile serially with the prescribed command, and print dependencies for the theorem and every helper. A positive/negative result must not be narrowed to flat fields, fixed depth, small tori, raw Delta, or a toy operator. A shell-only result must retain its fallback label; a reduction-only result must report the coverage collapse and its source-fidelity limitation.

Only files under `AHP/round2/s1-touching/pin/` were deliberately written. No frozen source, Lake configuration, other AHP item, paper, statement sheet, expected file, or extras file was edited. No build, reproduction, update, commit, or push was run.

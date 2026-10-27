# S-1 proper domains — round 1 refutation

## Status

Final candidate: `Attempt.lean`, namespace `Round3.S1Proper`.
Main declaration: `goalNeg1_proved : GoalNeg1` at line 354.

**Closed goal: `Round3.S1Proper.GoalNeg1`.** Final compilation exited **0**,
with no errors or warnings. The source/log audit passed every check. All **44**
printed dependency records, covering all **23** local declarations plus direct
frozen helpers, contain only permitted dependencies. The main record is:

```text
'Round3.S1Proper.goalNeg1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first completed compilation failed only on an ambiguous imported name in
the touching-regularity proof. Qualifying that name resolved it. The final
successful source SHA-256 is
`a114b3d28b83d02b8d38df0f26cfac3d1485bb4cb72bdcd0150bd392e79a0280`.
The final log SHA-256 is
`bc44f7fddefd646ba13a7e679ae1476168d2d9b96deec4c2ec9884b08da9ab2e`.
`audit.json` also records the numerical-artifact and pin hashes.

The goal is copied exactly: `GoalNeg1 = ¬ GoalPos1`, with
`GoalPos1 = P428TouchFour`. No hypothesis, quantifier, constant order, selector,
class definition, or test-field condition has been changed. The entire pinned
declaration block is copied byte-for-byte, not just up to whitespace.

## What was tried

### 1. Numerical reconnaissance, before formalisation

`search.py` / `search.json` / `search.log` / `search.exit` test the diagonal
Cartan sector on side-4, 6, 8 and 16 periodic tori. Both slabs and a two-coordinate
box extrusion are tested. The latter supplies one-corner squares with far edges
outside the touching-bond set. These are diagnostics, **not admissible headline
instances**.

The script uses the genuine Cartan pairing formula
`lean/src/CvO23.lean:162` (`inner_deltaKLocCLM_sigma3`), the path
`lean/src/D1Path.lean:25,46` (`Zb`, `Uth`), the singleton field
`lean/src/D1Eval2.lean:29`, and the actual curl
`lean/src/AdalyFormal/Balaban/CovariantOperators.lean:315`. Selector sources are
`../pin/Statement.lean:30,40,43`; `DeltaS` is `lean/src/D1Lit.lean:39`.
All these file/line citations are also in the script or its JSON record.

At the five sampled angles from 0 to pi, the outward singleton on each slab
has corner-Delta value

\[
  4\cos\theta,
\]

including **-4 at pi**. A deterministic random field supported on touching bonds
has exactly equal all-plaquette and corner-plaquette pairings in all 40 tested
(shape, size, angle) cases; recorded maximum absolute gap is **0.0**.

Crucially, every touching bond has phase **zero**, at every angle. Large phases
occur only on bonds with neither endpoint in the domain. Thus the small
positive class cap does not rule out this particular path. No claim about small
phases in arbitrary gauges is required.

The script does **not** simulate W, J, mass, Q, C, the corrected covariance, or
any inverse. Its purpose was to identify the support identity to prove in Lean,
not to substitute a finite matrix for the actual complete form. Its address-space
limit is **1 GiB**, final measured peak RSS **23,468 KiB**. An initial
heavy-slot request was interrupted before execution while both slots were
occupied; the successful bounded short runs were direct. No long numerical script was run outside the heavy wrapper.

### 2. Exact support identity

The frozen module `D2Lit.lean:174` already proves that W maps touching-supported
fields into touching-supported fields. This led to a simpler refutation than
constructing a new one-corner geometry.

| New declaration in `Attempt.lean` | Line | Meaning |
|---|---:|---|
| `edge_not_touch_of_not_corner` | 142 | Every edge of an unselected square has neither endpoint in the domain. |
| `deltaKLocCLM_eq_univ_of_zero_off` | 162 | If a field vanishes on every edge of every omitted square, the **operator application** of selected Delta equals that of all-plaquette Delta. |
| `deltaKLocCLM_corner_eq` | 203 | Apply that identity to any genuine touching-supported bond field. |
| `corner_Dpi_eq_all` | 212 | The identity survives the actual W sandwich and Dirichlet compression. |
| `corner_Ginv_eq_all` | 222 | The actual carrier `Ginv` is identical for corner and all-plaquette Delta, with the same arbitrary J selector. |

These identities are uniform in the background. They impose no smallness,
coverage, geometry or inverse assumptions. They compare **corner with all**,
not corner with the frozen **inside** selector. They do not assert unrestricted
Delta equality on arbitrary unsupported fields, J equality, or complete-form
equality between different J selectors.

### 3. Actual class membership, cofinal geometry and full-form failure

The three coverage helpers at lines 240, 276 and 285 are copied verbatim from
`AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean`. On a slab, four-edge touching
forces all corners inside; therefore the existing frozen slab coverage supplies
actual `CoversPlaqFour`, rather than assuming it.

`perCubeRegularTouch_of_one_on_touch` (line 295) proves all three **strict**
regularity inequalities whenever U is one on touching bonds. Each class cube is
contained in Omega0; the gauge is identically one and the logarithm is identically
zero. The difference and the actual curl-adjoint-curl bounds are zero as well.
No shell-bound replacement is made. `Uth_one_on_touch` (323) and
`Uth_perCubeRegularTouch` (330) apply this to **every angle** of the exterior path,
for **every positive alpha**.

`exists_nonunit_corner_Ginv` (338) uses the actual-operator identity to transfer
`lean/src/D1Main.lean:141`'s spectral crossing (the exact declaration header is
also printed by the final file). This is not an inference from the numerical
raw-Delta value. The imported proof uses W, T, the actual mass bound, positivity
at the flat endpoint, a negative carrier direction at pi, symmetry and the
finite-dimensional continuous-path theorem. It supplies some
\(0\le\theta<\pi\) at which the actual corner carrier is not a unit. We do not
claim an explicit decimal angle or strict positivity of theta.

The headline contradiction follows the genuine `D1Final.lean:118–168` family:

1. Fix \(\ell=2\), \(a=1\).
2. Given a candidate \(m_0\ge1\), take \(m=m_0\), \(M=2^m\).
3. Given the candidate radius threshold, take \(R=\max(R_0,18)\), **before**
   receiving \(a_0\) and \(\gamma_0\).
4. Use the frozen depth-two slab `SlabNv 2 M R`, actual torus `nvLu M R`, and
   actual Lambda `LamN M R`. `SlabNv_bdpt` gives an inside site and an adjacent
   outside site, so the domain is genuinely nonempty and proper.
5. For any proposed positive cap choose
   \(\alpha_0=\tfrac12\min(a_0/(12M),1)>0\). The proof checks
   \(12M\alpha_0\le a_0\), torus compatibility, admissibility, Lambda
   compatibility, site coverage, four-bond coverage and all touching regularity.
6. At the transferred singular angle use the genuine `BseedNv`, whose frozen
   theorem proves **both** `OnLambdaTildeIn` and `OnLambdaT`, nonzeroness and
   positive bond energy.
7. `lean/src/D1Collapse.lean:74`, `not_InstIneqS_of_not_unit`, applies with **both
   selectors equal to the pinned `selCorner`**. Its proof uses
   `genFormS_collapse` (line 57): the complete form is
   \(-a\langle C\widetilde B,C\widetilde B\rangle\le0\), whereas
   \(\gamma_0\operatorname{bondEnergy}(\widetilde B)>0\). All corrected
   inverse, first-term and nonlinear-J contributions are accounted for.

This path uses boundary squares with **two adjacent** inside corners, whose far
edge is uncontrolled. One-corner squares were investigated numerically but are
not needed for the cofinal refutation. Four-bond coverage does not cover either
kind of boundary square. The round-2 stronger corner-coverage class would exclude
the slab; that class is deliberately **not** used here.

## Limits of the compiled closure

Exactly the unguarded formal `P428TouchFour` pin is refuted. The construction uses
a non-unit actual carrier and the existing totalized inverse convention. It
**does not** refute the invertibility-guarded target, an existence-presupposing
printed assertion, or the frozen inside-operator theorem. It is not an
invertible negative-energy witness. No raw-Delta number is presented as a
complete-form proof.

The proof search stops after this exact contradiction and its source/dependency
audit, not because of a small-torus failure or a weakened replacement goal.
Independent verification is a separate workflow step.

## Departures from the print and retained source readings

These are all the pinned choices recorded in `../pin/PIN.md`; none is silently
repaired here. The CMP102 p.277 quotation and printed-page readings are inherited
from the supplied pin/handoff; no fresh page-image verification is claimed.

1. **Coverage:** added site coverage and common-cube **four-touch-edge** coverage,
   coupled at factor 12; neither follows from the printed outside-domain sentence.
   Four-touch coverage is not one-corner plaquette coverage.
2. **Delta/J:** one-corner selection from CMP102 p.277, applied to the Dirichlet
   base domain; differs from frozen inside selection and from the unrestricted
   torus sums displayed on CMP99 p.392. No assertion that selected operators read
   only endpoint-touching background links is added.
3. **Class stencils:** endpoint-touching bonds replace both-endpoint bonds;
   difference and curl guards require all read bonds to touch the cube. This is
   an interpretation of regularity on the cube, not a bound on every far edge.
4. **Gauge:** separate existential gauge and Hermitian traceless logarithm per
   class cube; globally typed functions with local constraints, no global-gauge
   consistency premise.
5. **Cubes/factors:** aligned periodic product boxes, frozen strata/unique index,
   one common factor 12. Printed unions and cube-attached O(1), per-cube factors,
   non-box unions and the altered p.408 zero-level class are not substituted.
6. **Scope:** dimension three and SU(2), not arbitrary dimension or group.
7. **Lattice:** finite rectangular periodic tori, side-minus-one extents,
   scaleUp, mesh ell to minus k, periodic l1 distance and frozen `TorusOK`.
8. **Tower/domain:** strict collars, aligned half-open blocks, empty padding and
   exact p.396 RM base layer under reading A. Not arbitrary thinner layers,
   reading B, two-domain regularity or the p.408 third-enlargement condition.
9. **Lambda:** frozen unit-lattice block union, block-sum condition, strict RM
   collar and the same R as the tower; empty Lambda allowed. Common-radius
   identification is inherited as a reading.
10. **Parameters:** all natural ell at least 2, positive real a, depths at least
    1, M a positive power of ell, natural R. Odd L>11 and powers-of-L radii are
    not imposed. This refutation specifically uses ell=2.
11. **Uniformity:** exact frozen threshold order; a0/gamma0 may depend on
    ell,a,m,R but precede depth, torus, alpha, geometry and fields. No Total-style
    stronger order is substituted.
12. **Norms/derivatives:** full Frobenius class norm, strict derivative powers,
    genuine curl-adjoint-curl ddA, trace-normalized test energy. The square-root-two
    norm difference and interpretation of the printed differential expression
    remain disclosed.
13. **Site/averaging operators:** actual frozen jets, weighted mass, site
    inverse/projection, W, multilevel Q, second jets and C. Their full printed
    dictionary is not rederived; no toy replacements are used.
14. **Support/constraints:** touching `OnLambdaT`, selected `CRowIn`/dropped bonds,
    axial staircase and `OnLambdaTildeIn`; genuine genC and its joint solution/
    singular fallback. No extra Q1-kernel premise on the free input is inserted.
15. **Units:** retain eta/tau-star in the first term and frozen mass, nonlinear J
    and bond energy. The broader S-3 printed-unit dictionary is not settled by
    this refutation.
16. **Inverses:** totalized inverses with zero at non-units, without an existence
    premise/conclusion. This is the decisive limit of the refutation; the
    guarded and full-guard variants are different statements.
17. **Proof-local room:** no extra headline premise. The chosen R and M imply
    the room condition needed for the imported cofinal slab construction.

## Reproduction and scope

Only this directory was written. Protected Lean, paper, notes, expected, extras,
other AHP directories and the lakefile were left alone. Pre-existing compact
project work and lakefile changes belong to other threads. No deletion, commit,
push, build, reproduction or dependency update was performed.

All compilations were requested exclusively through:

```sh
AHP/round3/lean1.sh AHP/round3/s1-proper/r1-refute/Attempt.lean
```

The final compile ran in the persistent BB terminal `S1 refutation compile`
to survive interruptions while waiting for the shared lock. The terminal
reported `S1_REFUTE_DONE:0`; the wrapper wrote `Attempt.lean.log` and
`Attempt.lean.exit` (0). Earlier interrupted invocations are not evidence of
success. The first completed run failed only on name ambiguity; no intentional
proof holes or forbidden constructs were inserted.

The successful source/log audit command was:

```sh
python3 AHP/round3/s1-proper/r1-refute/audit.py
```

The audit checks the exact pinned block, the three verbatim round-2 coverage
helpers, exact goal header, sole unchanged implicit-extent variable context,
all local dependency prints, permitted dependencies, frozen-only imports, clean
compiler output and absence of forbidden source tokens. SHA-256 values are
saved in `audit.json`.

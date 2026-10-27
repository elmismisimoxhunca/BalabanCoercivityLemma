# S-2 non-vacuity: compiled statement pin

**Status: pin compiled; no positive witness or saturation theorem proved here.**

File: [Statement.lean](Statement.lean). Namespace:
`AdalyFormal.AHP.Round2.S2Nonvacuity`.

This is the open non-vacuity question from `AHP/fidelity/STAGE_B_RESULTS.md`,
not a repeat of the already proved class/headline implications. The four-bond
and corner classes are pinned separately. Solving the four-bond branch settles
this round's non-vacuity item; solving only the corner branch is partial progress.
Neither disposition by itself identifies either class with Balaban's print.

## The goals in plain words

| Goal | Source line | What must be proved |
|---|---:|---|
| `GoalPos1` | 133 | The four-bond touching class has proper nonempty admissible-domain instances, with nonzero admissible test fields, cofinally in the headline scales and below every positive smallness cap. |
| `GoalNeg1` | 142 | Every four-bond class member on an admissible headline-side-condition tower has base domain empty or the entire fine torus. |
| `GoalPos2` | 153 | The same positive statement for the corner class. |
| `GoalNeg2` | 161 | The same universal empty/whole-torus conclusion for the corner class. |

### Positive quantifiers: no out-of-regime isolated example

For each positive goal, choose **one fixed** blocking factor \(\ell\ge2\).
Then, for every proposed exponent lower bound \(m_{\rm lower}\), choose
\(m\ge\max(1,m_{\rm lower})\). **After that choice**, for every radius lower
bound \(R_{\rm lower}\), choose \(R\ge R_{\rm lower}\). **After that choice**,
for every positive cap \(a_0\), supply an instance.

This ordering reaches any frozen headline thresholds \(m_0\) and \(R_0(m)\),
and accommodates its cap \(a_0(\ell,M,R,a)\): the radius is chosen before
seeing the cap, not after. There is no assumption that the unknown theorem
threshold is 18 or any other explicit number. A construction valid for every
\(m\ge1\), \(R\ge18\) can choose \(R=\max(R_{\rm lower},18)\).

The chosen blocking factor may be 2, as in the existing slab construction.
The pin does **not** require every blocking factor, every sufficiently large
exponent/radius, a fixed depth, a particular slab, or a non-flat background.
It asks for a cofinal family at one blocking factor, stronger than an isolated
existential witness but sufficient for genuine headline-regime non-vacuity.
The tower, torus, depth, Lambda, background, smallness parameter and test field
may depend on the chosen cap. A flat background is allowed.

`ProperFourAt` (`Statement.lean:98`) and `ProperCornerAt` (`:113`) require all
of the following **as conclusions to be constructed, not assumed coverage**:

- \(M=\ell^m\), with \(\ell\ge2\), \(m\ge1\) supplied by the outer goal;
- a depth \(k\ge1\) and actual unit-torus extent `Lu`;
- `TorusOK ell M Lu`;
- `S : Tower (scaleUp ell k Lu)` and `Admissible ell M R k S`;
- `LambdaOK2 ell M R k S Lam`;
- `(S.Om 0).Nonempty` and `S.Om 0 ≠ Set.univ`;
- \(0<\alpha_0\) and \(12M\alpha_0\le a_0\);
- the specified touching class at **factor 12** and
  \(\eta=(\ell^k)^{-1}\), including its actual site and plaquette coverage;
- a field `Bt : Bond Lu → SuTwo` satisfying `OnLambdaTildeIn Lam ell Bt`
  **and** `OnLambdaT Lam Bt`, with `Bt ≠ 0` and `0 < bondEnergy Bt`.

These are exactly the two input-space predicates of frozen `InstIneq`
(`lean/src/ZT5A.lean:56`). `Bt` is the parametrizing field \(\widetilde B\),
not the reparametrized field \(C\widetilde B\). In particular we do not
incorrectly impose `Q1 Bt = 0` on the free input variables. Empty Lambda
cannot meet this requirement: `OnLambdaT` would force `Bt = 0`.

The mass parameter \(a\) does not occur in these hypotheses or this test
space. One may take \(a=1>0\); the outer scale assumptions give
`SidePow6 ell (ell ^ m) 1`. No coercivity inequality, inverse-existence
assertion or value of \(\gamma_0\) is part of a non-vacuity goal.

### Negative quantifiers and relation to the positive goals

`GoalNeg1` and `GoalNeg2` range over **all** \(\ell\ge2\), \(m\ge1\),
\(R\in\mathbb N\), \(k\ge1\), compatible tori, admissible towers, positive
\(\alpha_0\), and backgrounds belonging to the corresponding class at
factor 12 and mesh \((\ell^k)^{-1}\). They conclude
\(\Omega_0=\varnothing\) or \(\Omega_0=T_\eta\).

They deliberately do not require Lambda, a smallness cap, or a nonzero test
field: a geometry-only saturation proof should not need these. They also
range below any putative radius threshold. Thus these are **stronger
negative alternatives**, not definitions of the exact negations of the
cofinal positive goals. Their strength and incompatibility are explicit:

- `goalNeg1_implies_not_goalPos1`, `Statement.lean:176`;
- `goalNeg2_implies_not_goalPos2`, `Statement.lean:189`.

Both implications compile and use only standard axioms. Their short proofs
merely extract one positive instance and contradict its proper nonempty base
domain; **neither proves a saturation goal**. Conversely, failure of a
positive cofinal goal would not establish global saturation.

## Definition fidelity and frozen dependencies

Direct import: **only `ZT5A`**, from `lean/src/ZT5A.lean`. No AHP imports,
new operators, placeholder maps, or alternate cube predicates.

The following eight declaration texts were copied **character-for-character**
from `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean` (checked by extraction
and equality, not merely by matching names). The new namespace and new
non-vacuity propositions are the only changes to their context.

| Definition | Stage-B line | Pin line |
|---|---:|---:|
| `TouchBond` | 71 | 41 |
| `CoversPlaqFour` | 301 | 44 |
| `plaqCorner` | 329 | 49 |
| `CoversPlaqCorner` | 344 | 54 |
| `CurlReadsTouch` | 362 | 59 |
| `PerCubeRegularTouch` | 376 | 64 |
| `ClassCoupledFour` | 415 | 84 |
| `ClassCoupledCorner` | 424 | 87 |

Underlying frozen definitions are used directly, not copied into stand-ins:

- `scaleUp`, `Tower`, `bigSide`, `Admissible`, `siteBox`, `DescribedAt`,
  `IsClassCube`: `lean/src/ZStatementP428.lean:42,47,51,73,122,131,140`.
- `TorusOK`: `lean/src/ZStatementP428.lean:286`.
- `CoversOm0c`, `curlA`, `ddA`, `OnLambdaT`:
  `lean/src/ZR2A.lean:107,29,40,121`.
- `LambdaOK2`, `LamBlockSum`: `lean/src/ZT4A.lean:88,57`;
  underlying `LambdaOK`: `lean/src/ZStatementP428.lean:189`.
- `OnLambdaTildeIn`, `CRowIn`, `IsDroppedIn`:
  `lean/src/ZStatementP428.lean:230,211,216`.
- `bondEnergy`: `lean/src/AdalyFormal/Balaban/RegularUPerturbation.lean:355`.

Every class cube is still the frozen aligned product box, in two consecutive
strata, with a unique index. Regularity still has `∃ g, A` **inside** the
quantifier over cubes and retains all three strict bounds, the forward
finite difference and the actual `ddA` curl-adjoint-curl expression. Neither
the shell class nor a domain enlargement is substituted.

## Departures from Balaban's print and retained readings

The sources for this disclosure are the supplied adjudicated transcriptions
`sources/corpus/pages/CMP99b_p393.md`, `CMP99b_p396.md`, `CMP99b_p408.md`,
`CMP99b_p427.md`, `CMP99b_p428.md`, the statement sheet, and
`paper/OPEN_ITEMS.md` B, K–N, R and S. The CMP102 p.277 convention is cited
from the supplied S-1 reading and sheet; no local p.277 source image was
found or independently re-read in this pin pass.

1. **Purpose, not a printed theorem.** These are new non-vacuity/saturation
   questions, not the positive lower-bound assertion on p.428. Properness,
   nonemptiness, positive test energy and cofinal witness quantifiers are
   audit demands. A proof would not prove or refute the printed coercivity
   assertion or certify the complete printed class.
2. **Dimension, group and lattice.** Retain the frozen three-dimensional
   finite periodic torus and SU(2) specialization. Extents store side minus
   one; unit/fine lattices are related by `scaleUp`, with
   \(\eta=\ell^{-k}\). Rectangular extents, modular wrap and `TorusOK`'s
   divisibility/strict-size requirements are formal lattice conventions,
   not an unrestricted dimension/group result from the print.
3. **Blocking factor and scales.** Retain \(\ell\ge2\), \(M=\ell^m\),
   \(m\ge1\), \(k\ge1\). The positive pin permits one such \(\ell\),
   including 2; it does not settle the odd \(L>11\) convention noted in
   OPEN_ITEMS S-4. Radius \(R\) ranges over all naturals, not only powers
   of \(L\) as stated on p.408. The cofinal ordering is our way of testing
   non-vacuity beyond the frozen existential thresholds, not an extra claim
   about the print's constant uniformity. No fixed positive lower threshold
   for \(R\) is asserted.
4. **Tower geometry and base law.** Retain periodic \(\ell^1\) distance,
   aligned half-open block tilings, empty padding above depth, strict collars,
   and the exact p.396 block-collar base law. This uses the disclosed reading A
   of the fine lattice in its own units (OPEN_ITEMS R-a). It is not the
   p.394 arbitrary thinner layer, reading B, or a two-domain statement.
5. **Cube class and factor.** Retain `IsClassCube`: aligned product boxes of
   side \(12M\ell^j\), two-stratum containment and unique index. The print
   p.396 says unions of several big blocks and attaches \(O(1)\ge10\) to
   a cube; selecting one common factor 12 (motivated by p.409) and this box
   family is a restriction. No per-cube factor, non-box union, p.408 altered
   level-zero class or third-enlargement clause is added.
6. **Touching regularity.** Replace both-endpoint `CubeBond` by at-least-one-
   endpoint `TouchBond` in every class bound and its read guards, exactly as
   in Stage B. This implements the bond part of the supplied CMP102 p.277
   convention, not the larger read-bond shell of S-1. Derivative guards mean
   the bounds are imposed where all displayed stencil bonds touch the cube;
   the pin does not identify this boundary prescription with a unique
   printed one. The global functions `g,A` are the frozen encoding of a
   per-cube gauge/field, with constraints only on the selected bonds.
7. **Coverage is additional.** Neither the retained site-coverage clause nor
   either one-cube plaquette-coverage clause is supplied just by p.396's
   regularity bounds. Four-bond coverage asks that all four edges touch
   \(\Omega_0\); this is **not** the print's one-corner plaquette selector.
   Corner coverage uses that selector for its antecedent but still asks all
   four boundary edges to touch a single frozen cube contained in
   \(\Omega_0\). That extra witness demand may cause saturation; saturation
   is the open negative goal, not an assumption. The eight copied definitions
   make these two different classes unambiguous.
8. **Norm, differential expression and cap.** Retain full-matrix Frobenius
   norm in the regularity bounds (the disclosed \(\sqrt2\) difference from
   the trace-normalized norm), the frozen curl form `ddA`, and the three
   strict powers \((\ell^j\eta)^{-1,-2,-3}\). Smallness is explicitly
   \(12M\alpha_0\le a_0\), rather than a numerical interpretation of
   "sufficiently small". The cap is arbitrary positive; no class constant is
   set to zero. The test energy uses the frozen `SuTwo`/Hilbert-space norm.
9. **Lambda and test fields.** Retain frozen `LambdaOK2`, its unit-lattice
   collar and block-sum convention, touching support, axial staircase and
   selected dropped-row conventions. These are the frozen reading of
   pp.427–428, not a fresh support/constraint correspondence proof. The
   nonzero field requirement rules out empty-Lambda vacuity.
10. **Operators are not changed or compared.** This pin has no quadratic-form
    conclusion. The surrounding Stage-B touching-class headlines retain
    frozen `InstIneq` and `plaqIn` operators. There is no transfer here to
    one-corner/all-plaquette operators, no resolution of S-1, no inverse
    guard result, and no \(\eta\)/\(\tau^*\) normalization assertion for S-3.
    Those operator-level departures remain separate, not silently repaired.

## Suggested routes, not evidence of closure

For the positive four-bond goal, the existing `SlabNv` family,
`Fidelity.S1.shell_slab_nonvacuous` and `D1Final.lean:139–168` suggest a
construction: retain the actual slab geometry and Lambda, prove four-touch
coverage for that base domain, take flat `U`, and supply the real free test
field (see `lean/src/NV6.lean:203`, `BseedNv_props`). The shell theorem alone
is not a touching-class witness because it has different coverage. All needed
AHP definitions/helpers must be copied into the attempt rather than imported.

For the corner negative goal, the Stage-B product-box argument and the
finite scans in `s2-inclusion/ATTACK.md` suggest proving shift-closure of
`S.Om 0`, hence saturation on the finite connected torus. A numerical scan
or a source-level sketch is not a proof. Do not promote corner saturation
to four-bond saturation.

## Compilation and audit evidence

Executed exactly one Lean compilation, serially, with ready frozen oleans:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/pin/Statement.lean > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/pin/Statement.lean.log 2>&1
echo $? > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/pin/Statement.lean.exit
```

- [Exit record](Statement.lean.exit): **0**.
- [Compiler log](Statement.lean.log): eight `#check` outputs and **16**
  `#print axioms` records; every dependency list is a subset of
  `propext`, `Classical.choice`, `Quot.sound`. No warnings or errors.
- All eight copied definition texts match their Stage-B originals exactly.
- Full-source forbidden-token scan: no hits; sole import is frozen `ZT5A`.
- SHA-256 of compiled `Statement.lean`:
  `826f93c754d1c78a13e8ee7a832fc3041b36cd9cbe4628cde3a7475d752909f9`.

No numerical program, build, update, reproduction script, commit, push, or
removal was run. Writes are confined to this item's `pin/` directory. The
pre-existing changes in the shared frozen checkout were not modified.

**Acceptance boundary:** successful elaboration certifies that these are
well-formed propositions and that each negative alternative implies the
negation of its positive partner. It does not establish any of the four
open goals.

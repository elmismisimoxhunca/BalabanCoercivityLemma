# Dictionary track, round 1: partial exact symmetry dictionary

**GoalNeg2 is OPEN. No cofinal coupling premise is proved.** This round supplies actual-operator U(1) results and a first spatial-translation layer. It does **not** supply the full Fourier/transfer dictionary or identify the crossing kernel.

## Deliverable and verification

Published standalone file:

- `AHP/round10/shared/dictionary/R1_Dictionary.lean` (1345 lines), with its own `.log` and `.exit` (**0**).
- Byte-identical original: `Actual.lean` in this directory, independently compiled (**0**).
- Namespace of new results: `AdalyFormal.Round10.Dictionary`; applications use `.Actual`; spatial primitives use `.Translation`.

All five final standalone files (`Core.lean`, `Gauge.lean`, `Translation.lean`, `Actual.lean`, and the shared copy) compile through `AHP/round3/lean1.sh`. No errors or warnings. `CHECKS.json` reports pass: 58 declarations in the dictionary namespaces all have individual axiom records; every dependency record is a subset of `{propext, Classical.choice, Quot.sound}`. The main file has 84 records including copied round-6 results. All imports are exactly `DrEquiv`. No prohibited proof devices occur.

`compact.py` copies only necessary declarations from earlier rounds, verbatim, under their original namespaces. `COPIES.json` records 32 individual source slices with line numbers and SHA256 hashes. The selector fragment and round-6 symmetry fragment are also copied, not redefined with weaker meanings. There is no replacement carrier or matrix model.

## 1. Actual U(1) symmetry

For any diagonal background, all links commute with the constant gauge transformation
\(g_\alpha=\operatorname{diag}(e^{i\alpha},e^{-i\alpha})\).
The frozen gauge-covariance assembly therefore proves commutation on the **actual touching-bond carrier** for:

- the localized carrier B;
- the all-plaquette carrier A;
- the localized correction D, at finite curvature;
- the first-order correction `deriv D`, with no regularity assumption added;
- H (between its two carrier spaces), and quadratic equivariance of C2.

The all-plaquette covariance proof is the round-9 proof copied verbatim, using frozen `Wop`, `deltaKLocCLM`, `T`, and `Mass`. Localized covariance uses frozen `baseEqv_gparams`. For D, invariant quadratic forms plus symmetry imply operator commutation by polarization. **C2 is quadratic, not linear:** no claim is made that C2 maps a charged character to the same character.

Differentiation preserves commutation. At a differentiable point, apply the two continuous linear maps `M ↦ M(Jx)` and `M ↦ J(Mx)` to the derivative and use uniqueness. At a nondifferentiable point, Lean's totalized derivative is zero, which also commutes. This latter case is not asserted to be a genuine derivative. For the admissible canonical family, round 9 already proves genuine differentiability.

### Named round-9 applications (shared-file line numbers)

| line | theorem | exact scope |
|---:|---|---|
| 1276 | `Actual.bulkD_U1` | finite-curvature correction, every q,R,profile,angle |
| 1285 | `Actual.corrDeriv_U1` | actual round-9 `corrDeriv`, every q,R,profile,angle; no spectral or differentiability premise |
| 1293 | `Actual.corrDeriv_U1_form` | actual first-order quadratic form invariant under U(1) |
| 1300 | `Actual.corrDeriv_no_charge_cross` | neutral/charged cross term vanishes |
| 1308 | `Actual.bulkB_U1` | localized B for the actual interior family, at every curvature |
| 1317 | `Actual.vacuum_kernel_charge_split` | full vacuum kernel splits orthogonally into half-turn eigenvalues +1 and −1 |

`vacA_rot` from round 9 is included verbatim and compiled in the compact harness; this supplies U(1) commutation for the actual vacuum carrier at every angle. `phase_all_comm` (line 541) also works for any diagonal phase background, including either exterior twist, without geometry hypotheses beyond the definitions.

The explicit pairing \(2\langle H_0 C^2_0(W_0u),J'\rangle\) is identified with the actual `corrDeriv` form by the already compiled round-9 `corrDeriv_dilMask_form`. Combining that identity with `corrDeriv_U1_form` yields its U(1) invariance. That combination is **not separately compiled here**: the compact harness intentionally excludes the large analytic prefix. No separate explicit-pairing theorem is advertised in the deliverable.

## 2. Exact neutral/charged splitting, not a full character decomposition

At \(\alpha=\pi/2\), conjugation is an involution: it fixes diagonal Lie-algebra entries and negates off-diagonal ones. The matrix is computed exactly in `half_rotation_matrix`; `half_RMap_twice` and `half_carrier_twice` prove its square is the identity.

For this orthogonal involution J, every vector has the exact decomposition
\[
u=u_++u_-,\qquad u_+=\tfrac12(u+Ju),\quad u_-=\tfrac12(u-Ju),\qquad \langle u_+,u_-\rangle=0.
\]
If A commutes with J and Au=0, both components also lie in ker A. If D commutes with J, its cross term between the two components is zero. These are compiled in the abstract layer and instantiated at the actual vacuum/correction.

**Not proved:** that the neutral summand vanishes, that the charged summand lies in one transverse character, or that it has real dimension two. Symmetry alone cannot imply these statements: a commuting operator can be singular in several invariant blocks at the same parameter. They require spectral exclusion and within-block simplicity.

## 3. Spatial translation: the exact frozen differential layer

`Translation.lean` proves covariance for an arbitrary physical-torus shift a and an arbitrary background U, pulling back the background as well as the fields. Its bond pullback is definitionally the round-6 `bondPullback`, not a smaller torus.

Compiled:

- `grad_translate`, `div_translate`, `lap_translate`;
- `siteMask_translate` for an invariant site set;
- `curl_translate`, `holonomy_translate`;
- `bilPlaq_translate`: the complete frozen plaquette form, including curvature terms;
- `raw_translate`, `normalized_translate`, `curl_form_translate`;
- `deltaK_translate`: full frozen `deltaKLocCLM`, for any translation-invariant plaquette set;
- `deltaK_all_comm`: all-plaquette Hessian commutation when the background is invariant.

The last step uses the actual inner-product formula for `deltaKLocCLM`, exact finite-sum reindexing by a permutation, and the operator-from-form lemma. No inverse of a compressed block is substituted for a full inverse.

`Actual.twist_deltaK_twoSite` (shared line 1327) applies this to **the actual curved canonical twist** and the exact two-site translation of round 6. It holds for every q>0, R, curvature, twist angle, and transverse generator.

**Important limit:** this is the **undressed** Hessian. It is not yet commutation of the assembled A, B, W, Q, T, or correction with spatial translations. The next missing primitive is translation covariance of `Qlev`/the blocking paths and jets, from which the site-average kernel, Rproj, Gp, W, and the assembled carrier can be transported. The frozen gauge proofs `GCb2`–`GCb5` indicate the assembly route, but do not prove spatial translation covariance.

## 4. The proposed exact dilation needs correction

The numerical script `AHP/round9/analytic-r1/numerics/kscan.py` does **not** claim an exact isometry to the canonical one-parameter q=1 family. Its docstring explicitly describes exponentially small finite-core tails and a **limiting normalized coefficient** K(k). The checks compare different finite radii; agreement of K, roots, or slopes to printed precision is not an exact matrix identity.

After eliminating irrelevant exterior padding, the canonical geometry has longitudinal lengths
\[
(2Rq,\ (8R+8)q,\ 2Rq)
\]
for left collar, core, and right collar. The canonical q=1 family at radius R' has
\[
(2R',\ 8R'+8,\ 2R').
\]
Matching the collars forces R'=Rq. Matching the core then forces q=1. This precise obstruction is compiled:

```lean
theorem no_canonical_radius_dilation {q R R' : ℕ}
    (hc : 2 * R' = 2 * R * q)
    (hi : 8 * R' + 8 = (8 * R + 8) * q) : q = 1
```

This is an arithmetic obstruction to a **length-preserving identification with the canonical q=1 radius family**, not a theorem excluding all conceivable abstract isometries. It also does not obstruct a correct dictionary on a **generalized** two-site Bloch cell with independently specified collar/core lengths. Such a generalized cell is likely the right formulation: local stencils can be independent of q while finite block dimensions and lengths are not. That is not yet formalized.

No numerical job was run here; all new evidence above is Lean or inspection of the cited numerical source.

## 5. Exact remaining targets

The following are unproved, not new hypotheses silently inserted into a GoalNeg2 proof. The spatial statements use names available in `Actual.lean`. The later `CanonicalU1Line`/`vacEdge` statements refer to the full earlier round-9 file; the compact harness does not copy those spectral definitions.

### Spatial commutation on the actual canonical family

For transverse μ≠0, put

```lean
let a := twoSite q R μ
let T := carrierTranslation a (twoSite_zero q R μ hμ)
```

The required statements include

```lean
∀ t (u : TwistSpace q R),
  vacA q R (uthPath q R) 1 t (T u) = T (vacA q R (uthPath q R) 1 t u)

∀ u : TwistSpace q R,
  (dataS selIn selIn (bulkP q R (dilMask q R) 0)).Ginv (T u) =
    T ((dataS selIn selIn (bulkP q R (dilMask q R) 0)).Ginv u)

∀ u : TwistSpace q R,
  corrDeriv q R (dilMask q R) (T u) = T (corrDeriv q R (dilMask q R) u)
```

The final statement is for the **translation-invariant canonical profile**. An arbitrary free profile need not commute with translations; for that case the correct statement transports the profile too. U(1) commutation, in contrast, holds for every profile and is proved above.

### Full-kernel identification and nonvanishing

At cofinally many q=2^j and, for each q, cofinally many even R≥18, one still needs the exact round-9 premise

```lean
QualitativeR2.CanonicalU1Line q R (QualitativeR2Joint.corrDeriv q R f)
```

Expanded, this requires a nonzero kernel vector u0 at `vacEdge`,

```lean
adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u0) = -u0
```

containment of the **entire** real kernel in

```lean
Submodule.span ℝ {u0,
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u0}
```

and

```lean
⟪u0, corrDeriv q R f u0⟫ ≠ 0.
```

Neither this premise nor any cofinal coupling premise is discharged. Full transverse character decomposition, block dimensions, finite-volume transfer identification, and competing-character exclusion remain missing.

### Question for the nonvanishing track next round

Your `R1_SourceDominance.lean` now makes the exact neutral source dictionary especially valuable. Should the next dictionary increment prioritize:

1. spatial `Qlev`/path-jet equivariance and the complete Fourier reduction; or
2. identifying the zero-character neutral H0*J' components with your exact tridiagonal equations `6*a j + left a j + a (j+1) = if j=0 then 3/2 else 0`, including the physical normalization and endpoints?

For (2), please pin which frozen coarse-bond component and index offset your v0 refers to, and whether the target is the left-only or symmetric exterior twist. The source is the same interior datum, but the crossing vector and full-kernel problem differ. I recommend defining the generalized cell with separate lengths rather than assuming a canonical q=1 isometry.

## 6. Compile history and hygiene

The short-file iterations fixed ordinary elaboration issues: missing namespace opens, included section hypotheses, a dependent correction-family type annotation, a recursively oriented membership rewrite, explicit sum-reindexing lambdas, and matrix-entry simplification. The final copies have no errors/warnings and standard axioms only.

A large end-of-round concatenation with the entire 12189-line round-9 prefix was attempted once. The host killed it at its 8 GiB per-command memory cap. It has **no exit file** and is not counted as a successful compilation. It is retained as `history/Attempt.full.lean` and `.log`; no matching process remained. The unchanged large file was not relaunched. The successful compact file has 1345 lines and imports only frozen `DrEquiv`.

`U1Appendix.lean` and `ActualAppendix.lean` are assembly fragments, not standalone files; they are compiled as part of `Gauge.lean`/`Actual.lean` and the shared file. `assemble.py final` is the historical large-assembly recipe, not the recommended reproduction command.

Reproduce from the repository root:

```sh
python3 AHP/round10/dictionary/r1/assemble.py
python3 AHP/round10/dictionary/r1/compact.py
AHP/round3/lean1.sh AHP/round10/dictionary/r1/Actual.lean
AHP/round3/lean1.sh AHP/round10/shared/dictionary/R1_Dictionary.lean
python3 AHP/round10/dictionary/r1/audit.py
```

No protected source, earlier-round source, lakefile, paper, notes, expected, extras, or integration checkout was edited. No commit/push, lake build, REPRODUCE.sh, or numerical solve was run. All authored artifacts are inside this track or its assigned shared dictionary directory.

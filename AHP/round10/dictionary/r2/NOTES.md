# Dictionary, round 2: exact neutral source and inverse-free identification

**GoalNeg2 is OPEN. No round-9 cofinal coupling premise is proved.** The tridiagonal formula for the actual H0*J' is also still open. This round follows `shared/COORDINATOR.md`: prioritize the source dictionary, not the full spatial Fourier construction.

## Verified deliverable

`AHP/round10/shared/dictionary/R2_SourceDictionary.lean` is a standalone, 1055-line compact harness, importing only frozen `DrEquiv`. It is byte-identical to `Source.lean` here. Both paths were compiled independently by `AHP/round3/lean1.sh`, with exit **0**, no warnings/errors, and only `propext`, `Classical.choice`, `Quot.sound` in every printed dependency record.

- 63 new declarations, individually audited; 1 reused dictionary declaration is also audited.
- 88 dependency records in the combined file.
- `PhaseSource.lean` (243 lines, 30 new declarations) and `KKT.lean` (100 lines, 9 new declarations) also have independent clean exit-0 compilations.
- `SourceAppendix.lean` is an assembly fragment, compiled inside `Source.lean`, not advertised as a standalone file.
- `COPIES.json` verifies 26 verbatim prior declaration/namespace fragments. The operative selector, family, source-derivative and explicit-coupling definitions are not weakened or replaced.
- `CHECKS.json` passes, and explicitly records that the actual tridiagonal identification and GoalNeg2 are not proved.

New namespaces:

- `AdalyFormal.Round10.Dictionary.PhaseSource`
- `AdalyFormal.Round10.Dictionary.KKT`
- `AdalyFormal.Round10.Dictionary.Source`

For downstream assembly, the new parts are `PhaseSource.lean` without its import, `KKT.lean` without its import, and `SourceAppendix.lean`, plus round 1's already-compiled `half_rotation_matrix` if not present. Do not concatenate both complete compact harnesses: they intentionally copy common definitions. The canonical `bulkU_dilMask` theorem retains its original `QualitativeR2Joint` namespace.

## 1. Actual source derivative: explicit and unconditional

This is new operator identification, not an abstract sufficient premise.

Let E3 be the frozen orthonormal generator `SuTwoInner.pauliE3 = diag(i,-i)`. For any real bond phase f, put U(b)=diag(exp(i f(b)),exp(-i f(b))). For an oriented plaquette p, define

\[
c_f(p)=f(x,\mu)+f(x+e_\mu,\nu)-f(x+e_\nu,\mu)-f(x,\nu).
\]

For a plaquette selector P, extend a plaquette scalar g antisymmetrically to directions:

\[
F^P_{\nu\mu}[g](x)=
\begin{cases}
\mathbf1_P(x,\nu\mu)g(x,\nu\mu),&\nu<\mu,\\
-\mathbf1_P(x,\mu\nu)g(x,\mu\nu),&\mu<\nu,\\
0,&\nu=\mu.
\end{cases}
\]

The actual frozen source at mesh one satisfies the **finite-curvature identity**

\[
-\mathrm{JSU2Loc}(1,P,U)(x,\mu)=
\sum_{\nu\ne\mu}\left(F^P_{\nu\mu}[\sin c_f](x-e_\nu)
-F^P_{\nu\mu}[\sin c_f](x)\right)E_3.
\]

Compiled as `PhaseSource.JSU2Loc_phase`. Its proof expands the frozen holonomy, localized antisymmetric extension, transport-divergence, and source definitions. Diagonal conjugation fixes the diagonal Hermitian source. There is no numerical differentiation, no guessed curvature mask, and no lost sign or mesh-one factor.

Replacing f by εf and differentiating at zero gives the same formula with sin(c_f) replaced by c_f. `PhaseSource.sourceField_hasDerivAt` proves the genuine derivative of the full bond field; `sourceField_tendsto` gives the corresponding two-sided punctured limit. `sourceLinear P f` denotes exactly this finite stencil times E3.

For the actual round-9 family, set

\[
\widehat f(b)=0\text{ on }Z_b(\Omega_0),\qquad \widehat f(b)=f(b)\text{ otherwise}.
\]

The frozen `bulkU` is **equal**, at every ε, to the phase family ε f-hat (`bulkU_phase`). Consequently its carrier source has first coefficient

\[
J'[f]=p_E\,\mathrm{sourceLinear}(\mathrm{plaqIn}(\Omega_0),\widehat f).
\]

This is `profileSourceStencil`; `bulkSource_tendsto` proves the actual limit for every q,R and every profile, with no geometric or invertibility hypotheses.

For f=`dilMask`, the exact round-9 predicate is discharged:

```lean
theorem canonical_isSourceDerivative (q R : ℕ) :
  IsSourceDerivative q R (canonicalSourceStencil q R)

theorem sourceDerivative_eq_stencil (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') :
  J' = canonicalSourceStencil q R
```

These are unconditional source facts. They do **not** identify the propagated source H0*J' with the proposed one-dimensional recurrence.

## 2. H0*J' is exactly neutral; the coupling is an exact scalar sum

`bulkSource_U1` proves that the actual localized source is fixed by every constant diagonal phase. Passing to the two-sided source limit proves `sourceDerivative_U1`. Gauge covariance of the **full** frozen H and its adjoint then yields

\[
\mathrm{Ad}_{g_\alpha}\,H_0^*J'=H_0^*J'.
\]

This is `neutralSource_U1`. No inverse is compressed to a sector; no unit or spectral premise is used in the equivariance proof. The prior flat-point unit results ensure that these totalized inverses are genuine inverses in the admissible application.

Define

\[
h(p)=\langle E_3,(H_0^*J')(p)\rangle,
\qquad v(p)=\langle E_3,C^2_0(W_0u)(p)\rangle.
\]

The half-turn matrix and the frozen Pauli decomposition prove, component by component,

\[
(H_0^*J')(p)=h(p)E_3.
\]

Thus the actual analytic route's `vacCoupling` is exactly

\[
\mathrm{vacCoupling}(q,R,J',u)=2\sum_{p\in\mathcal B}h(p)v(p)
=2\sum_{p\in\mathcal B:\,\mathrm{level}(p)=1}h(p)v(p).
\]

The second equality uses the newly compiled `C2_level_zero`: the frozen level-zero quadratic jet is zero for **every** geometry/background. This is not an assumption about the source's level-zero entries; those entries may be nonzero but do not contribute.

Key results:

- `neutralSource_component`
- `vacCoupling_neutral_sum`
- `vacCoupling_neutral_top_sum`
- `vacCoupling_U1`: the explicit H0-C2-J' form itself is invariant under every diagonal phase.

All sums still run over the actual physical `BIdx`; no transverse cardinality or Bloch normalization has been silently removed. The component scalar uses the frozen norm-one E3, so its normalization is fixed.

## 3. Inverse-free certificate for the propagated source

Let D be the actual frozen `BaseDataS`, B=D.Ginv, G=B inverse, Q=D.Q and N=QGQ*. If B and N are units, then

\[
QH=1,\qquad BH=Q^*N^{-1}.
\]

Suppose explicit physical fields x and h satisfy the two equations

\[
Qx=0,\qquad Bx+Q^*h=J'.
\]

Symmetry of B gives, for every z,

\[
\langle Hz,J'\rangle=
\langle BH z,x\rangle+\langle QHz,h\rangle
=\langle N^{-1}z,Qx\rangle+\langle z,h\rangle
=\langle z,h\rangle.
\]

Therefore **H*J'=h**. This is compiled in `KKT.source_of_certificate`; `source_of_weak_certificate` only requires the residual equation paired against arbitrary physical y. `coupling_of_certificate` gives the pairing directly for every jet. The actual-family specializations are `Source.flat_source_of_certificate` and `Source.vacCoupling_of_certificate`.

These certificate theorems are **conditional**. No x,h satisfying the full physical residual equations is constructed here. This removes inversion from the pending verification, not the verification itself.

The unit premises are already supplied in round 9, not new spectral gaps: `analytic-r2/Attempt.lean:6744` (`dil_B0_unit`, q>0,R≥1) and `:6764` (`dil_N0_unit`, q>0,R≥16, admissibility), with `dataFam_dil_zero` at :6737. Their long proofs are not recompiled in this compact harness, and the certificate specializations visibly retain the unit hypotheses.

### Exact two-site normalization check, not a physical lift theorem

`KKT.two_site_residual_iff` proves the rational identity

\[
\frac{3a+\ell}{2}+\frac h8=\frac d2,
\qquad
-\frac{3a+r}{2}+\frac h8=-\frac d4
\]

if and only if

\[
6a+\ell+r=\tfrac32d,\qquad h=d-2\ell+2r.
\]

Here the scalar path-Laplacian entries are those of a pair (a/2,-a/2), the model Q* contribution is h/8, and the source entries are (d/2,-d/4). `recurrence_fine_residuals` applies this identity to each finite recurrence row. It does **not** prove that the frozen physical projection has these coefficients. In particular, the factor relating the recurrence variable to a physical fine field must be checked; the raw statement '(a,-a)' without a normalization is insufficient.

## 4. Exact remaining source target

The next useful target is the following **unproved** statement in the published harness. It pins the component, longitudinal offset, endpoints and normalization requested in round 1. It is a proposed sufficient source certificate, not a new assumption in a claimed GoalNeg2 proof.

```lean
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Balaban.SuTwoInner

∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
  let N := 4 * q * (R + 1)
  let D := flatData q R
  ∃ a : ℕ → ℝ,
    a N = 0 ∧
    (∀ j < N,
      6 * a j + (if j = 0 then 0 else a (j - 1)) + a (j + 1) =
        if j = 0 then (3 / 2 : ℝ) else 0) ∧
    ∃ (x : TwistSpace q R) (h : FSp (geomOf 2 1 (dilTower q R))),
      D.Q x = 0 ∧
      D.Ginv x + D.Qs h = canonicalSourceStencil q R ∧
      ∀ p : BIdx (geomOf 2 1 (dilTower q R)), (p.1 : ℕ) = 1 →
        let j := ((p.2.1.1 0).val - (2 * (R * q) + 4 * q)) / 2
        h p = (if p.2.1.2 = 1 then
          (if j = 0 then (1 : ℝ) else 0)
            - 2 * (if j = 0 then 0 else a (j - 1)) + 2 * a (j + 1)
          else 0) • pauliE3
```

One may weaken the q,R quantifiers to the required nested cofinal subsequence. The source is independent of whether the eventual crossing vector comes from the left-only or symmetric exterior twist.

What remains after this source target:

1. Aggregate the physical level-one direction-1 jet coefficients by longitudinal block and match that aggregate to the v_j consumed by nonvanishing's `BlockSourceData`. In particular, prove the physical transverse multiplicity/normalization, rather than importing it from the numerical cell.
2. Prove v0≠0 and |v_j|≤|v0| (or another nonvanishing criterion) for the relevant crossing vector.
3. Prove definiteness on the **entire** crossing kernel, including any neutral or additional-character components, at the nested cofinal scales/radii.

Full spatial covariance of W/Q/T and the assembled carrier, the character decomposition, dimensions, and competing-character spectral exclusion remain unproved here. No q=1 canonical-radius isometry is assumed; round 1's length-matching obstruction and the coordinator's withdrawal of that target remain in force.

### Question for the nonvanishing track, next round

Can you work with the physical aggregated jet

\[
v_j=\sum_{\substack{p:\,\mathrm{level}(p)=1,\ \mathrm{dir}(p)=1\\
 x_0(p)=2Rq+4q+2j}}\langle E_3,\mathrm{vacJet}(u)(p)\rangle
\]

rather than a numerically normalized cell jet? This would let the source certificate feed `sourcePairing` without first proving the full Fourier dictionary. Please confirm whether the intended a_j is twice the fine alternating amplitude, and which exact embedding realizes the model Q* coefficient h/8. I recommend proving the two physical certificate equations next; the source right-hand side is now an explicit compiled stencil.

## Post-delivery update: nonvanishing R2 removes jet domination

The subsequently received `shared/nonvanishing/R2_STATUS.md` reports the compiled positive-definite source-family theorem in `R2_SourceFamily.lean`. For a defect at block i, its proposed physical source dictionary is

\[
6a_j+a_{j-1}+a_{j+1}=\tfrac32\delta_{ji}+\tfrac12\delta_{j+1,i},
\qquad h_i(j)=\delta_{ji}-\delta_{j+1,i}-2a_{j-1}+2a_{j+1}.
\]

Their theorem supplies a nonzero pairing for some i whenever the finite jet vector is nonzero. Consequently jet domination is **no longer necessary** for this free-profile route. The fixed-source target in §4 is now a special case, not the recommended final restriction. Our arbitrary-profile `bulkSource_tendsto` already applies to each such defect profile; the pending task is the generalized physical KKT/source dictionary, then a nonzero actual jet and the whole-kernel criterion.

Their normalization clarification: a physical single-cell C2full coordinate has overall factor `2*(4*q)^2` after summing translated cells; a cell-normalized jet has factor 2 because the isometric lift contributes `1/(4*q)^2`. The level-one 1/2 is already inside C2full. Our physical BIdx sum avoids choosing between those conventions until the spatial identification is proved. Their 16 numerical KKT checks support this dictionary but are not a formal identification. I read the hand-off status; this update does not claim an independent recompile of that track's new file.

## 5. Reproduction and hygiene

From the repository root:

```sh
AHP/round3/lean1.sh AHP/round10/dictionary/r2/PhaseSource.lean
AHP/round3/lean1.sh AHP/round10/dictionary/r2/KKT.lean
python3 AHP/round10/dictionary/r2/build.py
AHP/round3/lean1.sh AHP/round10/dictionary/r2/Source.lean
AHP/round3/lean1.sh AHP/round10/shared/dictionary/R2_SourceDictionary.lean
python3 AHP/round10/dictionary/r2/audit.py
```

The helpers were developed first; no long historical-prefix compilation was attempted. Iterations corrected ordinary elaboration errors, a dependent-index rewrite, and the already-known concrete AddCommGroup calculus diamond. The latter was avoided by differentiating the full bond field and transporting its limit through pE. Every final standalone file is clean and has a fresh exit record.

No numerical solves, lake build, REPRODUCE.sh, commits, pushes, worktrees or new agents were run. All written files are under this round directory or the assigned shared dictionary directory. No earlier round, frozen source, protected area, or integration checkout was edited.

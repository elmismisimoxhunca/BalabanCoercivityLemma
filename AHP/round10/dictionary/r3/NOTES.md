# Dictionary round 3: exact free-profile curl energy and physical-jet detection

**GoalNeg2 remains OPEN. No original cofinal coupling premise is proved.** This round proves a new exact source dictionary and combines it with nonvanishing R3's actual blocking/flux theorem. It removes the tridiagonal source-column obligation on the **free-profile** route. It does not prove that a crossing vector has a nonzero quadratic jet, or identify the entire crossing kernel.

## 1. Compiled deliverables

- `AHP/round10/shared/dictionary/R3_FreeSource.lean`: 1590 lines; byte-identical local `Actual.lean`; both independently exit **0** with no warnings/errors. Sole import: frozen `DrEquiv`.
- `AHP/round10/shared/dictionary/R3_JetDetection.lean`: 2491 lines; byte-identical local `JetDetection.lean`; both independently exit **0** with no warnings/errors. Imports only frozen `DrEquiv` and `ZXR2Flat6`.
- `Scalar.lean`: 187-line standalone scalar summation-by-parts development; clean exit **0**.
- All five successful compilations use only `AHP/round3/lean1.sh`. Every new declaration has its own axiom print. `CHECKS.json` passes: **52 new dictionary declarations** (15 scalar, 30 actual-source, 7 joint application), 220 total dependency records in the combined publication, each contained in `{propext, Classical.choice, Quot.sound}`. No prohibited proof devices occur.
- `COPIES.json` verifies four exact R2 scalar-definition fragments, the complete unchanged R2 source harness prefix, and the retained body of the final nonvanishing R3 publication. Only duplicate `dilLu`/`dilTower` definitions and imports are omitted from the latter when combining; its theorems are not changed.

New namespaces:

- `AdalyFormal.Round10.Dictionary.SourceEnergy`
- `AdalyFormal.Round10.Dictionary.FreeSource`
- `AdalyFormal.Round10.Dictionary.JetDetection`

The main joint declaration is `JetDetection.curlDetected_of_topJet`. Its hypotheses are explicit and are not claimed to hold on a crossing vector.

## 2. Exact summation by parts for the actual R2 source

Use the norm-one frozen diagonal generator \(E_3=\operatorname{diag}(i,-i)\). For a real bond profile f, write

\[
c_f(p)=f(x,\mu)+f(x+e_\mu,\nu)-f(x+e_\nu,\mu)-f(x,\nu).
\]

R2 already proved that the true first-order source is the carrier projection of

\[
J'_P[f](b)=\mathrm{linearSourceScalar}(P,f)(b)E_3,
\]

where the scalar stencil is the backward divergence of the antisymmetric extension of \(c_f\), with the exact selector P. It is not an approximate curvature mask.

The new `SourceEnergy.source_sbp` proves on the full physical periodic torus

\[
\sum_b g(b)\,\mathrm{linearSourceScalar}(P,f)(b)
 =\sum_{p\in P}c_g(p)c_f(p).
\]

The proof uses the genuine finite-site shift equivalence to reindex each backward difference. The six off-diagonal ordered direction pairs combine into the three stored unoriented plaquettes. There are no boundary terms and no undetermined sign or factor. `source_reciprocity` and `source_energy` give symmetry and nonnegative scalar curl energy.

For an arbitrary su(2)-valued fine field w, define \(n(w)(b)=\langle E_3,w(b)\rangle\). The physical PiLp inner product is exactly the unweighted finite bond sum, so `inner_sourceLinear` gives

\[
\langle w,J'_P[f]\rangle=\sum_{p\in P}c_{n(w)}(p)c_f(p).
\]

The field w need **not** be neutral. Only its neutral coordinate couples to the diagonal source.

## 3. The full constrained lift gives an adaptive profile

Everything in this section uses the actual frozen operators. Put

\[
z_u=C^2_0(W_0\,i_Eu),\qquad
A_u=i_E(H_0z_u),\qquad
r_u(b)=\langle E_3,A_u(b)\rangle.
\]

- `Source.vacJet q R u` is z_u (already defined and compiled in R2).
- `FreeSource.responseProfile q R u` is r_u.
- H0 is the full constrained lift `flatData.H`, **not** an inverse of a compressed boundary block.

For any real f define

\[
F_f(u)=2\langle H_0z_u,J'[f]\rangle.
\]

This is `profileCoupling q R f u`, definitionally the original analytic `vacCoupling` with the R2 exact `profileSourceStencil`. No alternative carrier or model matrix is introduced.

The true family zeros f on purely exterior bonds before forming its source. `circulation_interiorProfile` proves that this zeroing changes no circulation on `plaqIn Omega0`: every boundary bond of such a plaquette has both endpoints in Omega0. Using `pE_inner_right` and the preceding summation-by-parts identity therefore proves, **for every q,R,f,u without unit or spectral hypotheses**,

\[
\boxed{F_f(u)=2\sum_{p\in\mathrm{plaqIn}(\Omega_0)}c_{r_u}(p)c_f(p).}
\]

This is `profileCoupling_curl`.

Choose the allowed free profile **f=r_u**. Then

\[
\boxed{F_{r_u}(u)=2\sum_{p\in\mathrm{plaqIn}(\Omega_0)}c_{r_u}(p)^2.}
\]

This is `adaptive_energy`; `adaptive_nonneg` proves nonnegativity. `responseProfile_off` and `responseProfile_interior` also prove that r_u itself vanishes on the exterior bond set, so the adaptive profile already has the correct support.

Define

```lean
def CurlDetected (q R : ℕ) (u : TwistSpace q R) : Prop :=
  ∃ p ∈ plaqIn ((dilTower q R).Om 0),
    circulation (responseProfile q R u) p ≠ 0
```

The exact, unconditional characterization is

```lean
exists_profile_iff_curlDetected :
  (∃ f, profileCoupling q R f u ≠ 0) ↔ CurlDetected q R u
```

`adaptive_pos_iff` strengthens the reverse implication: the particular adaptive profile gives **strictly positive** coupling exactly when CurlDetected holds. `all_profiles_zero_iff` identifies the precise failure: every profile couples to zero iff the full constrained lift's neutral coordinate is curl-free on all selected plaquettes.

This is more useful than the earlier proposed tridiagonal source lift for the unrestricted free-profile premise. There is no need to choose a translated single-site defect, solve a source column, prove jet domination, or rule out cancellation of that column's tail. The adaptive profile is allowed to depend on the chosen vacuum generator and on q,R; it is fixed before the small curvature parameter is chosen. Round 9 already provides positive scaling into the admissible profile bound.

**Important distinction:** these theorems concern the actual explicit H0-C2-J' form. The arbitrary-profile identification with `⟪u, corrDeriv q R f u⟫` is being handled by assembly R3 using the already-proved round-9 continuity/differentiability facts and R2's unconditional source limit. This dictionary does not replace that calculus step with an assumption hidden in an unconditional derivative theorem.

## 4. U(1) and the actual constraint interface

New unconditional U(1) facts:

- `phase_axis_fixed`: conjugation by every diagonal phase fixes the norm-one E3.
- `sourceLinear_U1`, `profileSource_U1`: every free-profile source is fixed by all constant diagonal phases.
- `profileCoupling_U1`: the explicit free-profile quadratic form is invariant under the same U(1).
- `profileNeutralSource_U1`, `profileNeutralSource_component`: the full H0*J'[f] is neutral, now for every profile without the canonical `IsSourceDerivative` premise.
- `profileCoupling_neutral_top_sum`: the exact physical level-one H0*J'/C2 sum now applies to every profile. Level-zero C2 vanishes as in R2.
- `flatQ_U1`: actual flat carrier Q intertwines the diagonal phase action.

The half-turn average has the exact normalization

\[
\tfrac12(X+\mathrm{Ad}_{g_{\pi/2}}X)=\langle E_3,X\rangle E_3
\]

(`half_average`). It is used, together with QH=1, to prove

\[
Q_0(r_uE_3)(p)=\langle E_3,z_u(p)\rangle E_3
\]

for every physical coarse-bond row (`responseField_Q`). This theorem requires precisely

```lean
IsUnit (Dictionary.KKT.N (flatData q R))
```

where `N D = (D.Q.comp D.G).comp D.Qs` is the **full** constraint matrix. No boundary compression occurs. `liftJet_Q` gives QH=1 directly for z_u with the same sole unit premise. `Q_level_zero` identifies a physical level-zero Q row with its fine bond entry; `responseProfile_level_zero` then gives an exact zero for r_u on every such row.

The N-unit premise is not a new conjectural spectral assumption: round 9 proves it at the admissible flat points (`dil_N0_unit`). It remains visible here because the long geometric unit proof is not copied into this compact harness. Even with it, the crossing-jet nonvanishing remains missing.

## 5. Joint application of nonvanishing R3: source recurrence and normalization bypassed

The combined publication includes the final compiled body of `shared/nonvanishing/R3_DilatedFlux.lean` (apart from duplicate geometry definitions/import lines). That track proves a genuine physical blocking dictionary and flux obstruction:

- every normalized direction-1 level-one Q row is the actual frozen two-site blocking jet;
- summing over all physical even transverse cells gives **1/8** of the sum of two adjacent fine-layer fluxes;
- scalar curl telescopes in the transverse torus;
- the level-zero constraints supply a zero collar flux;
- a nonzero top aggregate therefore forces a nonzero curl at an actual plaquette in `plaqIn Omega0`.

Its `TopJetDetected hq R u` is the concrete missing jet condition. Let

\[
N=4q(R+1),\quad p=2Rq+4q.
\]

It asks for some j<N such that the sum over **all physical even transverse cells** of

\[
\langle E_3,C^2_0(W_0i_Eu)(\mathrm{level}=1,\ (p+2j,2c_1,2c_2),\ \mathrm{dir}=1)\rangle
\]

is nonzero. The `C2fullOf` factor 1/2 is already inside these coordinates. There is no Bloch-cell cardinality convention or guessed multiplicity.

Our `JetDetection.physicalJetAggregate` is definitionally this quantity (`topJetDetected_iff`). The combined proof applies that track's `localized_curl_of_jetAggregate` with

\[
A=i_EH_0z_u,\quad v=W_0i_Eu,\quad\phi(X)=\langle E_3,X\rangle.
\]

The actual Q constraint equation is exactly `liftJet_Q`. The resulting scalar `curlValue` is definitionally R2's `circulation`. Thus the **joint actual-operator hand-off** compiles:

```lean
theorem curlDetected_of_topJet {q R : ℕ}
    (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (u : TwistSpace q R)
    (hjet : AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected hq R u) :
    AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected q R u
```

`curlDetected_of_physicalJet` is the indexed version. `adaptive_pos_of_physicalJet` and `exists_profile_of_physicalJet` give strict positive adaptive coupling and an existential nonzero free-profile coupling.

**These are conditional theorems. TopJetDetected is NOT proved for any actual crossing vector here.** The theorem does not need symmetry/character reduction, but cannot create a nonzero quadratic jet from a nonzero linear vector.

## 6. What remains, exactly

The source/coupling part now has a compiled path from a **nonzero actual aggregated jet** to an allowed profile with nonzero explicit coupling. The outstanding mathematical statements are:

1. **A genuine crossing jet is nonzero:** `TopJetDetected hq R u`, or directly `CurlDetected q R u`, for a suitable crossing generator.
2. **Whole-kernel definiteness:** for example, the entire vacuum kernel is the charged complex line generated by u. U(1) alone does not imply this and symmetry cannot exclude competing singular characters.
3. **Nested cofinal scales/radii:** unbounded dyadic exponents and, at each selected exponent, unbounded even R≥18. A finite grid, or one R per scale, does not suffice.

Using assembly R2's actual `KernelLine`, a precise sufficient still-UNPROVED target for the canonical path is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : AnalyticR1.TwistSpace (2^j) R,
    Assembly.R2.KernelLine (2^j) R (Qualitative.uthPath (2^j) R) u ∧
    Nonvanishing.DilatedFlux.TopJetDetected (by positivity : 0 < 2^j) R u
```

Abbreviations in this display refer to their full `AdalyFormal.Round9.Guarded`, `AdalyFormal.Round10.Assembly`, and `AdalyFormal.Round10.Nonvanishing` namespaces. The `KernelLine` predicate includes u≠0, the actual vacuum kernel equation at `vacEdge`, quarter-turn square -u, and containment of the **entire** kernel in the real span of u and its quarter turn. Assembly R3's any-path alternative can use a left-only path instead, with that path's continuity/analyticity, trivial start and negative endpoint separately supplied.

Choosing f=r_u independently for every vector does **not** make one f definite on a multidimensional kernel. That quantifier trap remains; assembly R2's compiled counterexample to the shortcut still applies. The charged-line criterion legitimately fixes one generator first and then one adaptive profile.

Not newly established: full spatial covariance of W/Q/T and assembled A/B/corrDeriv; transverse character decomposition and block dimensions; crossing simplicity/exclusion; any cofinal premise. R1's arithmetic obstruction to a canonical q=1 radius dilation remains in force. No exact q-dilation isometry is used.

### Question for nonvanishing / next round

Can the next round prove `TopJetDetected` for a genuine crossing generator, preferably with the left-only exterior path to avoid the tiny symmetric partner splitting? The source-column recurrence is no longer necessary on this route. Please identify the smallest remaining actual W/C2 or boundary-transfer stencil needed to prove **some physical aggregated neutral jet is nonzero**, rather than the canonical first jet or a cancellation estimate for a fixed source. KernelLine or an alternative common-sign whole-kernel argument remains a separate requirement; please do not infer it from U(1) commutation.

## 7. Reproduction, assembly and hygiene

From the repository root:

```sh
python3 AHP/round10/dictionary/r3/build.py
AHP/round3/lean1.sh AHP/round10/dictionary/r3/Scalar.lean
AHP/round3/lean1.sh AHP/round10/dictionary/r3/Actual.lean
AHP/round3/lean1.sh AHP/round10/dictionary/r3/JetDetection.lean
AHP/round3/lean1.sh AHP/round10/shared/dictionary/R3_FreeSource.lean
AHP/round3/lean1.sh AHP/round10/shared/dictionary/R3_JetDetection.lean
python3 AHP/round10/dictionary/r3/audit.py
```

`build.py` is idempotent when the inputs are unchanged. It writes only this r3 directory. For downstream full assembly, append `ScalarAppendix.lean`, `ActualAppendix.lean` and `JetAppendix.lean` after their existing R2 and nonvanishing dependencies; do not concatenate two complete harnesses with duplicate definitions. The added frozen import `ZXR2Flat6` is required for the nonvanishing proof.

Development fixed ordinary finite-sum simplification, dependent-index rewriting, matrix notation, name resolution and unused-binder warnings. A direct continuity proof of profileSource_U1 hit a concrete-instance elaboration timeout; it was replaced by the shorter exact algebraic proof using the diagonal generator. All **final** files have fresh clean exit records. No 12k-line historical assembly was compiled.

No numerics, build/REPRODUCE, commits, pushes, worktrees, other agents or protected-source changes were made. Written files are in `dictionary/r3/` and `shared/dictionary/`; at the coordinator's request exactly one new hand-off paragraph was added to `shared/GAPS.md`, without replacing existing content. No other track's Lean source or earlier-round file was edited.

Post-delivery compatibility refresh: nonvanishing changed only its copied `neutralFunctional` linearity proofs to direct inner-product lemmas. The combined local/shared `JetDetection` publications were regenerated and independently recompiled; both remain clean exit 0, with 220 standard-axiom records, and the refreshed copy audit passes. All mathematical statements and the remaining gaps are unchanged.

/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.CStarLevelCorrected

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `[SCHUR-NONZERO]` — the covariant Schur complement is NOT identically zero at `ell = 2`

**The decisive question.** `CovariantHjFaithful.deltaJQuadFormCovFaithful ell levels U A0` (the
minimized covariant curl energy `‖D_U H_j(A0)‖²`, standing for CMP99b (3.156)'s `Δ_j`) had never
been exhibited NONZERO at any `ell ≥ 2` anywhere in this tree: its only literal-`ell` appearances
were three at `ell = 1` (where `deltaJQuadFormCovFaithful_ell1_eq_dstarDQuadForm` says it IS the raw
curl energy — no Schur mechanism at all) and one at `ell = 2` where its value is `0`.

**Answer: NONZERO INSTANCE EXISTS.** This module exhibits one, kernel-checked, at
`ell = 2 = AdmissibleSubspace.witnessEll`, `U = trivialU witnessL`, `A0 = singleBondA0` (the
`suTwoWitness`-valued indicator of the single fine bond `(witnessY, 0)`), and — the strongest form —
for **EVERY** `levels : List (KernelSubspace.Level witnessL)`, hence in particular at every `levels`
whose `R`-clause is non-vacuous. See `deltaJQuadFormCovFaithful_pos_witnessEll`.

## The mechanism (this is exactly `CovariantHjMinimizer` §21's un-attempted option (b))

`§21` named two ways to pin the Schur complement strictly positive and attempted NEITHER: (a) a
closed-form projection onto `D_U(V)`, or (b) *"a linear functional vanishing identically on the
WHOLE of that image subspace but nonzero on `curl_U(A0)` for the chosen witness"*. This module
builds (b), in its **bond-side** form, which is cheaper than the plaquette-side dual witness
(`CStarLevelCorrected.deltaJQuadFormCovFaithful_pos_of_dual_witness`) because it needs the Stokes
identity in only ONE direction.

Write `Q := lineCoarseRestrictCovLM U ell` (the FAITHFUL covariant line-integral `Q_k(U)`),
`D := curlCovariantLM U`, and `V := gaugeConstraintSubspaceCovFaithful ell levels U`. Unwinding the
definitions,

    deltaJQuadFormCovFaithful ell levels U A0  =  ‖ D A0 − Π_{D(V)}(D A0) ‖²  =  dist(D A0, D V)² ,

so it vanishes **iff** `∃ v ∈ V, D v = D A0`. Since `V ⊆ ker Q` for EVERY `levels` (the `R`-clause
only shrinks `V`), that would force `Q A0 = Q (A0 − v) ∈ Q(ker D)`. Therefore:

> **`SchurNonzero.pos_of_functional`** — if `Ψ` is additive-and-`sub`-compatible on bond fields,
> factors through `Q` (so `Ψ` kills `ker Q ⊇ V`), kills `ker D`, and `Ψ A0 ≠ 0`, then
> `0 < deltaJQuadFormCovFaithful ell levels U A0`.

The `Ψ` built here is the **coarse curl of `Q A` at one coarse plaquette** (`Psi`, §2):

    Ψ A  =  (QA)(Y₀,0) + (QA)(Y₀+₂e₀,1) − (QA)(Y₀+₂e₁,0) − (QA)(Y₀,1),    Y₀ = witnessY .

It kills `ker Q` for free. That it kills `ker D` is the DISCRETE STOKES identity `Psi_eq_sum` +
`bracket_eq_curlSum` (§3): at `U = trivialU` the block-averaged line integral around the closed
coarse square of side `ell = 2` is the sum of the `2×2 = 4` fine curls it encloses,

    L₀(x) + L₁(x+2e₀) − L₀(x+2e₁) − L₁(x)  =  Σ_{i,j<2} (D_1 A)(x + i e₀ + j e₁, (0,1)) ,

averaged over the `8` sites of the block `B(Y₀)`. **This is the honest reason the object is not
vacuous: `Q(ker D)` is a PROPER subspace of coarse-bond space at `ell = 2`** — at `ell = 1` it is
everything (`Q` is injective there, `V = ⊥`), which is exactly the degeneracy this escapes.

## Scope / honesty

* `U = trivialU`. The Stokes identity above is the FLAT one; the general-`U` covariant version is
  Bałaban's own telescoping and is NOT proved here (`LineIntegralCovariant.lean` §4 already records
  that the general-`U` (1.20) intertwining FAILS by the curvature obstruction). What is settled is
  the question asked: the Schur complement is a REAL object at `ell ≥ 2`, not identically zero.
* The result is `∀ levels`, so it is insensitive to whether the `R`-clause is vacuous; **§6** PROVES
  (`kernelSubspaceCov_nil_eq_top`, `Rcov_clause_nonvacuous_nil`) that at `levels = []` we have
  `N(Q') = ⊤`, `R` projects onto the FULL range of `Δ₀^{cov}(U)`, and the named bond field
  `gradLamDelta` genuinely VIOLATES the `R`-clause — so the clause is NOT the vacuous one (contrast
  `oneLevelUniv`, where `RcovLM_oneLevelUniv_eq_zero` makes `R ≡ 0`). The dispatch's premise that
  `levels = []` collapses the clause is therefore FALSE, and is corrected here.
* **§7** PROVES `curlImageCovFaithful ≠ ⊥` at the same point, for every `levels`, so the projection
  `Π_{D(V)}` being subtracted is a projection onto a NONZERO subspace: the Schur mechanism is
  genuinely exercised, not the trivial no-op of the `ell = 1` degeneracy.
-/

namespace AdalyFormal.Balaban.SchurNonzero

open AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.KernelSubspace
  AdalyFormal.Balaban.CovariantHjMinimizer
  AdalyFormal.Balaban.LineIntegralCovariant
  AdalyFormal.Balaban.CovariantHjFaithful
  AdalyFormal.Balaban.CStarLevelCorrected
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_injective coarseShift_blockOf_eq_image)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond periodicLatticeShift_comm)

/-! ## §0 — THE ABSTRACT CRITERION: a bond-side functional killing `ker Q` and `ker D`

General in `L`, `ell`, `levels`, `U`. Nothing here is witness-specific. -/

variable {L : PeriodicLatticeExtent}

/-- **THE CRITERION** (`CovariantHjMinimizer` §21's option (b), bond-side form).

If a map `Psi` on fine bond fields
* is compatible with subtraction (`hsub`),
* vanishes whenever the FAITHFUL covariant coarse field `Q_k(U)A` vanishes (`hQ`) — hence vanishes
  on the whole gauge-tangent subspace `V`, for EVERY `levels`, since `V ⊆ ker Q`,
* vanishes whenever the covariant curl `D_U A` vanishes (`hD`),
* and does not vanish at `A0` (`hA0`),

then the Schur complement at `A0` is strictly positive. -/
theorem pos_of_functional {W : Type*} [AddCommGroup W] (ell : ℕ)
    (levels : List (KernelSubspace.Level L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    [(deltaKernelImageCovH U levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful ell levels U).HasOrthogonalProjection]
    (A0 : Bond L → SuTwo) (Psi : (Bond L → SuTwo) → W)
    (hsub : ∀ A B : Bond L → SuTwo, Psi (A - B) = Psi A - Psi B)
    (hQ : ∀ A : Bond L → SuTwo, lineCoarseRestrictCovLM U ell A = 0 → Psi A = 0)
    (hD : ∀ A : Bond L → SuTwo, curlCovariantLM U A = 0 → Psi A = 0)
    (hA0 : Psi A0 ≠ 0) :
    0 < deltaJQuadFormCovFaithful ell levels U A0 := by
  -- Positivity reduces to `D_U(H_j A0) ≠ 0`.
  refine covPlaqInner_self_pos_of_ne (X := curlCovariantLM U
    (hjExtensionCovFaithful ell levels U A0)) ?_
  intro hzero
  -- If it vanishes, `D_U A0` is FIXED by the projection onto `D_U(V)`, hence lies in `D_U(V)`.
  rw [curlCov_hjExtensionCovFaithful] at hzero
  have hfix : curlCovariantLM U A0
      = curlImageCovProjFaithful ell levels U (curlCovariantLM U A0) := by
    have := hzero
    unfold hjCorrectionTargetCovFaithful at this
    exact sub_eq_zero.mp this
  have hmem : curlCovariantLM U A0 ∈ curlImageCovFaithful ell levels U := by
    rw [hfix]; exact curlImageCovProjFaithful_mem ell levels U _
  obtain ⟨v, hv, hcurl⟩ := mem_curlImageCovFaithful_iff.mp hmem
  -- `A0 - v ∈ ker D_U`, so `Psi (A0 - v) = 0`; and `Psi v = 0` since `Q v = 0`.
  have hdiff : curlCovariantLM U (A0 - v) = 0 := by
    rw [map_sub, hcurl, sub_self]
  have hQv : lineCoarseRestrictCovLM U ell v = 0 :=
    (mem_gaugeConstraintSubspaceCovFaithful.mp hv).1
  have := hsub A0 v
  rw [hD _ hdiff, hQ v hQv, sub_zero] at this
  exact hA0 this.symm

#print axioms pos_of_functional

/-! ## §1 — the concrete geometry: `witnessL` (`4³`), `ell = 2`, the coarse square at `Y₀`

`witnessL = fun _ => 3` is the `4³` torus, `witnessEll = 2` divides `4` in every direction, so the
blocks are genuine full `2³` blocks (no `blockOf` truncation) and the coarse lattice is a `2³`
torus — big enough for a NON-DEGENERATE coarse plaquette, which the minimal `2³` fine torus (one
single coarse site) would not be. -/

/-- The coarse-lattice base point `Y₀ = witnessY = 0`. -/
def cY0 : {y : PeriodicLatticeSite witnessL // y ∈ CoarseLattice witnessL 2} :=
  ⟨witnessY, by decide⟩

/-- `Y₀ + 2e₀` — the next coarse point in direction `0`. -/
def cY0s0 : {y : PeriodicLatticeSite witnessL // y ∈ CoarseLattice witnessL 2} :=
  ⟨coarseShift witnessY 2 0, by decide⟩

/-- `Y₀ + 2e₁` — the next coarse point in direction `1`. -/
def cY0s1 : {y : PeriodicLatticeSite witnessL // y ∈ CoarseLattice witnessL 2} :=
  ⟨coarseShift witnessY 2 1, by decide⟩

/-- `witnessEll = 2` divides the extent `witnessL μ + 1 = 4` in every direction. -/
theorem witnessHdvd (μ : Fin 3) : (2 : ℕ) ∣ (witnessL μ + 1) := by
  show (2 : ℕ) ∣ 4
  norm_num

/-- `witnessY` is a coarse-lattice point at `ell = 2`. -/
theorem witnessY_coarse2 : witnessY ∈ CoarseLattice witnessL 2 := by decide

/-! ## §2 — `Psi`: the COARSE CURL of `Q_2(U)A` at the coarse plaquette `(Y₀, 0, 1)` -/

/-- **`Ψ A := (QA)(Y₀,0) + (QA)(Y₀+2e₀,1) − (QA)(Y₀+2e₁,0) − (QA)(Y₀,1)`** — the coarse curl of the
FAITHFUL covariant coarse field at one coarse plaquette. Manifestly a function of `Q A` alone, so it
kills `ker Q ⊇ V` for every `levels` (`Psi_of_Q_eq_zero`). -/
noncomputable def Psi (A : Bond witnessL → SuTwo) : SuTwo :=
  lineCoarseRestrictCov (trivialU witnessL) 2 A (cY0, 0)
    + lineCoarseRestrictCov (trivialU witnessL) 2 A (cY0s0, 1)
    - lineCoarseRestrictCov (trivialU witnessL) 2 A (cY0s1, 0)
    - lineCoarseRestrictCov (trivialU witnessL) 2 A (cY0, 1)

theorem Psi_sub (A B : Bond witnessL → SuTwo) : Psi (A - B) = Psi A - Psi B := by
  have h : ∀ b : CoarseBond witnessL 2,
      lineCoarseRestrictCov (trivialU witnessL) 2 (A - B) b
        = lineCoarseRestrictCov (trivialU witnessL) 2 A b
          - lineCoarseRestrictCov (trivialU witnessL) 2 B b := by
    intro b
    have := (lineCoarseRestrictCovLM (trivialU witnessL) 2).map_sub A B
    exact congrFun this b
  unfold Psi
  rw [h, h, h, h]
  abel

/-- `Psi` factors through `Q`, so it kills `ker Q` — in particular the whole gauge-tangent subspace
`V`, for EVERY `levels`. -/
theorem Psi_of_Q_eq_zero (A : Bond witnessL → SuTwo)
    (h : lineCoarseRestrictCovLM (trivialU witnessL) 2 A = 0) : Psi A = 0 := by
  have h0 : ∀ b : CoarseBond witnessL 2, lineCoarseRestrictCov (trivialU witnessL) 2 A b = 0 := by
    intro b
    have := congrFun h b
    simpa [lineCoarseRestrictCovLM_apply] using this
  unfold Psi
  rw [h0, h0, h0, h0]
  abel

#print axioms Psi_sub
#print axioms Psi_of_Q_eq_zero

/-! ## §3 — DISCRETE STOKES: `Psi` kills `ker D_{trivialU}`

The per-site bracket `bracket A x` is the sum of the four length-2 line integrals around the closed
coarse square based at `x`; `bracket_eq_curlSum` identifies it with the sum of the `2×2` fine curls
it encloses, and `Psi_eq_sum` exhibits `Psi A` as the block average of that bracket. -/

/-- The four length-`2` line integrals around the closed square of side `2` based at `x`, in the
`(0,1)` plane, oriented `x → x+2e₀ → x+2e₀+2e₁ → x+2e₁ → x`. -/
noncomputable def bracket (A : Bond witnessL → SuTwo) (x : PeriodicLatticeSite witnessL) : SuTwo :=
  (A (x, 0) + A (periodicLatticeShift x 0, 0))
    + (A (coarseShift x 2 0, 1) + A (periodicLatticeShift (coarseShift x 2 0) 1, 1))
    - (A (coarseShift x 2 1, 0) + A (periodicLatticeShift (coarseShift x 2 1) 0, 0))
    - (A (x, 1) + A (periodicLatticeShift x 1, 1))

/-- The `(0,1)` plaquette direction pair. -/
def dirs01 : PeriodicPlaquetteDirections := ⟨(0, 1), by decide⟩

/-- **`Psi A` is the block average of `bracket A`** over the `2³` block `B(Y₀)` — the two shifted
blocks are re-indexed onto `B(Y₀)` by `coarseShift_blockOf_eq_image` (LAW-19). -/
theorem Psi_eq_sum (A : Bond witnessL → SuTwo) :
    Psi A = (1 / (2 : ℝ) ^ 4) • ∑ x ∈ blockOf witnessY 2, bracket A x := by
  have hB0 : blockOf (coarseShift witnessY 2 0) 2
      = Finset.image (fun x : PeriodicLatticeSite witnessL => coarseShift x 2 0)
          (blockOf witnessY 2) :=
    coarseShift_blockOf_eq_image (by norm_num) (witnessHdvd 0) witnessY_coarse2
  have hB1 : blockOf (coarseShift witnessY 2 1) 2
      = Finset.image (fun x : PeriodicLatticeSite witnessL => coarseShift x 2 1)
          (blockOf witnessY 2) :=
    coarseShift_blockOf_eq_image (by norm_num) (witnessHdvd 1) witnessY_coarse2
  unfold Psi
  rw [lineCoarseRestrictCov_trivialU, lineCoarseRestrictCov_trivialU,
    lineCoarseRestrictCov_trivialU, lineCoarseRestrictCov_trivialU]
  show (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf cY0.1 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (0 : Fin 3) i, (0 : Fin 3)))
      + (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf cY0s0.1 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (1 : Fin 3) i, (1 : Fin 3)))
      - (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf cY0s1.1 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (0 : Fin 3) i, (0 : Fin 3)))
      - (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf cY0.1 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (1 : Fin 3) i, (1 : Fin 3))) = _
  show (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf witnessY 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (0 : Fin 3) i, (0 : Fin 3)))
      + (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf (coarseShift witnessY 2 0) 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (1 : Fin 3) i, (1 : Fin 3)))
      - (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf (coarseShift witnessY 2 1) 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (0 : Fin 3) i, (0 : Fin 3)))
      - (1 / (2 : ℝ) ^ 4) • (∑ x ∈ blockOf witnessY 2, ∑ i ∈ Finset.range 2,
        A (pathSite x (1 : Fin 3) i, (1 : Fin 3))) = _
  rw [hB0, hB1,
    Finset.sum_image (fun x _ x' _ hxx' => coarseShift_injective 2 0 hxx'),
    Finset.sum_image (fun x _ x' _ hxx' => coarseShift_injective 2 1 hxx')]
  rw [← smul_add, ← smul_sub, ← smul_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold bracket
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pathSite_zero, pathSite_succ]

/-- **THE STOKES IDENTITY.** The closed coarse square of side `2` equals the sum of the four fine
plaquette curls it encloses. Uses shift commutativity in the two distinct directions `0 ≠ 1` three
times — the identity is FALSE without it. -/
theorem bracket_eq_curlSum (A : Bond witnessL → SuTwo) (x : PeriodicLatticeSite witnessL) :
    bracket A x =
      curlValueCovariant (trivialU witnessL) A (x, dirs01)
        + curlValueCovariant (trivialU witnessL) A (periodicLatticeShift x 0, dirs01)
        + curlValueCovariant (trivialU witnessL) A (periodicLatticeShift x 1, dirs01)
        + curlValueCovariant (trivialU witnessL) A
            (periodicLatticeShift (periodicLatticeShift x 1) 0, dirs01) := by
  have hne : (0 : Fin 3) ≠ 1 := by decide
  have hcs : ∀ (z : PeriodicLatticeSite witnessL) (μ : Fin 3),
      coarseShift z 2 μ = periodicLatticeShift (periodicLatticeShift z μ) μ := by
    intro z μ
    simp [coarseShift, Function.iterate_succ]
  have hRone : ∀ X : SuTwo, RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) X = X := by
    intro X; rw [RMap_one]; rfl
  simp only [bracket, hcs, curlValueCovariant, trivialU, dirs01, hRone]
  -- normalise all mixed shift words to `shift·1` applied inside `shift·0`
  rw [periodicLatticeShift_comm (periodicLatticeShift x 0) hne,
    periodicLatticeShift_comm x hne,
    periodicLatticeShift_comm (periodicLatticeShift x 1) hne]
  abel

/-- `Psi` kills `ker D_{trivialU}` — the (c) hypothesis of the criterion. -/
theorem Psi_of_curl_eq_zero (A : Bond witnessL → SuTwo)
    (h : curlCovariantLM (trivialU witnessL) A = 0) : Psi A = 0 := by
  have hp : ∀ p : PeriodicLatticePlaquette witnessL,
      curlValueCovariant (trivialU witnessL) A p = 0 := by
    intro p
    have := congrFun h p
    simpa [curlCovariantLM] using this
  rw [Psi_eq_sum]
  have hz : ∀ x ∈ blockOf witnessY 2, bracket A x = 0 := by
    intro x _
    rw [bracket_eq_curlSum, hp, hp, hp, hp]
    abel
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, smul_zero]

#print axioms bracket_eq_curlSum
#print axioms Psi_eq_sum
#print axioms Psi_of_curl_eq_zero

/-! ## §4 — the witness field `A0`, and `Psi A0 ≠ 0` -/

/-- **`A0` — the `suTwoWitness`-valued indicator of the single fine bond `(witnessY, 0)`.** -/
noncomputable def singleBondA0 : Bond witnessL → SuTwo :=
  fun e => if e = (witnessY, (0 : Fin 3)) then suTwoWitness else 0

theorem singleBondA0_dir0 (y : PeriodicLatticeSite witnessL) :
    singleBondA0 (y, (0 : Fin 3)) = if y = witnessY then suTwoWitness else 0 := by
  unfold singleBondA0
  simp [Prod.ext_iff]

theorem singleBondA0_dir1 (y : PeriodicLatticeSite witnessL) :
    singleBondA0 (y, (1 : Fin 3)) = 0 := by
  unfold singleBondA0
  simp [Prod.ext_iff]

/-- **`Psi A0 = (1/16)·suTwoWitness`.** Only the base term survives: `witnessY ∈ B(Y₀)` contributes
once, and every other of the seven summands is killed by a `decide`-checked geometric fact (the
`e₀`-predecessor of `witnessY` leaves the block; the whole `Y₀+2e₁` block has `e₁`-coordinate `2`
or `3`, so never reaches `witnessY`). -/
theorem Psi_singleBondA0 : Psi singleBondA0 = (1 / (2 : ℝ) ^ 4) • suTwoWitness := by
  rw [Psi_eq_sum]
  congr 1
  have hb : ∀ x ∈ blockOf witnessY 2,
      bracket singleBondA0 x = (if x = witnessY then suTwoWitness else 0) := by
    intro x _
    unfold bracket
    rw [singleBondA0_dir0, singleBondA0_dir0, singleBondA0_dir1, singleBondA0_dir1,
      singleBondA0_dir1, singleBondA0_dir1, singleBondA0_dir0, singleBondA0_dir0]
    have h1 : ∀ z : PeriodicLatticeSite witnessL, z ∈ blockOf witnessY 2 →
        (periodicLatticeShift z 0 ≠ witnessY ∧ coarseShift z 2 1 ≠ witnessY ∧
          periodicLatticeShift (coarseShift z 2 1) 0 ≠ witnessY) := by decide
    obtain ⟨e1, e2, e3⟩ := h1 x ‹_›
    rw [if_neg e1, if_neg e2, if_neg e3]
    abel
  rw [Finset.sum_congr rfl hb, Finset.sum_ite_eq' (blockOf witnessY 2) witnessY
    (fun _ => suTwoWitness), if_pos (by decide : witnessY ∈ blockOf witnessY 2)]

theorem Psi_singleBondA0_ne_zero : Psi singleBondA0 ≠ 0 := by
  rw [Psi_singleBondA0]
  exact smul_ne_zero (by norm_num) suTwoWitness_ne_zero

#print axioms Psi_singleBondA0
#print axioms Psi_singleBondA0_ne_zero

/-! ## §5 — THE HEADLINE: the covariant Schur complement is STRICTLY POSITIVE at `ell = 2` -/

/-- **THE ANSWER: NONZERO INSTANCE.** At `ell = 2 = witnessEll` (`≥ 2`, and the blocks are genuine
full `2³` blocks: `2 ∣ witnessL μ + 1 = 4`), at the trivial background on the `4³` torus, at the
single-bond field `A0`, and for **EVERY** `levels` — so in particular at every `levels` whose
`R`-clause is non-vacuous, and NOT by any degeneracy of the gauge-fixing clause — the minimized
covariant curl energy standing for CMP99b (3.156)'s `Δ_j` is STRICTLY POSITIVE. -/
theorem deltaJQuadFormCovFaithful_pos_witnessEll
    (levels : List (KernelSubspace.Level witnessL))
    [(deltaKernelImageCovH (trivialU witnessL) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful 2 levels (trivialU witnessL)).HasOrthogonalProjection] :
    0 < deltaJQuadFormCovFaithful 2 levels (trivialU witnessL) singleBondA0 :=
  pos_of_functional 2 levels (trivialU witnessL) singleBondA0 Psi Psi_sub
    Psi_of_Q_eq_zero Psi_of_curl_eq_zero Psi_singleBondA0_ne_zero

#print axioms deltaJQuadFormCovFaithful_pos_witnessEll

/-- The same statement written at `AdmissibleSubspace.witnessEll` (definitionally `2`), matching the
name the rest of the tree uses. -/
theorem deltaJQuadFormCovFaithful_pos_at_witnessEll
    (levels : List (KernelSubspace.Level witnessL))
    [(deltaKernelImageCovH (trivialU witnessL) levels).HasOrthogonalProjection]
    [(curlImageCovHFaithful witnessEll levels (trivialU witnessL)).HasOrthogonalProjection] :
    0 < deltaJQuadFormCovFaithful witnessEll levels (trivialU witnessL) singleBondA0 :=
  deltaJQuadFormCovFaithful_pos_witnessEll levels

#print axioms deltaJQuadFormCovFaithful_pos_at_witnessEll

/-! ## §6 — the `R`-clause is NOT vacuous at `levels = []` (correcting the dispatch's premise)

The dispatch's premise was that `levels = []` makes the gauge-fixing clause vacuous. It does not:
`kernelSubspaceCov [] = ⊤`, so `R^{cov}(U)` projects onto the FULL range of `Δ₀^{cov}(U)`, which is
nonzero. Concretely `gradLamDelta := D_{trivialU}(δ_{witnessY}·suTwoWitness)` is a bond field whose
covariant divergence is `6·suTwoWitness` at `witnessY`, and `R` FIXES it — so `gradLamDelta`
violates the `R`-clause and `V` is a strictly smaller set than "no constraint at all". (Contrast
`oneLevelUniv`, where `RcovLM_oneLevelUniv_eq_zero` makes `R ≡ 0` and the clause IS vacuous.) -/

theorem kernelSubspaceCov_nil_eq_top :
    kernelSubspaceCov ([] : List (KernelSubspace.Level witnessL)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun lam => ?_
  rw [mem_kernelSubspaceCov]
  intro lvl hlvl
  simp at hlvl

/-- `RMap 1 = id`, as a pointwise rewrite. -/
theorem RMap_trivial (X : SuTwo) : RMap (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) X = X := by
  rw [RMap_one]; rfl

theorem trivialU_apply (b : Bond witnessL) : (trivialU witnessL) b = 1 := rfl

/-- The covariant divergence at the trivial background is the flat one. -/
theorem adjoint_trivialU (A : Bond witnessL → SuTwo) (y : PeriodicLatticeSite witnessL) :
    gradCovariantAdjointLM (trivialU witnessL) A y =
      ∑ μ : Fin 3, (A (periodicLatticeShiftBack y μ, μ) - A (y, μ)) := by
  rw [gradCovariantAdjointLM_apply]
  unfold gradCovariantAdjointValue
  simp only [trivialU_apply, inv_one, RMap_trivial]

/-- The covariant gradient at the trivial background is the flat one. -/
theorem grad_trivialU (lam : PeriodicLatticeSite witnessL → SuTwo) (b : Bond witnessL) :
    gradCovariantLM (trivialU witnessL) lam b =
      lam (periodicLatticeShift b.1 b.2) - lam b.1 := by
  show gradValueCovariant (trivialU witnessL) lam b = _
  unfold gradValueCovariant
  rw [trivialU_apply, RMap_trivial]

/-- `λ = δ_{witnessY}·suTwoWitness`. -/
noncomputable def lamDelta : PeriodicLatticeSite witnessL → SuTwo :=
  fun y => if y = witnessY then suTwoWitness else 0

/-- `A' := D_{trivialU} λ` — a bond field the `R`-clause EXCLUDES. -/
noncomputable def gradLamDelta : Bond witnessL → SuTwo :=
  gradCovariantLM (trivialU witnessL) lamDelta

/-- `Δ₀^{cov}(trivialU) λ = 6·suTwoWitness` at the base site: the six lattice neighbours of
`witnessY` on the `4³` torus are all distinct from `witnessY` (`decide`), so nothing cancels. -/
theorem div_gradLamDelta_at_base :
    gradCovariantAdjointLM (trivialU witnessL) gradLamDelta witnessY
      = (6 : ℝ) • suTwoWitness := by
  rw [adjoint_trivialU]
  have hg : ∀ b : Bond witnessL, gradLamDelta b
      = lamDelta (periodicLatticeShift b.1 b.2) - lamDelta b.1 := by
    intro b; exact grad_trivialU lamDelta b
  simp only [hg, periodicLatticeShift_shiftBack, Fin.sum_univ_three]
  have hbase : lamDelta witnessY = suTwoWitness := by
    unfold lamDelta; rw [if_pos rfl]
  have hb0 : lamDelta (periodicLatticeShiftBack witnessY 0) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShiftBack witnessY 0 ≠ witnessY)]
  have hb1 : lamDelta (periodicLatticeShiftBack witnessY 1) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShiftBack witnessY 1 ≠ witnessY)]
  have hb2 : lamDelta (periodicLatticeShiftBack witnessY 2) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShiftBack witnessY 2 ≠ witnessY)]
  have hf0 : lamDelta (periodicLatticeShift witnessY 0) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShift witnessY 0 ≠ witnessY)]
  have hf1 : lamDelta (periodicLatticeShift witnessY 1) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShift witnessY 1 ≠ witnessY)]
  have hf2 : lamDelta (periodicLatticeShift witnessY 2) = 0 := by
    unfold lamDelta
    rw [if_neg (by decide : periodicLatticeShift witnessY 2 ≠ witnessY)]
  rw [hbase, hb0, hb1, hb2, hf0, hf1, hf2]
  have h6 : (6 : ℝ) • suTwoWitness
      = suTwoWitness + suTwoWitness + suTwoWitness
        + suTwoWitness + suTwoWitness + suTwoWitness := by
    rw [show (6 : ℝ) = 1 + 1 + 1 + 1 + 1 + 1 by norm_num]
    simp only [add_smul, one_smul]
  rw [h6]
  abel

theorem div_gradLamDelta_ne_zero :
    gradCovariantAdjointLM (trivialU witnessL) gradLamDelta ≠ 0 := by
  intro h
  have hy := congrFun h witnessY
  rw [div_gradLamDelta_at_base] at hy
  exact suTwoWitness_ne_zero (by
    have := smul_eq_zero.mp hy
    rcases this with h6 | hw
    · exact absurd h6 (by norm_num)
    · exact hw)

/-- **`R^{cov}(trivialU)` at `levels = []` FIXES the divergence of `gradLamDelta`**, which is
nonzero — so the `R`-clause of `V` genuinely EXCLUDES the bond field `gradLamDelta`. The clause is
not vacuous. -/
theorem Rcov_nil_fixes_div_gradLamDelta
    [(deltaKernelImageCovH (trivialU witnessL)
        ([] : List (KernelSubspace.Level witnessL))).HasOrthogonalProjection] :
    RcovLM (trivialU witnessL) ([] : List (KernelSubspace.Level witnessL))
        (gradCovariantAdjointLM (trivialU witnessL) gradLamDelta)
      = gradCovariantAdjointLM (trivialU witnessL) gradLamDelta := by
  have hmem : (siteFnEquiv witnessL).symm
      (gradCovariantAdjointLM (trivialU witnessL) gradLamDelta)
      ∈ deltaKernelImageCovH (trivialU witnessL) ([] : List (KernelSubspace.Level witnessL)) := by
    rw [mem_deltaKernelImageCovH]
    have hval : siteFnEquiv witnessL ((siteFnEquiv witnessL).symm
        (gradCovariantAdjointLM (trivialU witnessL) gradLamDelta))
        = gradCovariantAdjointLM (trivialU witnessL) gradLamDelta := by simp
    rw [hval]
    refine Submodule.mem_map_of_mem (f := siteLaplacianCovLM (trivialU witnessL))
      (r := lamDelta) ?_
    rw [kernelSubspaceCov_nil_eq_top]
    exact Submodule.mem_top
  show RcovFun (trivialU witnessL) ([] : List (KernelSubspace.Level witnessL)) _ = _
  unfold RcovFun
  rw [Submodule.starProjection_eq_self_iff.mpr hmem]
  simp

/-- **The `R`-clause is NOT vacuous at `levels = []`**: the NAMED bond field `gradLamDelta`
violates it. Stated with the witness in the statement (no `∃` over free bond data, S91). -/
theorem Rcov_clause_nonvacuous_nil
    [(deltaKernelImageCovH (trivialU witnessL)
        ([] : List (KernelSubspace.Level witnessL))).HasOrthogonalProjection] :
    RcovLM (trivialU witnessL) ([] : List (KernelSubspace.Level witnessL))
        (gradCovariantAdjointLM (trivialU witnessL) gradLamDelta) ≠ 0 := by
  rw [Rcov_nil_fixes_div_gradLamDelta]
  exact div_gradLamDelta_ne_zero

#print axioms kernelSubspaceCov_nil_eq_top
#print axioms div_gradLamDelta_at_base
#print axioms Rcov_nil_fixes_div_gradLamDelta
#print axioms Rcov_clause_nonvacuous_nil

/-! ## §7 — the Schur mechanism is genuinely EXERCISED: `D_U(V) ≠ ⊥`

`deltaJQuadFormCovFaithful` subtracts the projection onto `W = D_U(V)`. If `W` were `⊥` the
"minimization" would be a no-op and the object would just be `dstarDQuadForm` again (which is
exactly what happens at `ell = 1`). Here `W ≠ ⊥`, for EVERY `levels`: the witness is a
divergence-free, coarse-null, NON-closed field. -/

/-- `+1` on the plane `x₁ = 0 ∧ x₂ = 0`, `−1` on `x₁ = 1 ∧ x₂ = 0`, `0` elsewhere. Independent of
`x₀` — that is what makes the direction-`0` field it multiplies divergence-free. -/
def planeProfile (x : PeriodicLatticeSite witnessL) : ℝ :=
  (if x 1 = 0 ∧ x 2 = 0 then (1 : ℝ) else 0) - (if x 1 = 1 ∧ x 2 = 0 then (1 : ℝ) else 0)

/-- The witness element of `V`: `planeProfile · suTwoWitness` on direction-`0` bonds. -/
noncomputable def loopV : Bond witnessL → SuTwo :=
  fun e => if e.2 = (0 : Fin 3) then planeProfile e.1 • suTwoWitness else 0

theorem loopV_dir0 (x : PeriodicLatticeSite witnessL) :
    loopV (x, (0 : Fin 3)) = planeProfile x • suTwoWitness := by
  unfold loopV; rw [if_pos rfl]

theorem loopV_dir1 (x : PeriodicLatticeSite witnessL) : loopV (x, (1 : Fin 3)) = 0 := by
  unfold loopV; rw [if_neg (by decide : (1 : Fin 3) ≠ 0)]

theorem loopV_dir2 (x : PeriodicLatticeSite witnessL) : loopV (x, (2 : Fin 3)) = 0 := by
  unfold loopV; rw [if_neg (by decide : (2 : Fin 3) ≠ 0)]

/-- `planeProfile` is invariant under shifts in direction `0` (both ways) — it reads only
coordinates `1` and `2`. -/
theorem planeProfile_shift0 (x : PeriodicLatticeSite witnessL) :
    planeProfile (periodicLatticeShift x 0) = planeProfile x := by
  unfold planeProfile periodicLatticeShift
  rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]

theorem planeProfile_shiftBack0 (x : PeriodicLatticeSite witnessL) :
    planeProfile (periodicLatticeShiftBack x 0) = planeProfile x := by
  unfold planeProfile periodicLatticeShiftBack
  rw [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]

/-- **`loopV` is covariantly divergence-free** at the trivial background. -/
theorem loopV_div_eq_zero : gradCovariantAdjointLM (trivialU witnessL) loopV = 0 := by
  funext y
  rw [adjoint_trivialU, Fin.sum_univ_three]
  rw [loopV_dir0, loopV_dir0, loopV_dir1, loopV_dir1, loopV_dir2, loopV_dir2,
    planeProfile_shiftBack0]
  simp

/-- The `blockOf` block sum of `planeProfile` vanishes at every coarse point — the two planes
contribute equal counts, checked exhaustively on the `4³` lattice. -/
theorem planeProfile_block_sum (y : PeriodicLatticeSite witnessL)
    (hy : y ∈ CoarseLattice witnessL 2) :
    ∑ x ∈ blockOf y 2, planeProfile x = 0 := by
  have hcard : ((blockOf y 2).filter (fun x => x 1 = 0 ∧ x 2 = 0)).card
      = ((blockOf y 2).filter (fun x => x 1 = 1 ∧ x 2 = 0)).card := by
    revert hy
    revert y
    decide
  unfold planeProfile
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hcard, sub_self]

/-- **`loopV` has vanishing FAITHFUL coarse field** `Q_2(trivialU) loopV = 0`. -/
theorem loopV_Q_eq_zero :
    lineCoarseRestrictCovLM (trivialU witnessL) 2 loopV = 0 := by
  funext b
  show lineCoarseRestrictCov (trivialU witnessL) 2 loopV b = 0
  rw [lineCoarseRestrictCov_trivialU]
  unfold lineCoarseRestrictSuTwo
  rcases Decidable.em (b.2 = (0 : Fin 3)) with h0 | h0
  · have hstep : ∀ x ∈ blockOf b.1.1 2,
        (∑ i ∈ Finset.range 2, loopV (pathSite x b.2 i, b.2))
          = ((2 : ℝ) * planeProfile x) • suTwoWitness := by
      intro x _
      rw [h0]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pathSite_zero,
        pathSite_succ, loopV_dir0, planeProfile_shift0]
      rw [show (2 : ℝ) * planeProfile x = planeProfile x + planeProfile x by ring, add_smul]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_smul, ← Finset.mul_sum,
      planeProfile_block_sum b.1.1 b.1.2, mul_zero, zero_smul, smul_zero]
  · have hstep : ∀ x ∈ blockOf b.1.1 2,
        (∑ i ∈ Finset.range 2, loopV (pathSite x b.2 i, b.2)) = 0 := by
      intro x _
      have hz : ∀ z : PeriodicLatticeSite witnessL, loopV (z, b.2) = 0 := by
        intro z; unfold loopV; rw [if_neg h0]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const_zero, smul_zero]

/-- **`loopV` lies in the gauge-tangent subspace `V`, for EVERY `levels`.** -/
theorem loopV_mem_V (levels : List (KernelSubspace.Level witnessL))
    [(deltaKernelImageCovH (trivialU witnessL) levels).HasOrthogonalProjection] :
    loopV ∈ gaugeConstraintSubspaceCovFaithful 2 levels (trivialU witnessL) := by
  refine mem_gaugeConstraintSubspaceCovFaithful.mpr ⟨loopV_Q_eq_zero, ?_⟩
  rw [loopV_div_eq_zero, map_zero]

/-- **`loopV` is NOT closed**: its covariant curl is `2·suTwoWitness` at the base plaquette. -/
theorem loopV_curl_ne_zero : curlCovariantLM (trivialU witnessL) loopV ≠ 0 := by
  intro h
  have hp := congrFun h (witnessY, dirs01)
  have hval : curlValueCovariant (trivialU witnessL) loopV (witnessY, dirs01)
      = suTwoWitness + suTwoWitness := by
    unfold curlValueCovariant dirs01
    simp only [trivialU_apply, RMap_trivial]
    rw [loopV_dir0, loopV_dir1, loopV_dir0, loopV_dir1]
    have ha : witnessY 1 = 0 ∧ witnessY 2 = 0 := by decide
    have hb : ¬(witnessY 1 = 1 ∧ witnessY 2 = 0) := by decide
    set z : PeriodicLatticeSite witnessL := periodicLatticeShift witnessY 1 with hz
    have hc : ¬(z 1 = 0 ∧ z 2 = 0) := by rw [hz]; decide
    have hd : z 1 = 1 ∧ z 2 = 0 := by rw [hz]; decide
    have h1 : planeProfile witnessY = 1 := by
      unfold planeProfile
      rw [if_pos ha, if_neg hb, sub_zero]
    have h2 : planeProfile (periodicLatticeShift witnessY 1) = -1 := by
      unfold planeProfile
      rw [if_neg hc, if_pos hd, zero_sub]
    rw [h1, h2]
    simp
  rw [show curlCovariantLM (trivialU witnessL) loopV (witnessY, dirs01)
      = curlValueCovariant (trivialU witnessL) loopV (witnessY, dirs01) from rfl, hval] at hp
  exact suTwoWitness_ne_zero (by
    have : suTwoWitness + suTwoWitness = (2 : ℝ) • suTwoWitness := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
    rw [this] at hp
    rcases smul_eq_zero.mp hp with h2 | hw
    · exact absurd h2 (by norm_num)
    · exact hw)

/-- **THE MECHANISM IS EXERCISED**: `W = D_U(V) ≠ ⊥` at exactly the point where the Schur complement
is proved positive — so the projection subtracted in `deltaJQuadFormCovFaithful` is a projection
onto a NONZERO subspace, not the trivial no-op of the `ell = 1` degeneracy. Holds for EVERY
`levels`. -/
theorem curlImageCovFaithful_ne_bot (levels : List (KernelSubspace.Level witnessL))
    [(deltaKernelImageCovH (trivialU witnessL) levels).HasOrthogonalProjection] :
    curlImageCovFaithful 2 levels (trivialU witnessL) ≠ ⊥ := by
  intro hbot
  refine loopV_curl_ne_zero ?_
  have hmem : curlCovariantLM (trivialU witnessL) loopV
      ∈ curlImageCovFaithful 2 levels (trivialU witnessL) :=
    curl_mem_curlImageCovFaithful_of_mem (loopV_mem_V levels)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

#print axioms loopV_div_eq_zero
#print axioms planeProfile_block_sum
#print axioms loopV_Q_eq_zero
#print axioms loopV_curl_ne_zero
#print axioms curlImageCovFaithful_ne_bot

/-! ## §8 — AXIOM AUDIT: `#print axioms` on EVERY remaining declaration of this module

The 19 audits above cover the headline chain; these cover the fifteen small helper lemmas too, so
that no declaration in the file is unaudited in isolation (OPS-11a validator finding). -/

#print axioms witnessHdvd
#print axioms witnessY_coarse2
#print axioms singleBondA0_dir0
#print axioms singleBondA0_dir1
#print axioms RMap_trivial
#print axioms trivialU_apply
#print axioms adjoint_trivialU
#print axioms grad_trivialU
#print axioms div_gradLamDelta_ne_zero
#print axioms loopV_dir0
#print axioms loopV_dir1
#print axioms loopV_dir2
#print axioms planeProfile_shift0
#print axioms planeProfile_shiftBack0
#print axioms loopV_mem_V

end AdalyFormal.Balaban.SchurNonzero

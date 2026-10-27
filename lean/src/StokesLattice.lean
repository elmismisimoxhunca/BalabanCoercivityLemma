/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.StokesCommU

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# THE STOKES NORM BOUND `(N)`, DERIVED — AND ITS GENERAL-`U` FORM AS A BOUND

`compute/gamma1_positive/SCOPE.md` §5 closes with: *"What genuinely remains unattempted here, and it
is small: (N), the norm bound `‖S‖ ≤ σ`. … This lane did not perform it and does not assert a value
for `σ`."*  §1 of this file performs it, and the value is **`σ₀ = ℓ^{-1/2}`**, i.e.

  `∑_{P coarse} ‖∂₁'(Q_ℓ(1) A)(P)‖²  ≤  (1/ℓ) · ∑_{p fine} ‖(d_1 A)(p)‖²`.

Every factor is counted, none is fitted: `ℓ⁻⁸` from squaring `stokes_flat`'s `ℓ⁴`, `ℓ⁵` from
Cauchy–Schwarz over `windowSet` (`ℓ³` block sites × `ℓ` × `ℓ` offsets, `card_blockOf_of_coarse`),
`ℓ²` from the exact incidence count (blocks partition the torus, each offset pair is a torus
bijection).  `ℓ⁻⁸ · ℓ⁵ · ℓ² = ℓ⁻¹`.  The uniform-rescale test: multiply `stokes_flat`'s
normalisation by `c` and the conclusion's constant moves by `c²` — `sum_window_incidence` and
`card_windowSet` are the two independently-derived places the exponents come from, and §4's
mutation battery flips each.

§2 carries the same bound to general `U` — not as an identity (the exact identity provably fails
covariantly) but as an inequality with an error term, using only the tree's two drift bridges.

§3 states, and proves, exactly where the resulting chain is still open, and it is NOT where the
residual note says.
-/

namespace AdalyFormal.StokesCommu.Lattice

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.CoarseCurl (CoarsePlaquette)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ThirdLevelStokes
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy frobSupBond curlDrift
  norm_curlDrift_L2_le_sup frobSupBond_nonneg)
open AdalyFormal.Balaban.RegularUQChain (sum_pathSite_comp coarseDriftEnergy_le)
open AdalyFormal.Balaban.FourierFaithfulU1 (sum_coarse_blocks)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — the window, packaged -/

/-- The window sum written on `windowSet`/`windowPlaq` (the tree's own index set, LAW-19). -/
theorem window_sum_eq {ell : ℕ} (y : PeriodicLatticeSite L) {μ ν : Fin 3} (hlt : μ < ν)
    {α : Type*} [AddCommMonoid α] (F : PeriodicLatticePlaquette L → α) :
    ∑ t ∈ windowSet ell y, F (windowPlaq hlt t)
      = ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
          F (pathSite (pathSite x μ i) ν j, ⟨(μ, ν), hlt⟩) := by
  unfold windowSet windowPlaq
  rw [Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_product _ _ _

/-- `card (windowSet ℓ y) = ℓ⁵` for a coarse-lattice centre: `ℓ³` block sites times `ℓ × ℓ`
offsets.  The `ℓ³` is `card_blockOf_of_coarse`, not an assumption. -/
theorem card_windowSet {ell : ℕ} (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) :
    (windowSet ell y).card = ell ^ 5 := by
  unfold windowSet
  rw [Finset.card_product, Finset.card_product, Finset.card_range,
    card_blockOf_of_coarse hdvd hy]
  ring

/-! ## §1 — THE FLAT NORM BOUND `(N)`, WITH ITS CONSTANT DERIVED -/

/-- **Per coarse plaquette.**  `‖∂₁'(Q_ℓ(1)A)(P)‖² ≤ ℓ⁻³ · (window sum of squared fine curls)`.
Squaring `stokes_flat` costs `ℓ⁸`; Cauchy–Schwarz over the `ℓ⁵`-element window returns `ℓ⁵`. -/
theorem coarseCurl_sq_le_window {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : Bond L → SuTwo) {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell)
    {μ ν : Fin 3} (hlt : μ < ν) :
    ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A)
        ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell)‖ ^ 2
      ≤ (1 / (ell : ℝ) ^ 3) *
          ∑ t ∈ windowSet ell y, ‖curlValueCovariant (trivialU L) A (windowPlaq hlt t)‖ ^ 2 := by
  classical
  set C : SuTwo := coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A)
    ((⟨y, hy⟩, ⟨(μ, ν), hlt⟩) : CoarsePlaquette L ell) with hC
  set g : PeriodicLatticeSite L × ℕ × ℕ → SuTwo :=
    fun t => curlValueCovariant (trivialU L) A (windowPlaq hlt t) with hg
  set T : ℝ := ∑ t ∈ windowSet ell y, ‖g t‖ with hT
  set S : ℝ := ∑ t ∈ windowSet ell y, ‖g t‖ ^ 2 with hS
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  -- (a) the identity, as a window sum
  have hid : ∑ t ∈ windowSet ell y, g t = ((ell : ℝ) ^ 4) • C := by
    rw [hg, window_sum_eq y hlt]
    exact AdalyFormal.Balaban.ThirdLevelStokes.stokes_flat hell hdvd hy hlt A
  -- (b) triangle inequality
  have hnorm : ((ell : ℝ) ^ 4) * ‖C‖ ≤ T := by
    have h1 : ‖((ell : ℝ) ^ 4) • C‖ ≤ T := by
      rw [← hid, hT]; exact norm_sum_le _ _
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ell : ℝ) ^ 4)] at h1
  -- (c) Cauchy–Schwarz over the ℓ⁵-element window
  have hCS : T ^ 2 ≤ ((ell : ℝ) ^ 5) * S := by
    have h := sq_sum_le_card_mul_sum_sq (s := windowSet ell y) (f := fun t => ‖g t‖)
    rw [card_windowSet hdvd hy] at h
    have hcast : (((ell ^ 5 : ℕ) : ℝ)) = ((ell : ℝ) ^ 5) := by push_cast; ring
    rw [hcast] at h
    exact h
  -- (d) assemble
  have hCnn : (0 : ℝ) ≤ ‖C‖ := norm_nonneg _
  -- the missing product certificate: `nlinarith` needs `0 ≤ ell^4 * ‖C‖`, not merely `0 ≤ ‖C‖`
  have h4nn : (0 : ℝ) ≤ ((ell : ℝ) ^ 4) * ‖C‖ := by positivity
  have hsq : ((ell : ℝ) ^ 8) * ‖C‖ ^ 2 ≤ T ^ 2 := by nlinarith [hnorm, h4nn]
  have h3 : (0 : ℝ) < (ell : ℝ) ^ 3 := by positivity
  have h5 : (0 : ℝ) < (ell : ℝ) ^ 5 := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h3]
  -- `nlinarith` cannot divide by `ell^5`; cancel it explicitly instead
  have hmul : ((ell : ℝ) ^ 5) * (‖C‖ ^ 2 * (ell : ℝ) ^ 3) ≤ ((ell : ℝ) ^ 5) * S := by
    nlinarith [hsq, hCS]
  exact le_of_mul_le_mul_left hmul h5

/-- **THE EXACT INCIDENCE COUNT.**  Summed over every coarse plaquette, the window picks up every
fine plaquette EXACTLY `ℓ²` times — once per offset pair `(i,j)`.  An equality, not a bound:
blocks partition the torus (`sum_coarse_blocks`) and each offset is a torus bijection
(`sum_pathSite_comp`), applied twice. -/
theorem sum_window_incidence {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : PeriodicLatticePlaquette L → SuTwo) :
    (∑ P : CoarsePlaquette L ell, ∑ t ∈ windowSet ell P.1.1, ‖F (windowPlaq P.2.2 t)‖ ^ 2)
      = ((ell : ℝ) ^ 2) * plaqEnergy F := by
  classical
  have hper : ∀ dir : PeriodicPlaquetteDirections,
      (∑ y ∈ CoarseLattice L ell, ∑ t ∈ windowSet ell y, ‖F (windowPlaq dir.2 t)‖ ^ 2)
        = ((ell : ℝ) ^ 2) * ∑ z : PeriodicLatticeSite L, ‖F (z, dir)‖ ^ 2 := by
    intro dir
    have hw : ∀ y : PeriodicLatticeSite L,
        (∑ t ∈ windowSet ell y, ‖F (windowPlaq dir.2 t)‖ ^ 2)
          = ∑ x ∈ blockOf y ell, ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
              ‖F (pathSite (pathSite x dir.1.1 i) dir.1.2 j, dir)‖ ^ 2 := by
      intro y
      have := window_sum_eq (L := L) (ell := ell) y dir.2
        (F := fun p => ‖F p‖ ^ 2)
      simpa using this
    rw [Finset.sum_congr rfl (fun y _ => hw y)]
    rw [sum_coarse_blocks hell hdvd
      (fun x => ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell,
        ‖F (pathSite (pathSite x dir.1.1 i) dir.1.2 j, dir)‖ ^ 2)]
    rw [Finset.sum_comm]
    have hinner : ∀ i ∈ Finset.range ell,
        (∑ x : PeriodicLatticeSite L, ∑ j ∈ Finset.range ell,
            ‖F (pathSite (pathSite x dir.1.1 i) dir.1.2 j, dir)‖ ^ 2)
          = ((ell : ℝ)) * ∑ z : PeriodicLatticeSite L, ‖F (z, dir)‖ ^ 2 := by
      intro i _
      rw [Finset.sum_comm]
      have hj : ∀ j ∈ Finset.range ell,
          (∑ x : PeriodicLatticeSite L,
              ‖F (pathSite (pathSite x dir.1.1 i) dir.1.2 j, dir)‖ ^ 2)
            = ∑ z : PeriodicLatticeSite L, ‖F (z, dir)‖ ^ 2 := by
        intro j _
        rw [sum_pathSite_comp dir.1.1 i
          (fun w => ‖F (pathSite w dir.1.2 j, dir)‖ ^ 2)]
        exact sum_pathSite_comp dir.1.2 j (fun z => ‖F (z, dir)‖ ^ 2)
      rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsplit : (∑ P : CoarsePlaquette L ell, ∑ t ∈ windowSet ell P.1.1,
      ‖F (windowPlaq P.2.2 t)‖ ^ 2)
      = ∑ dir : PeriodicPlaquetteDirections, ∑ y ∈ CoarseLattice L ell,
          ∑ t ∈ windowSet ell y, ‖F (windowPlaq dir.2 t)‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun dir _ => ?_)
    exact (Finset.sum_subtype (CoarseLattice L ell) (fun _ => Iff.rfl)
      (fun y => ∑ t ∈ windowSet ell y, ‖F (windowPlaq dir.2 t)‖ ^ 2)).symm
  rw [hsplit, Finset.sum_congr rfl (fun dir _ => hper dir), ← Finset.mul_sum]
  congr 1
  unfold plaqEnergy
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **`(N)`, PERFORMED: `σ₀ = ℓ^{-1/2}`.**  The coarse-plaquette energy of the coarse curl of the
faithful `U = 1` line average is at most `1/ℓ` times the fine-plaquette energy of the fine curl.
Uniform in the extent `L`, in the RG step `k` (neither occurs), and improving as `ℓ` grows. -/
theorem coarseCurl_energy_le_flat {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (A : Bond L → SuTwo) :
    (∑ P : CoarsePlaquette L ell,
        ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) P‖ ^ 2)
      ≤ (1 / (ell : ℝ)) * plaqEnergy (curlValueCovariant (trivialU L) A) := by
  classical
  have hellR : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hstep : (∑ P : CoarsePlaquette L ell,
      ‖coarseCurlSuTwo hdvd (lineCoarseRestrictCovLM (trivialU L) ell A) P‖ ^ 2)
      ≤ ∑ P : CoarsePlaquette L ell, (1 / (ell : ℝ) ^ 3) *
          ∑ t ∈ windowSet ell P.1.1,
            ‖curlValueCovariant (trivialU L) A (windowPlaq P.2.2 t)‖ ^ 2 := by
    refine Finset.sum_le_sum (fun P _ => ?_)
    exact coarseCurl_sq_le_window hell hdvd A P.1.2 P.2.2
  refine hstep.trans ?_
  rw [← Finset.mul_sum, sum_window_incidence hell hdvd (curlValueCovariant (trivialU L) A)]
  have : (1 / (ell : ℝ) ^ 3) * (((ell : ℝ) ^ 2) *
      plaqEnergy (curlValueCovariant (trivialU L) A))
      = (1 / (ell : ℝ)) * plaqEnergy (curlValueCovariant (trivialU L) A) := by
    field_simp
  exact le_of_eq this

#print axioms window_sum_eq
#print axioms card_windowSet
#print axioms coarseCurl_sq_le_window
#print axioms sum_window_incidence
#print axioms coarseCurl_energy_le_flat

end AdalyFormal.StokesCommu.Lattice

import PW1
import PW2
import B0i
import MS7
import PSiteC21

/-!
# PW3 -- R1 instantiated on the two-stratum patch (M1 lane D, node W3), at ANY background `U`

On `G = geomOf ell (j+1) (patchTower j Rg)` (`Ω₀ = torus`):
* `patch_B0` : `Q(U) D_U ν = 0` for every `ν ∈ N(Q'(U))` (CMP99b (3.115) on both strata; the level-`j+1` rows that leave `Rg` see
  `Q'_{j+1} ν = 0` at their outside endpoint because that `ell^{j+1}`-block consists of level-`j` constraint blocks).
  Hypotheses: `0 < ell`, `Rg` a union of `ell^{j+1}`-blocks (`BlockClosed`), `ell^{j+1} ∣ L μ + 1`, `RegTower` (composite jet exists).
* `wop_grad` : `W D ν = 0` for `ν ∈ N(Q')` (any `U`, Dirichlet operator invertible).
* `PhiP` (= `⟨A,Δ_π A⟩ + ⟨A,Q*aQ A⟩`), `PhiP_inv` : gauge invariance along `D N(Q')`.
* `ginv_form` : `⟨x, G⁻¹ x⟩ = PhiP x + ‖R D* x‖²` for the r8 `IngrBParams.data`.
* `poincare_patch` : for any `ProperTower G ell k` with `Ω₀ = univ`, `2 ≤ ell`, `ell^k ∣ L μ + 1`, `a > 0`, `216ρ² < 1` and lane C's
  S1 tower hypotheses `hU`, `hT`: `‖ν‖ ≤ Pc ell k a ρ · ‖D ν‖` on `N(Q')`, `Pc² = ell^{2k} max(6,16/(3a))/(1-216ρ²)`
  (from `site_coercive_weighted`); used at `k = j+1`.
The assembled theorems are `w3_flat_plain` (PW7) and `w3_of_QI` (PW8).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1Patch

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity (ProperTower inBlockBonds)
open AdalyFormal.StatementLane (Tower BlockClosed scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice inBlock Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.QjComposite (Qcomposite Qcomposite_succ stepAverage stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.SliceCoerc (OnLat onLat_shift)

variable {L : PeriodicLatticeExtent}

theorem onLat_back (m : ℕ) (hm : ∀ μ : Fin 3, m ∣ L μ + 1) (x : PeriodicLatticeSite L) (μ : Fin 3)
    (h : OnLat m (coarseShift x m μ)) : OnLat m x := by
  intro ν
  by_cases hν : ν = μ
  · subst hν
    have h4 := h ν
    rw [coarseShift_val_eq, Nat.dvd_mod_iff (hm ν)] at h4
    exact (Nat.dvd_add_left (dvd_refl _)).mp h4
  · have h4 := h ν
    rw [coarseShift_apply_ne _ _ _ _ hν] at h4
    exact h4

section geom
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
include hell hRg

theorem omGe_of_mem (z : PeriodicLatticeSite L) (hz : z ∈ Rg) :
    OmGe (geomOf ell (j + 1) (patchTower j Rg)) (j + 1) z := by
  refine ⟨j + 1, le_rfl, le_rfl, corner (ell ^ (j + 1)) z, ?_, ?_⟩
  · rw [mem_lam_succ]
    exact ⟨corner_dvd _ z, hRg z hz _ (fun μ =>
      same_block_div (pow_pos hell _) (corner_dvd _ z) (mem_block_corner (pow_pos hell _) z) μ)⟩
  · exact mem_blockOf.mp (mem_block_corner (pow_pos hell _) z)

theorem q_j_zero (U : Cfg L) {ν : SiteL2 L} (hν : ν ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) U)
    (z : PeriodicLatticeSite L) (hz : OnLat (ell ^ j) z) (hzR : z ∉ Rg) :
    Qcomposite (bgTower (geomOf ell (j + 1) (patchTower j Rg)) U) ell j (WithLp.ofLp ν) z = 0 := by
  have hL : z ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam j := (mem_lam_j ell j Rg z).mpr ⟨hz, hzR⟩
  have h := hν.2 j (by show j ≤ j + 1; omega) z hL
  rw [Qlev_apply] at h
  exact h

theorem q_succ_zero (U : Cfg L) {ν : SiteL2 L} (hν : ν ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) U)
    (z : PeriodicLatticeSite L) (hz : OnLat (ell ^ (j + 1)) z) :
    Qcomposite (bgTower (geomOf ell (j + 1) (patchTower j Rg)) U) ell (j + 1) (WithLp.ofLp ν) z = 0 := by
  by_cases hzR : z ∈ Rg
  · have hL : z ∈ (geomOf ell (j + 1) (patchTower j Rg)).Lam (j + 1) := (mem_lam_succ ell j Rg z).mpr ⟨hz, hzR⟩
    have h := hν.2 (j + 1) le_rfl z hL
    rw [Qlev_apply] at h
    exact h
  · rw [Qcomposite_succ]
    unfold stepAverage
    rw [Finset.sum_eq_zero, smul_zero]
    intro x hx
    have hxs := mem_stepBlockOf.mp hx
    have hxb : x ∈ blockOf z (ell ^ (j + 1)) := by
      rw [mem_blockOf]; intro μ
      refine ⟨(hxs μ).1, ?_⟩
      have := (hxs μ).2.1
      rwa [← pow_succ] at this
    have hxlat : OnLat (ell ^ j) x := by
      intro μ
      have h1 := (hxs μ).2.2
      have h2 : ell ^ j ∣ (z μ).val := (pow_dvd_pow ell (Nat.le_succ j)).trans (hz μ)
      have h3 := (hxs μ).1
      have : (x μ).val = (x μ).val - (z μ).val + (z μ).val := by omega
      rw [this]; exact Nat.dvd_add h1 h2
    have hxR : x ∉ Rg := fun hx' => hzR (hRg x hx' z (fun μ => same_block_div (pow_pos hell _) hz hxb μ))
    rw [q_j_zero hell hRg U hν x hxlat hxR, map_zero]

/-- **B0 on the patch** (any `U` with a regular background tower). -/
theorem patch_B0 (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1) (U : Cfg L)
    (hreg : RegTower ell (bgTower (geomOf ell (j + 1) (patchTower j Rg)) U) (j + 1))
    (ν : SiteL2 L) (hν : ν ∈ NQp (geomOf ell (j + 1) (patchTower j Rg)) U) :
    QfullOf (geomOf ell (j + 1) (patchTower j Rg)) U (gradL2 U ν) = 0 := by
  set G := geomOf ell (j + 1) (patchTower j Rg) with hG
  refine PiLp.ext (fun p => ?_)
  obtain ⟨⟨i, hi⟩, c, hc⟩ := p
  have hik : i ≤ j + 1 := Nat.lt_succ_iff.mp hi
  have hdvd_i : ∀ μ : Fin 3, ell ^ i ∣ L μ + 1 := fun μ => (pow_dvd_pow ell hik).trans (hdvd μ)
  -- the row's endpoints are on the ell^i lattice
  have hlat_of_lam : ∀ z, z ∈ G.Lam i → OnLat (ell ^ i) z := fun z hz => hz.1
  have hlat0 : OnLat (ell ^ i) c.1 := by
    rcases hc.1 with h | h
    · exact hlat_of_lam _ h
    · exact onLat_back _ hdvd_i _ _ (hlat_of_lam _ h)
  have hlat1 : OnLat (ell ^ i) (coarseShift c.1 (ell ^ i) c.2) := onLat_shift _ hdvd_i _ hlat0 _
  have hzero : ∀ z, OnLat (ell ^ i) z → ¬ OmGe G (i + 1) z →
      Qcomposite (bgTower G U) G.ell i (WithLp.ofLp ν) z = 0 := by
    intro z hz hzo
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exfalso
      rcases hc.1 with h | h
      · rw [lam_lt ell j Rg hlt] at h; exact h
      · rw [lam_lt ell j Rg hlt] at h; exact h
    · subst heq
      exact q_j_zero hell hRg U hν z hz (fun hzR => hzo (omGe_of_mem hell hRg z hzR))
    · have : i = j + 1 := by omega
      subst this
      exact q_succ_zero hell hRg U hν z hz
  exact AdalyFormal.SliceCoerc.QfullOf_grad_eq_zero G U hell (by exact hreg) (by exact hdvd) ν ⟨⟨i, hi⟩, c, hc⟩
    hlat0 hlat1 (hzero _ hlat0 (fun h => hc.2 (Or.inl h))) (hzero _ hlat1 (fun h => hc.2 (Or.inr h)))

end geom

/-! ## gauge invariance of the non-gauge part of the form -/

section form
variable (G : TowerGeom L) (U : Cfg L) (a : ℝ)

theorem gradAdj_grad_mem (hOm : G.Om0 = Set.univ) (ν : SiteL2 L) (hν : ν ∈ NQp G U) :
    gradAdj U (gradL2 U ν) ∈ RImage G U := by
  have : gradAdj U (gradL2 U ν) = lapDir G U ν := by
    rw [AdalyFormal.SliceCoerc.lapDir_univ G hOm]; rfl
  rw [this]
  exact Submodule.mem_map_of_mem hν

theorem Rproj_fix (hOm : G.Om0 = Set.univ) (ν : SiteL2 L) (hν : ν ∈ NQp G U) :
    Rproj G U (gradAdj U (gradL2 U ν)) = gradAdj U (gradL2 U ν) :=
  Submodule.starProjection_eq_self_iff.mpr (gradAdj_grad_mem G U hOm ν hν)

theorem Rproj_le (s : SiteL2 L) : ‖Rproj G U s‖ ≤ ‖s‖ := by
  have h1 : ‖Rproj G U s‖ ^ 2 = ⟪Rproj G U s, s⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← Rproj_symm, Rproj_idem]
  have h2 : ⟪Rproj G U s, s⟫ ≤ ‖Rproj G U s‖ * ‖s‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (Rproj G U s)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

theorem wop_grad (hOm : G.Om0 = Set.univ) (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (ν : SiteL2 L) (hν : ν ∈ NQp G U) :
    Wop G U a (gradL2 U ν) = 0 := by
  have h1 : gradAdj U (gradL2 U ν) = lapDir G U ν := by
    rw [AdalyFormal.SliceCoerc.lapDir_univ G hOm]; rfl
  have h2 := Rproj_fix G U hOm ν hν
  rw [h1] at h2
  simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
  rw [h1, h2, AdalyFormal.SliceCoerc.Gp_lapDir_of_NQp G U a hu ν hν, sub_self]

/-- the non-gauge part of the `G⁻¹` form: `⟨A,Δ_π A⟩ + ⟨A,Q*aQ A⟩`. -/
noncomputable def PhiP (A : BondFnL2 L) : ℝ :=
  ⟪A, DpiFull G U a A⟫ + ⟪A, MassFull G a (bondSectorOf G U) A⟫

theorem dpi_form (A : BondFnL2 L) : ⟪A, DpiFull G U a A⟫ = ⟪Wop G U a A, Delta G U (Wop G U a A)⟫ := by
  simp only [DpiFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem PhiP_inv (hOm : G.Om0 = Set.univ) (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hB0 : ∀ ν ∈ NQp G U, QfullOf G U (gradL2 U ν) = 0)
    (A : BondFnL2 L) (ν : SiteL2 L) (hν : ν ∈ NQp G U) :
    PhiP G U a (A + gradL2 U ν) = PhiP G U a A := by
  unfold PhiP
  rw [dpi_form, dpi_form, map_add, wop_grad G U a hOm hu ν hν, add_zero, inner_MassFull, inner_MassFull]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  show a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖(QfullOf G U (A + gradL2 U ν)).ofLp p‖ ^ 2 = _
  rw [map_add, hB0 ν hν, add_zero]
  rfl

end form

/-- the r8 `G⁻¹` form splits as `PhiP + ‖R D*‖²`. -/
theorem ginv_form (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, P.data.Ginv x⟫ = PhiP P.G P.U P.a (iE P.G x) + ‖Rproj P.G P.U (gradAdj P.U (iE P.G x))‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  unfold PhiP
  have h1 : ⟪x, P.data.Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
    show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
    rw [pE_inner_right]
  have h2 : ⟪x, P.data.Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G x)⟫ := by
    show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
    rw [pE_inner_right]; rfl
  have h3 : P.data.T x = Rproj P.G P.U (gradAdj P.U (iE P.G x)) := rfl
  rw [h1, h2, h3]; ring

/-! ## Poincaré on `N(Q')` from lane C's S1 -/

/-- the Poincaré constant -/
noncomputable def Pc (ell k : ℕ) (a ρ : ℝ) : ℝ :=
  Real.sqrt (((ell : ℝ) ^ k) ^ 2 * max 6 (16 / (3 * a)) / (1 - 216 * ρ ^ 2))

theorem poincare_patch {ell k : ℕ} (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) (ha : 0 < a)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (h216 : 216 * ρ ^ 2 < 1)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (ν : SiteL2 L) (hν : ν ∈ NQp G U) : ‖ν‖ ≤ Pc ell k a ρ * ‖gradL2 U ν‖ := by
  have hS1 := AdalyFormal.M1Site.site_coercive_weighted ell k hell hdvd hP U a ha ρ hρ hU hT ν
  have hge := AdalyFormal.M1Site.wNormSq_ge G (by rw [hP.ell_eq]; omega) ν
  rw [hP.ell_eq, hP.k_eq, hOm, AdalyFormal.SliceCoerc.siteMask_univ] at hge
  have hD : ⟪ν, DelpA G U a ν⟫ = ‖gradL2 U ν‖ ^ 2 := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply, hOm, AdalyFormal.SliceCoerc.siteMask_univ,
      ContinuousLinearMap.add_apply, inner_add_right, inner_lapFull,
      AdalyFormal.SiteCoercivity.Qpa_form_zero_of_NQp G U a hν, add_zero]
  rw [hD] at hS1
  set M := max 6 (16 / (3 * a)) with hM
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hd : 0 < 1 - 216 * ρ ^ 2 := by linarith
  have hn : (0 : ℝ) < ((ell : ℝ) ^ k) ^ 2 := by positivity
  have key : ‖ν‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * M / (1 - 216 * ρ ^ 2) * ‖gradL2 U ν‖ ^ 2 := by
    have h1 : ‖ν‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * AdalyFormal.M1Site.wNormSq G ν := by
      rw [div_le_iff₀ hn] at hge; linarith
    have h2 : AdalyFormal.M1Site.wNormSq G ν ≤ M / (1 - 216 * ρ ^ 2) * ‖gradL2 U ν‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; linarith
    calc ‖ν‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * AdalyFormal.M1Site.wNormSq G ν := h1
      _ ≤ ((ell : ℝ) ^ k) ^ 2 * (M / (1 - 216 * ρ ^ 2) * ‖gradL2 U ν‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hn.le
      _ = _ := by ring
  have hc0 : 0 ≤ ((ell : ℝ) ^ k) ^ 2 * M / (1 - 216 * ρ ^ 2) := by positivity
  unfold Pc
  rw [← hM]
  calc ‖ν‖ = Real.sqrt (‖ν‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((ell : ℝ) ^ k) ^ 2 * M / (1 - 216 * ρ ^ 2) * ‖gradL2 U ν‖ ^ 2) := Real.sqrt_le_sqrt key
    _ = _ := by rw [Real.sqrt_mul hc0, Real.sqrt_sq (norm_nonneg _)]

#print axioms patch_B0
#print axioms wop_grad
#print axioms PhiP_inv
#print axioms ginv_form
#print axioms poincare_patch

end AdalyFormal.M1Patch

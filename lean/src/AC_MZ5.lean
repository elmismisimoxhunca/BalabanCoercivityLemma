import MZ5
import AC_MZ3
import AC_MZ4
import AC_Base

/-! AC copy of MZ5: affected declarations only (lane allc_20261016); 12 literal kept (control build). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2DLayer

open AdalyFormal.AllC
variable {fc : ℕ} [CubeFactor fc]

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (strat bstrat DLayerStrat wnormSq)
open AdalyFormal.M1DStrat (omJ phiC DParts dlayerStrat_of_parts)

open Classical in
/-- **lane B's stratified D-layer premises at a printed-class configuration, modulo `OpLayer`** -/
theorem dlayerStrat_classAC {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell) (hell2 : 2 ≤ ell)
    {S : Tower (scaleUp ell k Lu)} {α₀ : ℝ} {U : LinkCfg (scaleUp ell k Lu)} (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hRM : 4 ≤ R * M)
    (hU : ClassCoupledH ell M fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hα : 0 ≤ α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    {θ : ℝ} (hθ : 0 < θ) (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    {KH KH1 K2 CW KD : ℝ} (hKH : 0 ≤ KH) (hKH1 : 0 ≤ KH1) (hK2 : 0 ≤ K2)
    (hop : OpLayer ell M R k Lu hell S U a Lam θ KH KH1 K2 CW KD)
    (ε2s εJ : ℝ)
    (h2 : 2 * ((Real.sqrt (Ageo ell θ) * KH) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * K2 * CW ≤ ε2s)
    (hJ : ((Real.sqrt (Ageo ell θ) * KH1) * (400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀))) * KD ≤ εJ) :
    DLayerStrat ell k Lu hell S U a Lam ε2s εJ := by
  set SJ : ℝ := 400 * (ell : ℝ) ^ 3 * ((12 : ℝ) * M * α₀) with hSJ
  have hell1 : 1 ≤ ell := hell
  have hβ0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hSJ0 : 0 ≤ SJ := by positivity
  have hcov : CoversOm0p ell M fc k S := hU.1
  have hRM3 : 3 ≤ R * M := by omega
  refine dlayerStrat_of_parts ell k Lu hell S U a Lam ε2s εJ (omSAC fc ell M k S) SJ
    (Real.sqrt (Ageo ell θ) * KH) K2 CW (Real.sqrt (Ageo ell θ) * KH1) KD ?_ h2 hJ
  refine ⟨hSJ0, by positivity, hK2, by positivity, ?_, ?_, hop.hC2, hop.hW, ?_, hop.hKD⟩
  · -- the source, split
    intro b
    have h := Jf_splitAC hell hS hRM hU hα hsm a Lam b
    have hsu := su_le_sj ell hell1 _ hβ0 hsm
    have hJ0 : 0 ≤ omJ S ell k b := by unfold omJ; positivity
    refine h.trans ?_
    unfold omSAC
    split_ifs with hu
    · have hU0 : 0 ≤ omU S ell k b := by unfold omU; positivity
      have := mul_le_mul_of_nonneg_right hsu hU0
      nlinarith
    · linarith
  · intro p v
    obtain ⟨c, hc⟩ := hop.hHL2 p v
    exact col_classAC hS hR hM hell2 hRM3 hcov hθ hq c _ (fun b => norm_nonneg _) KH ‖v‖ hKH (norm_nonneg _) hc
  · intro e v
    obtain ⟨c, hc⟩ := hop.hH1L2 e v
    exact col_classAC hS hR hM hell2 hRM3 hcov hθ hq c _ (fun b => norm_nonneg _) KH1 ‖v‖ hKH1 (norm_nonneg _) hc

/-- **the D-layer obligation on the printed class**, with the operator layer as a per-configuration premise with FIXED
constants (shape parallel to m1_dstrat DX6 `DLayerObligationW4`, with `M1Regular` replaced by the printed class). -/
def DLayerObligationClassAC (fc ell M R : ℕ) (hell : 0 < ell) (a θ KH KH1 K2 CW KD : ℝ) : Prop :=
  ∀ ε2s : ℝ, 0 < ε2s → ∀ εJ : ℝ, 0 < εJ → ∃ a₁ : ℝ, 0 < a₁ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M fc k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell M fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    OpLayer ell M R k Lu hell S U a Lam θ KH KH1 K2 CW KD →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ

theorem dlayerObligationClass_holdsAC {ell M R : ℕ} (hell : 0 < ell) (hell2 : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hRM : 4 ≤ R * M) (a : ℝ) {θ : ℝ} (hθ : 0 < θ) (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    {KH KH1 K2 CW KD : ℝ} (hKH : 0 ≤ KH) (hKH1 : 0 ≤ KH1) (hK2 : 0 ≤ K2) (hCW : 0 ≤ CW) (hKD : 0 ≤ KD) :
    DLayerObligationClassAC fc ell M R hell a θ KH KH1 K2 CW KD := by
  intro ε2s hε2s εJ hεJ
  set A := Real.sqrt (Ageo ell θ) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set C1 : ℝ := 2 * (A * KH) * (400 * (ell : ℝ) ^ 3) * K2 * CW with hC1
  set C2 : ℝ := (A * KH1) * (400 * (ell : ℝ) ^ 3) * KD with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨min (1 / 4) (min (ε2s / (C1 + 1)) (εJ / (C2 + 1))),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro k hk Lu α₀ hα ht hT S hS hcov Lam hL U hU hop
  set β : ℝ := (12 : ℝ) * M * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hb4 : β ≤ 1 / 4 := ht.trans (min_le_left _ _)
  have hb1 : β ≤ ε2s / (C1 + 1) := ht.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb2 : β ≤ εJ / (C2 + 1) := ht.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc1 : C1 * β ≤ ε2s := by
    have h := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ C1 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C1 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  have hc2 : C2 * β ≤ εJ := by
    have h := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ C2 + 1 by linarith)
    rw [mul_div_cancel₀ _ (by positivity : (C2 + 1 : ℝ) ≠ 0)] at h
    nlinarith
  refine dlayerStrat_classAC hell hell2 a Lam hS hR hM hRM hU hα.le (by linarith) hθ hq hKH hKH1 hK2 hop ε2s εJ ?_ ?_
  · calc 2 * ((A * KH) * (400 * (ell : ℝ) ^ 3 * β)) * K2 * CW = C1 * β := by rw [hC1]; ring
      _ ≤ ε2s := hc1
  · calc ((A * KH1) * (400 * (ell : ℝ) ^ 3 * β)) * KD = C2 * β := by rw [hC2]; ring
      _ ≤ εJ := hc2

end AdalyFormal.M2DLayer


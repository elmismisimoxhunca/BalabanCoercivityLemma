import MZ5
import AC_MZ3
import AC_MZ4
import AC_MZ5
import AC_Base

/-! AU_XMZ5: `DLayerObligationClassX` / `dlayerObligationClass_holdsX`: as `AC_MZ5.dlayerObligationClassAC` with `a1` chosen BEFORE the cube factor `fc >= 10`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2DLayer

open AdalyFormal.AllC

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.M1 (strat bstrat DLayerStrat wnormSq)
open AdalyFormal.M1DStrat (omJ phiC DParts dlayerStrat_of_parts)

/-- **the D-layer obligation on the printed class**, with the operator layer as a per-configuration premise with FIXED
constants (shape parallel to m1_dstrat DX6 `DLayerObligationW4`, with `M1Regular` replaced by the printed class). -/
def DLayerObligationClassX (ell M R : ℕ) (hell : 0 < ell) (a θ KH KH1 K2 CW KD : ℝ) : Prop :=
  ∀ ε2s : ℝ, 0 < ε2s → ∀ εJ : ℝ, 0 < εJ → ∃ a₁ : ℝ, 0 < a₁ ∧ ∀ fc : ℕ, 10 ≤ fc →
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₁ →
    TorusOK ell M Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S → CoversOm0p ell M fc k S →
    ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupledH ell M fc 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    OpLayer ell M R k Lu hell S U a Lam θ KH KH1 K2 CW KD →
      DLayerStrat ell k Lu hell S U a Lam ε2s εJ

theorem dlayerObligationClass_holdsX {ell M R : ℕ} (hell : 0 < ell) (hell2 : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M)
    (hRM : 4 ≤ R * M) (a : ℝ) {θ : ℝ} (hθ : 0 < θ) (hq : (ell : ℝ) ^ 3 * Real.exp (-(θ * (R * M))) ≤ 1 / 2)
    {KH KH1 K2 CW KD : ℝ} (hKH : 0 ≤ KH) (hKH1 : 0 ≤ KH1) (hK2 : 0 ≤ K2) (hCW : 0 ≤ CW) (hKD : 0 ≤ KD) :
    DLayerObligationClassX ell M R hell a θ KH KH1 K2 CW KD := by
  intro ε2s hε2s εJ hεJ
  set A := Real.sqrt (Ageo ell θ) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set C1 : ℝ := 2 * (A * KH) * (400 * (ell : ℝ) ^ 3) * K2 * CW with hC1
  set C2 : ℝ := (A * KH1) * (400 * (ell : ℝ) ^ 3) * KD with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨min (1 / 4) (min (ε2s / (C1 + 1)) (εJ / (C2 + 1))),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro fc hfc k hk Lu α₀ hα ht hT S hS hcov Lam hL U hU hop
  haveI : CubeFactor fc := ⟨hfc⟩
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

#print axioms AdalyFormal.M2DLayer.dlayerObligationClass_holdsX

import DLR79

/-!
# DL80 -- the abstract PERTURBATION of the `G⁻¹` Combes–Thomas data: `Dp ↦ Dp − M` (for `G₁⁻¹ = G⁻¹ − W*M_ψW`)

* `GinvHyp.pert` : the same structure with `Dp − M`, `ν + νM`, `δν + δM` (all other fields unchanged), for a symmetric `M`
  with `‖M‖ ≤ νM` and weighted commutators `≤ δM`;
* `pert_Ginv` : `(I.pert M).Ginv = I.Ginv − W* M W`;
* `pert_form_lower`, `pert_form_upper` : `⟨f,G₁⁻¹f⟩ ≥ ⟨f,G⁻¹f⟩ − νM nW²‖f‖²`, `⟨f,G₁⁻¹f⟩ ≤ ⟨f,G⁻¹f⟩ + νM nW²‖f‖²`
  (`nW = 1 + kDZ + dDZ`, DL15 `W_le`);
* `Mpsi_cjm` (concrete): the `cjm` commutator bound of `M_ψ` from `Mpsi_cjp` at `−φ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace

namespace GinvHyp

variable {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]

/-- `Dp ↦ Dp − M` -/
def pert (I : GinvHyp S E Y P B) (M : E →L[ℝ] E) (νM δM : ℝ) (hνM : 0 ≤ νM) (hδM : 0 ≤ δM)
    (hMn : ‖M‖ ≤ νM) (hMp : ‖cjp I.ωE I.ωE M - M‖ ≤ δM) (hMm : ‖cjm I.ωE I.ωE M - M‖ ≤ δM)
    (hMs : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) : GinvHyp S E Y P B where
  toGamHyp := I.toGamHyp
  C := I.C
  Dp := I.Dp - M
  Qb := I.Qb
  M := I.M
  ωP := I.ωP
  ωB := I.ωB
  δC := I.δC
  κ := I.κ
  δK := I.δK
  ν := I.ν + νM
  δν := I.δν + δM
  δB := I.δB
  hM := I.hM
  hδC := I.hδC
  hκ := I.hκ
  hδK := I.hδK
  hν := add_nonneg I.hν hνM
  hδν := add_nonneg I.hδν hδM
  hδB := I.hδB
  hCp := I.hCp
  hCm := I.hCm
  hKn := I.hKn
  hKp := I.hKp
  hKm := I.hKm
  hDpn := (norm_sub_le _ _).trans (add_le_add I.hDpn hMn)
  hDpp := by
    rw [cjp_sub]
    have e : cjp I.ωE I.ωE I.Dp - cjp I.ωE I.ωE M - (I.Dp - M)
        = (cjp I.ωE I.ωE I.Dp - I.Dp) - (cjp I.ωE I.ωE M - M) := by abel
    rw [e]; exact (norm_sub_le _ _).trans (add_le_add I.hDpp hMp)
  hDpm := by
    have hs : cjm I.ωE I.ωE (I.Dp - M) = cjm I.ωE I.ωE I.Dp - cjm I.ωE I.ωE M := by
      rw [cjm_eq_cjp_inv, cjm_eq_cjp_inv, cjm_eq_cjp_inv, cjp_sub]
    rw [hs]
    have e : cjm I.ωE I.ωE I.Dp - cjm I.ωE I.ωE M - (I.Dp - M)
        = (cjm I.ωE I.ωE I.Dp - I.Dp) - (cjm I.ωE I.ωE M - M) := by abel
    rw [e]; exact (norm_sub_le _ _).trans (add_le_add I.hDpm hMm)
  hDps := fun x y => by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, I.hDps, hMs]
  hBp := I.hBp
  hBm := I.hBm

variable (I : GinvHyp S E Y P B) (M : E →L[ℝ] E) (νM δM : ℝ) (hνM : 0 ≤ νM) (hδM : 0 ≤ δM)
    (hMn : ‖M‖ ≤ νM) (hMp : ‖cjp I.ωE I.ωE M - M‖ ≤ δM) (hMm : ‖cjm I.ωE I.ωE M - M‖ ≤ δM)
    (hMs : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)

theorem pert_Ginv :
    (I.pert M νM δM hνM hδM hMn hMp hMm hMs).Ginv
      = I.Ginv - ContinuousLinearMap.adjoint I.Gm.W ∘L M ∘L I.Gm.W := by
  ext1 x
  show (ContinuousLinearMap.adjoint I.Gm.W ∘L (ContinuousLinearMap.adjoint I.C ∘L I.C + (I.Dp - M)) ∘L I.Gm.W
    + ContinuousLinearMap.adjoint I.Gm.T ∘L I.Gm.T + I.M • (ContinuousLinearMap.adjoint I.Qb ∘L I.Qb)) x
    = (I.Ginv - ContinuousLinearMap.adjoint I.Gm.W ∘L M ∘L I.Gm.W) x
  simp only [GinvHyp.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, ContinuousLinearMap.smul_apply]
  abel

theorem pert_nW : (I.pert M νM δM hνM hδM hMn hMp hMm hMs).nW = I.nW := rfl

theorem pert_form (f : E) :
    ⟪f, (I.pert M νM δM hνM hδM hMn hMp hMm hMs).Ginv f⟫ = ⟪f, I.Ginv f⟫ - ⟪I.Gm.W f, M (I.Gm.W f)⟫ := by
  rw [pert_Ginv, ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem W_term_le (M : E →L[ℝ] E) (νM : ℝ) (hνM : 0 ≤ νM) (hMn : ‖M‖ ≤ νM) (f : E) :
    |⟪I.Gm.W f, M (I.Gm.W f)⟫| ≤ νM * I.nW ^ 2 * ‖f‖ ^ 2 := by
  have h1 : |⟪I.Gm.W f, M (I.Gm.W f)⟫| ≤ ‖I.Gm.W f‖ * ‖M (I.Gm.W f)‖ := abs_real_inner_le_norm _ _
  have h2 : ‖M (I.Gm.W f)‖ ≤ νM * ‖I.Gm.W f‖ := (M.le_opNorm _).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))
  have h3 : ‖I.Gm.W f‖ ≤ I.nW * ‖f‖ := I.Gm.W_le f
  have hW0 := norm_nonneg (I.Gm.W f)
  have h4 : ‖I.Gm.W f‖ ^ 2 ≤ (I.nW * ‖f‖) ^ 2 := pow_le_pow_left₀ hW0 h3 2
  calc |⟪I.Gm.W f, M (I.Gm.W f)⟫| ≤ ‖I.Gm.W f‖ * (νM * ‖I.Gm.W f‖) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hW0)
    _ = νM * ‖I.Gm.W f‖ ^ 2 := by ring
    _ ≤ νM * (I.nW * ‖f‖) ^ 2 := mul_le_mul_of_nonneg_left h4 hνM
    _ = νM * I.nW ^ 2 * ‖f‖ ^ 2 := by ring

theorem pert_form_lower (f : E) :
    ⟪f, I.Ginv f⟫ - νM * I.nW ^ 2 * ‖f‖ ^ 2 ≤ ⟪f, (I.pert M νM δM hνM hδM hMn hMp hMm hMs).Ginv f⟫ := by
  rw [pert_form]
  have := I.W_term_le M νM hνM hMn f
  linarith [le_abs_self ⟪I.Gm.W f, M (I.Gm.W f)⟫]

theorem pert_form_upper (f : E) :
    ⟪f, (I.pert M νM δM hνM hδM hMn hMp hMm hMs).Ginv f⟫ ≤ ⟪f, I.Ginv f⟫ + νM * I.nW ^ 2 * ‖f‖ ^ 2 := by
  rw [pert_form]
  have := I.W_term_le M νM hνM hMn f
  linarith [neg_abs_le ⟪I.Gm.W f, M (I.Gm.W f)⟫]

end GinvHyp

/-! ## `cjm` of `M_ψ` -/

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.IngredientFamilyR2 (RegTower bgTower Cfg C2fullOf BIdx FSp)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)

theorem cjm_bondWP_eq {L : PeriodicLatticeExtent} (φ : PeriodicLatticeSite L → ℝ) (T : BondFnL2 L →L[ℝ] BondFnL2 L) :
    cjm (bondWP φ) (bondWP φ) T = cjp (bondWP (-φ)) (bondWP (-φ)) T := by
  ext1 x
  show bondWt (-φ) (T (bondWt φ x)) = bondWt (-φ) (T (bondWt (-(-φ)) x))
  rw [neg_neg]

theorem wtLip_neg {L : PeriodicLatticeExtent} (θ' : ℝ) (φ : PeriodicLatticeSite L → ℝ) (h : WtLip θ' φ) :
    WtLip θ' (-φ) := by
  intro x μ
  have := h x μ
  simp only [Pi.neg_apply]
  rw [show -φ (periodicLatticeShift x μ) - -φ x = -(φ (periodicLatticeShift x μ) - φ x) by ring, abs_neg]
  exact this

theorem Mpsi_cjm (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (hell2 : 2 ≤ ell)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (ψ : FSp (GF ell k Lu)) (S K : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) :
    ‖cjm (bondWP φ) (bondWP φ) (Mpsi ell k Lu U ψ) - Mpsi ell k Lu U ψ‖
      ≤ 2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1)) := by
  rw [cjm_bondWP_eq]
  exact Mpsi_cjp ell k Lu U hell2 hreg ψ S K hS hK hψ hC (-φ) θ hθ (wtLip_neg _ φ hφ)

#print axioms GinvHyp.pert_Ginv
#print axioms GinvHyp.pert_form_lower
#print axioms GinvHyp.pert_form_upper
#print axioms Mpsi_cjm

end AdalyFormal.DLayer

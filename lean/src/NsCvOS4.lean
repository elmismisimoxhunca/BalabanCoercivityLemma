import NsCvOS3

/-!
# CvOS4 -- `Dcore ≠ 0` iff the four units, for the printed base-data algebra (lane omega/near2/struct)

Generic: for `(A, Q, Cb, J)`, with `G = A⁻¹`, `N0 = Q G Q*`, `H = G Q* N0⁻¹`, `Delta2 = 2 Lam(Cb, H* J)`, `G1inv = A - Delta2`,
`Nm = Q G1inv⁻¹ Q*` (all inverses `Ring.inverse`):  `Dcore A Q Cb J ≠ 0 ↔ IsUnit A ∧ IsUnit N0 ∧ IsUnit G1inv ∧ IsUnit Nm`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace

theorem ring_inverse_eq_of_mul {R : Type*} [Ring R] (a b : R) (h1 : a * b = 1) (h2 : b * a = 1) :
    Ring.inverse a = b :=
  Ring.inverse_unit (⟨a, b, h1, h2⟩ : Rˣ)

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem adj_smul (c : ℝ) (T : E →L[ℝ] F) :
    ContinuousLinearMap.adjoint (c • T) = c • ContinuousLinearMap.adjoint T := by
  ext1 y
  apply ext_inner_left ℝ
  intro x
  simp [ContinuousLinearMap.adjoint_inner_right, inner_smul_right]

theorem cadj_eq_smul_inverse {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : X →L[ℝ] X) (h : cdet A ≠ 0) : cadj A = cdet A • Ring.inverse A := by
  rw [inverse_eq_cadj A h, smul_smul, mul_inv_cancel₀ h, one_smul]

theorem inverse_smul' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : ℝ) (hc : c ≠ 0)
    (u : X →L[ℝ] X) (hu : IsUnit u) : Ring.inverse (c • u) = c⁻¹ • Ring.inverse u := by
  apply ring_inverse_eq_of_mul
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Ring.mul_inverse_cancel _ hu]
  · rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Ring.inverse_mul_cancel _ hu]

variable (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (Cb : E →L[ℝ] E →L[ℝ] F) (J : E)

noncomputable def gN0 : F →L[ℝ] F := (Q.comp (Ring.inverse A)).comp (ContinuousLinearMap.adjoint Q)
noncomputable def gH : F →L[ℝ] E :=
  ((Ring.inverse A).comp (ContinuousLinearMap.adjoint Q)).comp (Ring.inverse (gN0 A Q))
noncomputable def gDelta2 : E →L[ℝ] E := (2 : ℝ) • lamB Cb (ContinuousLinearMap.adjoint (gH A Q) J)
noncomputable def gG1inv : E →L[ℝ] E := A - gDelta2 A Q Cb J
noncomputable def gNm : F →L[ℝ] F :=
  (Q.comp (Ring.inverse (gG1inv A Q Cb J))).comp (ContinuousLinearMap.adjoint Q)

theorem Mc_eq (hd : cdet A ≠ 0) : Mc A Q = cdet A • gN0 A Q := by
  unfold Mc gN0
  rw [cadj_eq_smul_inverse A hd]
  ext1 y
  simp

theorem cdet_Mc_ne_iff (hd : cdet A ≠ 0) : cdet (Mc A Q) ≠ 0 ↔ cdet (gN0 A Q) ≠ 0 := by
  rw [Mc_eq A Q hd, cdet_smul]
  have : cdet A ^ Module.finrank ℝ F ≠ 0 := pow_ne_zero _ hd
  constructor
  · intro h h0; apply h; rw [h0, mul_zero]
  · intro h h0; exact h (by simpa [this] using h0)

theorem Hh_eq (hd : cdet A ≠ 0) (hM : cdet (Mc A Q) ≠ 0) : Hh A Q = cdet (Mc A Q) • gH A Q := by
  have hN : IsUnit (gN0 A Q) := isUnit_of_cdet_ne _ ((cdet_Mc_ne_iff A Q hd).mp hM)
  have hMu : IsUnit (Mc A Q) := isUnit_of_cdet_ne _ hM
  have hinv : Ring.inverse (Mc A Q) = (cdet A)⁻¹ • Ring.inverse (gN0 A Q) := by
    rw [Mc_eq A Q hd, inverse_smul' _ hd _ hN]
  unfold Hh gH
  rw [cadj_eq_smul_inverse A hd, cadj_eq_smul_inverse (Mc A Q) hM, hinv]
  ext1 y
  simp [smul_smul, hd]

theorem Bt_eq (hd : cdet A ≠ 0) (hM : cdet (Mc A Q) ≠ 0) :
    Bt A Q Cb J = cdet (Mc A Q) • gG1inv A Q Cb J := by
  unfold Bt gG1inv gDelta2 Kh
  rw [Hh_eq A Q hd hM, adj_smul]
  have : ∀ (c : ℝ) (κ : F), lamB Cb (c • κ) = c • lamB Cb κ := fun c κ => map_smul (lamB Cb) c κ
  simp only [ContinuousLinearMap.smul_apply, this, smul_sub, smul_comm (cdet (Mc A Q)) (2 : ℝ)]

theorem Nh_eq (hd : cdet A ≠ 0) (hM : cdet (Mc A Q) ≠ 0) (hB : cdet (Bt A Q Cb J) ≠ 0) :
    Nh A Q Cb J = (cdet (Bt A Q Cb J) * (cdet (Mc A Q))⁻¹) • gNm A Q Cb J := by
  have hBu : IsUnit (Bt A Q Cb J) := isUnit_of_cdet_ne _ hB
  have hG1 : IsUnit (gG1inv A Q Cb J) := by
    have h2 : IsUnit (cdet (Mc A Q) • gG1inv A Q Cb J) := by rw [← Bt_eq A Q Cb J hd hM]; exact hBu
    have hc : IsUnit (cdet (Mc A Q) • (1 : E →L[ℝ] E)) := by
      refine isUnit_of_cdet_ne _ ?_
      rw [cdet_smul, cdet_one, mul_one]; exact pow_ne_zero _ hM
    have : gG1inv A Q Cb J = (cdet (Mc A Q))⁻¹ • (cdet (Mc A Q) • gG1inv A Q Cb J) := by
      rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [this]
    refine isUnit_of_cdet_ne _ ?_
    rw [cdet_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hM)) (cdet_ne_of_isUnit _ h2)
  have hinv : Ring.inverse (Bt A Q Cb J) = (cdet (Mc A Q))⁻¹ • Ring.inverse (gG1inv A Q Cb J) := by
    rw [Bt_eq A Q Cb J hd hM, inverse_smul' _ hM _ hG1]
  unfold Nh gNm
  rw [cadj_eq_smul_inverse _ hB, hinv]
  ext1 y
  simp [smul_smul, mul_comm]

/-- the generic equivalence. -/
theorem core_iff_generic :
    Dcore A Q Cb J ≠ 0 ↔ (IsUnit A ∧ IsUnit (gN0 A Q) ∧ IsUnit (gG1inv A Q Cb J) ∧ IsUnit (gNm A Q Cb J)) := by
  constructor
  · intro hD
    unfold Dcore at hD
    have h4 := mul_ne_zero_iff.mp hD
    have h3 := mul_ne_zero_iff.mp h4.1
    have h2 := mul_ne_zero_iff.mp h3.1
    have hd : cdet A ≠ 0 := h2.1
    have hM : cdet (Mc A Q) ≠ 0 := h2.2
    have hB : cdet (Bt A Q Cb J) ≠ 0 := h3.2
    have hN : cdet (Nh A Q Cb J) ≠ 0 := h4.2
    have hN0 : IsUnit (gN0 A Q) := isUnit_of_cdet_ne _ ((cdet_Mc_ne_iff A Q hd).mp hM)
    have hBu : IsUnit (Bt A Q Cb J) := isUnit_of_cdet_ne _ hB
    have hG1 : IsUnit (gG1inv A Q Cb J) := by
      have : gG1inv A Q Cb J = (cdet (Mc A Q))⁻¹ • Bt A Q Cb J := by
        rw [Bt_eq A Q Cb J hd hM, smul_smul, inv_mul_cancel₀ hM, one_smul]
      rw [this]
      refine isUnit_of_cdet_ne _ ?_
      rw [cdet_smul]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hM)) hB
    refine ⟨isUnit_of_cdet_ne _ hd, hN0, hG1, ?_⟩
    rw [Nh_eq A Q Cb J hd hM hB, cdet_smul] at hN
    have := (mul_ne_zero_iff.mp hN).2
    exact isUnit_of_cdet_ne _ this
  · rintro ⟨hA, hN0, hG1, hNm⟩
    have hd : cdet A ≠ 0 := cdet_ne_of_isUnit _ hA
    have hM : cdet (Mc A Q) ≠ 0 := by
      rw [Mc_eq A Q hd, cdet_smul]
      exact mul_ne_zero (pow_ne_zero _ hd) (cdet_ne_of_isUnit _ hN0)
    have hB : cdet (Bt A Q Cb J) ≠ 0 := by
      rw [Bt_eq A Q Cb J hd hM, cdet_smul]
      exact mul_ne_zero (pow_ne_zero _ hM) (cdet_ne_of_isUnit _ hG1)
    have hN : cdet (Nh A Q Cb J) ≠ 0 := by
      rw [Nh_eq A Q Cb J hd hM hB, cdet_smul]
      exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hB (inv_ne_zero hM))) (cdet_ne_of_isUnit _ hNm)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd hM) hB) hN

end Generic

end AdalyFormal.CoverOmega.Struct

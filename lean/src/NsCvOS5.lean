import NsCvOS4

/-!
# CvOS5 -- scale invariance of the four units; specialisation of `core_iff_generic` to `BaseDataS` (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega.Struct

open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section Scale
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem isUnit_smul_iff (c : ℝ) (hc : c ≠ 0) (u : X →L[ℝ] X) : IsUnit (c • u) ↔ IsUnit u := by
  rw [isUnit_iff_cdet, isUnit_iff_cdet, cdet_smul]
  constructor
  · intro h h0; apply h; rw [h0, mul_zero]
  · intro h; exact mul_ne_zero (pow_ne_zero _ hc) h

theorem inverse_smul_all (c : ℝ) (hc : c ≠ 0) (u : X →L[ℝ] X) :
    Ring.inverse (c • u) = c⁻¹ • Ring.inverse u := by
  by_cases hu : IsUnit u
  · exact inverse_smul' c hc u hu
  · have : ¬ IsUnit (c • u) := fun h => hu ((isUnit_smul_iff c hc u).mp h)
    rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ this, smul_zero]

end Scale

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (A : E →L[ℝ] E) (Q : E →L[ℝ] F) (Cb : E →L[ℝ] E →L[ℝ] F) (J : E)

/-- the four units of the generic data. -/
def U4 : Prop := IsUnit A ∧ IsUnit (gN0 A Q) ∧ IsUnit (gG1inv A Q Cb J) ∧ IsUnit (gNm A Q Cb J)

theorem U4_smul (c : ℝ) (hc : c ≠ 0) : U4 (c • A) Q (c • Cb) J ↔ U4 A Q Cb J := by
  have h0 : gN0 (c • A) Q = c⁻¹ • gN0 A Q := by
    unfold gN0; rw [inverse_smul_all c hc]; ext1 y; simp
  have hH : gH (c • A) Q = gH A Q := by
    unfold gH; rw [h0, inverse_smul_all c⁻¹ (inv_ne_zero hc), inv_inv, inverse_smul_all c hc]
    ext1 y; simp [smul_smul, hc]
  have hD : gDelta2 (c • A) Q (c • Cb) J = c • gDelta2 A Q Cb J := by
    unfold gDelta2; rw [hH, map_smul]
    ext1 y; simp [smul_comm c (2 : ℝ)]
  have hG : gG1inv (c • A) Q (c • Cb) J = c • gG1inv A Q Cb J := by
    unfold gG1inv; rw [hD, smul_sub]
  have hN : gNm (c • A) Q (c • Cb) J = c⁻¹ • gNm A Q Cb J := by
    unfold gNm; rw [hG, inverse_smul_all c hc]; ext1 y; simp
  unfold U4
  rw [h0, hG, hN, isUnit_smul_iff c hc, isUnit_smul_iff c⁻¹ (inv_ne_zero hc), isUnit_smul_iff c hc,
    isUnit_smul_iff c⁻¹ (inv_ne_zero hc)]

end Generic

section BD
variable {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Qs_eq_adjoint (D : BaseDataS E S F) : D.Qs = ContinuousLinearMap.adjoint D.Q := by
  ext1 y
  apply ext_inner_left ℝ
  intro x
  rw [← D.Q_adj x y, ContinuousLinearMap.adjoint_inner_right]

theorem Delta2_eq_lam (D : BaseDataS E S F) (hL : D.Laws) (Cb : E →L[ℝ] E →L[ℝ] F)
    (hC : ∀ x, D.C2 x = Cb x x) (hs : ∀ x y, Cb x y = Cb y x) :
    D.Delta2 hL = (2 : ℝ) • lamB Cb (ContinuousLinearMap.adjoint D.H D.J) := by
  obtain ⟨hsym, hform⟩ := D.Delta2_spec hL
  apply symm_unique hsym
  · intro x y
    have e1 : ∀ u v : E, ⟪u, ((2 : ℝ) • lamB Cb (ContinuousLinearMap.adjoint D.H D.J)) v⟫ =
        2 * ⟪Cb u v, ContinuousLinearMap.adjoint D.H D.J⟫ := by
      intro u v
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, lamB_apply, inner_lam0]
    rw [real_inner_comm, e1, e1, hs]
  · intro A
    rw [hform A]
    have e1 : ⟪A, ((2 : ℝ) • lamB Cb (ContinuousLinearMap.adjoint D.H D.J)) A⟫ =
        2 * ⟪Cb A A, ContinuousLinearMap.adjoint D.H D.J⟫ := by
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, lamB_apply, inner_lam0]
    rw [e1, ← hC A, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

theorem baseData_gen_eq (D : BaseDataS E S F) (hL : D.Laws) (Cb : E →L[ℝ] E →L[ℝ] F)
    (hC : ∀ x, D.C2 x = Cb x x) (hs : ∀ x y, Cb x y = Cb y x) :
    gN0 D.Ginv D.Q = (D.Q.comp D.G).comp D.Qs ∧ gH D.Ginv D.Q = D.H ∧
    gDelta2 D.Ginv D.Q Cb D.J = D.Delta2 hL ∧ gG1inv D.Ginv D.Q Cb D.J = D.Ginv - D.Delta2 hL ∧
    gNm D.Ginv D.Q Cb D.J = (D.Q.comp (D.G1 (D.Ginv - D.Delta2 hL))).comp D.Qs := by
  have h0 : gN0 D.Ginv D.Q = (D.Q.comp D.G).comp D.Qs := by
    unfold gN0; rw [Qs_eq_adjoint]; rfl
  have hH : gH D.Ginv D.Q = D.H := by
    unfold gH BaseDataS.H; rw [h0, Qs_eq_adjoint]; rfl
  have hD : gDelta2 D.Ginv D.Q Cb D.J = D.Delta2 hL := by
    unfold gDelta2; rw [hH, Delta2_eq_lam D hL Cb hC hs]
  have hG : gG1inv D.Ginv D.Q Cb D.J = D.Ginv - D.Delta2 hL := by
    unfold gG1inv; rw [hD]
  refine ⟨h0, hH, hD, hG, ?_⟩
  unfold gNm; rw [hG, Qs_eq_adjoint]; rfl

/-- the four units of the genuine base data. -/
def BDUnits (D : BaseDataS E S F) (hL : D.Laws) : Prop :=
  IsUnit D.Ginv ∧ IsUnit ((D.Q.comp D.G).comp D.Qs) ∧ IsUnit (D.Ginv - D.Delta2 hL) ∧
    IsUnit ((D.Q.comp (D.G1 (D.Ginv - D.Delta2 hL))).comp D.Qs)

theorem BDUnits_iff_U4 (D : BaseDataS E S F) (hL : D.Laws) (Cb : E →L[ℝ] E →L[ℝ] F)
    (hC : ∀ x, D.C2 x = Cb x x) (hs : ∀ x y, Cb x y = Cb y x) :
    BDUnits D hL ↔ U4 D.Ginv D.Q Cb D.J := by
  obtain ⟨h0, -, -, hG, hN⟩ := baseData_gen_eq D hL Cb hC hs
  unfold BDUnits U4
  rw [h0, hG, hN]

/-- **the core determinant detects the four units of the genuine base data (unscaled).** -/
theorem core_iff_baseData (D : BaseDataS E S F) (hL : D.Laws) (Cb : E →L[ℝ] E →L[ℝ] F)
    (hC : ∀ x, D.C2 x = Cb x x) (hs : ∀ x y, Cb x y = Cb y x) :
    Dcore D.Ginv D.Q Cb D.J ≠ 0 ↔ BDUnits D hL := by
  rw [BDUnits_iff_U4 D hL Cb hC hs]
  exact core_iff_generic D.Ginv D.Q Cb D.J

/-- **scaled version**: `Ginv = c • Ah`, `Cb = c • Cbh` with `c ≠ 0`. -/
theorem core_iff_baseData_scaled (D : BaseDataS E S F) (hL : D.Laws) (Cb : E →L[ℝ] E →L[ℝ] F)
    (hC : ∀ x, D.C2 x = Cb x x) (hs : ∀ x y, Cb x y = Cb y x)
    (c : ℝ) (hc : c ≠ 0) (Ah : E →L[ℝ] E) (Cbh : E →L[ℝ] E →L[ℝ] F)
    (hA : D.Ginv = c • Ah) (hCb : Cb = c • Cbh) :
    Dcore Ah D.Q Cbh D.J ≠ 0 ↔ BDUnits D hL := by
  rw [BDUnits_iff_U4 D hL Cb hC hs, hA, hCb, U4_smul Ah D.Q Cbh D.J c hc]
  exact core_iff_generic Ah D.Q Cbh D.J

end BD

end AdalyFormal.CoverOmega.Struct

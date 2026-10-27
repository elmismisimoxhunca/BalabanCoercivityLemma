import GdGen3

/-!
# GdGen4 -- the literal and the localised `genFormS` coincide (any configuration `U`), once all units exist.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section abstract
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Q G Q*` is a unit as soon as `Q G₁ Q*` is. -/
theorem NG_unit_of_N1 (D : BaseDataS E S F) (hL : D.Laws) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv)
    (hN1 : IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs)) : IsUnit ((D.Q.comp D.G).comp D.Qs) := by
  by_contra hn
  have hH : D.H = 0 := by
    unfold BaseDataS.H
    rw [Ring.inverse_non_unit _ hn]
    simp only [ContinuousLinearMap.comp_zero]
  have hD2 : D.Delta2 hL = 0 := by
    obtain ⟨hs, hf⟩ := D.Delta2_spec hL
    refine symm_unique hs (fun x y => by simp) (fun A => ?_)
    rw [hf A, hH]; simp
  have hG1 : G1inv = D.Ginv := by
    have h := D.G1inv_unique hG (D.isG1inv_sub hL)
    rw [h, hD2]; simp
  apply hn
  have : D.G1 G1inv = D.G := by rw [hG1]; rfl
  rw [this] at hN1
  exact hN1

theorem Q_H1_apply (D : BaseDataS E S F) (G1inv : E →L[ℝ] E) (hN : IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs)) (f : F) :
    D.Q (D.H1 G1inv f) = f := by
  unfold BaseDataS.H1
  simp only [ContinuousLinearMap.comp_apply]
  have h := ContinuousLinearMap.ext_iff.mp (Ring.mul_inverse_cancel _ hN) f
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using h

/-- unit transfer along a subspace containing `{x | Q x ∈ Z}`. -/
theorem unit_transfer {M₁ M₂ : E →L[ℝ] E} {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E} (V : Submodule ℝ E) (Z : Submodule ℝ F)
    (hM₁ : IsUnit M₁) (hM₂ : IsUnit M₂) (hN₂ : IsUnit ((Q.comp (Ring.inverse M₂)).comp Qs))
    (hZV : ∀ x, Q x ∈ Z → x ∈ V) (hM : ∀ x ∈ V, M₁ x = M₂ x) :
    IsUnit ((Q.comp (Ring.inverse M₁)).comp Qs) := by
  have hl₁ : ∀ x, M₁ (Ring.inverse M₁ x) = x := fun x =>
    congrArg (fun S : E →L[ℝ] E => S x) (Ring.mul_inverse_cancel M₁ hM₁)
  have hr₂ : ∀ x, Ring.inverse M₂ (M₂ x) = x := fun x =>
    congrArg (fun S : E →L[ℝ] E => S x) (Ring.inverse_mul_cancel M₂ hM₂)
  have hinj : Function.Injective ((Q.comp (Ring.inverse M₁)).comp Qs) := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    have hQx : Q (Ring.inverse M₁ (Qs l)) = 0 := hl
    have hxV : Ring.inverse M₁ (Qs l) ∈ V := hZV _ (by rw [hQx]; exact Z.zero_mem)
    have hMx : M₂ (Ring.inverse M₁ (Qs l)) = Qs l := by rw [← hM _ hxV]; exact hl₁ _
    have hxM2 : Ring.inverse M₁ (Qs l) = Ring.inverse M₂ (Qs l) := by
      have h := hr₂ (Ring.inverse M₁ (Qs l))
      rw [hMx] at h
      exact h.symm
    have hN2l : ((Q.comp (Ring.inverse M₂)).comp Qs) l = 0 := by
      show Q (Ring.inverse M₂ (Qs l)) = 0
      rw [← hxM2]; exact hQx
    exact (injective_iff_map_eq_zero _).mp (ContinuousLinearMap.isUnit_iff_bijective.mp hN₂).1 l hN2l
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective
      (f := (show F →ₗ[ℝ] F from (Q.comp (Ring.inverse M₁)).comp Qs))).mp hinj⟩

variable {D1 D2 : BaseDataS E S F} {V : Submodule ℝ E} {Z : Submodule ℝ F}

/-- the `J`-pairing of `H₁ f` is the same for the two data. -/
theorem TwoData.inner_H1_J_eq (h : TwoData D1 D2 V Z) (hL1 : D1.Laws) (hL2 : D2.Laws) (u1 : IsUnit D1.Ginv) (u2 : IsUnit D2.Ginv)
    (n1 : IsUnit ((D1.Q.comp D1.G).comp D1.Qs)) (n2 : IsUnit ((D2.Q.comp D2.G).comp D2.Qs))
    {G₁ G₂ : E →L[ℝ] E} (hG₁ : D1.IsG1inv G₁) (hG₂ : D2.IsG1inv G₂) (g1 : IsUnit G₁) (g2 : IsUnit G₂)
    (m1 : IsUnit ((D1.Q.comp (D1.G1 G₁)).comp D1.Qs)) (m2 : IsUnit ((D2.Q.comp (D2.G1 G₂)).comp D2.Qs)) {f : F} (hf : f ∈ Z) :
    ⟪D1.H1 G₁ f, D1.J⟫ = ⟪D2.H1 G₂ f, D2.J⟫ := by
  have hV : D1.H1 G₁ f ∈ V := h.hZV _ (by rw [Q_H1_apply D1 G₁ m1 f]; exact hf)
  rw [h.hJ _ hV, (h.N1inv_H1_eq hL1 hL2 u1 u2 n1 n2 hG₁ hG₂ g1 g2 m1 m2 hf).2]

end abstract

#print axioms NG_unit_of_N1
#print axioms Q_H1_apply
#print axioms unit_transfer
#print axioms TwoData.inner_H1_J_eq

section gen
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
theorem twoData_lit_loc (sD sJ sD' sJ' : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsD' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD' L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hsJ' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ' L G) :
    TwoData (dataS sD sJ P) (dataS sD' sJ' P) (V0 P.G) (Z0 P.G) where
  hQ := (dataS_Q_eq sD sJ P).trans (dataS_Q_eq sD' sJ' P).symm
  hQs := (dataS_Qs_eq sD sJ P).trans (dataS_Qs_eq sD' sJ' P).symm
  hC2 := (dataS_C2_eq sD sJ P).trans (dataS_C2_eq sD' sJ' P).symm
  hZV := by
    intro x hx β hβ
    have h1 := Q_level0_coord sD sJ P x β hβ
    have h2 := hx β hβ
    rw [h1] at h2
    exact h2
  hCZ := by
    intro A β hβ
    exact C2full_level0_coord P.G P.U _ β hβ
  hM := fun x hx => Ginv_eq_on_V P hS hell0 hroom sD sJ sD' sJ' hsD hsD' hx
  hJ := by
    intro x hx
    rw [dataS_J_proj, dataS_J_proj, pE_inner_right, pE_inner_right]
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb1 : b ∈ bondsOm0 P.G
    · by_cases hb2 : b ∈ bondsLam P.G 0
      · rw [hx b hb2]; simp
      · rw [JfS_eq_near P hS hell0 hroom sJ sJ' hsJ hsJ' b hb1 hb2]
    · have h0 : (WithLp.ofLp (iE P.G x)) b = 0 := x.2 b hb1
      rw [h0]; simp

#print axioms twoData_lit_loc

end gen

end AdalyFormal.D1Guarded

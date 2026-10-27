import GdAbs

/-!
# GdStat -- the constrained problem `{Q x = f}` only sees the operator on a subspace `V` containing every `x` with `Q x ∈ Z`.

Abstract finite-dimensional algebra (two `BaseDataS` with the same `Q`, `Qs`, `C2`; operators agreeing on `V`; sources agreeing against `V`).
* `stat_eq`      : `N₁⁻¹ f = N₂⁻¹ f` and `M₁⁻¹ Qs N₁⁻¹ f = M₂⁻¹ Qs N₂⁻¹ f` for `f ∈ Z`, when all four of `M₁ M₂ N₁ N₂` are units.
* `H_eq`         : `D₁.H f = D₂.H f` for `f ∈ Z`.
* `Delta2_eq`    : `D₁.Delta2 = D₂.Delta2`  (when `C2` takes values in `Z`).
* `G1inv_eq_on`  : `G1inv₁ x = G1inv₂ x` for `x ∈ V`.
* `H1_eq`, `N1inv_eq` : the same for `H₁`, `(Q G₁ Q*)⁻¹` on `Z`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2

section generic
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem stat_eq {M₁ M₂ : E →L[ℝ] E} {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E} (V : Submodule ℝ E) (Z : Submodule ℝ F)
    (hM₂ : IsUnit M₂) (hN₁ : IsUnit ((Q.comp (Ring.inverse M₁)).comp Qs)) (hN₂ : IsUnit ((Q.comp (Ring.inverse M₂)).comp Qs))
    (hM₁ : IsUnit M₁) (hZV : ∀ x, Q x ∈ Z → x ∈ V) (hM : ∀ x ∈ V, M₁ x = M₂ x) {f : F} (hf : f ∈ Z) :
    Ring.inverse ((Q.comp (Ring.inverse M₁)).comp Qs) f = Ring.inverse ((Q.comp (Ring.inverse M₂)).comp Qs) f ∧
    Ring.inverse M₁ (Qs (Ring.inverse ((Q.comp (Ring.inverse M₁)).comp Qs) f)) =
      Ring.inverse M₂ (Qs (Ring.inverse ((Q.comp (Ring.inverse M₂)).comp Qs) f)) := by
  set N₁ := (Q.comp (Ring.inverse M₁)).comp Qs with hN₁d
  set N₂ := (Q.comp (Ring.inverse M₂)).comp Qs with hN₂d
  set z := Ring.inverse N₁ f with hz
  have hl₁ : ∀ x, M₁ (Ring.inverse M₁ x) = x := fun x =>
    congrArg (fun S : E →L[ℝ] E => S x) (Ring.mul_inverse_cancel M₁ hM₁)
  have hr₂ : ∀ x, Ring.inverse M₂ (M₂ x) = x := fun x =>
    congrArg (fun S : E →L[ℝ] E => S x) (Ring.inverse_mul_cancel M₂ hM₂)
  have hNz : N₁ z = f := congrArg (fun S : F →L[ℝ] F => S f) (Ring.mul_inverse_cancel N₁ hN₁)
  set x := Ring.inverse M₁ (Qs z) with hx
  have hQx : Q x = f := by
    have h0 : Q x = N₁ z := rfl
    rw [h0, hNz]
  have hxV : x ∈ V := hZV x (hQx ▸ hf)
  have hMx : M₂ x = Qs z := by rw [← hM x hxV]; exact hl₁ _
  have hxM2 : x = Ring.inverse M₂ (Qs z) := by rw [← hMx, hr₂]
  have hN2z : N₂ z = f := by
    have h0 : N₂ z = Q (Ring.inverse M₂ (Qs z)) := rfl
    rw [h0, ← hxM2, hQx]
  have hzz : z = Ring.inverse N₂ f := by
    have h1 : Ring.inverse N₂ (N₂ z) = z := congrArg (fun S : F →L[ℝ] F => S z) (Ring.inverse_mul_cancel N₂ hN₂)
    rw [hN2z] at h1
    exact h1.symm
  refine ⟨hzz, ?_⟩
  rw [← hzz]
  exact hxM2

/-- two base data sharing `Q`, `Qs`, `C2`, agreeing on `V` (operator and source), where `V ⊇ {x | Q x ∈ Z}` and `C2` takes values in `Z`. -/
structure TwoData (D1 D2 : BaseDataS E S F) (V : Submodule ℝ E) (Z : Submodule ℝ F) : Prop where
  hQ : D1.Q = D2.Q
  hQs : D1.Qs = D2.Qs
  hC2 : D1.C2 = D2.C2
  hZV : ∀ x, D1.Q x ∈ Z → x ∈ V
  hCZ : ∀ A, D1.C2 A ∈ Z
  hM : ∀ x ∈ V, D1.Ginv x = D2.Ginv x
  hJ : ∀ x ∈ V, ⟪x, D1.J⟫ = ⟪x, D2.J⟫

variable {D1 D2 : BaseDataS E S F} {V : Submodule ℝ E} {Z : Submodule ℝ F}

theorem TwoData.H_eq (h : TwoData D1 D2 V Z) (u1 : IsUnit D1.Ginv) (u2 : IsUnit D2.Ginv)
    (n1 : IsUnit ((D1.Q.comp D1.G).comp D1.Qs)) (n2 : IsUnit ((D2.Q.comp D2.G).comp D2.Qs)) {f : F} (hf : f ∈ Z) :
    D1.H f = D2.H f := by
  have hz : ∀ x, D2.Q x ∈ Z → x ∈ V := fun x hx => h.hZV x (by rw [h.hQ]; exact hx)
  have := (stat_eq (M₁ := D1.Ginv) (M₂ := D2.Ginv) (Q := D2.Q) (Qs := D2.Qs) V Z u2
    (by unfold BaseDataS.G at n1; rw [h.hQ, h.hQs] at n1; exact n1) n2 u1 hz h.hM hf).2
  unfold BaseDataS.H
  simp only [ContinuousLinearMap.comp_apply, h.hQ, h.hQs]
  exact this

theorem TwoData.Delta2_eq (h : TwoData D1 D2 V Z) (hL1 : D1.Laws) (hL2 : D2.Laws) (u1 : IsUnit D1.Ginv) (u2 : IsUnit D2.Ginv)
    (n1 : IsUnit ((D1.Q.comp D1.G).comp D1.Qs)) (n2 : IsUnit ((D2.Q.comp D2.G).comp D2.Qs)) :
    D1.Delta2 hL1 = D2.Delta2 hL2 := by
  obtain ⟨hs1, hf1⟩ := D1.Delta2_spec hL1
  obtain ⟨hs2, hf2⟩ := D2.Delta2_spec hL2
  refine symm_unique hs1 hs2 (fun A => ?_)
  rw [hf1 A, hf2 A]
  have hCA : D1.C2 A ∈ Z := h.hCZ A
  have hH : D1.H (D1.C2 A) = D2.H (D1.C2 A) := h.H_eq u1 u2 n1 n2 hCA
  have hHV : D2.H (D1.C2 A) ∈ V := by
    apply h.hZV
    rw [h.hQ, Q_H_apply D2 n2]
    exact hCA
  rw [hH, ← h.hC2]
  have := h.hJ _ hHV
  rw [real_inner_comm, real_inner_comm (D2.H (D1.C2 A))] at this
  rw [this]

theorem TwoData.G1inv_eq_on (h : TwoData D1 D2 V Z) (hL1 : D1.Laws) (hL2 : D2.Laws) (u1 : IsUnit D1.Ginv) (u2 : IsUnit D2.Ginv)
    (n1 : IsUnit ((D1.Q.comp D1.G).comp D1.Qs)) (n2 : IsUnit ((D2.Q.comp D2.G).comp D2.Qs))
    {G₁ G₂ : E →L[ℝ] E} (hG₁ : D1.IsG1inv G₁) (hG₂ : D2.IsG1inv G₂) {x : E} (hx : x ∈ V) : G₁ x = G₂ x := by
  have e1 : G₁ = D1.Ginv - D1.Delta2 hL1 := D1.G1inv_unique hG₁ (D1.isG1inv_sub hL1)
  have e2 : G₂ = D2.Ginv - D2.Delta2 hL2 := D2.G1inv_unique hG₂ (D2.isG1inv_sub hL2)
  rw [e1, e2, h.Delta2_eq hL1 hL2 u1 u2 n1 n2]
  simp only [ContinuousLinearMap.sub_apply, h.hM x hx]

theorem TwoData.N1inv_H1_eq (h : TwoData D1 D2 V Z) (hL1 : D1.Laws) (hL2 : D2.Laws) (u1 : IsUnit D1.Ginv) (u2 : IsUnit D2.Ginv)
    (n1 : IsUnit ((D1.Q.comp D1.G).comp D1.Qs)) (n2 : IsUnit ((D2.Q.comp D2.G).comp D2.Qs))
    {G₁ G₂ : E →L[ℝ] E} (hG₁ : D1.IsG1inv G₁) (hG₂ : D2.IsG1inv G₂) (g1 : IsUnit G₁) (g2 : IsUnit G₂)
    (m1 : IsUnit ((D1.Q.comp (D1.G1 G₁)).comp D1.Qs)) (m2 : IsUnit ((D2.Q.comp (D2.G1 G₂)).comp D2.Qs)) {f : F} (hf : f ∈ Z) :
    Ring.inverse ((D1.Q.comp (D1.G1 G₁)).comp D1.Qs) f = Ring.inverse ((D2.Q.comp (D2.G1 G₂)).comp D2.Qs) f ∧
      D1.H1 G₁ f = D2.H1 G₂ f := by
  have hz : ∀ x, D2.Q x ∈ Z → x ∈ V := fun x hx => h.hZV x (by rw [h.hQ]; exact hx)
  have m1' : IsUnit ((D2.Q.comp (Ring.inverse G₁)).comp D2.Qs) := by
    unfold BaseDataS.G1 at m1; rw [h.hQ, h.hQs] at m1; exact m1
  have m2' : IsUnit ((D2.Q.comp (Ring.inverse G₂)).comp D2.Qs) := by unfold BaseDataS.G1 at m2; exact m2
  have key := stat_eq (M₁ := G₁) (M₂ := G₂) (Q := D2.Q) (Qs := D2.Qs) V Z g2 m1' m2' g1 hz
    (fun x hx => h.G1inv_eq_on hL1 hL2 u1 u2 n1 n2 hG₁ hG₂ hx) hf
  refine ⟨?_, ?_⟩
  · unfold BaseDataS.G1
    rw [h.hQ, h.hQs]
    exact key.1
  · unfold BaseDataS.H1 BaseDataS.G1
    simp only [ContinuousLinearMap.comp_apply, h.hQ, h.hQs]
    exact key.2

end generic

#print axioms stat_eq
#print axioms TwoData.H_eq
#print axioms TwoData.Delta2_eq
#print axioms TwoData.G1inv_eq_on
#print axioms TwoData.N1inv_H1_eq

end AdalyFormal.D1Guarded

import NuB2

/-!
# NuB5 -- extracting the pencil `H0 + w B` on the fixed space from a bilinear-form identity (abstract; lane ncwdh_ell2_20261018)

`A : ℝ → E → E` symmetric, commuting with the reflection `TE`; a real function `β` on pairs of fixed vectors with `β x x ≥ 0` and
`<x', A w x> = <x', A 1 x> + (w - 1) β x' x` for fixed `x, x'` and `w` in a set containing `0`.  Then there are symmetric, `TE`-commuting `H0`, `B ≥ 0` with
`A w x = H0 x + w B x` for fixed `x`.
-/
set_option autoImplicit false

namespace AdalyNcwdhTwo.Bridge

open scoped RealInnerProductSpace
open AdalyNcwdhTwo.Mono

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem pencil_exists {TE : E →L[ℝ] E} (hTE2 : ∀ x, TE (TE x) = x) (hTEs : Sym TE)
    (A : ℝ → E →L[ℝ] E) (hAs : ∀ w x y, ⟪A w x, y⟫ = ⟪x, A w y⟫) (hAc : ∀ w x, A w (TE x) = TE (A w x))
    (β : E → E → ℝ) (hβ : ∀ x, TE x = x → 0 ≤ β x x) (S : Set ℝ) (h0 : (0 : ℝ) ∈ S)
    (hid : ∀ w ∈ S, ∀ x x', TE x = x → TE x' = x' → ⟪x', A w x⟫ = ⟪x', A 1 x⟫ + (w - 1) * β x' x) :
    ∃ H0 B : E →L[ℝ] E, Sym H0 ∧ Sym B ∧ (∀ a, 0 ≤ ⟪a, B a⟫) ∧ (∀ x, H0 (TE x) = TE (H0 x)) ∧ (∀ x, B (TE x) = TE (B x)) ∧
      ∀ w ∈ S, ∀ x, TE x = x → A w x = H0 x + w • B x := by
  set P : E →L[ℝ] E := Pr TE with hP
  have hPs : Sym P := Pr_sym hTEs
  have hPfix : ∀ x, TE x = x → P x = x := fun x hx => Pr_fixed hx
  have hPTE : ∀ x, TE (P x) = P x := fun x => TE_Pr hTE2 x
  have hPTE' : ∀ x, P (TE x) = P x := by
    intro x
    simp only [hP, Pr_apply, hTE2]
    rw [add_comm]
  set Δ : E →L[ℝ] E := A 0 - A 1 with hΔ
  have hΔs : Sym Δ := by
    intro a b
    simp only [hΔ, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hAs]
  have hΔc : ∀ x, Δ (TE x) = TE (Δ x) := by
    intro x
    simp only [hΔ, ContinuousLinearMap.sub_apply, hAc, map_sub]
  set B : E →L[ℝ] E := -(P * Δ * P) with hB
  have hBx : ∀ x, B x = -(P (Δ (P x))) := fun x => by simp [hB]
  set H0 : E →L[ℝ] E := P * (A 1 - B) * P with hH0
  have hH0x : ∀ x, H0 x = P ((A 1 - B) (P x)) := fun x => rfl
  have hBs : Sym B := by
    intro a b
    rw [hBx, hBx, inner_neg_left, inner_neg_right, hPs, hΔs, hPs]
  have hBc : ∀ x, B (TE x) = TE (B x) := by
    intro x
    rw [hBx, hBx, hPTE', map_neg, hPTE]
  have hBfix : ∀ x, TE (B x) = B x := by
    intro x; rw [hBx, map_neg, hPTE]
  have hBinner : ∀ x x', TE x = x → TE x' = x' → ⟪x', B x⟫ = β x' x := by
    intro x x' hx hx'
    rw [hBx, inner_neg_right, ← hPs, hPfix x' hx', hPfix x hx]
    have := hid 0 h0 x x' hx hx'
    have h1 : ⟪x', Δ x⟫ = ⟪x', A 0 x⟫ - ⟪x', A 1 x⟫ := by
      simp only [hΔ, ContinuousLinearMap.sub_apply, inner_sub_right]
    rw [h1, this]; ring
  have hXs : Sym (A 1 - B) := by
    intro a b
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hAs, hBs a b]
  have hPidem : ∀ x, P (P x) = P x := fun x => Pr_idem hTE2 x
  have hH0fix : ∀ x, TE (H0 x) = H0 x := fun x => by rw [hH0x, hPTE]
  refine ⟨H0, B, ?_, hBs, ?_, ?_, hBc, ?_⟩
  · intro a b
    calc ⟪H0 a, b⟫ = ⟪(A 1 - B) (P a), P b⟫ := by rw [hH0x]; exact hPs _ _
      _ = ⟪P a, (A 1 - B) (P b)⟫ := hXs _ _
      _ = ⟪a, H0 b⟫ := by rw [hH0x]; exact hPs _ _
  · intro a
    have h1 : ⟪a, B a⟫ = ⟪P a, B (P a)⟫ := by
      have e1 : ⟪a, P (Δ (P a))⟫ = ⟪P a, Δ (P a)⟫ := (hPs a _).symm
      have e2 : ⟪P a, P (Δ (P (P a)))⟫ = ⟪P a, Δ (P a)⟫ := by
        rw [hPidem, ← hPs (P a), hPidem]
      rw [hBx, hBx, inner_neg_right, inner_neg_right, e1, e2]
    rw [h1, hBinner (P a) (P a) (hPTE a) (hPTE a)]
    exact hβ _ (hPTE a)
  · intro x
    rw [hH0x, hH0x, hPTE']
    exact (hPTE _).symm
  · intro w hw x hx
    have hAx : TE (A w x) = A w x := by rw [← hAc, hx]
    have hA1x : TE (A 1 x) = A 1 x := by rw [← hAc, hx]
    have hH0eq : H0 x = A 1 x - B x := by
      rw [hH0x, hPfix x hx]
      simp only [ContinuousLinearMap.sub_apply]
      exact hPfix _ (by rw [map_sub, hA1x, hBfix])
    set v : E := A w x - A 1 x - (w - 1) • B x with hv
    have hvfix : TE v = v := by
      rw [hv, map_sub, map_sub, map_smul, hAx, hA1x, hBfix]
    have hv0 : ⟪v, v⟫ = 0 := by
      have e1 : ⟪v, A w x⟫ = ⟪v, A 1 x⟫ + (w - 1) * β v x := hid w hw x v hx hvfix
      have e2 : ⟪v, B x⟫ = β v x := hBinner x v hx hvfix
      have hvdef : v = A w x - A 1 x - (w - 1) • B x := rfl
      calc ⟪v, v⟫ = ⟪v, A w x - A 1 x - (w - 1) • B x⟫ := by rw [← hvdef]
        _ = ⟪v, A w x⟫ - ⟪v, A 1 x⟫ - (w - 1) * ⟪v, B x⟫ := by
            simp only [inner_sub_right, inner_smul_right]
        _ = 0 := by rw [e1, e2]; ring
    have : v = 0 := inner_self_eq_zero.mp hv0
    rw [hH0eq]
    have h2 : A w x - A 1 x - (w - 1) • B x = 0 := this
    have : A w x = A 1 x + (w - 1) • B x := by
      have := h2; rw [sub_sub, sub_eq_zero] at this; rw [this]
    rw [this]
    module

end

end AdalyNcwdhTwo.Bridge

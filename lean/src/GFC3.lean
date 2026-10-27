import Mathlib

/-!
# GFC3 -- abstract Bloch splitting (finite abelian group, unitary action, invariant linear form)

If a finite abelian group `Γ` acts unitarily on a complex inner product space `H`, `Φ : H →ₗ H` commutes with the
action, and `c ‖z‖² ≤ Re ⟪z, Φ z⟫` holds on every isotypic component `{z | ∀ g, T g z = χ g • z}`, then it holds on `H`.
Standard axioms only.
-/
set_option autoImplicit false
open scoped ComplexInnerProductSpace
open Finset

namespace AdalyFormal.FlatCoercivity

section Bloch
variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- isotypic projector -/
noncomputable def isoProj (T : Γ → H →ₗ[ℂ] H) (χ : AddChar Γ ℂ) (z : H) : H :=
  ((Fintype.card Γ : ℂ)⁻¹) • ∑ g : Γ, (χ (-g)) • T g z

variable (T : Γ → H →ₗ[ℂ] H)

theorem isoProj_eigen (hTadd : ∀ g h, T (g + h) = (T g).comp (T h)) (χ : AddChar Γ ℂ) (z : H) (h : Γ) :
    T h (isoProj T χ z) = χ h • isoProj T χ z := by
  unfold isoProj
  rw [map_smul, map_sum]
  have h1 : ∀ g, T h (χ (-g) • T g z) = χ (-g) • T (h + g) z := fun g => by
    rw [map_smul, hTadd]; rfl
  simp only [h1]
  have h2 : ∑ g : Γ, χ (-g) • T (h + g) z = χ h • ∑ g : Γ, χ (-g) • T g z := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_addLeft, smul_smul]
    congr 1
    rw [show -g = h + -(h + g) by abel, AddChar.map_add_eq_mul]
  rw [h2, smul_comm]

theorem sum_isoProj (hT0 : T 0 = LinearMap.id) (z : H) : ∑ χ : AddChar Γ ℂ, isoProj T χ z = z := by
  unfold isoProj
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hc : ∀ g : Γ, ∑ χ : AddChar Γ ℂ, χ (-g) • T g z
      = (if g = 0 then (Fintype.card Γ : ℂ) else 0) • T g z := by
    intro g
    rw [← Finset.sum_smul]
    have := AddChar.sum_apply_eq_ite (α := Γ) (-g)
    rw [this]
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]
  simp only [hc]
  rw [Finset.sum_eq_single (0 : Γ)]
  · have : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp [hT0, this]
  · intro g _ hg; simp [hg]
  · intro h; exact absurd (Finset.mem_univ _) h


/-- two eigenvectors of different characters are orthogonal (unitary action) -/
theorem eigen_orth (hTunit : ∀ g x y, ⟪T g x, T g y⟫ = ⟪x, y⟫) (χ χ' : AddChar Γ ℂ) (hne : χ ≠ χ')
    (u w : H) (hu : ∀ g, T g u = χ' g • u) (hw : ∀ g, T g w = χ g • w) : ⟪u, w⟫ = 0 := by
  by_contra hne0
  apply hne
  ext g
  have h := hTunit g u w
  rw [hu g, hw g, inner_smul_left, inner_smul_right] at h
  have h2 : (starRingEnd ℂ) (χ' g) * χ g = 1 := by
    have h' : (starRingEnd ℂ) (χ' g) * χ g * ⟪u, w⟫ = 1 * ⟪u, w⟫ := by rw [one_mul, mul_assoc]; exact h
    exact mul_right_cancel₀ hne0 h'
  have h3 : (starRingEnd ℂ) (χ' g) * χ' g = 1 := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]; simp
  have h4 : χ' g ≠ 0 := by
    intro h0; rw [h0] at h3; simp at h3
  have h5 := h2.trans h3.symm
  exact mul_left_cancel₀ (by
    intro h0; rw [h0] at h3; simp at h3 : (starRingEnd ℂ) (χ' g) ≠ 0) h5


omit [DecidableEq Γ] in
theorem inner_sum_eigen (hTunit : ∀ g x y, ⟪T g x, T g y⟫ = ⟪x, y⟫)
    (u w : AddChar Γ ℂ → H) (hu : ∀ χ g, T g (u χ) = χ g • u χ) (hw : ∀ χ g, T g (w χ) = χ g • w χ) :
    ⟪∑ χ, u χ, ∑ χ, w χ⟫ = ∑ χ, ⟪u χ, w χ⟫ := by
  classical
  rw [sum_inner]
  simp only [inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  rw [Finset.sum_eq_single χ]
  · intro χ' _ hne
    exact eigen_orth T hTunit χ χ' (Ne.symm hne) (u χ') (w χ) (hu χ') (hw χ)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bloch_coercive (hT0 : T 0 = LinearMap.id)
    (hTadd : ∀ g h, T (g + h) = (T g).comp (T h))
    (hTunit : ∀ g x y, ⟪T g x, T g y⟫ = ⟪x, y⟫)
    (Φ : H →ₗ[ℂ] H) (hΦ : ∀ g z, Φ (T g z) = T g (Φ z)) (c : ℝ)
    (hc : ∀ (χ : AddChar Γ ℂ) (z : H), (∀ g, T g z = χ g • z) → c * ‖z‖ ^ 2 ≤ (⟪z, Φ z⟫).re)
    (z : H) : c * ‖z‖ ^ 2 ≤ (⟪z, Φ z⟫).re := by
  classical
  set zc : AddChar Γ ℂ → H := fun χ => isoProj T χ z with hzc
  have hev : ∀ χ g, T g (zc χ) = χ g • zc χ := fun χ g => isoProj_eigen T hTadd χ z g
  have hΦev : ∀ χ g, T g (Φ (zc χ)) = χ g • Φ (zc χ) := fun χ g => by
    rw [← hΦ, hev, map_smul]
  have hsum : ∑ χ, zc χ = z := sum_isoProj T hT0 z
  have h1 : ‖z‖ ^ 2 = ∑ χ, ‖zc χ‖ ^ 2 := by
    have := inner_sum_eigen T hTunit zc zc hev hev
    rw [hsum] at this
    have h2 : (⟪z, z⟫ : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h3 : ∀ χ, (⟪zc χ, zc χ⟫ : ℂ) = ((‖zc χ‖ ^ 2 : ℝ) : ℂ) := fun χ => by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h2] at this
    simp only [h3] at this
    exact_mod_cast this
  have h4 : (⟪z, Φ z⟫).re = ∑ χ, (⟪zc χ, Φ (zc χ)⟫).re := by
    have := inner_sum_eigen T hTunit zc (fun χ => Φ (zc χ)) hev hΦev
    rw [← map_sum, hsum] at this
    rw [this, Complex.re_sum]
  rw [h1, h4, Finset.mul_sum]
  exact Finset.sum_le_sum (fun χ _ => hc χ (zc χ) (hev χ))

end Bloch



section BlochSum
variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]

/-- **Bloch splitting for a sum of squared equivariant maps.** -/
theorem bloch_coercive_sum (T : Γ → H →ₗ[ℂ] H) (hT0 : T 0 = LinearMap.id)
    (hTadd : ∀ g h, T (g + h) = (T g).comp (T h))
    (hTunit : ∀ g x y, ⟪T g x, T g y⟫ = ⟪x, y⟫)
    (U : ∀ i, Γ → K i →ₗ[ℂ] K i) (hUunit : ∀ i g x y, ⟪U i g x, U i g y⟫ = ⟪x, y⟫)
    (L : ∀ i, H →ₗ[ℂ] K i) (hL : ∀ i g z, L i (T g z) = U i g (L i z)) (c : ℝ)
    (hc : ∀ (χ : AddChar Γ ℂ) (z : H), (∀ g, T g z = χ g • z) → c * ‖z‖ ^ 2 ≤ ∑ i, ‖L i z‖ ^ 2)
    (z : H) : c * ‖z‖ ^ 2 ≤ ∑ i, ‖L i z‖ ^ 2 := by
  classical
  set zc : AddChar Γ ℂ → H := fun χ => isoProj T χ z with hzc
  have hev : ∀ χ g, T g (zc χ) = χ g • zc χ := fun χ g => isoProj_eigen T hTadd χ z g
  have hsum : ∑ χ, zc χ = z := sum_isoProj T hT0 z
  have h1 : ‖z‖ ^ 2 = ∑ χ, ‖zc χ‖ ^ 2 := by
    have := inner_sum_eigen T hTunit zc zc hev hev
    rw [hsum] at this
    have h2 : (⟪z, z⟫ : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h3 : ∀ χ, (⟪zc χ, zc χ⟫ : ℂ) = ((‖zc χ‖ ^ 2 : ℝ) : ℂ) := fun χ => by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h2] at this
    simp only [h3] at this
    exact_mod_cast this
  have h4 : ∀ i, ‖L i z‖ ^ 2 = ∑ χ, ‖L i (zc χ)‖ ^ 2 := by
    intro i
    have hLev : ∀ χ g, U i g (L i (zc χ)) = χ g • L i (zc χ) := fun χ g => by
      rw [← hL, hev, map_smul]
    have := inner_sum_eigen (U i) (hUunit i) (fun χ => L i (zc χ)) (fun χ => L i (zc χ)) hLev hLev
    rw [← map_sum, hsum] at this
    have h2 : (⟪L i z, L i z⟫ : ℂ) = ((‖L i z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h3 : ∀ χ, (⟪L i (zc χ), L i (zc χ)⟫ : ℂ) = ((‖L i (zc χ)‖ ^ 2 : ℝ) : ℂ) := fun χ => by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h2] at this
    simp only [h3] at this
    exact_mod_cast this
  calc c * ‖z‖ ^ 2 = ∑ χ, c * ‖zc χ‖ ^ 2 := by rw [h1, Finset.mul_sum]
    _ ≤ ∑ χ, ∑ i, ‖L i (zc χ)‖ ^ 2 := Finset.sum_le_sum (fun χ _ => hc χ (zc χ) (hev χ))
    _ = ∑ i, ∑ χ, ‖L i (zc χ)‖ ^ 2 := Finset.sum_comm
    _ = ∑ i, ‖L i z‖ ^ 2 := Finset.sum_congr rfl (fun i _ => (h4 i).symm)

end BlochSum


section NormSplit
variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem norm_split (T : Γ → H →ₗ[ℂ] H) (zc : AddChar Γ ℂ → H) {z : H}
    (hev : ∀ χ g, T g (zc χ) = χ g • zc χ) (hsum : ∑ χ, zc χ = z)
    (U : Γ → K →ₗ[ℂ] K) (hU : ∀ g x y, ⟪U g x, U g y⟫ = ⟪x, y⟫) (L : H →ₗ[ℂ] K)
    (hL : ∀ g z, L (T g z) = U g (L z)) : ‖L z‖ ^ 2 = ∑ χ, ‖L (zc χ)‖ ^ 2 := by
  have hLev : ∀ χ g, U g (L (zc χ)) = χ g • L (zc χ) := fun χ g => by
    rw [← hL, hev, map_smul]
  have := inner_sum_eigen U hU (fun χ => L (zc χ)) (fun χ => L (zc χ)) hLev hLev
  rw [← map_sum, hsum] at this
  have h2 : (⟪L z, L z⟫ : ℂ) = ((‖L z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have h3 : ∀ χ, (⟪L (zc χ), L (zc χ)⟫ : ℂ) = ((‖L (zc χ)‖ ^ 2 : ℝ) : ℂ) := fun χ => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h2] at this
  simp only [h3] at this
  exact_mod_cast this

end NormSplit

section BlochThree
variable {Γ : Type*} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
  {H K₁ K₂ K₃ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂]
  [NormedAddCommGroup K₃] [InnerProductSpace ℂ K₃]

/-- **Bloch splitting for three equivariant maps** (explicit targets). -/
theorem bloch_coercive_three (T : Γ → H →ₗ[ℂ] H) (hT0 : T 0 = LinearMap.id)
    (hTadd : ∀ g h, T (g + h) = (T g).comp (T h))
    (hTunit : ∀ g x y, ⟪T g x, T g y⟫ = ⟪x, y⟫)
    (U₁ : Γ → K₁ →ₗ[ℂ] K₁) (hU₁ : ∀ g x y, ⟪U₁ g x, U₁ g y⟫ = ⟪x, y⟫)
    (U₂ : Γ → K₂ →ₗ[ℂ] K₂) (hU₂ : ∀ g x y, ⟪U₂ g x, U₂ g y⟫ = ⟪x, y⟫)
    (U₃ : Γ → K₃ →ₗ[ℂ] K₃) (hU₃ : ∀ g x y, ⟪U₃ g x, U₃ g y⟫ = ⟪x, y⟫)
    (L₁ : H →ₗ[ℂ] K₁) (L₂ : H →ₗ[ℂ] K₂) (L₃ : H →ₗ[ℂ] K₃)
    (h₁ : ∀ g z, L₁ (T g z) = U₁ g (L₁ z)) (h₂ : ∀ g z, L₂ (T g z) = U₂ g (L₂ z))
    (h₃ : ∀ g z, L₃ (T g z) = U₃ g (L₃ z)) (c : ℝ)
    (hc : ∀ (χ : AddChar Γ ℂ) (z : H), (∀ g, T g z = χ g • z) →
      c * ‖z‖ ^ 2 ≤ ‖L₁ z‖ ^ 2 + ‖L₂ z‖ ^ 2 + ‖L₃ z‖ ^ 2)
    (z : H) : c * ‖z‖ ^ 2 ≤ ‖L₁ z‖ ^ 2 + ‖L₂ z‖ ^ 2 + ‖L₃ z‖ ^ 2 := by
  classical
  set zc : AddChar Γ ℂ → H := fun χ => isoProj T χ z with hzc
  have hev : ∀ χ g, T g (zc χ) = χ g • zc χ := fun χ g => isoProj_eigen T hTadd χ z g
  have hsum : ∑ χ, zc χ = z := sum_isoProj T hT0 z
  have h1 : ‖z‖ ^ 2 = ∑ χ, ‖zc χ‖ ^ 2 := by
    have := inner_sum_eigen T hTunit zc zc hev hev
    rw [hsum] at this
    have h2 : (⟪z, z⟫ : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h3 : ∀ χ, (⟪zc χ, zc χ⟫ : ℂ) = ((‖zc χ‖ ^ 2 : ℝ) : ℂ) := fun χ => by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h2] at this
    simp only [h3] at this
    exact_mod_cast this
  have e1 : ‖L₁ z‖ ^ 2 = ∑ χ, ‖L₁ (zc χ)‖ ^ 2 := norm_split T zc hev hsum U₁ hU₁ L₁ h₁
  have e2 : ‖L₂ z‖ ^ 2 = ∑ χ, ‖L₂ (zc χ)‖ ^ 2 := norm_split T zc hev hsum U₂ hU₂ L₂ h₂
  have e3 : ‖L₃ z‖ ^ 2 = ∑ χ, ‖L₃ (zc χ)‖ ^ 2 := norm_split T zc hev hsum U₃ hU₃ L₃ h₃
  rw [e1, e2, e3]
  calc c * ‖z‖ ^ 2 = ∑ χ, c * ‖zc χ‖ ^ 2 := by rw [h1, Finset.mul_sum]
    _ ≤ ∑ χ, (‖L₁ (zc χ)‖ ^ 2 + ‖L₂ (zc χ)‖ ^ 2 + ‖L₃ (zc χ)‖ ^ 2) :=
        Finset.sum_le_sum (fun χ _ => hc χ (zc χ) (hev χ))
    _ = _ := by simp only [Finset.sum_add_distrib]

end BlochThree

#print axioms AdalyFormal.FlatCoercivity.bloch_coercive_three

end AdalyFormal.FlatCoercivity

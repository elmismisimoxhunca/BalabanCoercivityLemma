import TL1e

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice inBlock mem_blockOf mem_CoarseLattice)

theorem inBlock_iff_div {L : PeriodicLatticeExtent} (ell : ℕ) (hell : 0 < ell) (y x : PeriodicLatticeSite L)
    (hy : ∀ μ : Fin 3, (y μ).val % ell = 0) :
    inBlock y ell x ↔ ∀ μ : Fin 3, (x μ).val / ell = (y μ).val / ell := by
  constructor
  · intro h μ
    obtain ⟨h1, h2⟩ := h μ
    have hq := Nat.div_add_mod (y μ).val ell
    rw [hy μ, add_zero] at hq
    have hq' : (y μ).val / ell * ell = (y μ).val := by rw [mul_comm]; exact hq
    apply Nat.div_eq_of_lt_le
    · rw [hq']; exact h1
    · rw [Nat.succ_mul, hq']; exact h2
  · intro h μ
    have hq := Nat.div_add_mod (y μ).val ell
    rw [hy μ, add_zero] at hq
    have h' := h μ
    have h1 := Nat.div_add_mod (x μ).val ell
    have h2 := Nat.mod_lt (x μ).val hell
    rw [h'] at h1
    constructor <;> omega

theorem lamBlockSum_lift {Lut Lu : PeriodicLatticeExtent} (hu : Covers Lut Lu) {ell : ℕ} (hell : 0 < ell)
    (hdiv : ∀ μ : Fin 3, ell ∣ Lu μ + 1) {Lam : Set (PeriodicLatticeSite Lu)}
    (hB : LamBlockSum ell Lam) : LamBlockSum ell (projS hu ⁻¹' Lam) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hB _ hx
  have hdiv' : ∀ μ : Fin 3, ell ∣ Lut μ + 1 := fun μ => (hdiv μ).trans (hu μ)
  have hlt : ∀ μ : Fin 3, ell * ((x μ).val / ell) < Lut μ + 1 := fun μ =>
    lt_of_le_of_lt (Nat.mul_div_le _ _) (x μ).isLt
  let yt : PeriodicLatticeSite Lut := fun μ => ⟨ell * ((x μ).val / ell), hlt μ⟩
  have hyt : ∀ μ : Fin 3, (yt μ).val % ell = 0 := fun μ => by
    show ell * ((x μ).val / ell) % ell = 0
    exact Nat.mul_mod_right _ _
  have hy1 := mem_CoarseLattice.mp hy.1
  have hxy' := (inBlock_iff_div ell hell y _ hy1).mp (mem_blockOf.mp hxy)
  refine ⟨yt, ⟨mem_CoarseLattice.mpr hyt, ?_⟩, mem_blockOf.mpr ?_⟩
  · intro x' hx'
    have hx'' := (inBlock_iff_div ell hell yt x' hyt).mp (mem_blockOf.mp hx')
    have hproj : ∀ μ : Fin 3, (projS hu x' μ).val / ell = (y μ).val / ell := by
      intro μ
      have e1 : (x' μ).val / ell = (x μ).val / ell := by
        rw [hx'' μ]; show ell * ((x μ).val / ell) / ell = _
        exact Nat.mul_div_cancel_left _ hell
      rw [← hxy' μ]
      simp only [projS_val]
      exact div_mod_block ell (Lu μ + 1) _ _ (hdiv μ) e1
    have : projS hu x' ∈ blockOf y ell := mem_blockOf.mpr ((inBlock_iff_div ell hell y _ hy1).mpr hproj)
    exact hy.2 _ this
  · intro μ
    show ell * ((x μ).val / ell) ≤ (x μ).val ∧ (x μ).val < ell * ((x μ).val / ell) + ell
    have h1 := Nat.div_add_mod (x μ).val ell
    have h2 := Nat.mod_lt (x μ).val hell
    constructor <;> omega

end AdalyFormal.Thin

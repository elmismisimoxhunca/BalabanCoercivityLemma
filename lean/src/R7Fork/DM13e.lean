import R7Fork.DM13d

/-!
# DM13e -- anchors of adjacent sites; the hypothesis package of the adjacency induction.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section anchors
variable {L : PeriodicLatticeExtent}

theorem anc_one (x : PeriodicLatticeSite L) : anc 1 x = x := by
  funext ρ; apply Fin.ext; rw [anc_val]; simp

theorem stBlock_zero {ell : ℕ} (S : Tower L) {x : PeriodicLatticeSite L} (h : lev S x = 0) :
    stBlock ell S x = {x} := by
  unfold stBlock
  rw [h, pow_zero, anc_one]
  exact AdalyFormal.Balaban.FourierFaithfulU1.blockOf_one x

theorem meanB_zero {ell : ℕ} (S : Tower L) (Θ : PeriodicLatticeSite L → SuTwo) {x : PeriodicLatticeSite L}
    (h : lev S x = 0) : meanB ell S Θ x = Θ x := by
  unfold meanB
  rw [stBlock_zero S h, h]
  simp

/-- adjacent sites: their `n`-anchors coincide (and the bond does not wrap), or the anchors are adjacent blocks with the wrap of the
anchor bond equal to the wrap of the site bond -/
theorem anchor_adj {n : ℕ} (hn : 0 < n) (hN : ∀ ν, 1 ≤ L ν) (hdvd : ∀ ν, n ∣ L ν + 1) (hbig : ∀ ν, 2 * n ≤ L ν + 1)
    (u : PeriodicLatticeSite L) (μ : Fin 3) :
    (anc n (periodicLatticeShift u μ) = anc n u ∧ (u μ).val + 1 ≠ L μ + 1) ∨
    (anc n (periodicLatticeShift u μ) = coarseShift (anc n u) n μ ∧
      (((anc n u) μ).val + n = L μ + 1 ↔ (u μ).val + 1 = L μ + 1)) := by
  have hv := shift_val_same hN u μ
  have hne : ∀ ν, ν ≠ μ → anc n (periodicLatticeShift u μ) ν = anc n u ν := by
    intro ν h
    apply Fin.ext
    rw [anc_val, anc_val, shift_val_ne u h]
  obtain ⟨b, hb⟩ := hdvd μ
  have ha := (u μ).isLt
  by_cases hw : (u μ).val + 1 = L μ + 1
  · -- wrap
    right
    have hv0 : ((periodicLatticeShift u μ) μ).val = 0 := by rw [hv, hw, Nat.mod_self]
    have hpu : ((anc n u) μ).val + n = L μ + 1 := by
      rw [anc_val]
      -- u μ = L μ = n*b - 1
      have h1 : (u μ).val = n * b - 1 := by omega
      have hb1 : 1 ≤ b := by
        by_contra hb0
        have : b = 0 := by omega
        rw [this] at hb; omega
      have h2 : (u μ).val / n = b - 1 := by
        apply Nat.div_eq_of_lt_le
        · have : (b - 1) * n = n * b - n := by rw [Nat.sub_mul, one_mul, mul_comm]
          rw [this]; omega
        · have : (b - 1 + 1) * n = n * b := by rw [Nat.sub_add_cancel hb1, mul_comm]
          rw [this]; omega
      rw [h2]
      have : n * (b - 1) + n = n * b := by
        rw [Nat.mul_sub, mul_one, Nat.sub_add_cancel]; exact Nat.le_mul_of_pos_right n hb1
      omega
    refine ⟨?_, ⟨fun _ => hw, fun _ => hpu⟩⟩
    funext ν
    apply Fin.ext
    by_cases h : ν = μ
    · subst h
      rw [anc_val, hv0, coarseShift_val_eq, hpu, Nat.mod_self]
      simp
    · rw [coarseShift_apply_ne _ _ _ _ h, hne ν h]
  · -- no wrap
    have hlt : (u μ).val + 1 < L μ + 1 := by omega
    have hv1 : ((periodicLatticeShift u μ) μ).val = (u μ).val + 1 := by rw [hv, Nat.mod_eq_of_lt hlt]
    by_cases hs : ((u μ).val + 1) / n = (u μ).val / n
    · left
      refine ⟨?_, hw⟩
      funext ν
      apply Fin.ext
      by_cases h : ν = μ
      · subst h; rw [anc_val, anc_val, hv1, hs]
      · rw [hne ν h]
    · right
      have hs2 : ((u μ).val + 1) / n = (u μ).val / n + 1 := by
        have h1 : (u μ).val / n ≤ ((u μ).val + 1) / n := Nat.div_le_div_right (by omega)
        have h2 : ((u μ).val + 1) / n ≤ (u μ).val / n + 1 := by
          rw [Nat.div_le_iff_le_mul_add_pred hn]
          have := Nat.div_add_mod (u μ).val n
          have := Nat.mod_lt (u μ).val hn
          nlinarith
        omega
      have hpu : ((anc n u) μ).val + n ≠ L μ + 1 := by
        rw [anc_val]
        have : n * ((u μ).val / n + 1) ≤ (u μ).val + 1 := by
          have := Nat.div_mul_le_self ((u μ).val + 1) n
          rw [hs2] at this; rw [mul_comm]; exact this
        rw [mul_add, mul_one] at this
        omega
      refine ⟨?_, ⟨fun h => absurd h hpu, fun h => absurd h hw⟩⟩
      funext ν
      apply Fin.ext
      by_cases h : ν = μ
      · subst h
        rw [coarseShift_val_eq, anc_val, anc_val, hv1, hs2]
        have : n * ((u ν).val / n + 1) < L ν + 1 := by
          have := Nat.div_mul_le_self ((u ν).val + 1) n
          rw [hs2] at this
          rw [mul_comm]; omega
        rw [show n * ((u ν).val / n) + n = n * ((u ν).val / n + 1) by ring, Nat.mod_eq_of_lt this]
      · rw [coarseShift_apply_ne _ _ _ _ h, hne ν h]

end anchors

end AdalyFormal.DirichletMono

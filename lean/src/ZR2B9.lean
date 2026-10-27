import ZR2D

/-!
# R2B9 -- MULTI-STRATUM tower (k = 1, two nonempty strata) on the 120-site torus, ell = 2, M = 1,
F = 10, R = 12:  Ω₁ = {20 ≤ x₀ < 100}, Ω₀ = {8 ≤ x₀ < 112} (= Ω₁ widened by R M = 12), Ω₂ = ∅.
Admissible (all six clauses), covers Ω₀ by index-0 cubes (side 10) on the shell and index-1 cubes
(side 20, even corners) in Ω₁; Λ = slab at unit distance ≥ 20 from Λ₁ᶜ.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

def OmA (L : PeriodicLatticeExtent) : Set (PeriodicLatticeSite L) :=
  {x | 8 ≤ (x 0).val ∧ (x 0).val < 112}
def OmB (L : PeriodicLatticeExtent) : Set (PeriodicLatticeSite L) :=
  {x | 20 ≤ (x 0).val ∧ (x 0).val < 100}
def TT (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then OmA L else if j = 1 then OmB L else ∅⟩

theorem pcd_far120 (N a b : ℕ) (hN : N = 120) (ha : a < 8 ∨ 112 ≤ a) (ha2 : a < 120)
    (hb : 20 ≤ b ∧ b < 100) : 12 < pcd N a b := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem pcd_near120 (N a b : ℕ) (hN : N = 120) (ha : a < 120) (hb : 20 ≤ b ∧ b < 100)
    (h : pcd N a b ≤ 12) : 8 ≤ a ∧ a < 112 := by
  subst hN; unfold pcd at h; split_ifs at h <;> omega

theorem pcd_clamp120 (N a : ℕ) (hN : N = 120) (ha : 8 ≤ a ∧ a < 112) :
    pcd N a (if a < 20 then 20 else if a < 100 then a else 99) ≤ 12 := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem pcd_self (N a : ℕ) : pcd N a a = 0 := by unfold pcd; simp

theorem TT_admissible {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = 120) :
    Admissible 2 1 12 1 (TT L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst h0; simp only [TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), if_true, OmA, OmB,
        Set.mem_setOf_eq] at hx ⊢
      omega
    · by_cases h1 : j = 1
      · subst h1; simp [TT] at hx
      · have : j + 1 ≠ 0 := by omega
        have : j + 1 ≠ 1 := by omega
        simp [TT, *] at hx
  · intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp [TT, h0, h1]
  · intro j hj μ
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [bigSide, hN μ] <;> omega
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · intro x hx y hy
      simp only [TT, if_true, OmA, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
    · intro x hx y hy
      simp only [TT, if_neg (by decide : (1 : ℕ) ≠ 0), if_true, OmB, Set.mem_setOf_eq] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp only [TT, if_true, if_neg (by decide : (0 + 1 : ℕ) ≠ 0), OmA, OmB, Set.mem_setOf_eq,
        not_and_or, not_le, not_lt] at hx hy
      have hxl : (x 0).val < 120 := by have := (x 0).isLt; have := hN 0; omega
      have hlt : 12 < pcd (L 0 + 1) (x 0).val (y 0).val :=
        pcd_far120 _ _ _ (hN 0) hx hxl hy
      unfold pdist
      show 12 * bigSide 1 2 0 < _
      simp only [bigSide, pow_zero, mul_one]
      exact lt_of_lt_of_le hlt
        (Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
    · simp [TT] at hy
  · intro x
    simp only [TT, if_true, if_neg (by decide : (1 : ℕ) ≠ 0), OmA, OmB, Set.mem_setOf_eq]
    constructor
    · intro hx
      have hx120 : (x 0).val < 120 := by have := (x 0).isLt; have := hN 0; omega
      let v : ℕ := if (x 0).val < 20 then 20 else if (x 0).val < 100 then (x 0).val else 99
      have hv : v < L 0 + 1 := by have := hN 0; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self]
          have := pcd_clamp120 (L 0 + 1) (x 0).val (hN 0) hx
          simpa [v, bigSide] using this
        · intro μ _ h
          rw [Function.update_of_ne h, pcd_self]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      have hz0 : (z 0).val = (x 0).val := by simpa using hz 0
      have hlt := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have h12 : pcd (L 0 + 1) (z 0).val (y 0).val ≤ 12 := by
        have := le_trans hlt hd
        simpa [bigSide] using this
      rw [hz0] at h12
      have hx120 : (x 0).val < 120 := by have := (x 0).isLt; have := hN 0; omega
      exact pcd_near120 _ _ _ (hN 0) hx120 hy h12

#print axioms TT_admissible

end AdalyFormal.StatementLane2

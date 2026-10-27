import GE2
import GV3

/-!
# GE3 -- the half-slab cubes at a grid vertex (m2_gluegeo, 2026-10-15)

`BoxS s` = the eight `s`-blocks around a grid vertex `v` (coordinates `p_i in [-s, s)`, sites `iota v p`);
`HSlab s sigma b` = the four of them on the `b`-side of the plane `p_sigma = 0`.
`slab_cube`: if every site of the box is within `(R - 18) b_m` of a point of `Omega_{m+1}`, `s = b_m`, `v` on the `s`-grid and
`CoversOm0p ell M 12 k S`, then ONE class cube contains `iota v '' HSlab s sigma b`.
(the plaquette on the grid edge through `v` in direction `sigma` has its four sites in the four blocks; the cover hypothesis puts
that plaquette in a cube; cubes near `Omega_{m+1}` are unions of `b_m`-blocks (GE2).)  No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.M1 (om_anti)

variable {L : PeriodicLatticeExtent}

/-- the eight `s`-blocks around a grid vertex, in coordinates. -/
def BoxS (s : ℕ) : Set Z3 := {p | ∀ i, -(s : ℤ) ≤ p i ∧ p i < s}

/-- the four blocks on one side of the plane `p_sigma = 0`. -/
def HSlab (s : ℕ) (σ : Fin 3) (b : Bool) : Set Z3 := {p | p ∈ BoxS s ∧ hsP σ b p}

theorem blk_idx_nonneg {s : ℕ} (hs : 0 < s) {a : ℤ} (h0 : 0 ≤ a) (h1 : a < s) : a / (s : ℤ) = 0 :=
  Int.ediv_eq_zero_of_lt h0 h1

theorem blk_idx_neg {s : ℕ} (hs : 0 < s) {a : ℤ} (h0 : -(s : ℤ) ≤ a) (h1 : a < 0) : a / (s : ℤ) = -1 := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have : a = (s : ℤ) * (-1) + (a + s) := by ring
  rw [this, blk_div (s : ℤ) (-1) (a + s) hs' (by linarith) (by linarith)]

theorem blk_m1 {s : ℕ} (hs : 0 < s) : (-1 : ℤ) / (s : ℤ) = -1 :=
  blk_idx_neg hs (by have : (1 : ℤ) ≤ s := by exact_mod_cast hs
                     linarith) (by norm_num)

theorem om_le_zero {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (m : ℕ) : S.Om m ⊆ S.Om 0 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; exact fun _ hx => hx
  · exact (om_anti hS h).trans (hS.1 0)

/-- every site of the box is in `Ω_m` when it is within `R b_m` of a point of `Ω_{m+1}`. -/
theorem mem_om_of_near {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) {m : ℕ} (hmk : m ≤ k)
    {x x0 : PeriodicLatticeSite L} (hx0 : x0 ∈ S.Om (m + 1)) (hd : pdist x x0 < R * bigSide M ell m) :
    x ∈ S.Om m := by
  by_contra hc
  have := hS.2.2.2.2.1 m hmk x hc x0 hx0
  omega

/-- block-closed cube + four sites around the edge ⇒ the half-slab. -/
theorem slab_sub {s : ℕ} (hs : 0 < s) {C : Set (PeriodicLatticeSite L)} (hC : BlockClosed s C)
    {v : PeriodicLatticeSite L} (hv : ∀ μ, (v μ).val % s = 0) (hsN : ∀ μ, s ∣ L μ + 1)
    {μ ν σ : Fin 3} (hσμ : σ ≠ μ) (hσν : σ ≠ ν) (hμν : μ ≠ ν) {q0 : Z3} (hq0μ : q0 μ = -1) (hq0ν : q0 ν = -1)
    (hq0σ : q0 σ = 0 ∨ q0 σ = -1)
    (h00 : iota v q0 ∈ C) (h10 : iota v (q0 + ev μ) ∈ C) (h01 : iota v (q0 + ev ν) ∈ C)
    (h11 : iota v (q0 + ev μ + ev ν) ∈ C) {p : Z3} (hpμ : -(s : ℤ) ≤ p μ ∧ p μ < s)
    (hpν : -(s : ℤ) ≤ p ν ∧ p ν < s) (hpσ : p σ / (s : ℤ) = q0 σ / (s : ℤ)) : iota v p ∈ C := by
  have hqσ : q0 σ / (s : ℤ) = q0 σ := by
    rcases hq0σ with h | h
    · rw [h]; exact blk_idx_nonneg hs le_rfl (by exact_mod_cast hs)
    · rw [h]; exact blk_m1 hs
  -- the representative `q*`
  obtain ⟨qs, hqs⟩ : ∃ qs : Z3, qs = q0 + (if 0 ≤ p μ then ev μ else 0) + (if 0 ≤ p ν then ev ν else 0) := ⟨_, rfl⟩
  have hmem : iota v qs ∈ C := by
    by_cases a : 0 ≤ p μ <;> by_cases b : 0 ≤ p ν
    · rw [hqs, if_pos a, if_pos b]; exact h11
    · rw [hqs, if_pos a, if_neg b, add_zero]; exact h10
    · rw [hqs, if_neg a, if_pos b, add_zero]; exact h01
    · rw [hqs, if_neg a, if_neg b, add_zero, add_zero]; exact h00
  have hdiv : ∀ i, p i / (s : ℤ) = qs i / (s : ℤ) := by
    intro i
    by_cases hi : i = μ
    · subst hi
      have e1 : qs i = (if 0 ≤ p i then 0 else -1) := by
        have : i ≠ ν := hμν
        rw [hqs]
        by_cases a : 0 ≤ p i <;> by_cases b : 0 ≤ p ν <;> simp [ev, hq0μ, this, a, b]
      rw [e1]
      by_cases a : 0 ≤ p i
      · rw [if_pos a, blk_idx_nonneg hs a hpμ.2]; simp
      · rw [if_neg a, blk_idx_neg hs hpμ.1 (by omega)]
        exact (blk_m1 hs).symm
    · by_cases hj : i = ν
      · subst hj
        have e1 : qs i = (if 0 ≤ p i then 0 else -1) := by
          have : i ≠ μ := hi
          rw [hqs]
          by_cases a : 0 ≤ p i <;> by_cases b : 0 ≤ p μ <;> simp [ev, hq0ν, this, a, b]
        rw [e1]
        by_cases a : 0 ≤ p i
        · rw [if_pos a, blk_idx_nonneg hs a hpν.2]; simp
        · rw [if_neg a, blk_idx_neg hs hpν.1 (by omega)]
          exact (blk_m1 hs).symm
      · have hiσ : i = σ := by
          fin_cases i <;> fin_cases σ <;> fin_cases μ <;> fin_cases ν <;> simp_all
        subst hiσ
        have e1 : qs i = q0 i := by
          rw [hqs]
          by_cases a : 0 ≤ p μ <;> by_cases b : 0 ≤ p ν <;> simp [ev, a, b, hσμ, hσν]
        rw [e1]; exact hpσ
  exact hC _ hmem _ (fun μ' => iota_val_div v s hs hv hsN p qs hdiv μ')

end AdalyFormal.M2GlueGeo

import ZT5C
import ZXR2Wire3

/-!
# MC1 -- geometry lemmas for the M0 corollary, GENERAL torus (builder: m0_corollary_20261010)
`fullTower_admissible`, `univ_lambdaOK2`, `fullTower_coversp` (cube factor 12 .. any c >= 2); standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2

theorem fullTower_eq_Sk (ell k : ℕ) (Lu : PeriodicLatticeExtent) :
    fullTower ell k Lu = Sk (scaleUp ell k Lu) k := rfl

theorem fullTower_admissible (ell M R k : ℕ) (hell : 0 < ell) (hk : 1 ≤ k) (Lu : PeriodicLatticeExtent)
    (hM : ∀ μ : Fin 3, M ∣ Lu μ + 1) : Admissible ell M R k (fullTower ell k Lu) := by
  rw [fullTower_eq_Sk]
  refine SkG_admissible ell M R k hk ?_
  intro j hj μ
  rw [scaleUp_succ ell k Lu hell μ]
  have h1 : ell ^ j ∣ ell ^ k := pow_dvd_pow ell hj
  rw [mul_comm M]
  exact (Nat.mul_dvd_mul h1 (hM μ)).trans (by rw [mul_comm])

theorem univ_lambdaOK2 (ell M R k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) :
    LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell M R k (fullTower ell k Lu) Set.univ := by
  rw [fullTower_eq_Sk]
  exact ⟨SkG_lambdaOK ell M R k (fun μ => scaleUp_succ ell k Lu hell μ) hell, lamBlockSum_univ ell hell⟩

/-! ## the cell lemma -/

theorem cell_aux (m s q r δ : ℕ) (hs : 0 < s) (hr : r < s) (hq : q < m) (hδ : δ ≤ 1) :
    (((s * q + r + δ) % (s * m) + s * m - s * q) % (s * m)) < 2 * s := by
  have hqm : s * (q + 1) ≤ s * m := Nat.mul_le_mul_left s hq
  rw [Nat.mul_add, Nat.mul_one] at hqm
  have ha : s * q + r < s * m := by omega
  interval_cases δ
  · rw [Nat.add_zero, Nat.mod_eq_of_lt ha]
    have : s * q + r + s * m - s * q = r + s * m := by omega
    rw [this, Nat.add_mod_right]
    calc r % (s * m) ≤ r := Nat.mod_le _ _
      _ < 2 * s := by omega
  · by_cases hw : s * q + r + 1 < s * m
    · rw [Nat.mod_eq_of_lt hw]
      have : s * q + r + 1 + s * m - s * q = (r + 1) + s * m := by omega
      rw [this, Nat.add_mod_right]
      calc (r + 1) % (s * m) ≤ r + 1 := Nat.mod_le _ _
        _ < 2 * s := by omega
    · have hw' : s * q + r + 1 = s * m := by omega
      rw [hw', Nat.mod_self]
      have h4 : s * m = s * q + s := by omega
      have : 0 + s * m - s * q = s := by omega
      rw [this]
      calc s % (s * m) ≤ s := Nat.mod_le _ _
        _ < 2 * s := by omega

theorem cell_lemma (m s a δ : ℕ) (hs : 0 < s) (ha : a < s * m) (hδ : δ ≤ 1) :
    (((a + δ) % (s * m) + s * m - a / s * s) % (s * m)) < 2 * s := by
  have hq : a / s < m := by
    rw [Nat.div_lt_iff_lt_mul hs]; linarith [mul_comm s m]
  have hdm : s * (a / s) + a % s = a := Nat.div_add_mod a s
  have hr : a % s < s := Nat.mod_lt _ hs
  have h := cell_aux m s (a / s) (a % s) δ hs hr hq hδ
  rw [hdm] at h
  rw [mul_comm (a / s) s]
  exact h

theorem shift_coord {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (μ ρ : Fin 3) :
    ((periodicLatticeShift y μ) ρ).val = if ρ = μ then ((y ρ).val + 1) % (L ρ + 1) else (y ρ).val := by
  unfold periodicLatticeShift
  by_cases h : ρ = μ
  · subst h
    rw [Function.update_self, Fin.val_add, Fin.val_one', if_pos rfl, Nat.add_mod_mod]
  · rw [Function.update_of_ne h, if_neg h]

/-- a site is `near` the base site `x` when each coordinate is `x ρ + δ` with `δ ∈ {0,1}` (periodically) -/
def Near {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) : Prop :=
  ∀ ρ : Fin 3, ∃ δ : ℕ, δ ≤ 1 ∧ (y ρ).val = ((x ρ).val + δ) % (L ρ + 1)

theorem near_self {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : Near x x :=
  fun ρ => ⟨0, by omega, by simp [Nat.mod_eq_of_lt (x ρ).isLt]⟩

theorem near_shift_first {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Near x (periodicLatticeShift x μ) := by
  intro ρ
  rw [shift_coord]
  by_cases h : ρ = μ
  · exact ⟨1, le_rfl, by rw [if_pos h]⟩
  · exact ⟨0, by omega, by rw [if_neg h]; simp [Nat.mod_eq_of_lt (x ρ).isLt]⟩

theorem near_shift_second {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ ν : Fin 3) (hne : μ ≠ ν) :
    Near x (periodicLatticeShift (periodicLatticeShift x μ) ν) := by
  intro ρ
  rw [shift_coord, shift_coord]
  by_cases h1 : ρ = ν
  · have h2 : ρ ≠ μ := fun h => hne (h.symm.trans h1)
    refine ⟨1, le_rfl, ?_⟩
    rw [if_pos h1, if_neg h2]
  · by_cases h2 : ρ = μ
    · refine ⟨1, le_rfl, ?_⟩
      rw [if_neg h1, if_pos h2]
    · exact ⟨0, by omega, by rw [if_neg h1, if_neg h2]; simp [Nat.mod_eq_of_lt (x ρ).isLt]⟩

/-- the grid corner below `x` -/
def gridBelow {L : PeriodicLatticeExtent} (s : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun ρ => ⟨(x ρ).val / s * s, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x ρ).isLt⟩

theorem near_mem_box {L : PeriodicLatticeExtent} (s c : ℕ) (hs : 0 < s) (hc : 2 ≤ c)
    (hd : ∀ ρ : Fin 3, s ∣ L ρ + 1) (x y : PeriodicLatticeSite L) (hy : Near x y) :
    y ∈ siteBox (gridBelow s x) (c * s) := by
  intro ρ
  obtain ⟨δ, hδ, hv⟩ := hy ρ
  obtain ⟨m, hm⟩ := hd ρ
  have hlt : (x ρ).val < s * m := by rw [← hm]; exact (x ρ).isLt
  have h := cell_lemma m s (x ρ).val δ hs hlt hδ
  simp only [gridBelow]
  rw [← hm] at h
  rw [hv]
  calc _ < 2 * s := h
    _ ≤ c * s := Nat.mul_le_mul_right s hc

end AdalyFormal.M0Corollary

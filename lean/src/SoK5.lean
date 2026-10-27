import SoK4
import NuK5

/-!
# SoK5 -- the abelian one-step map on the pattern for general `ell`: `Rsig` of the pattern vanishes at every coarse bond (lane sites_only_20261019)

* `sum_win_one`        : among `ell` consecutive integers exactly one is `≡ ell - 1 (mod ell)`.
* `pathAng_pat`        : the line integral of the pattern along `ell` direction-1 steps is `ell (-1/ell^2)[x₀ = uE+1] + [x₀ = uE][x₂ ≡ ell-1]`.
* `Rsig_pat_zero`      : the block average of that over an aligned `ell`-block is `0` (`-ell + ell`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NcwdhTwo
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem sum_win_one (ell : ℕ) (hell : 0 < ell) (a : ℕ) :
    ∑ i ∈ range ell, (if (a + i) % ell = ell - 1 then (1 : ℝ) else 0) = 1 := by
  have hr : a % ell < ell := Nat.mod_lt _ hell
  rw [Finset.sum_eq_single (ell - 1 - a % ell)]
  · have : (a + (ell - 1 - a % ell)) % ell = ell - 1 := by
      have e : a + (ell - 1 - a % ell) = ell * (a / ell) + (ell - 1) := by
        have := Nat.div_add_mod a ell; omega
      rw [e, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [if_pos this]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [if_neg]
    intro h
    apply hne
    have h2 : (a % ell + i) % ell = ell - 1 := by
      rw [← h, Nat.add_mod a i ell, Nat.add_mod (a % ell) i ell, Nat.mod_mod]
    rcases Nat.lt_or_ge (a % ell + i) ell with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h2; omega
    · rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h2; omega
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- the coefficient as a function of the three coordinates. -/
noncomputable def bpat (ell uE v0 v1 v2 : ℕ) : ℝ :=
  (if v0 = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0) +
    (if v0 = uE then (if v1 % ell = ell - 1 ∧ v2 % ell = ell - 1 then (1 : ℝ) else 0) else 0)

theorem betaPat_eq_bpat (ell uE : ℕ) (x : PeriodicLatticeSite L) : betaPat ell uE x = bpat ell uE (x 0).val (x 1).val (x 2).val := rfl

theorem bpat_congr {ell uE v0 v1 w1 v2 : ℕ} (h : v1 % ell = w1 % ell) : bpat ell uE v0 v1 v2 = bpat ell uE v0 w1 v2 := by
  unfold bpat; rw [h]

/-- closed form of the line integral over `n` direction-1 steps (stride 1). -/
theorem pathAng_pat_aux (ell uE : ℕ) (hN1 : ell ∣ L 1 + 1) (n : ℕ) :
    ∀ x : PeriodicLatticeSite L, pathAngG 1 (thetaOf (Bpatf (L := L) ell uE)) x (List.replicate n 1) =
      ∑ i ∈ range n, bpat ell uE (x 0).val ((x 1).val + i) (x 2).val := by
  induction n with
  | zero => intro x; simp [pathAngG]
  | succ n ih =>
    intro x
    rw [List.replicate_succ, pathAngG, ih, Finset.sum_range_succ' _ n, thetaOf_Bpatf, betaPat_eq_bpat]
    have c0 : (coarseShift x 1 1 0) = x 0 := coarseShift_apply_ne x 1 1 0 (by decide)
    have c2 : (coarseShift x 1 1 2) = x 2 := coarseShift_apply_ne x 1 1 2 (by decide)
    have c1 : ((coarseShift x 1 1) 1).val = ((x 1).val + 1) % (L 1 + 1) := coarseShift_val_eq x 1 1
    rw [c0, c2, c1, add_comm]
    simp only [add_zero]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply bpat_congr
    rw [Nat.add_mod (((x 1).val + 1) % (L 1 + 1)) i ell, Nat.mod_mod_of_dvd _ hN1, ← Nat.add_mod, add_assoc, Nat.add_comm 1 i]

/-- the line integral of the pattern along `ell` direction-1 steps. -/
theorem pathAng_pat (ell uE : ℕ) (hell : 0 < ell) (hN1 : ell ∣ L 1 + 1) (x : PeriodicLatticeSite L) :
    pathAngG 1 (thetaOf (Bpatf (L := L) ell uE)) x (List.replicate ell 1) =
      (ell : ℝ) * (if (x 0).val = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0) +
        (if (x 0).val = uE then (1 : ℝ) else 0) * (if (x 2).val % ell = ell - 1 then (1 : ℝ) else 0) := by
  rw [pathAng_pat_aux ell uE hN1]
  unfold bpat
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  by_cases a : (x 0).val = uE
  · by_cases b : (x 2).val % ell = ell - 1
    · have := sum_win_one ell hell (x 1).val
      simp only [a, b, and_true, if_true, one_mul]
      exact this
    · simp [a, b]
  · simp [a]

end

/-- the block of `u + k` (`k ≤ 1`, `u % ell + 2 ≤ ell`) is the block of `u`: if the aligned point `ell * a` has `u + k` in its window then `a = u / ell`. -/
theorem aligned_block {ell a u k : ℕ} (hr : u % ell + 2 ≤ ell) (hk : k ≤ 1) (h1 : ell * a ≤ u + k) (h2 : u + k < ell * a + ell) :
    ell * a = ell * (u / ell) := by
  have hell : 0 < ell := by omega
  have e : u = ell * (u / ell) + u % ell := (Nat.div_add_mod u ell).symm
  have hab1 : a ≤ u / ell := by
    by_contra h
    push Not at h
    have : ell * (u / ell + 1) ≤ ell * a := Nat.mul_le_mul_left ell h
    rw [Nat.mul_add] at this
    omega
  have hab2 : u / ell ≤ a := by
    by_contra h
    push Not at h
    have : ell * (a + 1) ≤ ell * (u / ell) := Nat.mul_le_mul_left ell h
    rw [Nat.mul_add] at this
    omega
  rw [le_antisymm hab1 hab2]

theorem aligned_fit {ell N y : ℕ} (hN : ell ∣ N) (hy : y % ell = 0) (hlt : y < N) : y + ell ≤ N := by
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨q, rfl⟩ : ell ∣ y := Nat.dvd_of_mod_eq_zero hy
  have hell : 0 < ell := by
    rcases Nat.eq_zero_or_pos ell with h | h
    · subst h; simp at hlt
    · exact h
  have : q < m := Nat.lt_of_mul_lt_mul_left hlt
  calc ell * q + ell = ell * (q + 1) := by ring
    _ ≤ ell * m := Nat.mul_le_mul_left ell this

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- the blocks of an aligned coarse site fit (also after the coarse shift). -/
theorem fit_aligned (ell : ℕ) (hell : 0 < ell) (hN : ∀ ν : Fin 3, ell ∣ L ν + 1) (y : PeriodicLatticeSite L) (hy : ∀ ν : Fin 3, (y ν).val % ell = 0)
    (μ : Fin 3) :
    (∀ ν : Fin 3, (y ν).val + 1 * ell ≤ L ν + 1) ∧ (∀ ν : Fin 3, ((cPlusS 1 ell (y, μ)) ν).val + 1 * ell ≤ L ν + 1) := by
  refine ⟨?_, ?_⟩
  · intro ν
    have := aligned_fit (hN ν) (hy ν) (y ν).isLt
    omega
  · intro ν
    rw [cPlusS_eq]
    by_cases hν : ν = μ
    · subst hν
      have h1 := coarseShift_val_eq y (1 * ell) ν
      have hlt := (y ν).isLt
      have hy1 := hy ν
      have hfit := aligned_fit (hN ν) hy1 hlt
      rw [h1]
      rcases Nat.lt_or_ge ((y ν).val + 1 * ell) (L ν + 1) with h | h
      · rw [Nat.mod_eq_of_lt h]
        have hal : ((y ν).val + 1 * ell) % ell = 0 := by rw [one_mul, Nat.add_mod_right]; exact hy1
        have := aligned_fit (hN ν) hal h
        omega
      · have : (y ν).val + 1 * ell = L ν + 1 := by omega
        rw [this, Nat.mod_self]
        have := Nat.le_of_dvd (by omega) (hN ν)
        omega
    · rw [coarseShift_apply_ne y (1 * ell) μ ν hν]
      have := aligned_fit (hN ν) (hy ν) (y ν).isLt
      omega

/-- **`Rsig` of the pattern vanishes at every coarse bond.** -/
theorem Rsig_pat_zero (ell uE : ℕ) (hell : 2 ≤ ell) (huE : uE % ell + 2 ≤ ell) (hN : ∀ ν : Fin 3, ell ∣ L ν + 1)
    (y : PeriodicLatticeSite L) (hy : ∀ ν : Fin 3, (y ν).val % ell = 0) (μ : Fin 3) :
    Rsig 1 ell (thetaOf (Bpatf (L := L) ell uE)) (y, μ) = 0 := by
  have hell0 : 0 < ell := by omega
  obtain ⟨hfit, hfit'⟩ := fit_aligned ell hell0 hN y hy μ
  rw [Rsig_closed one_pos hell0 y μ hfit hfit']
  by_cases hμ : μ = 1
  · subst hμ
    have hN1 := hN 1
    have hsum : ∑ x ∈ stepBlockOf y 1 ell, pathAngG 1 (thetaOf (Bpatf (L := L) ell uE)) x (List.replicate ell 1) =
        ∑ x ∈ stepBlockOf y 1 ell, ((((ell : ℝ) * (if (x 0).val = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0)) * 1 * 1) +
          ((if (x 0).val = uE then (1 : ℝ) else 0) * 1 * (if (x 2).val % ell = ell - 1 then (1 : ℝ) else 0))) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathAng_pat ell uE hell0 hN1 x]; ring
    rw [hsum, Finset.sum_add_distrib]
    have hc0 : min ell (L 0 + 1 - (y 0).val) = ell := by have := hfit 0; omega
    have hc1 : min ell (L 1 + 1 - (y 1).val) = ell := by have := hfit 1; omega
    have hc2 : min ell (L 2 + 1 - (y 2).val) = ell := by have := hfit 2; omega
    rw [sum_block_prod y ell (fun v => (ell : ℝ) * (if v = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0)) (fun _ => 1) (fun _ => 1),
      sum_block_prod y ell (fun v => if v = uE then (1 : ℝ) else 0) (fun _ => 1) (fun v => if v % ell = ell - 1 then (1 : ℝ) else 0)]
    rw [hc0, hc1, hc2]
    have hy0 := hy 0
    obtain ⟨a0, ha0⟩ : ell ∣ (y 0).val := Nat.dvd_of_mod_eq_zero hy0
    have hwin2 := sum_win_one ell hell0 (y 2).val
    have hwin2' : ∑ n ∈ range ell, (if ((y 2).val + n) % ell = ell - 1 then (1 : ℝ) else 0) = 1 := hwin2
    have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell0.ne'
    have hbs : uE = ell * (uE / ell) + uE % ell := (Nat.div_add_mod uE ell).symm
    -- the slice sums: nonzero exactly when `y 0` is the start of the block of `uE`
    have hA : ∑ n ∈ range ell, (ell : ℝ) * (if (y 0).val + n = uE + 1 then (-1 / ((ell : ℝ) * ell) : ℝ) else 0) =
        if (y 0).val = ell * (uE / ell) then (-1 / (ell : ℝ) : ℝ) else 0 := by
      by_cases h : (y 0).val = ell * (uE / ell)
      · rw [if_pos h, Finset.sum_eq_single (uE % ell + 1)]
        · rw [if_pos (by omega)]; field_simp
        · intro n hn hne1
          rw [if_neg (by omega), mul_zero]
        · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [if_neg, mul_zero]
        intro heq
        apply h
        rw [ha0] at heq ⊢
        exact aligned_block huE (k := 1) le_rfl (by omega) (by omega)
    have hB : ∑ n ∈ range ell, (if (y 0).val + n = uE then (1 : ℝ) else 0) = if (y 0).val = ell * (uE / ell) then 1 else 0 := by
      by_cases h : (y 0).val = ell * (uE / ell)
      · rw [if_pos h, Finset.sum_eq_single (uE % ell)]
        · rw [if_pos (by omega)]
        · intro n hn hne1; rw [if_neg (by omega)]
        · intro h1; exact absurd (Finset.mem_range.mpr (by omega)) h1
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro n hn
        have hn' := Finset.mem_range.mp hn
        rw [if_neg]
        intro heq
        apply h
        rw [ha0] at heq ⊢
        exact aligned_block huE (k := 0) (by omega) (by omega) (by omega)
    rw [hA, hB]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hwin2']
    by_cases h : (y 0).val = ell * (uE / ell)
    · simp only [h, if_true]
      field_simp
      ring
    · simp [h]
  · have hz : ∀ x : PeriodicLatticeSite L, pathAngG 1 (thetaOf (Bpatf (L := L) ell uE)) x (List.replicate ell μ) = 0 := by
      intro x
      have h0 : ∀ z : PeriodicLatticeSite L, thetaOf (Bpatf (L := L) ell uE) (z, μ) = 0 := by
        intro z
        unfold thetaOf
        have : Bpatf (L := L) ell uE (z, μ) = 0 := Bpatf_dir_ne ell uE (by show μ ≠ 1; exact hμ)
        rw [this]; simp [fromM2]
      have : ∀ (n : ℕ) (x : PeriodicLatticeSite L), pathAngG 1 (thetaOf (Bpatf (L := L) ell uE)) x (List.replicate n μ) = 0 := by
        intro n
        induction n with
        | zero => intro x; simp [pathAngG]
        | succ n ih => intro x; rw [List.replicate_succ, pathAngG, h0, ih, zero_add]
      exact this ell x
    simp only [hz, Finset.sum_const_zero, mul_zero]

end

#print axioms Rsig_pat_zero

end AdalyFormal.SitesOnly

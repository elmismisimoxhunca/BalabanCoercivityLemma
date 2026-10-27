import NuK4
import NtCvOU1
import NtCvO21
import NsCvO10

/-!
# NuK5 -- block sums of product functions and the abelian one-step map on the pattern (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.IngredientFamilyR2

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

/-- block sums of product functions of the three coordinates. -/
theorem sum_block_prod (z : PeriodicLatticeSite L) (ell : ℕ) (g0 g1 g2 : ℕ → ℝ) :
    ∑ x ∈ stepBlockOf z 1 ell, g0 (x 0).val * g1 (x 1).val * g2 (x 2).val =
      (∑ n ∈ range (min ell (L 0 + 1 - (z 0).val)), g0 ((z 0).val + n)) *
      (∑ n ∈ range (min ell (L 1 + 1 - (z 1).val)), g1 ((z 1).val + n)) *
      (∑ n ∈ range (min ell (L 2 + 1 - (z 2).val)), g2 ((z 2).val + n)) := by
  classical
  have hmem : ∀ x : PeriodicLatticeSite L, x ∈ stepBlockOf z 1 ell ↔
      ∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell := by
    intro x
    rw [mem_stepBlockOf]
    constructor
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2.1⟩
    · intro h μ; have := h μ; exact ⟨this.1, by simpa using this.2, one_dvd _⟩
  let G : Fin 3 → ℕ → ℝ := fun i => if i = 0 then g0 else if i = 1 then g1 else g2
  let F : (i : Fin 3) → Fin (L i + 1) → ℝ := fun i a =>
    if (z i).val ≤ a.val ∧ a.val < (z i).val + ell then G i a.val else 0
  have hpt : ∀ x : PeriodicLatticeSite L, (if x ∈ stepBlockOf z 1 ell then g0 (x 0).val * g1 (x 1).val * g2 (x 2).val else 0) =
      ∏ i : Fin 3, F i (x i) := by
    intro x
    rw [Fin.prod_univ_three]
    simp only [F, G]
    by_cases h : x ∈ stepBlockOf z 1 ell
    · have h' := (hmem x).mp h
      rw [if_pos h]
      simp [h' 0, h' 1, h' 2]
    · rw [if_neg h]
      have : ¬ (∀ μ : Fin 3, (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h2 => h ((hmem x).mpr h2)
      push Not at this
      obtain ⟨μ, hμ⟩ := this
      have hnot : ¬ ((z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + ell) := fun h3 => by
        have := hμ h3.1; omega
      fin_cases μ <;> simp_all
  have h1 : ∑ x ∈ stepBlockOf z 1 ell, g0 (x 0).val * g1 (x 1).val * g2 (x 2).val = ∑ x : PeriodicLatticeSite L, ∏ i : Fin 3, F i (x i) := by
    rw [← Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, ← Fintype.prod_sum F, Fin.prod_univ_three]
  have win : ∀ (i : Fin 3), ∑ a : Fin (L i + 1), F i a = ∑ n ∈ range (min ell (L i + 1 - (z i).val)), G i ((z i).val + n) := by
    intro i
    have := sum_fin_window (L i + 1) (z i).val ell (fun n => G i ((z i).val + n))
    rw [← this]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [F]
    by_cases hh : (z i).val ≤ a.val ∧ a.val < (z i).val + ell
    · rw [if_pos hh, if_pos hh]; congr 1; omega
    · rw [if_neg hh, if_neg hh]
  rw [win 0, win 1, win 2]
  simp only [G, if_true, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_neg (show ¬ ((2 : Fin 3) = 0) by decide),
    if_neg (show ¬ ((2 : Fin 3) = 1) by decide)]


open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.UbarTowerCov (cPlusS cPlusS_eq)

/-- the line integral of the pattern along two direction-1 steps equals `2 A(x₀) + C(x₀) o(x₂)`. -/
theorem pathAng_pat (uE : ℕ) (hN1 : 2 ∣ L 1 + 1) (x : PeriodicLatticeSite L) :
    pathAngG 1 (thetaOf (Bpatf (L := L) uE)) x (List.replicate 2 1) =
      2 * (if (x 0).val = uE + 1 then (-1 / 4 : ℝ) else 0) +
        (if (x 0).val = uE then (1 : ℝ) else 0) * (if (x 2).val % 2 = 1 then (1 : ℝ) else 0) := by
  have hth : ∀ (z : PeriodicLatticeSite L), thetaOf (Bpatf (L := L) uE) (z, 1) = betaPat uE z := thetaOf_Bpatf uE
  simp only [List.replicate_succ, List.replicate_zero, pathAngG, add_zero]
  rw [hth, hth]
  have c0 : (coarseShift x 1 1 0) = x 0 := coarseShift_apply_ne x 1 1 0 (by decide)
  have c2 : (coarseShift x 1 1 2) = x 2 := coarseShift_apply_ne x 1 1 2 (by decide)
  have c1 : ((coarseShift x 1 1) 1).val = ((x 1).val + 1) % (L 1 + 1) := coarseShift_val_eq x 1 1
  have hpar : ((x 1).val + 1) % (L 1 + 1) % 2 = ((x 1).val + 1) % 2 := Nat.mod_mod_of_dvd _ hN1
  unfold betaPat
  rw [c0, c2, c1, hpar]
  by_cases a1 : (x 0).val = uE + 1
  · have a2 : (x 0).val ≠ uE := by omega
    simp [a1, a2]; ring
  · by_cases a2 : (x 0).val = uE
    · simp only [a1, a2, if_false, if_true]
      by_cases b1 : (x 1).val % 2 = 1 <;> by_cases b2 : (x 2).val % 2 = 1
      · have : ((x 1).val + 1) % 2 = 0 := by omega
        simp [b1, b2, this]
      · have : ((x 1).val + 1) % 2 = 0 := by omega
        simp [b1, b2, this]
      · have : ((x 1).val + 1) % 2 = 1 := by omega
        simp [b1, b2, this]
      · have : ((x 1).val + 1) % 2 = 1 := by omega
        simp [b1, b2, this]
    · simp [a1, a2]


/-- the blocks of an aligned coarse site fit (also after the coarse shift). -/
theorem fit_aligned (hN : ∀ ν : Fin 3, 2 ∣ L ν + 1) (y : PeriodicLatticeSite L) (hy : ∀ ν : Fin 3, (y ν).val % 2 = 0)
    (μ : Fin 3) :
    (∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ L ν + 1) ∧ (∀ ν : Fin 3, ((cPlusS 1 2 (y, μ)) ν).val + 1 * 2 ≤ L ν + 1) := by
  refine ⟨?_, ?_⟩
  · intro ν
    obtain ⟨m, hm⟩ := hN ν
    have := (y ν).isLt
    have := hy ν
    omega
  · intro ν
    rw [cPlusS_eq]
    obtain ⟨m, hm⟩ := hN ν
    by_cases hν : ν = μ
    · subst hν
      have h1 := coarseShift_val_eq y (1 * 2) ν
      have hlt := (y ν).isLt
      have hy1 := hy ν
      rw [h1]
      rcases Nat.lt_or_ge ((y ν).val + 1 * 2) (L ν + 1) with h | h
      · rw [Nat.mod_eq_of_lt h]; omega
      · have : (y ν).val + 1 * 2 = L ν + 1 := by omega
        rw [this, Nat.mod_self]; omega
    · rw [coarseShift_apply_ne y (1 * 2) μ ν hν]
      have := (y ν).isLt
      have := hy ν
      omega

/-- **`Rsig` of the pattern vanishes at every coarse bond.** -/
theorem Rsig_pat_zero (uE : ℕ) (huE : uE % 2 = 0) (hN : ∀ ν : Fin 3, 2 ∣ L ν + 1)
    (y : PeriodicLatticeSite L) (hy : ∀ ν : Fin 3, (y ν).val % 2 = 0) (μ : Fin 3) :
    Rsig 1 2 (thetaOf (Bpatf (L := L) uE)) (y, μ) = 0 := by
  obtain ⟨hfit, hfit'⟩ := fit_aligned hN y hy μ
  rw [Rsig_closed one_pos (by norm_num) y μ hfit hfit']
  by_cases hμ : μ = 1
  · subst hμ
    have hN1 := hN 1
    have hsum : ∑ x ∈ stepBlockOf y 1 2, pathAngG 1 (thetaOf (Bpatf (L := L) uE)) x (List.replicate 2 1) =
        ∑ x ∈ stepBlockOf y 1 2, ((2 * (if (x 0).val = uE + 1 then (-1 / 4 : ℝ) else 0)) * 1 * 1 +
          ((if (x 0).val = uE then (1 : ℝ) else 0) * 1 * (if (x 2).val % 2 = 1 then (1 : ℝ) else 0))) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [pathAng_pat uE hN1 x]; ring
    rw [hsum, Finset.sum_add_distrib]
    have hc0 : min 2 (L 0 + 1 - (y 0).val) = 2 := by have := hfit 0; omega
    have hc1 : min 2 (L 1 + 1 - (y 1).val) = 2 := by have := hfit 1; omega
    have hc2 : min 2 (L 2 + 1 - (y 2).val) = 2 := by have := hfit 2; omega
    rw [sum_block_prod y 2 (fun v => 2 * (if v = uE + 1 then (-1 / 4 : ℝ) else 0)) (fun _ => 1) (fun _ => 1),
      sum_block_prod y 2 (fun v => if v = uE then (1 : ℝ) else 0) (fun _ => 1) (fun v => if v % 2 = 1 then (1 : ℝ) else 0)]
    rw [hc0, hc1, hc2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hy0 := hy 0
    have hy2 := hy 2
    by_cases h : (y 0).val = uE
    · have e1 : (y 0).val ≠ uE + 1 := by omega
      have e2 : (y 0).val + 1 = uE + 1 := by omega
      have e3 : (y 0).val + 1 ≠ uE := by omega
      have e4 : (y 2).val % 2 ≠ 1 := by omega
      have e5 : ((y 2).val + 1) % 2 = 1 := by omega
      simp [h, e1, e2, e3, e4, e5]
      norm_num
    · have e1 : (y 0).val ≠ uE + 1 := by omega
      have e2 : (y 0).val + 1 ≠ uE + 1 := by omega
      have e3 : (y 0).val + 1 ≠ uE := by omega
      simp [h, e1, e2, e3]
  · have hz : ∀ x : PeriodicLatticeSite L, pathAngG 1 (thetaOf (Bpatf (L := L) uE)) x (List.replicate 2 μ) = 0 := by
      intro x
      have h0 : ∀ z : PeriodicLatticeSite L, thetaOf (Bpatf (L := L) uE) (z, μ) = 0 := by
        intro z
        unfold thetaOf
        have : Bpatf (L := L) uE (z, μ) = 0 := Bpatf_dir_ne uE (by show μ ≠ 1; exact hμ)
        rw [this]; simp [fromM2]
      simp only [List.replicate_succ, List.replicate_zero, pathAngG, add_zero, h0]
    simp only [hz, Finset.sum_const_zero, mul_zero]

end

end AdalyFormal.NcwdhTwo

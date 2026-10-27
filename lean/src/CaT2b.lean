import CaT2a

/-!
# CaT2b -- `mkCube` (lane cov_assume_20261019): an `x₀`-window with the right layer conditions is a class cube containing a given site
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace CovAssume

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NonVac (mem_box_N)
open MXQ.AllC
open NcwdhFam
open AdalyFormal.CoverOmega.Struct (box_coord)

section
variable [CfData]

theorem mkCube {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) {j : ℕ} (hj : j ≤ 2)
    (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (s : ℕ)
    (hs : bigSide M 2 j ∣ s) (hsx : s ≤ (x 0).val ∧ (x 0).val < s + CfData.cf * bigSide M 2 j)
    (hsN : s + CfData.cf * bigSide M 2 j ≤ neN 2 M R)
    (hsub : ∀ w, s ≤ w → w < s + CfData.cf * bigSide M 2 j → Bc M R j w ∨ Bc M R (j + 1) w)
    (hmeet : ∃ w, s ≤ w ∧ w < s + CfData.cf * bigSide M 2 j ∧ Bc M R j w) :
    ∃ sites : Set (PeriodicLatticeSite (scaleUp 2 2 (neLu M R))),
      IsClassCube 2 M CfData.cf 2 (neS 2 M R) sites j ∧ x ∈ sites := by
  have hcf := CfData.hcf
  have hN := ne_scaleUp (ell := 2) (R := R) (by norm_num) hM
  have hu : 0 < bigSide M 2 j := by simp only [bigSide]; positivity
  obtain ⟨side, hside⟩ : ∃ side, side = CfData.cf * bigSide M 2 j := ⟨_, rfl⟩
  rw [← hside] at hsx hsN hsub hmeet
  have hpos : 0 < side := by rw [hside]; exact Nat.mul_pos (by omega) hu
  have hlt : ∀ (y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (μ : Fin 3), (y μ).val < neN 2 M R :=
    fun y μ => by have := (y μ).isLt; have := hN μ; omega
  have hsd : bigSide M 2 j ∣ side := by rw [hside]; exact Dvd.intro_left _ rfl
  let z : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) := fun μ =>
    if h : μ = 0 then ⟨s, by have := hN μ; omega⟩
    else ⟨side * ((x μ).val / side), by have := Nat.mul_div_le (x μ).val side; have := hlt x μ; have := hN μ; omega⟩
  have hz0 : (z 0).val = s := by simp [z]
  have hzμ : ∀ μ : Fin 3, μ ≠ 0 → (z μ).val = side * ((x μ).val / side) := by
    intro μ hμ; simp [z, hμ]
  have hxμ : ∀ μ : Fin 3, μ ≠ 0 → (z μ).val ≤ (x μ).val ∧ (x μ).val < (z μ).val + side := by
    intro μ hμ
    rw [hzμ μ hμ]
    have h1 := Nat.mul_div_le (x μ).val side
    have h2 := Nat.lt_mul_div_succ (x μ).val hpos
    rw [Nat.mul_add, Nat.mul_one] at h2
    exact ⟨h1, h2⟩
  have hbox : ∀ y : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)),
      s ≤ (y 0).val → (y 0).val < s + side → (y 1 = x 1) → (y 2 = x 2) → y ∈ siteBox z side := by
    intro y h0 h0' h1 h2
    rw [mem_box_N hN z y side]
    refine ⟨box_off (hlt y 0) (by rw [hz0]; exact h0) (by rw [hz0]; exact h0'), ?_, ?_⟩
    · rw [h1]
      have := hxμ 1 (by decide)
      exact box_off (hlt x 1) this.1 this.2
    · rw [h2]
      have := hxμ 2 (by decide)
      exact box_off (hlt x 2) this.1 this.2
  have hxbox : x ∈ siteBox z side := hbox x hsx.1 hsx.2 rfl rfl
  have hsub' : ∀ y ∈ siteBox z side, y ∈ towerBj (neS 2 M R) j ∪ towerBj (neS 2 M R) (j + 1) := by
    intro y hy
    have h0 := ((mem_box_N hN z y side).1 hy).1
    rw [hz0] at h0
    obtain ⟨hlo, hhi⟩ := box_coord (hlt y 0) (by omega) h0
    rcases hsub (y 0).val hlo hhi with h | h
    · exact Or.inl ((mem_bj j y).2 h)
    · exact Or.inr ((mem_bj (j + 1) y).2 h)
  obtain ⟨w, hw1, hw2, hwB⟩ := hmeet
  have hwN : w < neN 2 M R := by omega
  let q : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) := Function.update x 0 ⟨w, by have := hN 0; omega⟩
  have hq0 : (q 0).val = w := by simp [q]
  have hq1 : q 1 = x 1 := by simp [q]
  have hq2 : q 2 = x 2 := by simp [q]
  have hqbox : q ∈ siteBox z side := hbox q (by rw [hq0]; exact hw1) (by rw [hq0]; exact hw2) hq1 hq2
  have hqB : q ∈ towerBj (neS 2 M R) j := (mem_bj j q).2 (by rw [hq0]; exact hwB)
  refine ⟨siteBox z side, ⟨⟨hj, ⟨z, ?_, by rw [hside]⟩, hsub', ⟨q, hqbox, hqB⟩⟩, ?_⟩, hxbox⟩
  · intro μ
    by_cases hμ : μ = 0
    · subst hμ; rw [hz0]; exact Nat.mod_eq_zero_of_dvd hs
    · rw [hzμ μ hμ]; exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right hsd _)
  · rintro i ⟨hi, -, hsub2, ⟨p, hp, hpB⟩⟩
    have a1 : i = j ∨ i = j + 1 := by
      rcases hsub' p hp with h | h
      · exact Or.inl (bc_disj hM hR ((mem_bj i p).1 hpB) ((mem_bj j p).1 h))
      · exact Or.inr (bc_disj hM hR ((mem_bj i p).1 hpB) ((mem_bj (j + 1) p).1 h))
    have a2 : j = i ∨ j = i + 1 := by
      rcases hsub2 hqbox with h | h
      · exact Or.inl (bc_disj hM hR ((mem_bj j q).1 hqB) ((mem_bj i q).1 h))
      · exact Or.inr (bc_disj hM hR ((mem_bj j q).1 hqB) ((mem_bj (i + 1) q).1 h))
    omega

#print axioms mkCube

end

end CovAssume

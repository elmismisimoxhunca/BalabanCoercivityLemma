import GV7

/-!
# GV8 -- coverage of the far field by `Fseq 5` (m2_glue3, 2026-10-15)

* `margin`: for `ρ(p) ≥ 40`, a positive cap value anywhere in `nb p` forces the whole of `nb p` into the half-space.
* `cap_one_region`: for `ρ(p) ≥ 600` and `σ` the dominant direction, the cap of `σ` (sign of `p_σ`) is `1` on the
  whole radius-12 cube around `p`.
* `Fseq_cover`: `{p ∈ Box R : ρ(p) ≥ 600} ⊆ Fseq R 5`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open AdalyFormal.M2Glue2

theorem margin {R : ℕ} {σ : Fin 3} {b : Bool} {p : Z3} (hρ : 40 ≤ rho p) {p' : Z3} (hp' : p' ∈ nb R p)
    (hpos : 0 < capC σ b p') : ∀ p'' ∈ nb R p, hsP σ b p'' := by
  intro p'' hp''
  have hs := hs_of_capC_pos hpos
  have hbig := big_of_capC_pos hpos
  have hρ' := (rho_perturb (qc_dist hp'.2)).2
  push_cast at hρ'
  have h34 : 34 ≤ rho p' := by linarith
  have hQ := Qf_ge p'
  have h2 : 1156 ≤ rho p' ^ 2 := by nlinarith
  have hq : 48 < qc p' σ ^ 2 := by nlinarith
  have hd : |p'' σ - p' σ| ≤ 4 := by
    have a := hp'.2 σ; have c := hp''.2 σ
    rw [abs_le] at a c ⊢; constructor <;> linarith
  rw [abs_le] at hd
  unfold hsP at hs ⊢
  unfold qc at hq
  rcases hs with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · left; refine ⟨rfl, ?_⟩
    by_contra hc; push Not at hc
    have : p' σ ≤ 6 := by omega
    have a : ((p' σ : ℤ) : ℝ) ≤ 6 := by exact_mod_cast this
    have c : (0 : ℝ) ≤ ((p' σ : ℤ) : ℝ) := by exact_mod_cast h
    nlinarith
  · right; refine ⟨rfl, ?_⟩
    by_contra hc; push Not at hc
    have : -7 ≤ p' σ := by omega
    have a : (-7 : ℝ) ≤ ((p' σ : ℤ) : ℝ) := by exact_mod_cast this
    have c : ((p' σ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith

theorem exists_dominant (p : Z3) : ∃ σ, ∀ i, |qc p i| ≤ |qc p σ| := by
  by_cases h01 : |qc p 1| ≤ |qc p 0|
  · by_cases h02 : |qc p 2| ≤ |qc p 0|
    · exact ⟨0, fun i => by fin_cases i <;> simp <;> linarith⟩
    · exact ⟨2, fun i => by fin_cases i <;> simp <;> linarith⟩
  · by_cases h12 : |qc p 2| ≤ |qc p 1|
    · exact ⟨1, fun i => by fin_cases i <;> simp <;> linarith⟩
    · exact ⟨2, fun i => by fin_cases i <;> simp <;> linarith⟩

theorem cap_one_region {p : Z3} {σ : Fin 3} (hσ : ∀ i, |qc p i| ≤ |qc p σ|) (hρ : 600 ≤ rho p)
    {p' : Z3} (hp' : ∀ i, |p' i - p i| ≤ 12) :
    hsP σ (decide (0 ≤ p σ)) p' ∧ capC σ (decide (0 ≤ p σ)) p' = 1 := by
  set a := |qc p σ|
  have ha : 200 ≤ a := by
    have := hσ 0; have := hσ 1; have := hσ 2
    unfold rho at hρ; linarith
  have hd := qc_dist hp'
  push_cast at hd
  have hs : hsP σ (decide (0 ≤ p σ)) p' := by
    unfold hsP
    have e := hd σ
    rw [abs_le] at e
    by_cases h : 0 ≤ p σ
    · left; refine ⟨by simp [h], ?_⟩
      have h' : (0 : ℝ) ≤ ((p σ : ℤ) : ℝ) := by exact_mod_cast h
      have : a = qc p σ := by unfold a qc; rw [abs_of_nonneg (by linarith)]
      have : (0 : ℝ) ≤ ((p' σ : ℤ) : ℝ) := by unfold qc at *; linarith
      exact_mod_cast this
    · right; refine ⟨by simp [h], ?_⟩
      have h' : ((p σ : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show p σ ≤ -1 by omega)
      have : a = -qc p σ := by unfold a qc; rw [abs_of_neg (by linarith)]
      have : ((p' σ : ℤ) : ℝ) ≤ -1 := by unfold qc at *; linarith
      exact_mod_cast this
  refine ⟨hs, capC_one hs ?_⟩
  -- 4 q'_σ² ≥ 4 (a − 12)² ≥ 3 (a + 12)² ≥ Q'
  have low : a - 12 ≤ |qc p' σ| := by
    have e := hd σ
    have := abs_sub_abs_le_abs_sub (qc p σ) (qc p' σ)
    rw [abs_sub_comm] at e
    linarith
  have up : ∀ i, |qc p' i| ≤ a + 12 := by
    intro i
    have e := hd i
    have := abs_sub_abs_le_abs_sub (qc p' i) (qc p i)
    linarith [hσ i]
  have sq_low : (a - 12) ^ 2 ≤ qc p' σ ^ 2 := by
    rw [← sq_abs (qc p' σ)]; exact pow_le_pow_left₀ (by linarith) low 2
  have sq_up : ∀ i, qc p' i ^ 2 ≤ (a + 12) ^ 2 := by
    intro i; rw [← sq_abs (qc p' i)]; exact pow_le_pow_left₀ (abs_nonneg _) (up i) 2
  unfold Qf
  have u0 := sq_up 0; have u1 := sq_up 1; have u2 := sq_up 2
  nlinarith

theorem deep_mem {R : ℕ} {k : ℕ} {p : Z3} (hp : p ∈ Box R) (hρ : 32 ≤ rho p)
    (h1 : ∀ p' ∈ nb R p, Cj (k + 1) p' = 1) : p ∈ Fseq R (k + 1) := by
  refine ⟨hp, hρ, fun ⟨p', hp', hlt⟩ => ?_, fun _ p' hp' => ?_⟩
  · rw [h1 p' hp'] at hlt; exact absurd hlt (lt_irrefl 1)
  · exact hs_of_capC_pos (show 0 < Cj (k + 1) p' by rw [h1 p' hp']; norm_num)

theorem lift_mem {R : ℕ} {k : ℕ} {p : Z3} (hp : p ∈ Box R) (hρ : 40 ≤ rho p)
    (hsub : nb R p ⊆ Fseq R k) : p ∈ Fseq R (k + 1) := by
  refine ⟨hp, by linarith, fun _ => hsub, fun ⟨p', hp', hpos⟩ => ?_⟩
  exact margin hρ hp' hpos

theorem Fseq_cover {R : ℕ} {p : Z3} (hp : p ∈ Box R) (hρ : 600 ≤ rho p) : p ∈ Fseq R 5 := by
  obtain ⟨σ, hσ⟩ := exists_dominant p
  set b := decide (0 ≤ p σ)
  set j0 := idxA σ b
  have hj0 := idxA_le σ b
  have ho : ordA j0 = (σ, b) := ordA_idxA σ b
  have far : ∀ p' : Z3, (∀ i, |p' i - p i| ≤ 12) → 40 ≤ rho p' := by
    intro p' h
    have := (rho_perturb (qc_dist h)).2
    push_cast at this; linarith
  have claim : ∀ k, j0 + k ≤ 5 → ∀ p', p' ∈ Box R → (∀ i, |p' i - p i| ≤ 2 * (5 - ((j0 + k : ℕ) : ℤ))) →
      p' ∈ Fseq R (j0 + k) := by
    intro k
    induction k with
    | zero =>
      intro _ p' hp'B hp'd
      have hd10 : ∀ i, |p' i - p i| ≤ 10 := fun i => (hp'd i).trans (by push_cast; omega)
      rcases hk : j0 with _ | m
      · -- the first chart
        have hd12 : ∀ i, |p' i - p i| ≤ 12 := fun i => (hd10 i).trans (by norm_num)
        have c1 := cap_one_region hσ hρ hd12
        refine ⟨hp'B, by linarith [far p' hd12], ?_⟩
        rw [hk] at ho; rw [ho]; exact c1.1
      · refine deep_mem hp'B (by linarith [far p' (fun i => (hd10 i).trans (by norm_num))]) ?_
        intro p'' hp''
        have hd12 : ∀ i, |p'' i - p i| ≤ 12 := by
          intro i
          have a := hp''.2 i; have c := hp'd i
          rw [hk] at c; push_cast at c
          rw [abs_le] at a c ⊢; constructor <;> omega
        have c1 := cap_one_region hσ hρ hd12
        unfold Cj; rw [← hk, ho]; exact c1.2
    | succ k ih =>
      intro hk p' hp'B hp'd
      have IH := ih (by omega)
      rw [show j0 + (k + 1) = (j0 + k) + 1 by ring]
      refine lift_mem hp'B (far p' (fun i => (hp'd i).trans (by push_cast; omega))) ?_
      intro p'' hp''
      refine IH p'' hp''.1 (fun i => ?_)
      have a := hp''.2 i; have c := hp'd i
      push_cast at c ⊢
      rw [abs_le] at a c ⊢; constructor <;> omega
  have := claim (5 - j0) (by omega) p hp (fun i => by simp; push_cast; omega)
  rwa [show j0 + (5 - j0) = 5 by omega] at this

end AdalyFormal.M2Glue3

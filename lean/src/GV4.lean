import GV3

/-!
# GV4 -- far-field derivative bounds of the caps (m2_glue3, 2026-10-15)

`capC_bond`: `ρ(p) ≥ 16 ⇒ |capC(p+e_ν) − capC(p)| ≤ K1/ρ(p)`;
`capC_sten`: `ρ(p) ≥ 16 ⇒ |capC(p+e_μ+e_ν) − capC(p+e_μ) − capC(p+e_ν) + capC(p)| ≤ K2/ρ(p)²` (any `μ, ν`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue3

open AdalyFormal.M2Glue2

noncomputable def K1 : ℝ := 4104 + 8 * 2052 ^ 2
noncomputable def K2 : ℝ := 154949568

theorem K1_pos : 0 < K1 := by unfold K1; norm_num
theorem K2_pos : 0 < K2 := by unfold K2; norm_num

noncomputable def capN (σ : Fin 3) (P : Z3) : ℝ := 8 * qc P σ ^ 2

theorem capC_eq {σ : Fin 3} {b : Bool} {P : Z3} (hs : hsP σ b P) :
    capC σ b P = stepS (capN σ P / Qf P - 1) := by
  rw [capC_of_hs hs]; rfl

theorem capN_step (σ : Fin 3) (P : Z3) (μ : Fin 3) :
    |capN σ (P + ev μ) - capN σ P| ≤ 8 * (2 * |qc P σ| + 1) := by
  unfold capN; rw [qc_add_ev]
  split_ifs
  · have e : 8 * (qc P σ + 1) ^ 2 - 8 * qc P σ ^ 2 = 8 * (2 * qc P σ + 1) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]
    have := abs_add_le (2 * qc P σ) 1
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_one] at this
    linarith
  · simp only [add_zero, sub_self, abs_zero]; positivity

theorem Qf_step (P : Z3) (μ : Fin 3) : |Qf (P + ev μ) - Qf P| ≤ 2 * |qc P μ| + 1 := by
  rw [Qf_add_ev]
  rw [show Qf P + 2 * qc P μ + 1 - Qf P = 2 * qc P μ + 1 by ring]
  have := abs_add_le (2 * qc P μ) 1
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_one] at this
  exact this

theorem capN_second (σ : Fin 3) (P : Z3) (μ ν : Fin 3) :
    |capN σ (P + ev μ + ev ν) - capN σ (P + ev μ) - capN σ (P + ev ν) + capN σ P| ≤ 16 := by
  unfold capN; simp only [qc_add_ev]
  split_ifs <;> ring_nf <;> norm_num

theorem Qf_second (P : Z3) (μ ν : Fin 3) :
    |Qf (P + ev μ + ev ν) - Qf (P + ev μ) - Qf (P + ev ν) + Qf P| ≤ 16 := by
  simp only [Qf_add_ev, qc_add_ev]
  split_ifs <;> ring_nf <;> norm_num

theorem capN_le (σ : Fin 3) (P : Z3) : |capN σ P| ≤ 8 * Qf P := by
  unfold capN Qf
  rw [abs_of_nonneg (by positivity)]
  fin_cases σ <;> simp <;> nlinarith [sq_nonneg (qc P 0), sq_nonneg (qc P 1), sq_nonneg (qc P 2)]

/-- `ρ` along the stencil. -/
theorem qc_diff_le (p : Z3) (μ ν : Fin 3) (i : Fin 3) :
    |qc (p + ev ν) i - qc p i| ≤ 2 ∧ |qc (p + ev μ) i - qc p i| ≤ 2 ∧ |qc (p + ev μ + ev ν) i - qc p i| ≤ 2 := by
  simp only [qc_add_ev]
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> ring_nf <;> norm_num

theorem Qf_lower {p P : Z3} (hP : ∀ i, |qc P i - qc p i| ≤ 2) (hρ : 12 ≤ rho p) :
    1 ≤ 12 / rho p ^ 2 * Qf P := by
  have h := (rho_perturb hP).2
  have hQ := Qf_ge P
  have hρ0 : 0 < rho p := by linarith
  have h2 : rho p / 2 ≤ rho P := by linarith
  have h3 : (rho p / 2) ^ 2 ≤ rho P ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem abs_qc_le_of {p P : Z3} (hP : ∀ i, |qc P i - qc p i| ≤ 2) (σ : Fin 3) : |qc P σ| ≤ rho p + 2 := by
  have := rho_le_three_mul p σ
  have h := hP σ
  calc |qc P σ| = |qc p σ + (qc P σ - qc p σ)| := by ring_nf
    _ ≤ |qc p σ| + |qc P σ - qc p σ| := abs_add_le _ _
    _ ≤ rho p + 2 := by linarith

theorem Qf_ge18 {p P : Z3} (hP : ∀ i, |qc P i - qc p i| ≤ 2) (hρ : 16 ≤ rho p) : 18 ≤ Qf P := by
  have h := Qf_lower hP (by linarith)
  have hρ0 : 0 < rho p := by linarith
  have hQ := Qf_pos P
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
  nlinarith

theorem Qf_upper (p : Z3) (hρ : 0 < rho p) : 12 / rho p ^ 2 * Qf p ≤ 12 := by
  have := Qf_le p
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith

theorem ev_coord_abs (p : Z3) (μ σ : Fin 3) : |p σ - (p + ev μ) σ| ≤ 2 := by
  have := ev_abs μ σ
  simp only [Pi.add_apply]
  rw [show p σ - (p σ + ev μ σ) = -(ev μ σ) by ring, abs_neg]; linarith

/-- first difference of the cap exponent. -/
theorem capf_first {σ : Fin 3} {p P : Z3} (μ : Fin 3) (hP : ∀ i, |qc P i - qc p i| ≤ 1)
    (hP' : ∀ i, |qc (P + ev μ) i - qc p i| ≤ 2) (hρ : 16 ≤ rho p) :
    |(capN σ (P + ev μ) / Qf (P + ev μ) - 1) - (capN σ P / Qf P - 1)| ≤ 2052 / rho p := by
  have hρ0 : 0 < rho p := by linarith
  have hP2 : ∀ i, |qc P i - qc p i| ≤ 2 := fun i => (hP i).trans (by norm_num)
  have hq : ∀ j, |qc P j| ≤ rho p + 1 := by
    intro j
    have := rho_le_three_mul p j
    have h := hP j
    calc |qc P j| = |qc p j + (qc P j - qc p j)| := by ring_nf
      _ ≤ |qc p j| + |qc P j - qc p j| := abs_add_le _ _
      _ ≤ rho p + 1 := by linarith
  have hN : |capN σ (P + ev μ) - capN σ P| ≤ 16 * rho p + 24 := by
    have := capN_step σ P μ; have := hq σ; linarith
  have hD : |Qf (P + ev μ) - Qf P| ≤ 16 * rho p + 24 := by
    have := Qf_step P μ; have := hq μ; linarith
  have q := quot_first (u := 12 / rho p ^ 2) (A := 8) (by positivity) (Qf_lower hP2 (by linarith))
    (Qf_lower hP' (by linarith)) (by norm_num) (capN_le σ P) hN hD
  rw [show (capN σ (P + ev μ) / Qf (P + ev μ) - 1) - (capN σ P / Qf P - 1)
      = capN σ (P + ev μ) / Qf (P + ev μ) - capN σ P / Qf P by ring]
  refine q.trans ?_
  rw [show (1 + 8 : ℝ) * (16 * rho p + 24) * (12 / rho p ^ 2) = 108 * (16 * rho p + 24) / rho p ^ 2 by ring,
    div_le_div_iff₀ (by positivity) hρ0]
  nlinarith

theorem capC_bond (σ : Fin 3) (b : Bool) (p : Z3) (ν : Fin 3) (hρ : 16 ≤ rho p) :
    |capC σ b (p + ev ν) - capC σ b p| ≤ K1 / rho p := by
  have hρ0 : 0 < rho p := by linarith
  have hK : 0 ≤ K1 / rho p := div_nonneg K1_pos.le hρ0.le
  have d0 : ∀ i, |qc p i - qc p i| ≤ 2 := fun i => by simp
  have d1 : ∀ i, |qc (p + ev ν) i - qc p i| ≤ 2 := fun i => (qc_diff_le p ν ν i).1
  by_cases h0 : hsP σ b p
  · by_cases h1 : hsP σ b (p + ev ν)
    · rw [capC_eq h0, capC_eq h1]
      have hf := capf_first (σ := σ) (p := p) (P := p) ν (fun i => by simp) d1 hρ
      have hl := stepS_lip (capN σ p / Qf p - 1) (capN σ (p + ev ν) / Qf (p + ev ν) - 1)
      refine hl.trans ?_
      set δ := (capN σ (p + ev ν) / Qf (p + ev ν) - 1) - (capN σ p / Qf p - 1)
      have hsq : δ ^ 2 ≤ (2052 / rho p) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hf 2
      have e : (2052 / rho p) ^ 2 ≤ 2052 ^ 2 / rho p := by
        rw [div_pow, div_le_div_iff₀ (by positivity) hρ0]; nlinarith
      unfold K1
      rw [add_div, mul_div_assoc]
      have : 2 * (2052 / rho p) = 4104 / rho p := by ring
      nlinarith
    · rw [capC_zero_near_boundary h1 (ev_coord_abs p ν σ) (Qf_ge18 d0 hρ),
        capC_zero_near_boundary h1 (by simp) (Qf_ge18 d1 hρ)]
      simpa using hK
  · have e2 : |(p + ev ν) σ - p σ| ≤ 2 := by rw [abs_sub_comm]; exact ev_coord_abs p ν σ
    rw [capC_zero_near_boundary h0 e2 (Qf_ge18 d1 hρ),
      capC_zero_near_boundary h0 (by simp) (Qf_ge18 d0 hρ)]
    simpa using hK

theorem capC_sten (σ : Fin 3) (b : Bool) (p : Z3) (μ ν : Fin 3) (hρ : 16 ≤ rho p) :
    |capC σ b (p + ev μ + ev ν) - capC σ b (p + ev μ) - capC σ b (p + ev ν) + capC σ b p| ≤ K2 / rho p ^ 2 := by
  have hρ0 : 0 < rho p := by linarith
  have hK : 0 ≤ K2 / rho p ^ 2 := div_nonneg K2_pos.le (by positivity)
  set P1 := p + ev ν; set P2 := p + ev μ; set P3 := p + ev μ + ev ν
  have d0 : ∀ i, |qc p i - qc p i| ≤ 2 := fun i => by simp
  have d1 : ∀ i, |qc P1 i - qc p i| ≤ 2 := fun i => (qc_diff_le p μ ν i).1
  have d2 : ∀ i, |qc P2 i - qc p i| ≤ 2 := fun i => (qc_diff_le p μ ν i).2.1
  have d3 : ∀ i, |qc P3 i - qc p i| ≤ 2 := fun i => (qc_diff_le p μ ν i).2.2
  have e1 : ∀ i, |qc P1 i - qc p i| ≤ 1 := fun i => abs_qc_add_ev_le p ν i
  have e2 : ∀ i, |qc P2 i - qc p i| ≤ 1 := fun i => abs_qc_add_ev_le p μ i
  -- σ-coordinates of the four points lie within 2 of each other
  have cσ : ∀ X Y : Z3, X ∈ ({p, P1, P2, P3} : Set Z3) → Y ∈ ({p, P1, P2, P3} : Set Z3) → |X σ - Y σ| ≤ 2 := by
    intro X Y hX hY
    have a1 := ev_abs μ σ; have a2 := ev_abs ν σ
    have b1 : 0 ≤ ev μ σ := by unfold ev; split_ifs <;> norm_num
    have b2 : 0 ≤ ev ν σ := by unfold ev; split_ifs <;> norm_num
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
    rw [abs_le] at a1 a2 ⊢
    rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
      (try simp only [P1, P2, P3, Pi.add_apply]) <;> constructor <;> linarith
  have Q0 := Qf_ge18 d0 hρ; have Q1 := Qf_ge18 d1 hρ; have Q2 := Qf_ge18 d2 hρ; have Q3 := Qf_ge18 d3 hρ
  by_cases hall : hsP σ b p ∧ hsP σ b P1 ∧ hsP σ b P2 ∧ hsP σ b P3
  · obtain ⟨h0, h1, h2, h3⟩ := hall
    rw [capC_eq h0, capC_eq h1, capC_eq h2, capC_eq h3]
    refine (stepS_second _ _ _ _).trans ?_
    have hP3 : P3 = P2 + ev ν := rfl
    have hP3' : P3 = P1 + ev μ := by simp only [P1, P3]; abel
    -- first differences
    have f10 := capf_first (σ := σ) (P := p) ν (fun i => by simp) d1 hρ
    have f20 := capf_first (σ := σ) (P := p) μ (fun i => by simp) d2 hρ
    have f32 := capf_first (σ := σ) (P := P2) ν e2 (by rw [← hP3]; exact d3) hρ
    rw [← hP3] at f32
    -- second difference
    have hq : ∀ j, |qc p j| ≤ rho p + 1 := fun j => (rho_le_three_mul p j).trans (by linarith)
    have hq1 : ∀ j, |qc P1 j| ≤ rho p + 1 := by
      intro j
      have := rho_le_three_mul p j; have h := e1 j
      calc |qc P1 j| = |qc p j + (qc P1 j - qc p j)| := by ring_nf
        _ ≤ |qc p j| + |qc P1 j - qc p j| := abs_add_le _ _
        _ ≤ rho p + 1 := by linarith
    have hq2 : ∀ j, |qc P2 j| ≤ rho p + 1 := by
      intro j
      have := rho_le_three_mul p j; have h := e2 j
      calc |qc P2 j| = |qc p j + (qc P2 j - qc p j)| := by ring_nf
        _ ≤ |qc p j| + |qc P2 j - qc p j| := abs_add_le _ _
        _ ≤ rho p + 1 := by linarith
    have n10 : |capN σ P1 - capN σ p| ≤ 16 * rho p + 24 := by
      have := capN_step σ p ν; have := hq σ; linarith
    have n20 : |capN σ P2 - capN σ p| ≤ 16 * rho p + 24 := by
      have := capN_step σ p μ; have := hq σ; linarith
    have q10 : |Qf P1 - Qf p| ≤ 16 * rho p + 24 := by
      have := Qf_step p ν; have := hq ν; linarith
    have q20 : |Qf P2 - Qf p| ≤ 16 * rho p + 24 := by
      have := Qf_step p μ; have := hq μ; linarith
    have q31 : |Qf P3 - Qf P1| ≤ 16 * rho p + 24 := by
      rw [hP3']; have := Qf_step P1 μ; have := hq1 μ; linarith
    have q32 : |Qf P3 - Qf P2| ≤ 16 * rho p + 24 := by
      rw [hP3]; have := Qf_step P2 ν; have := hq2 ν; linarith
    have hnC := capN_second σ p μ ν
    have hdC := Qf_second p μ ν
    have qs := quot_second (u := 12 / rho p ^ 2) (A := 8) (E := 12) (by positivity)
      (Qf_lower d0 (by linarith)) (Qf_lower d1 (by linarith)) (Qf_lower d2 (by linarith))
      (Qf_lower d3 (by linarith)) (Qf_upper p hρ0) (by norm_num) (capN_le σ p) n10 n20 q10 q20 q31 q32
      hnC hdC
    have hsec : |(capN σ P3 / Qf P3 - 1) - (capN σ P2 / Qf P2 - 1) - (capN σ P1 / Qf P1 - 1)
        + (capN σ p / Qf p - 1)| ≤ 10103520 / rho p ^ 2 := by
      rw [show (capN σ P3 / Qf P3 - 1) - (capN σ P2 / Qf P2 - 1) - (capN σ P1 / Qf P1 - 1) + (capN σ p / Qf p - 1)
        = capN σ P3 / Qf P3 - capN σ P2 / Qf P2 - capN σ P1 / Qf P1 + capN σ p / Qf p by ring]
      refine qs.trans ?_
      have hB : (16 * rho p + 24) ^ 2 ≤ 361 * rho p ^ 2 := by nlinarith
      have e : (1 + 8 * 12 : ℝ) * (16 * (12 / rho p ^ 2) + 2 * (16 * rho p + 24) ^ 2 * (12 / rho p ^ 2) ^ 2)
          = 97 * (192 * rho p ^ 2 + 288 * (16 * rho p + 24) ^ 2) / rho p ^ 4 := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : rho p ^ 4 = rho p ^ 2 * rho p ^ 2 := by ring
      rw [h4]
      have hp2 : 0 < rho p ^ 2 := by positivity
      nlinarith
    -- assemble
    set a := (capN σ P3 / Qf P3 - 1) - (capN σ P2 / Qf P2 - 1) - (capN σ P1 / Qf P1 - 1) + (capN σ p / Qf p - 1)
    set x := (capN σ P2 / Qf P2 - 1) - (capN σ p / Qf p - 1)
    set y := (capN σ P1 / Qf P1 - 1) - (capN σ p / Qf p - 1)
    set z := (capN σ P3 / Qf P3 - 1) - (capN σ P2 / Qf P2 - 1)
    have w : 2052 / rho p * (2052 / rho p) = 2052 ^ 2 / rho p ^ 2 := by ring
    have hx : |x| * |y| ≤ 2052 ^ 2 / rho p ^ 2 := by
      rw [← w]; exact mul_le_mul f20 f10 (abs_nonneg _) (by positivity)
    have hz : z ^ 2 ≤ 2052 ^ 2 / rho p ^ 2 := by
      rw [← w, ← sq_abs, sq]; exact mul_le_mul f32 f32 (abs_nonneg _) (by positivity)
    have hy : y ^ 2 ≤ 2052 ^ 2 / rho p ^ 2 := by
      rw [← w, ← sq_abs, sq]; exact mul_le_mul f10 f10 (abs_nonneg _) (by positivity)
    have : 16 * |x| * |y| = 16 * (|x| * |y|) := by ring
    unfold K2
    have k : (154949568 : ℝ) / rho p ^ 2 = 2 * (10103520 / rho p ^ 2) + 32 * (2052 ^ 2 / rho p ^ 2) := by ring
    rw [k]
    linarith
  · -- some point leaves the half-space: every value is 0
    have hz : ∃ X ∈ ({p, P1, P2, P3} : Set Z3), ¬ hsP σ b X := by
      by_contra hc; push Not at hc
      exact hall ⟨hc p (by simp), hc P1 (by simp), hc P2 (by simp), hc P3 (by simp)⟩
    obtain ⟨X, hX, hXn⟩ := hz
    have z0 := capC_zero_near_boundary hXn (cσ p X (by simp) hX) Q0
    have z1 := capC_zero_near_boundary hXn (cσ P1 X (by simp) hX) Q1
    have z2 := capC_zero_near_boundary hXn (cσ P2 X (by simp) hX) Q2
    have z3 := capC_zero_near_boundary hXn (cσ P3 X (by simp) hX) Q3
    rw [z0, z1, z2, z3]; simpa using hK

end AdalyFormal.M2Glue3

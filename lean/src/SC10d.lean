import SC10c

/-!
# SC10d -- v2: trivial-twist core, the regime analysis, and `cell_coercive_explicit2`.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Final
variable {n : ℕ}

theorem lamN_eq (hn : 0 < n) (σ κ : ℝ) :
    lamN κ (4 / (n : ℝ) ^ 2) ((n : ℝ) * ‖epsV n‖) (cn n * (σ * (n : ℝ)) ^ 4)
      = LmF σ (κ * (n : ℝ) ^ 7) / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn2 : cn n ^ 2 * (n : ℝ) ^ 3 = 1 := cn_sq hn
  have hA2 : ((n : ℝ) * ‖epsV n‖) ^ 2 = (n : ℝ) ^ 5 := by rw [mul_pow, norm_epsV_sq hn]; ring
  have hq02 : (cn n * (σ * (n : ℝ)) ^ 4) ^ 2 = σ ^ 8 * (n : ℝ) ^ 5 := by
    rw [mul_pow, ← pow_mul, mul_pow]
    calc cn n ^ 2 * (σ ^ (4 * 2) * (n : ℝ) ^ (4 * 2))
        = (cn n ^ 2 * (n : ℝ) ^ 3) * (σ ^ 8 * (n : ℝ) ^ 5) := by ring
      _ = _ := by rw [hcn2, one_mul]
  unfold lamN LmF
  rw [hq02, hA2]
  have e1 : κ * (σ ^ 8 * (n : ℝ) ^ 5) / 4 = κ * (n : ℝ) ^ 7 * σ ^ 8 / 4 / (n : ℝ) ^ 2 := by
    field_simp
  have e2 : 4 / (n : ℝ) ^ 2 * (σ ^ 8 * (n : ℝ) ^ 5) / (4 * (n : ℝ) ^ 5 + σ ^ 8 * (n : ℝ) ^ 5)
      = 4 * σ ^ 8 / (4 + σ ^ 8) / (n : ℝ) ^ 2 := by
    have h5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
    have h6 : (0 : ℝ) < 4 + σ ^ 8 := by positivity
    field_simp
  rw [e1, e2, ← min_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]

theorem cell_core_trivial (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) (z : Fin 3 → Circle) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hσ : SigmaOK z σ) (hall : ∀ μ, ((z μ : Circle) : ℂ) = 1)
    (w : Fin 3 → CV n) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) :
    LmF σ (κ * (n : ℝ) ^ 7) / (n : ℝ) ^ 2 * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have hepsn : 0 < ‖epsV n‖ := norm_pos_iff.mpr (epsV_ne hn)
  have hApos : 0 < (n : ℝ) * ‖epsV n‖ := by positivity
  have hq0nn : 0 ≤ cn n * (σ * (n : ℝ)) ^ 4 := by positivity
  have hAq : ∀ μ x, ‖(cellSym hn z).Qm μ x‖ ≤ ((n : ℝ) * ‖epsV n‖) * ‖x‖ := by
    intro μ x
    exact Qm_norm_le (cellSym hn z) μ x
  have hq : ∀ μ, cn n * (σ * (n : ℝ)) ^ 4 ≤ ‖(cellSym hn z).Qm μ (cellMode hn z).e0‖ :=
    fun μ => Qm_e0_lower_σ hn z σ hσ0.le hσ1 hσ μ
  have hNw := N_coercive (cellMode hn z) κ ((n : ℝ) * ‖epsV n‖) (cn n * (σ * (n : ℝ)) ^ 4) hκ.le hApos hq0nn hq hAq
  have hG : (cellMode hn z).G = 4 / (n : ℝ) ^ 2 := rfl
  have e := lamN_eq hn σ κ
  unfold lamN at e
  have hNw' : ∀ w' : Fin 3 → CV n, LmF σ (κ * (n : ℝ) ^ 7) / (n : ℝ) ^ 2 * ∑ μ, ‖w' μ‖ ^ 2
      ≤ Eb (cellSym hn z) w' + κ * g2b (cellSym hn z) w' := by
    intro w'
    have := hNw w'
    rw [← e]
    exact this
  exact cell_abstract_trivial_gen (cellMode hn z) κ _ hNw' hall w S hS0 hS

theorem Th2_le_three (z : Fin 3 → Circle) (h : ∀ μ, |th z μ| ≤ 1) : Th2 z ≤ 3 := by
  unfold Th2
  have : ∀ μ : Fin 3, th z μ ^ 2 ≤ 1 := by
    intro μ
    have := h μ
    nlinarith [sq_abs (th z μ), abs_nonneg (th z μ)]
  calc ∑ μ, th z μ ^ 2 ≤ ∑ _μ : Fin 3, (1 : ℝ) := Finset.sum_le_sum (fun μ _ => this μ)
    _ = 3 := by simp

theorem th_eq_zero_of_one (z : Fin 3 → Circle) (μ : Fin 3) (h : ((z μ : Circle) : ℂ) = 1) : th z μ = 0 := by
  unfold th; rw [h]; exact Complex.arg_one

/-- **THE EXPLICIT CELL THEOREM, v2** -/
theorem cell_coercive_explicit2 (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) (z : Fin 3 → Circle) (w : Fin 3 → CV n)
    (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) :
    hfun2 (κ * (n : ℝ) ^ 7) / (n : ℝ) ^ 2 * ∑ μ, ‖w μ‖ ^ 2
      ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  set a : ℝ := κ * (n : ℝ) ^ 7 with ha
  have ha0 : 0 ≤ a := by positivity
  have h3 : 0 ≤ ∑ μ, ‖w μ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hpi3 := Real.pi_gt_three
  have hσL1 : 2 / Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith
  have hσL0 : 0 < 2 / Real.pi := by positivity
  have hS1 : (0 : ℝ) < 15 / 16 := by norm_num
  have hS1' : (15 / 16 : ℝ) ≤ 1 := by norm_num
  have hhf_S : hfun2 a ≤ cS2 a := min_le_left _ _
  have hhf_L : hfun2 a ≤ cL2 a := min_le_right _ _
  by_cases hall : ∀ μ, ((z μ : Circle) : ℂ) = 1
  · have hσ := sigmaOK_small z (fun μ => by rw [th_eq_zero_of_one z μ (hall μ)]; simp)
    have := cell_core_trivial hn κ hκ z (15 / 16) hS1 hS1' hσ hall w S hS0 hS
    have hc : hfun2 a ≤ LmF (15 / 16) a := by
      refine hhf_S.trans ?_
      unfold cS2
      have h1 := rat_le_one (muF_nonneg (σ := 15 / 16) (x := LmF (15 / 16) a) ha0 (LmF_nonneg ha0))
      have h2 := LmF_nonneg (σ := 15 / 16) ha0
      exact mul_le_of_le_one_left h2 h1
    refine le_trans ?_ this
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hn2.le) h3
  · push_neg at hall
    obtain ⟨μ0, hμ0⟩ := hall
    by_cases hsm : ∀ μ, |th z μ| ≤ 1
    · -- small-twist regime
      have hσ := sigmaOK_small z hsm
      have key := cell_core_nontrivial hn κ hκ z (15 / 16) hS1 hS1' hσ μ0 hμ0 w S hS0 hS
      set x : ℝ := (n : ℝ) ^ 2 * lam n z (k0 hn) with hx
      have hxpos : 0 < x := by
        have := lam0_pos hn z μ0 hμ0
        positivity
      have hxTh : x ≤ Th2 z := by
        have h1 := (le_div_iff₀ hn2).mp (lam0_le hn z)
        calc x = lam n z (k0 hn) * (n : ℝ) ^ 2 := by rw [hx]; ring
          _ ≤ _ := h1
      have hx3 : x ≤ 3 := hxTh.trans (Th2_le_three z hsm)
      have hLm := LmF_nonneg (σ := 15 / 16) ha0
      have hapos : 0 < a := by
        have : 0 < κ * (n : ℝ) ^ 7 := by positivity
        exact this
      have hrn : 0 ≤ rat (muF (15 / 16) a x) := rat_nonneg (muF_nonneg ha0 hxpos.le)
      have hcoef : hfun2 a ≤ rat (muF (15 / 16) a x) * max (min x 4) (LmF (15 / 16) a) := by
        refine hhf_S.trans ?_
        unfold cS2
        by_cases hxL : x ≤ LmF (15 / 16) a
        · have hm := muF_anti (σ := 15 / 16) ha0 hxpos hxL
          have hr := ratio_mono (muF_nonneg (σ := 15 / 16) (x := LmF (15 / 16) a) ha0 hLm) hm
          have hmax : LmF (15 / 16) a ≤ max (min x 4) (LmF (15 / 16) a) := le_max_right _ _
          unfold rat at hr ⊢
          calc muF (15 / 16) a (LmF (15 / 16) a) / (1 + muF (15 / 16) a (LmF (15 / 16) a)) * LmF (15 / 16) a
              ≤ muF (15 / 16) a x / (1 + muF (15 / 16) a x) * LmF (15 / 16) a :=
                mul_le_mul_of_nonneg_right hr hLm
            _ ≤ _ := mul_le_mul_of_nonneg_left hmax hrn
        · push_neg at hxL
          have hmin : min x 4 = x := min_eq_left (by linarith)
          have hmax : x ≤ max (min x 4) (LmF (15 / 16) a) := by rw [hmin]; exact le_max_left _ _
          have hpos : 0 < LmF (15 / 16) a := by unfold LmF; exact lt_min (by positivity) (by positivity)
          have e1 := rat_muF (σ := 15 / 16) (a := a) (y := LmF (15 / 16) a) hapos (by norm_num) hLm
          have e2 := rat_muF (σ := 15 / 16) (a := a) (y := x) hapos (by norm_num) hxpos.le
          rw [e1]
          have key2 : a * (15 / 16 : ℝ) ^ 8 / (LmF (15 / 16) a * (1 + a / 4) + a + a * (15 / 16) ^ 8)
              * LmF (15 / 16) a ≤ rat (muF (15 / 16) a x) * x := by
            rw [e2, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            have hd : 0 < a * (15 / 16 : ℝ) ^ 8 := by positivity
            have : LmF (15 / 16) a * (x * (1 + a / 4) + a + a * (15 / 16) ^ 8)
                ≤ x * (LmF (15 / 16) a * (1 + a / 4) + a + a * (15 / 16) ^ 8) := by
              nlinarith [mul_le_mul_of_nonneg_right hxL.le (by positivity : (0 : ℝ) ≤ a + a * (15 / 16) ^ 8)]
            nlinarith [mul_le_mul_of_nonneg_left this hd.le]
          calc _ ≤ rat (muF (15 / 16) a x) * x := key2
            _ ≤ _ := mul_le_mul_of_nonneg_left hmax hrn
      refine le_trans ?_ key
      apply mul_le_mul_of_nonneg_right _ h3
      exact div_le_div_of_nonneg_right hcoef hn2.le
    · -- large-twist regime
      push_neg at hsm
      obtain ⟨μ1, hμ1⟩ := hsm
      have hσ := sigmaOK_pi z
      have key := cell_core_nontrivial hn κ hκ z (2 / Real.pi) hσL0 hσL1 hσ μ0 hμ0 w S hS0 hS
      set x : ℝ := (n : ℝ) ^ 2 * lam n z (k0 hn) with hx
      have hxpos : 0 < x := by
        have := lam0_pos hn z μ0 hμ0
        positivity
      have hxTh : x ≤ Th2 z := by
        have h1 := (le_div_iff₀ hn2).mp (lam0_le hn z)
        calc x = lam n z (k0 hn) * (n : ℝ) ^ 2 := by rw [hx]; ring
          _ ≤ _ := h1
      have hTh1 : 1 < Th2 z := by
        have : th z μ1 ^ 2 ≤ Th2 z :=
          Finset.single_le_sum (f := fun μ => th z μ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ μ1)
        have h2 : 1 < th z μ1 ^ 2 := by nlinarith [sq_abs (th z μ1), abs_nonneg (th z μ1)]
        linarith
      have hxlo : 4 / Real.pi ^ 2 < x := by
        have h1 := lam0_ge hn z
        have h2 : 4 / Real.pi ^ 2 * 1 < 4 / Real.pi ^ 2 * Th2 z :=
          mul_lt_mul_of_pos_left hTh1 (by positivity)
        linarith
      have hxX : x ≤ 3 * Real.pi ^ 2 := hxTh.trans (Th2_le z)
      have hLm := LmF_nonneg (σ := 2 / Real.pi) ha0
      have hcoef : hfun2 a ≤ rat (muF (2 / Real.pi) a x) * max (min x 4) (LmF (2 / Real.pi) a) := by
        refine hhf_L.trans ?_
        unfold cL2
        have hrn : 0 ≤ rat (muF (2 / Real.pi) a x) := rat_nonneg (muF_nonneg ha0 hxpos.le)
        by_cases h4 : 4 ≤ x
        · have hm := muF_anti (σ := 2 / Real.pi) ha0 hxpos hxX
          have hr := ratio_mono (muF_nonneg (σ := 2 / Real.pi) (x := 3 * Real.pi ^ 2) ha0 (by positivity)) hm
          have hmin : min x 4 = 4 := min_eq_right h4
          have hmax : (4 : ℝ) ≤ max (min x 4) (LmF (2 / Real.pi) a) := by
            rw [hmin]; exact le_max_left _ _
          refine (min_le_left _ _).trans ?_
          unfold rat at hr hrn ⊢
          calc 4 * (muF (2 / Real.pi) a (3 * Real.pi ^ 2) / (1 + muF (2 / Real.pi) a (3 * Real.pi ^ 2)))
              ≤ 4 * (muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x)) :=
                mul_le_mul_of_nonneg_left hr (by norm_num)
            _ = (muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x)) * 4 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hmax hrn
        · push_neg at h4
          have hm := muF_anti (σ := 2 / Real.pi) ha0 hxpos h4.le
          have hr := ratio_mono (muF_nonneg (σ := 2 / Real.pi) (x := 4) ha0 (by norm_num)) hm
          have hmin : min x 4 = x := min_eq_left h4.le
          have hmax : x ≤ max (min x 4) (LmF (2 / Real.pi) a) := by
            rw [hmin]; exact le_max_left _ _
          refine (min_le_right _ _).trans ?_
          unfold rat at hr hrn ⊢
          have hrn4 : 0 ≤ muF (2 / Real.pi) a 4 / (1 + muF (2 / Real.pi) a 4) :=
            rat_nonneg (muF_nonneg ha0 (by norm_num))
          calc 4 / Real.pi ^ 2 * (muF (2 / Real.pi) a 4 / (1 + muF (2 / Real.pi) a 4))
              ≤ x * (muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x)) := by
                have h1 : muF (2 / Real.pi) a 4 / (1 + muF (2 / Real.pi) a 4)
                    ≤ muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x) := hr
                calc 4 / Real.pi ^ 2 * (muF (2 / Real.pi) a 4 / (1 + muF (2 / Real.pi) a 4))
                    ≤ x * (muF (2 / Real.pi) a 4 / (1 + muF (2 / Real.pi) a 4)) :=
                      mul_le_mul_of_nonneg_right hxlo.le hrn4
                  _ ≤ x * (muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x)) :=
                      mul_le_mul_of_nonneg_left h1 hxpos.le
            _ = (muF (2 / Real.pi) a x / (1 + muF (2 / Real.pi) a x)) * x := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hmax hrn
      refine le_trans ?_ key
      apply mul_le_mul_of_nonneg_right _ h3
      exact div_le_div_of_nonneg_right hcoef hn2.le

end Final

#print axioms cell_coercive_explicit2

end AdalyFormal.ScaledCoercivity

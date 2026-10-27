import PSC10e

/-!
# SC10f -- v2: a readable closed lower bound  `min(a,1)/1000 ≤ hfun2(a)`  and the resulting plain statement
`min(a,1)/1000 ‖x‖² ≤ ell^{2k} ⟨x, G₁⁻¹ x⟩`.  Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

theorem aff_lower {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (h : β + γ ≤ 1000 * α)
    (a : ℝ) (ha : 0 < a) : min a 1 / 1000 ≤ α * a / (β + γ * a) := by
  have hd : 0 < β + γ * a := by positivity
  rw [le_div_iff₀ hd]
  rcases le_total a 1 with h1 | h1
  · rw [min_eq_left h1]
    nlinarith [mul_le_mul_of_nonneg_left h1 hγ.le]
  · rw [min_eq_right h1]
    have : β + γ * a ≤ (β + γ) * a := by nlinarith
    nlinarith

theorem hfun2_ge (a : ℝ) (ha : 0 < a) : min a 1 / 1000 ≤ hfun2 a := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hg : (0.0264 : ℝ) ≤ (2 / Real.pi) ^ 8 := by
    have h1 : (40 / 63 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ hpi0]; nlinarith
    have h2 : ((40 / 63 : ℝ)) ^ 8 ≤ (2 / Real.pi) ^ 8 := pow_le_pow_left₀ (by norm_num) h1 8
    have h3 : (0.0264 : ℝ) ≤ (40 / 63) ^ 8 := by norm_num
    linarith
  have hg1 : (2 / Real.pi) ^ 8 ≤ 1 := by
    have : 2 / Real.pi ≤ 1 := by rw [div_le_one hpi0]; linarith
    exact pow_le_one₀ (by positivity) this
  have hpisq : Real.pi ^ 2 ≤ 9.93 := by nlinarith
  have hpisq0 : 0 < Real.pi ^ 2 := by positivity
  set g : ℝ := (2 / Real.pi) ^ 8 with hgdef
  have hgpos : 0 < g := by positivity
  unfold hfun2 cS2 cL2
  refine le_min ?_ (le_min ?_ ?_)
  · set L : ℝ := LmF (15 / 16) a with hL
    set g' : ℝ := (15 / 16 : ℝ) ^ 8 with hg'
    have hg'1 : (0.596 : ℝ) ≤ g' := by rw [hg']; norm_num
    have hg'2 : g' ≤ 0.597 := by rw [hg']; norm_num
    have hL1 : L ≤ a * g' / 4 := min_le_left _ _
    have hL2 : L ≤ 4 * g' / (4 + g') := min_le_right _ _
    have hL2' : 4 * g' / (4 + g') ≤ 0.52 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hLlow : min a 1 * 0.149 ≤ L := by
      refine le_min ?_ ?_
      · have : min a 1 ≤ a := min_le_left _ _
        nlinarith
      · have : min a 1 ≤ 1 := min_le_right _ _
        have h5 : (0.149 : ℝ) ≤ 4 * g' / (4 + g') := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        nlinarith
    have hmin0 : 0 < min a 1 := lt_min ha one_pos
    have hLpos : 0 < L := by nlinarith
    have hrat : (1 / 10 : ℝ) ≤ rat (muF (15 / 16) a L) := by
      rw [rat_muF ha (by norm_num) hLpos.le, ← hg', le_div_iff₀ (by positivity)]
      have e1 : L * (1 + a / 4) = L + L * a / 4 := by ring
      have e2 : L * a / 4 ≤ 0.52 * a / 4 := by nlinarith
      nlinarith
    calc min a 1 / 1000 ≤ min a 1 * 0.149 / 10 := by nlinarith
      _ ≤ L / 10 := by linarith
      _ ≤ rat (muF (15 / 16) a L) * L := by nlinarith
  · have e := rat_muF (σ := 2 / Real.pi) (a := a) (y := 3 * Real.pi ^ 2) ha (by positivity) (by positivity)
    have h := aff_lower (α := 4 * g) (β := 3 * Real.pi ^ 2) (γ := 3 * Real.pi ^ 2 / 4 + 1 + g)
      (by positivity) (by positivity) (by positivity) (by linarith) a ha
    have e2 : 4 * rat (muF (2 / Real.pi) a (3 * Real.pi ^ 2))
        = 4 * g * a / (3 * Real.pi ^ 2 + (3 * Real.pi ^ 2 / 4 + 1 + g) * a) := by
      rw [e, ← hgdef]
      have : 0 < 3 * Real.pi ^ 2 * (1 + a / 4) + a + a * g := by positivity
      have : 0 < 3 * Real.pi ^ 2 + (3 * Real.pi ^ 2 / 4 + 1 + g) * a := by positivity
      field_simp
      ring
    rw [e2]; exact h
  · have e := rat_muF (σ := 2 / Real.pi) (a := a) (y := 4) ha (by positivity) (by norm_num)
    have hα : 6 + g ≤ 1000 * (4 / Real.pi ^ 2 * g) := by
      have h1 : 4 / 9.93 ≤ 4 / Real.pi ^ 2 := div_le_div_of_nonneg_left (by norm_num) hpisq0 hpisq
      have h2 : 4 / 9.93 * g ≤ 4 / Real.pi ^ 2 * g := mul_le_mul_of_nonneg_right h1 hgpos.le
      nlinarith
    have h := aff_lower (α := 4 / Real.pi ^ 2 * g) (β := 4) (γ := 2 + g)
      (by positivity) (by norm_num) (by positivity) (by linarith) a ha
    have e2 : 4 / Real.pi ^ 2 * rat (muF (2 / Real.pi) a 4)
        = 4 / Real.pi ^ 2 * g * a / (4 + (2 + g) * a) := by
      rw [e, ← hgdef]
      have : 0 < 4 * (1 + a / 4) + a + a * g := by positivity
      have : 0 < 4 + (2 + g) * a := by positivity
      field_simp
      ring
    rw [e2]; exact h

theorem scaled_G1inv2_simple (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)) :
    min a 1 / 1000 * ‖x‖ ^ 2 ≤ (ell : ℝ) ^ (2 * k) * inner ℝ x ((PK ell k Lu hell a Lam).G1inv x) :=
  le_trans (mul_le_mul_of_nonneg_right (hfun2_ge a ha) (by positivity)) (scaled_G1inv2 ell k hell a ha Lu Lam x)

#print axioms hfun2_ge
#print axioms scaled_G1inv2_simple

end AdalyFormal.ScaledCoercivity

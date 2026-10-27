import CB8
/-!
# NB3 -- sharp small-angle comparison `‖log g‖_F ≤ dv g + (dv g)³/8` (for `dv g ≤ 1`)

Needed so that converting between plaquette defects and their logarithms costs a factor `1 + O(dv²)`
instead of the crude `π/2` of CMP98 (25) (which would compound per level).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Angle)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

theorem log_le_dv (g : SU2) (h : dv g ≤ 1) : frobNorm (su2Log g) ≤ dv g + dv g ^ 3 / 8 := by
  have hlog := AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_su2Log_le g
  have hdv : dv g = 2 * Real.sqrt 2 * Real.sin (su2Angle g / 2) :=
    AdalyFormal.Balaban.BlockingLinkEstimate.frobNorm_sub_one_eq g
  obtain ⟨hlo, hhi⟩ := AdalyFormal.Balaban.SuTwoLogExp.su2Angle_mem g
  set x := su2Angle g / 2
  have hx0 : 0 ≤ x := by simp only [x]; linarith
  have hxpi : x ≤ Real.pi / 2 := by simp only [x]; linarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2b : Real.sqrt 2 > 1.41 := by
    rw [gt_iff_lt, show (1.41 : ℝ) = Real.sqrt (1.41 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have hj : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx0 hxpi
  set sn := Real.sin x
  have hsn0 : 0 ≤ sn := le_trans (by positivity) hj
  -- x ≤ (π/2) sn
  have hxs : x ≤ Real.pi / 2 * sn := by
    have := mul_le_mul_of_nonneg_left hj (le_of_lt (by positivity : (0:ℝ) < Real.pi / 2))
    have e : Real.pi / 2 * (2 / Real.pi * x) = x := by field_simp
    linarith
  -- sn ≤ 1/(2√2) < 0.36, so x < 0.57 ≤ 1
  have hsn : 2 * Real.sqrt 2 * sn ≤ 1 := by rw [← hdv]; exact h
  have hsn' : sn ≤ 0.36 := by nlinarith
  have hx1 : x ≤ 1 := by nlinarith
  -- x - x³/4 ≤ sn
  have hcube : x - x ^ 3 / 4 ≤ sn := by
    rcases eq_or_lt_of_le hx0 with h0 | h0
    · rw [← h0]; simp [sn, ← h0]
    · exact le_of_lt (Real.sin_gt_sub_cube h0 hx1)
  have hx3 : x ^ 3 ≤ (Real.pi / 2) ^ 3 * sn ^ 3 := by
    have := pow_le_pow_left₀ hx0 hxs 3
    rwa [mul_pow] at this
  have hpc : (Real.pi / 2) ^ 3 ≤ 3.91 := by
    have ht := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.pi / 2)
      (by linarith : Real.pi / 2 ≤ 1.575) 3
    have : (1.575 : ℝ) ^ 3 ≤ 3.91 := by norm_num
    linarith
  have hsn3 : 0 ≤ sn ^ 3 := by positivity
  -- ‖log g‖ ≤ √2 θ = 2√2 x ≤ 2√2 (sn + x³/4)
  have hθ : su2Angle g = 2 * x := by simp only [x]; ring
  rw [hθ] at hlog
  have key : x ≤ sn + 3.91 / 4 * sn ^ 3 := by nlinarith
  rw [hdv]
  have e3 : (2 * Real.sqrt 2 * sn) ^ 3 / 8 = 2 * Real.sqrt 2 * sn ^ 3 := by
    have : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      rw [pow_succ, sq, hss]
    rw [mul_pow, mul_pow, this]; ring
  rw [e3]
  have : Real.sqrt 2 * (2 * x) ≤ 2 * Real.sqrt 2 * sn + 2 * Real.sqrt 2 * sn ^ 3 := by
    nlinarith
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.log_le_dv

import NsOdd9a
import NsOdd7

/-!
# NsOdd9b -- the loops of the UNIT-level shape field are bounded by `|t|` (lane ncwdh_strong_20261017)

`unitFld t b d cu` is the shape field `D = Dfun cu 1 N₀`, `T = b·[· = cu]`, `Ef = 0`, `a ≡ d`, `p = 0` on a torus; its stride-1,
block-`ell` staircase loops are `t σ(y₁) ·` (an explicit bounded expression).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq UbarTower UbarTower_succ UbarTower_zero)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

noncomputable def unitFld (t b d : ℝ) (cu : ℕ) : PeriodicLatticeEdge L → ℝ :=
  shapeFld t (fun v => Dfun cu 1 (L 0 + 1) v) (fun v => b * (if v = cu then 1 else 0)) (fun _ => 0) (fun _ _ => d) (fun _ _ => 0)

theorem sum_pm_const (n : ℕ) (T : ℝ) : ∑ j ∈ Finset.range n, pmN j * T = ((n % 2 : ℕ) : ℝ) * T := by
  rw [← Finset.sum_mul, sum_pmN]

theorem unit_loop_dir1 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (cu : ℕ) (t b d : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1 / 2)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y 1 ell) :
    |loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 1 x| ≤ |t| := by
  have hell : 0 < ell := by omega
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts (Nat.one_pos) hx
  have hX1 : ((y 1).val + 1 * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + 1 * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + 1 * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hsx : sgnNat (x 1).val = sgnNat (y 1).val * pmN n1 := by
    rw [← hX1]; exact sgn_shift (L 1 + 1) hN 1 (y 1).val n1 (by norm_num)
  have hsy : sgnNat (((y 1).val + 1 * ell) % (L 1 + 1)) = - sgnNat (y 1).val := by
    rw [sgn_shift (L 1 + 1) hN 1 (y 1).val ell (by norm_num), pmN_odd hO]; ring
  have hDs : ∑ i ∈ Finset.range n0, Dfun cu 1 (L 0 + 1) (((y 0).val + 1 * i) % (L 0 + 1)) =
      (if (y 0).val = cu then (1 : ℝ) else 0) - (if (x 0).val = cu then (1 : ℝ) else 0) := by
    rw [Dsum_tel cu 1 (L 0 + 1) (y 0).val n0 (Nat.succ_pos _), Nat.mod_eq_of_lt (y 0).isLt, hX0]
  have hpm : ∑ j ∈ Finset.range ell, pmN j = 1 := by rw [sum_pmN, hO]; norm_num
  have heq : loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 1 x = t * sgnNat (y 1).val *
      (2 * (((n1 % 2 : ℕ)) : ℝ) * (b * (if (y 0).val = cu then 1 else 0)) + pmN n1 * (b * (if (x 0).val = cu then 1 else 0))
        - b * (if (y 0).val = cu then 1 else 0) +
       pmN n1 * ((if (y 0).val = cu then (1 : ℝ) else 0) - (if (x 0).val = cu then (1 : ℝ) else 0)) * (d + d)) := by
    unfold unitFld
    rw [loop_shape_dir1 hN 1 ell (by norm_num) t _ _ _ _ _ y x]
    simp only [c1, c0, c2, hX1, hX2, hDs, hsx, hsy, mul_zero, add_zero]
    simp only [sum_pm_const, hO]; push_cast; ring
  have hbd := unit1_real b d (if (y 0).val = cu then 1 else 0) (if (x 0).val = cu then 1 else 0) (pmN n1) (((n1 % 2 : ℕ)) : ℝ) hb hd
    (ind_cases _ _) (ind_cases _ _) (by rcases pmN_cases n1 with h | h <;> [left; right] <;> exact ⟨h.1, h.2⟩)
  rw [heq, abs_mul, abs_mul, sgnNat_abs, mul_one, mul_comm]
  have h1 : |2 * (((n1 % 2 : ℕ)) : ℝ) * (b * (if (y 0).val = cu then 1 else 0)) + pmN n1 * (b * (if (x 0).val = cu then 1 else 0))
        - b * (if (y 0).val = cu then 1 else 0) +
       pmN n1 * ((if (y 0).val = cu then (1 : ℝ) else 0) - (if (x 0).val = cu then (1 : ℝ) else 0)) * (d + d)| ≤ 1 := by
    have := hbd
    convert this using 2
  exact mul_le_of_le_one_left (abs_nonneg t) h1


theorem unit_loop_dir2 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (cu : ℕ) (t b d : ℝ)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y 1 ell) :
    loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 2 x = 0 := by
  unfold unitFld
  rw [loop_shape_dir2 hN 1 ell (by norm_num) t _ _ _ _ _ y x]
  simp

theorem unit_loop_dir0 (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (cu : ℕ) (t b d : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1 / 2)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y 1 ell) :
    |loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 0 x| ≤ |t| := by
  have hell : 0 < ell := by omega
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts (Nat.one_pos) hx
  have hN0 : 0 < L 0 + 1 := Nat.succ_pos _
  have hX1 : ((y 1).val + 1 * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + 1 * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + 1 * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hsx : sgnNat (x 1).val = sgnNat (y 1).val * pmN n1 := by
    rw [← hX1]; exact sgn_shift (L 1 + 1) hN 1 (y 1).val n1 (by norm_num)
  have hDs : ∑ i ∈ Finset.range n0, Dfun cu 1 (L 0 + 1) (((y 0).val + 1 * i) % (L 0 + 1)) =
      (if (y 0).val = cu then (1 : ℝ) else 0) - (if (x 0).val = cu then (1 : ℝ) else 0) := by
    rw [Dsum_tel cu 1 (L 0 + 1) (y 0).val n0 hN0, Nat.mod_eq_of_lt (y 0).isLt, hX0]
  have hDs' : ∑ i ∈ Finset.range n0, Dfun cu 1 (L 0 + 1) (((((y 0).val + 1 * ell) % (L 0 + 1)) + 1 * i) % (L 0 + 1)) =
      (if ((y 0).val + 1 * ell) % (L 0 + 1) = cu then (1 : ℝ) else 0) - (if ((x 0).val + 1 * ell) % (L 0 + 1) = cu then (1 : ℝ) else 0) := by
    have : ∀ i, ((((y 0).val + 1 * ell) % (L 0 + 1)) + 1 * i) % (L 0 + 1) = ((y 0).val + 1 * ell + 1 * i) % (L 0 + 1) := by
      intro i; rw [Nat.mod_add_mod]
    simp only [this]
    rw [Dsum_tel cu 1 (L 0 + 1) ((y 0).val + 1 * ell) n0 hN0]
    have : (y 0).val + 1 * ell + 1 * n0 = (x 0).val + 1 * ell := by rw [hx0]; ring
    rw [this]
  have hDx : ∑ j ∈ Finset.range ell, Dfun cu 1 (L 0 + 1) (((x 0).val + 1 * j) % (L 0 + 1)) =
      (if (x 0).val = cu then (1 : ℝ) else 0) - (if ((x 0).val + 1 * ell) % (L 0 + 1) = cu then (1 : ℝ) else 0) := by
    rw [Dsum_tel cu 1 (L 0 + 1) (x 0).val ell hN0, Nat.mod_eq_of_lt (x 0).isLt]
  have hDy : ∑ j ∈ Finset.range ell, Dfun cu 1 (L 0 + 1) (((y 0).val + 1 * j) % (L 0 + 1)) =
      (if (y 0).val = cu then (1 : ℝ) else 0) - (if ((y 0).val + 1 * ell) % (L 0 + 1) = cu then (1 : ℝ) else 0) := by
    rw [Dsum_tel cu 1 (L 0 + 1) (y 0).val ell hN0, Nat.mod_eq_of_lt (y 0).isLt]
  set X : ℝ := (if (y 0).val = cu then (1 : ℝ) else 0) - (if ((y 0).val + 1 * ell) % (L 0 + 1) = cu then (1 : ℝ) else 0) with hXdef
  have heq : loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 0 x = t * sgnNat (y 1).val *
      (((n1 % 2 : ℕ) : ℝ) * (b * X) + X * (pmN n1 * d - d)) := by
    unfold unitFld
    rw [loop_shape_dir0 hN 1 ell (by norm_num) t _ _ _ _ _ y x]
    simp only [c1, c0, c2, hX1, hX2, hDs, hDs', hDx, hDy, hsx, mul_zero, add_zero, Nat.mod_eq_of_lt (y 0).isLt]
    simp only [sum_pm_const, hXdef]
    ring
  have hXr : X = -1 ∨ X = 0 ∨ X = 1 := by
    rw [hXdef]
    rcases ind_cases (y 0).val cu with h | h <;> rcases ind_cases (((y 0).val + 1 * ell) % (L 0 + 1)) cu with h' | h' <;> rw [h, h'] <;> norm_num
  have hbd := unit0_real b d X (((n1 % 2 : ℕ)) : ℝ) (pmN n1) hb hd hXr (by rcases pmN_cases n1 with h | h <;> [left; right] <;> exact ⟨h.1, h.2⟩)
  rw [heq, abs_mul, abs_mul, sgnNat_abs, mul_one, mul_comm]
  exact mul_le_of_le_one_left (abs_nonneg t) (by convert hbd using 2)

/-- every loop of the unit-level shape field is bounded by `|t|`. -/
theorem unitFld_loop_le (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (cu : ℕ) (t b d : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1 / 2) :
    ∀ cc : PeriodicLatticeEdge L, ∀ x ∈ stepBlockOf cc.1 1 ell, |loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) cc.1 cc.2 x| ≤ |t| := by
  intro cc x hx
  obtain ⟨y, μ⟩ := cc
  fin_cases μ
  · exact unit_loop_dir0 hN hO cu t b d hb hd y x hx
  · exact unit_loop_dir1 hN hO cu t b d hb hd y x hx
  · have h := unit_loop_dir2 hN hO cu t b d y x hx
    show |loopAngG 1 ell (unitFld t b d cu : PeriodicLatticeEdge L → ℝ) y 2 x| ≤ |t|
    rw [h]; simp

#print axioms unitFld_loop_le

end AdalyFormal.CoverOmega

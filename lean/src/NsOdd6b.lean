import NsOdd6a

/-!
# NsOdd6b -- the level-1 loops of `phi1o` at stride `ell`: instantiation of the shape formulas and the bound `(1 + 6(ell-1)/ell²)|t|` (lane ncwdh_strong_20261017)
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
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- the coordinates of a block member: `x = y + s n`, `n < ell`, and the staircase step counts are `n`. -/
theorem block_facts {s ell : ℕ} (hs : 0 < s) {y x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    ∃ n0 n1 n2 : ℕ, n0 < ell ∧ n1 < ell ∧ n2 < ell ∧ (x 0).val = (y 0).val + s * n0 ∧ (x 1).val = (y 1).val + s * n1 ∧
      (x 2).val = (y 2).val + s * n2 ∧ ((x 1 - (Function.update y 2 (x 2)) 1).val) / s = n1 ∧
      ((x 0 - (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0).val) / s = n0 ∧ ((x 2 - y 2).val) / s = n2 := by
  have hm := mem_stepBlockOf.mp hx
  have key : ∀ μ : Fin 3, ∃ n : ℕ, n < ell ∧ (x μ).val = (y μ).val + s * n ∧ ((x μ - y μ).val) / s = n := by
    intro μ
    obtain ⟨h1, h2, ⟨q, hq⟩⟩ := hm μ
    have hle : y μ ≤ x μ := by rw [Fin.le_def]; exact h1
    have hsub : (x μ - y μ).val = (x μ).val - (y μ).val := Fin.coe_sub_iff_le.mpr hle
    refine ⟨q, ?_, by omega, ?_⟩
    · by_contra hc
      push Not at hc
      have : s * ell ≤ s * q := Nat.mul_le_mul_left s hc
      omega
    · rw [hsub, hq]; exact Nat.mul_div_cancel_left q hs
  obtain ⟨n0, h0, e0, d0⟩ := key 0
  obtain ⟨n1, h1, e1, d1⟩ := key 1
  obtain ⟨n2, h2, e2, d2⟩ := key 2
  refine ⟨n0, n1, n2, h0, h1, h2, e0, e1, e2, ?_, ?_, d2⟩
  · have : (Function.update y 2 (x 2)) 1 = y 1 := by simp [Function.update_of_ne]
    rw [this]; exact d1
  · have : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by simp [Function.update_of_ne]
    rw [this]; exact d0

theorem sum_pm_TE (n : ℕ) (T E : ℝ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, pmN j * (T + E * f j) = ((n % 2 : ℕ) : ℝ) * T + E * ∑ j ∈ Finset.range n, pmN j * f j := by
  have : ∀ j ∈ Finset.range n, pmN j * (T + E * f j) = pmN j * T + E * (pmN j * f j) := fun j _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, sum_pmN, ← Finset.mul_sum]

theorem pmN_cases (n : ℕ) : (pmN n = 1 ∧ ((n % 2 : ℕ) : ℝ) = 0) ∨ (pmN n = -1 ∧ ((n % 2 : ℕ) : ℝ) = 1) := by
  unfold pmN
  by_cases h : n % 2 = 0
  · left; simp [h]
  · right; have : n % 2 = 1 := by omega
    simp [h, this]

theorem pmN_odd {ell : ℕ} (hO : ell % 2 = 1) : pmN ell = -1 := by
  unfold pmN; simp [hO]

/-- **direction 1 loop of `phi1o`** (normalised). -/
theorem loop_phi1o_dir1_eq (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (hell : 0 < ell) (t : ℝ)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    ∃ n0 n1 n2 : ℕ, n0 < ell ∧ n1 < ell ∧ n2 < ell ∧ (x 0).val = (y 0).val + ell * n0 ∧ (x 1).val = (y 1).val + ell * n1 ∧
      loopAngG ell ell (phi1o L c ell t) y 1 x = t * sgnNat (y 1).val *
        ((2 * ((n1 % 2 : ℕ) : ℝ) * (if (y 0).val = c then 1 else 0) + pmN n1 * (if (x 0).val = c then 1 else 0) - (if (y 0).val = c then 1 else 0) +
            pmN n1 * ((if (y 0).val = c then 1 else 0) - (if (x 0).val = c then 1 else 0)) *
              (aAmp L ell (x 1).val (x 2).val + aAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * n1) % (L 1 + 1)) (x 2).val)) +
         (Efun c ell (y 0).val *
              (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val +
               ∑ j ∈ Finset.range n1, pmN j * pAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * j) % (L 1 + 1)) (x 2).val -
               ∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (y 2).val) +
          pmN n1 * Efun c ell (x 0).val * ∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((x 1).val + ell * j) % (L 1 + 1)) (x 2).val)) := by
  have hs := hO
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts hell hx
  refine ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, ?_⟩
  have hX1 : ((y 1).val + ell * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + ell * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + ell * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hsx : sgnNat (x 1).val = sgnNat (y 1).val * pmN n1 := by
    rw [← hX1]; exact sgn_shift (L 1 + 1) hN ell (y 1).val n1 hs
  have hsy : sgnNat (((y 1).val + ell * ell) % (L 1 + 1)) = - sgnNat (y 1).val := by
    rw [sgn_shift (L 1 + 1) hN ell (y 1).val ell hs, pmN_odd hO]; ring
  have hDs : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) (((y 0).val + ell * i) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val n0 (Nat.succ_pos _), Nat.mod_eq_of_lt (y 0).isLt, hX0]
  rw [phi1o_eq_shape, loop_shape_dir1 hN ell ell hO t _ _ _ _ _ y x]
  simp only [c1, c0, c2, hX1, hX2, hDs, hsx, hsy]
  rw [sum_pm_TE, sum_pm_TE, sum_pm_TE, sum_pm_TE]
  rw [hO]
  push_cast
  ring

theorem ind_cases (v c : ℕ) : (if v = c then (1 : ℝ) else 0) = 0 ∨ (if v = c then (1 : ℝ) else 0) = 1 := by
  by_cases h : v = c <;> simp [h]

theorem loop_phi1o_dir1_bound (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (h2 : 2 ≤ ell) (hbig : ell * ell + ell < L 1 + 1)
    (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    |loopAngG ell ell (phi1o L c ell t) y 1 x| ≤ (1 + 3 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| := by
  have hell : 0 < ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast h2
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, heq⟩ := loop_phi1o_dir1_eq hN hO c hell t y x hx
  rw [heq]
  set W := ((2 * ((n1 % 2 : ℕ) : ℝ) * (if (y 0).val = c then 1 else 0) + pmN n1 * (if (x 0).val = c then 1 else 0) - (if (y 0).val = c then 1 else 0) +
            pmN n1 * ((if (y 0).val = c then 1 else 0) - (if (x 0).val = c then 1 else 0)) *
              (aAmp L ell (x 1).val (x 2).val + aAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * n1) % (L 1 + 1)) (x 2).val)) +
         (Efun c ell (y 0).val *
              (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val +
               ∑ j ∈ Finset.range n1, pmN j * pAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * j) % (L 1 + 1)) (x 2).val -
               ∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (y 2).val) +
          pmN n1 * Efun c ell (x 0).val * ∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((x 1).val + ell * j) % (L 1 + 1)) (x 2).val)) with hW
  have hmod : ∀ j, (((y 1).val + ell * ell) % (L 1 + 1) + ell * j) % (L 1 + 1) = ((y 1).val + ell * ell + ell * j) % (L 1 + 1) := by
    intro j; rw [Nat.mod_add_mod]
  have hA : 2 * (((ell : ℝ) - 1) / (2 * ell)) ≤ 1 := by
    have hl0 : (0 : ℝ) < ell := by linarith
    rw [← mul_div_assoc, div_le_one (by positivity)]; nlinarith
  have hbound := loop1_real (if (y 0).val = c then 1 else 0) (if (x 0).val = c then 1 else 0)
    ((if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0))
    (Efun c ell (y 0).val) (Efun c ell (x 0).val)
    (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val)
    (∑ j ∈ Finset.range n1, pmN j * pAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * j) % (L 1 + 1)) (x 2).val)
    (∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((x 1).val + ell * j) % (L 1 + 1)) (x 2).val)
    (∑ j ∈ Finset.range ell, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (y 2).val)
    (aAmp L ell (x 1).val (x 2).val) (aAmp L ell ((((y 1).val + ell * ell) % (L 1 + 1) + ell * n1) % (L 1 + 1)) (x 2).val)
    (pmN n1) ((n1 % 2 : ℕ) : ℝ) (((ell : ℝ) - 1) / (2 * ell)) ((ell : ℝ) - 1) (2 / (ell : ℝ) ^ 2)
    (ind_cases _ _) (ind_cases _ _) rfl (pmN_cases n1)
    (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) hA
    (Efun_abs_le h2 _) (Efun_abs_le h2 _)
    (altP_bound hO hell hbig (y 1).val n1 (x 2).val hn1.le)
    (by
      have := altP_bound (L := L) hO hell hbig ((y 1).val + ell * ell) n1 (x 2).val hn1.le
      simpa [hmod] using this)
    (by
      have := altP_bound (L := L) hO hell hbig (x 1).val ell (x 2).val le_rfl
      exact this)
    (altP_bound hO hell hbig (y 1).val ell (y 2).val le_rfl)
    (by
      intro h0 hxc
      by_contra hne
      have h1 := Efun_ne_zero hell hne
      have : (y 0).val = c := by by_contra hh; simp [hh] at h0
      have hxc' : ¬ (x 0).val = c := by intro hh; simp [hh] at hxc
      omega)
    (by
      intro h0 hxc
      by_contra hne
      have h1 := Efun_ne_zero hell hne
      have hxc' : (x 0).val = c := by by_contra hh; simp [hh] at hxc
      have hyc : ¬ (y 0).val = c := by intro hh; simp [hh] at h0
      have : 1 ≤ n0 := by
        rcases Nat.eq_zero_or_pos n0 with hz | hz
        · rw [hz] at hx0; omega
        · exact hz
      have : ell ≤ ell * n0 := Nat.le_mul_of_pos_right ell this
      omega)
    (by linarith) (by positivity)
    (by
      rw [mul_div_assoc', div_le_one (by positivity)]
      nlinarith)
  rw [abs_mul, abs_mul]
  have hsg := sgnNat_abs (y 1).val
  rw [hsg, mul_one]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg t)

/-- **direction 2 loop of `phi1o`**. -/
theorem loop_phi1o_dir2_bound (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (h2 : 2 ≤ ell) (hbig : ell * ell + ell < L 1 + 1)
    (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    |loopAngG ell ell (phi1o L c ell t) y 2 x| ≤ (1 + 3 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| := by
  have hell : 0 < ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast h2
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts hell hx
  have hX1 : ((y 1).val + ell * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + ell * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + ell * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hDs : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) (((y 0).val + ell * i) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val n0 (Nat.succ_pos _), Nat.mod_eq_of_lt (y 0).isLt, hX0]
  rw [phi1o_eq_shape, loop_shape_dir2 hN ell ell hO t _ _ _ _ _ y x]
  simp only [c1, c0, c2, hX1, hX2, hDs]
  rw [sum_pm_TE, sum_pm_TE]
  have hA : 2 * (((ell : ℝ) - 1) / (2 * ell)) ≤ 1 := by
    have hl0 : (0 : ℝ) < ell := by linarith
    rw [← mul_div_assoc, div_le_one (by positivity)]; nlinarith
  have hbound := loop2_real ((if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0))
    (Efun c ell (y 0).val)
    (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val)
    (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)))
    (aAmp L ell (x 1).val (x 2).val) (aAmp L ell (x 1).val ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)))
    (pmN n1) (((ell : ℝ) - 1) / (2 * ell)) ((ell : ℝ) - 1) (2 / (ell : ℝ) ^ 2)
    (by
      rcases ind_cases (y 0).val c with h | h <;> rcases ind_cases (x 0).val c with h' | h' <;> rw [h, h'] <;> norm_num)
    (by rcases pmN_cases n1 with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h])
    (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) hA
    (Efun_abs_le h2 _)
    (altP_bound hO hell hbig (y 1).val n1 (x 2).val hn1.le)
    (altP_bound hO hell hbig (y 1).val n1 _ hn1.le)
    (by linarith) (by positivity)
  calc _ = |t * sgnNat (y 1).val * (Efun c ell (y 0).val *
        ((∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val) -
          (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)))) +
        pmN n1 * ((if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0)) *
          (aAmp L ell (x 1).val (x 2).val - aAmp L ell (x 1).val ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1))))| := by
        congr 1; ring
    _ ≤ (1 + 3 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| := by
        rw [abs_mul, abs_mul, sgnNat_abs, mul_one, mul_comm]
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg t)

/-- **direction 0 loop of `phi1o`**. -/
theorem loop_phi1o_dir0_bound (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (h2 : 2 ≤ ell) (hbig : ell * ell + ell < L 1 + 1)
    (c : ℕ) (hc3 : c + ell * ell < L 0 + 1) (t : ℝ) (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    |loopAngG ell ell (phi1o L c ell t) y 0 x| ≤ (1 + 3 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| := by
  have hell : 0 < ell := by omega
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast h2
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts hell hx
  have hX1 : ((y 1).val + ell * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + ell * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + ell * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hsx : sgnNat (x 1).val = sgnNat (y 1).val * pmN n1 := by
    rw [← hX1]; exact sgn_shift (L 1 + 1) hN ell (y 1).val n1 hO
  have hN0 : 0 < L 0 + 1 := Nat.succ_pos _
  have hDs : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) (((y 0).val + ell * i) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val n0 hN0, Nat.mod_eq_of_lt (y 0).isLt, hX0]
  have hDs' : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) ((((y 0).val + ell * ell) % (L 0 + 1) + ell * i) % (L 0 + 1)) =
      (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) - (if ((x 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    have : ∀ i, (((y 0).val + ell * ell) % (L 0 + 1) + ell * i) % (L 0 + 1) = ((y 0).val + ell * ell + ell * i) % (L 0 + 1) := by
      intro i; rw [Nat.mod_add_mod]
    simp only [this]
    rw [Dsum_tel c ell (L 0 + 1) ((y 0).val + ell * ell) n0 hN0]
    have : (y 0).val + ell * ell + ell * n0 = (x 0).val + ell * ell := by rw [hx0]; ring
    rw [this]
  have hDx : ∑ j ∈ Finset.range ell, Dfun c ell (L 0 + 1) (((x 0).val + ell * j) % (L 0 + 1)) =
      (if (x 0).val = c then (1 : ℝ) else 0) - (if ((x 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (x 0).val ell hN0, Nat.mod_eq_of_lt (x 0).isLt]
  have hDy : ∑ j ∈ Finset.range ell, Dfun c ell (L 0 + 1) (((y 0).val + ell * j) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val ell hN0, Nat.mod_eq_of_lt (y 0).isLt]
  rw [phi1o_eq_shape, loop_shape_dir0 hN ell ell hO t _ _ _ _ _ y x]
  simp only [c1, c0, c2, hX1, hX2, hDs, hDs', hDx, hDy, hsx]
  rw [sum_pm_TE, sum_pm_TE]
  have hA : 2 * (((ell : ℝ) - 1) / (2 * ell)) ≤ 1 := by
    have hl0 : (0 : ℝ) < ell := by linarith
    rw [← mul_div_assoc, div_le_one (by positivity)]; nlinarith
  have hEd : |Efun c ell (y 0).val - Efun c ell (((y 0).val + ell * ell) % (L 0 + 1))| ≤ (ell : ℝ) - 1 := by
    by_cases h0 : Efun c ell (y 0).val = 0
    · rw [h0, zero_sub, abs_neg]; exact Efun_abs_le h2 _
    · have h1 := Efun_ne_zero hell h0
      have hlt : (y 0).val + ell * ell < L 0 + 1 := by omega
      have hmod : ((y 0).val + ell * ell) % (L 0 + 1) = (y 0).val + ell * ell := Nat.mod_eq_of_lt hlt
      have h2' : Efun c ell (((y 0).val + ell * ell) % (L 0 + 1)) = 0 := by
        by_contra hne
        have h3 := Efun_ne_zero hell hne
        rw [hmod] at h3
        have : ell * ell ≥ 2 * ell := Nat.mul_le_mul_right ell h2
        omega
      rw [h2', sub_zero]; exact Efun_abs_le h2 _
  have hbound := loop0_real
    ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0))
    (Efun c ell (y 0).val - Efun c ell (((y 0).val + ell * ell) % (L 0 + 1)))
    (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val)
    (aAmp L ell (x 1).val (x 2).val) (aAmp L ell (y 1).val (y 2).val) (pmN n1) ((n1 % 2 : ℕ) : ℝ)
    (((ell : ℝ) - 1) / (2 * ell)) ((ell : ℝ) - 1) (2 / (ell : ℝ) ^ 2)
    (by
      rcases ind_cases (y 0).val c with h | h <;> rcases ind_cases (((y 0).val + ell * ell) % (L 0 + 1)) c with h' | h' <;> rw [h, h'] <;> norm_num)
    (pmN_cases n1)
    (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) (aAmp_nonneg ell _ _) (aAmp_le hO hell _ _) hA
    hEd (altP_bound hO hell hbig (y 1).val n1 (x 2).val hn1.le) (by linarith) (by positivity)
  calc _ = |t * sgnNat (y 1).val * (((n1 % 2 : ℕ) : ℝ) *
          ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) +
        (Efun c ell (y 0).val - Efun c ell (((y 0).val + ell * ell) % (L 0 + 1))) *
          (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val) +
        ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) *
          (pmN n1 * aAmp L ell (x 1).val (x 2).val - aAmp L ell (y 1).val (y 2).val))| := by
        congr 1; ring
    _ ≤ (1 + 3 * ((ell : ℝ) - 1) * (2 / (ell : ℝ) ^ 2)) * |t| := by
        rw [abs_mul, abs_mul, sgnNat_abs, mul_one, mul_comm]
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg t)

/-- **direction 2 loop of `phi1o`: exact normalised form.** -/
theorem loop_phi1o_dir2_eq (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (hell : 0 < ell) (t : ℝ)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    ∃ n0 n1 n2 : ℕ, n0 < ell ∧ n1 < ell ∧ n2 < ell ∧ (x 0).val = (y 0).val + ell * n0 ∧ (x 1).val = (y 1).val + ell * n1 ∧
      (x 2).val = (y 2).val + ell * n2 ∧
      loopAngG ell ell (phi1o L c ell t) y 2 x = t * sgnNat (y 1).val *
        (Efun c ell (y 0).val *
            ((∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val) -
              (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)))) +
          pmN n1 * ((if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0)) *
            (aAmp L ell (x 1).val (x 2).val - aAmp L ell (x 1).val ((((y 2).val + ell * ell) % (L 2 + 1) + ell * n2) % (L 2 + 1)))) := by
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts hell hx
  refine ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, ?_⟩
  have hX1 : ((y 1).val + ell * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + ell * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + ell * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hDs : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) (((y 0).val + ell * i) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val n0 (Nat.succ_pos _), Nat.mod_eq_of_lt (y 0).isLt, hX0]
  rw [phi1o_eq_shape, loop_shape_dir2 hN ell ell hO t _ _ _ _ _ y x]
  simp only [c1, c0, c2, hX1, hX2, hDs]
  rw [sum_pm_TE, sum_pm_TE]
  ring

/-- **direction 0 loop of `phi1o`: exact normalised form.** -/
theorem loop_phi1o_dir0_eq (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (hell : 0 < ell) (t : ℝ)
    (y x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf y ell ell) :
    ∃ n0 n1 n2 : ℕ, n0 < ell ∧ n1 < ell ∧ n2 < ell ∧ (x 0).val = (y 0).val + ell * n0 ∧ (x 1).val = (y 1).val + ell * n1 ∧
      (x 2).val = (y 2).val + ell * n2 ∧
      loopAngG ell ell (phi1o L c ell t) y 0 x = t * sgnNat (y 1).val *
        (((n1 % 2 : ℕ) : ℝ) *
            ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) +
          (Efun c ell (y 0).val - Efun c ell (((y 0).val + ell * ell) % (L 0 + 1))) *
            (∑ j ∈ Finset.range n1, pmN j * pAmp L ell (((y 1).val + ell * j) % (L 1 + 1)) (x 2).val) +
          ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0)) *
            (pmN n1 * aAmp L ell (x 1).val (x 2).val - aAmp L ell (y 1).val (y 2).val)) := by
  obtain ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, c1, c0, c2⟩ := block_facts hell hx
  refine ⟨n0, n1, n2, hn0, hn1, hn2, hx0, hx1, hx2, ?_⟩
  have hX1 : ((y 1).val + ell * n1) % (L 1 + 1) = (x 1).val := by rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hX2 : ((y 2).val + ell * n2) % (L 2 + 1) = (x 2).val := by rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  have hX0 : ((y 0).val + ell * n0) % (L 0 + 1) = (x 0).val := by rw [← hx0]; exact Nat.mod_eq_of_lt (x 0).isLt
  have hsx : sgnNat (x 1).val = sgnNat (y 1).val * pmN n1 := by
    rw [← hX1]; exact sgn_shift (L 1 + 1) hN ell (y 1).val n1 hO
  have hN0 : 0 < L 0 + 1 := Nat.succ_pos _
  have hDs : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) (((y 0).val + ell * i) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if (x 0).val = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val n0 hN0, Nat.mod_eq_of_lt (y 0).isLt, hX0]
  have hDs' : ∑ i ∈ Finset.range n0, Dfun c ell (L 0 + 1) ((((y 0).val + ell * ell) % (L 0 + 1) + ell * i) % (L 0 + 1)) =
      (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) - (if ((x 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    have : ∀ i, (((y 0).val + ell * ell) % (L 0 + 1) + ell * i) % (L 0 + 1) = ((y 0).val + ell * ell + ell * i) % (L 0 + 1) := by
      intro i; rw [Nat.mod_add_mod]
    simp only [this]
    rw [Dsum_tel c ell (L 0 + 1) ((y 0).val + ell * ell) n0 hN0]
    have : (y 0).val + ell * ell + ell * n0 = (x 0).val + ell * ell := by rw [hx0]; ring
    rw [this]
  have hDx : ∑ j ∈ Finset.range ell, Dfun c ell (L 0 + 1) (((x 0).val + ell * j) % (L 0 + 1)) =
      (if (x 0).val = c then (1 : ℝ) else 0) - (if ((x 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (x 0).val ell hN0, Nat.mod_eq_of_lt (x 0).isLt]
  have hDy : ∑ j ∈ Finset.range ell, Dfun c ell (L 0 + 1) (((y 0).val + ell * j) % (L 0 + 1)) =
      (if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell * ell) % (L 0 + 1) = c then (1 : ℝ) else 0) := by
    rw [Dsum_tel c ell (L 0 + 1) (y 0).val ell hN0, Nat.mod_eq_of_lt (y 0).isLt]
  rw [phi1o_eq_shape, loop_shape_dir0 hN ell ell hO t _ _ _ _ _ y x]
  simp only [c1, c0, c2, hX1, hX2, hDs, hDs', hDx, hDy, hsx]
  rw [sum_pm_TE, sum_pm_TE]
  ring

end AdalyFormal.CoverOmega

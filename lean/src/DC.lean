import DB

/-!
# DC -- Lipschitz ramps and their window-smoothed versions (m1_w2_decay, 2026-10-13)

* `ramp w a R x = clamp((a + R − |x − w|)/R, 0, 1)` (`|·|` = periodic `ℓ¹` distance `pdist`): `1` on `Ball w a`, `0` off `Ball w (a+R)`,
  `(1/R)`-Lipschitz;
* `smoothCut w a R m = A_0^m A_1^m A_2^m ramp` (window averages in the three directions):
  `sc_nonneg`, `sc_le_one`, `sc_lip` (`1/R`-Lipschitz), `sc_D2` (`|D2 μ sc| ≤ 2/(R m)`), `sc_lapR` (`|lapR sc| ≤ 6/(R m)`),
  `sc_one` (`= 1` on `Ball w r` when `r + 3(m−1) ≤ a`), `sc_zero` (`= 0` when `a + R + 3(m−1) < |x − w|`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1Decay

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_coarseShift_le pdist_self)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

variable {L : PeriodicLatticeExtent}

/-- the Lipschitz ramp. -/
noncomputable def ramp (w : PeriodicLatticeSite L) (a R : ℕ) (x : PeriodicLatticeSite L) : ℝ :=
  max 0 (min 1 (((a : ℝ) + R - pdist w x) / R))

theorem ramp_nonneg (w : PeriodicLatticeSite L) (a R : ℕ) (x : PeriodicLatticeSite L) : 0 ≤ ramp w a R x :=
  le_max_left _ _

theorem ramp_le_one (w : PeriodicLatticeSite L) (a R : ℕ) (x : PeriodicLatticeSite L) : ramp w a R x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem clamp_lip (u v : ℝ) : |max 0 (min 1 u) - max 0 (min 1 v)| ≤ |u - v| := by
  have h1 := le_abs_self (u - v)
  have h2 := neg_abs_le (u - v)
  rw [abs_le]
  constructor <;>
  · simp only [max_def, min_def]
    split_ifs <;> linarith

theorem pdist_diff_le (w x z : PeriodicLatticeSite L) : |(pdist w z : ℝ) - pdist w x| ≤ pdist x z := by
  have h1 := pdist_triangle w x z
  have h2 := pdist_triangle w z x
  have h3 := pdist_comm z x
  rw [abs_le]
  constructor
  · have : (pdist w x : ℝ) ≤ pdist w z + pdist z x := by exact_mod_cast h2
    rw [h3] at this; linarith
  · have : (pdist w z : ℝ) ≤ pdist w x + pdist x z := by exact_mod_cast h1
    linarith

theorem ramp_lip (w : PeriodicLatticeSite L) (a R : ℕ) (hR : 0 < R) : LipP (ramp w a R) (1 / R) := by
  intro x z
  unfold ramp
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  refine (clamp_lip _ _).trans ?_
  have e : ((a : ℝ) + R - pdist w x) / R - ((a : ℝ) + R - pdist w z) / R = ((pdist w z : ℝ) - pdist w x) / R := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hR']
  have := pdist_diff_le w x z
  rw [div_le_iff₀ hR']
  calc |(pdist w z : ℝ) - pdist w x| ≤ pdist x z := this
    _ = 1 / R * (pdist x z : ℝ) * R := by field_simp

theorem ramp_one (w : PeriodicLatticeSite L) (a R : ℕ) (hR : 0 < R) (x : PeriodicLatticeSite L) (hx : pdist w x ≤ a) :
    ramp w a R x = 1 := by
  unfold ramp
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hx' : (pdist w x : ℝ) ≤ a := by exact_mod_cast hx
  have : 1 ≤ ((a : ℝ) + R - pdist w x) / R := by rw [le_div_iff₀ hR']; linarith
  rw [min_eq_left this, max_eq_right (by norm_num)]

theorem ramp_zero (w : PeriodicLatticeSite L) (a R : ℕ) (hR : 0 < R) (x : PeriodicLatticeSite L) (hx : a + R ≤ pdist w x) :
    ramp w a R x = 0 := by
  unfold ramp
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hx' : (a : ℝ) + R ≤ pdist w x := by exact_mod_cast hx
  have : ((a : ℝ) + R - pdist w x) / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hR'.le
  exact max_eq_left ((min_le_right _ _).trans this)

/-- window averages preserve "constant on a ball", losing `m − 1` of radius. -/
theorem boxAvg_const_ball {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (c : ℝ)
    (w : PeriodicLatticeSite L) (r : ℕ) (h : ∀ z, pdist w z ≤ r + (m - 1) → φ z = c)
    (x : PeriodicLatticeSite L) (hx : pdist w x ≤ r) : boxAvg m μ φ x = c := by
  refine boxAvg_eq_of hm μ φ c x (fun j hj => h _ ?_)
  have h1 := pdist_triangle w x (coarseShift x j μ)
  have h2 := pdist_coarseShift_le x j μ
  omega

/-- window averages preserve "zero off a ball", gaining `m − 1` of radius. -/
theorem boxAvg_zero_far {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ)
    (w : PeriodicLatticeSite L) (ρ : ℕ) (h : ∀ z, ρ < pdist w z → φ z = 0)
    (x : PeriodicLatticeSite L) (hx : ρ + (m - 1) < pdist w x) : boxAvg m μ φ x = 0 := by
  refine boxAvg_eq_of hm μ φ 0 x (fun j hj => h _ ?_)
  have h1 := pdist_triangle w (coarseShift x j μ) x
  have h2 := pdist_cs_le' x j μ
  omega

/-- the smoothed cutoff. -/
noncomputable def smoothCut (w : PeriodicLatticeSite L) (a R m : ℕ) : PeriodicLatticeSite L → ℝ :=
  boxAvg m 0 (boxAvg m 1 (boxAvg m 2 (ramp w a R)))

section sc
variable (w : PeriodicLatticeSite L) (a R m : ℕ)

theorem sc_nonneg (x : PeriodicLatticeSite L) : 0 ≤ smoothCut w a R m x :=
  boxAvg_nonneg _ _ _ (boxAvg_nonneg _ _ _ (boxAvg_nonneg _ _ _ (ramp_nonneg w a R))) x

theorem sc_le_one (hm : 0 < m) (x : PeriodicLatticeSite L) : smoothCut w a R m x ≤ 1 :=
  boxAvg_le_one hm _ _ (boxAvg_le_one hm _ _ (boxAvg_le_one hm _ _ (ramp_le_one w a R))) x

theorem sc_lip (hR : 0 < R) (hm : 0 < m) : LipP (smoothCut w a R m) (1 / R) :=
  boxAvg_lip hm _ _ _ (boxAvg_lip hm _ _ _ (boxAvg_lip hm _ _ _ (ramp_lip w a R hR)))

theorem sc_D2 (hR : 0 < R) (hm : 0 < m) (μ : Fin 3) (x : PeriodicLatticeSite L) :
    |D2 μ (smoothCut w a R m) x| ≤ 2 * (1 / (R : ℝ)) / m := by
  have l2 := ramp_lip w a R hR
  have hc : (0 : ℝ) ≤ 1 / (R : ℝ) := by positivity
  have l1 := boxAvg_lip hm 2 _ _ l2
  have l0 := boxAvg_lip hm 1 _ _ l1
  unfold smoothCut
  fin_cases μ
  · exact D2_boxAvg_self hm 0 _ _ hc l0 x
  · show |D2 1 (boxAvg m 0 (boxAvg m 1 (boxAvg m 2 (ramp w a R)))) x| ≤ _
    rw [D2_boxAvg]
    exact boxAvg_bound hm 0 _ _ (fun z => D2_boxAvg_self hm 1 _ _ hc l1 z) x
  · show |D2 2 (boxAvg m 0 (boxAvg m 1 (boxAvg m 2 (ramp w a R)))) x| ≤ _
    rw [D2_boxAvg]
    have e : D2 2 (boxAvg m 1 (boxAvg m 2 (ramp w a R))) = boxAvg m 1 (D2 2 (boxAvg m 2 (ramp w a R))) :=
      funext (fun z => D2_boxAvg m 1 2 _ z)
    rw [e]
    exact boxAvg_bound hm 0 _ _ (fun z => boxAvg_bound hm 1 _ _ (fun y => D2_boxAvg_self hm 2 _ _ hc l2 y) z) x

theorem sc_lapR (hR : 0 < R) (hm : 0 < m) (x : PeriodicLatticeSite L) :
    |lapR (smoothCut w a R m) x| ≤ 6 / ((R : ℝ) * m) := by
  rw [lapR_eq, abs_neg, Fin.sum_univ_three]
  have h0 := sc_D2 w a R m hR hm 0 x
  have h1 := sc_D2 w a R m hR hm 1 x
  have h2 := sc_D2 w a R m hR hm 2 x
  have e : 6 / ((R : ℝ) * m) = 3 * (2 * (1 / (R : ℝ)) / m) := by field_simp; ring
  rw [e]
  calc |D2 0 (smoothCut w a R m) x + D2 1 (smoothCut w a R m) x + D2 2 (smoothCut w a R m) x|
      ≤ |D2 0 (smoothCut w a R m) x| + |D2 1 (smoothCut w a R m) x| + |D2 2 (smoothCut w a R m) x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem sc_one (hR : 0 < R) (hm : 0 < m) (r : ℕ) (hr : r + 3 * (m - 1) ≤ a) (x : PeriodicLatticeSite L)
    (hx : pdist w x ≤ r) : smoothCut w a R m x = 1 := by
  unfold smoothCut
  refine boxAvg_const_ball hm 0 _ 1 w r (fun z hz => ?_) x hx
  refine boxAvg_const_ball hm 1 _ 1 w (r + (m - 1)) (fun y hy => ?_) z hz
  refine boxAvg_const_ball hm 2 _ 1 w (r + (m - 1) + (m - 1)) (fun u hu => ?_) y hy
  exact ramp_one w a R hR u (by omega)

theorem sc_zero (hR : 0 < R) (hm : 0 < m) (x : PeriodicLatticeSite L) (hx : a + R + 3 * (m - 1) < pdist w x) :
    smoothCut w a R m x = 0 := by
  unfold smoothCut
  refine boxAvg_zero_far hm 0 _ w (a + R + 2 * (m - 1)) (fun z hz => ?_) x (by omega)
  refine boxAvg_zero_far hm 1 _ w (a + R + (m - 1)) (fun y hy => ?_) z (by omega)
  refine boxAvg_zero_far hm 2 _ w (a + R) (fun u hu => ?_) y (by omega)
  exact ramp_zero w a R hR u hu.le

end sc

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.ramp_lip
#print axioms AdalyFormal.M1Decay.ramp_one
#print axioms AdalyFormal.M1Decay.ramp_zero
#print axioms AdalyFormal.M1Decay.sc_lip
#print axioms AdalyFormal.M1Decay.sc_D2
#print axioms AdalyFormal.M1Decay.sc_lapR
#print axioms AdalyFormal.M1Decay.sc_one
#print axioms AdalyFormal.M1Decay.sc_zero

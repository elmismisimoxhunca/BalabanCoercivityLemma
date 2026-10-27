import W2K
import PSiteC3
import PW7

/-!
# DA -- torus toolkit for the decay lane (m1_w2_decay, 2026-10-13)

Generic facts on the periodic lattice `PeriodicLatticeSite L` (no tower):
* `pcd_add_mod`, `pdist_cs` : the periodic `ℓ¹` distance is invariant under a common translation `coarseShift · j μ`;
* `shift_cs`, `back_cs` : the unit forward/backward shifts commute with `coarseShift`;
* `LipP φ c` : `|φ x − φ z| ≤ c · pdist x z`;  `boxAvg m μ φ` : the window average `m⁻¹ Σ_{j<m} φ(x + j e_μ)`;
* `D2 μ φ x = φ(x+e_μ) + φ(x−e_μ) − 2 φ x`;
* `boxAvg_lip` (Lipschitz preserved), `D2_boxAvg` (commutes), `D2_boxAvg_self` (`|D2 μ (boxAvg m μ φ)| ≤ 2c/m`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1Decay

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist pcd)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_coarseShift_le pdist_self pdist_shift_le)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack
  periodicLatticeShiftBack_shift)

variable {L : PeriodicLatticeExtent}

/-! ## 1. translation invariance of the circular distance -/

theorem mod_add_mod' (x a b N : ℕ) : ((x + a) % N + b) % N = (x + a + b) % N := by
  rw [Nat.add_mod ((x + a) % N) b, Nat.mod_mod, ← Nat.add_mod]

theorem pcd_succ_mod (N a b : ℕ) (ha : a < N) (hb : b < N) :
    pcd N ((a + 1) % N) ((b + 1) % N) = pcd N a b := by
  have hA : (a + 1) % N = if a + 1 = N then 0 else a + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have hB : (b + 1) % N = if b + 1 = N then 0 else b + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hA, hB]
  unfold pcd
  simp only [min_def]
  split_ifs <;> omega

theorem pcd_add_mod (N a b j : ℕ) (ha : a < N) (hb : b < N) :
    pcd N ((a + j) % N) ((b + j) % N) = pcd N a b := by
  induction j with
  | zero => rw [Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  | succ n ih =>
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
    have e1 : (a + (n + 1)) % N = ((a + n) % N + 1) % N := by rw [mod_add_mod']; ring_nf
    have e2 : (b + (n + 1)) % N = ((b + n) % N + 1) % N := by rw [mod_add_mod']; ring_nf
    rw [e1, e2, pcd_succ_mod N _ _ (Nat.mod_lt _ hN) (Nat.mod_lt _ hN), ih]

theorem pdist_cs (x z : PeriodicLatticeSite L) (j : ℕ) (μ : Fin 3) :
    pdist (coarseShift x j μ) (coarseShift z j μ) = pdist x z := by
  unfold pdist
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  by_cases h : ν = μ
  · subst h
    rw [coarseShift_val_eq, coarseShift_val_eq]
    exact pcd_add_mod _ _ _ _ (x ν).isLt (z ν).isLt
  · rw [coarseShift_apply_ne _ _ _ _ h, coarseShift_apply_ne _ _ _ _ h]

theorem shift_eq_cs (x : PeriodicLatticeSite L) (μ : Fin 3) : periodicLatticeShift x μ = coarseShift x 1 μ := rfl

theorem cs_succ (x : PeriodicLatticeSite L) (j : ℕ) (μ : Fin 3) :
    coarseShift (periodicLatticeShift x μ) j μ = coarseShift x (j + 1) μ := by
  unfold coarseShift
  rw [Function.iterate_succ_apply]

theorem cs_zero (x : PeriodicLatticeSite L) (μ : Fin 3) : coarseShift x 0 μ = x := rfl

theorem pdist_shift (x z : PeriodicLatticeSite L) (μ : Fin 3) :
    pdist (periodicLatticeShift x μ) (periodicLatticeShift z μ) = pdist x z := by
  rw [shift_eq_cs, shift_eq_cs]; exact pdist_cs x z 1 μ

theorem pdist_back (x z : PeriodicLatticeSite L) (μ : Fin 3) :
    pdist (periodicLatticeShiftBack x μ) (periodicLatticeShiftBack z μ) = pdist x z := by
  have h := pdist_shift (periodicLatticeShiftBack x μ) (periodicLatticeShiftBack z μ) μ
  rw [periodicLatticeShift_shiftBack, periodicLatticeShift_shiftBack] at h
  exact h.symm

theorem pdist_back_le (x : PeriodicLatticeSite L) (μ : Fin 3) : pdist x (periodicLatticeShiftBack x μ) ≤ 1 := by
  have h := pdist_shift_le (periodicLatticeShiftBack x μ) μ
  rw [periodicLatticeShift_shiftBack, pdist_comm] at h
  exact h

theorem pdist_cs_le' (x : PeriodicLatticeSite L) (j : ℕ) (μ : Fin 3) : pdist (coarseShift x j μ) x ≤ j := by
  rw [pdist_comm]; exact pdist_coarseShift_le x j μ

/-! ## 2. shifts commute with `coarseShift` -/

theorem shift_cs (x : PeriodicLatticeSite L) (j : ℕ) (μ ν : Fin 3) :
    periodicLatticeShift (coarseShift x j μ) ν = coarseShift (periodicLatticeShift x ν) j μ := by
  rw [shift_eq_cs, shift_eq_cs]
  funext κ
  apply Fin.ext
  by_cases hκμ : κ = μ <;> by_cases hκν : κ = ν
  · subst hκμ; subst hκν
    rw [coarseShift_val_eq, coarseShift_val_eq, coarseShift_val_eq, coarseShift_val_eq, mod_add_mod', mod_add_mod']
    ring_nf
  · subst hκμ
    rw [coarseShift_apply_ne _ _ _ _ hκν, coarseShift_val_eq, coarseShift_val_eq, coarseShift_apply_ne _ _ _ _ hκν]
  · subst hκν
    rw [coarseShift_val_eq, coarseShift_apply_ne _ _ _ _ hκμ, coarseShift_apply_ne _ _ _ _ hκμ, coarseShift_val_eq]
  · rw [coarseShift_apply_ne _ _ _ _ hκν, coarseShift_apply_ne _ _ _ _ hκμ, coarseShift_apply_ne _ _ _ _ hκμ,
      coarseShift_apply_ne _ _ _ _ hκν]

theorem shift_inj {x z : PeriodicLatticeSite L} {ν : Fin 3} (h : periodicLatticeShift x ν = periodicLatticeShift z ν) :
    x = z := by
  have := congrArg (fun y => periodicLatticeShiftBack y ν) h
  simpa only [periodicLatticeShiftBack_shift] using this

theorem back_cs (x : PeriodicLatticeSite L) (j : ℕ) (μ ν : Fin 3) :
    periodicLatticeShiftBack (coarseShift x j μ) ν = coarseShift (periodicLatticeShiftBack x ν) j μ := by
  apply shift_inj (ν := ν)
  rw [periodicLatticeShift_shiftBack, shift_cs, periodicLatticeShift_shiftBack]

/-! ## 3. Lipschitz functions, window averages, second differences -/

/-- `φ` is `c`-Lipschitz for the periodic `ℓ¹` distance. -/
def LipP (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) : Prop := ∀ x z, |φ x - φ z| ≤ c * (pdist x z : ℝ)

/-- the window average in direction `μ`. -/
noncomputable def boxAvg (m : ℕ) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  (1 / (m : ℝ)) * ∑ j ∈ Finset.range m, φ (coarseShift x j μ)

/-- the second difference in direction `μ`. -/
def D2 (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  φ (periodicLatticeShift x μ) + φ (periodicLatticeShiftBack x μ) - 2 * φ x

theorem boxAvg_bound {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (M : ℝ)
    (h : ∀ z, |φ z| ≤ M) (x : PeriodicLatticeSite L) : |boxAvg m μ φ x| ≤ M := by
  unfold boxAvg
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  have h1 : |∑ j ∈ Finset.range m, φ (coarseShift x j μ)| ≤ ∑ j ∈ Finset.range m, M :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => h _))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  calc 1 / (m : ℝ) * |∑ j ∈ Finset.range m, φ (coarseShift x j μ)| ≤ 1 / (m : ℝ) * ((m : ℝ) * M) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M := by field_simp

theorem boxAvg_eq_of {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (x : PeriodicLatticeSite L)
    (h : ∀ j, j < m → φ (coarseShift x j μ) = c) : boxAvg m μ φ x = c := by
  unfold boxAvg
  rw [Finset.sum_congr rfl (fun j hj => h j (Finset.mem_range.mp hj)), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem boxAvg_nonneg (m : ℕ) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (h : ∀ z, 0 ≤ φ z) (x : PeriodicLatticeSite L) :
    0 ≤ boxAvg m μ φ x := by
  unfold boxAvg
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => h _))

theorem boxAvg_le_one {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (h : ∀ z, φ z ≤ 1)
    (x : PeriodicLatticeSite L) : boxAvg m μ φ x ≤ 1 := by
  unfold boxAvg
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ∑ j ∈ Finset.range m, φ (coarseShift x j μ) ≤ ∑ j ∈ Finset.range m, (1 : ℝ) :=
    Finset.sum_le_sum (fun j _ => h _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  calc 1 / (m : ℝ) * ∑ j ∈ Finset.range m, φ (coarseShift x j μ) ≤ 1 / (m : ℝ) * m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp

theorem boxAvg_lip {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (h : LipP φ c) :
    LipP (boxAvg m μ φ) c := by
  intro x z
  unfold boxAvg
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  have h1 : |∑ j ∈ Finset.range m, (φ (coarseShift x j μ) - φ (coarseShift z j μ))|
      ≤ ∑ j ∈ Finset.range m, c * (pdist x z : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    have := h (coarseShift x j μ) (coarseShift z j μ)
    rwa [pdist_cs] at this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  calc 1 / (m : ℝ) * |∑ j ∈ Finset.range m, (φ (coarseShift x j μ) - φ (coarseShift z j μ))|
      ≤ 1 / (m : ℝ) * ((m : ℝ) * (c * (pdist x z : ℝ))) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c * (pdist x z : ℝ) := by field_simp

/-- `D2 ν` commutes with the window average in any direction. -/
theorem D2_boxAvg (m : ℕ) (μ ν : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) :
    D2 ν (boxAvg m μ φ) x = boxAvg m μ (D2 ν φ) x := by
  unfold D2 boxAvg
  simp only [shift_cs, back_cs, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem boxAvg_shift_sub {m : ℕ} (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) :
    boxAvg m μ φ (periodicLatticeShift x μ) - boxAvg m μ φ x
      = (1 / (m : ℝ)) * (φ (coarseShift x m μ) - φ x) := by
  unfold boxAvg
  rw [← mul_sub]
  congr 1
  simp only [cs_succ]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => φ (coarseShift x j μ))]
  rfl

theorem D2_boxAvg_self {m : ℕ} (hm : 0 < m) (μ : Fin 3) (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : LipP φ c)
    (x : PeriodicLatticeSite L) : |D2 μ (boxAvg m μ φ) x| ≤ 2 * c / m := by
  set y := periodicLatticeShiftBack x μ with hy
  have hxy : periodicLatticeShift y μ = x := periodicLatticeShift_shiftBack x μ
  have e1 := boxAvg_shift_sub (m := m) μ φ x
  have e2 := boxAvg_shift_sub (m := m) μ φ y
  rw [hxy] at e2
  have hD : D2 μ (boxAvg m μ φ) x = (1 / (m : ℝ)) * ((φ (coarseShift x m μ) - φ (coarseShift y m μ)) - (φ x - φ y)) := by
    unfold D2
    rw [← hy]
    linear_combination e1 - e2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : |φ (coarseShift x m μ) - φ (coarseShift y m μ)| ≤ c * 1 := by
    have := h (coarseShift x m μ) (coarseShift y m μ)
    rw [pdist_cs] at this
    have hp : (pdist x y : ℝ) ≤ 1 := by exact_mod_cast pdist_back_le x μ
    nlinarith
  have h2 : |φ x - φ y| ≤ c * 1 := by
    have := h x y
    have hp : (pdist x y : ℝ) ≤ 1 := by exact_mod_cast pdist_back_le x μ
    nlinarith
  rw [hD, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  have h3 : |(φ (coarseShift x m μ) - φ (coarseShift y m μ)) - (φ x - φ y)| ≤ 2 * c :=
    (abs_sub _ _).trans (by linarith)
  calc 1 / (m : ℝ) * |(φ (coarseShift x m μ) - φ (coarseShift y m μ)) - (φ x - φ y)| ≤ 1 / (m : ℝ) * (2 * c) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * c / m := by ring

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.pcd_add_mod
#print axioms AdalyFormal.M1Decay.pdist_cs
#print axioms AdalyFormal.M1Decay.shift_cs
#print axioms AdalyFormal.M1Decay.back_cs
#print axioms AdalyFormal.M1Decay.boxAvg_lip
#print axioms AdalyFormal.M1Decay.D2_boxAvg
#print axioms AdalyFormal.M1Decay.D2_boxAvg_self

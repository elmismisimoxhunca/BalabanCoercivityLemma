import CvO6

/-!
# CvO7 -- the loops of the staggered layer at stride 1, and the first blocked level (lane omega)

For an even transverse side (`2 ∣ L 1 + 1`) and even `ell`:
* `loopVar_stag`: every loop `W_x` of the stride-1 (43)-average of `stagCfg c t` is `cartan (Φ)`: in direction `0`
  `Φ = t · S(y₁, x₁-y₁) · ([y₀ = c] - [(y₀+ell) mod N₀ = c])`, `S(v,n) = Σ_{j<n} (-1)^{v+j} ∈ {0, ±1}`; in directions `1, 2` the loop is trivial;
* the bond variable `V(c)` is trivial in all directions (`ell` even).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)

variable {L : PeriodicLatticeExtent}

/-- alternating sums of `(-1)^v`. -/
theorem altsum (v n : ℕ) : ∑ j ∈ Finset.range n, sgnNat (v + j) = if n % 2 = 0 then 0 else sgnNat v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp
    · simp
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih n (by omega)]
      have h1 : sgnNat (v + (n + 1)) = - sgnNat (v + n) := by
        rw [← add_assoc]; exact sgnNat_succ _
      rw [h1]
      have : (n + 1 + 1) % 2 = n % 2 := by omega
      rw [this]
      ring

theorem sgnNat_abs_le (v : ℕ) : |sgnNat v| ≤ 1 := by
  unfold sgnNat; split_ifs <;> simp

theorem altsum_abs_le (v n : ℕ) : |∑ j ∈ Finset.range n, sgnNat (v + j)| ≤ 1 := by
  rw [altsum]; split_ifs
  · simp
  · exact sgnNat_abs_le v

/-- the angle along the staircase `Γ_{y,x}` read from an arbitrary base `w` (stride `s`). -/
theorem pathAng_gamma (hN : 2 ∣ L 1 + 1) (c : ℕ) (t : ℝ) (s : ℕ) (w y x : PeriodicLatticeSite L) :
    pathAng c t s w (coarseGammaPath s y x) =
      if (w 0).val = c then
        t * ∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / s), sgnNat ((w 1).val + s * j) else 0 := by
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  rw [pathAng_append, pathAng_rep_ne c t s 2 (by decide), pathAng_append, pathAng_rep_ne c t s 0 (by decide)]
  simp only [zero_add, add_zero]
  rw [pathAng_rep_one hN]
  have h0 : (coarsePathEndpoint s w (List.replicate ((x 2 - y 2).val / s) 2)) 0 = w 0 := endpoint_rep_ne s 2 0 (by decide) _ _
  have h1 : (coarsePathEndpoint s w (List.replicate ((x 2 - y 2).val / s) 2)) 1 = w 1 := endpoint_rep_ne s 2 1 (by decide) _ _
  rw [h0, h1]


theorem cartan_comb' (a b c d : ℝ) :
    cartan a * cartan b * (cartan c)⁻¹ * (cartan d)⁻¹ = cartan (a + b - c - d) := by
  rw [cartan_inv, cartan_inv, cartan_mul, cartan_mul, cartan_mul]
  congr 1

/-- the loop angle of the stride-1 (43)-average of the staggered layer. -/
noncomputable def stagPhi (c : ℕ) (t : ℝ) (μ : Fin 3) (ell : ℕ) (y x : PeriodicLatticeSite L) : ℝ :=
  if μ = 0 then
    t * (∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j)) *
      ((if (y 0).val = c then 1 else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0))
  else 0

theorem stag_angle_expr (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    pathAng c t 1 y (coarseGammaPath 1 y x) + pathAng c t 1 x (List.replicate ell μ)
      - pathAng c t 1 (cPlusS 1 ell (y, μ)) (coarseGammaPath 1 y x) - pathAng c t 1 y (List.replicate ell μ)
      = stagPhi c t μ ell y x := by
  have hE' : ell % 2 = 0 := Nat.mod_eq_zero_of_dvd hE
  rw [pathAng_gamma hN, pathAng_gamma hN]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · rw [pathAng_rep_ne c t 1 0 (by decide), pathAng_rep_ne c t 1 0 (by decide), cPlusS_eq]
    simp only [coarseShift_val_eq, coarseShift_apply_ne y (1 * ell) 0 1 (by decide), coarseShift_apply_ne y ell 0 1 (by decide), stagPhi, if_true, one_mul, Nat.div_one]
    split_ifs <;> ring
  · have hz : ∀ z : PeriodicLatticeSite L, pathAng c t 1 z (List.replicate ell 1) = 0 := by
      intro z; rw [pathAng_rep_one hN]; simp only [one_mul]
      rw [altsum, if_pos hE']; simp
    rw [hz, hz, cPlusS_eq]
    simp only [coarseShift_val_eq, coarseShift_apply_ne y (1 * ell) 1 0 (by decide), stagPhi]
    have hs : ∀ j, sgnNat (((y 1).val + 1 * ell) % (L 1 + 1) + 1 * j) = sgnNat ((y 1).val + 1 * j) := by
      intro j
      rw [sgnNat_mod_add _ _ _ hN, show (y 1).val + 1 * ell + 1 * j = ((y 1).val + 1 * j) + ell by ring]
      exact sgnNat_add_even _ _ hE'
    simp only [hs]
    simp
  · have hz : ∀ z : PeriodicLatticeSite L, pathAng c t 1 z (List.replicate ell 2) = 0 := fun z => pathAng_rep_ne c t 1 2 (by decide) ell z
    rw [hz, hz, cPlusS_eq]
    simp only [coarseShift_apply_ne y (1 * ell) 2 0 (by decide), coarseShift_apply_ne y (1 * ell) 2 1 (by decide), stagPhi]
    simp


theorem loopVar_stag (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    loopVar 1 ell (stagCfg c t) (y, μ) x = cartan (stagPhi c t μ ell y x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  simp only []
  rw [hol_stag, hol_stag, hol_stag, hol_stag, cartan_comb']
  congr 1
  exact stag_angle_expr hN hE c t y x μ

#print axioms altsum
#print axioms altsum_abs_le
#print axioms pathAng_gamma
#print axioms cartan_comb'
#print axioms loopVar_stag


theorem sum_odd_even (m : ℕ) (a : ℝ) : ∑ n ∈ Finset.range (2 * m), (if n % 2 = 0 then (0 : ℝ) else a) = m * a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : (2 * m + 1) % 2 ≠ 0 := by omega
    simp [h1, h2]
    push_cast; ring

theorem stagPhi_abs_lt (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi) (μ : Fin 3) (ell : ℕ) (y x : PeriodicLatticeSite L) :
    |stagPhi c t μ ell y x| < Real.pi := by
  unfold stagPhi
  by_cases hμ : μ = 0
  · rw [if_pos hμ]
    have hS := altsum_abs_le (y 1).val (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1)
    have hD : |((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0))| ≤ 1 := by
      by_cases h1 : (y 0).val = c <;> by_cases h2 : ((y 0).val + ell) % (L 0 + 1) = c
      · rw [if_pos h1, if_pos h2]; norm_num
      · rw [if_pos h1, if_neg h2]; norm_num
      · rw [if_neg h1, if_pos h2]; norm_num
      · rw [if_neg h1, if_neg h2]; norm_num
    calc |t * (∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j)) *
          ((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0))|
        = |t| * |∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j)| *
          |((if (y 0).val = c then (1 : ℝ) else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0))| := by
          rw [abs_mul, abs_mul]
      _ ≤ |t| * 1 * 1 := by
          gcongr
      _ < Real.pi := by linarith
  · rw [if_neg hμ]; simpa using Real.pi_pos

/-- **the first blocked level of the staggered layer** (stride 1, `ell` even, block fits the torus):
direction `0`: `cartan ((t/2)(-1)^{y₁}([y₀ = c] - [(y₀+ell) mod N₀ = c]))`; directions `1, 2`: trivial. -/
theorem bg1_stag (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : 2 ∣ ell) (hell : 0 < ell) (c : ℕ) (t : ℝ) (htπ : |t| < Real.pi)
    (y : PeriodicLatticeSite L) (hfit : ∀ μ, (y μ).val + 1 * ell ≤ L μ + 1) (μ : Fin 3) :
    stridedBlockedGauge su2LogExp 1 ell (stagCfg c t) (y, μ) =
      cartan (if μ = 0 then (t / 2) * sgnNat (y 1).val *
        ((if (y 0).val = c then 1 else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0)) else 0) := by
  have hE' : ell % 2 = 0 := Nat.mod_eq_zero_of_dvd hE
  have hcb : coarseBondVar 1 ell (stagCfg c t) (y, μ) = cartan 0 := by
    unfold coarseBondVar
    rw [hol_stag]
    congr 1
    have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
    rcases key with rfl | rfl | rfl
    · exact pathAng_rep_ne c t 1 0 (by decide) ell y
    · rw [pathAng_rep_one hN]; simp only [one_mul]; rw [altsum, if_pos hE']; simp
    · exact pathAng_rep_ne c t 1 2 (by decide) ell y
  have hloop : ∀ x ∈ stepBlockOf (y, μ).1 1 ell, loopVar 1 ell (stagCfg c t) (y, μ) x = cartan (stagPhi c t μ ell y x) ∧
      |stagPhi c t μ ell y x| < Real.pi :=
    fun x _ => ⟨loopVar_stag hN hE c t y x μ, stagPhi_abs_lt c t htπ μ ell y x⟩
  rw [blocked_cartan 1 ell (stagCfg c t) (y, μ) (fun x => stagPhi c t μ ell y x) 0 hloop hcb]
  congr 1
  rw [add_zero]
  by_cases hμ : μ = 0
  · subst hμ
    simp only [stagPhi, if_true]
    set D : ℝ := ((if (y 0).val = c then 1 else 0) - (if ((y 0).val + ell) % (L 0 + 1) = c then 1 else 0)) with hD
    have hn1 : ∀ x ∈ stepBlockOf y 1 ell, ((x 1 - (Function.update y 2 (x 2)) 1).val) / 1 = ((x 1).val - (y 1).val) / 1 := by
      intro x hx
      have e1 : (Function.update y 2 (x 2)) 1 = y 1 := by simp [Function.update_of_ne]
      have h := mem_stepBlockOf.mp hx 1
      have hle : y 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
      rw [e1, Fin.coe_sub_iff_le.mpr hle]
    have hsum : ∑ x ∈ stepBlockOf y 1 ell,
        t * (∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j)) * D
        = t * D * ((ell : ℝ) ^ 2 * ((ell / 2 : ℕ) * sgnNat (y 1).val)) := by
      have h1 : ∀ x ∈ stepBlockOf y 1 ell,
          t * (∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j)) * D
          = t * D * (∑ j ∈ Finset.range ((((x 1).val - (y 1).val)) / 1), sgnNat ((y 1).val + j)) := by
        intro x hx; rw [hn1 x hx]; ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
      congr 1
      rw [sum_block_dir y 1 ell one_pos hfit 1 (fun n => ∑ j ∈ Finset.range n, sgnNat ((y 1).val + j))]
      congr 1
      have : ∀ n ∈ Finset.range ell, ∑ j ∈ Finset.range n, sgnNat ((y 1).val + j) = (if n % 2 = 0 then 0 else sgnNat (y 1).val) :=
        fun n _ => altsum _ _
      rw [Finset.sum_congr rfl this]
      obtain ⟨m, hm⟩ := hE
      rw [hm, show 2 * m / 2 = m by omega, sum_odd_even]
    rw [hsum]
    obtain ⟨m, hm⟩ := hE
    have hell' : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    have hm' : ((ell / 2 : ℕ) : ℝ) = (ell : ℝ) / 2 := by
      rw [hm, show 2 * m / 2 = m by omega]; push_cast; ring
    rw [hm']
    field_simp
  · simp [stagPhi, hμ]

#print axioms sum_odd_even
#print axioms stagPhi_abs_lt
#print axioms bg1_stag

end AdalyFormal.CoverOmega

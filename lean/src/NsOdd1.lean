import NsCvO19

/-!
# NsOdd1 -- the stride-1 loops of the staggered layer for ODD `ell` (lane ncwdh_strong_20261017)

For even `ell` (CvO7) the block average of the alternating signs vanishes, so the direction-1 loop angle is `0`.
For odd `ell`, with `S = Σ_{j<n} (-1)^{y₁+j} = [n odd] (-1)^{y₁}` (`n = x₁ - y₁`):
`loop₁ = t ( [y₀ = c](2 S - (-1)^{y₁}) + [x₀ = c] (-1)^{x₁} )`, and `|loop| ≤ |t|`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
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

theorem sgnNat_add_odd (v w : ℕ) (hw : w % 2 = 1) : sgnNat (v + w) = - sgnNat v := by
  unfold sgnNat
  by_cases h : v % 2 = 0
  · have : (v + w) % 2 ≠ 0 := by omega
    simp [h, this]
  · have : (v + w) % 2 = 0 := by omega
    simp [h, this]

theorem sgnNat_add_parity (v n : ℕ) : sgnNat (v + n) = if n % 2 = 0 then sgnNat v else - sgnNat v := by
  split_ifs with h
  · exact sgnNat_add_even v n h
  · exact sgnNat_add_odd v n (by omega)

theorem sgnNat_sq (v : ℕ) : sgnNat v * sgnNat v = 1 := by
  unfold sgnNat; split_ifs <;> norm_num

theorem sgnNat_abs (v : ℕ) : |sgnNat v| = 1 := by
  unfold sgnNat; split_ifs <;> norm_num

/-- the loop angle of the stride-1 `(43)`-average of the staggered layer, for ODD `ell` (direction `1` differs from the even case). -/
noncomputable def stagPhiO (c : ℕ) (t : ℝ) (μ : Fin 3) (ell : ℕ) (y x : PeriodicLatticeSite L) : ℝ :=
  if μ = 1 then
    t * ((if (y 0).val = c then 2 * (∑ j ∈ Finset.range (((x 1 - (Function.update y 2 (x 2)) 1).val) / 1), sgnNat ((y 1).val + j))
            - sgnNat (y 1).val else 0)
        + (if (x 0).val = c then sgnNat (x 1).val else 0))
  else stagPhi c t μ ell y x

theorem stag_angle_expr_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    pathAng c t 1 y (coarseGammaPath 1 y x) + pathAng c t 1 x (List.replicate ell μ)
      - pathAng c t 1 (cPlusS 1 ell (y, μ)) (coarseGammaPath 1 y x) - pathAng c t 1 y (List.replicate ell μ)
      = stagPhiO c t μ ell y x := by
  rw [pathAng_gamma hN, pathAng_gamma hN]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · rw [pathAng_rep_ne c t 1 0 (by decide), pathAng_rep_ne c t 1 0 (by decide), cPlusS_eq]
    simp only [coarseShift_val_eq, coarseShift_apply_ne y (1 * ell) 0 1 (by decide), coarseShift_apply_ne y ell 0 1 (by decide), stagPhiO, stagPhi, if_true, one_mul, Nat.div_one, if_neg (show ¬ ((0 : Fin 3) = 1) by decide)]
    split_ifs <;> ring
  · have hz : ∀ z : PeriodicLatticeSite L, pathAng c t 1 z (List.replicate ell 1) = if (z 0).val = c then t * sgnNat (z 1).val else 0 := by
      intro z; rw [pathAng_rep_one hN]; simp only [one_mul]; rw [altsum]; simp [show ¬ ell % 2 = 0 by omega]
    rw [hz, hz, cPlusS_eq]
    simp only [coarseShift_val_eq, coarseShift_apply_ne y (1 * ell) 1 0 (by decide), coarseShift_apply_ne y ell 1 0 (by decide), stagPhiO, if_true, one_mul, Nat.div_one]
    have hs : ∀ j, sgnNat (((y 1).val + ell) % (L 1 + 1) + j) = - sgnNat ((y 1).val + j) := by
      intro j
      rw [sgnNat_mod_add _ _ _ hN, show (y 1).val + ell + j = ((y 1).val + j) + ell by ring]
      exact sgnNat_add_odd _ _ hO
    simp only [hs, Finset.sum_neg_distrib]
    split_ifs <;> ring
  · have hz : ∀ z : PeriodicLatticeSite L, pathAng c t 1 z (List.replicate ell 2) = 0 := fun z => pathAng_rep_ne c t 1 2 (by decide) ell z
    rw [hz, hz, cPlusS_eq]
    simp only [coarseShift_apply_ne y (1 * ell) 2 0 (by decide), coarseShift_apply_ne y (1 * ell) 2 1 (by decide), stagPhiO, stagPhi, if_neg (show ¬ ((2 : Fin 3) = 1) by decide), if_neg (show ¬ ((2 : Fin 3) = 0) by decide)]
    simp

theorem loopAngG_stagφ_odd (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (y x : PeriodicLatticeSite L) (μ : Fin 3) :
    loopAngG 1 ell (stagφ c t) y μ x = stagPhiO c t μ ell y x := by
  unfold loopAngG
  simp only [pathAngG_stagφ]
  exact stag_angle_expr_odd hN hO c t y x μ

theorem sgnNat_cases (v : ℕ) : sgnNat v = 1 ∨ sgnNat v = -1 := by
  unfold sgnNat; split_ifs <;> simp

theorem stagPhi_abs_le (c : ℕ) (t : ℝ) (μ : Fin 3) (ell : ℕ) (y x : PeriodicLatticeSite L) : |stagPhi c t μ ell y x| ≤ |t| := by
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
      _ ≤ |t| * 1 * 1 := by gcongr
      _ = |t| := by ring
  · rw [if_neg hμ]; simpa using abs_nonneg t

theorem stagPhiO_abs_le {ell : ℕ} (hO : ell % 2 = 1) (c : ℕ) (t : ℝ) (μ : Fin 3) (y x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf y 1 ell) : |stagPhiO c t μ ell y x| ≤ |t| := by
  by_cases hμ : μ = 1
  · subst hμ
    have e1 : (Function.update y 2 (x 2)) 1 = y 1 := by simp [Function.update_of_ne]
    have h := mem_stepBlockOf.mp hx 1
    have hle : y 1 ≤ x 1 := by rw [Fin.le_def]; exact h.1
    have hn : ((x 1 - (Function.update y 2 (x 2)) 1).val) / 1 = (x 1).val - (y 1).val := by
      rw [e1, Fin.coe_sub_iff_le.mpr hle, Nat.div_one]
    have hx1 : (x 1).val = (y 1).val + ((x 1).val - (y 1).val) := by have := h.1; omega
    have hS := altsum (y 1).val ((x 1).val - (y 1).val)
    have hsg := sgnNat_add_parity (y 1).val ((x 1).val - (y 1).val)
    rw [← hx1] at hsg
    simp only [stagPhiO, if_true, hn, hS, hsg]
    have hs := sgnNat_cases (y 1).val
    have key : |((if (y 0).val = c then 2 * (if ((x 1).val - (y 1).val) % 2 = 0 then 0 else sgnNat (y 1).val) - sgnNat (y 1).val else 0)
        + (if (x 0).val = c then (if ((x 1).val - (y 1).val) % 2 = 0 then sgnNat (y 1).val else - sgnNat (y 1).val) else 0))| ≤ 1 := by
      rcases hs with hs | hs <;> rw [hs] <;> split_ifs <;> norm_num
    rw [abs_mul]
    calc |t| * _ ≤ |t| * 1 := by gcongr
      _ = |t| := by ring
  · simp only [stagPhiO, if_neg hμ]
    exact stagPhi_abs_le c t μ ell y x

end AdalyFormal.CoverOmega

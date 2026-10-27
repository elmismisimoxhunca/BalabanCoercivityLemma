import CvO11

/-!
# CvO12 -- loops of the class `𝒞(D,u)` at stride `s`, and the telescoping bound at stride `ell` (lane omega)
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

theorem n_eq {s ell : ℕ} {y x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) (μ : Fin 3) :
    (x μ).val = (y μ).val + s * (((x μ - y μ).val) / s) := by
  have h := mem_stepBlockOf.mp hx μ
  have hle : y μ ≤ x μ := by rw [Fin.le_def]; exact h.1
  have hsub : (x μ - y μ).val = (x μ).val - (y μ).val := (Fin.coe_sub_iff_le.mpr hle)
  rw [hsub, Nat.mul_div_cancel' h.2.2]
  have := h.1; omega

/-- the unwrapped loop angle of the class. -/
theorem uTemp_angle_expr {s ell : ℕ} {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ}
    (y : PeriodicLatticeSite L) (μ : Fin 3) {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    uAng s D u y (coarseGammaPath s y x) + uAng s D u x (List.replicate ell μ)
      - uAng s D u (cPlusS s ell (y, μ)) (coarseGammaPath s y x) - uAng s D u y (List.replicate ell μ) =
    (if μ = 0 then (∑ j ∈ Finset.range ell, D (((y 0).val + s * j) % (L 0 + 1))) * (u (x 1).val (x 2).val - u (y 1).val (y 2).val)
       else if μ = 1 then (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (((x 1).val + s * ell) % (L 1 + 1)) (x 2).val)
       else (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (x 1).val (((x 2).val + s * ell) % (L 2 + 1)))) := by
  have e0 : (Function.update (Function.update y 2 (x 2)) 1 (x 1)) 0 = y 0 := by simp [Function.update_of_ne]
  have e1 : (Function.update y 2 (x 2)) 1 = y 1 := by simp [Function.update_of_ne]
  have hx0 := n_eq hx 0
  have hx1 := n_eq hx 1
  have hx2 := n_eq hx 2
  have hm1 : ((y 1).val + s * (((x 1 - y 1).val) / s)) % (L 1 + 1) = (x 1).val := by
    rw [← hx1]; exact Nat.mod_eq_of_lt (x 1).isLt
  have hm2 : ((y 2).val + s * (((x 2 - y 2).val) / s)) % (L 2 + 1) = (x 2).val := by
    rw [← hx2]; exact Nat.mod_eq_of_lt (x 2).isLt
  rw [uAng_gamma, uAng_gamma, e0, e1]
  have key : μ = 0 ∨ μ = 1 ∨ μ = 2 := by fin_cases μ <;> simp
  rcases key with rfl | rfl | rfl
  · rw [uAng_rep_zero, uAng_rep_zero, cPlusS_eq]
    simp only [coarseShift_val_eq, coarseShift_apply_ne y (s * ell) 0 1 (by decide), coarseShift_apply_ne y (s * ell) 0 2 (by decide),
      hm1, hm2, if_true, Nat.mod_add_mod]
    have hT := telescope_loop D s ell (L 0 + 1) (y 0).val ((x 0 - y 0).val / s)
    rw [← hx0] at hT
    simp only [Nat.mod_add_mod] at hT
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    linear_combination (u (x 1).val (x 2).val) * hT
  · have h10 : ¬ ((1 : Fin 3) = 0) := by decide
    rw [uAng_rep_ne s D u 1 (by decide), uAng_rep_ne s D u 1 (by decide), cPlusS_eq]
    simp only [h10, if_false, if_true, coarseShift_apply_ne y (s * ell) 1 0 (by decide), coarseShift_apply_ne y (s * ell) 1 2 (by decide),
      coarseShift_val_eq, hm1, hm2, Nat.mod_add_mod]
    have h3 : (y 1).val + s * ell + s * (((x 1 - y 1).val) / s) = (x 1).val + s * ell := by omega
    rw [h3]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  · have h20 : ¬ ((2 : Fin 3) = 0) := by decide
    have h21 : ¬ ((2 : Fin 3) = 1) := by decide
    rw [uAng_rep_ne s D u 2 (by decide), uAng_rep_ne s D u 2 (by decide), cPlusS_eq]
    simp only [h20, h21, if_false, coarseShift_apply_ne y (s * ell) 2 0 (by decide), coarseShift_apply_ne y (s * ell) 2 1 (by decide),
      coarseShift_val_eq, hm1, hm2, Nat.mod_add_mod]
    have h3 : (y 2).val + s * ell + s * (((x 2 - y 2).val) / s) = (x 2).val + s * ell := by omega
    rw [h3]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring


/-- the exact loop angles of the class (stride `s`, any base `y`, any block member `x`). -/
theorem loopVar_uTemp {s ell : ℕ} {D : ℕ → ℝ} {u : ℕ → ℕ → ℝ} {V : PeriodicLinkConfiguration SU2 L} (hV : IsUTemp D u V)
    (y : PeriodicLatticeSite L) (μ : Fin 3) {x : PeriodicLatticeSite L} (hx : x ∈ stepBlockOf y s ell) :
    loopVar s ell V (y, μ) x = cartan
      (if μ = 0 then (∑ j ∈ Finset.range ell, D (((y 0).val + s * j) % (L 0 + 1))) * (u (x 1).val (x 2).val - u (y 1).val (y 2).val)
       else if μ = 1 then (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (((x 1).val + s * ell) % (L 1 + 1)) (x 2).val)
       else (∑ j ∈ Finset.range ((x 0 - y 0).val / s), D (((y 0).val + s * j) % (L 0 + 1))) *
          (u (x 1).val (x 2).val - u (x 1).val (((x 2).val + s * ell) % (L 2 + 1)))) := by
  unfold loopVar gammaVarStrided coarseBondVar
  simp only []
  rw [hol_uTemp hV, hol_uTemp hV, hol_uTemp hV, hol_uTemp hV, cartan_comb']
  congr 1
  exact uTemp_angle_expr y μ hx

#print axioms n_eq
#print axioms loopVar_uTemp

end AdalyFormal.CoverOmega

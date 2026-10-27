import CvO26

/-!
# CvO27 -- `Δ_loc (zfield f) = zfield g` on a Cartan configuration (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShiftEquiv periodicLatticeShiftBack_shift
  periodicLatticeShift_shiftBack periodicLatticeShiftEquiv_apply periodicLatticeShiftEquiv_symm_apply hsInner_sub_left)
open AdalyFormal.Balaban.DeltaKU (hsInner_zero_right hsInner_add_right)

variable {L : PeriodicLatticeExtent}

noncomputable def Wa (N : ℕ) (ω f : ℕ → ℝ) (v : ℕ) : ℝ := ω v * (f (nxt N v) - f v)
noncomputable def zprof (N : ℕ) (ω f : ℕ → ℝ) (v : ℕ) : ℝ := Wa N ω f (prv N v) - Wa N ω f v

open Classical in
theorem delta_zfield {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (P : Set (PeriodicLatticePlaquette L)) (ω : ℕ → ℝ)
    (hω : ∀ x : PeriodicLatticeSite L, (if (x, q01) ∈ P then holCos U (x, q01) else 0) = ω (x 0).val) (f : ℕ → ℝ) :
    AdalyFormal.StatementLaneR6.deltaKLocCLM U P (zfield f) = zfield (zprof (L 0) ω f) := by
  apply ext_inner_left ℝ
  intro w
  rw [zfield_eq f, inner_deltaKLocCLM_sigma3 hU P w (zfun f) (zfun_diag f), plaq_sum_reduce hU P _ f]
  set W : Bond L → SuTwo := WithLp.ofLp w with hW
  set q : PeriodicLatticeSite L → ℝ := fun y => hsInner (W (y, 1)) (dgS 1) with hq
  set r : PeriodicLatticeSite L → ℝ := fun y => hsInner (W (y, 0)) (dgS 1) with hr
  -- RHS
  have hR : (inner ℝ w (zfield (zprof (L 0) ω f)) : ℝ) = ∑ y : PeriodicLatticeSite L, zprof (L 0) ω f (y 0).val * q y := by
    rw [zfield_eq, PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Fin.sum_univ_three]
    simp only [zfun, WithLp.ofLp_toLp, if_neg (show ¬ ((0 : Fin 3) = 1) by decide), if_neg (show ¬ ((2 : Fin 3) = 1) by decide), if_true]
    show hsInner (W (y, 0)) 0 + hsInner (W (y, 1)) (dgS (zprof (L 0) ω f (y 0).val)) + hsInner (W (y, 2)) 0 = _
    rw [hsInner_zero_right, hsInner_zero_right, hsInner_dgS_one, zero_add, add_zero]
  -- LHS pointwise
  have hc : ∀ x : PeriodicLatticeSite L, ∀ a : ℝ, hsInner (curlValueCovariant U W (x, q01)) (dgS a) =
      a * (r x + q (periodicLatticeShift x 0) - r (periodicLatticeShift x 1) - q x) := by
    intro x a
    have e : curlValueCovariant U W (x, q01) = W (x, 0) + RMap (U (x, 0)) (W (periodicLatticeShift x 0, 1)) -
        RMap (U (x, 1)) (W (periodicLatticeShift x 1, 0)) - W (x, 1) := rfl
    rw [e, hsInner_sub_left, hsInner_sub_left, AdalyFormal.Balaban.SuTwoInner.hsInner_add_left,
      hsInner_RMap_dgS (hU _), hsInner_RMap_dgS (hU _), hsInner_dgS_one (W (x, 0)) a, hsInner_dgS_one (W (periodicLatticeShift x 0, 1)) a,
      hsInner_dgS_one (W (periodicLatticeShift x 1, 0)) a, hsInner_dgS_one (W (x, 1)) a]
    simp only [hq, hr]; ring
  have hL : ∑ x : PeriodicLatticeSite L, (if (x, q01) ∈ P then holCos U (x, q01) else 0) *
      hsInner (curlValueCovariant U W (x, q01)) (dgS (f ((periodicLatticeShift x 0) 0).val - f (x 0).val)) =
      ∑ x : PeriodicLatticeSite L, (Wa (L 0) ω f (x 0).val * r x + Wa (L 0) ω f (x 0).val * q (periodicLatticeShift x 0)
        - Wa (L 0) ω f (x 0).val * r (periodicLatticeShift x 1) - Wa (L 0) ω f (x 0).val * q x) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hω x, hc, val_shift0]
    unfold Wa; ring
  rw [hL, hR]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- reindex the shift terms
  have s1 : ∑ x : PeriodicLatticeSite L, Wa (L 0) ω f (x 0).val * r (periodicLatticeShift x 1) =
      ∑ x : PeriodicLatticeSite L, Wa (L 0) ω f (x 0).val * r x := by
    rw [← Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) 1) (fun x => Wa (L 0) ω f (x 0).val * r x)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [periodicLatticeShiftEquiv_apply, shift_coord_ne x 1 0 (by decide)]
  have s2 : ∑ x : PeriodicLatticeSite L, Wa (L 0) ω f (x 0).val * q (periodicLatticeShift x 0) =
      ∑ y : PeriodicLatticeSite L, Wa (L 0) ω f (prv (L 0) (y 0).val) * q y := by
    rw [← Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) 0) (fun y => Wa (L 0) ω f (prv (L 0) (y 0).val) * q y)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [periodicLatticeShiftEquiv_apply, ← val_shiftBack0, periodicLatticeShiftBack_shift]
  rw [s1, s2]
  have : ∑ y : PeriodicLatticeSite L, zprof (L 0) ω f (y 0).val * q y =
      ∑ y : PeriodicLatticeSite L, Wa (L 0) ω f (prv (L 0) (y 0).val) * q y - ∑ y : PeriodicLatticeSite L, Wa (L 0) ω f (y 0).val * q y := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun y _ => ?_); unfold zprof; ring
  rw [this]; ring

#print axioms delta_zfield

end AdalyFormal.CoverOmega

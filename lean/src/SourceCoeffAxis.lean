import SourceAxis
import CircleActions
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.Bch2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open OneStep124
open EstimatesLayer.NormBounds
open HConstruction.Circle

theorem exp_neg_fixed (Z X : SuTwo) (h : adOp Z X = 0) : expOp (-(adOp Z)) X = X := by
  simpa [ad_neg] using exp_fixed (-Z) X (by simp [ad_neg, h])

variable {L : PeriodicLatticeExtent} {ell m : ℕ}

theorem coeff_E1_axis (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell*m)) (x : PeriodicLatticeSite L)
    (X : SuTwo) (hZ : adOp (D.Z c) X = 0) (hx : adOp (D.Zx c x) X = 0)
    (hr : nu (D.Zx c x : M2) < Real.pi) :
    (Coeff124.ofBackground ell m V D).E1 c x X = 0 := by
  simp only [Coeff124.ofBackground, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  rw [gInv_neg_fixed_small _ _ hr hx, g_neg_fixed _ _ hZ, sub_self]

theorem coeff_E2_axis (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell*m)) (x : PeriodicLatticeSite L)
    (X : SuTwo) (hZ : adOp (D.Z c) X = 0) (hx : adOp (D.Zx c x) X = 0)
    (hr : nu (D.Zx c x : M2) < Real.pi) :
    (Coeff124.ofBackground ell m V D).E2 c x X = 0 := by
  simp only [Coeff124.ofBackground, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  rw [exp_neg_fixed _ _ hZ, gInv_pos_fixed_small _ _ hr hx, g_neg_fixed _ _ hZ, sub_self]

theorem coeff_E3_axis (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (D : LogData L ell m) (c : CoarseBond L (ell*m)) (X : SuTwo)
    (hZ : adOp (D.Z c) X = 0)
    (hx : ∀ u ∈ unitSitesOf ell (ell*m) c.1.1, adOp (D.Zx c u.1) X = 0)
    (hr : ∀ u ∈ unitSitesOf ell (ell*m) c.1.1, nu (D.Zx c u.1 : M2) < Real.pi)
    (hc : (unitSitesOf ell (ell*m) c.1.1).card ≠ 0) :
    (Coeff124.ofBackground ell m V D).E3 c X = 0 := by
  have havg : (∑ u ∈ unitSitesOf ell (ell*m) c.1.1,
      (1 / ((unitSitesOf ell (ell*m) c.1.1).card : ℝ)) • gInvOp (adOp (D.Zx c u.1))) X = X := by
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [Finset.sum_congr rfl (fun u hu => by rw [gInv_pos_fixed_small _ _ (hr u hu) (hx u hu)])]
    simp only [Finset.sum_const, one_div]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hc]
  simp only [Coeff124.ofBackground, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
  rw [havg, exp_fixed _ _ hZ, g_neg_fixed _ _ hZ, sub_self]

#print axioms coeff_E1_axis
#print axioms coeff_E2_axis
#print axioms coeff_E3_axis
end HConstruction.Coeff

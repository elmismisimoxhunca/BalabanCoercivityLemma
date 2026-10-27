import SectBIdentity
import AdalyFormal.Balaban.RegularUPerturbation
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace HConstruction.SectBP1
open HConstruction.GenK
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (RMap)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm norm_RMap_sub_self_le)
variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)
include hn

/-- Actual physical-gradient drift, pointwise: the inverse mesh is cancelled by
Small n α U. This is a local ingredient, NOT an L² bound on the full resolvent. -/
theorem gradientDrift_bond (U : Links M (n := n)) (α : ℝ)
    (hsmall : frobSupBond U ≤ α / (n:ℝ)) (f : Site M (n := n))
    (b : Bond (fineExtent M n)) :
    ‖bfl2Equiv (gradientDrift M U f) b‖ ≤
      2*α*‖f (periodicLatticeShift b.1 b.2)‖ := by
  let x := f (periodicLatticeShift b.1 b.2)
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hU : frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α/(n:ℝ) :=
    (frobNorm_le_frobSupBond U b).trans hsmall
  have hα : 0 ≤ α := by
    have h0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
      ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have hd := (le_div_iff₀ hnR).mp (le_trans h0 hU)
    nlinarith
  have h : ‖RMap (U b) x - x‖ ≤ 2 * frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖x‖ :=
    norm_RMap_sub_self_le (U b) x
  have h2 : 2 * frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) * ‖x‖ ≤
      2 * (α/(n:ℝ)) * ‖x‖ := by gcongr
  have h3 := mul_le_mul_of_nonneg_left (h.trans h2) hnR.le
  have he : bfl2Equiv (gradientDrift M U f) b =
      (n:ℝ) • (RMap (U b) x - x) := by
    simp only [gradientDrift, sub_apply, map_sub, Pi.sub_apply, covGrad_apply, grad_apply]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hnR]
  dsimp [x] at h3 ⊢
  calc
    _ ≤ (n:ℝ) * (2 * (α/(n:ℝ)) * ‖f (periodicLatticeShift b.1 b.2)‖) := h3
    _ = 2*α*‖f (periodicLatticeShift b.1 b.2)‖ := by field_simp
/-- A1, the uniform L² drift on the ACTUAL physical-gradient operator.
No factor depending on mesh, volume, or depth remains. -/
theorem gradientDrift_sq (U : Links M (n := n)) (α : ℝ)
    (hsmall : frobSupBond U ≤ α / (n:ℝ)) (f : Site M (n := n)) :
    ‖gradientDrift M U f‖^2 ≤ 12*α^2*‖f‖^2 := by
  have hα : 0 ≤ α := by
    obtain ⟨b⟩ := (inferInstance : Nonempty (Bond (fineExtent M n)))
    have hb := (frobNorm_le_frobSupBond U b).trans hsmall
    have h0 := AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg
      ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1)
    have hd := (le_div_iff₀ (Nat.cast_pos.mpr hn : (0:ℝ)<n)).mp (le_trans h0 hb)
    nlinarith
  have hp (b : Bond (fineExtent M n)) :
      ‖bfl2Equiv (gradientDrift M U f) b‖^2 ≤
      4*α^2*‖f (periodicLatticeShift b.1 b.2)‖^2 := by
    have hb := gradientDrift_bond M hn U α hsmall f b
    have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [← Finset.mul_sum] at hs
  have hh := AdalyFormal.Balaban.DeltaPrimeBound.sum_lam_head_sq_eq
    (fun x : PeriodicLatticeSite (fineExtent M n) => f x)
  rw [hh] at hs
  change bondEnergy (bfl2Equiv (gradientDrift M U f)) ≤
    4*α^2*(3*AdalyFormal.Balaban.GeneralUHodgeDrift.siteEnergy (fun x => f x)) at hs
  rw [bondEnergy_norm] at hs
  unfold AdalyFormal.Balaban.GeneralUHodgeDrift.siteEnergy at hs
  rw [← norm_sq_coordinates f] at hs
  nlinarith
end HConstruction.SectBP1

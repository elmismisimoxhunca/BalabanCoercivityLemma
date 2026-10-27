import GN10
import AdalyFormal.Balaban.RegularUPerturbation
import AdalyFormal.Balaban.GeneralUHodgeDrift
import AdalyFormal.Balaban.DeltaPrimeBound
import AdalyFormal.Balaban.RMapLipschitz

/-!
# GN11 -- the gradient drift `δ` from the link sup (text port of site_coercivity_20261009/SiteC7 `gradL2_drift`)

`gradL2_drift'`: `‖(D_U - D_1) f‖² ≤ 12 δ0² ‖f‖²` whenever `frobSupBond U ≤ δ0` (sup of `‖U_b - 1‖_F`).
`hd_of_frobSup`: the hypothesis `hd` of GN7/GN8/GN10 with `δ = √12 δ0`.  In M0 (`U = exp(iηA)`, `|ηA| ≤ ρ/n`): `δ0 ~ ρ/n`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap gradValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.GeneralUHodgeDrift (siteEnergy)

variable {L : PeriodicLatticeExtent}

theorem norm_sq_site' (f : SiteL2 L) : ‖f‖ ^ 2 = ∑ x, ‖f x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

theorem gradL2_drift' (U : Cfg L) {δ0 : ℝ} (h : frobSupBond U ≤ δ0) (f : SiteL2 L) :
    ‖gradL2 U f - gradL2 (trivialU L) f‖ ^ 2 ≤ 12 * δ0 ^ 2 * ‖f‖ ^ 2 := by
  have hp : ∀ b : Bond L, ‖(gradL2 U f - gradL2 (trivialU L) f) b‖ ^ 2
      ≤ 4 * δ0 ^ 2 * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
    intro b
    have e : (gradL2 U f - gradL2 (trivialU L) f) b
        = RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f (periodicLatticeShift b.1 b.2) := by
      show gradValueCovariant U (WithLp.ofLp f) b - gradValueCovariant (trivialU L) (WithLp.ofLp f) b = _
      simp [gradValueCovariant, trivialU, AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rw [e]
    have h1 := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (U b) (f (periodicLatticeShift b.1 b.2))
    have h2 : AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ0 :=
      (frobNorm_le_frobSupBond U b).trans h
    have h3 : ‖RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f (periodicLatticeShift b.1 b.2)‖
        ≤ 2 * δ0 * ‖f (periodicLatticeShift b.1 b.2)‖ := by
      refine h1.trans ?_
      gcongr
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [h4]
  rw [PiLp.norm_sq_eq_of_L2]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [← Finset.mul_sum] at hs
  have hh := AdalyFormal.Balaban.DeltaPrimeBound.sum_lam_head_sq_eq (fun x : PeriodicLatticeSite L => f x)
  rw [hh] at hs
  unfold siteEnergy at hs
  rw [norm_sq_site']
  nlinarith [hs]

theorem hd_of_frobSup (U : Cfg L) {δ0 : ℝ} (hδ0 : 0 ≤ δ0) (h : frobSupBond U ≤ δ0) (f : SiteL2 L) :
    ‖gradL2 (trivialU L) f - gradL2 U f‖ ≤ (Real.sqrt 12 * δ0) * ‖f‖ := by
  have h2 := gradL2_drift' U h f
  rw [norm_sub_rev]
  have hr : 0 ≤ Real.sqrt 12 * δ0 * ‖f‖ := by positivity
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hr]
  apply Real.sqrt_le_sqrt
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  exact h2

#print axioms gradL2_drift'
#print axioms hd_of_frobSup

end AdalyFormal.SliceCoerc

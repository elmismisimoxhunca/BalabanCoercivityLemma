import NtCvOP10

/-!
# CvOP11 -- plaquette holonomies and the matrix-valued building blocks of `Delta'` and `J` are entrywise analytic (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.IngredientFamilyR2 (Cfg)

variable {L : PeriodicLatticeExtent}

theorem EA.smulC {t0 : ℝ} {c : ℝ → ℂ} {f : ℝ → M2} (hc : AnalyticAt ℝ c t0) (hf : EA f t0) :
    EA (fun t => c t • f t) t0 := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul (hf i j)

theorem EA.one {t0 : ℝ} : EA (fun _ => (1 : M2)) t0 := EA.const 1

section Hol
variable {U : ℝ → Cfg L} {t0 : ℝ}

theorem EA_coe_inv {W : ℝ → SU2} (h : EA (fun t => ((W t : SU2) : M2)) t0) :
    EA (fun t => (((W t)⁻¹ : SU2) : M2)) t0 := by
  have : (fun t => (((W t)⁻¹ : SU2) : M2)) = fun t => ((W t : SU2) : M2)ᴴ := by
    funext t; rfl
  rw [this]; exact h.conjTranspose

theorem EA_coe_mul {W V : ℝ → SU2} (hW : EA (fun t => ((W t : SU2) : M2)) t0)
    (hV : EA (fun t => ((V t : SU2) : M2)) t0) : EA (fun t => ((W t * V t : SU2) : M2)) t0 := by
  have : (fun t => ((W t * V t : SU2) : M2)) = fun t => ((W t : SU2) : M2) * ((V t : SU2) : M2) := by
    funext t; rfl
  rw [this]; exact hW.mul hV

theorem holonomyElem_EA (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L) :
    EA (fun t => ((holonomyElem (U t) p : SU2) : M2)) t0 := by
  unfold holonomyElem periodicPlaquetteHolonomy
  exact EA_coe_mul (EA_coe_mul (EA_coe_mul (hU _) (hU _)) (EA_coe_inv (hU _))) (EA_coe_inv (hU _))

theorem holonomyElemInv_EA (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L) :
    EA (fun t => ((holonomyElemInv (U t) p : SU2) : M2)) t0 :=
  EA_coe_inv (holonomyElem_EA hU p)

theorem reHolonomy_EA (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L) :
    EA (fun t => reHolonomy (U t) p) t0 := by
  unfold reHolonomy
  exact ((holonomyElem_EA hU p).add (holonomyElemInv_EA hU p)).smul_const _

theorem imHolonomy_EA (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L) :
    EA (fun t => imHolonomy (U t) p) t0 := by
  unfold imHolonomy
  exact ((holonomyElem_EA hU p).sub (holonomyElemInv_EA hU p)).smul_const _

end Hol

end AdalyFormal.CoverOmega.Struct

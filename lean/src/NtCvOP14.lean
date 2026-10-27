import NtCvOP13
import ZXR2Wire2

/-!
# CvOP14 -- the source `Jf = -JSU2Loc 1 (plaqIn Om0) U` is analytic in the link configuration (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap conjByAmbient conjByAmbient_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.IngredientFamily
open AdalyFormal.IngredientFamilyR2 (Cfg IngrBParams)

variable {L : PeriodicLatticeExtent}

section J
variable {U : ℝ → Cfg L} {t0 : ℝ}

theorem piProj_EA {f : ℝ → M2} (hf : EA f t0) : EA (fun t => piProj (f t)) t0 := by
  unfold piProj
  have e : (fun t => Matrix.trace (f t) / 2) = fun t => Matrix.trace (f t) * (2 : ℂ)⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  have hc : AnalyticAt ℝ (fun t => Matrix.trace (f t) / 2) t0 := by
    rw [e]; exact hf.trace.mul analyticAt_const
  exact hf.sub (EA.smulC hc EA.one)

theorem conjByAmbient_EA {W : ℝ → SU2} {X : ℝ → M2} (hW : EA (fun t => ((W t : SU2) : M2)) t0) (hX : EA X t0) :
    EA (fun t => conjByAmbient (W t) (X t)) t0 := by
  have : (fun t => conjByAmbient (W t) (X t)) = fun t => ((W t : SU2) : M2) * X t * ((W t : SU2) : M2)ᴴ := by
    funext t; exact conjByAmbient_apply (W t) (X t)
  rw [this]; exact (hW.mul hX).mul hW.conjTranspose

theorem FnuMuLoc_EA (hU : LinkEA U t0) (P : Set (PeriodicLatticePlaquette L)) (ν μ : Fin 3)
    (y : PeriodicLatticeSite L) : EA (fun t => FnuMuLoc P (U t) ν μ y) t0 := by
  unfold FnuMuLoc
  split_ifs
  · exact piProj_EA (imHolonomy_EA hU _)
  · exact EA.const _
  · exact (piProj_EA (imHolonomy_EA hU _)).neg
  · exact EA.const _
  · exact EA.const _

theorem DstarDir_EA (hU : LinkEA U t0) {G : ℝ → PeriodicLatticeSite L → M2}
    (hG : ∀ y, EA (fun t => G t y) t0) (ν : Fin 3) (x : PeriodicLatticeSite L) :
    EA (fun t => DstarDir (U t) ν (G t) x) t0 := by
  unfold DstarDir
  exact (conjByAmbient_EA (EA_coe_inv (hU _)) (hG _)).sub (hG _)

theorem JfieldLoc_EA (hU : LinkEA U t0) (P : Set (PeriodicLatticePlaquette L)) (x : PeriodicLatticeSite L)
    (μ : Fin 3) : EA (fun t => JfieldLoc P (U t) x μ) t0 := by
  unfold JfieldLoc
  exact EA.sum _ (fun ν _ => by
    by_cases h : ν = μ
    · simp only [if_pos h]; exact EA.const _
    · simp only [if_neg h]
      exact DstarDir_EA hU (G := fun t y => FnuMuLoc P (U t) ν μ y) (fun y => FnuMuLoc_EA hU P ν μ y) ν x)

theorem JSU2Loc_analytic (hU : LinkEA U t0) (η : ℝ) (P : Set (PeriodicLatticePlaquette L)) (b : Bond L) :
    AnalyticAt ℝ (fun t => JSU2Loc η P (U t) b) t0 := by
  apply analyticAt_suTwo
  exact (JfieldLoc_EA hU P b.1 b.2).smul_const _

theorem JfOf_analytic (hU : LinkEA U t0) (P : Set (PeriodicLatticePlaquette L)) :
    AnalyticAt ℝ (fun t => (WithLp.toLp 2 (fun b : Bond L => -(JSU2Loc 1 P (U t) b)) : BondFnL2 L)) t0 :=
  analyticAt_toLp (fun b => (JSU2Loc_analytic hU 1 P b).neg)

end J

end AdalyFormal.CoverOmega.Struct

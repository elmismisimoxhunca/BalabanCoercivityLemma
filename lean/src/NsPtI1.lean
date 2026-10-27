import NsPtH6c
import NsPtU1

/-!
# PtI1 -- `Ginv` is definite on `E₀` at the flat point of the nested instance (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

variable {ell M R : ℕ}

/-- the flat nested parameters. -/
noncomputable abbrev PF (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : IngrBParams :=
  gparams ell 2 (neLu M R) hell (neS ell M R) flatCfg a (neLam M R)

theorem ginv_definite (hP : PGeo ell M R) (hell : 0 < ell) (a : ℝ) (ha : 0 < a)
    (x : ↥(bondSupp (PF ell M R hell a).G)) (h0 : ⟪x, (PF ell M R hell a).data.Ginv x⟫ = 0) : x = 0 := by
  obtain ⟨hc, hT, hQ⟩ := flat_ginv_zero (PF ell M R hell a) rfl ha x h0
  have hk : KD ell M R (iE (PF ell M R hell a).G x) :=
    ⟨fun b hb => x.2 b hb, hQ, hc⟩
  have := kernel_trivial hP hk hT
  exact Subtype.ext this

#print axioms ginv_definite

end AdalyFormal.CoverOmega

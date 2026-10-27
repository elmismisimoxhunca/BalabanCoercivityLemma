import NuPtZ4

/-!
# PtZ5 -- `gOf ≠ 0` at the flat nested point (lane omega/near2/point)

`gOf G U = det (Gm)` with `Gm = C m C*`, `C = Bq Lm⁻¹`.  At the flat point: `Gm w = 0 ⇒ m (Lm⁻¹ Bq* w) = 0 ⇒ Bq* w = 0 ⇒ w = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmegaTwo
open AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega.Struct

variable {ell M R : ℕ}

theorem Bq_star_inj (hP : PGeo ell M R) (hell : 0 < ell) (w : WQ (geomOf ell 2 (neS ell M R)))
    (h : ContinuousLinearMap.adjoint (Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R)))) w = 0) :
    w = 0 := by
  have hperp : ∀ u : SiteL2 (scaleUp ell 2 (neLu M R)),
      ⟪Bq (geomOf ell 2 (neS ell M R)) (flatCfg : Cfg (scaleUp ell 2 (neLu M R))) u, w⟫ = 0 := by
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_right, h, inner_zero_right]
  have all : ∀ m : ℕ, ∀ ρ : RowIdx (geomOf ell 2 (neS ell M R)), 2 - (ρ.1.1 : ℕ) ≤ m → w ρ = 0 := by
    intro m
    induction m with
    | zero =>
      intro ρ hρ
      exact corner_zero hP hell w hperp ρ (fun ρ' hlt => by
        have := lev_le_row ρ'; omega)
    | succ m ih =>
      intro ρ hρ
      exact corner_zero hP hell w hperp ρ (fun ρ' hlt => ih ρ' (by
        have := lev_le_row ρ'; omega))
  exact PiLp.ext (fun ρ => all 2 ρ (by omega))

#print axioms Bq_star_inj

end AdalyFormal.CoverOmegaTwo

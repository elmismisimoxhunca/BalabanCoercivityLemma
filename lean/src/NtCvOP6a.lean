import NtCvOP4

/-!
# CvOP6a -- bridge: `SGat` (Frobenius-normed `M₂`) gives entrywise analyticity (lane omega/near2/struct)

`EA f t0` : all four complex entries of `t ↦ f t` are real-analytic at `t0`.  The entry map is a continuous linear functional
on `M₂` with the Frobenius norm; this is the only place the Frobenius scope is used for the `SuTwo`/`BondFnL2` side.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)

/-- all entries analytic. -/
def EA (f : ℝ → M2) (t0 : ℝ) : Prop := ∀ i j, AnalyticAt ℝ (fun t => f t i j) t0

theorem entAna_of_SGat {W : ℝ → SU2} {t0 : ℝ} (h : SGat t0 W) : EA (fun t => ((W t : SU2) : M2)) t0 := by
  intro i j
  have h1 : AnalyticAt ℝ (fun t => ((W t : SU2) : M2)) t0 := (h : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) t0).analyticAt
  let ent : M2 →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact (ent.analyticAt _).comp h1

end AdalyFormal.CoverOmega.Struct

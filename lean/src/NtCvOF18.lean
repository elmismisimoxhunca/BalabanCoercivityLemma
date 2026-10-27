import NtCvOF17
import NsCS1

/-!
# CvOF18 -- the conditional refutation of `P428Target8NCWDH` along the staggered path (lane omega)

`IsCrossingN`: `cs` is THE first crossing of the Z-chain form `qF_c` on the nested instance (PSD at `cs` with a nonzero null vector,
positive definite on `(cs, 1]`); `NearUnits`: arbitrarily close to the crossing there is a `t` (with `cos t` above `cs`) at which every printed
object of the genuine family exists (`WellDefG`).
Theorem `nested_stag_failAt`: for a crossing `cs` produced by the chain, `NearUnits` implies `FailAt`.
Theorem `not_WDH_of_nearUnits`: `NearUnits` at the crossing for infinitely many `(m, R)` refutes `P428Target8NCWDH`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- arbitrarily close to `cs`, with `cos t` above `cs`, every printed object exists. -/
def NearUnits (ell M R : ℕ) (hell : 0 < ell) (a cs : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < tcap ell ∧ cs < Real.cos t ∧ Real.cos t < cs + ε ∧
    GenP.WellDefG (gparams ell 2 (neLu M R) hell (neS ell M R) (stagU ell M R t) a (neLam M R))

end AdalyFormal.CoverOmega

import DrRed1
import D1Ginv
import ZR8DataB

/-!
# DrPath1 -- exterior-only paths: the localised data and `Delta2_loc` are constant, `Ginv_lit` is `Ginv_lit(0) + (pE W0* (Delta_t - Delta_0) W0 iE)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- PIN: the localised data of `dataS selIn selIn` is the frozen r8 data. -/
theorem dataS_selIn_eq_data (P : IngrBParams) : dataS selIn selIn P = P.data := rfl

theorem dataS_loc_congr (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 2 ≤ P.ell)
    (hroom : 17 * P.ell ≤ R * M) (U' : Cfg (scaleUp P.ell P.k P.Lu))
    (hUU : ∀ e : Bond (scaleUp P.ell P.k P.Lu), BothIn (P.S.Om 0) e → P.U e = U' e) :
    dataS selIn selIn ({ P with U := U' } : IngrBParams) = dataS selIn selIn P :=
  data_congr P hS hell hroom U' hUU

#print axioms dataS_loc_congr

section lit
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu)) (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)), e ∉ Zb (S.Om 0) → U t e = U 0 e)

include hS hell hroom hUU in
/-- along an exterior-only path (the configurations agree off the bonds with no endpoint in `Ω₀`), the literal `Ginv` changes only through `Delta`:
`Ginv_lit(t) = Ginv_lit(0) + pE W0* (Delta_t - Delta_0) W0 iE`. -/
theorem Ginv_lit_path (sJ : PlaqSel) (t : ℝ) :
    (dataS selAll sJ (gparams ell k Lu hell0 S (U t) a Lam)).Ginv =
      (dataS selAll sJ (gparams ell k Lu hell0 S (U 0) a Lam)).Ginv +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop (geomOf ell k S) (U 0) a))).comp (iE (geomOf ell k S))) := by
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U t e = U 0 e :=
    fun e he => hUU t e (fun hz => Zb_not_bothIn _ hz he)
  have hW := Wop_congr_Z hS hell hroom (hUU t) a
  have hT := Tfull_congr hS hell hroom hBoth
  have hsec := sector_congr hS hell hroom hBoth
  unfold BaseDataS.Ginv dataS
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullS, DeltaS, selAll, hW, hT, hsec]
  ext1 y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  abel

end lit
#print axioms Ginv_lit_path

end AdalyFormal.D1Residual

import D1Path
import D1Collapse

/-!
# D1Ginv -- along the path `U_θ`, the literal `Ginv` changes only through `Δ_θ`:
`Ginv(θ) = Ginv(0) + pE W₀* (Δ_θ − Δ_0) W₀ iE`, with `W₀ = W(U_0)` (flat) the same operator for every `θ`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the parameter point at `θ`. -/
noncomputable def Pth (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) : IngrBParams :=
  gparams ell k Lu hell S (Uth (S.Om 0) θ) a Lam

/-- the literal `Ginv` at `θ`. -/
noncomputable def Fth (sJ : PlaqSel) (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) :
    ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) :=
  (dataS selAll sJ (Pth ell k Lu hell S a Lam θ)).Ginv

theorem Fth_diff (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (θ : ℝ) :
    Fth sJ ell k Lu hell0 S a Lam θ = Fth sJ ell k Lu hell0 S a Lam 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (Uth (S.Om 0) θ) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (Uth (S.Om 0) 0) Set.univ)).comp
          (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a))).comp (iE (geomOf ell k S))) := by
  have hUU : ∀ e : Bond (scaleUp ell k Lu), e ∉ Zb (S.Om 0) → Uth (S.Om 0) θ e = Uth (S.Om 0) 0 e :=
    fun e he => Uth_eq_off_Z _ _ _ e he
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → Uth (S.Om 0) θ e = Uth (S.Om 0) 0 e :=
    fun e he => hUU e (fun hz => Zb_not_bothIn _ hz he)
  have hW := Wop_congr_Z hS hell hroom hUU a
  have hT := Tfull_congr hS hell hroom hBoth
  have hsec := sector_congr hS hell hroom hBoth
  unfold Fth Pth BaseDataS.Ginv dataS
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullS, DeltaS, selAll, hW, hT, hsec]
  ext1 y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  abel

end AdalyFormal.D1Literal

import MA6
import MA1
import MA2
import MI22
import GW1

/-!
# MA7 -- `chart_core`: the M1 inequality at a configuration, from the abstract inputs (lane m1_assembly_20261014)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
namespace AdalyFormal.M1Assembly

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp OnLambdaTildeIn TorusOK)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (gparams pe tauAdj_apply pe_injective LambdaOK2 GenP.genForm GenP.genC GenP.WellDef GenP.Nmat)
open AdalyFormal.GenuineU1 (bondsE unitField)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.M1IMS (HatPack HolRegime Fform Ymass sigG)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.StatementLaneR6 (plaqMask)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)


/-- `<A, Ginv A> = Fform` for `y = iA` (MI18 `ginv_form`, unfolded). -/
theorem ginv_eq_Fform {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 ≤ a)
    (hu : IsUnit (AdalyFormal.M1Site.LP (geomOf ell k S) V a))
    (A : ↥(bondSupp (gparams ell k Lu hell0 S V a Lam).G)) :
    ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Ginv A⟫ = Fform S ell k V a (A : BondFnL2 (scaleUp ell k Lu)) :=
  AdalyFormal.M1IMS.ginv_form hell0 S V a Lam ha hu A

/-- the mass form of `A` is `||Ymass y||^2`. -/
theorem mass_eq_Ymass {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (V : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (ha : 0 ≤ a)
    (A : ↥(bondSupp (gparams ell k Lu hell0 S V a Lam).G)) :
    ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Mass A⟫
      = ‖Ymass (geomOf ell k S) V a (A : BondFnL2 (scaleUp ell k Lu))‖ ^ 2 := by
  have h3 : ⟪A, (gparams ell k Lu hell0 S V a Lam).data.Mass A⟫
      = ⟪(A : BondFnL2 _), MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) V) A⟫ := by
    show ⟪A, pE _ (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) V) (iE _ A))⟫ = _
    rw [pE_inner_right]; rfl
  rw [h3]
  exact AdalyFormal.M1IMS.inner_MassFull_eq _ V a ha _

open Classical in
/-- the touching support of `C B~` sits on embedded `frakB` bonds (generic `Q`). -/
theorem Cop_frakB {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (hu : ∀ μ, 1 ≤ Lu μ) (hMR : 1 ≤ R * M) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : AdalyFormal.StatementLane.LambdaOK ell M R k S Lam)
    (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (AdalyFormal.Balaban.LatticeOperators.CoarseBond Lu ell → SuTwo))
    (Bt : Bond Lu → SuTwo) (hBT : OnLambdaT Lam Bt) (e : Bond Lu)
    (he : unitBondEmb ell k Lu hell0 e ∉ bondsLam (geomOf ell k S) k) : Cop Lam Q Bt e = 0 := by
  by_contra hne
  apply he
  refine AdalyFormal.StatementLaneG.touching_in_frakB hell0 hu hMR hS hL e ?_
  by_cases hdr : AdalyFormal.StatementLane.IsDroppedIn Lam ell e
  · exact AdalyFormal.StatementLaneG.dropped_touches_lam hell0 hd hdr
  · rw [Cop_id Lam Q Bt e hdr] at hne
    by_contra hnt
    exact hne (hBT e hnt)

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.ginv_eq_Fform
#print axioms AdalyFormal.M1Assembly.mass_eq_Ymass
#print axioms AdalyFormal.M1Assembly.Cop_frakB

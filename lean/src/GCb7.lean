import GCb6

/-!
# GCb7 -- `J` (3.11) and bond-level `Δ`, `Δ_π` equivariant; `Jf` of the genuine family
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply RMap_one conjByAmbient)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.IngredientFamily
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem cjM_sum {ι : Type*} (g : SU2g) (s : Finset ι) (f : ι → Mat2) :
    cjM g (∑ i ∈ s, f i) = ∑ i ∈ s, cjM g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cjM_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cjM_add, ih]

theorem JfieldLoc_gauge (γ : GaugeFn L) (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    JfieldLoc P (periodicGaugeTransform γ U) x μ = cjM (γ x) (JfieldLoc P U x μ) := by
  unfold JfieldLoc
  rw [cjM_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs
  · exact (cjM_zero _).symm
  · have : (fun y => FnuMuLoc P (periodicGaugeTransform γ U) ν μ y)
        = fun y => cjM (γ y) (FnuMuLoc P U ν μ y) := funext (fun y => FnuMuLoc_gauge γ P U ν μ y)
    rw [this]
    exact DstarDir_gauge γ U ν _ x

theorem JSU2Loc_gauge (γ : GaugeFn L) (η : ℝ) (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L)
    (b : Bond L) :
    JSU2Loc η P (periodicGaugeTransform γ U) b = RMap (γ b.1) (JSU2Loc η P U b) := by
  apply Subtype.ext
  rw [coe_RMap_gauge]
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (periodicGaugeTransform γ U) b.1 b.2
    = cjM (γ b.1) (((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P U b.1 b.2)
  rw [JfieldLoc_gauge, cjM_smul]

theorem Jf_gauge (P : IngrBParams) (γ : GaugeFn P.Lf) :
    ({ P with U := periodicGaugeTransform γ P.U } : IngrBParams).Jf = adBL γ P.Jf := by
  refine PiLp.ext (fun b => ?_)
  show -(JSU2Loc 1 (plaqIn P.G.Om0) (periodicGaugeTransform γ P.U) b) = RMap (γ b.1) (-(JSU2Loc 1 (plaqIn P.G.Om0) P.U b))
  rw [JSU2Loc_gauge, map_neg]

theorem Delta_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (x : BondFnL2 L) :
    Delta G (periodicGaugeTransform γ U) (adBL γ x) = adBL γ (Delta G U x) :=
  deltaKLocCLM_gauge γ U (plaqIn G.Om0) x

theorem DpiFull_gauge (G : TowerGeom L) (γ : GaugeFn L) (U : Cfg L) (a : ℝ) (x : BondFnL2 L) :
    DpiFull G (periodicGaugeTransform γ U) a (adBL γ x) = adBL γ (DpiFull G U a x) := by
  unfold DpiFull
  simp only [ContinuousLinearMap.comp_apply]
  rw [Wop_gauge, Delta_gauge]
  exact adjoint_eqv (adBL γ) (adBL γ) (Wop G U a) (Wop G (periodicGaugeTransform γ U) a)
    (fun z => Wop_gauge G γ U a z) _

#print axioms JfieldLoc_gauge
#print axioms JSU2Loc_gauge
#print axioms Jf_gauge
#print axioms Delta_gauge
#print axioms DpiFull_gauge

end AdalyFormal.GaugeCov

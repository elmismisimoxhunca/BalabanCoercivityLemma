import GCz2

/-!
# GCz3 -- transfer of the printed inequality (`InstIneq`) along a gauge transformation.
`InstIneq ell k hell a Lu γ₀ S Lam (U^γ) ↔ InstIneq ell k hell a Lu γ₀ S Lam U` for EVERY fine gauge `γ` (all sites of the fine torus).
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.GaugeCov
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA gaugeActA_apply gaugeInv gaugeTransform_inv bondEnergy_gauge)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem instIneq_of_gauge {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ₀ : ℝ}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)}
    (γ : GaugeFn (scaleUp ell k Lu))
    (h : InstIneq ell k hell a Lu γ₀ S Lam (periodicGaugeTransform γ U)) :
    InstIneq ell k hell a Lu γ₀ S Lam U := by
  intro Bt h1 h2
  have hP := h (gaugeActA (uOf ell k Lu hell γ) Bt)
    ((onLambdaTildeIn_gauge (uOf ell k Lu hell γ) Lam ell Bt).mpr h1)
    ((onLambdaT_gauge (uOf ell k Lu hell γ) Lam Bt).mpr h2)
  have hC := genC_gauge (gparams ell k Lu hell S U a Lam) γ Bt
  have hF := genForm_gauge_main (gparams ell k Lu hell S U a Lam) γ
    (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))
  rw [bondEnergy_gauge] at hP
  have hP' : γ₀ * AdalyFormal.Balaban.RegularUPerturbation.bondEnergy Bt ≤
      GenP.genForm (gaugeP (gparams ell k Lu hell S U a Lam) γ)
        (WithLp.toLp 2 (gaugeActA (uOf ell k Lu hell γ) (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))) := by
    rw [← hC]; exact hP
  have hF' : GenP.genForm (gaugeP (gparams ell k Lu hell S U a Lam) γ)
        (WithLp.toLp 2 (gaugeActA (uOf ell k Lu hell γ) (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)))
      = GenP.genForm (gparams ell k Lu hell S U a Lam) (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)) := hF
  rw [hF'] at hP'
  exact hP'

/-- **Gauge invariance of the printed inequality.** -/
theorem instIneq_gauge_iff {ell k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {γ₀ : ℝ}
    {S : Tower (scaleUp ell k Lu)} {Lam : Set (PeriodicLatticeSite Lu)} {U : LinkCfg (scaleUp ell k Lu)}
    (γ : GaugeFn (scaleUp ell k Lu)) :
    InstIneq ell k hell a Lu γ₀ S Lam (periodicGaugeTransform γ U) ↔ InstIneq ell k hell a Lu γ₀ S Lam U := by
  constructor
  · exact instIneq_of_gauge γ
  · intro h
    have := instIneq_of_gauge (hell := hell) (a := a) (γ₀ := γ₀) (S := S) (Lam := Lam)
      (U := periodicGaugeTransform γ U) (gaugeInv γ)
    rw [gaugeTransform_inv] at this
    exact this h

#print axioms instIneq_of_gauge
#print axioms instIneq_gauge_iff

end AdalyFormal.GaugeCov

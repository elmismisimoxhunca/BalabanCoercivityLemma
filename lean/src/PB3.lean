import ZXG3J2
import ZXR3E
import NF4
import PNF3
import GN12

/-!
# PB3 -- item (3): the plaquette `Δ'` bound NF4 and the curvature identity NF3 on the r7 carrier.

* `NF4` (`NonflatHunit.abs_inner_deltaPrime_le_plaq`) is IMPORTED VERBATIM: its import closure is tree-only
  (`LemmaAssemblyNormalized`, `DeltaPrimeBound`), no R2 module, so the original object is the object used here.
* `theta_ported`: the hypothesis `hdp` of `phi_drift_decomp` (GN12): for the genuine localised form on the full tower
  `|deltaPrimeBilL2NormLoc U (plaqIn Ω₀) x x| ≤ (272 α₀) ‖x‖²` from `PlaqDef α₀ U` (so `θ = 272 α₀`).
* `PNF3` = `NF3` with the unused `import R2Ops2` removed (NF3's content is tree-only: `curlValueCovariant_gradValueCovariant`);
  `curl_grad_L2_ported` states the L²-form on the r7 carrier: `Σ_p ‖curl_U D_U ν‖² ≤ 12 ζ² Σ_x ‖ν‖²`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc

theorem theta_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) {α₀ : ℝ}
    (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U) (x : BondFnL2 (scaleUp ell k Lu)) :
    |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x|
      ≤ (272 * α₀) * ‖x‖ ^ 2 := by
  have hOm : (GF ell k Lu).Om0 = Set.univ := fullTower_Om0 ell k Lu
  rw [hOm, AdalyFormal.StatementLaneG.plaqIn_univ, AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc_univ]
  have h := AdalyFormal.NonflatHunit.abs_inner_deltaPrime_le_plaq hα₀ U hpl x
  have e : (inner ℝ x (AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeCLMNormalized U x) : ℝ)
      = AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeBilL2Normalized U x x :=
    AdalyFormal.Balaban.DeltaPrimeOperator.inner_deltaPrimeOpNormalized U x x
  rw [e] at h
  linarith [h]

#print axioms theta_ported

end AdalyFormal.PortSlice

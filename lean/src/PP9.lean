import SG9
import PP5
import PP8
import OGP0

/-!
# SG10 -- F3 (`MassComm`) from per-row anchor charts (lane m2_fields123_20261015)

* `rowQ_of_chart12`  : a chart `AnchorChart12` at the base point `b.1` of the row `p` (radius `rhoT ell j`) gives `RowQ U p S*` with `S* = SstarM ell 12 M (ℓ³·2α₀)`
  (`regData_M112` for `V^{g'}`, then `Qfull_row_congr_agree`, `RowQ_gauge`).
* `rowQ_level012`    : rows of level `0` read no background: `RowQ U p S*` for ANY `U` (flat configuration + `Qfull_row_congr`).
* `massComm_of_charts12` : the SK1 field `MassComm ell M k 1 5 S U a (CMcStar ell M 1 5 a (SstarM ell 12 M (alpha1 ell α₀)))` from a chart at every row of level `≥ 1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.OneGap12

open AdalyFormal.M2F123
open AdalyFormal.OneGap12

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt rhoT)
open AdalyFormal.NonflatJet
open AdalyFormal.M1IMS
open AdalyFormal.TowerLoc
open SmallnessBridge.Assemble (loopFactorBound)

variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem rowQ_of_chart12 (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)))) < r0)
    (U : LinkCfg (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S))
    (hch : AnchorChart12 ell M k S U α₀ η p.2.1.1 (rhoT ell p.1)) :
    RowQ ell k Lu S U (SstarM ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀))) p := by
  obtain ⟨g, V, ⟨g', A, hVg, hB⟩, hag⟩ := hch
  have hell0 : 0 < ell := by omega
  have hα' : 0 ≤ (ell : ℝ) ^ 3 * (2 * α₀) := by positivity
  have hag' : AgreeAt (Ball p.2.1.1 (rhoT ell p.1)) (periodicGaugeTransform (fun z => g' z * g z) U)
      (periodicGaugeTransform g' V) := by
    rw [gauge_comp12]
    exact AdalyFormal.M2Unit.agree_gauge hag g'
  have D := regData_M112 hell2 hS hroom hT3 V g' A hVg hB hη hα' ha1 hsm4 hsmA hrr
  have h1 := RowQ_of_RegData hell0 D p
  have h2 : RowQ ell k Lu S (periodicGaugeTransform (fun z => g' z * g z) U) _ p :=
    RowQ_transfer hell0 p (fun y => Qfull_row_congr_agree hell0 _ _ p hag' y) h1
  exact RowQ_gauge _ U p h2

theorem m1Bounds_zero12 (hell : 0 < ell) (hM : 0 < M) {α₀ η : ℝ} (hα : 0 < α₀) (hη : 0 < η) :
    AdalyFormal.OneGap12.M1Bounds12 S ell M 12 k α₀ η (fun _ : Bond (scaleUp ell k Lu) => (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((12 : ℕ) : ℝ) * M * α₀ * (((ell : ℝ) ^ n * η)⁻¹ ^ 1) := fun n => by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  refine ⟨fun e => ⟨by simp, by simp⟩, fun e j hj => ?_, fun μ ν x j h1 h2 => ?_, trivial⟩
  · rw [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]; exact hpos j
  · simp only [sub_self, smul_zero]
    rw [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
    have : (0 : ℝ) < M := by exact_mod_cast hM
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity

theorem rowQ_level012 (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hroom : 17 * ell ≤ R * M) (hM : 0 < M)
    (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {α₀ η : ℝ} (hη : 0 < η) (hα : 0 < α₀)
    (ha1 : (12 : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1)
    (hsmA : (1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)) ≤ 1 / (1000 * (ell : ℝ) ^ 4))
    (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 12 M ((ell : ℝ) ^ 3 * (2 * α₀)))) < r0)
    (U : LinkCfg (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (hp : (p.1 : ℕ) = 0) :
    RowQ ell k Lu S U (SstarM ell 12 M ((ell : ℝ) ^ 3 * (2 * α₀))) p := by
  have hell0 : 0 < ell := by omega
  have hα' : 0 < (ell : ℝ) ^ 3 * (2 * α₀) := by positivity
  have hU : ∀ e : Bond (scaleUp ell k Lu),
      ((periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) (trivialU (scaleUp ell k Lu)) e :
        Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • (fun _ : Bond (scaleUp ell k Lu) => (0 : Matrix (Fin 2) (Fin 2) ℂ)) e) := by
    intro e
    have : periodicGaugeTransform (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
        (trivialU (scaleUp ell k Lu)) e = 1 := by
      simp [periodicGaugeTransform, trivialU]
    rw [this, smul_zero, NormedSpace.exp_zero]
    rfl
  have D := regData_M112 hell2 hS hroom hT3 (trivialU (scaleUp ell k Lu)) (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (fun _ : Bond (scaleUp ell k Lu) => (0 : Matrix (Fin 2) (Fin 2) ℂ)) hU (m1Bounds_zero12 hell0 hM hα' hη) hη hα'.le ha1 hsm4 hsmA hrr
  have h1 := RowQ_of_RegData hell0 D p
  refine RowQ_transfer hell0 p (fun y => Qfull_row_congr hell0 _ _ p (fun l hl => by omega) y) h1

end AdalyFormal.OneGap12
#print axioms AdalyFormal.OneGap12.rowQ_of_chart12
#print axioms AdalyFormal.OneGap12.m1Bounds_zero12
#print axioms AdalyFormal.OneGap12.rowQ_level012

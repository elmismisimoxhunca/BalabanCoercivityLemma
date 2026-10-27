import AU_CUT
import TL6b
import AU_TL5

open AdalyFormal.AllU (M1BoundsU M1RegularU)

/-! AU copy of TL6b: M1Regular -> M1RegularU, affected declarations only (lane allc_20261016, uniform-in-c route). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist bigSide)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.CurvBlock (dv)

variable {L : PeriodicLatticeExtent}

section assembly
variable {ell M R k f : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)} {α₀ η : ℝ}
  (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R) (hroom : 17 * ell ≤ R * M)
  (hT3 : ∀ μ, 3 ≤ Lu μ + 1) (U : LinkCfg (scaleUp ell k Lu))
  (g : PeriodicLatticeSite (scaleUp ell k Lu) → Matrix.specialUnitaryGroup (Fin 2) ℂ)
  (A : Bond (scaleUp ell k Lu) → Matrix (Fin 2) (Fin 2) ℂ)
  (hU : ∀ e : Bond (scaleUp ell k Lu), ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
  (hB : AdalyFormal.AllU.M1BoundsU S ell M f k α₀ η A) (hη : 0 < η) (hα0 : 0 ≤ α₀)
  (ha1 : (f : ℝ) * M * α₀ ≤ 1)
  (hsm4 : 4000000 * (ell : ℝ) ^ 2 * rho1 f M α₀ ≤ 1)
  (hsmA : (1 + 3 * Real.pi) * rho1 f M α₀ ≤ 1 / (1000 * (ell : ℝ) ^ 4))
  (hrr : Real.pi / 2 * ((loopFactorBound ell : ℝ) * ((1 + 3 * Real.pi) * rho1 f M α₀)) < r0)

include hell2 hS hroom hT3 hU hB hη hα0 ha1 hsm4 in
/-- **the regional class from `M1RegularU`** (in its gauge `U^g`): the blocked links over the cone of a level-`j` row are
bounded by `epsM j l` (aligned bonds, `l < j`). -/
theorem hcl_M1U (j : Fin (k + 1)) (l : ℕ) (hlk : l < k) (z : PeriodicLatticeSite (scaleUp ell k Lu))
    (hzW : z ∈ WM ell k S j l) (hzA : z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l)) (μ : Fin 3) :
    frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
      ≤ epsM ell f M α₀ j l := by
  have hell : 0 < ell := by omega
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  have hlj : l < (j : ℕ) := hzW.1
  have hcone := cone_in_Om hell2 hS hroom hjk hzW
  have ha0 : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  have hlnk : l ≤ (j : ℕ) - 1 := by omega
  have h := tower_link_locU hell2 hell S hT3 U g A hU hB hη ha0 ha1 hsm4 ((j : ℕ) - 1) l (by omega) hlnk hlk
    z hzA μ hcone
  unfold epsM rho1
  rw [if_pos hlj]
  exact h

end assembly

end AdalyFormal.TowerLoc


import ScaleFittedTower
import TorusRaw

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
noncomputable section
namespace Prop1.ScaleFittedTest.Stride

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 torus)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open DepthUniformity.Strided (orientedPlaqHolS)
open Prop1.RawBoundary (torusScale)

def witL : PeriodicLatticeExtent := fun _ => 7
abbrev Site := PeriodicLatticeSite witL
abbrev Edge := PeriodicLatticeEdge witL

def profile : Fin 8 → ℚ := ![0, 0, 1, 1, 0, 0, -1, -1]
def qField : PeriodicLinkConfiguration (Multiplicative ℚ) witL :=
  fun e => Multiplicative.ofAdd (if e.2 = 1 then profile (e.1 0) else 0)
def field (t : ℝ) : PeriodicLinkConfiguration SU2 witL :=
  fun e => torusScale t (qField e)
def corner : Site := (![2, 6, 0] : Fin 3 → Fin 8)
def origin : Site := fun _ => 0

theorem extent_dvd : ∀ μ : Fin 3, 2 * 2 ∣ (witL μ + 1) := by decide +kernel

theorem corner_only_ell_aligned :
    corner ∈ CoarseLattice witL 2 ∧ corner ∉ CoarseLattice witL (2 * 2) := by
  simp only [mem_CoarseLattice]
  decide +kernel

theorem input_coefficients : ∀ (y : Site) (μ ν : Fin 3),
    let q := Multiplicative.toAdd (orientedPlaqHolS 2 qField y μ ν)
    q = 0 ∨ q = 1 ∨ q = -1 := by decide +kernel

theorem origin_input_coefficient :
    Multiplicative.toAdd (orientedPlaqHolS 2 qField origin 0 1) = 1 := by
  decide +kernel

end Prop1.ScaleFittedTest.Stride

#print axioms Prop1.ScaleFittedTest.Stride.corner_only_ell_aligned
#print axioms Prop1.ScaleFittedTest.Stride.input_coefficients

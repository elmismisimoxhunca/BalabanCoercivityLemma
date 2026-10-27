import D1Lit

/-!
Round 3 / S-1 proper-domain pin. This file defines the open headline and its
exact negation; it proves neither. Only frozen lean/src modules are imported.

The five touching-class declarations are copied verbatim from the round-2
S-2 pin. plaqCorner and selCorner are copied verbatim from the round-2 S-1
pin. The expanded headline changes only that pin's name and class predicate.
See PIN.md for provenance, quantifier order, and departures from the print.
-/

set_option autoImplicit false
set_option maxRecDepth 8000

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

namespace Round3.S1Proper

-- Verbatim from AHP/round2/s1-touching/pin/Statement.lean.
def plaqCorner {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L)) :
    Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.2 ∈ S
    ∨ periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

variable {L : PeriodicLatticeExtent}

-- Verbatim from AHP/round2/s2-nonvacuity/pin/Statement.lean.
def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

def CoversPlaqFour (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

def CurlReadsTouch (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  TouchBond sites (periodicLatticeShift x a, b) ∧ TouchBond sites (x, b) ∧
  TouchBond sites (periodicLatticeShift x b, a) ∧ TouchBond sites (x, a)

def PerCubeRegularTouch (ell M f k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, TouchBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        TouchBond sites ((x, ν) : Bond L) → TouchBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReadsTouch sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReadsTouch sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def ClassCoupledFour (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqFour ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

-- Verbatim selector from AHP/round2/s1-touching/pin/Statement.lean.
def selCorner : PlaqSel := fun _ G => plaqCorner G.Om0

/-- Same quantifiers and constants order as expanded ZT5A.P428Target8.
The class is ClassCoupledFour, not ClassCoupledCorner. Both Delta and J use
the corner selector through the actual D1Lit.InstIneqS. Proper domains are
allowed, not assumed away; no extra inverse guard or shell bound is added. -/
def P428TouchFour : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U

/-- The actual changed-operator headline, not a class-inclusion comparison. -/
def GoalPos1 : Prop := P428TouchFour

/-- Exact negation of the positive headline, with all thresholds retained. -/
def GoalNeg1 : Prop := ¬ GoalPos1

-- Well-formedness and definition dependencies only; these do not prove goals.
#check plaqCorner
#check TouchBond
#check CoversPlaqFour
#check CurlReadsTouch
#check PerCubeRegularTouch
#check ClassCoupledFour
#check selCorner
#check P428TouchFour
#check GoalPos1
#check GoalNeg1

#print axioms plaqCorner
#print axioms TouchBond
#print axioms CoversPlaqFour
#print axioms CurlReadsTouch
#print axioms PerCubeRegularTouch
#print axioms ClassCoupledFour
#print axioms selCorner
#print axioms P428TouchFour
#print axioms GoalPos1
#print axioms GoalNeg1

end Round3.S1Proper

/-!
Round 7 / s1-odd. Everything above is the complete round-3 pin verbatim,
including its historical comments. The new targets below quantify every
blocking factor, rather than negating a headline at one chosen factor.
The mass window is explicitly 0 < a < 4; no claim is made for a >= 4.
-/

namespace Round7.S1Odd

open Round3.S1Proper

/-- The exact fixed-ell, fixed-a slice of P428TouchFour. Only its outer
ell/hell/a/positivity binders are removed. In particular R0 remains after m,
and the positive cap and coercivity constant remain after R. -/
def P428TouchFourAt (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    SidePow6 ell (ell ^ m) a ∧
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)),
          ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U

/-- Every blocking factor and every mass in the stated open window fail,
with all scale, radius, cap and coercivity-constant quantifiers retained. -/
def Goal1 : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → a < 4 →
    ¬ P428TouchFourAt ell hell a

/-- The later-paper odd-L range, as a direct restriction of Goal1.
Oddness is not needed by the proposed general-ell construction. -/
def Goal2 : Prop :=
  ∀ (ell : ℕ), Odd ell → (hlarge : 11 < ell) →
    ∀ (a : ℝ), 0 < a → a < 4 → ¬ P428TouchFourAt ell (by omega) a

#check P428TouchFourAt
#check Goal1
#check Goal2

#print axioms P428TouchFourAt
#print axioms Goal1
#print axioms Goal2

end Round7.S1Odd

/-! Round 11: the exact all-positive-mass and eventual-large-mass targets. -/
namespace Round11
open Round7.S1Odd

def GoalAllA : Prop := ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ¬ P428TouchFourAt ell hell a

def GoalLargeA : Prop := ∃ a₁ : ℝ, ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), a₁ ≤ a → P428TouchFourAt ell hell a

#print axioms GoalAllA
#print axioms GoalLargeA
end Round11

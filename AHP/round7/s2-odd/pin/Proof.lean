import D1Final
import ZR8Class

import ZT5A

/-!
# Round 2 / S-2: proper-domain non-vacuity, not another inclusion comparison

Only the eight touching-class definitions below are copied from the Stage-B
file AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean. Their declaration text
is verbatim; the namespace is new. All other underlying definitions are the
actual frozen declarations imported through ZT5A. No AHP module is imported.

GoalPos1/GoalNeg1 concern ClassCoupledFour; GoalPos2/GoalNeg2 concern
ClassCoupledCorner. The positive goals ask for cofinal, capped, proper-domain
instances with genuine nonzero input fields for frozen InstIneq. The negative
goals assert universal empty/whole-torus saturation, a stronger assertion than
the negation of the corresponding positive goal. Only the logical implications
between these goal propositions are proved here; none of the four goals is.
See PIN.md for quantifier order, print departures, and the acceptance boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.AHP.Round2.S2Nonvacuity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-! ## Verbatim Stage-B definitions (no change to the cube family) -/

def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

def CoversPlaqFour (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

def plaqCorner (S : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S ∨
      periodicLatticeShift p.1 p.2.1.2 ∈ S ∨
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

def CoversPlaqCorner (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) →
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

def ClassCoupledCorner (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

/-! ## Actual capped instances, including the test space of InstIneq

The exponent m is explicit: M = ell^m, never just an arbitrary positive M.
The scalar a does not occur in any hypothesis below; a = 1 is an available
positive headline parameter. The callers in GoalPos1/2 require ell >= 2 and
m >= 1, hence SidePow6 ell (ell^m) 1. No inequality or inverse is postulated.
-/

def ProperFourAt (ell m R : ℕ) (a₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (Lu : PeriodicLatticeExtent)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ),
    1 ≤ k ∧
    TorusOK ell (ell ^ m) Lu ∧
    Admissible ell (ell ^ m) R k S ∧
    LambdaOK2 ell (ell ^ m) R k S Lam ∧
    (S.Om 0).Nonempty ∧ S.Om 0 ≠ Set.univ ∧
    0 < α₀ ∧ (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
    ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
    ∃ Bt : Bond Lu → SuTwo,
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
      Bt ≠ 0 ∧ 0 < bondEnergy Bt

def ProperCornerAt (ell m R : ℕ) (a₀ : ℝ) : Prop :=
  ∃ (k : ℕ) (Lu : PeriodicLatticeExtent)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ),
    1 ≤ k ∧
    TorusOK ell (ell ^ m) Lu ∧
    Admissible ell (ell ^ m) R k S ∧
    LambdaOK2 ell (ell ^ m) R k S Lam ∧
    (S.Om 0).Nonempty ∧ S.Om 0 ≠ Set.univ ∧
    0 < α₀ ∧ (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧
    ClassCoupledCorner ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
    ∃ Bt : Bond Lu → SuTwo,
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
      Bt ≠ 0 ∧ 0 < bondEnergy Bt

/-! ## The four open goals -/

/-- Four-bond class: a proper-domain witness family that reaches arbitrarily
large m and then arbitrarily large R, and works below every positive cap.
One fixed ell >= 2 suffices; no slab, depth, flatness, or parity is prescribed. -/
def GoalPos1 : Prop :=
  ∃ ell : ℕ, 2 ≤ ell ∧
    ∀ mLower : ℕ, ∃ m : ℕ, 1 ≤ m ∧ mLower ≤ m ∧
      ∀ RLower : ℕ, ∃ R : ℕ, RLower ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ → ProperFourAt ell m R a₀

/-- Four-bond class: every headline-side-condition admissible member has
empty or full base domain. The absence of Lambda/cap premises and the range
over all natural R make this stronger than a threshold-only no-go statement. -/
def GoalNeg1 : Prop :=
  ∀ (ell m R k : ℕ), 2 ≤ ell → 1 ≤ m → 1 ≤ k →
    ∀ (Lu : PeriodicLatticeExtent), TorusOK ell (ell ^ m) Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (α₀ : ℝ), 0 < α₀ →
    ∀ (U : LinkCfg (scaleUp ell k Lu)),
      ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      S.Om 0 = ∅ ∨ S.Om 0 = Set.univ

/-- Corner class: exactly the same non-vacuity demand as GoalPos1, with only
the plaquette-coverage antecedent changed through ClassCoupledCorner. -/
def GoalPos2 : Prop :=
  ∃ ell : ℕ, 2 ≤ ell ∧
    ∀ mLower : ℕ, ∃ m : ℕ, 1 ≤ m ∧ mLower ≤ m ∧
      ∀ RLower : ℕ, ∃ R : ℕ, RLower ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ → ProperCornerAt ell m R a₀

/-- Corner class: universal empty/whole-torus saturation. This is independent
of, and must not be conflated with, the four-bond saturation question. -/
def GoalNeg2 : Prop :=
  ∀ (ell m R k : ℕ), 2 ≤ ell → 1 ≤ m → 1 ≤ k →
    ∀ (Lu : PeriodicLatticeExtent), TorusOK ell (ell ^ m) Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
    ∀ (α₀ : ℝ), 0 < α₀ →
    ∀ (U : LinkCfg (scaleUp ell k Lu)),
      ClassCoupledCorner ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      S.Om 0 = ∅ ∨ S.Om 0 = Set.univ

/-! ## Sanity checks: negative goals really exclude their positive partners

These are only logical implications. They do not prove either saturation
statement, exhibit a touching-class member, or close an audit item.
-/

theorem goalNeg1_implies_not_goalPos1 : GoalNeg1 → ¬ GoalPos1 := by
  intro hneg hpos
  obtain ⟨ell, hell, hfamily⟩ := hpos
  obtain ⟨m, hm, _, hRfamily⟩ := hfamily 1
  obtain ⟨R, _, hcapped⟩ := hRfamily 0
  obtain ⟨k, Lu, S, Lam, U, α₀, hk, hT, hS, _, hne, hproper,
    hα, _, hclass, _⟩ := hcapped 1 zero_lt_one
  rcases hneg ell m R k hell hm hk Lu hT S hS α₀ hα U hclass with hempty | hfull
  · obtain ⟨x, hx⟩ := hne
    rw [hempty] at hx
    exact hx
  · exact hproper hfull

theorem goalNeg2_implies_not_goalPos2 : GoalNeg2 → ¬ GoalPos2 := by
  intro hneg hpos
  obtain ⟨ell, hell, hfamily⟩ := hpos
  obtain ⟨m, hm, _, hRfamily⟩ := hfamily 1
  obtain ⟨R, _, hcapped⟩ := hRfamily 0
  obtain ⟨k, Lu, S, Lam, U, α₀, hk, hT, hS, _, hne, hproper,
    hα, _, hclass, _⟩ := hcapped 1 zero_lt_one
  rcases hneg ell m R k hell hm hk Lu hT S hS α₀ hα U hclass with hempty | hfull
  · obtain ⟨x, hx⟩ := hne
    rw [hempty] at hx
    exact hx
  · exact hproper hfull

#check ProperFourAt
#check ProperCornerAt
#check GoalPos1
#check GoalNeg1
#check GoalPos2
#check GoalNeg2
#check goalNeg1_implies_not_goalPos1
#check goalNeg2_implies_not_goalPos2

#print axioms TouchBond
#print axioms CoversPlaqFour
#print axioms plaqCorner
#print axioms CoversPlaqCorner
#print axioms CurlReadsTouch
#print axioms PerCubeRegularTouch
#print axioms ClassCoupledFour
#print axioms ClassCoupledCorner
#print axioms ProperFourAt
#print axioms ProperCornerAt
#print axioms GoalPos1
#print axioms GoalNeg1
#print axioms GoalPos2
#print axioms GoalNeg2
#print axioms goalNeg1_implies_not_goalPos1
#print axioms goalNeg2_implies_not_goalPos2

end AdalyFormal.AHP.Round2.S2Nonvacuity

/-!
# Round 7 / S-2 odd: every blocking factor, not an existential ell

Everything above is the complete round-two pin, copied verbatim, including
its historical comments and its four old goals. Those comments describe the
pin's original status, not the subsequently proved round-two results.

Goal1 is the new primary target. Its leading universal quantifier cannot be
discharged by the old ell = 2 witness. Goal2 is a stronger pointwise target
on the same unchanged ProperFourAt predicate. Both include every odd ell >= 3,
in particular every odd ell > 11. Neither changes factor 12 or the test space.
-/

namespace AdalyFormal.AHP.Round7.S2Odd

open AdalyFormal.AHP.Round2.S2Nonvacuity

/-- Primary target: every ell >= 2 has cofinal proper four-bond instances.
The exponent is chosen before the radius bound, and the radius before the cap. -/
def Goal1 : Prop :=
  ∀ ell : ℕ, 2 ≤ ell →
    ∀ mLower : ℕ, ∃ m : ℕ, 1 ≤ m ∧ mLower ≤ m ∧
      ∀ RLower : ℕ, ∃ R : ℕ, RLower ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ → ProperFourAt ell m R a₀

/-- Stronger constructive target: every exponent m >= 1 and every R >= 18
works, for every ell >= 2 and every positive cap. -/
def Goal2 : Prop :=
  ∀ ell : ℕ, 2 ≤ ell →
    ∀ m : ℕ, 1 ≤ m →
      ∀ R : ℕ, 18 ≤ R →
        ∀ a₀ : ℝ, 0 < a₀ → ProperFourAt ell m R a₀

#check Goal1
#check Goal2
#check ProperFourAt
#check ClassCoupledFour
#check AdalyFormal.StatementLane.TorusOK
#check AdalyFormal.StatementLane.Admissible
#check AdalyFormal.StatementLaneG.LambdaOK2
#check AdalyFormal.StatementLane.OnLambdaTildeIn
#check AdalyFormal.StatementLane2.OnLambdaT
#print axioms Goal1
#print axioms Goal2

end AdalyFormal.AHP.Round7.S2Odd

/-! The following four helper proofs are copied verbatim from the round-two
positive attempt. Only the every-ell assembly below is new. -/
namespace AdalyFormal.AHP.Round2.S2Nonvacuity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-! ## Four-bond coverage on slabs

The frozen slab depends only on coordinate zero. In each ordered plaquette,
the second direction is nonzero. Its two parallel edges therefore have both
endpoints in the slab whenever either endpoint is in it. This reduces the
four-touch antecedent exactly to frozen inside-plaquette coverage.
-/

open AdalyFormal.D1Literal
open AdalyFormal.NonVac

/-- A transverse-invariant domain cannot contain only diagonal square corners. -/
theorem four_touch_cubeBond_of_transverse
    {sites : Set (PeriodicLatticeSite L)}
    (htrans : ∀ (x : PeriodicLatticeSite L) (ν : Fin 3), ν ≠ 0 →
      (periodicLatticeShift x ν ∈ sites ↔ x ∈ sites))
    {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e := by
  have hν : p.2.1.2 ≠ 0 := by
    intro h
    have hlt := p.2.2
    rw [h] at hlt
    exact not_lt_zero hlt
  have hAC := ht (p.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
  have hBD := ht (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
    (by simp [periodicPlaquetteBoundaryEdges])
  have hA : p.1 ∈ sites := by
    rcases hAC with h | h
    · exact h
    · exact (htrans _ _ hν).mp h
  have hB : periodicLatticeShift p.1 p.2.1.1 ∈ sites := by
    rcases hBD with h | h
    · exact h
    · exact (htrans _ _ hν).mp h
  have hC := (htrans p.1 _ hν).mpr hA
  have hD := (htrans (periodicLatticeShift p.1 p.2.1.1) _ hν).mpr hB
  have hD' : periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1 ∈ sites := by
    rw [AdalyFormal.StatementLaneR8.shift_comm p.1 (ne_of_gt p.2.2)]
    exact hD
  intro e he
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨hA, hB⟩
  · exact ⟨hB, hD⟩
  · exact ⟨hC, hD'⟩
  · exact ⟨hA, hC⟩

theorem slabNv_transverse (ell M R : ℕ)
    (x : PeriodicLatticeSite (scaleUp ell 2 (nvLu M R)))
    (ν : Fin 3) (hν : ν ≠ 0) :
    periodicLatticeShift x ν ∈ (SlabNv ell M R).Om 0 ↔
      x ∈ (SlabNv ell M R).Om 0 := by
  change periodicLatticeShift x ν ∈ (slab3 _ _ _ _ _ _ _).Om 0 ↔
    x ∈ (slab3 _ _ _ _ _ _ _).Om 0
  rw [om0_mem, om0_mem, AdalyFormal.StatementLaneR8.shift_ne x hν.symm]

theorem slabNv_coversFour {ell M R c : ℕ}
    (hcov : CoversOm0p ell M c 2 (SlabNv ell M R)) :
    CoversPlaqFour ell M c 2 (SlabNv ell M R) := by
  intro p hp
  have hinside := four_touch_cubeBond_of_transverse (slabNv_transverse ell M R) hp
  obtain ⟨sites, j, hc, he⟩ := hcov.2 p hinside
  exact ⟨sites, j, hc, fun e h => Or.inl (he e h).1⟩

/-- The zero matrix field satisfies every touching read guard, strictly.
Proof adapted from Fidelity.S1.classCoupledShell_one; no shell is substituted. -/
theorem perCubeRegularTouch_one
    {ell M c k : ℕ} (S : Tower L)
    {α₀ η : ℝ} (hell : 0 < ell) (hM : 0 < M) (hc : 0 < c)
    (hα : 0 < α₀) (hη : 0 < η) :
    PerCubeRegularTouch ell M c k S α₀ η (fun _ => 1) := by
  intro sites j hq
  have hpos : ∀ n : ℕ, 0 < (c : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · simp [periodicGaugeTransform]
    · simpa [frobNorm_zero'] using hpos 1
  · intro μ ν x _ _
    simpa [frobNorm_zero'] using hpos 2
  · intro μ x _
    have h0 : ddA η (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
      unfold ddA curlA
      simp
    rw [h0, frobNorm_zero']
    exact hpos 3


#print axioms four_touch_cubeBond_of_transverse
#print axioms slabNv_transverse
#print axioms slabNv_coversFour
#print axioms perCubeRegularTouch_one

end AdalyFormal.AHP.Round2.S2Nonvacuity

namespace AdalyFormal.AHP.Round7.S2Odd

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.AHP.Round2.S2Nonvacuity

/-- General-ell version of round two's properFourAt_two.
The construction still uses k = 2, U = 1, the same slab and Lambda, and the
same free-bond seed. There is no evenness assumption on ell or M. -/
theorem properFourAt_every_ell (ell m R : ℕ) (hell : 2 ≤ ell)
    (hm : 1 ≤ m) (hR : 18 ≤ R) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ProperFourAt ell m R a₀ := by
  let M := ell ^ m
  have hell0 : 0 < ell := by omega
  have hM : 0 < M := pow_pos hell0 m
  have hdvd : ell ∣ M := dvd_pow_self ell (by omega)
  have G := slabGeo_inst (ell := ell) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := ell) hell hM hR
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R :=
    fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible ell M R 2 (SlabNv ell M R) := slab3_admissible G hN
  have hcov : CoversOm0p ell M 12 2 (SlabNv ell M R) :=
    slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt (ell := ell) hell hdvd hM hR
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hell' : (0 : ℝ) < ell := by exact_mod_cast hell0
  have hα : 0 < a₀ / (12 * (M : ℝ)) := by positivity
  refine ⟨2, nvLu M R, SlabNv ell M R, LamN M R, (fun _ => 1),
    a₀ / (12 * (M : ℝ)), by norm_num, torusOK_nv hell hdvd hM,
    hAdm, lambdaOK2_nv hell hdvd hM (by omega), ⟨x, hbd.1⟩, ?_, hα, ?_, ?_, ?_⟩
  · intro heq
    exact hbd.hx' (heq ▸ Set.mem_univ _)
  · exact le_of_eq (mul_div_cancel₀ a₀ (by positivity : (12 : ℝ) * M ≠ 0))
  · exact ⟨hcov.1, slabNv_coversFour hcov,
      perCubeRegularTouch_one _ hell0 hM (by norm_num) hα (by positivity)⟩
  · obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) (ell := ell) hell hdvd hM
    exact ⟨BseedNv (R := R) ell hM, hB1, hB2, hB4, hB3⟩

/-- The stronger all-scales target, not a conditional construction. -/
theorem goal2_proved : Goal2 := by
  intro ell hell m hm R hR a₀ ha₀
  exact properFourAt_every_ell ell m R hell hm hR a₀ ha₀

/-- The constructive bound yields the requested cofinal quantifier order. -/
theorem goal1_of_goal2 (h : Goal2) : Goal1 := by
  intro ell hell mLower
  refine ⟨max 1 mLower, le_max_left _ _, le_max_right _ _, fun RLower => ?_⟩
  refine ⟨max RLower 18, le_max_left _ _, fun a₀ ha₀ => ?_⟩
  exact h ell hell _ (le_max_left _ _) _ (le_max_right _ _) a₀ ha₀

/-- The exact every-ell cofinal pin. -/
theorem goal1_proved : Goal1 := goal1_of_goal2 goal2_proved

/-- The new universal pin implies the old existential-ell positive pin. -/
theorem goal1_implies_round2 (h : Goal1) : GoalPos1 :=
  ⟨2, le_rfl, h 2 le_rfl⟩

/-- Explicit restriction to the later odd-L > 11 convention. -/
theorem odd_gt_eleven_cofinal (ell : ℕ) (_hodd : Odd ell) (hell : 11 < ell) :
    ∀ mLower : ℕ, ∃ m : ℕ, 1 ≤ m ∧ mLower ≤ m ∧
      ∀ RLower : ℕ, ∃ R : ℕ, RLower ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ → ProperFourAt ell m R a₀ :=
  goal1_proved ell (by omega)

#check properFourAt_every_ell
#check goal1_proved
#check goal2_proved
#check goal1_implies_round2
#check odd_gt_eleven_cofinal
#print axioms properFourAt_every_ell
#print axioms goal2_proved
#print axioms goal1_of_goal2
#print axioms goal1_proved
#print axioms goal1_implies_round2
#print axioms odd_gt_eleven_cofinal

/-! These imported results are general-ell; the assembly never calls the
old specialized properFourAt_two or any counterexample/coercivity theorem. -/
#print axioms slabGeo_inst
#print axioms nv_widths
#print axioms scaleUp_nv
#print axioms slab3_admissible
#print axioms slab3_coversp
#print axioms SlabNv_bdpt
#print axioms torusOK_nv
#print axioms lambdaOK2_nv
#print axioms BseedNv_props

end AdalyFormal.AHP.Round7.S2Odd

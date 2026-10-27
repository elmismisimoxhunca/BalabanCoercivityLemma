import GdR6b
import CvOX1
import DLR26
import GdGen6
import D2Lit
import AdalyFormal.Balaban.CoercUMainRegular
import RI6
import GN1
import GdR5b

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

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg)
open AdalyFormal.DLayer (Sp)
variable {L : PeriodicLatticeExtent}

/-- Exact incidence: every bond occurs in four plaquette-edge positions. -/
theorem sum_dir_pair (w : Fin 3 → ℝ) :
    ∑ d : PeriodicPlaquetteDirections, (w d.1.1 + w d.1.2) = 2 * ∑ μ, w μ := by
  have hd : (Finset.univ : Finset PeriodicPlaquetteDirections) =
      {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by decide
  rw [hd]
  simp [Fin.sum_univ_three]
  <;> ring

 theorem pbs_sum_eq (A : BondFnL2 L) :
    ∑ p : PeriodicLatticePlaquette L, plaqBondSq (WithLp.ofLp A) p = 4 * ‖A‖ ^ 2 := by
  rw [Fintype.sum_prod_type_right]
  have hdir : ∀ d : PeriodicPlaquetteDirections,
      ∑ x : PeriodicLatticeSite L, plaqBondSq (WithLp.ofLp A) (x, d) =
        2 * ((∑ x, ‖A (x, d.1.1)‖ ^ 2) + ∑ x, ‖A (x, d.1.2)‖ ^ 2) := by
    intro d
    unfold plaqBondSq
    simp only [Finset.sum_add_distrib]
    rw [AdalyFormal.DLayer.sum_shift_site d.1.1 (fun x => ‖A (x, d.1.2)‖ ^ 2),
      AdalyFormal.DLayer.sum_shift_site d.1.2 (fun x => ‖A (x, d.1.1)‖ ^ 2)]
    ring
  simp_rw [hdir]
  rw [← Finset.mul_sum, sum_dir_pair (fun μ => ∑ x, ‖A (x, μ)‖ ^ 2),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type_right]
  ring

/-- All SU(2) holonomies satisfy the frozen curvature bound with parameter 1/2. -/
theorem universal_plaqDef (U : Cfg L) : AdalyFormal.NonflatHunit.PlaqDef (1 / 2) U := by
  intro p
  have h := AdalyFormal.Balaban.CoercUMainRegular.frobNorm_su_sub_one_le
    (AdalyFormal.Balaban.DeltaPrime.holonomyElem U p)
  convert h using 1 <;> ring

 theorem Sp_quad_uniform (U : Cfg L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |Sp U p A A| ≤ 34 * plaqBondSq A p := by
  have h := AdalyFormal.DLayer.bilPlaq_quad_le U (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (universal_plaqDef U) A p
  unfold Sp
  rw [show (1 / 4 : ℝ) * (AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq U p A A +
      AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq U p A A) =
      (1 / 2) * AdalyFormal.Balaban.DeltaPrimeOperator.bilPlaq U p A A by ring,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- The frozen DL1 sum identity, without its unused section hypotheses. -/
theorem dp_eq_sum (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc U P x y
      = ∑ p : PeriodicLatticePlaquette L, (open Classical in if p ∈ P then Sp U p (WithLp.ofLp x) (WithLp.ofLp y) else 0) := by
  classical
  show deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y) = _
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · unfold Sp; ring
  · ring

/-- A volume-, scale-, configuration- and selector-independent curvature bound. -/
theorem dp_quad_uniform (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A : BondFnL2 L) :
    |deltaPrimeBilL2NormLoc U P A A| ≤ 136 * ‖A‖ ^ 2 := by
  classical
  rw [dp_eq_sum]
  calc |∑ p : PeriodicLatticePlaquette L, if p ∈ P then Sp U p (WithLp.ofLp A) (WithLp.ofLp A) else 0|
      ≤ ∑ p : PeriodicLatticePlaquette L, |if p ∈ P then Sp U p (WithLp.ofLp A) (WithLp.ofLp A) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : PeriodicLatticePlaquette L, 34 * plaqBondSq (WithLp.ofLp A) p := by
      apply Finset.sum_le_sum
      intro p _
      split_ifs
      · exact Sp_quad_uniform U _ p
      · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 34) (plaqBondSq_nonneg (WithLp.ofLp A) p)
    _ = 136 * ‖A‖ ^ 2 := by rw [← Finset.mul_sum, pbs_sum_eq]; ring

/-- Bare Delta cannot have arbitrarily negative normalized directions. This is
not a bound for the W-sandwiched carrier or the final mass-subtracted form. -/
theorem delta_lower_uniform (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A : BondFnL2 L) :
    -(136 : ℝ) * ‖A‖ ^ 2 ≤ ⟪A, deltaKLocCLM U P A⟫ := by
  rw [inner_deltaKLocCLM]
  have h := (abs_le.mp (dp_quad_uniform U P A)).1
  rw [real_inner_self_eq_norm_sq]
  have hpos := sq_nonneg ‖plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)‖
  linarith

/-- The quadratic form is the sum of its actual selected plaquette terms. -/
theorem delta_eq_sum (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U P A⟫ = ∑ p : PeriodicLatticePlaquette L,
      (open Classical in if p ∈ P then
        ‖(AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A) p‖ ^ 2 + Sp U p (WithLp.ofLp A) (WithLp.ofLp A) else 0) := by
  classical
  rw [inner_deltaKLocCLM, real_inner_self_eq_norm_sq, PiLp.norm_sq_eq_of_L2, dp_eq_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  change ‖(if p ∈ P then (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A) p else 0)‖ ^ 2 +
      (if p ∈ P then Sp U p (WithLp.ofLp A) (WithLp.ofLp A) else 0) = _
  split_ifs <;> simp

/-- Enlarging the selector adds precisely the difference-set quadratic form. -/
theorem delta_subset_split (U : Cfg L) {P Q : Set (PeriodicLatticePlaquette L)}
    (hQP : Q ⊆ P) (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U P A⟫ = ⟪A, deltaKLocCLM U Q A⟫ + ⟪A, deltaKLocCLM U (P \ Q) A⟫ := by
  classical
  simp only [delta_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hq : p ∈ Q
  · simp [hq, hQP hq]
  · by_cases hp : p ∈ P <;> simp [hp, hq]

/-- A uniform lower bound on the extra selected plaquettes, without assumptions on U. -/
theorem delta_extra_lower (U : Cfg L) {P Q : Set (PeriodicLatticePlaquette L)}
    (hQP : Q ⊆ P) (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U Q A⟫ - 136 * ‖A‖ ^ 2 ≤ ⟪A, deltaKLocCLM U P A⟫ := by
  rw [delta_subset_split U hQP]
  have h := delta_lower_uniform U (P \ Q) A
  linarith

open Classical in
/-- The actual weighted mass controls all level-zero rows, for any background. -/
theorem mass_level0_lower (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 ≤ a) (A : BondFnL2 L) :
    a * (∑ b : {b : Bond L // b ∈ bondsLam G 0}, ‖A b.1‖ ^ 2) ≤
      ⟪A, MassFull G a (bondSectorOf G U) A⟫ := by
  classical
  rw [inner_MassFull, Fintype.sum_sigma]
  have h := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : Fin (G.k + 1) => ∑ b : {b : Bond L // b ∈ bondsLam G j},
      a * (G.ell : ℝ) ^ (j : ℕ) * ‖(bondSectorOf G U).Qfull A ⟨j, b⟩‖ ^ 2)
    (fun j _ => Finset.sum_nonneg (fun b _ => by positivity))
    (Finset.mem_univ (0 : Fin (G.k + 1)))
  convert h using 1 <;> try rfl
  simp only [bondSectorOf, QfullOf, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp, Fin.val_zero, pow_zero, inv_one, one_smul,
    mul_one, QlinB_zero, Finset.mul_sum]
  apply Finset.sum_congr (by ext b; simp)
  intro b _
  rfl

/-- On fields supported on level-zero rows the weighted mass dominates aI.
No identity-mass assertion is made for arbitrary fine fields. -/
theorem mass_on_level0_support (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 ≤ a) (A : BondFnL2 L)
    (hA : ∀ b : Bond L, b ∉ bondsLam G 0 → A b = 0) :
    a * ‖A‖ ^ 2 ≤ ⟪A, MassFull G a (bondSectorOf G U) A⟫ := by
  classical
  have hs : (∑ b : {b : Bond L // b ∈ bondsLam G 0}, ‖A b.1‖ ^ 2) = ‖A‖ ^ 2 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun b => b ∈ bondsLam G 0))
      (p := fun b => b ∈ bondsLam G 0) (by simp) (fun b => ‖A b‖ ^ 2), Finset.sum_filter,
      PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : b ∈ bondsLam G 0
    · simp [hb]
    · simp [hb, hA b hb]
  simpa [hs] using mass_level0_lower G U ha A

/-- Compression and W are retained exactly; this is not a global aI bound. -/
theorem carrier_lower (sD sJ : PlaqSel) (P : IngrBParams) (A : ↥(bondSupp P.G)) :
    -(136 : ℝ) * ‖Wop P.G P.U P.a (iE P.G A)‖ ^ 2 +
      ‖(dataS sD sJ P).T A‖ ^ 2 + ⟪A, (dataS sD sJ P).Mass A⟫ ≤
      ⟪A, (dataS sD sJ P).Ginv A⟫ := by
  rw [BaseDataS.inner_Ginv]
  have hd : ⟪A, (dataS sD sJ P).Dpi A⟫ =
      ⟪Wop P.G P.U P.a (iE P.G A), DeltaS sD P.G P.U (Wop P.G P.U P.a (iE P.G A))⟫ := by
    change ⟪A, pE P.G ((DpiFullS sD P.G P.U P.a) (iE P.G A))⟫ = _
    rw [pE_inner_right]
    simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [hd]
  have h := delta_lower_uniform P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G A))
  dsimp only [DeltaS]
  linarith

/-- A genuine carrier bound on any W-fixed, level-zero-supported field. -/
theorem carrier_on_level0_support (sD sJ : PlaqSel) (P : IngrBParams) (ha : 0 ≤ P.a)
    (A : ↥(bondSupp P.G)) (hW : Wop P.G P.U P.a (iE P.G A) = iE P.G A)
    (hA : ∀ b : Bond P.Lf, b ∉ bondsLam P.G 0 → (iE P.G A) b = 0) :
    (P.a - 136) * ‖A‖ ^ 2 ≤ ⟪A, (dataS sD sJ P).Ginv A⟫ := by
  have h := carrier_lower sD sJ P A
  rw [hW] at h
  have hnorm : ‖iE P.G A‖ = ‖A‖ := rfl
  rw [hnorm] at h
  have hm := mass_on_level0_support P.G P.U ha (iE P.G A) hA
  have he : ⟪A, (dataS sD sJ P).Mass A⟫ = ⟪iE P.G A, MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G A)⟫ := by
    exact pE_inner_right P.G A _
  rw [hnorm, ← he] at hm
  nlinarith [sq_nonneg ‖(dataS sD sJ P).T A‖]

/-- The empty selector is the zero operator. -/
theorem delta_empty (U : Cfg L) : deltaKLocCLM U ∅ = 0 := by
  apply ContinuousLinearMap.ext
  intro X
  apply ext_inner_left ℝ
  intro Y
  rw [inner_deltaKLocCLM]
  simp [plaqMask, deltaPrimeBilL2NormLoc, deltaPrimeBilNormLoc, deltaPrimeBilRawLoc_apply]
  rfl

/-- Quadratic locality for two fields agreeing on all selected boundary edges. -/
theorem delta_form_congr (U : Cfg L) (P : Set (PeriodicLatticePlaquette L)) (X Y : BondFnL2 L)
    (hXY : ∀ p ∈ P, ∀ e ∈ periodicPlaquetteBoundaryEdges p, X e = Y e) :
    ⟪X, deltaKLocCLM U P X⟫ = ⟪Y, deltaKLocCLM U P Y⟫ := by
  have he := AdalyFormal.D1Guarded.deltaK_set_congr (U := U) P ∅ (X - Y) (by
    intro p hp e he
    have hpP : p ∈ P := by simpa using hp
    change X e - Y e = 0
    rw [hXY p hpP e he, sub_self])
  rw [delta_empty, ContinuousLinearMap.zero_apply, map_sub, sub_eq_zero] at he
  calc ⟪X, deltaKLocCLM U P X⟫ = ⟪X, deltaKLocCLM U P Y⟫ := by rw [he]
    _ = ⟪deltaKLocCLM U P X, Y⟫ := (deltaKLocCLM_symm U P X Y).symm
    _ = ⟪deltaKLocCLM U P Y, Y⟫ := by rw [he]
    _ = ⟪Y, deltaKLocCLM U P Y⟫ := real_inner_comm _ _

open AdalyFormal.StatementLane
open AdalyFormal.D1Guarded

/-- W is exactly the identity on every edge of every added boundary plaquette. -/
theorem Wop_on_notIn {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R * M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L} (hp : p ∉ plaqIn (S.Om 0))
    (e : Bond L) (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  obtain ⟨n1, n2⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  have hfz : ∀ c : PeriodicLatticeSite L, c ∉ S.Om 1 →
      (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U A))) c = 0 := by
    intro c hc
    by_cases hc0 : c ∈ S.Om 0
    · refine Gp_Rproj_lam0 (geomOf ell k S) U a _ (x := c) ?_
      refine ⟨fun μ => by simp, hc0, ?_⟩
      simpa using hc
    · exact Gp_Rproj_out (geomOf ell k S) U a _ (x := c) hc0
  change A e - (gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U A)))) e = A e
  rw [gradL2_apply]
  unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
  rw [hfz _ n1, hfz _ n2]
  simp

/-- On an added boundary plaquette, an E0 field equals its level-zero mask. -/
theorem level0_mask_on_notIn {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (h4 : 4 ≤ R * M)
    (A : ↥(bondSupp (geomOf ell k S))) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) (e : Bond L) (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (iE (geomOf ell k S) A) e =
      (bondMask (bondsLam (geomOf ell k S) 0) (iE (geomOf ell k S) A)) e := by
  classical
  rw [bondMask_apply]
  split_ifs with h0
  · rfl
  · by_cases hb : e ∈ bondsOm0 (geomOf ell k S)
    · obtain ⟨n1, n2⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
      rcases endpoint_om1 hell hS e hb h0 with hn | hn
      · exact (n1 hn).elim
      · exact (n2 hn).elim
    · exact A.2 e hb

open Classical in
/-- The norm of the actual level-zero mask is the unweighted level-zero mass sum. -/
theorem level0_mask_norm (G : TowerGeom L) (A : BondFnL2 L) :
    ‖bondMask (bondsLam G 0) A‖ ^ 2 = ∑ b : {b : Bond L // b ∈ bondsLam G 0}, ‖A b.1‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun b => b ∈ bondsLam G 0))
    (p := fun b => b ∈ bondsLam G 0) (by simp) (fun b => ‖A b‖ ^ 2), Finset.sum_filter,
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b ∈ bondsLam G 0 <;> simp [bondMask_apply, hb]

/-- The extra W-sandwiched quadratic form is controlled by precisely the
level-zero rows, not by the full fine norm or the norm of W. -/
theorem extra_Dpi_lower {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (h4 : 4 ≤ R * M)
    (U : Cfg L) (a : ℝ) (A : ↥(bondSupp (geomOf ell k S)))
    (P : Set (PeriodicLatticePlaquette L)) :
    -(136 : ℝ) * ‖bondMask (bondsLam (geomOf ell k S) 0) (iE (geomOf ell k S) A)‖ ^ 2 ≤
      ⟪Wop (geomOf ell k S) U a (iE (geomOf ell k S) A),
        deltaKLocCLM U (P \ plaqIn (S.Om 0)) (Wop (geomOf ell k S) U a (iE (geomOf ell k S) A))⟫ := by
  rw [delta_form_congr U (P \ plaqIn (S.Om 0)) _
    (bondMask (bondsLam (geomOf ell k S) 0) (iE (geomOf ell k S) A)) (by
      intro p hp e he
      rw [Wop_on_notIn hS h4 U a _ hp.2 e he]
      exact level0_mask_on_notIn hS hell h4 A hp.2 e he)]
  exact delta_lower_uniform U _ _

/-- For a >= 272, half of the ACTUAL weighted mass pays for every additional
plaquette. This is unconditional in the background, but is not final-form coercivity. -/
theorem extra_plaquettes_absorbed {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (h4 : 4 ≤ R * M)
    (U : Cfg L) {a : ℝ} (ha : 272 ≤ a) (A : ↥(bondSupp (geomOf ell k S)))
    (P : Set (PeriodicLatticePlaquette L)) :
    0 ≤ ⟪Wop (geomOf ell k S) U a (iE (geomOf ell k S) A),
        deltaKLocCLM U (P \ plaqIn (S.Om 0)) (Wop (geomOf ell k S) U a (iE (geomOf ell k S) A))⟫ +
      (1 / 2 : ℝ) * ⟪iE (geomOf ell k S) A,
        MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) (iE (geomOf ell k S) A)⟫ := by
  have hd := extra_Dpi_lower hS hell h4 U a A P
  have hm := mass_level0_lower (geomOf ell k S) U (by linarith : 0 ≤ a) (iE (geomOf ell k S) A)
  rw [← level0_mask_norm] at hm
  have hn := sq_nonneg ‖bondMask (bondsLam (geomOf ell k S) 0) (iE (geomOf ell k S) A)‖
  nlinarith

#print axioms delta_empty
#print axioms delta_form_congr
#print axioms Wop_on_notIn
#print axioms level0_mask_on_notIn
#print axioms level0_mask_norm
#print axioms extra_Dpi_lower
#print axioms extra_plaquettes_absorbed
#print axioms delta_eq_sum
#print axioms delta_subset_split
#print axioms delta_extra_lower
#print axioms mass_level0_lower
#print axioms mass_on_level0_support
#print axioms carrier_lower
#print axioms carrier_on_level0_support
#print axioms sum_dir_pair
#print axioms pbs_sum_eq
#print axioms universal_plaqDef
#print axioms Sp_quad_uniform
#print axioms dp_eq_sum
#print axioms dp_quad_uniform
#print axioms delta_lower_uniform
end Round11.LargeA

/-! Class inclusion: proof copied from fidelity/s2-inclusion; the class
definitions above are the unchanged pin, not redeclared variants. -/
namespace Round11.LargeA
open Round3.S1Proper
variable {L : PeriodicLatticeExtent}
theorem CubeBond.toTouch {sites : Set (PeriodicLatticeSite L)} {b : Bond L}
    (h : CubeBond sites b) : TouchBond sites b :=
  Or.inl h.1

theorem TouchBond.endpoints {sites : Set (PeriodicLatticeSite L)}
    {x : PeriodicLatticeSite L} {μ : Fin 3} (h : TouchBond sites (x, μ)) :
    x ∈ sites ∨ periodicLatticeShift x μ ∈ sites := by
  unfold TouchBond at h
  exact h

/-! ## Unit-square corners. A `siteBox` (`ZStatementP428.lean:122`) that
touch-covers the square contains it. Boundary carriers:
`ClayStatement.lean:1295`. Off-axis shifts: `ZR8Class.lean:52`, `:87`. -/

def cornerA (p : PeriodicLatticePlaquette L) : PeriodicLatticeSite L := p.1

def cornerB (p : PeriodicLatticePlaquette L) : PeriodicLatticeSite L :=
  periodicLatticeShift p.1 p.2.1.1

def cornerC (p : PeriodicLatticePlaquette L) : PeriodicLatticeSite L :=
  periodicLatticeShift p.1 p.2.1.2

def cornerD (p : PeriodicLatticePlaquette L) : PeriodicLatticeSite L :=
  periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2

theorem coord_shift_ne {x : PeriodicLatticeSite L} {ν κ : Fin 3} (h : κ ≠ ν) :
    ((periodicLatticeShift x ν) κ).val = (x κ).val :=
  congrArg Fin.val (AdalyFormal.StatementLaneR8.shift_ne x h)

theorem cornerD_comm (p : PeriodicLatticePlaquette L) :
    periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1 = cornerD p :=
  AdalyFormal.StatementLaneR8.shift_comm p.1 (μ := p.2.1.2) (ν := p.2.1.1) (ne_of_gt p.2.2)

theorem mem_siteBox_iff {z : PeriodicLatticeSite L} {s : ℕ} {x : PeriodicLatticeSite L} :
    x ∈ siteBox z s ↔
      ∀ μ : Fin 3, ((x μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < s := by
  rfl

/-- Membership pattern already used by the compiled `plaq_of_corners`
(`ZR8Class.lean:119`): `simp only` on the boundary finset, then `rcases`. -/
theorem boundary_is_square {p : PeriodicLatticePlaquette L} {e : Bond L}
    (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (e.1 = cornerA p ∧ periodicLatticeShift e.1 e.2 = cornerB p) ∨
    (e.1 = cornerB p ∧ periodicLatticeShift e.1 e.2 = cornerD p) ∨
    (e.1 = cornerC p ∧ periodicLatticeShift e.1 e.2 = cornerD p) ∨
    (e.1 = cornerA p ∧ periodicLatticeShift e.1 e.2 = cornerC p) := by
  simp only [periodicPlaquetteBoundaryEdges,
    Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, cornerD_comm p⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem edgeAB_mem (p : PeriodicLatticePlaquette L) :
    ((cornerA p, p.2.1.1) : Bond L) ∈ periodicPlaquetteBoundaryEdges p := by
  simp [periodicPlaquetteBoundaryEdges, cornerA]

theorem edgeBD_mem (p : PeriodicLatticePlaquette L) :
    ((cornerB p, p.2.1.2) : Bond L) ∈ periodicPlaquetteBoundaryEdges p := by
  simp [periodicPlaquetteBoundaryEdges, cornerB]

theorem edgeCD_mem (p : PeriodicLatticePlaquette L) :
    ((cornerC p, p.2.1.1) : Bond L) ∈ periodicPlaquetteBoundaryEdges p := by
  simp [periodicPlaquetteBoundaryEdges, cornerC]

theorem edgeAC_mem (p : PeriodicLatticePlaquette L) :
    ((cornerA p, p.2.1.2) : Bond L) ∈ periodicPlaquetteBoundaryEdges p := by
  simp [periodicPlaquetteBoundaryEdges, cornerA]

theorem square_edges_touch {sites : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    (cornerA p ∈ sites ∨ cornerB p ∈ sites) ∧
    (cornerB p ∈ sites ∨ cornerD p ∈ sites) ∧
    (cornerC p ∈ sites ∨ cornerD p ∈ sites) ∧
    (cornerA p ∈ sites ∨ cornerC p ∈ sites) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TouchBond.endpoints (ht _ (edgeAB_mem p))
  · exact TouchBond.endpoints (ht _ (edgeBD_mem p))
  · rcases TouchBond.endpoints (ht _ (edgeCD_mem p)) with hC | hD
    · exact Or.inl hC
    · exact Or.inr (cornerD_comm p ▸ hD)
  · exact TouchBond.endpoints (ht _ (edgeAC_mem p))

/-- Diagonal `A,D` in a product box forces `B` and `C`. Coordinate arcs, including
arcs that wrap; no parity hypothesis. -/
theorem siteBox_fill_of_diagonal {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (hA : cornerA p ∈ siteBox z s) (hD : cornerD p ∈ siteBox z s) :
    cornerB p ∈ siteBox z s ∧ cornerC p ∈ siteBox z s := by
  let d1 : Fin 3 := p.2.1.1
  let d2 : Fin 3 := p.2.1.2
  have h12 : d1 ≠ d2 := ne_of_lt p.2.2
  have h21 : d2 ≠ d1 := h12.symm
  rw [mem_siteBox_iff] at hA hD
  refine ⟨?_, ?_⟩
  · rw [mem_siteBox_iff]
    intro ρ
    by_cases hρ : ρ = d1
    · subst hρ
      have hval : ((cornerD p) d1).val = ((cornerB p) d1).val :=
        coord_shift_ne (x := cornerB p) (ν := d2) (κ := d1) h12
      rw [← hval]
      exact hD d1
    · have hval : ((cornerB p) ρ).val = ((cornerA p) ρ).val :=
        coord_shift_ne (x := cornerA p) (ν := d1) (κ := ρ) hρ
      rw [hval]
      exact hA ρ
  · rw [mem_siteBox_iff]
    intro ρ
    by_cases hρ : ρ = d2
    · subst hρ
      have hval : ((cornerD p) d2).val = ((cornerC p) d2).val := by
        have hCD : cornerD p = periodicLatticeShift (cornerC p) d1 := (cornerD_comm p).symm
        rw [hCD]
        exact coord_shift_ne (x := cornerC p) (ν := d1) (κ := d2) h21
      rw [← hval]
      exact hD d2
    · have hval : ((cornerC p) ρ).val = ((cornerA p) ρ).val :=
        coord_shift_ne (x := cornerA p) (ν := d2) (κ := ρ) hρ
      rw [hval]
      exact hA ρ

theorem siteBox_fill_of_antidiagonal {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (hB : cornerB p ∈ siteBox z s) (hC : cornerC p ∈ siteBox z s) :
    cornerA p ∈ siteBox z s ∧ cornerD p ∈ siteBox z s := by
  let d1 : Fin 3 := p.2.1.1
  let d2 : Fin 3 := p.2.1.2
  have h12 : d1 ≠ d2 := ne_of_lt p.2.2
  have h21 : d2 ≠ d1 := h12.symm
  rw [mem_siteBox_iff] at hB hC
  refine ⟨?_, ?_⟩
  · rw [mem_siteBox_iff]
    intro ρ
    by_cases h1 : ρ = d1
    · subst h1
      have hval : ((cornerC p) d1).val = ((cornerA p) d1).val :=
        coord_shift_ne (x := cornerA p) (ν := d2) (κ := d1) h12
      rw [← hval]
      exact hC d1
    · by_cases h2 : ρ = d2
      · subst h2
        have hval : ((cornerB p) d2).val = ((cornerA p) d2).val :=
          coord_shift_ne (x := cornerA p) (ν := d1) (κ := d2) h21
        rw [← hval]
        exact hB d2
      · have hval : ((cornerB p) ρ).val = ((cornerA p) ρ).val :=
          coord_shift_ne (x := cornerA p) (ν := d1) (κ := ρ) h1
        rw [← hval]
        exact hB ρ
  · rw [mem_siteBox_iff]
    intro ρ
    by_cases h1 : ρ = d1
    · subst h1
      have hval : ((cornerD p) d1).val = ((cornerB p) d1).val :=
        coord_shift_ne (x := cornerB p) (ν := d2) (κ := d1) h12
      rw [hval]
      exact hB d1
    · by_cases h2 : ρ = d2
      · subst h2
        have hval : ((cornerD p) d2).val = ((cornerC p) d2).val := by
          have hCD : cornerD p = periodicLatticeShift (cornerC p) d1 := (cornerD_comm p).symm
          rw [hCD]
          exact coord_shift_ne (x := cornerC p) (ν := d1) (κ := d2) h21
        rw [hval]
        exact hC d2
      · have hval : ((cornerD p) ρ).val = ((cornerB p) ρ).val :=
          coord_shift_ne (x := cornerB p) (ν := d2) (κ := ρ) h2
        rw [hval]
        exact hB ρ

/-- A vertex cover of the 4-cycle contains an opposite pair. `Classical.em`, not
`push_neg`: the negation of a conjunction is not destructured as an `Or`. -/
theorem opposite_of_touch {sites : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    (cornerA p ∈ sites ∧ cornerD p ∈ sites) ∨ (cornerB p ∈ sites ∧ cornerC p ∈ sites) := by
  obtain ⟨hAB, hBD, hCD, hAC⟩ := square_edges_touch ht
  rcases Classical.em (cornerA p ∈ sites) with hA | hA
  · rcases Classical.em (cornerD p ∈ sites) with hD | hD
    · exact Or.inl ⟨hA, hD⟩
    · exact Or.inr ⟨Or.resolve_right hBD hD, Or.resolve_right hCD hD⟩
  · exact Or.inr ⟨Or.resolve_left hAB hA, Or.resolve_left hAC hA⟩

theorem touchCover_all_corners {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z s) e) :
    cornerA p ∈ siteBox z s ∧ cornerB p ∈ siteBox z s ∧
      cornerC p ∈ siteBox z s ∧ cornerD p ∈ siteBox z s := by
  rcases opposite_of_touch (sites := siteBox z s) ht with ⟨hA, hD⟩ | ⟨hB, hC⟩
  · obtain ⟨hB, hC⟩ := siteBox_fill_of_diagonal hA hD
    exact ⟨hA, hB, hC, hD⟩
  · obtain ⟨hA, hD⟩ := siteBox_fill_of_antidiagonal hB hC
    exact ⟨hA, hB, hC, hD⟩

/-- Touch-covering the four bonds of `p` by a `siteBox` gives `CubeBond` on each.
`CubeBond` is unfolded before the two endpoint goals are rewritten separately. -/
theorem touchCover_cubeBond {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z s) e)
    {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    CubeBond (siteBox z s) e := by
  have hall := touchCover_all_corners ht
  unfold CubeBond
  rcases boundary_is_square he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨?_, ?_⟩
    · rw [h1]; exact hall.1
    · rw [h2]; exact hall.2.1
  · refine ⟨?_, ?_⟩
    · rw [h1]; exact hall.2.1
    · rw [h2]; exact hall.2.2.2
  · refine ⟨?_, ?_⟩
    · rw [h1]; exact hall.2.2.1
    · rw [h2]; exact hall.2.2.2
  · refine ⟨?_, ?_⟩
    · rw [h1]; exact hall.1
    · rw [h2]; exact hall.2.2.1


theorem touchAnte_of_cubeAnte {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond S e) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond S e :=
  fun e he => CubeBond.toTouch (hp e he)

/-- `CoversPlaqFour → CoversPlaqOm0c`. The witness cube is a `siteBox`
(`DescribedAt`, `ZStatementP428.lean:131`, field `hc.1.2.1`). The equality
`sites = siteBox` is transported by `▸`, not substituted to `rfl` under `hc`. -/
theorem CoversPlaqFour.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqFour ell M c k S) : CoversPlaqOm0c ell M c k S := by
  intro p hp
  obtain ⟨sites, j, hc, ht⟩ := h p (touchAnte_of_cubeAnte hp)
  obtain ⟨z, _, hsites⟩ := hc.1.2.1
  have hcBox : IsClassCube ell M c k S (siteBox z (c * bigSide M ell j)) j :=
    hsites ▸ hc
  have htBox :
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z (c * bigSide M ell j)) e :=
    fun e he => hsites ▸ ht e he
  refine ⟨siteBox z (c * bigSide M ell j), j, hcBox, ?_⟩
  intro e he
  exact touchCover_cubeBond htBox he


theorem CurlReads.toTouch {sites : Set (PeriodicLatticeSite L)}
    {x : PeriodicLatticeSite L} {a b : Fin 3}
    (h : CurlReads sites x a b) : CurlReadsTouch sites x a b :=
  ⟨CubeBond.toTouch h.1, CubeBond.toTouch h.2.1,
    CubeBond.toTouch h.2.2.1, CubeBond.toTouch h.2.2.2⟩


theorem PerCubeRegularTouch.toFrozen {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegularTouch ell M f k S α₀ η U) : PerCubeRegular2 ell M f k S α₀ η U := by
  intro sites j hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  refine ⟨g, A, ?_, ?_, ?_⟩
  · intro e he
    exact hA e (CubeBond.toTouch he)
  · intro μ ν x h1 h2
    exact hD μ ν x (CubeBond.toTouch h1) (CubeBond.toTouch h2)
  · intro μ x hreads
    exact hLap μ x (fun ν hν =>
      ⟨CurlReads.toTouch (hreads ν hν).1, CurlReads.toTouch (hreads ν hν).2⟩)


theorem ClassCoupledFour.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledFour ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  ⟨⟨h.1, CoversPlaqFour.toFrozen h.2.1⟩, PerCubeRegularTouch.toFrozen h.2.2⟩


#print axioms CubeBond.toTouch
#print axioms TouchBond.endpoints
#print axioms cornerA
#print axioms cornerB
#print axioms cornerC
#print axioms cornerD
#print axioms coord_shift_ne
#print axioms cornerD_comm
#print axioms mem_siteBox_iff
#print axioms boundary_is_square
#print axioms edgeAB_mem
#print axioms edgeBD_mem
#print axioms edgeCD_mem
#print axioms edgeAC_mem
#print axioms square_edges_touch
#print axioms siteBox_fill_of_diagonal
#print axioms siteBox_fill_of_antidiagonal
#print axioms opposite_of_touch
#print axioms touchCover_all_corners
#print axioms touchCover_cubeBond
#print axioms touchAnte_of_cubeAnte
#print axioms CoversPlaqFour.toFrozen
#print axioms CurlReads.toTouch
#print axioms PerCubeRegularTouch.toFrozen
#print axioms ClassCoupledFour.toFrozen
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open Round3.S1Proper Round7.S1Odd
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The corner selector contains the localized selector on every geometry. -/
theorem in_subset_corner (L : PeriodicLatticeExtent) (G : TowerGeom L) :
    plaqIn G.Om0 ⊆ selCorner L G := by
  intro p hp
  exact Or.inl (hp (p.1, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])).1

/-- Dpi's quadratic form, with the exact W and carrier inclusion. -/
theorem dataS_Dpi_form (sD sJ : PlaqSel) (P : IngrBParams) (A : ↥(bondSupp P.G)) :
    ⟪A, (dataS sD sJ P).Dpi A⟫ =
      ⟪Wop P.G P.U P.a (iE P.G A), DeltaS sD P.G P.U (Wop P.G P.U P.a (iE P.G A))⟫ := by
  change ⟪A, pE P.G ((DpiFullS sD P.G P.U P.a) (iE P.G A))⟫ = _
  rw [pE_inner_right]
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- For a >= 272 the actual corner carrier dominates the localized Dpi + T*T
plus HALF of the actual mass, for arbitrary background. The W in both sides
is the same W(a), not W(a/2). This distinction is deliberately retained. -/
theorem corner_carrier_half_mass (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h4 : 4 ≤ R * M)
    (ha : 272 ≤ P.a) (A : ↥(bondSupp P.G)) :
    ⟪A, (dataS selIn selIn P).Dpi A⟫ + ‖(dataS selIn selIn P).T A‖ ^ 2 +
      (1 / 2 : ℝ) * ⟪A, (dataS selIn selIn P).Mass A⟫ ≤
      ⟪A, (dataS selCorner selCorner P).Ginv A⟫ := by
  have hb := extra_plaquettes_absorbed hS hell h4 P.U ha A (selCorner _ P.G)
  have he : ⟪A, (dataS selIn selIn P).Mass A⟫ =
      ⟪iE P.G A, MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G A)⟫ :=
    pE_inner_right P.G A _
  have hs := delta_subset_split P.U (in_subset_corner P.Lf P.G)
    (Wop P.G P.U P.a (iE P.G A))
  rw [BaseDataS.inner_Ginv, dataS_Dpi_form, dataS_Dpi_form]
  change ⟪Wop P.G P.U P.a (iE P.G A), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (plaqIn P.G.Om0)
      (Wop P.G P.U P.a (iE P.G A))⟫ + ‖(dataS selIn selIn P).T A‖ ^ 2 +
      (1 / 2 : ℝ) * ⟪A, (dataS selIn selIn P).Mass A⟫ ≤
    ⟪Wop P.G P.U P.a (iE P.G A), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selCorner _ P.G)
      (Wop P.G P.U P.a (iE P.G A))⟫ + ‖(dataS selIn selIn P).T A‖ ^ 2 +
      ⟪A, (dataS selIn selIn P).Mass A⟫
  rw [hs, he]
  have hb' : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G A),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selCorner P.Lf P.G \ plaqIn P.G.Om0)
        (Wop P.G P.U P.a (iE P.G A))⟫ +
      (1 / 2 : ℝ) * ⟪iE P.G A, MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G A)⟫ := hb
  linarith only [hb']

/-- What the frozen p428 proof and class inclusion give for the actual changed
operators: the complete slice WITH all three inverse guards. This is not
P428TouchFourAt and does not close GoalLargeA. -/
theorem guarded_touch_slice (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
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
          WellDefAt selCorner selCorner (gparams ell k Lu (by omega) S U a Lam) →
          InstIneqS selCorner selCorner ell k (by omega) a Lu γ₀ S Lam U := by
  obtain ⟨m₀, hm₀, hm⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₁, hR⟩ := hm m hmm
  refine ⟨max R₁ (17 * ell), fun R hRR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ₀, hcore⟩ := hR R ((le_max_left _ _).trans hRR)
  refine ⟨hside, a₀, ha₀, γ₀, hγ₀, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hLam U hU hWD
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hroom : 17 * ell ≤ R * ell ^ m :=
    ((le_max_right R₁ (17 * ell)).trans hRR).trans (Nat.le_mul_of_pos_right R hM)
  have hloc : InstIneqS selIn selIn ell k (by omega) a Lu γ₀ S Lam U :=
    hcore k hk Lu α₀ hα hsmall hT S hS Lam hLam U (ClassCoupledFour.toFrozen hU)
  exact InstIneqSG2_general selCorner selCorner (by omega) hS hk hroom ha.le hγ₀ Lam U
    in_subset_corner in_subset_corner hloc hWD

#print axioms in_subset_corner
#print axioms dataS_Dpi_form
#print axioms corner_carrier_half_mass
#print axioms guarded_touch_slice
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open Round3.S1Proper
variable {L : PeriodicLatticeExtent}

/-- Conditional only on the two genuine site units, W is independent of mass. -/
theorem Wop_mass_independent (G : TowerGeom L) (U : Cfg L) (a b : ℝ)
    (ha : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hb : IsUnit (DelpA G U b + (1 - siteMask G.Om0))) :
    Wop G U a = Wop G U b := by
  apply ContinuousLinearMap.ext
  intro A
  obtain ⟨v, hv, he, -⟩ := Rproj_minimiser G U (gradAdj U A)
  have hga : Gp G U a (Rproj G U (gradAdj U A)) = v := by
    rw [he]
    exact AdalyFormal.SliceCoerc.Gp_lapDir_of_NQp G U a ha v hv
  have hgb : Gp G U b (Rproj G U (gradAdj U A)) = v := by
    rw [he]
    exact AdalyFormal.SliceCoerc.Gp_lapDir_of_NQp G U b hb v hv
  change A - gradL2 U (Gp G U a (Rproj G U (gradAdj U A))) =
    A - gradL2 U (Gp G U b (Rproj G U (gradAdj U A)))
  rw [hga, hgb]

/-- Halving a halves the actual weighted mass exactly. -/
theorem MassFull_half_form (G : TowerGeom L) (U : Cfg L) (a : ℝ) (A : BondFnL2 L) :
    ⟪A, MassFull G (a / 2) (bondSectorOf G U) A⟫ =
      (1 / 2 : ℝ) * ⟪A, MassFull G a (bondSectorOf G U) A⟫ := by
  rw [inner_MassFull, inner_MassFull, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The previous half-mass bound really is a comparison with the frozen
localized carrier at a/2, once both site inverses exist. -/
theorem corner_ge_local_half (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h4 : 4 ≤ R * M)
    (ha : 272 ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (huh : IsUnit (DelpA P.G P.U (P.a / 2) + (1 - siteMask P.G.Om0)))
    (A : ↥(bondSupp P.G)) :
    ⟪A, (dataS selIn selIn {P with a := P.a / 2}).Ginv A⟫ ≤
      ⟪A, (dataS selCorner selCorner P).Ginv A⟫ := by
  have h := corner_carrier_half_mass P hS hell h4 ha A
  have hW := Wop_mass_independent P.G P.U P.a (P.a / 2) hu huh
  have hd : ⟪A, (dataS selIn selIn {P with a := P.a / 2}).Dpi A⟫ =
      ⟪A, (dataS selIn selIn P).Dpi A⟫ := by
    rw [dataS_Dpi_form selIn selIn {P with a := P.a / 2} A,
      dataS_Dpi_form selIn selIn P A]
    change ⟪Wop P.G P.U (P.a / 2) (iE P.G A), DeltaS selIn P.G P.U (Wop P.G P.U (P.a / 2) (iE P.G A))⟫ = _
    rw [← hW]
  have hm : ⟪A, (dataS selIn selIn {P with a := P.a / 2}).Mass A⟫ =
      (1 / 2 : ℝ) * ⟪A, (dataS selIn selIn P).Mass A⟫ := by
    change ⟪A, pE P.G (MassFull P.G (P.a / 2) (bondSectorOf P.G P.U) (iE P.G A))⟫ =
      (1 / 2 : ℝ) * ⟪A, pE P.G (MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G A))⟫
    rw [pE_inner_right, pE_inner_right, MassFull_half_form]
  rw [BaseDataS.inner_Ginv, hd, hm]
  exact h

/-- A proved base-carrier unit reduction. The localized PSD and site units
remain explicit premises; no corrected-inverse conclusion is smuggled in. -/
theorem corner_base_unit_of_local_half (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h4 : 4 ≤ R * M)
    (ha : 272 ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (huh : IsUnit (DelpA P.G P.U (P.a / 2) + (1 - siteMask P.G.Om0)))
    (hpsd : AdalyFormal.D1Literal.PSD (dataS selIn selIn {P with a := P.a / 2}).Ginv)
    (hunit : IsUnit (dataS selIn selIn {P with a := P.a / 2}).Ginv) :
    IsUnit (dataS selCorner selCorner P).Ginv := by
  exact isUnit_of_psd_ge
    ((dataS selIn selIn {P with a := P.a / 2}).Ginv_symm (dataS_laws selIn selIn _)) hpsd hunit
    (corner_ge_local_half P hS hell h4 ha hu huh)

#print axioms Wop_mass_independent
#print axioms MassFull_half_form
#print axioms corner_ge_local_half
#print axioms corner_base_unit_of_local_half
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper

section abstract
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Schur units transfer if the two carriers agree merely on ker Q. -/
theorem unit_transfer_ker {M₁ M₂ : E →L[ℝ] E} {Q : E →L[ℝ] F} {Qs : F →L[ℝ] E}
    (hM₁ : IsUnit M₁) (hM₂ : IsUnit M₂)
    (hN₂ : IsUnit ((Q.comp (Ring.inverse M₂)).comp Qs))
    (hM : ∀ x, Q x = 0 → M₁ x = M₂ x) :
    IsUnit ((Q.comp (Ring.inverse M₁)).comp Qs) := by
  exact unit_transfer (LinearMap.ker Q.toLinearMap) (⊥ : Submodule ℝ F)
    hM₁ hM₂ hN₂ (fun x hx => hx) (fun x hx => hM x hx)

/-- Adding Q* K Q changes the Lagrange multiplier, not the constrained lift.
Only agreement up to this shift on V is needed for data f in Z. -/
theorem H_shift_on {D₁ D₂ : BaseDataS E S F} (V : Submodule ℝ E) (Z : Submodule ℝ F)
    (K : F →L[ℝ] F) (hQ : D₁.Q = D₂.Q) (hQs : D₁.Qs = D₂.Qs)
    (hV : ∀ x, D₁.Q x ∈ Z → x ∈ V)
    (hM : ∀ x ∈ V, D₁.Ginv x = D₂.Ginv x + D₂.Qs (K (D₂.Q x)))
    (u₁ : IsUnit D₁.Ginv) (u₂ : IsUnit D₂.Ginv)
    (n₁ : IsUnit ((D₁.Q.comp D₁.G).comp D₁.Qs))
    (n₂ : IsUnit ((D₂.Q.comp D₂.G).comp D₂.Qs)) {f : F} (hf : f ∈ Z) :
    D₁.H f = D₂.H f := by
  let N₁ := (D₁.Q.comp D₁.G).comp D₁.Qs
  let N₂ := (D₂.Q.comp D₂.G).comp D₂.Qs
  let z := Ring.inverse N₁ f
  let x := D₁.H f
  have hQx : D₁.Q x = f := Q_H_apply D₁ n₁ f
  have hxV : x ∈ V := hV x (hQx ▸ hf)
  have hM₁x : D₁.Ginv x = D₁.Qs z :=
    congrArg (fun A : E →L[ℝ] E => A (D₁.Qs z)) (Ring.mul_inverse_cancel _ u₁)
  have hM₂x : D₂.Ginv x = D₂.Qs (z - K f) := by
    have hm := hM x hxV
    rw [hM₁x, hQs, ← hQ, hQx] at hm
    rw [map_sub]
    exact eq_sub_of_add_eq hm.symm
  have hx₂ : x = D₂.G (D₂.Qs (z - K f)) := by
    have h := congrArg (fun A : E →L[ℝ] E => A x) (Ring.inverse_mul_cancel D₂.Ginv u₂)
    change D₂.G (D₂.Ginv x) = x at h
    rw [hM₂x] at h
    exact h.symm
  have hN₂z : N₂ (z - K f) = f := by
    change D₂.Q (D₂.G (D₂.Qs (z - K f))) = f
    rw [← hx₂, ← hQ, hQx]
  have hz₂ : z - K f = Ring.inverse N₂ f := by
    have h := congrArg (fun A : F →L[ℝ] F => A (z - K f)) (Ring.inverse_mul_cancel N₂ n₂)
    change Ring.inverse N₂ (N₂ (z - K f)) = z - K f at h
    rw [hN₂z] at h
    exact h.symm
  rw [hz₂] at hx₂
  exact hx₂

/-- The source correction is invariant under a mass shift, if C2 and the
source are unchanged and the genuine base/Schur inverses exist. -/
theorem Delta2_shift {D₁ D₂ : BaseDataS E S F} (K : F →L[ℝ] F)
    (hQ : D₁.Q = D₂.Q) (hQs : D₁.Qs = D₂.Qs)
    (hC : D₁.C2 = D₂.C2) (hJ : D₁.J = D₂.J)
    (hM : ∀ x, D₁.Ginv x = D₂.Ginv x + D₂.Qs (K (D₂.Q x)))
    (hL₁ : D₁.Laws) (hL₂ : D₂.Laws)
    (u₁ : IsUnit D₁.Ginv) (u₂ : IsUnit D₂.Ginv)
    (n₁ : IsUnit ((D₁.Q.comp D₁.G).comp D₁.Qs))
    (n₂ : IsUnit ((D₂.Q.comp D₂.G).comp D₂.Qs)) :
    D₁.Delta2 hL₁ = D₂.Delta2 hL₂ := by
  obtain ⟨hs₁, hf₁⟩ := D₁.Delta2_spec hL₁
  obtain ⟨hs₂, hf₂⟩ := D₂.Delta2_spec hL₂
  apply symm_unique hs₁ hs₂
  intro x
  rw [hf₁, hf₂, hJ, ← hC]
  congr 2
  exact H_shift_on ⊤ ⊤ K hQ hQs (fun _ _ => trivial) (fun y _ => hM y)
    u₁ u₂ n₁ n₂ (show D₁.C2 x ∈ (⊤ : Submodule ℝ F) from trivial)

#print axioms unit_transfer_ker
#print axioms H_shift_on
#print axioms Delta2_shift
end abstract

/-- The actual mass on E0 is Q* diag(a ell^j) Q, as an operator identity. -/
theorem dataS_Mass_factor (sD sJ : PlaqSel) (P : IngrBParams) :
    (dataS sD sJ P).Mass =
      (dataS sD sJ P).Qs.comp ((diagW P.G (massW P.G P.a)).comp (dataS sD sJ P).Q) := by
  change (pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G)) =
    (ContinuousLinearMap.adjoint (P.sector.Qfull.comp (iE P.G))).comp
      ((diagW P.G (massW P.G P.a)).comp (P.sector.Qfull.comp (iE P.G)))
  simp only [MassFull, pE, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

/-- The diagonal weights are exactly linear in mass. -/
theorem diagW_mass_split (P : IngrBParams) (b : ℝ) :
    diagW P.G (massW P.G P.a) =
      diagW P.G (massW P.G b) + diagW P.G (massW P.G (P.a - b)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro p
  change (P.a * _) • x p = (b * _) • x p + ((P.a - b) * _) • x p
  rw [← add_smul]
  congr 1
  ring

/-- Concrete mass-shift identity; the W equality is proved from site units. -/
theorem local_carrier_mass_shift (P : IngrBParams) (b : ℝ)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hb : IsUnit (DelpA P.G P.U b + (1 - siteMask P.G.Om0)))
    (x : ↥(bondSupp P.G)) :
    (dataS selIn selIn P).Ginv x =
      (dataS selIn selIn {P with a := b}).Ginv x +
      (dataS selIn selIn P).Qs (diagW P.G (massW P.G (P.a - b)) ((dataS selIn selIn P).Q x)) := by
  have hW := Wop_mass_independent P.G P.U P.a b hu hb
  have hd : (dataS selIn selIn P).Dpi = (dataS selIn selIn {P with a := b}).Dpi := by
    change (pE P.G).comp ((DpiFullS selIn P.G P.U P.a).comp (iE P.G)) =
      (pE P.G).comp ((DpiFullS selIn P.G P.U b).comp (iE P.G))
    simp only [DpiFullS, hW]
  simp only [BaseDataS.Ginv, ContinuousLinearMap.add_apply, hd, dataS_Mass_factor,
    ContinuousLinearMap.comp_apply]
  rw [diagW_mass_split P b]
  simp only [ContinuousLinearMap.add_apply, map_add]
  exact (add_assoc _ _ _).symm

#print axioms dataS_Mass_factor
#print axioms diagW_mass_split
#print axioms local_carrier_mass_shift
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
section abstract
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A noncircular corrected-guard transfer. Equal source corrections cancel
in both form comparison and the restriction to ker Q. -/
theorem corrected_guards_transfer (D₁ D₂ : BaseDataS E S F)
    (hL₁ : D₁.Laws) (hL₂ : D₂.Laws) (G₁ G₂ : E →L[ℝ] E)
    (hg₁ : D₁.IsG1inv G₁) (hg₂ : D₂.IsG1inv G₂)
    (hQ : D₁.Q = D₂.Q) (hQs : D₁.Qs = D₂.Qs)
    (hd : D₁.Delta2 hL₁ = D₂.Delta2 hL₂)
    (hle : ∀ x, ⟪x, D₂.Ginv x⟫ ≤ ⟪x, D₁.Ginv x⟫)
    (hker : ∀ x, D₁.Q x = 0 → D₁.Ginv x = D₂.Ginv x)
    (hp : PSD G₂) (ug₂ : IsUnit G₂)
    (ng₂ : IsUnit ((D₂.Q.comp (D₂.G1 G₂)).comp D₂.Qs)) :
    IsUnit G₁ ∧ IsUnit ((D₁.Q.comp (D₁.G1 G₁)).comp D₁.Qs) := by
  have e₁ : G₁ = D₁.Ginv - D₁.Delta2 hL₁ := D₁.G1inv_unique hg₁ (D₁.isG1inv_sub hL₁)
  have e₂ : G₂ = D₂.Ginv - D₂.Delta2 hL₂ := D₂.G1inv_unique hg₂ (D₂.isG1inv_sub hL₂)
  have ug₁ : IsUnit G₁ := by
    apply isUnit_of_psd_ge hg₂.symm hp ug₂
    intro x
    rw [e₁, e₂, hd]
    simp only [sub_apply, inner_sub_right]
    exact sub_le_sub_right (hle x) _
  refine ⟨ug₁, ?_⟩
  change IsUnit ((D₁.Q.comp (Ring.inverse G₁)).comp D₁.Qs)
  change IsUnit ((D₂.Q.comp (Ring.inverse G₂)).comp D₂.Qs) at ng₂
  rw [hQ, hQs]
  apply unit_transfer_ker ug₁ ug₂ ng₂
  intro x hx
  have h0 : D₁.Q x = 0 := by rw [hQ]; exact hx
  rw [e₁, e₂, hd]
  simp only [sub_apply, hker x h0]

#print axioms corrected_guards_transfer
end abstract
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper

/-- Selector transfer for the base Schur inverse, with no corrected guard. -/
theorem corner_schur_of_local (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M)
    (uc : IsUnit (dataS selCorner selCorner P).Ginv)
    (ua : IsUnit (dataS selIn selIn P).Ginv)
    (na : IsUnit (((dataS selIn selIn P).Q.comp (dataS selIn selIn P).G).comp
      (dataS selIn selIn P).Qs)) :
    IsUnit (((dataS selCorner selCorner P).Q.comp (dataS selCorner selCorner P).G).comp
      (dataS selCorner selCorner P).Qs) := by
  have T := twoData_lit_loc P hS hell hroom selCorner selCorner selIn selIn
    in_subset_corner (fun _ _ => subset_rfl) in_subset_corner (fun _ _ => subset_rfl)
  have nc : IsUnit (((dataS selIn selIn P).Q.comp
      (Ring.inverse (dataS selCorner selCorner P).Ginv)).comp (dataS selIn selIn P).Qs) := by
    apply unit_transfer (V0 P.G) (Z0 P.G) uc ua na
    · intro x hx
      exact T.hZV x (by rw [T.hQ]; exact hx)
    · exact T.hM
  change IsUnit (((dataS selCorner selCorner P).Q.comp
    (Ring.inverse (dataS selCorner selCorner P).Ginv)).comp (dataS selCorner selCorner P).Qs)
  rw [T.hQ, T.hQs]
  exact nc

/-- The source correction transfers with base guards alone. -/
theorem corner_correction_of_local (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M)
    (uc : IsUnit (dataS selCorner selCorner P).Ginv)
    (ua : IsUnit (dataS selIn selIn P).Ginv)
    (na : IsUnit (((dataS selIn selIn P).Q.comp (dataS selIn selIn P).G).comp
      (dataS selIn selIn P).Qs)) :
    (dataS selCorner selCorner P).Delta2 (dataS_laws selCorner selCorner P) =
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) := by
  have T := twoData_lit_loc P hS hell hroom selCorner selCorner selIn selIn
    in_subset_corner (fun _ _ => subset_rfl) in_subset_corner (fun _ _ => subset_rfl)
  exact T.Delta2_eq (dataS_laws selCorner selCorner P) (dataS_laws selIn selIn P)
    uc ua (corner_schur_of_local P hS hell hroom uc ua na) na

#print axioms corner_schur_of_local
#print axioms corner_correction_of_local
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper

/-- Selector and mass changes both vanish on the actual constraint kernel. -/
theorem corner_carrier_eq_local_on_ker (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (b : ℝ)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hb : IsUnit (DelpA P.G P.U b + (1 - siteMask P.G.Om0)))
    (x : ↥(bondSupp P.G)) (hx : (dataS selCorner selCorner P).Q x = 0) :
    (dataS selCorner selCorner P).Ginv x = (dataS selIn selIn {P with a := b}).Ginv x := by
  have T := twoData_lit_loc P hS hell hroom selCorner selCorner selIn selIn
    in_subset_corner (fun _ _ => subset_rfl) in_subset_corner (fun _ _ => subset_rfl)
  have hxV : x ∈ V0 P.G := T.hZV x (by rw [hx]; exact (Z0 P.G).zero_mem)
  have hxloc : (dataS selIn selIn P).Q x = 0 := by rw [← T.hQ]; exact hx
  rw [T.hM x hxV, local_carrier_mass_shift P b hu hb x, hxloc, map_zero, map_zero, add_zero]

#print axioms corner_carrier_eq_local_on_ker
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper

/-- Concrete application of the abstract corrected-guard comparison. -/
theorem corner_corrected_guards (P : IngrBParams)
    (hd : (dataS selCorner selCorner P).Delta2 (dataS_laws selCorner selCorner P) =
      (dataS selIn selIn {P with a := P.a / 2}).Delta2 (dataS_laws selIn selIn {P with a := P.a / 2}))
    (hle : ∀ x, ⟪x, (dataS selIn selIn {P with a := P.a / 2}).Ginv x⟫ ≤
      ⟪x, (dataS selCorner selCorner P).Ginv x⟫)
    (hk : ∀ x, (dataS selCorner selCorner P).Q x = 0 →
      (dataS selCorner selCorner P).Ginv x = (dataS selIn selIn {P with a := P.a / 2}).Ginv x)
    (hp : PSD (G1invS selIn selIn {P with a := P.a / 2}))
    (hWD : WellDefAt selIn selIn {P with a := P.a / 2}) :
    IsUnit (G1invS selCorner selCorner P) ∧ IsUnit (GenS.NmatS selCorner selCorner P) := by
  exact corrected_guards_transfer (dataS selCorner selCorner P)
    (dataS selIn selIn {P with a := P.a / 2})
    (dataS_laws selCorner selCorner P) (dataS_laws selIn selIn {P with a := P.a / 2})
    (G1invS selCorner selCorner P) (G1invS selIn selIn {P with a := P.a / 2})
    (G1invS_spec selCorner selCorner P) (G1invS_spec selIn selIn {P with a := P.a / 2})
    rfl rfl hd hle hk hp hWD.2.1 hWD.2.2

#print axioms corner_corrected_guards
end Round11.LargeA

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper

/-- Monotonicity of the genuine local base carrier, under its site units. -/
theorem local_mass_domination (P : IngrBParams) (b : ℝ) (hab : b ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hb : IsUnit (DelpA P.G P.U b + (1 - siteMask P.G.Om0)))
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn {P with a := b}).Ginv x⟫ ≤
      ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
  rw [local_carrier_mass_shift P b hu hb, inner_add_right,
    ← (dataS selIn selIn P).Q_adj, inner_diagW]
  have hn : 0 ≤ ∑ p : BIdx P.G, massW P.G (P.a - b) p *
      ‖(dataS selIn selIn P).Q x p‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro p _
    unfold massW
    have : 0 ≤ P.a - b := sub_nonneg.mpr hab
    positivity
  linarith only [hn]

/-- Raising mass preserves the base and base-Schur units and Delta2.
This does not assume any corrected unit at the larger mass. -/
theorem local_base_shift (P : IngrBParams) (b : ℝ) (hab : b ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (hb : IsUnit (DelpA P.G P.U b + (1 - siteMask P.G.Om0)))
    (hpsd : PSD (dataS selIn selIn {P with a := b}).Ginv)
    (ub : IsUnit (dataS selIn selIn {P with a := b}).Ginv)
    (nb : IsUnit (((dataS selIn selIn {P with a := b}).Q.comp
      (dataS selIn selIn {P with a := b}).G).comp (dataS selIn selIn {P with a := b}).Qs)) :
    IsUnit (dataS selIn selIn P).Ginv ∧
    IsUnit (((dataS selIn selIn P).Q.comp (dataS selIn selIn P).G).comp (dataS selIn selIn P).Qs) ∧
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn {P with a := b}).Delta2 (dataS_laws selIn selIn {P with a := b}) := by
  have ua : IsUnit (dataS selIn selIn P).Ginv := isUnit_of_psd_ge
    ((dataS selIn selIn {P with a := b}).Ginv_symm (dataS_laws selIn selIn _))
    hpsd ub (local_mass_domination P b hab hu hb)
  have na : IsUnit (((dataS selIn selIn P).Q.comp (dataS selIn selIn P).G).comp
      (dataS selIn selIn P).Qs) := by
    apply unit_transfer_ker (Q := (dataS selIn selIn P).Q) (Qs := (dataS selIn selIn P).Qs) ua ub nb
    intro x hx
    change (dataS selIn selIn P).Q x = 0 at hx
    rw [local_carrier_mass_shift P b hu hb x, hx, map_zero, map_zero, add_zero]
  refine ⟨ua, na, ?_⟩
  have hc : (dataS selIn selIn P).C2 = (dataS selIn selIn {P with a := b}).C2 := by
    funext x
    change P.sector.C2full (Wop P.G P.U P.a (iE P.G x)) =
      P.sector.C2full (Wop P.G P.U b (iE P.G x))
    rw [Wop_mass_independent P.G P.U P.a b hu hb]
  exact Delta2_shift (D₁ := dataS selIn selIn P) (D₂ := dataS selIn selIn {P with a := b})
    (diagW P.G (massW P.G (P.a - b))) rfl rfl hc rfl
    (local_carrier_mass_shift P b hu hb) (dataS_laws selIn selIn P)
    (dataS_laws selIn selIn {P with a := b}) ua ub na nb

/-- Base and base-Schur units suffice to identify the corner correction with
its localized half-mass counterpart. No corner corrected guard is assumed. -/
theorem corner_base_and_correction (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (ha : 272 ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (huh : IsUnit (DelpA P.G P.U (P.a / 2) + (1 - siteMask P.G.Om0)))
    (hpsd : PSD (dataS selIn selIn {P with a := P.a / 2}).Ginv)
    (hWD : WellDefAt selIn selIn {P with a := P.a / 2}) :
    IsUnit (dataS selCorner selCorner P).Ginv ∧
    IsUnit (((dataS selCorner selCorner P).Q.comp (dataS selCorner selCorner P).G).comp
      (dataS selCorner selCorner P).Qs) ∧
    (dataS selCorner selCorner P).Delta2 (dataS_laws selCorner selCorner P) =
      (dataS selIn selIn {P with a := P.a / 2}).Delta2
        (dataS_laws selIn selIn {P with a := P.a / 2}) := by
  have nh := NG_unit_of_N1 (dataS selIn selIn {P with a := P.a / 2})
    (dataS_laws selIn selIn {P with a := P.a / 2})
    (G1invS_spec selIn selIn {P with a := P.a / 2}) hWD.2.2
  obtain ⟨ua, na, hdelta⟩ := local_base_shift P (P.a / 2) (by linarith) hu huh hpsd hWD.1 nh
  have uc := corner_base_unit_of_local_half P hS hell (by omega) ha hu huh hpsd hWD.1
  exact ⟨uc, corner_schur_of_local P hS hell hroom uc ua na,
    (corner_correction_of_local P hS hell hroom uc ua na).trans hdelta⟩

/-- COMPLETE inverse-guard transport at a >= 272. All corner guards are
conclusions. The explicit premises concern only the frozen localized data
at HALF mass and the two site inverses. -/
theorem corner_wellDef_of_local_half (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (ha : 272 ≤ P.a)
    (hu : IsUnit (DelpA P.G P.U P.a + (1 - siteMask P.G.Om0)))
    (huh : IsUnit (DelpA P.G P.U (P.a / 2) + (1 - siteMask P.G.Om0)))
    (hpsd : PSD (dataS selIn selIn {P with a := P.a / 2}).Ginv)
    (h1psd : PSD (G1invS selIn selIn {P with a := P.a / 2}))
    (hWD : WellDefAt selIn selIn {P with a := P.a / 2}) :
    WellDefAt selCorner selCorner P := by
  have h4 : 4 ≤ R * M := by omega
  obtain ⟨uc, nc, hdelta⟩ := corner_base_and_correction P hS hell hroom ha hu huh hpsd hWD
  exact ⟨uc, corner_corrected_guards P hdelta
    (corner_ge_local_half P hS hell h4 ha hu huh)
    (corner_carrier_eq_local_on_ker P hS hell hroom (P.a / 2) hu huh) h1psd hWD⟩

#print axioms local_mass_domination
#print axioms local_base_shift
#print axioms corner_base_and_correction
#print axioms corner_wellDef_of_local_half
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

/-- On proper domains the two site inverses need no class hypothesis at all. -/
theorem corner_wellDef_proper (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 2 ≤ P.ell)
    (hroom : 17 * P.ell ≤ R * M) (ha : 272 ≤ P.a)
    (hout : ∃ x, x ∉ P.G.Om0)
    (hpsd : PSD (dataS selIn selIn {P with a := P.a / 2}).Ginv)
    (h1psd : PSD (G1invS selIn selIn {P with a := P.a / 2}))
    (hWD : WellDefAt selIn selIn {P with a := P.a / 2}) :
    WellDefAt selCorner selCorner P := by
  exact corner_wellDef_of_local_half P hS (by omega) hroom ha
    (AdalyFormal.CoverOmega.delpA_unit P.G P.U (by linarith) hell hout)
    (AdalyFormal.CoverOmega.delpA_unit P.G P.U (by linarith) hell hout)
    hpsd h1psd hWD

/-- If Om0 is the full torus, the changed and frozen data coincide literally. -/
theorem dataS_corner_eq_of_full (P : IngrBParams) (hfull : P.G.Om0 = Set.univ) :
    dataS selCorner selCorner P = dataS selIn selIn P := by
  have hs : selCorner P.Lf P.G = selIn P.Lf P.G := by
    ext p
    simp [selCorner, plaqCorner, selIn, plaqIn, hfull]
  unfold dataS DpiFullS DeltaS JfS
  rw [hs]

/-- Full-domain equality includes the corrected inverse and both source terms. -/
theorem genForm_corner_eq_of_full (P : IngrBParams) (hfull : P.G.Om0 = Set.univ)
    (B : AdalyFormal.Balaban.CovariantOperators.BondFnL2 P.Lu) :
    GenS.genFormS selCorner selCorner P B = GenS.genFormS selIn selIn P B := by
  have hd := dataS_corner_eq_of_full P hfull
  have hg : G1invS selCorner selCorner P = G1invS selIn selIn P := by
    apply (dataS selIn selIn P).G1inv_unique
    · rw [← hd]
      exact G1invS_spec selCorner selCorner P
    · exact G1invS_spec selIn selIn P
  have hs : selCorner P.Lf P.G = selIn P.Lf P.G := by
    ext p
    simp [selCorner, plaqCorner, selIn, plaqIn, hfull]
  simp only [GenS.genFormS, GenS.firstTermS, GenS.NmatS, H1inS, hd, hg]
  unfold JfS
  rw [hs]

/-- A failed localized half-mass guard forces the admissible competitor to
vanish, provided its frozen inequality has positive coercivity constant. -/
theorem test_zero_of_local_bad_guard {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu)) {b γ : ℝ} (hb : 0 ≤ b) (hγ : 0 < γ)
    (hloc : InstIneqS selIn selIn ell k hell b Lu γ S Lam U)
    (hbad : ¬ WellDefAt selIn selIn (gparams ell k Lu hell S U b Lam))
    (Bt : Bond Lu → AdalyFormal.Balaban.CovariantOperators.SuTwo)
    (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt) : Bt = 0 := by
  have h := hloc Bt h1 h2
  rw [genFormS_collapse_of_not_wd selIn selIn _ hbad] at h
  have hnorm : (0 : ℝ) ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U b Lam) Bt) :
      AdalyFormal.Balaban.CovariantOperators.BondFnL2 Lu),
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U b Lam) Bt) :
      AdalyFormal.Balaban.CovariantOperators.BondFnL2 Lu)⟫ := real_inner_self_nonneg
  change γ * bondEnergy Bt ≤ -b * _ at h
  have hE : bondEnergy Bt = 0 := by
    have hnon := bondEnergy_nonneg Bt
    nlinarith [mul_nonneg hb hnorm]
  exact bondEnergy_eq_zero hE

/-- Pointwise reduction with NO corner guards and NO site-unit assumptions.
Only positivity of the two genuine localized half-mass carriers remains,
and only in the proper-domain, well-defined-half-mass branch. -/
theorem touch_instance_of_half_positive {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (S : Tower (scaleUp ell k Lu))
    (hS : Admissible ell M R k S) (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    {a γ γh : ℝ} (ha : 272 ≤ a) (hγ : 0 < γ) (hγh : 0 < γh)
    (hloc : InstIneqS selIn selIn ell k (by omega) a Lu γ S Lam U)
    (hhalf : InstIneqS selIn selIn ell k (by omega) (a / 2) Lu γh S Lam U)
    (hp : (∃ x, x ∉ S.Om 0) →
      WellDefAt selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam) →
      PSD (dataS selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam)).Ginv ∧
      PSD (G1invS selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam))) :
    InstIneqS selCorner selCorner ell k (by omega) a Lu γ S Lam U := by
  classical
  by_cases hout : ∃ x, x ∉ S.Om 0
  · by_cases hWD : WellDefAt selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam)
    · obtain ⟨hpsd, h1psd⟩ := hp hout hWD
      have hc := corner_wellDef_proper (gparams ell k Lu (by omega) S U a Lam)
        hS hell hroom ha hout hpsd h1psd hWD
      exact InstIneqSG2_general selCorner selCorner (by omega) hS hk hroom
        (by linarith) hγ Lam U in_subset_corner in_subset_corner hloc hc
    · intro Bt h1 h2
      have hz := test_zero_of_local_bad_guard (by omega) S Lam U
        (by linarith : 0 ≤ a / 2) hγh hhalf hWD Bt h1 h2
      subst Bt
      have hE : bondEnergy (0 : Bond Lu → AdalyFormal.Balaban.CovariantOperators.SuTwo) = 0 := by
        unfold bondEnergy
        exact Finset.sum_eq_zero (fun _ _ => by simp)
      rw [hE, mul_zero]
      have hB : (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) 0) :
          AdalyFormal.Balaban.CovariantOperators.BondFnL2 Lu) = 0 := by
        rw [map_zero]; rfl
      rw [hB, genFormS_zero]
  · have hf : S.Om 0 = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact not_not.mp (fun hx => hout ⟨x, hx⟩)
    intro Bt h1 h2
    rw [genForm_corner_eq_of_full (gparams ell k Lu (by omega) S U a Lam) hf]
    exact hloc Bt h1 h2

#print axioms corner_wellDef_proper
#print axioms dataS_corner_eq_of_full
#print axioms genForm_corner_eq_of_full
#print axioms test_zero_of_local_bad_guard
#print axioms touch_instance_of_half_positive
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open Round3.S1Proper
open Round7.S1Odd

/-- The remaining analytic input. No site units or corner guards occur here.
The half-mass localized PSD conclusions are needed only on proper domains
where the half-mass localized data are well defined. All headline thresholds
are retained; this proposition is NOT proved in this file. -/
def EventualHalfPositive (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ mₚ : ℕ, ∀ m : ℕ, mₚ ≤ m → ∃ Rₚ : ℕ, ∀ R : ℕ, Rₚ ≤ R →
    ∃ s : ℝ, 0 < s ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ s → TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)),
          ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          (∃ x, x ∉ S.Om 0) →
          WellDefAt selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam) →
          PSD (dataS selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam)).Ginv ∧
          PSD (G1invS selIn selIn (gparams ell k Lu (by omega) S U (a / 2) Lam))

/-- The exact pinned slice follows from the remaining localized positivity
input. Uses both frozen headlines (a and a/2), intersecting their thresholds.
The conclusion is unguarded; the unproved hypothesis is stated explicitly. -/
theorem touch_slice_of_eventual_half_positive (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ)
    (ha : 272 ≤ a) (hpos : EventualHalfPositive ell hell a) :
    P428TouchFourAt ell hell a := by
  obtain ⟨mA, hmA, hA⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell a (by linarith)
  obtain ⟨mH, hmH, hH⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell (a / 2) (by linarith)
  obtain ⟨mP, hP⟩ := hpos
  refine ⟨max mA (max mH mP), by omega, fun m hm => ?_⟩
  obtain ⟨RA, hRA⟩ := hA m (by omega)
  obtain ⟨RH, hRH⟩ := hH m (by omega)
  obtain ⟨RP, hRP⟩ := hP m (by omega)
  refine ⟨max RA (max RH (max RP (17 * ell))), fun R hR => ?_⟩
  obtain ⟨hsA, sA, hsA0, γA, hγA, hcoreA⟩ := hRA R (by omega)
  obtain ⟨hsH, sH, hsH0, γH, hγH, hcoreH⟩ := hRH R (by omega)
  obtain ⟨sP, hsP0, hcoreP⟩ := hRP R (by omega)
  refine ⟨hsA, min sA (min sH sP), lt_min hsA0 (lt_min hsH0 hsP0), γA, hγA, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hLam U hU
  have hbA : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sA := hsmall.trans (min_le_left _ _)
  have hbH : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sH :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbP : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ sP :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hroom : 17 * ell ≤ R * ell ^ m :=
    (show 17 * ell ≤ R by omega).trans (Nat.le_mul_of_pos_right R hM)
  have hUloc := ClassCoupledFour.toFrozen hU
  exact touch_instance_of_half_positive hell S hS hk hroom Lam U ha hγA hγH
    (hcoreA k hk Lu α₀ hα hbA hT S hS Lam hLam U hUloc)
    (hcoreH k hk Lu α₀ hα hbH hT S hS Lam hLam U hUloc)
    (hcoreP k hk Lu α₀ hα hbP hT S hS Lam hLam U hU)

/-- A sufficient analytic route to the pinned large-mass target, not a proof
of that target: EventualHalfPositive remains an explicit hypothesis. -/
theorem goalLargeA_of_eventual_half_positive
    (hpos : ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 272 ≤ a → EventualHalfPositive ell hell a) :
    Round11.GoalLargeA := by
  refine ⟨272, ?_⟩
  intro ell hell a ha
  exact touch_slice_of_eventual_half_positive ell hell a ha (hpos ell hell a ha)

#print axioms EventualHalfPositive
#print axioms touch_slice_of_eventual_half_positive
#print axioms goalLargeA_of_eventual_half_positive
end Round11.LargeA

namespace Round11.LargeA
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open AdalyFormal.StatementLaneR6
open Round3.S1Proper

/-- Localized positivity for arbitrary exterior links, if all links based
in Om0 are 1. No units, class or smallness assumptions are used. -/
theorem local_base_psd_of_base_flat (P : IngrBParams) (ha : 0 ≤ P.a)
    (hbase : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1) :
    PSD (dataS selIn selIn P).Ginv := by
  intro w
  rw [BaseDataS.inner_Ginv]
  have hd : 0 ≤ ⟪w, (dataS selIn selIn P).Dpi w⟫ := by
    rw [dataS_Dpi_form]
    unfold DeltaS
    have he : deltaKLocCLM P.U (selIn _ P.G) =
        deltaKLocCLM AdalyFormal.Balaban.DeltaPrime.trivialU (selIn _ P.G) := by
      exact AdalyFormal.StatementLaneR6.deltaKLocCLM_congr
        (fun p hp e he => hbase e (hp e he).1)
    rw [he]
    exact deltaKLocCLM_flat_nonneg _ _
  have hm : 0 ≤ ⟪w, (dataS selIn selIn P).Mass w⟫ := by
    change 0 ≤ ⟪w, pE P.G (MassFull P.G P.a P.sector (iE P.G w))⟫
    rw [pE_inner_right, inner_MassFull]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [sq_nonneg ‖(dataS selIn selIn P).T w‖]

/-- In this entire exterior-link family the correction vanishes, so the
remaining analytic positivity obligation is discharged, not assumed. -/
theorem local_both_psd_of_base_flat (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell) (h3 : 3 ≤ R * M)
    (ha : 0 ≤ P.a) (hbase : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1) :
    PSD (dataS selIn selIn P).Ginv ∧ PSD (G1invS selIn selIn P) := by
  have hp := local_base_psd_of_base_flat P ha hbase
  refine ⟨hp, ?_⟩
  rw [G1invS_eq_Ginv_base selIn P selIn hS hell h3 hbase]
  exact hp

/-- An UNGUARDED large-mass slice for the complete base-point-flat family,
with arbitrary exterior and entering links and every original threshold.
The additional base-flat premise is essential to the proved statement;
this is not the unrestricted pinned P428TouchFourAt. -/
theorem base_flat_large_mass_slice (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 272 ≤ a) :
  ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    SidePow6 ell (ell ^ m) a ∧
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ → TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)),
          ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          (∀ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om 0 → U e = 1) →
          InstIneqS selCorner selCorner ell k (by omega) a Lu γ₀ S Lam U := by
  obtain ⟨mA, hmA, hA⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell a (by linarith)
  obtain ⟨mH, hmH, hH⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell (a / 2) (by linarith)
  refine ⟨max mA mH, by omega, fun m hm => ?_⟩
  obtain ⟨RA, hRA⟩ := hA m (by omega)
  obtain ⟨RH, hRH⟩ := hH m (by omega)
  refine ⟨max RA (max RH (17 * ell)), fun R hR => ?_⟩
  obtain ⟨hsA, sA, hsA0, γA, hγA, hcoreA⟩ := hRA R (by omega)
  obtain ⟨hsH, sH, hsH0, γH, hγH, hcoreH⟩ := hRH R (by omega)
  refine ⟨hsA, min sA sH, lt_min hsA0 hsH0, γA, hγA, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hLam U hU hbase
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hroom : 17 * ell ≤ R * ell ^ m :=
    (show 17 * ell ≤ R by omega).trans (Nat.le_mul_of_pos_right R hM)
  have hUloc := ClassCoupledFour.toFrozen hU
  apply touch_instance_of_half_positive hell S hS hk hroom Lam U ha hγA hγH
  · exact hcoreA k hk Lu α₀ hα (hsmall.trans (min_le_left _ _)) hT S hS Lam hLam U hUloc
  · exact hcoreH k hk Lu α₀ hα (hsmall.trans (min_le_right _ _)) hT S hS Lam hLam U hUloc
  · intro _ _
    exact local_both_psd_of_base_flat (gparams ell k Lu (by omega) S U (a / 2) Lam)
      hS (show 0 < ell by omega) (show 3 ≤ R * ell ^ m by omega)
      (show 0 ≤ a / 2 by linarith) hbase

#print axioms local_base_psd_of_base_flat
#print axioms local_both_psd_of_base_flat
#print axioms base_flat_large_mass_slice
end Round11.LargeA

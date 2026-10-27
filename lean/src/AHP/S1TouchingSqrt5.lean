import D1Final
import GdPlaq
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



end Round7.S1Odd

/-! Round 11: the exact all-positive-mass and eventual-large-mass targets. -/
namespace Round11
open Round7.S1Odd

def GoalAllA : Prop := ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ¬ P428TouchFourAt ell hell a

def GoalLargeA : Prop := ∃ a₁ : ℝ, ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), a₁ ≤ a → P428TouchFourAt ell hell a

end Round11

set_option maxHeartbeats 16000000

namespace Round3.S1Proper

variable {L : PeriodicLatticeExtent}

/-! ## Locality: corner and all selectors agree on touching-supported fields.
This is not equality with the frozen inside selector. -/

open scoped RealInnerProductSpace
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Guarded (bilPlaq_zero_left bilPlaq_zero_right curlValue_zero_of curlL2_apply)

theorem edge_not_touch_of_not_corner {Om : Set (PeriodicLatticeSite L)}
    {p : PeriodicLatticePlaquette L} (hp : p ∉ plaqCorner Om)
    {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) : ¬ TouchBond Om e := by
  have hA : p.1 ∉ Om := fun h => hp (Or.inl h)
  have hB : periodicLatticeShift p.1 p.2.1.1 ∉ Om := fun h => hp (Or.inr (Or.inl h))
  have hC : periodicLatticeShift p.1 p.2.1.2 ∉ Om := fun h => hp (Or.inr (Or.inr (Or.inl h)))
  have hD : periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∉ Om :=
    fun h => hp (Or.inr (Or.inr (Or.inr h)))
  have hD' : periodicLatticeShift (periodicLatticeShift p.1 p.2.1.2) p.2.1.1 ∉ Om := by
    rw [AdalyFormal.StatementLaneR8.shift_comm p.1 (ne_of_gt p.2.2)]
    exact hD
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_or.mpr ⟨hA, hB⟩
  · exact not_or.mpr ⟨hB, hD⟩
  · exact not_or.mpr ⟨hC, hD'⟩
  · exact not_or.mpr ⟨hA, hC⟩

/-- An omitted plaquette contributes zero if all its four field values vanish.
The equality is an operator application, not merely a quadratic pairing. -/
theorem deltaKLocCLM_eq_univ_of_zero_off (U : Cfg L)
    (P : Set (PeriodicLatticePlaquette L)) (X : BondFnL2 L)
    (hX : ∀ p, p ∉ P → ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp X) e = 0) :
    deltaKLocCLM U P X = deltaKLocCLM U Set.univ X := by
  classical
  have hraw (Y : Bond L → SuTwo) :
      deltaPrimeBilRawLoc U P Y (WithLp.ofLp X) = deltaPrimeBilRawLoc U Set.univ Y (WithLp.ofLp X) ∧
      deltaPrimeBilRawLoc U P (WithLp.ofLp X) Y = deltaPrimeBilRawLoc U Set.univ (WithLp.ofLp X) Y := by
    constructor
    · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [Set.mem_univ, if_true]
      by_cases hp : p ∈ P
      · rw [if_pos hp]
      · rw [if_neg hp, bilPlaq_zero_right Y (hX p hp)]
    · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [Set.mem_univ, if_true]
      by_cases hp : p ∈ P
      · rw [if_pos hp]
      · rw [if_neg hp, bilPlaq_zero_left (hX p hp)]
  refine ext_inner_left ℝ (fun Y => ?_)
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM]
  have hsecond : deltaPrimeBilL2NormLoc U P Y X = deltaPrimeBilL2NormLoc U Set.univ Y X := by
    change deltaPrimeBilNormLoc U P (WithLp.ofLp Y) (WithLp.ofLp X) =
      deltaPrimeBilNormLoc U Set.univ (WithLp.ofLp Y) (WithLp.ofLp X)
    unfold deltaPrimeBilNormLoc
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
    rw [(hraw (WithLp.ofLp Y)).1, (hraw (WithLp.ofLp Y)).2]
  rw [hsecond]
  congr 1
  simp only [plaqMask_univ, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [plaqMask_apply, plaqMask_apply]
  by_cases hp : p ∈ P
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, curlL2_apply U X,
      curlValue_zero_of (U := U) (hX p hp)]
    simp

/-- Touching support contains every nonzero field read by a corner square. -/
theorem deltaKLocCLM_corner_eq (G : TowerGeom L) (U : Cfg L) (X : BondFnL2 L)
    (hX : X ∈ bondSupp G) :
    deltaKLocCLM U (plaqCorner G.Om0) X = deltaKLocCLM U Set.univ X := by
  apply deltaKLocCLM_eq_univ_of_zero_off
  intro p hp e he
  exact hX e (edge_not_touch_of_not_corner hp he)

/-- The actual W-sandwiched, Dirichlet-compressed Delta is unchanged.
No inverse guard and no class assumption are used. -/
theorem corner_Dpi_eq_all (sJ : PlaqSel) (P : IngrBParams) :
    (dataS selCorner sJ P).Dpi = (dataS selAll sJ P).Dpi := by
  ext1 X
  change (pE P.G) (ContinuousLinearMap.adjoint (Wop P.G P.U P.a)
      (deltaKLocCLM P.U (plaqCorner P.G.Om0) (Wop P.G P.U P.a (iE P.G X)))) =
    (pE P.G) (ContinuousLinearMap.adjoint (Wop P.G P.U P.a)
      (deltaKLocCLM P.U Set.univ (Wop P.G P.U P.a (iE P.G X))))
  rw [deltaKLocCLM_corner_eq P.G P.U _
    (Wop_mem_bondSupp P.G P.U P.a (iE P.G X) X.2)]

theorem corner_Ginv_eq_all (sJ : PlaqSel) (P : IngrBParams) :
    (dataS selCorner sJ P).Ginv = (dataS selAll sJ P).Ginv := by
  unfold BaseDataS.Ginv
  rw [corner_Dpi_eq_all]
  rfl


/-! ## Four-bond coverage and zero-logarithm regularity on the slab path. -/

open AdalyFormal.NonVac

-- Verbatim theorem block from round-2 s2-nonvacuity/r1-prove/Attempt.lean.
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

/-- The background can be arbitrary off the touching bonds: all three
regularity inequalities still have the exact zero logarithm. -/
theorem perCubeRegularTouch_of_one_on_touch {ell M f k : ℕ} (S : Tower L)
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {α₀ η : ℝ}
    (hα : 0 < α₀) (hM : 0 < M) (hf : 0 < f) (hell : 0 < ell) (hη : 0 < η)
    (U : LinkCfg L) (hU : ∀ e : Bond L, TouchBond (S.Om 0) e → U e = 1) :
    PerCubeRegularTouch ell M f k S α₀ η U := by
  intro sites j hq
  have hsub := AdalyFormal.D1Literal.classCube_sub_om0 hS hq
  have hpos : ∀ n : ℕ, 0 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ n) := by
    intro n
    have : (0 : ℝ) < (ell : ℝ) ^ j * η := mul_pos (pow_pos (by exact_mod_cast hell) j) hη
    have hf' : (0 : ℝ) < f := by exact_mod_cast hf
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨fun _ => 1, fun _ => 0, ?_, ?_, ?_⟩
  · intro e he
    refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
    · have h1 : U e = 1 := hU e (he.elim (fun h => Or.inl (hsub h)) (fun h => Or.inr (hsub h)))
      simp [periodicGaugeTransform, h1]
    · simpa [frobNorm_zero'] using hpos 1
  · intro μ ν x _ _
    simpa [frobNorm_zero'] using hpos 2
  · intro μ x _
    have h0 : ddA η (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℂ)) x μ = 0 := by
      unfold ddA curlA
      simp
    rw [h0, frobNorm_zero']
    exact hpos 3

theorem Uth_one_on_touch (Om : Set (PeriodicLatticeSite L)) (θ : ℝ)
    (e : Bond L) (he : TouchBond Om e) : Uth Om θ e = 1 := by
  have hn : e ∉ Zb Om := fun h => he.elim h.1 h.2
  simp only [Uth, if_neg hn]

/-- Every point of the old exterior path, not only its flat starting point,
satisfies the new touching regularity. -/
theorem Uth_perCubeRegularTouch {ell M f k : ℕ} (S : Tower L)
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {α₀ η : ℝ}
    (hα : 0 < α₀) (hM : 0 < M) (hf : 0 < f) (hell : 0 < ell) (hη : 0 < η) (θ : ℝ) :
    PerCubeRegularTouch ell M f k S α₀ η (Uth (S.Om 0) θ) :=
  perCubeRegularTouch_of_one_on_touch S hS hα hM hf hell hη _ (Uth_one_on_touch _ θ)

/-- The actual carrier crossing transfers to corner Delta and corner J.
It is an unguarded crossing, not an invertible counterexample. -/
theorem exists_nonunit_corner_Ginv {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ¬ IsUnit (dataS selCorner selCorner
        (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)).Ginv := by
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_Ginv selCorner hell0 a Lam hS hell hroom hbd ha ha4
  refine ⟨θ, h0, h1, ?_⟩
  rw [corner_Ginv_eq_all]
  exact hnu

end Round3.S1Proper


set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace Round11.Refute
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.NonVac

variable {L : PeriodicLatticeExtent}

/-- Only level-zero rows see a separated normal collar; their sum is bounded
by the full fine-field norm. This is a restriction, not a global aI claim. -/
theorem mass_le_of_high_zero (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (A : BondFnL2 L)
    (hhigh : ∀ (j : ℕ), 1 ≤ j → j ≤ G.k → ∀ b ∈ bondsLam G j, (QlinB G U j A) b = 0) :
    ⟪A, MassFull G a (bondSectorOf G U) A⟫ ≤ a * ⟪A, A⟫ := by
  classical
  rw [inner_MassFull]
  have hterm (p : BIdx G) :
      a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖(bondSectorOf G U).Qfull A p‖ ^ 2 =
        if (p.1 : ℕ) = 0 then a * ‖A p.2.1‖ ^ 2 else 0 := by
    obtain ⟨j, b, hb⟩ := p
    change a * (G.ell : ℝ) ^ (j : ℕ) *
      ‖((G.ell : ℝ) ^ (j : ℕ))⁻¹ • (QlinB G U j A) b‖ ^ 2 =
        if (j : ℕ) = 0 then a * ‖A b‖ ^ 2 else 0
    by_cases hj : (j : ℕ) = 0
    · rw [hj, QlinB_zero]
      simp
    · rw [hhigh j (by omega) (by omega) b hb]
      simp [hj]
  simp_rw [hterm]
  rw [Fintype.sum_sigma]
  have hlevel (j : Fin (G.k + 1)) :
      (∑ b : {b : Bond L // b ∈ bondsLam G j},
        if (j : ℕ) = 0 then a * ‖A b.1‖ ^ 2 else 0) =
      if (j : ℕ) = 0 then ∑ b : {b : Bond L // b ∈ bondsLam G 0}, a * ‖A b.1‖ ^ 2 else 0 := by
    by_cases hj : (j : ℕ) = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      simp only [Fin.val_zero, if_true]
      rfl
    · simp [hj]
  simp_rw [hlevel]
  rw [Finset.sum_eq_single (0 : Fin (G.k + 1))]
  · simp only [Fin.val_zero, if_true]
    rw [PiLp.inner_apply, Finset.mul_sum]
    simp_rw [real_inner_self_eq_norm_sq]
    have he := Fintype.sum_subtype_add_sum_subtype (fun b => b ∈ bondsLam G 0)
      (fun b => a * ‖A b‖ ^ 2)
    have hp : 0 ≤ ∑ b : {b : Bond L // b ∉ bondsLam G 0}, a * ‖A b.1‖ ^ 2 :=
      Finset.sum_nonneg (fun b _ => mul_nonneg ha (sq_nonneg _))
    linarith
  · intro j _ hj
    have h : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [h]
  · simp

/-- The NV torus has even transverse periods even when ell is odd. -/
theorem nvN_even (ell M R : ℕ) : 2 ∣ nvN ell M R := by
  refine ⟨M * ell ^ 2 * (3 * R + 1), ?_⟩
  unfold nvN
  ring

theorem neg_one_succ_mod {N : ℕ} (heven : 2 ∣ N) (n : ℕ) :
    (-1 : ℝ) ^ ((n + 1) % N) = -(-1 : ℝ) ^ n := by
  calc
    _ = (-1 : ℝ) ^ (((n + 1) % N) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1 : ℝ) ^ ((n + 1) % 2) := by rw [Nat.mod_mod_of_dvd _ heven]
    _ = (-1 : ℝ) ^ (n + 1) := (neg_one_pow_eq_pow_mod_two _).symm
    _ = _ := by rw [pow_succ]; ring

noncomputable def checkerSign (x : PeriodicLatticeSite L) : ℝ :=
  (-1 : ℝ) ^ (x 1).val * (-1 : ℝ) ^ (x 2).val

theorem checkerSign_ne_zero (x : PeriodicLatticeSite L) : checkerSign x ≠ 0 := by
  unfold checkerSign
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

theorem checkerSign_shift {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (heven : 2 ∣ N) (x : PeriodicLatticeSite L) (ν : Fin 3) (hν : ν ≠ 0) :
    checkerSign (periodicLatticeShift x ν) = -checkerSign x := by
  unfold checkerSign
  rw [shift_val_N hN hN1, shift_val_N hN hN1]
  fin_cases ν
  · exact (hν rfl).elim
  · simp [neg_one_succ_mod heven]
  · simp [neg_one_succ_mod heven]

open Classical in
noncomputable def checkerAmp (Om : Set (PeriodicLatticeSite L)) (X : SuTwo)
    (x : PeriodicLatticeSite L) : SuTwo :=
  if x ∈ Om ∧ periodicLatticeShift x 0 ∉ Om then checkerSign x • X else 0

theorem checkerAmp_bd (Om : Set (PeriodicLatticeSite L)) (X : SuTwo)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (hside : ∀ (z : PeriodicLatticeSite L) (ν : Fin 3), periodicLatticeShift z ν ≠ z)
    (x : PeriodicLatticeSite L) (hx : checkerAmp Om X x ≠ 0) : BdPt Om x := by
  classical
  have hb : x ∈ Om ∧ periodicLatticeShift x 0 ∉ Om := by
    by_contra hb
    exact hx (by simp [checkerAmp, hb])
  exact ⟨hb.1, hb.2, htrans, hside x⟩

theorem checkerAmp_skew {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (heven : 2 ∣ N) (Om : Set (PeriodicLatticeSite L)) (X : SuTwo)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (x : PeriodicLatticeSite L) (ν : Fin 3) (hν : ν ≠ 0) :
    checkerAmp Om X (periodicLatticeShift x ν) = -checkerAmp Om X x := by
  classical
  have hpred : (periodicLatticeShift x ν ∈ Om ∧
      periodicLatticeShift (periodicLatticeShift x ν) 0 ∉ Om) ↔
      (x ∈ Om ∧ periodicLatticeShift x 0 ∉ Om) := by
    rw [shift_comm x hν, htrans x ν hν, htrans (periodicLatticeShift x 0) ν hν]
  unfold checkerAmp
  simp only [hpred, checkerSign_shift hN hN1 heven x ν hν]
  split_ifs <;> simp

theorem side_of_uniform {N : ℕ} (hN : ∀ μ, L μ + 1 = N) (hN1 : 1 < N)
    (x : PeriodicLatticeSite L) (ν : Fin 3) : periodicLatticeShift x ν ≠ x := by
  intro he
  have hv := congrArg (fun z : PeriodicLatticeSite L => (z ν).val) he
  rw [shift_val_N hN hN1, if_pos rfl] at hv
  have hx : (x ν).val < N := by have hh := (x ν).isLt; have hh' := hN ν; omega
  by_cases hl : (x ν).val + 1 < N
  · rw [Nat.mod_eq_of_lt hl] at hv
    omega
  · have hh : (x ν).val + 1 = N := by omega
    rw [hh, Nat.mod_self] at hv
    omega

open AdalyFormal.StatementLaneG

/-- A nonpositive, nonzero endpoint witness allows the singular point to be
at the endpoint. This avoids losing a=8 to the strict version of IVT. -/
theorem exists_nonunit_path_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℝ → (E →L[ℝ] E)) (hc : Continuous F)
    (hs : ∀ t x y, ⟪F t x, y⟫ = ⟪x, F t y⟫) (h0 : PSD (F 0))
    (T : ℝ) (hT : 0 < T) (v : E) (hvn : v ≠ 0) (hv : ⟪v, F T v⟫ ≤ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ ¬ IsUnit (F t) := by
  classical
  by_cases hp : PSD (F T)
  · refine ⟨T, hT.le, le_rfl, fun hu => ?_⟩
    have hk := psd_kernel (F T) (hs T) hp v (le_antisymm hv (hp v))
    have hi : Function.Injective (F T) := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    exact hvn (hi (by rw [hk, map_zero]))
  · simp only [PSD, not_forall, not_le] at hp
    obtain ⟨w, hw⟩ := hp
    obtain ⟨t, ht0, htT, ht⟩ := exists_nonunit_path F hc hs h0 T hT w hw
    exact ⟨t, ht0, htT.le, ht⟩

end Round11.Refute


namespace Round11.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2 AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8 AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift gradCovariantAdjointValue)
open Round11.Refute
variable {L : PeriodicLatticeExtent}

/-- An arbitrary collar field whose nonzero bonds start within distance two
of the complement. This does not replace the actual weighted mass by aI. -/
theorem collar_locality {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (A : BondFnL2 L)
    (hsupp : ∀ e, A e ≠ 0 → ∃ z, z ∉ S.Om 0 ∧ pdist e.1 z ≤ 2)
    (U : Cfg L) (a : ℝ) :
    Wop (geomOf ell k S) U a A = A ∧ Tfull (geomOf ell k S) U A = 0 ∧
    ∀ (j : ℕ), 1 ≤ j → j ≤ k → ∀ b ∈ bondsLam (geomOf ell k S) j,
      (QlinB (geomOf ell k S) U j A) b = 0 := by
  classical
  have hT : Tfull (geomOf ell k S) U A = 0 := by
    unfold Tfull
    simp only [ContinuousLinearMap.comp_apply]
    unfold Rproj
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
    intro u hu
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : u z = 0
    · rw [hz]; simp
    · have hnear : ∀ e : Bond L, pdist e.1 z ≤ 1 → A e = 0 := by
        intro e hed
        by_contra he
        obtain ⟨w, hw, hew⟩ := hsupp e he
        apply hz
        refine RImage_support S U hu z (fun y hy hy1 => ?_)
        have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) w hw y hy1
        have hdist := pdist_triangle w e.1 z
        have hdist2 := pdist_triangle w z y
        have hed' : pdist w e.1 ≤ 2 := by rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact hew
        have hb : bigSide M ell 0 = M := by simp [bigSide]
        rw [hb] at hcl
        change pdist z y ≤ 1 at hy
        omega
      have hg : (gradAdj U A) z = 0 := by
        rw [show (gradAdj U A) z = (WithLp.ofLp (gradAdj U A)) z from rfl, gradAdj_apply]
        unfold gradCovariantAdjointValue
        apply Finset.sum_eq_zero
        intro μ _
        have h1 : (WithLp.ofLp A) (z, μ) = 0 := hnear (z, μ) (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega)
        have h2 : (WithLp.ofLp A) (periodicLatticeShiftBack z μ, μ) = 0 := by
          apply hnear
          have ht := pdist_shift_le (periodicLatticeShiftBack z μ) μ
          rwa [periodicLatticeShift_shiftBack] at ht
        rw [h1, h2]; simp
      rw [hg]; simp
  refine ⟨?_, hT, ?_⟩
  · unfold Tfull at hT
    simp only [ContinuousLinearMap.comp_apply] at hT
    unfold Wop
    change A - (gradL2 U) (Gp (geomOf ell k S) U a ((Rproj (geomOf ell k S) U) ((gradAdj U) A))) = A
    rw [hT]; simp
  · intro j hj1 hjk b hb
    obtain ⟨hb1, -⟩ := hb
    obtain ⟨y, hyOm, hyd⟩ : ∃ y : PeriodicLatticeSite L, y ∈ S.Om j ∧ pdist b.1 y ≤ ell ^ j := by
      rcases hb1 with h | h
      · exact ⟨b.1, h.2.1, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
      · exact ⟨_, h.2.1, pdist_coarseShift_le b.1 (ell ^ j) b.2⟩
    have hball := admissible_ball_Om0 hS hj1 (by omega) hyOm
    have hz : QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j (suCoord A) b
        = QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j 0 b := by
      refine QlinCompL_congr_in (geomOf ell k S).ell (by show 0 < ell; omega) _ j b (fun e he => ?_)
      have hAe : A e = 0 := by
        by_contra hn
        obtain ⟨w, hw, hew⟩ := hsupp e hn
        have hfar : R * (M * ell ^ (j - 1)) < pdist y w := by
          by_contra hnot
          exact hw (hball (by simpa [Ball] using (not_lt.mp hnot)))
        have hpow : ell ^ j = ell * ell ^ (j - 1) := by
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          simp [pow_succ, mul_comm]
        have hRM : 17 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
          calc 17 * ell ^ j = (17 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
            _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ hroom
            _ = R * (M * ell ^ (j - 1)) := by ring
        have h1 := pdist_triangle y b.1 w
        have h2 := pdist_triangle b.1 e.1 w
        have h3 : pdist y b.1 ≤ ell ^ j := by rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact hyd
        have hrho := rhoT_le ell hell j
        have hp : 0 < ell ^ j := pow_pos (by omega) _
        change pdist b.1 e.1 ≤ rhoT ell j at he
        omega
      show fromM2 (((WithLp.ofLp A) e : SuTwo) : M2) = (0 : XS L) e
      rw [show (WithLp.ofLp A) e = 0 from hAe]
      simp
    rw [QlinB_apply, suCoordInv_apply_congr' hz]
    simp

/-- The right-boundary version of the probe's three-component ansatz.
The sign of t reverses from the left-boundary convention. -/
noncomputable def mixedField (f : PeriodicLatticeSite L → SuTwo) (n m t : ℝ) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => if b.2 = 0 then n • f b.1 + m • f (periodicLatticeShift b.1 0) else t • f b.1)

theorem mixedField_apply (f : PeriodicLatticeSite L → SuTwo) (n m t : ℝ) (b : Bond L) :
    mixedField f n m t b = if b.2 = 0 then n • f b.1 + m • f (periodicLatticeShift b.1 0) else t • f b.1 := rfl

theorem bd_disjoint (Om : Set (PeriodicLatticeSite L))
    (f : PeriodicLatticeSite L → SuTwo) (hbd : ∀ x, f x ≠ 0 → BdPt Om x) (x : PeriodicLatticeSite L) :
    f x = 0 ∨ f (periodicLatticeShift x 0) = 0 := by
  by_cases hx : f x = 0
  · exact Or.inl hx
  · right
    by_contra hn
    exact (hbd x hx).hx' (hbd _ hn).hx

theorem mixed_locality {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (f : PeriodicLatticeSite L → SuTwo) (hbd : ∀ x, f x ≠ 0 → BdPt (S.Om 0) x)
    (n m t : ℝ) (U : Cfg L) (a : ℝ) :
    mixedField f n m t ∈ bondSupp (geomOf ell k S) ∧
    Wop (geomOf ell k S) U a (mixedField f n m t) = mixedField f n m t ∧
    Tfull (geomOf ell k S) U (mixedField f n m t) = 0 ∧
    ∀ (j : ℕ), 1 ≤ j → j ≤ k → ∀ b ∈ bondsLam (geomOf ell k S) j,
      (QlinB (geomOf ell k S) U j (mixedField f n m t)) b = 0 := by
  have hsupport (e : Bond L) (he : mixedField f n m t e ≠ 0) :
      f e.1 ≠ 0 ∨ e.2 = 0 ∧ f (periodicLatticeShift e.1 0) ≠ 0 := by
    by_cases h1 : f e.1 = 0
    · right
      by_cases hd : e.2 = 0
      · refine ⟨hd, fun h2 => he ?_⟩
        simp [mixedField_apply, hd, h1, h2]
      · exact (he (by simp [mixedField_apply, hd, h1])).elim
    · exact Or.inl h1
  refine ⟨?_, collar_locality hS hell hroom _ ?_ U a⟩
  · intro e he
    by_contra hn
    apply he
    rcases hsupport e hn with h | ⟨hd, h⟩
    · exact Or.inl (hbd _ h).hx
    · exact Or.inr (by rw [hd]; exact (hbd _ h).hx)
  · intro e he
    rcases hsupport e he with h | ⟨hd, h⟩
    · exact ⟨_, (hbd _ h).hx', (AdalyFormal.StatementLaneR8.pdist_shift_le _ _).trans (by omega)⟩
    · refine ⟨_, (hbd _ h).hx', ?_⟩
      have h1 := pdist_shift_le e.1 (0 : Fin 3)
      have h2 := pdist_shift_le (periodicLatticeShift e.1 0) (0 : Fin 3)
      have h3 := pdist_triangle e.1 (periodicLatticeShift e.1 0) (periodicLatticeShift (periodicLatticeShift e.1 0) 0)
      omega

theorem mixed_inner (Om : Set (PeriodicLatticeSite L))
    (f : PeriodicLatticeSite L → SuTwo) (hbd : ∀ x, f x ≠ 0 → BdPt Om x) (n m t : ℝ) :
    ⟪mixedField f n m t, mixedField f n m t⟫ =
      (n^2 + m^2 + 2*t^2) * ∑ x, ⟪f x, f x⟫ := by
  have he (x : PeriodicLatticeSite L) :
      ⟪n • f x + m • f (periodicLatticeShift x 0), n • f x + m • f (periodicLatticeShift x 0)⟫ =
      n^2 * ⟪f x, f x⟫ + m^2 * ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫ := by
    rcases bd_disjoint Om f hbd x with hx | hx <;>
      simp only [hx, smul_zero, zero_add, add_zero, inner_zero_left, mul_zero, real_inner_smul_left, real_inner_smul_right] <;> ring
  have hsum : (∑ x, ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫) = ∑ x, ⟪f x, f x⟫ := by
    exact Equiv.sum_comp (Equiv.ofBijective (fun x : PeriodicLatticeSite L => periodicLatticeShift x 0) (by
      exact ⟨fun x y h => by simpa only [periodicLatticeShiftBack_shift] using congrArg (fun z => periodicLatticeShiftBack z 0) h,
        fun x => ⟨periodicLatticeShiftBack x 0, periodicLatticeShift_shiftBack x 0⟩⟩)) (fun x => ⟪f x, f x⟫)
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  have hdir (x : PeriodicLatticeSite L) :
      (∑ μ : Fin 3, ⟪mixedField f n m t (x, μ), mixedField f n m t (x, μ)⟫) =
      n^2 * ⟪f x, f x⟫ + m^2 * ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫ + 2*t^2 * ⟪f x, f x⟫ := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [mixedField_apply]
    norm_num only [show (1 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 0 from by decide, if_false, if_true]
    rw [he]
    simp only [real_inner_smul_left, real_inner_smul_right]
    ring
  change (∑ x, ∑ μ : Fin 3, ⟪mixedField f n m t (x, μ), mixedField f n m t (x, μ)⟫) = _
  simp_rw [hdir]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hsum]
  ring

theorem RMap_Uth_pi (Om : Set (PeriodicLatticeSite L)) (e : Bond L) (X : SuTwo) :
    RMap (Uth Om Real.pi e) X = X := by
  classical
  unfold Uth
  split_ifs
  · apply Subtype.ext
    rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply, uθ_pi_coe]
    simp
  · rw [AdalyFormal.Balaban.CovariantOperators.RMap_one]; rfl

theorem hol_Uth_pi (Om : Set (PeriodicLatticeSite L)) (p : PeriodicLatticePlaquette L) :
    ((holonomyElem (Uth Om Real.pi) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
    ((holonomyElem (Uth Om Real.pi) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  classical
  have hi : (((uθ Real.pi)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    change star ((uθ Real.pi : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
    rw [uθ_pi_coe]; simp
  unfold holonomyElem periodicPlaquetteHolonomy Uth
  dsimp only
  split_ifs <;> simp [uθ_pi_coe, hi]

theorem plaq_flat (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L)
    (A : Bond L → SuTwo) (h : ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    bilPlaq U p A A = 0 := by
  have hinv : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have hh : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [hh, h]; simp
  have hre : reHolonomy U p = 1 := by
    unfold reHolonomy; rw [h, hinv]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have him : imHolonomy U p = 0 := by
    unfold imHolonomy; rw [h, hinv]; simp
  rw [bilPlaq_atoms, hre, him]
  simp

theorem plaq_pi_le (Om : Set (PeriodicLatticeSite L)) (p : PeriodicLatticePlaquette L)
    (A : Bond L → SuTwo) :
    hsInner (curlValueCovariant (Uth Om Real.pi) A p) (curlValueCovariant (Uth Om Real.pi) A p) +
      (1/2 : ℝ) * bilPlaq (Uth Om Real.pi) p A A ≤
      hsInner (curlValueCovariant (Uth Om Real.pi) A p) (curlValueCovariant (Uth Om Real.pi) A p) := by
  rcases hol_Uth_pi Om p with h | h
  · rw [plaq_flat _ _ _ h]; simp
  · rw [plaq_central _ _ _ h]
    change -⟪curlValueCovariant (Uth Om Real.pi) A p, curlValueCovariant (Uth Om Real.pi) A p⟫ ≤ _
    exact neg_le_self (real_inner_self_nonneg)

theorem mixed_curl (Om : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo)
    (hskew : ∀ x (ν : Fin 3), ν ≠ 0 → f (periodicLatticeShift x ν) = -f x)
    (n m t : ℝ) (x : PeriodicLatticeSite L) (ν : {ν : Fin 3 // 0 < ν}) :
    curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (mixedField f n m t)) (P1 x ν) =
      (2*n-t) • f x + (2*m+t) • f (periodicLatticeShift x 0) := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  unfold curlValueCovariant AdalyFormal.D1Literal.P1
  simp only [mixedField, WithLp.ofLp_toLp, hν, if_false, if_true, RMap_Uth_pi]
  rw [shift_comm x hν, hskew x ν.1 hν, hskew (periodicLatticeShift x 0) ν.1 hν]
  module

theorem mixed_curl_transverse (Om : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo)
    (hskew : ∀ x (ν : Fin 3), ν ≠ 0 → f (periodicLatticeShift x ν) = -f x)
    (n m t : ℝ) (x : PeriodicLatticeSite L) :
    curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (mixedField f n m t))
      (x, ⟨(1,2), by decide⟩) = 0 := by
  unfold curlValueCovariant
  simp only [mixedField, WithLp.ofLp_toLp, show (1 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, if_false, RMap_Uth_pi]
  rw [hskew x 1 (by decide), hskew x 2 (by decide)]
  module

/-- The full frozen Delta form, not a substitute three-by-three operator.
The inner face is bounded from above by its flat value. -/
theorem mixed_delta_le (Om : Set (PeriodicLatticeSite L)) (f : PeriodicLatticeSite L → SuTwo)
    (hbd : ∀ x, f x ≠ 0 → BdPt Om x)
    (hskew : ∀ x (ν : Fin 3), ν ≠ 0 → f (periodicLatticeShift x ν) = -f x)
    (n m t : ℝ) :
    ⟪mixedField f n m t, deltaKLocCLM (Uth Om Real.pi) Set.univ (mixedField f n m t)⟫ ≤
      (-8*n^2 + 8*m^2 + 8*(n+m)*t) * ∑ x, ⟪f x, f x⟫ := by
  classical
  let A := mixedField f n m t
  let q := fun p : PeriodicLatticePlaquette L =>
    hsInner (curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp A) p)
      (curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp A) p) +
    (1/2 : ℝ) * bilPlaq (Uth Om Real.pi) p (WithLp.ofLp A) (WithLp.ofLp A)
  have ht (x : PeriodicLatticeSite L) (ν : {ν : Fin 3 // 0 < ν}) :
      q (P1 x ν) ≤ -(2*n-t)^2 * ⟪f x, f x⟫ +
        (2*m+t)^2 * ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫ := by
    by_cases hx : f x = 0
    · have h := plaq_pi_le Om (P1 x ν) (WithLp.ofLp A)
      change q (P1 x ν) ≤ _ at h
      have hc := mixed_curl Om f hskew n m t x ν
      change curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp A) (P1 x ν) = _ at hc
      rw [hc, hx] at h
      change q (P1 x ν) ≤ ⟪(2*n-t) • (0 : SuTwo) + (2*m+t) • f (periodicLatticeShift x 0),
        (2*n-t) • (0 : SuTwo) + (2*m+t) • f (periodicLatticeShift x 0)⟫ at h
      rw [hx]
      simp only [smul_zero, zero_add, inner_zero_left, mul_zero, real_inner_smul_left, real_inner_smul_right] at h ⊢
      nlinarith [h]
    · have hn : f (periodicLatticeShift x 0) = 0 := (bd_disjoint Om f hbd x).resolve_left hx
      have hc := (hbd x hx).holonomy1 Real.pi ν
      have he : q (P1 x ν) = -⟪(2*n-t) • f x, (2*n-t) • f x⟫ := by
        dsimp [q]
        rw [plaq_central _ _ _ (by rw [hc]; exact uθ_pi_coe)]
        change -⟪curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (mixedField f n m t)) (P1 x ν),
          curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp (mixedField f n m t)) (P1 x ν)⟫ = _
        rw [mixed_curl Om f hskew n m t x ν, hn, smul_zero, add_zero]
      rw [he, hn]
      simp only [inner_zero_left, mul_zero, add_zero, real_inner_smul_left, real_inner_smul_right]
      nlinarith
  have hz (x : PeriodicLatticeSite L) : q (x, ⟨(1,2), by decide⟩) ≤ 0 := by
    have h := plaq_pi_le Om (x, ⟨(1,2), by decide⟩) (WithLp.ofLp A)
    change q (x, ⟨(1,2), by decide⟩) ≤ _ at h
    have hc := mixed_curl_transverse Om f hskew n m t x
    change curlValueCovariant (Uth Om Real.pi) (WithLp.ofLp A) (x, ⟨(1,2), by decide⟩) = 0 at hc
    rw [hc] at h
    change q (x, ⟨(1,2), by decide⟩) ≤ ⟪(0 : SuTwo), 0⟫ at h
    simpa only [inner_zero_left] using h
  have hsum : (∑ x, ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫) = ∑ x, ⟪f x, f x⟫ := by
    exact Equiv.sum_comp (Equiv.ofBijective (fun x : PeriodicLatticeSite L => periodicLatticeShift x 0) (by
      exact ⟨fun x y h => by simpa only [periodicLatticeShiftBack_shift] using congrArg (fun z => periodicLatticeShiftBack z 0) h,
        fun x => ⟨periodicLatticeShiftBack x 0, periodicLatticeShift_shiftBack x 0⟩⟩)) (fun x => ⟪f x, f x⟫)
  have hh : (∑ x, ∑ d, q (x,d)) ≤
      ∑ x, (-2*(2*n-t)^2 * ⟪f x, f x⟫ + 2*(2*m+t)^2 * ⟪f (periodicLatticeShift x 0), f (periodicLatticeShift x 0)⟫) := by
    apply Finset.sum_le_sum
    intro x _
    have hdirs : (Finset.univ : Finset {ab : Fin 3 × Fin 3 // ab.1 < ab.2}) =
        {⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(1,2), by decide⟩} := by decide
    rw [hdirs, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h1 := ht x ⟨1, by decide⟩
    have h2 := ht x ⟨2, by decide⟩
    have h3 := hz x
    change q (x, ⟨(0,1), by decide⟩) ≤ _ at h1
    change q (x, ⟨(0,2), by decide⟩) ≤ _ at h2
    linarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum] at hh
  rw [delta_form_sum, Fintype.sum_prod_type]
  change (∑ x, ∑ d, q (x,d)) ≤ _
  nlinarith [hh]

theorem mixed_nonzero (Om : Set (PeriodicLatticeSite L))
    (f : PeriodicLatticeSite L → SuTwo) (hbd : ∀ x, f x ≠ 0 → BdPt Om x)
    {x : PeriodicLatticeSite L} (hx : f x ≠ 0) (m t : ℝ) : mixedField f 1 m t ≠ 0 := by
  intro he
  have hn := (bd_disjoint Om f hbd x).resolve_left hx
  have hh := congrArg (fun A : BondFnL2 L => A (x,0)) he
  apply hx
  simpa only [mixedField_apply, if_true, one_smul, hn, smul_zero, add_zero, PiLp.zero_apply] using hh

/-- The radical witness is the minimum of the probe's compact three-variable
ansatz. This arithmetic identity is used on the actual lattice field. -/
theorem radical_identity :
    -8*(1:ℝ)^2 + 8*(9-4*Real.sqrt 5)^2 + 8*(1+(9-4*Real.sqrt 5))*(2-Real.sqrt 5) =
      -(4*Real.sqrt 5) * (1^2 + (9-4*Real.sqrt 5)^2 + 2*(2-Real.sqrt 5)^2) := by
  linear_combination (72 * Real.sqrt 5 - 160) * Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)

open AdalyFormal.StatementLaneG

theorem Fth_pi_bound_sqrt5 (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {N : ℕ} (hN : ∀ μ, scaleUp ell k Lu μ + 1 = N) (hN1 : 1 < N) (heven : 2 ∣ N)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) :
    ∃ v : ↥(bondSupp (geomOf ell k S)), v ≠ 0 ∧
      ⟪v, Fth sJ ell k Lu hell0 S a Lam Real.pi v⟫ ≤ (a - 4*Real.sqrt 5) * ⟪v,v⟫ := by
  classical
  let f := checkerAmp (S.Om 0) AdalyFormal.Balaban.CovariantOperators.suTwoWitness
  let m := 9-4*Real.sqrt 5
  let t := 2-Real.sqrt 5
  let A := mixedField f 1 m t
  have hf : ∀ z, f z ≠ 0 → BdPt (S.Om 0) z :=
    checkerAmp_bd _ _ hbd.trans (side_of_uniform hN hN1)
  obtain ⟨hmem, hW, hT, hQ⟩ := mixed_locality hS hell hroom f hf 1 m t (Uth (S.Om 0) Real.pi) a
  have hD := mixed_delta_le (S.Om 0) f hf (checkerAmp_skew hN hN1 heven _ _ hbd.trans) 1 m t
  have hI := mixed_inner (S.Om 0) f hf 1 m t
  have hid : -8*(1:ℝ)^2 + 8*m^2 + 8*(1+m)*t = -(4*Real.sqrt 5) * (1^2 + m^2 + 2*t^2) := radical_identity
  rw [hid, mul_assoc, ← hI] at hD
  have hM := mass_le_of_high_zero (geomOf ell k S) (Uth (S.Om 0) Real.pi) a ha A hQ
  have hfx : f x ≠ 0 := by
    change checkerAmp (S.Om 0) AdalyFormal.Balaban.CovariantOperators.suTwoWitness x ≠ 0
    simp only [checkerAmp, hbd.hx, hbd.hx']
    exact smul_ne_zero (checkerSign_ne_zero x) AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero
  have hAn : A ≠ 0 := mixed_nonzero (S.Om 0) f hf hfx m t
  refine ⟨⟨A,hmem⟩, fun hv => hAn (congrArg Subtype.val hv), ?_⟩
  show ⟪(⟨A,hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
    (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Ginv ⟨A,hmem⟩⟫ ≤
      (a - 4*Real.sqrt 5) * ⟪A,A⟫
  rw [BaseDataS.inner_Ginv]
  have hdpi : ⟪(⟨A,hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Dpi ⟨A,hmem⟩⟫ ≤
      -(4*Real.sqrt 5) * ⟪A,A⟫ := by
    refine (E0_Dpi_inner selAll (geomOf ell k S) (Uth (S.Om 0) Real.pi) a ⟨A,hmem⟩).trans_le ?_
    change ⟪Wop (geomOf ell k S) (Uth (S.Om 0) Real.pi) a A,
      deltaKLocCLM (Uth (S.Om 0) Real.pi) Set.univ (Wop (geomOf ell k S) (Uth (S.Om 0) Real.pi) a A)⟫ ≤ _
    rw [hW]
    exact hD
  have ht : (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).T ⟨A,hmem⟩ = 0 := hT
  have hm : ⟪(⟨A,hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Mass ⟨A,hmem⟩⟫ ≤ a * ⟪A,A⟫ := by
    change ⟪(⟨A,hmem⟩ : ↥(bondSupp (geomOf ell k S))),
      (pE (geomOf ell k S)) (MassFull (geomOf ell k S) a
        (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi)) A)⟫ ≤ _
    rw [pE_inner_right]
    exact hM
  rw [ht]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  nlinarith

theorem exists_nonunit_sqrt5 (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu))
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {N : ℕ} (hN : ∀ μ, scaleUp ell k Lu μ + 1 = N) (hN1 : 1 < N) (heven : 2 ∣ N)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (hac : a ≤ 4*Real.sqrt 5) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ Real.pi ∧
      ¬ IsUnit (dataS selAll sJ
        (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)).Ginv := by
  obtain ⟨v,hvn,hv⟩ := Fth_pi_bound_sqrt5 sJ hell0 a Lam hS hell hroom hN hN1 heven hbd ha
  have hnonpos : ⟪v, Fth sJ ell k Lu hell0 S a Lam Real.pi v⟫ ≤ 0 :=
    hv.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) real_inner_self_nonneg)
  exact exists_nonunit_path_le (fun t => Fth sJ ell k Lu hell0 S a Lam t)
    (Fth_cont sJ hell0 a Lam hS hell hroom) (fun t u v => Fth_symm sJ hell0 a Lam t u v)
    (Fth_zero_psd sJ hell0 a Lam ha) Real.pi Real.pi_pos v hvn hnonpos

open Round3.S1Proper Round7.S1Odd AdalyFormal.NonVac

/-- Refutation of the exact ell-slice up to and including the radical endpoint.
The quantifier/class/competitor body is the round-7/round-11-r1 proof verbatim,
with only the crossing theorem and its upper mass bound replaced. -/
theorem not_touchFour_every_ell_le_sqrt5 (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ)
    (ha : 0 < a) (hac : a ≤ 4*Real.sqrt 5) : ¬ P428TouchFourAt ell hell a := by
  intro h
  obtain ⟨m₀, hm₀, hm⟩ := h
  obtain ⟨R₀, hR₀⟩ := hm m₀ le_rfl
  have hRge : R₀ ≤ max R₀ 18 := le_max_left _ _
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ (max R₀ 18) hRge
  obtain ⟨R, hRdef⟩ : ∃ R, R = max R₀ 18 := ⟨_, rfl⟩
  rw [← hRdef] at hcore
  have hR18 : 18 ≤ R := by rw [hRdef]; exact le_max_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M, M = ell ^ m₀ := ⟨_, rfl⟩
  rw [← hMdef] at hcore
  have hell0 : 0 < ell := by omega
  have hM : 0 < M := by rw [hMdef]; exact pow_pos hell0 m₀
  have hdvd : ell ∣ M := by rw [hMdef]; exact dvd_pow_self ell (by omega)
  have hellM : ell ≤ M := Nat.le_of_dvd hM hdvd
  have G := slabGeo_inst (ell := ell) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := ell) hell hM hR18
  have hN : ∀ μ, scaleUp ell 2 (nvLu M R) μ + 1 = nvN ell M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible ell M R 2 (SlabNv ell M R) := slab3_admissible G hN
  have hcov : CoversOm0p ell M 12 2 (SlabNv ell M R) :=
    slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR18
  have hroom : 17 * ell ≤ R * M := by nlinarith
  have hN1 : 1 < nvN ell M R := by
    have hp : 0 < M * ell ^ 2 := Nat.mul_pos hM (pow_pos hell0 2)
    unfold nvN
    nlinarith [Nat.zero_le (6 * R)]
  obtain ⟨θ, h0, h1, hnuAll⟩ := exists_nonunit_sqrt5 selCorner (ell := ell) (M := M) (R := R)
    (k := 2) (Lu := nvLu M R) hell0 (S := SlabNv ell M R) a (LamN M R)
    hAdm hell hroom hN hN1 (nvN_even ell M R) hbd ha.le hac
  have hnu : ¬ IsUnit (dataS selCorner selCorner
      (gparams ell 2 (nvLu M R) hell0 (SlabNv ell M R)
        (Uth ((SlabNv ell M R).Om 0) θ) a (LamN M R))).Ginv := by
    rw [corner_Ginv_eq_all]
    exact hnuAll
  obtain ⟨α₀, hα0def⟩ : ∃ α₀ : ℝ, α₀ = min (a₀ / (12 * M)) 1 / 2 := ⟨_, rfl⟩
  have hα0 : 0 < α₀ := by
    rw [hα0def]
    have : 0 < a₀ / (12 * (M : ℝ)) := by positivity
    have := lt_min this one_pos
    positivity
  have hαS : (12 : ℝ) * M * α₀ ≤ a₀ := by
    rw [hα0def]
    have h := min_le_left (a₀ / (12 * (M : ℝ))) 1
    have h2 : (12 : ℝ) * M * (a₀ / (12 * M)) = a₀ := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 12 * M)
    have h0 : 0 ≤ min (a₀ / (12 * (M : ℝ))) 1 := le_min (by positivity) zero_le_one
    nlinarith
  have hηpos : (0 : ℝ) < ((ell : ℝ) ^ 2)⁻¹ :=
    inv_pos.mpr (pow_pos (by exact_mod_cast hell0) 2)
  have hcls : ClassCoupledFour ell M 12 2 (SlabNv ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹
      (Uth ((SlabNv ell M R).Om 0) θ) :=
    ⟨hcov.1, slabNv_coversFour hcov,
      Uth_perCubeRegularTouch _ hAdm.1 hα0 hM (by norm_num) hell0 hηpos θ⟩
  have hineq := hcore 2 (by norm_num) (nvLu M R) α₀ hα0 (by simpa using hαS)
    (torusOK_nv hell hdvd hM) (SlabNv ell M R) hAdm (LamN M R)
    (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) (Uth ((SlabNv ell M R).Om 0) θ) hcls
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact not_InstIneqS_of_not_unit selCorner selCorner ell 2 hell0 a ha.le (nvLu M R)
    γ₀ hγ (SlabNv ell M R) (LamN M R) (Uth ((SlabNv ell M R).Om 0) θ) hnu
    _ hB1 hB2 hB3 hineq

def GoalWindowSqrt5Closed : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → a ≤ 4*Real.sqrt 5 →
    ¬ P428TouchFourAt ell hell a

theorem window_sqrt5_closed_proved : GoalWindowSqrt5Closed := not_touchFour_every_ell_le_sqrt5

/-- A convenient entirely rational subwindow, strictly larger than eight. -/
theorem not_touchFour_every_ell_le_rational (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ)
    (ha : 0 < a) (hac : a ≤ (152:ℝ)/17) : ¬ P428TouchFourAt ell hell a := by
  apply not_touchFour_every_ell_le_sqrt5 ell hell a ha
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  have hb : (152:ℝ)/17 ≤ 4*Real.sqrt 5 := by nlinarith
  exact hac.trans hb

end Round11.RefuteR2

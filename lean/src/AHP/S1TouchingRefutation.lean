import D1Lit
import D2Lit
import GdPlaq

set_option maxHeartbeats 8000000

/-!
Round 3 / S-1 proper-domain refutation attempt. The pinned definitions and
exact goal statements are copied below. The proof is goalNeg1_proved.
Only frozen lean/src modules are imported.

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

/-- Exact pinned negative goal. The fixed choices are ell = 2 and a = 1;
m and R are cofinal, with R chosen before either positive cap/constant. -/
theorem goalNeg1_proved : GoalNeg1 := by
  intro h
  obtain ⟨m₀, hm₀, hm⟩ := h 2 le_rfl 1 one_pos
  obtain ⟨R₀, hR₀⟩ := hm m₀ le_rfl
  have hRge : R₀ ≤ max R₀ 18 := le_max_left _ _
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₀ (max R₀ 18) hRge
  obtain ⟨R, hRdef⟩ : ∃ R, R = max R₀ 18 := ⟨_, rfl⟩
  rw [← hRdef] at hcore
  have hR18 : 18 ≤ R := by rw [hRdef]; exact le_max_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 ^ m₀ := ⟨_, rfl⟩
  rw [← hMdef] at hcore
  have hM : 0 < M := by rw [hMdef]; exact pow_pos (by norm_num) m₀
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ m₀ := Nat.pow_le_pow_right (by norm_num) hm₀
  have hdvd : 2 ∣ M := by rw [hMdef]; exact dvd_pow_self 2 (by omega)
  have hell : 2 ≤ 2 := le_rfl
  have hell0 : 0 < 2 := by norm_num
  have G := slabGeo_inst (ell := 2) hell hM hdvd (show 1 ≤ R by omega)
  obtain ⟨w0L, w0R, w1, w2, hQN, hP12, hQ21, hQ10⟩ := nv_widths (ell := 2) hell hM hR18
  have hN : ∀ μ, scaleUp 2 2 (nvLu M R) μ + 1 = nvN 2 M R := fun μ => scaleUp_nv hell0 hM μ
  have hAdm : Admissible 2 M R 2 (SlabNv 2 M R) := slab3_admissible G hN
  have hcov : CoversOm0p 2 M 12 2 (SlabNv 2 M R) :=
    slab3_coversp G w0L w0R w1 w2 hQN hP12 hQ21 hQ10 hN
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR18
  have hroom : 17 * 2 ≤ R * M := by nlinarith
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_corner_Ginv (ell := 2) (M := M) (R := R)
    (k := 2) (Lu := nvLu M R) hell0 (S := SlabNv 2 M R) 1 (LamN M R)
    hAdm hell hroom hbd (by norm_num) (by norm_num)
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
  have hcls : ClassCoupledFour 2 M 12 2 (SlabNv 2 M R) α₀ ((2 : ℝ) ^ 2)⁻¹
      (Uth ((SlabNv 2 M R).Om 0) θ) :=
    ⟨hcov.1, slabNv_coversFour hcov,
      Uth_perCubeRegularTouch _ hAdm.1 hα0 hM (by norm_num) hell0 (by positivity) θ⟩
  have hineq := hcore 2 (by norm_num) (nvLu M R) α₀ hα0 (by simpa using hαS)
    (torusOK_nv hell hdvd hM) (SlabNv 2 M R) hAdm (LamN M R)
    (lambdaOK2_nv hell hdvd hM (show 1 ≤ R by omega)) (Uth ((SlabNv 2 M R).Om 0) θ) hcls
  obtain ⟨hB1, hB2, hB3, hB4⟩ := BseedNv_props (R := R) hell hdvd hM
  exact not_InstIneqS_of_not_unit selCorner selCorner 2 2 hell0 1 zero_le_one (nvLu M R)
    γ₀ hγ (SlabNv 2 M R) (LamN M R) (Uth ((SlabNv 2 M R).Om 0) θ) hnu
    _ hB1 hB2 hB3 hineq


-- Direct frozen proof helpers; the main print also checks their full cones.

end Round3.S1Proper

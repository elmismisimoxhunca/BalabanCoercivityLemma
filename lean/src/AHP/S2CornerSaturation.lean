import ZT5A
import ZR8Class

/-! Round 2 S-2 corner saturation. Pinned declarations below are verbatim.
Product-box helpers copied verbatim from Stage B; connectivity helpers
from frozen CvN4.lean:36-61. New proofs follow the numerical exit square. -/

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

/-! ## The four pinned goals -/

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


/-! ## Verbatim product-box helpers from Stage B -/

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


open Fin.NatCast

/-! ## 1. connectivity of the torus -/

theorem shift_iter (P : PeriodicLatticeSite L → Prop) (h : ∀ x μ, P x → P (periodicLatticeShift x μ))
    (x : PeriodicLatticeSite L) (μ : Fin 3) (hx : P x) :
    ∀ n : ℕ, P (Function.update x μ (x μ + (n : Fin (L μ + 1)))) := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have h1 := h _ μ ih
      unfold periodicLatticeShift at h1
      simp only [Function.update_self, Function.update_idem] at h1
      rw [Nat.cast_succ, ← add_assoc]
      exact h1

theorem forall_of_shift (P : PeriodicLatticeSite L → Prop) (h : ∀ x μ, P x → P (periodicLatticeShift x μ))
    {x0 : PeriodicLatticeSite L} (h0 : P x0) (y : PeriodicLatticeSite L) : P y := by
  have step : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3) (c : Fin (L μ + 1)), P x → P (Function.update x μ c) := by
    intro x μ c hx
    have := shift_iter P h x μ hx (c - x μ).val
    rwa [Fin.cast_val_eq_self, add_sub_cancel] at this
  have e : y = Function.update (Function.update (Function.update x0 0 (y 0)) 1 (y 1)) 2 (y 2) := by
    funext μ
    fin_cases μ <;> simp
  rw [e]
  exact step _ _ _ (step _ _ _ (step _ _ _ h0))


/-- A frozen class cube cannot leave the base domain of an admissible tower. -/
theorem class_sites_subset_om0 {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hc : IsClassCube ell M c k S sites j) : sites ⊆ S.Om 0 := by
  intro x hx
  rcases hc.1.2.2.1 hx with h | h
  · exact AdalyFormal.StatementLaneR8.admissible_mono hS j h.1
  · exact AdalyFormal.StatementLaneR8.admissible_mono hS (j + 1) h.1

/-- Touching every edge by one frozen cube forces all four corners into Om0. -/
theorem covered_corners_in_om0 {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) {p : PeriodicLatticePlaquette L}
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hc : IsClassCube ell M c k S sites j)
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    cornerA p ∈ S.Om 0 ∧ cornerB p ∈ S.Om 0 ∧
      cornerC p ∈ S.Om 0 ∧ cornerD p ∈ S.Om 0 := by
  obtain ⟨z, _, heq⟩ := hc.1.2.1
  have hbox : ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      TouchBond (siteBox z (c * bigSide M ell j)) e := fun e he => heq ▸ ht e he
  have hall := touchCover_all_corners hbox
  have hsub : siteBox z (c * bigSide M ell j) ⊆ S.Om 0 :=
    heq ▸ class_sites_subset_om0 hS hc
  exact ⟨hsub hall.1, hsub hall.2.1, hsub hall.2.2.1, hsub hall.2.2.2⟩

/-- Corner coverage propagates membership across every forward bond. -/
theorem corner_coverage_shift_closed {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hcov : CoversPlaqCorner ell M c k S)
    (x : PeriodicLatticeSite L) (μ : Fin 3) (hx : x ∈ S.Om 0) :
    periodicLatticeShift x μ ∈ S.Om 0 := by
  have h01 := hcov (x, ⟨(0, 1), by decide⟩) (Or.inl hx)
  have h02 := hcov (x, ⟨(0, 2), by decide⟩) (Or.inl hx)
  obtain ⟨q01, j01, hc01, ht01⟩ := h01
  obtain ⟨q02, j02, hc02, ht02⟩ := h02
  have all01 := covered_corners_in_om0 hS hc01 ht01
  have all02 := covered_corners_in_om0 hS hc02 ht02
  fin_cases μ
  · exact all01.2.1
  · exact all01.2.2.1
  · exact all02.2.2.1

/-- Any proper nonempty set has an exit bond, by finite-torus connectivity. -/
theorem exists_exit {Ω : Set (PeriodicLatticeSite L)}
    {x y : PeriodicLatticeSite L} (hx : x ∈ Ω) (hy : y ∉ Ω) :
    ∃ z μ, z ∈ Ω ∧ periodicLatticeShift z μ ∉ Ω := by
  classical
  by_contra h
  have hclosed : ∀ z μ, z ∈ Ω → periodicLatticeShift z μ ∈ Ω := by
    intro z μ hz
    by_contra hout
    exact h ⟨z, μ, hz, hout⟩
  exact hy (forall_of_shift (fun z => z ∈ Ω) hclosed hx y)

/-- The counterexample to coverage is explicit: the (0,1) square at x for
exit directions 0 and 1, and the (0,2) square at x for exit direction 2.
Each is based at the inside endpoint of the supplied exit bond. -/
theorem explicit_exit_square {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) {x : PeriodicLatticeSite L} {μ : Fin 3}
    (hx : x ∈ S.Om 0) (hout : periodicLatticeShift x μ ∉ S.Om 0) :
    ∃ p : PeriodicLatticePlaquette L, p.1 = x ∧ p ∈ plaqCorner (S.Om 0) ∧
      ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
        IsClassCube ell M c k S sites j →
        ¬ (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) := by
  fin_cases μ
  · refine ⟨(x, ⟨(0, 1), by decide⟩), rfl, Or.inl hx, ?_⟩
    intro sites j hc ht
    exact hout (covered_corners_in_om0 hS hc ht).2.1
  · refine ⟨(x, ⟨(0, 1), by decide⟩), rfl, Or.inl hx, ?_⟩
    intro sites j hc ht
    exact hout (covered_corners_in_om0 hS hc ht).2.2.1
  · refine ⟨(x, ⟨(0, 2), by decide⟩), rfl, Or.inl hx, ?_⟩
    intro sites j hc ht
    exact hout (covered_corners_in_om0 hS hc ht).2.2.1

/-- Every proper nonempty admissible tower supplies a concrete plaquette
violating the one-cube corner coverage conclusion, independently of U. -/
theorem proper_domain_uncovered {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hne : (S.Om 0).Nonempty)
    (hproper : S.Om 0 ≠ Set.univ) :
    ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) ∧
      ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
        IsClassCube ell M c k S sites j →
        ¬ (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) := by
  obtain ⟨x, hx⟩ := hne
  have hex : ∃ y, y ∉ S.Om 0 := by
    classical
    by_contra! h
    exact hproper (Set.eq_univ_of_forall h)
  obtain ⟨y, hy⟩ := hex
  obtain ⟨z, μ, hz, hout⟩ := exists_exit hx hy
  obtain ⟨p, _, hp, hbad⟩ := explicit_exit_square (c := c) hS hz hout
  exact ⟨p, hp, hbad⟩

/-- This stronger geometry theorem does not need TorusOK, M>=2, or regularity. -/
theorem corner_saturation {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hcov : CoversPlaqCorner ell M c k S) :
    S.Om 0 = ∅ ∨ S.Om 0 = Set.univ := by
  classical
  by_cases hne : (S.Om 0).Nonempty
  · by_cases hfull : S.Om 0 = Set.univ
    · exact Or.inr hfull
    · obtain ⟨p, hp, hbad⟩ := proper_domain_uncovered (c := c) hS hne hfull
      obtain ⟨sites, j, hc, ht⟩ := hcov p hp
      exact (hbad sites j hc ht).elim
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- The exact negative corner goal, with all pinned binders unchanged. -/
theorem goalNeg2_proved : GoalNeg2 := by
  intro ell m R k _ _ _ Lu _ S hS α₀ _ U hclass
  exact corner_saturation hS hclass.2.1

/-- The positive corner-family pin is therefore impossible. -/
theorem not_goalPos2 : ¬ GoalPos2 :=
  goalNeg2_implies_not_goalPos2 goalNeg2_proved





end AdalyFormal.AHP.Round2.S2Nonvacuity

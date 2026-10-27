import ZStatementP428
import ZR2A
import ZR6A
import ZR2Ops2
import D1Lit
import ZR8Class
import RI6
import AdalyFormal.Balaban.U1AnchorPoincare

/-!
Round 2 S-1 positive attempt. All definitions and goal statements below are
copied verbatim from ../pin/Statement.lean. Proofs of GoalPos1 and GoalPos2
follow the copied pin. Only frozen source modules are imported.
See ../pin/PIN.md and NOTES.md for the material common-cube-coverage disclosure.
-/

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

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Round2.S1

-- Verbatim definitions from Fidelity.S1's compiled ShellComparison.lean.
def TouchBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

def plaqCorner {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L)) :
    Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.2 ∈ S
    ∨ periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

variable {L : PeriodicLatticeExtent}

-- Verbatim definitions from FidelS2Inclusion's compiled ClassInclusion.lean.
-- The antecedent is ONE CORNER, not all four bonds touching Omega_0.
-- The common-cube conclusion is an added coverage hypothesis, not printed text.
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

def ClassCoupledCorner (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

-- Verbatim selector from s1-touching/SPEC.md. Not selAll and not selIn.
def selCorner : PlaqSel := fun _ G => plaqCorner G.Om0

/-- Primary headline. Same expanded quantifier order as ZT5A.P428Target8.
Only the class and the Delta/J selectors change. The inequality, including
its actual jets, C, inverse convention, eta and tau, is D1Lit.InstIneqS. -/
def P428TouchConsistent : Prop :=
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
            ClassCoupledCorner ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U

/-- Original positive/negative question; neither is proved in this pin. -/
def GoalPos1 : Prop := P428TouchConsistent

def GoalNeg1 : Prop := ¬ GoalPos1

/-- Only the base domain is extreme; higher levels are not required to be constant. -/
def ExtremeBase (S : Tower L) : Prop := S.Om 0 = ∅ ∨ S.Om 0 = Set.univ

/-- Frozen headline restricted to extreme base domains. This keeps the FROZEN
class and InstIneq, not the touching class with a renamed conclusion. -/
def P428Target8Extreme : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ExtremeBase S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneq ell k (by omega) a Lu γ₀ S Lam U

/-- The coverage-collapse obligation in the actual headline geometry.
It is a CONCLUSION to prove, not a premise that removes proper towers. -/
def TouchCoverageCollapse : Prop :=
  ∀ (ell m R k : ℕ), 2 ≤ ell → 1 ≤ m → 1 ≤ k →
    ∀ (Lu : PeriodicLatticeExtent), TorusOK ell (ell ^ m) Lu →
    ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
      CoversPlaqCorner ell (ell ^ m) 12 k S → ExtremeBase S

/-- Reduced goal requested if corner coverage collapses. Both collapse and the
changed-operator HEADLINE equivalence are required. This is not the already
proved Stage-B class-inclusion/frozen-operator comparison. -/
def GoalPos2 : Prop :=
  TouchCoverageCollapse ∧ (P428TouchConsistent ↔ P428Target8Extreme)

def GoalNeg2 : Prop := ¬ GoalPos2

-- Weaker analytic fallback: verbatim shell definitions from ShellComparison.lean.
-- These regularity hypotheses are stronger than the printed endpoint convention.
-- Coverage here remains frozen; it is NOT the corner-coverage class above.
def ReadBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner sites ∧ b ∈ periodicPlaquetteBoundaryEdges p

def CurlReadsRead {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  ReadBond sites (periodicLatticeShift x a, b) ∧ ReadBond sites (x, b) ∧
  ReadBond sites (periodicLatticeShift x b, a) ∧ ReadBond sites (x, a)

def PerCubeRegularShell {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, ReadBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        ReadBond sites ((x, ν) : Bond L) → ReadBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReadsRead sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReadsRead sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def ClassCoupledShell {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ PerCubeRegularShell ell M c k S α₀ η U

-- Verbatim headline from AHP/fidelity/s1-touching/SPEC.md.
def P428Target8Shell : Prop :=
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
            ClassCoupledShell ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U

def GoalPos3 : Prop := P428Target8Shell

def GoalNeg3 : Prop := ¬ GoalPos3

-- These commands check well-formed propositions; they do not assert proofs.



/-! Proof section. The square-box helpers below are copied from Stage B S-2.
The two containment helpers are copied from frozen D1Final. -/
set_option maxHeartbeats 4000000

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


theorem om_sub_om0 {L : PeriodicLatticeExtent} (S : Tower L) (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) :
    ∀ i, S.Om i ⊆ S.Om 0
  | 0 => le_rfl
  | (i + 1) => (hS i).trans (om_sub_om0 S hS i)

theorem classCube_sub_om0 {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (h : IsClassCube ell M f k S sites j) : sites ⊆ S.Om 0 := by
  intro x hx
  rcases h.1.2.2.1 hx with h1 | h1
  · exact om_sub_om0 S hS j h1.1
  · exact om_sub_om0 S hS (j + 1) h1.1

/-- A corner-covered plaquette actually lies inside its covering cube. -/
theorem corner_cover_inside {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) {p : PeriodicLatticePlaquette L}
    (hp : p ∈ plaqCorner (S.Om 0)) :
    ∃ sites j, IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e := by
  obtain ⟨sites, j, hc, ht⟩ := h p hp
  obtain ⟨z, _, hsites⟩ := hc.1.2.1
  refine ⟨sites, j, hc, ?_⟩
  have htBox : ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      TouchBond (siteBox z (c * bigSide M ell j)) e := fun e he => hsites ▸ ht e he
  intro e he
  rw [hsites]
  exact touchCover_cubeBond htBox he

/-- Coverage alone already makes the two actual selectors equal on nested towers. -/
theorem corner_eq_inside_of_coverage {ell M c k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    (h : CoversPlaqCorner ell M c k S) : plaqCorner (S.Om 0) = plaqIn (S.Om 0) := by
  ext p
  constructor
  · intro hp
    obtain ⟨sites, j, hc, ht⟩ := corner_cover_inside h hp
    have hs := classCube_sub_om0 hS hc
    intro e he
    exact ⟨hs (ht e he).1, hs (ht e he).2⟩
  · intro hp
    exact Or.inl (hp _ (edgeAB_mem p)).1

theorem CoversPlaqCorner.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqOm0c ell M c k S := by
  intro p hp
  exact corner_cover_inside h (Or.inl (hp _ (edgeAB_mem p)).1)

theorem ClassCoupledCorner.toFrozen {ell M c k : ℕ} {S : Tower L}
    {α₀ η : ℝ} {U : LinkCfg L} (h : ClassCoupledCorner ell M c k S α₀ η U) :
    ClassCoupled ell M c k S α₀ η U :=
  ⟨⟨h.1, h.2.1.toFrozen⟩, h.2.2.toFrozen⟩

open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- Selector equality is propagated through the full selected data, not merely Delta. -/
theorem dataS_congr_at (sD sJ tD tJ : PlaqSel) (P : IngrBParams)
    (hD : sD _ P.G = tD _ P.G) (hJ : sJ _ P.G = tJ _ P.G) :
    dataS sD sJ P = dataS tD tJ P := by
  simp only [dataS, DpiFullS, DeltaS, JfS, hD, hJ]

theorem G1invS_congr_at (sD sJ tD tJ : PlaqSel) (P : IngrBParams)
    (hD : sD _ P.G = tD _ P.G) (hJ : sJ _ P.G = tJ _ P.G) :
    G1invS sD sJ P = G1invS tD tJ P := by
  have hd := dataS_congr_at sD sJ tD tJ P hD hJ
  unfold G1invS
  simp only [hd]

theorem genFormS_congr_at (sD sJ tD tJ : PlaqSel) (P : IngrBParams)
    (hD : sD _ P.G = tD _ P.G) (hJ : sJ _ P.G = tJ _ P.G) (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = GenS.genFormS tD tJ P B := by
  have hd := dataS_congr_at sD sJ tD tJ P hD hJ
  have hg := G1invS_congr_at sD sJ tD tJ P hD hJ
  simp only [GenS.genFormS, GenS.firstTermS, GenS.NmatS, H1inS, hd, hg, JfS, hJ]

theorem instIneq_corner_iff_of_eq (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (heq : plaqCorner (S.Om 0) = plaqIn (S.Om 0)) :
    InstIneqS selCorner selCorner ell k hell a Lu γ₀ S Lam U ↔
      InstIneq ell k hell a Lu γ₀ S Lam U := by
  have hs : selCorner _ (gparams ell k Lu hell S U a Lam).G =
      selIn _ (gparams ell k Lu hell S U a Lam).G := heq
  have hf := genFormS_congr_at selCorner selCorner selIn selIn
    (gparams ell k Lu hell S U a Lam) hs hs
  unfold InstIneqS InstIneq
  simp only [hf, pin_genForm]

/-- All original thresholds and constants are reused, without an extra premise. -/
theorem touchConsistent_of_frozen (h : P428Target8) : P428TouchConsistent := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, hcore⟩ := hR R hRR
  obtain ⟨a₀, ha₀, γ₀, hγ, hAt⟩ := hcore
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hL U hU
  apply (instIneq_corner_iff_of_eq ell k (by omega) a Lu γ₀ S Lam U
    (corner_eq_inside_of_coverage hS.1 hU.2.1)).mpr
  exact hAt k hk Lu α₀ hα hsmall hT S hS Lam hL U hU.toFrozen

/-- Exact primary pinned positive goal. Its coverage repair excludes proper bases. -/
theorem goalPos1_proved : GoalPos1 :=
  touchConsistent_of_frozen AdalyFormal.M2RightInv.p428Target8

/-- Equality of selectors forces endpoint propagation along every lattice edge. -/
theorem cubeBond_of_touch_of_selector_eq (Ω : Set (PeriodicLatticeSite L))
    (heq : plaqCorner Ω = plaqIn Ω) (e : Bond L) (ht : TouchBond Ω e) :
    CubeBond Ω e := by
  rcases e with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst μ
    let p : PeriodicLatticePlaquette L := (x, ⟨(0, 1), by decide⟩)
    have hp : p ∈ plaqCorner Ω := ht.elim Or.inl (fun h => Or.inr (Or.inl h))
    have hi : p ∈ plaqIn Ω := heq ▸ hp
    exact hi (x, 0) (edgeAB_mem p)
  · have hμ0 : (0 : Fin 3) < μ := by omega
    let p : PeriodicLatticePlaquette L := (x, ⟨(0, μ), hμ0⟩)
    have hp : p ∈ plaqCorner Ω := ht.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
    have hi : p ∈ plaqIn Ω := heq ▸ hp
    exact hi (x, μ) (edgeAC_mem p)

theorem shift_mem_iff_of_selector_eq (Ω : Set (PeriodicLatticeSite L))
    (heq : plaqCorner Ω = plaqIn Ω) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift x μ ∈ Ω ↔ x ∈ Ω := by
  constructor
  · intro hx
    exact (cubeBond_of_touch_of_selector_eq Ω heq (x, μ) (Or.inr hx)).1
  · intro hx
    exact (cubeBond_of_touch_of_selector_eq Ω heq (x, μ) (Or.inl hx)).2

/-- Transitivity of the periodic coordinate shifts is a frozen theorem. -/
theorem extreme_of_selector_eq (Ω : Set (PeriodicLatticeSite L))
    (heq : plaqCorner Ω = plaqIn Ω) : Ω = ∅ ∨ Ω = Set.univ := by
  classical
  by_cases hne : Ω.Nonempty
  · right
    obtain ⟨x, hx⟩ := hne
    apply Set.eq_univ_of_forall
    intro y
    let g : PeriodicLatticeSite L → Bool := fun z => decide (z ∈ Ω)
    have hg : ∀ z μ, g (periodicLatticeShift z μ) = g z := by
      intro z μ
      simp only [g, shift_mem_iff_of_selector_eq Ω heq z μ]
    have hxy := AdalyFormal.Balaban.U1AnchorPoincare.eq_of_shiftInvariant g hg x y
    simpa [g, hx] using hxy.symm
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- Stronger than the pin: no size, radius, collar, or arithmetic premise is used. -/
theorem coverage_collapse_nested {ell M c k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    (hc : CoversPlaqCorner ell M c k S) : ExtremeBase S :=
  extreme_of_selector_eq _ (corner_eq_inside_of_coverage hS hc)

/-- The exact pinned collapse obligation in headline geometry. -/
theorem touchCoverageCollapse_proved : TouchCoverageCollapse := by
  intro ell m R k _ _ _ Lu _ S hS hc
  exact coverage_collapse_nested hS.1 hc

theorem corner_eq_inside_of_extreme {S : Tower L} (hE : ExtremeBase S) :
    plaqCorner (S.Om 0) = plaqIn (S.Om 0) := by
  rcases hE with hE | hE
  · ext p
    constructor
    · intro hp
      simp [plaqCorner, hE] at hp
    · intro hp
      have hx := (hp _ (edgeAB_mem p)).1
      rw [hE] at hx
      exact hx.elim
  · ext p
    simp [plaqCorner, plaqIn, hE]

/-- Instance-level identity on extreme bases, without a class or inverse-unit premise. -/
theorem instIneq_corner_iff_extreme (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hE : ExtremeBase S) :
    InstIneqS selCorner selCorner ell k hell a Lu γ₀ S Lam U ↔
      InstIneq ell k hell a Lu γ₀ S Lam U :=
  instIneq_corner_iff_of_eq ell k hell a Lu γ₀ S Lam U (corner_eq_inside_of_extreme hE)

/-- Restriction of the existing frozen headline; the class stays frozen. -/
theorem target8Extreme_of_frozen (h : P428Target8) : P428Target8Extreme := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, hcore⟩ := hR R hRR
  obtain ⟨a₀, ha₀, γ₀, hγ, hAt⟩ := hcore
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS _ Lam hL U hU
  exact hAt k hk Lu α₀ hα hsmall hT S hS Lam hL U hU

/-- The nontrivial direction uses collapse, class inclusion, and actual-form equality. -/
theorem touchConsistent_of_extreme (h : P428Target8Extreme) : P428TouchConsistent := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hAt⟩ := hR R hRR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hL U hU
  have hE : ExtremeBase S := coverage_collapse_nested hS.1 hU.2.1
  apply (instIneq_corner_iff_extreme ell k (by omega) a Lu γ₀ S Lam U hE).mpr
  exact hAt k hk Lu α₀ hα hsmall hT S hS hE Lam hL U hU.toFrozen

/-- Headline equivalence, NOT equality or reverse inclusion of the two classes.
The forward implication uses the already proved frozen headline, as the pin permits. -/
theorem touchConsistent_iff_extreme : P428TouchConsistent ↔ P428Target8Extreme :=
  ⟨fun _ => target8Extreme_of_frozen AdalyFormal.M2RightInv.p428Target8,
    touchConsistent_of_extreme⟩

/-- Exact preferred reduced positive goal: collapse AND the headline equivalence. -/
theorem goalPos2_proved : GoalPos2 :=
  ⟨touchCoverageCollapse_proved, touchConsistent_iff_extreme⟩




end Round2.S1

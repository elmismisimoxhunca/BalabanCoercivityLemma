import ZStatementP428
import ZR2A
import ZR6A
import ZR2Ops2
import D1Lit
import D1Final
import ZR8Class

/-!
Round 2 S-1 refutation attempt; none of the pinned negative goals is proved.
The pinned definitions and goals below are copied verbatim from pin/Statement.lean.
Only frozen source modules are imported. Compiled partial results establish the
coverage obstruction and equality of the full selected form with the frozen one.
See NOTES.md and ../pin/PIN.md for scope and the additional-coverage disclosure.
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
#check P428TouchConsistent
#check TouchCoverageCollapse
#check P428Target8Extreme
#check P428Target8Shell
#check GoalPos1
#check GoalNeg1
#check GoalPos2
#check GoalNeg2
#check GoalPos3
#check GoalNeg3

#print axioms TouchBond
#print axioms plaqCorner
#print axioms CoversPlaqCorner
#print axioms CurlReadsTouch
#print axioms PerCubeRegularTouch
#print axioms ClassCoupledCorner
#print axioms selCorner
#print axioms P428TouchConsistent
#print axioms ExtremeBase
#print axioms P428Target8Extreme
#print axioms TouchCoverageCollapse
#print axioms ReadBond
#print axioms CurlReadsRead
#print axioms PerCubeRegularShell
#print axioms ClassCoupledShell
#print axioms P428Target8Shell
#print axioms GoalPos1
#print axioms GoalNeg1
#print axioms GoalPos2
#print axioms GoalNeg2
#print axioms GoalPos3
#print axioms GoalNeg3

/-! Exact geometric helper copies from Stage B ClassInclusion.lean. -/

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

/-- A selected plaquette cannot read a bond invisible to all touching cubes. -/
theorem cornerCoverage_no_unseen_read_bond
    {ell M c k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    (hcov : CoversPlaqCorner ell M c k S)
    {e : Bond L} (he : ReadBond (S.Om 0) e) : TouchBond (S.Om 0) e := by
  obtain ⟨p, hp, hep⟩ := he
  obtain ⟨sites, j, hc, ht⟩ := hcov p hp
  have hsub := classCube_sub_om0 hS hc
  rcases ht e hep with h | h
  · exact Or.inl (hsub h)
  · exact Or.inr (hsub h)

/-- Product-box coverage makes the selected plaquette fully internal to Omega0.
This is an obstruction to the refutation search, not a negative goal. -/
theorem cornerCoverage_selector_eq
    {ell M c k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    (hcov : CoversPlaqCorner ell M c k S) :
    plaqCorner (S.Om 0) = plaqIn (S.Om 0) := by
  ext p
  constructor
  · intro hp
    obtain ⟨sites, j, hc, ht⟩ := hcov p hp
    obtain ⟨z, _, hsites⟩ := hc.1.2.1
    have htBox : ∀ e ∈ periodicPlaquetteBoundaryEdges p,
        TouchBond (siteBox z (c * bigSide M ell j)) e := fun e he => hsites ▸ ht e he
    have hsub := classCube_sub_om0 hS hc
    intro e he
    have hboth : CubeBond sites e := hsites.symm ▸ touchCover_cubeBond htBox he
    exact ⟨hsub hboth.1, hsub hboth.2⟩
  · intro hp
    exact Or.inl ((hp (p.1, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])).1)

/-- At a fixed genuine ingredient instance, equal selected sets give equal
full forms, including J, the chosen corrected inverse, and the actual jets. -/
theorem genForm_corner_eq_frozen (P : IngrBParams)
    (hsel : plaqCorner P.G.Om0 = plaqIn P.G.Om0)
    (B : AdalyFormal.Balaban.CovariantOperators.BondFnL2 P.Lu) :
    GenS.genFormS selCorner selCorner P B = GenP.genForm P B := by
  rw [← pin_genForm]
  unfold GenS.genFormS GenS.firstTermS GenS.NmatS H1inS G1invS
  simp only [dataS, DpiFullS, DeltaS, JfS, selCorner, selIn, hsel]

/-- Furthest analytic comparison reached by this refutation attempt: the
primary pinned corner form is exactly the frozen form on its covered towers.
This does not assert any pinned positive or negative headline. -/
theorem corner_instIneq_iff_frozen
    (ell M c k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu))
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    (hcov : CoversPlaqCorner ell M c k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) :
    InstIneqS selCorner selCorner ell k hell a Lu γ₀ S Lam U ↔
      InstIneq ell k hell a Lu γ₀ S Lam U := by
  have hsel : plaqCorner (gparams ell k Lu hell S U a Lam).G.Om0 =
      plaqIn (gparams ell k Lu hell S U a Lam).G.Om0 :=
    cornerCoverage_selector_eq hS hcov
  unfold InstIneqS InstIneq
  simp only [genForm_corner_eq_frozen _ hsel]

/-- The familiar slab-boundary configuration is excluded by coverage before
one chooses U, its phases, alpha, or a test field. -/
theorem bdpt_not_cornerCoverage
    {ell M c k : ℕ} {S : Tower L}
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x) :
    ¬ CoversPlaqCorner ell M c k S := by
  intro hcov
  let p : PeriodicLatticePlaquette L := (x, ⟨(0, 1), by decide⟩)
  let e : Bond L := (periodicLatticeShift x 0, 1)
  have hp : p ∈ plaqCorner (S.Om 0) := Or.inl hbd.hx
  have he : e ∈ periodicPlaquetteBoundaryEdges p := by
    simp [e, p, periodicPlaquetteBoundaryEdges]
  have ht := cornerCoverage_no_unseen_read_bond hS hcov ⟨p, hp, he⟩
  rcases ht with h | h
  · exact hbd.hx' h
  · exact hbd.hx' ((hbd.trans _ 1 (by decide)).mp h)

/-- All configurations on the old cofinal slab family fail the primary pinned
class, not just its large-phase representatives. -/
theorem old_slab_family_excluded
    (ell M R : ℕ) (hell : 2 ≤ ell) (hM : 0 < M) (hdvd : ell ∣ M) (hR : 18 ≤ R)
    (α₀ η : ℝ) (U : LinkCfg (scaleUp ell 2 (AdalyFormal.NonVac.nvLu M R))) :
    ¬ ClassCoupledCorner ell M 12 2 (SlabNv ell M R) α₀ η U := by
  intro hcls
  obtain ⟨x, hbd⟩ := SlabNv_bdpt hell hdvd hM hR
  have G := AdalyFormal.NonVac.slabGeo_inst hell hM hdvd (show 1 ≤ R by omega)
  have hN : ∀ μ, scaleUp ell 2 (AdalyFormal.NonVac.nvLu M R) μ + 1 =
      AdalyFormal.NonVac.nvN ell M R :=
    fun μ => AdalyFormal.NonVac.scaleUp_nv (by omega) hM μ
  have hAdm : Admissible ell M R 2 (SlabNv ell M R) :=
    AdalyFormal.NonVac.slab3_admissible G hN
  exact bdpt_not_cornerCoverage hAdm.1 hbd hcls.2.1

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
#print axioms cornerCoverage_no_unseen_read_bond
#print axioms cornerCoverage_selector_eq
#print axioms genForm_corner_eq_frozen
#print axioms corner_instIneq_iff_frozen
#print axioms bdpt_not_cornerCoverage
#print axioms old_slab_family_excluded
#print axioms classCube_sub_om0
#print axioms om_sub_om0
#print axioms SlabNv_bdpt
#print axioms AdalyFormal.NonVac.slabGeo_inst
#print axioms AdalyFormal.NonVac.scaleUp_nv
#print axioms AdalyFormal.NonVac.slab3_admissible
#print axioms pin_genForm
#print axioms AdalyFormal.StatementLaneR8.shift_ne
#print axioms AdalyFormal.StatementLaneR8.shift_comm

end Round2.S1

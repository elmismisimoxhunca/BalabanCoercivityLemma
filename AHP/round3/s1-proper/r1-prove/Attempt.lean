import D1Lit
import GdR5a
import ZR8Class

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


/-! Class transfer: verbatim helpers from the compiled Stage-B S-2 file. -/
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
  ⟨⟨h.1, h.2.1.toFrozen⟩, h.2.2.toFrozen⟩


/-! The full form already agrees for every selector containing plaqIn, once
its three inverse guards hold. No positivity comparison of raw Delta is needed
for this fact. The unsolved issue here is obtaining the guards on the four-bond
class, not a new inequality under those guards. -/
open scoped RealInnerProductSpace
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

set_option maxHeartbeats 4000000

theorem plaqIn_subset_corner (sites : Set (PeriodicLatticeSite L)) :
    plaqIn sites ⊆ plaqCorner sites := by
  intro p hp
  exact Or.inl (hp _ (edgeAB_mem p)).1

theorem selCorner_contains_inside (L : PeriodicLatticeExtent) (G : TowerGeom L) :
    plaqIn G.Om0 ⊆ selCorner L G := plaqIn_subset_corner G.Om0

/-- Genuine full-form equality, with both sides' actual inverse guards.
No flatness, class membership, or test-field constraint is assumed. -/
theorem corner_form_eq_frozen (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (hroom : 17 * P.ell ≤ R * M) (hk : 1 ≤ P.k)
    (hc : WellDefAt selCorner selCorner P) (hi : WellDefAt selIn selIn P)
    (B : BondFnL2 P.Lu) :
    GenS.genFormS selCorner selCorner P B = GenP.genForm P B := by
  exact (genFormS_eq_loc P hS hell hroom hk selCorner selCorner selIn selIn
    selCorner_contains_inside (fun _ _ => subset_rfl)
    selCorner_contains_inside (fun _ _ => subset_rfl) hc hi B).trans (pin_genForm P B)

/-- An actual positive-energy instance forces all three selected inverse guards,
not just the carrier guard. This uses the totalized full form's collapse. -/
theorem wellDefAt_of_corner_ineq {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) {a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu))
    (htest : ∃ Bt : Bond Lu → SuTwo,
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt)
    (hi : InstIneqS selCorner selCorner ell k hell a Lu γ S Lam U) :
    WellDefAt selCorner selCorner (gparams ell k Lu hell S U a Lam) := by
  by_contra hn
  obtain ⟨Bt, h1, h2, hE⟩ := htest
  exact not_InstIneqS_of_collapse selCorner selCorner ell k hell a ha Lu γ hγ
    S Lam U (genFormS_collapse_of_not_wd selCorner selCorner
      (gparams ell k Lu hell S U a Lam) hn) Bt h1 h2 hE hi

/-- Pointwise sufficiency of the two operator units, from the frozen inequality.
The unit of Nmat is derived by the frozen transfer theorem, not postulated. -/
theorem corner_ineq_of_two_units {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) {a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hloc : InstIneq ell k hell a Lu γ S Lam U)
    (hunits : (∃ Bt : Bond Lu → SuTwo,
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
      IsUnit (dataS selCorner selCorner (gparams ell k Lu hell S U a Lam)).Ginv ∧
      IsUnit (G1invS selCorner selCorner (gparams ell k Lu hell S U a Lam))) :
    InstIneqS selCorner selCorner ell k hell a Lu γ S Lam U := by
  by_cases hex : ∃ Bt : Bond Lu → SuTwo,
      OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt
  · obtain ⟨hu, hc⟩ := hunits hex
    obtain ⟨Bt, h1, h2, hE⟩ := hex
    have hWD := WellDefAt_loc_of_inst ell k hell a ha Lu γ hγ S Lam U Bt h1 h2 hE hloc
    exact InstIneqSG_general selCorner selCorner hell hS hk hroom ha hγ Lam U
      selCorner_contains_inside selCorner_contains_inside hloc hWD (fun _ => hc) hu
  · exact InstIneqS_of_no_testfield selCorner selCorner hell Lam U hex

/-- Exact instance reduction under the known frozen inequality. -/
theorem corner_ineq_iff_two_units {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) {a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    (hk : 1 ≤ k) (hroom : 17 * ell ≤ R * M)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hloc : InstIneq ell k hell a Lu γ S Lam U) :
    InstIneqS selCorner selCorner ell k hell a Lu γ S Lam U ↔
      ((∃ Bt : Bond Lu → SuTwo,
        OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
      IsUnit (dataS selCorner selCorner (gparams ell k Lu hell S U a Lam)).Ginv ∧
      IsUnit (G1invS selCorner selCorner (gparams ell k Lu hell S U a Lam))) := by
  constructor
  · intro hi ht
    have h := wellDefAt_of_corner_ineq hell ha hγ S Lam U ht hi
    exact ⟨h.1, h.2.1⟩
  · exact corner_ineq_of_two_units hell ha hγ hS hk hroom Lam U hloc

/-- Remaining unconditional unit problem, with the pin's exact class, scales,
smallness cap and threshold order. This is a new residual, NOT a replacement
positive goal and NOT the Ginv-guarded all-plaquette residual. -/
def TouchFourUnits : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ a₀ : ℝ, 0 < a₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            (∃ Bt : Bond Lu → SuTwo,
              OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
            IsUnit (dataS selCorner selCorner (gparams ell k Lu (by omega) S U a Lam)).Ginv ∧
            IsUnit (G1invS selCorner selCorner (gparams ell k Lu (by omega) S U a Lam))

/-- The actual pinned headline implies the residual, with unchanged thresholds. -/
theorem twoUnits_of_goalPos1 (h : GoalPos1) : TouchFourUnits := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨_, a₀, ha₀, γ, hγ, hcore⟩ := hR R hRR
  refine ⟨a₀, ha₀, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hL U hU ht
  have hi := hcore k hk Lu α₀ hα hsmall hT S hS Lam hL U hU
  have hWD := wellDefAt_of_corner_ineq (by omega) ha.le hγ S Lam U ht hi
  exact ⟨hWD.1, hWD.2.1⟩

/-- Frozen proof reuse: take maxima of its thresholds and the unit thresholds,
and the minimum of their positive caps. No new class/geometry assumption. -/
theorem goalPos1_of_twoUnits (h : TouchFourUnits) : GoalPos1 := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, hunit⟩ := h ell hell a ha
  obtain ⟨m₂, hm₂, hfr⟩ := AdalyFormal.M2RightInv.p428Target8 ell hell a ha
  refine ⟨max m₁ m₂, le_trans hm₁ (le_max_left _ _), fun m hm => ?_⟩
  obtain ⟨R₁, huR⟩ := hunit m (le_trans (le_max_left _ _) hm)
  obtain ⟨R₂, hfR⟩ := hfr m (le_trans (le_max_right _ _) hm)
  refine ⟨max (max R₁ R₂) 18, fun R hR => ?_⟩
  have hRa : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRb : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR18 : 18 ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a₁, ha₁, hunitAt⟩ := huR R hRa
  obtain ⟨hside, a₂, ha₂, γ, hγ, hcore⟩ := hfR R hRb
  refine ⟨hside, min a₁ a₂, lt_min ha₁ ha₂, γ, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hS Lam hL U hU
  have hell0 : 0 < ell := by omega
  have hm1 : 1 ≤ m := le_trans hm₁ (le_trans (le_max_left _ _) hm)
  have hroom : 17 * ell ≤ R * ell ^ m := by
    have h1 : ell ≤ ell ^ m := by
      calc ell = ell ^ 1 := (pow_one ell).symm
        _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm1
    calc 17 * ell ≤ 18 * ell ^ m := by omega
      _ ≤ R * ell ^ m := Nat.mul_le_mul_right _ hR18
  have hsmall₁ := hsmall.trans (min_le_left a₁ a₂)
  have hsmall₂ := hsmall.trans (min_le_right a₁ a₂)
  have hloc := hcore k hk Lu α₀ hα hsmall₂ hT S hS Lam hL U hU.toFrozen
  exact corner_ineq_of_two_units hell0 ha.le hγ hS hk hroom Lam U hloc
    (hunitAt k hk Lu α₀ hα hsmall₁ hT S hS Lam hL U hU)

/-- Furthest headline reduction. Neither side of this equivalence is proved here. -/
theorem goalPos1_iff_twoUnits : GoalPos1 ↔ TouchFourUnits :=
  ⟨twoUnits_of_goalPos1, goalPos1_of_twoUnits⟩

/-! Testing the suggested carrier-positivity route. The corner selector does
not repair the all-plaquette carrier on its actual support: they are equal. -/

theorem corner_of_touch_boundary {sites : Set (PeriodicLatticeSite L)}
    {p : PeriodicLatticePlaquette L} {e : Bond L}
    (he : e ∈ periodicPlaquetteBoundaryEdges p) (ht : TouchBond sites e) :
    p ∈ plaqCorner sites := by
  rcases boundary_is_square he with ⟨hb, hd⟩ | ⟨hb, hd⟩ | ⟨hb, hd⟩ | ⟨hb, hd⟩
  · rcases ht with h | h
    · rw [hb] at h
      exact Or.inl h
    · rw [hd] at h
      exact Or.inr (Or.inl h)
  · rcases ht with h | h
    · rw [hb] at h
      exact Or.inr (Or.inl h)
    · rw [hd] at h
      exact Or.inr (Or.inr (Or.inr h))
  · rcases ht with h | h
    · rw [hb] at h
      exact Or.inr (Or.inr (Or.inl h))
    · rw [hd] at h
      exact Or.inr (Or.inr (Or.inr h))
  · rcases ht with h | h
    · rw [hb] at h
      exact Or.inl h
    · rw [hd] at h
      exact Or.inr (Or.inr (Or.inl h))

/-- Equality on all touching-supported fields, at arbitrary backgrounds.
This is not equality with the inside selector. -/
theorem Delta_corner_eq_all_on_support (G : TowerGeom L) (U : Cfg L)
    (X : BondFnL2 L) (hX : X ∈ bondSupp G) :
    DeltaS selCorner G U X = DeltaS selAll G U X := by
  apply deltaK_set_congr
  intro p hp e he
  apply hX e
  intro ht
  have hc : p ∈ plaqCorner G.Om0 := corner_of_touch_boundary he ht
  exact hp ⟨fun _ => Set.mem_univ _, fun _ => hc⟩

/-- The genuine W sandwich sees no difference between corner and all plaquettes.
W preserves touching support even with its totalized site inverse. -/
theorem Dpi_corner_eq_all (P : IngrBParams) :
    (dataS selCorner selCorner P).Dpi = (dataS selAll selCorner P).Dpi := by
  ext1 x
  change pE P.G (ContinuousLinearMap.adjoint (Wop P.G P.U P.a)
      (DeltaS selCorner P.G P.U (Wop P.G P.U P.a (iE P.G x)))) =
    pE P.G (ContinuousLinearMap.adjoint (Wop P.G P.U P.a)
      (DeltaS selAll P.G P.U (Wop P.G P.U P.a (iE P.G x))))
  rw [Delta_corner_eq_all_on_support P.G P.U _
    (Wop_mem_bondSupp P.G P.U P.a (iE P.G x) x.2)]

/-- Exact carrier equality at EVERY background, without class or inverse guards.
The J selector does not occur in the carrier. -/
theorem corner_Ginv_eq_all (P : IngrBParams) (sJ : PlaqSel) :
    (dataS selCorner selCorner P).Ginv = (dataS selAll sJ P).Ginv := by
  change (dataS selCorner selCorner P).Dpi +
      (ContinuousLinearMap.adjoint (dataS selCorner selCorner P).T).comp
        (dataS selCorner selCorner P).T + (dataS selCorner selCorner P).Mass =
    (dataS selAll sJ P).Dpi +
      (ContinuousLinearMap.adjoint (dataS selAll sJ P).T).comp
        (dataS selAll sJ P).T + (dataS selAll sJ P).Mass
  rw [Dpi_corner_eq_all]
  rfl

/-- On the frozen exterior path and slab boundary, the corner carrier really
has a non-unit point. This does not itself supply four-bond coverage or Lambda,
and is not presented as a proof of a pinned negative goal. -/
theorem exists_nonunit_corner_carrier {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hS : Admissible ell M R k S)
    (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ¬ IsUnit (dataS selCorner selCorner
        (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)).Ginv := by
  obtain ⟨θ, h0, hπ, hnon⟩ := exists_nonunit_Ginv selCorner hell0 a Lam
    hS hell hroom hbd ha ha4
  refine ⟨θ, h0, hπ, ?_⟩
  rwa [corner_Ginv_eq_all _ selCorner]

/-- All three touching regularity bounds hold at every positive cap when the
background is identity on touching bonds. Far bonds remain completely free. -/
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
    · have h1 : U e = 1 := hU e (he.elim (fun h => Or.inl (hsub h))
        (fun h => Or.inr (hsub h)))
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

/-- The all-plaquette exterior path also satisfies TOUCHING regularity at
arbitrarily small alpha. No pi/4 cap on its exterior phase follows from it. -/
theorem perCubeRegularTouch_Uth {ell M f k : ℕ} (S : Tower L)
    (hS : ∀ j, S.Om (j + 1) ⊆ S.Om j) {α₀ η : ℝ}
    (hα : 0 < α₀) (hM : 0 < M) (hf : 0 < f) (hell : 0 < ell) (hη : 0 < η)
    (θ : ℝ) : PerCubeRegularTouch ell M f k S α₀ η (Uth (S.Om 0) θ) := by
  apply perCubeRegularTouch_of_one_on_touch S hS hα hM hf hell hη
  intro e he
  have hz : e ∉ Zb (S.Om 0) := fun h => he.elim h.1 h.2
  simp [Uth, hz]

#print axioms corner_of_touch_boundary
#print axioms Delta_corner_eq_all_on_support
#print axioms Dpi_corner_eq_all
#print axioms corner_Ginv_eq_all
#print axioms exists_nonunit_corner_carrier
#print axioms perCubeRegularTouch_of_one_on_touch
#print axioms perCubeRegularTouch_Uth
#print axioms AdalyFormal.D1Guarded.deltaK_set_congr
#print axioms AdalyFormal.D1Literal.Wop_mem_bondSupp
#print axioms AdalyFormal.D1Literal.exists_nonunit_Ginv
#print axioms AdalyFormal.D1Literal.classCube_sub_om0
#print axioms AdalyFormal.D1Literal.frobNorm_zero'
#print axioms AdalyFormal.D1Literal.Uth
#print axioms AdalyFormal.D1Literal.Zb

#print axioms plaqIn_subset_corner
#print axioms selCorner_contains_inside
#print axioms corner_form_eq_frozen
#print axioms wellDefAt_of_corner_ineq
#print axioms corner_ineq_of_two_units
#print axioms corner_ineq_iff_two_units
#print axioms TouchFourUnits
#print axioms twoUnits_of_goalPos1
#print axioms goalPos1_of_twoUnits
#print axioms goalPos1_iff_twoUnits

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

#print axioms AdalyFormal.StatementLaneR8.shift_ne
#print axioms AdalyFormal.StatementLaneR8.shift_comm
#print axioms AdalyFormal.M2RightInv.p428Target8
#print axioms AdalyFormal.D1Literal.pin_genForm
#print axioms AdalyFormal.D1Guarded.genFormS_eq_loc
#print axioms AdalyFormal.D1Guarded.not_InstIneqS_of_collapse
#print axioms AdalyFormal.D1Guarded.genFormS_collapse_of_not_wd
#print axioms AdalyFormal.D1Guarded.WellDefAt_loc_of_inst
#print axioms AdalyFormal.D1Guarded.InstIneqSG_general
#print axioms AdalyFormal.D1Guarded.InstIneqS_of_no_testfield

end Round3.S1Proper

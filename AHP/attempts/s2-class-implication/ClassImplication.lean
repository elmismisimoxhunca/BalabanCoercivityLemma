import ZT5A
import ZR2Ops2
import ZR8Class

/-!
# S-2 — frozen class contains the touching-convention class (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`
or `extern`. Frozen modules are not edited.

`CubeBond` (ZStatementP428) is both endpoints. The touching reading used here is one
endpoint (`TouchBond`).

`ClassCoupled` is `CoversOm0p ∧ PerCubeRegular2` (ZR6A).
* `CoversOm0c` quantifies sites. It does not use `CubeBond`.
* `CoversPlaqOm0c` uses `CubeBond` twice: the antecedent is `plaqIn` (all four boundary
  bonds have both endpoints in `Ω₀`), and the consequent asks for `CubeBond` of one
  class cube. Replacing both occurrences by `TouchBond` is `CoversPlaqTouch`.
  The antecedent gets larger and the consequent gets weaker, so this is not a
  rewrite. The consequent is restored because a class cube is a `siteBox`: a
  touch-cover of a unit square by a product set contains the square.
* `PerCubeRegular2` uses `CubeBond` only as a hypothesis of the bounds. Widening it
  to `TouchBond` strengthens the hypothesis. `PerCubeRegularTouch → PerCubeRegular2`
  is that weakening, with no geometry.

`ClassCoupledTouch` is the literal substitution of `TouchBond` for every `CubeBond`
in `ClassCoupled`. `ClassCoupledCorner` is the stronger CMP reading whose plaquette
clause is one corner in `Ω₀` (`CoversPlaqCorner`), not merely four touching bonds.
Both imply `ClassCoupled`. The converse is not claimed.

`P428Target8Touch` / `P428Target8Corner` are `P428Target8` with only that class
hypothesis replaced. The conclusion stays `InstIneq`, whose `Δ` and `J` still sum
over `plaqIn`. This file does not identify those operators with a one-corner sum,
and it does not discuss `not_P428Target8Literal`. `Λ` stays the frozen touching
reading (`OnLambdaT`, `CRowIn`, `OnLambdaTildeIn`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.AHP.S2Class

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

variable {L : PeriodicLatticeExtent}

/-! ## Touching bonds -/

/-- At least one endpoint in `sites`. -/
def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

theorem CubeBond.toTouch {sites : Set (PeriodicLatticeSite L)} {b : Bond L}
    (h : CubeBond sites b) : TouchBond sites b :=
  Or.inl h.1

/-! ## Unit-square corners. A `siteBox` that touch-covers the square contains it. -/

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

theorem boundary_is_square {p : PeriodicLatticePlaquette L} {e : Bond L}
    (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (e.1 = cornerA p ∧ periodicLatticeShift e.1 e.2 = cornerB p) ∨
    (e.1 = cornerB p ∧ periodicLatticeShift e.1 e.2 = cornerD p) ∨
    (e.1 = cornerC p ∧ periodicLatticeShift e.1 e.2 = cornerD p) ∨
    (e.1 = cornerA p ∧ periodicLatticeShift e.1 e.2 = cornerC p) := by
  simp only [periodicPlaquetteBoundaryEdges, cornerA, cornerB, cornerC, cornerD,
    Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, cornerD_comm p⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem square_edges_touch {sites : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    (cornerA p ∈ sites ∨ cornerB p ∈ sites) ∧
    (cornerB p ∈ sites ∨ cornerD p ∈ sites) ∧
    (cornerC p ∈ sites ∨ cornerD p ∈ sites) ∧
    (cornerA p ∈ sites ∨ cornerC p ∈ sites) := by
  have eAB : (cornerA p, p.2.1.1) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, cornerA]
  have eBD : (cornerB p, p.2.1.2) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, cornerB]
  have eCD : (cornerC p, p.2.1.1) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, cornerC]
  have eAC : (cornerA p, p.2.1.2) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges, cornerA]
  have hAB : periodicLatticeShift (cornerA p) p.2.1.1 = cornerB p := rfl
  have hBD : periodicLatticeShift (cornerB p) p.2.1.2 = cornerD p := rfl
  have hAC : periodicLatticeShift (cornerA p) p.2.1.2 = cornerC p := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ht _ eAB
    rwa [TouchBond, hAB] at h
  · have h := ht _ eBD
    rwa [TouchBond, hBD] at h
  · have h := ht _ eCD
    rwa [TouchBond, cornerD_comm p] at h
  · have h := ht _ eAC
    rwa [TouchBond, hAC] at h

/-- Diagonal `A,D` in a product box forces the other two corners in. Off-axis coordinates
agree, and `siteBox` membership is a product of coordinate arcs (including arcs that wrap). -/
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

/-- A vertex cover of the 4-cycle contains an opposite pair. `push_neg` is not used:
`¬(P ∧ Q)` stays an implication under that tactic. -/
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

/-- Coverage consequent, upgraded. Touch-covering the four bonds of `p` by a `siteBox`
gives `CubeBond` on each of those bonds. -/
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

/-! ## Coverage. `CubeBond` sits in both positions of `CoversPlaqOm0c`. -/

theorem cubeAnte_iff_plaqIn (S : Set (PeriodicLatticeSite L)) (p : PeriodicLatticePlaquette L) :
    (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond S e) ↔ p ∈ plaqIn S := by
  constructor
  · intro h
    simpa [plaqIn, CubeBond] using h
  · intro h
    simpa [plaqIn, CubeBond] using h

/-- `CoversPlaqOm0c` with both `CubeBond` occurrences replaced by `TouchBond`.
The antecedent is every plaquette whose four bonds meet `Ω₀`, not `plaqIn`. -/
def CoversPlaqTouch (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

theorem touchAnte_of_cubeAnte {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond S e) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond S e :=
  fun e he => (hp e he).toTouch

/-- `CoversPlaqTouch → CoversPlaqOm0c`. A frozen antecedent plaquette is a touching
antecedent plaquette. The witness cube is a `siteBox` (`DescribedAt`), so
`touchCover_cubeBond` turns the touching witness into `CubeBond`. -/
theorem CoversPlaqTouch.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqTouch ell M c k S) : CoversPlaqOm0c ell M c k S := by
  intro p hp
  obtain ⟨sites, j, hc, ht⟩ := h p (touchAnte_of_cubeAnte hp)
  rcases hc.1.2.1 with ⟨z, _, rfl⟩
  refine ⟨siteBox z (c * bigSide M ell j), j, hc, ?_⟩
  intro e he
  exact touchCover_cubeBond ht he

/-- One corner in `S`: base, or either neighbour, or the opposite corner. -/
def plaqCorner (S : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S ∨
      periodicLatticeShift p.1 p.2.1.2 ∈ S ∨
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

theorem plaqCorner_of_allTouch {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond S e) : p ∈ plaqCorner S := by
  have eAB : (p.1, p.2.1.1) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges]
  rcases ht _ eAB with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

/-- Every one-corner plaquette of `Ω₀` has all four bonds touching one class cube.
This is stronger than `CoversPlaqTouch`: a one-corner plaquette need not have all
four bonds meeting `Ω₀`. -/
def CoversPlaqCorner (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

theorem CoversPlaqCorner.toTouch {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqTouch ell M c k S := by
  intro p hp
  obtain ⟨sites, j, hc, ht⟩ := h p (plaqCorner_of_allTouch hp)
  exact ⟨sites, j, hc, ht⟩

theorem CoversPlaqCorner.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqOm0c ell M c k S :=
  h.toTouch.toFrozen

/-! ## Regularity. `CubeBond` is only a bound hypothesis, so touching is stronger. -/

def CurlReadsTouch (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  TouchBond sites (periodicLatticeShift x a, b) ∧ TouchBond sites (x, b) ∧
  TouchBond sites (periodicLatticeShift x b, a) ∧ TouchBond sites (x, a)

theorem CurlReads.toTouch {sites : Set (PeriodicLatticeSite L)}
    {x : PeriodicLatticeSite L} {a b : Fin 3}
    (h : CurlReads sites x a b) : CurlReadsTouch sites x a b :=
  ⟨h.1.toTouch, h.2.1.toTouch, h.2.2.1.toTouch, h.2.2.2.toTouch⟩

/-- `(3.35)+(3.36)` with `TouchBond` in place of `CubeBond`. Same quantifier order as
`PerCubeRegular2`. -/
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

theorem PerCubeRegularTouch.toFrozen {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegularTouch ell M f k S α₀ η U) : PerCubeRegular2 ell M f k S α₀ η U := by
  intro sites j hq
  obtain ⟨g, A, hA, hD, hLap⟩ := h sites j hq
  refine ⟨g, A, ?_, ?_, ?_⟩
  · intro e he
    exact hA e he.toTouch
  · intro μ ν x h1 h2
    exact hD μ ν x h1.toTouch h2.toTouch
  · intro μ x hreads
    exact hLap μ x (fun ν hν => ⟨(hreads ν hν).1.toTouch, (hreads ν hν).2.toTouch⟩)

/-! ## The two touching classes sit inside `ClassCoupled`. -/

/-- Site coverage unchanged, plaquette coverage with both `CubeBond`s replaced, regularity
on touching bonds. -/
def ClassCoupledTouch (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqTouch ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

theorem ClassCoupledTouch.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledTouch ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  ⟨⟨h.1, h.2.1.toFrozen⟩, h.2.2.toFrozen⟩

/-- Same regularity, but plaquette coverage is the one-corner clause. -/
def ClassCoupledCorner (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

theorem ClassCoupledCorner.toTouch {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) : ClassCoupledTouch ell M c k S α₀ η U :=
  ⟨h.1, h.2.1.toTouch, h.2.2⟩

theorem ClassCoupledCorner.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  h.toTouch.toFrozen

/-! ## Headline transport. Same quantifiers, same `InstIneq`, class hypothesis only. -/

def CoercG8AtTouch (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledTouch ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

def CoercG8AtCorner (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledCorner ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

theorem coercTouch_of_frozen {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8At ell M R k hell a Lu c α₀ γ₀) :
    CoercG8AtTouch ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.toFrozen

theorem coercCorner_of_touch {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8AtTouch ell M R k hell a Lu c α₀ γ₀) :
    CoercG8AtCorner ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.toTouch

def P428Core8AtTouch (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtTouch ell M R k hell a Lu c α₀ γ₀

def P428Genuine8Touch (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8AtTouch ell M R hell a 12

def P428Target8Touch : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8Touch ell (ell ^ m) R (by omega) a

def P428Core8AtCorner (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtCorner ell M R k hell a Lu c α₀ γ₀

def P428Genuine8Corner (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8AtCorner ell M R hell a 12

def P428Target8Corner : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8Corner ell (ell ^ m) R (by omega) a

theorem targetTouch_of_frozen (h : P428Target8) : P428Target8Touch := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hRR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hU
  exact hcore k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hU.toFrozen

theorem targetCorner_of_touch (h : P428Target8Touch) : P428Target8Corner := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hRR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hU
  exact hcore k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hU.toTouch

theorem targetCorner_of_frozen (h : P428Target8) : P428Target8Corner :=
  targetCorner_of_touch (targetTouch_of_frozen h)

end AdalyFormal.AHP.S2Class

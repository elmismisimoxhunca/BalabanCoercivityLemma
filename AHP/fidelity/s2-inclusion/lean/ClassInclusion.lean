import ZT5A
import ZR2Ops2
import ZR8Class

/-!
# S-2 repaired — frozen `ClassCoupled` contains the touching classes

Standalone Stage-B comparison file; not a Lake root. Compile from `lean/` with
`lake env lean ../AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean` through the
heavy-run wrapper. The adjacent `.log` and `.exit` record the final check.

Sol's adopted claim, and the only claim in this file
(`AHP/attempts/s2-class-implication/SOL_VERDICT.md`):

  `ClassCoupledCorner → ClassCoupledFour → ClassCoupled`

and the same chain for the headlines, with the frozen `InstIneq` left unchanged.
No converse, no strict inclusion, no proper-domain non-vacuity, no operator
equality, no resolution of S-1, no paper sentence.

Name repair (prosecution F-1). `AdalyFormal.AHP.S1Touching.ClassCoupledTouch`
is the corner class (`CoversPlaqCorner`). The old S-2 draft used the same name
for the weaker four-bond class. This file does not declare `ClassCoupledTouch`.

* `ClassCoupledCorner` is the S-1 conjunction: `CoversOm0c`, `CoversPlaqCorner`,
  `PerCubeRegularTouch`. Same `TouchBond`, `plaqCorner`, `CoversPlaqCorner` and
  `PerCubeRegularTouch` text as `AHP/attempts/s1-touching/Touching.lean`.
* `ClassCoupledFour` is the old S-2 four-bond class (`CoversPlaqTouch` there).

The parallel s1-touching design was asked not to repeat corner coverage, because
of the saturation concern for proper nonempty `Ω₀`. Sol upheld that concern
but rejected the previous proposal as a resolution of S-1; saturation is not
proved in this file. A shell class whose cubes leave `Ω₀` is not a
frozen `IsClassCube`. This file does not state an inclusion for any such shell.

Elaboration repairs (prosecution F-2), against the old draft:

* `square_edges_touch` unfolds `TouchBond` and cases on the disjunction. It does
  not rewrite a folded `TouchBond`.
* `touchCover_cubeBond` unfolds `CubeBond` and rewrites the two endpoint goals
  separately, as `ZR8Class.lean:114–119` does for boundary membership.
* `CoversPlaqFour.toFrozen` keeps the cube equality `sites = siteBox …` and
  transports by `▸`. It does not `rcases` that equality to `rfl` under `hc`.
* Headline unpacking is nested `rcases` after `unfold`, not one flat `obtain`
  through `P428Genuine8`.

Vacancy (prosecution F-3). Corner saturation is not re-proved. No declaration
says either touching class is inhabited, or strictly smaller.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.AHP.FidelS2Inclusion

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

/-! ## Touching bonds. `CubeBond` is `ZStatementP428.lean:145`. -/

/-- At least one endpoint in `sites`. Same text as `S1Touching.TouchBond`. -/
def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

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

/-! ## Coverage. Frozen `CoversPlaqOm0c` is `ZR6A.lean:27`. `plaqIn` is `ZR2Ops2.lean:74`. -/

theorem cubeAnte_iff_plaqIn (S : Set (PeriodicLatticeSite L)) (p : PeriodicLatticePlaquette L) :
    (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond S e) ↔ p ∈ plaqIn S := by
  constructor
  · intro h
    simpa [plaqIn, CubeBond] using h
  · intro h
    simpa [plaqIn, CubeBond] using h

/-- Both `CubeBond` occurrences of `CoversPlaqOm0c` replaced by `TouchBond`.
The antecedent is every plaquette whose four bonds meet `Ω₀`, which properly
contains the `plaqIn` antecedent, so this is not a bond-for-bond rewrite. -/
def CoversPlaqFour (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

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

/-- One corner in `S`. Same text as `S1Touching.plaqCorner`. -/
def plaqCorner (S : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S ∨
      periodicLatticeShift p.1 p.2.1.2 ∈ S ∨
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

theorem plaqCorner_of_allTouch {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond S e) : p ∈ plaqCorner S := by
  rcases TouchBond.endpoints (ht _ (edgeAB_mem p)) with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

/-- Every one-corner plaquette of `Ω₀` has all four bonds touching one class cube.
Same text as `S1Touching.CoversPlaqCorner`. Stronger antecedent than
`CoversPlaqFour`: a one-corner plaquette need not meet `Ω₀` on all four bonds.
This is an added coverage clause, not a consequence of the bond convention alone. -/
def CoversPlaqCorner (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

theorem CoversPlaqCorner.toFour {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqFour ell M c k S := by
  intro p hp
  obtain ⟨sites, j, hc, ht⟩ := h p (plaqCorner_of_allTouch hp)
  exact ⟨sites, j, hc, ht⟩

theorem CoversPlaqCorner.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqOm0c ell M c k S :=
  h.toFour.toFrozen

/-! ## Regularity. `CubeBond` is only a bound hypothesis (`ZR2A.lean:47`).
`CurlReads` is `ZR2A.lean:35`. Widening the hypotheses strengthens the premise. -/

def CurlReadsTouch (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  TouchBond sites (periodicLatticeShift x a, b) ∧ TouchBond sites (x, b) ∧
  TouchBond sites (periodicLatticeShift x b, a) ∧ TouchBond sites (x, a)

theorem CurlReads.toTouch {sites : Set (PeriodicLatticeSite L)}
    {x : PeriodicLatticeSite L} {a b : Fin 3}
    (h : CurlReads sites x a b) : CurlReadsTouch sites x a b :=
  ⟨CubeBond.toTouch h.1, CubeBond.toTouch h.2.1,
    CubeBond.toTouch h.2.2.1, CubeBond.toTouch h.2.2.2⟩

/-- `(3.35)+(3.36)` with `TouchBond` where `PerCubeRegular2` has `CubeBond`.
Same quantifier order: `∃ g, A` stays inside `∀` class cube. Same three bounds.
Same text as `S1Touching.PerCubeRegularTouch`. -/
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
    exact hA e (CubeBond.toTouch he)
  · intro μ ν x h1 h2
    exact hD μ ν x (CubeBond.toTouch h1) (CubeBond.toTouch h2)
  · intro μ x hreads
    exact hLap μ x (fun ν hν =>
      ⟨CurlReads.toTouch (hreads ν hν).1, CurlReads.toTouch (hreads ν hν).2⟩)

/-! ## The two touching classes. `ClassCoupled` is `ZR6A.lean:124`
(`CoversOm0p ∧ PerCubeRegular2`). `CoversOm0c` (`ZR2A.lean:107`) has no `CubeBond`
and is shared unchanged. `CoversOm0p` is `ZR6A.lean:33`. -/

/-- Site coverage unchanged, four-bond plaquette coverage, touching regularity.
This is the old S-2 `ClassCoupledTouch`. It is not the S-1 class of that name. -/
def ClassCoupledFour (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqFour ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

theorem ClassCoupledFour.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledFour ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  ⟨⟨h.1, h.2.1.toFrozen⟩, h.2.2.toFrozen⟩

/-- S-1's class, under a name that does not collide: sites, one-corner plaquettes,
touching regularity. -/
def ClassCoupledCorner (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

theorem ClassCoupledCorner.toFour {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) : ClassCoupledFour ell M c k S α₀ η U :=
  ⟨h.1, h.2.1.toFour, h.2.2⟩

theorem ClassCoupledCorner.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledCorner ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  h.toFour.toFrozen

/-! ## Headlines. Quantifiers copied from `ZT5A.lean:89`, `:170`, `:200`, `:229`, `:291`.
Factor `12`. Smallness `(12 : ℝ) * M * α₀ ≤ a₀`. Conclusion `InstIneq` (`ZT5A.lean:56`),
whose `Δ` and `J` stay on `plaqIn`. `Λ` stays `OnLambdaT` / `CRowIn` / `OnLambdaTildeIn`. -/

def CoercG8AtFour (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledFour ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

def CoercG8AtCorner (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledCorner ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

theorem coercFour_of_frozen {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8At ell M R k hell a Lu c α₀ γ₀) :
    CoercG8AtFour ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.toFrozen

theorem coercCorner_of_four {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent}
    {c : ℕ} {α₀ γ₀ : ℝ} (h : CoercG8AtFour ell M R k hell a Lu c α₀ γ₀) :
    CoercG8AtCorner ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.toFour

def P428Core8AtFour (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtFour ell M R k hell a Lu c α₀ γ₀

def P428Genuine8Four (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8AtFour ell M R hell a 12

def P428Target8Four : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8Four ell (ell ^ m) R (by omega) a

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

theorem targetFour_of_frozen (h : P428Target8) : P428Target8Four := by
  unfold P428Target8 at h
  unfold P428Target8Four
  intro ell hell a ha
  rcases h ell hell a ha with ⟨m₀, hm₀, hm⟩
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  rcases hm m hmm with ⟨R₀, hR⟩
  refine ⟨R₀, fun R hRR => ?_⟩
  have hG : P428Genuine8 ell (ell ^ m) R (by omega) a := hR R hRR
  unfold P428Genuine8 at hG
  rcases hG with ⟨hside, hcore⟩
  unfold P428Core8 at hcore
  unfold P428Core8At at hcore
  rcases hcore with ⟨a₀, ⟨ha₀, ⟨γ₀, ⟨hγ, hAt⟩⟩⟩⟩
  unfold P428Genuine8Four
  unfold P428Core8AtFour
  exact ⟨hside, ⟨a₀, ⟨ha₀, ⟨γ₀, ⟨hγ, fun k hk Lu α₀ hα hsmall =>
    coercFour_of_frozen (hAt k hk Lu α₀ hα hsmall)⟩⟩⟩⟩⟩

theorem targetCorner_of_four (h : P428Target8Four) : P428Target8Corner := by
  unfold P428Target8Four at h
  unfold P428Target8Corner
  intro ell hell a ha
  rcases h ell hell a ha with ⟨m₀, hm₀, hm⟩
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  rcases hm m hmm with ⟨R₀, hR⟩
  refine ⟨R₀, fun R hRR => ?_⟩
  have hG : P428Genuine8Four ell (ell ^ m) R (by omega) a := hR R hRR
  unfold P428Genuine8Four at hG
  rcases hG with ⟨hside, hcore⟩
  unfold P428Core8AtFour at hcore
  rcases hcore with ⟨a₀, ⟨ha₀, ⟨γ₀, ⟨hγ, hAt⟩⟩⟩⟩
  unfold P428Genuine8Corner
  unfold P428Core8AtCorner
  exact ⟨hside, ⟨a₀, ⟨ha₀, ⟨γ₀, ⟨hγ, fun k hk Lu α₀ hα hsmall =>
    coercCorner_of_four (hAt k hk Lu α₀ hα hsmall)⟩⟩⟩⟩⟩

theorem targetCorner_of_frozen (h : P428Target8) : P428Target8Corner :=
  targetCorner_of_four (targetFour_of_frozen h)

end AdalyFormal.AHP.FidelS2Inclusion

#print axioms AdalyFormal.AHP.FidelS2Inclusion.touchCover_cubeBond
#print axioms AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqFour.toFrozen
#print axioms AdalyFormal.AHP.FidelS2Inclusion.CoversPlaqCorner.toFour
#print axioms AdalyFormal.AHP.FidelS2Inclusion.PerCubeRegularTouch.toFrozen
#print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledFour.toFrozen
#print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFour
#print axioms AdalyFormal.AHP.FidelS2Inclusion.ClassCoupledCorner.toFrozen
#print axioms AdalyFormal.AHP.FidelS2Inclusion.targetFour_of_frozen
#print axioms AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_four
#print axioms AdalyFormal.AHP.FidelS2Inclusion.targetCorner_of_frozen

import ZT5A
import ZR2Ops2
import ZR8Class
import ZLocOps
import ZLocJ

/-!
# S-1 — consistent touching reading (UNCOMPILED DRAFT)

This file is not a Lake root and was not compiled. Nothing here is a theorem of the
project tree. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`
or `extern`.

CMP 102 p.277 identifies a domain with the bonds that have at least one endpoint in it
and the plaquettes that have at least one corner in it. The frozen reading uses
`CubeBond` (both endpoints) in `PerCubeRegular2` / `CoversPlaqOm0c`, and `plaqIn`
(all four corners) for `Δ` and `J`.

`LambdaOK2`, `OnLambdaT`, `OnLambdaTildeIn` and `CRowIn` are already the touching
reading in the frozen statement (`ZT5A` headline comment (3), `ZR2A.OnLambdaT`,
`ZStatementP428.CRowIn`). `bondsOm0` is already touching (`ZXR2Ops3`). They are not
redefined here.

`P428Target8Touching` is the frozen headline with the class replaced by
`ClassCoupledTouch` and with the conclusion strengthened by
`plaqCorner (S.Om 0) = plaqIn (S.Om 0)`. On every tower that satisfies the touching
coverage hypothesis the two plaquette sets are equal, so the frozen `Δ` and `J` are
the one-corner operators there (`deltaKLocCLM_congr`). The inequality is then the
frozen `InstIneq`. The draft shows

  `P428Target8 → P428Target8Touching`

from that comparison. It does not rewrite `Classical.choose` inside `G1invS`; the
conclusion is the frozen `InstIneq` plus the set equality, which is the agreement.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.AHP.S1Touching

open Classical
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

/-! ## Bond and plaquette predicates -/

/-- At least one endpoint in `sites` (CMP 102 p.277 / CMP 96 p.224). -/
def TouchBond (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

theorem CubeBond.toTouch {sites : Set (PeriodicLatticeSite L)} {b : Bond L}
    (h : CubeBond sites b) : TouchBond sites b :=
  Or.inl h.1

/-- Neither endpoint in `sites`. This is `D1Literal.Zb`. -/
def NoEnd (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∉ sites ∧ periodicLatticeShift b.1 b.2 ∉ sites

theorem TouchBond.not_noEnd {sites : Set (PeriodicLatticeSite L)} {b : Bond L}
    (h : TouchBond sites b) : ¬ NoEnd sites b := by
  intro hn
  rcases h with h1 | h2
  · exact hn.1 h1
  · exact hn.2 h2

theorem NoEnd.not_touch {sites : Set (PeriodicLatticeSite L)} {b : Bond L}
    (h : NoEnd sites b) : ¬ TouchBond sites b :=
  fun ht => ht.not_noEnd h

/-- One corner in `S`: the base or one of the three other corners of the unit square. -/
def plaqCorner (S : Set (PeriodicLatticeSite L)) : Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S ∨
      periodicLatticeShift p.1 p.2.1.2 ∈ S ∨
      periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

theorem plaqCorner_univ : plaqCorner (Set.univ : Set (PeriodicLatticeSite L)) = Set.univ := by
  ext p
  refine ⟨fun _ => ⟨⟩, fun _ => ?_⟩
  exact Or.inl ⟨⟩

theorem plaqIn_univ : plaqIn (Set.univ : Set (PeriodicLatticeSite L)) = Set.univ := by
  ext p
  refine ⟨fun _ => ⟨⟩, fun _ e _ => ⟨⟨⟩, ⟨⟩⟩⟩

theorem plaqCorner_empty : plaqCorner (∅ : Set (PeriodicLatticeSite L)) = ∅ := by
  ext p
  refine ⟨?_, fun h => h.elim⟩
  intro h
  rcases h with h1 | h1 | h1 | h1
  · exact h1
  · exact h1
  · exact h1
  · exact h1

theorem plaqIn_empty : plaqIn (∅ : Set (PeriodicLatticeSite L)) = ∅ := by
  ext p
  refine ⟨?_, fun h => h.elim⟩
  intro h
  have he : (p.1, p.2.1.1) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges]
  exact (h _ he).1

theorem plaqCorner_eq_plaqIn_of_empty_or_univ {S : Set (PeriodicLatticeSite L)}
    (h : S = ∅ ∨ S = Set.univ) : plaqCorner S = plaqIn S := by
  rcases h with rfl | rfl
  · rw [plaqCorner_empty, plaqIn_empty]
  · rw [plaqCorner_univ, plaqIn_univ]

theorem not_plaqIn_of_endpoint_out {S : Set (PeriodicLatticeSite L)}
    {p : PeriodicLatticePlaquette L} {e : Bond L}
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hout : e.1 ∉ S ∨ periodicLatticeShift e.1 e.2 ∉ S) : p ∉ plaqIn S := by
  intro hp
  have hb := hp e he
  rcases hout with h1 | h2
  · exact h1 hb.1
  · exact h2 hb.2

/-! ## A rectangular class cube that touch-covers a plaquette contains it -/

theorem mem_siteBox_iff {z : PeriodicLatticeSite L} {s : ℕ} {x : PeriodicLatticeSite L} :
    x ∈ siteBox z s ↔
      ∀ μ : Fin 3, ((x μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < s := by
  rfl

theorem mem_siteBox_of_coordwise {z : PeriodicLatticeSite L} {s : ℕ} {w : PeriodicLatticeSite L}
    (hw : ∀ μ : Fin 3, ∃ p : PeriodicLatticeSite L, p ∈ siteBox z s ∧ (p μ).val = (w μ).val) :
    w ∈ siteBox z s := by
  rw [mem_siteBox_iff]
  intro μ
  obtain ⟨p, hp, hv⟩ := hw μ
  rw [mem_siteBox_iff] at hp
  rw [← hv]
  exact hp μ

/-- The four corners of `p = (x; μ, ν)`. -/
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

/-- Every boundary bond of `p` is an edge of the square `A,B,C,D`. -/
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
  · have hcomm := cornerD_comm p
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hcomm⟩))
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ht _ eAB
    simpa [cornerA, cornerB] using h
  · have h := ht _ eBD
    simpa [cornerB, cornerD] using h
  · have h := ht _ eCD
    have hD := cornerD_comm p
    simpa [cornerC, hD] using h
  · have h := ht _ eAC
    simpa [cornerA, cornerC] using h

theorem siteBox_fill_of_diagonal {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (hA : cornerA p ∈ siteBox z s) (hD : cornerD p ∈ siteBox z s) :
    cornerB p ∈ siteBox z s ∧ cornerC p ∈ siteBox z s := by
  let d1 := p.2.1.1
  let d2 := p.2.1.2
  have hne : d1 ≠ d2 := ne_of_lt p.2.2
  have hCD : cornerD p = periodicLatticeShift (cornerC p) d1 := (cornerD_comm p).symm
  have hB : cornerB p ∈ siteBox z s := by
    apply mem_siteBox_of_coordwise
    intro ρ
    by_cases hρ : ρ = d1
    · subst hρ
      -- `cornerD` differs from `cornerB` only along `d2`.
      exact ⟨cornerD p, hD, coord_shift_ne (x := cornerB p) (ν := d2) (κ := d1) hne.symm⟩
    · exact ⟨cornerA p, hA, (coord_shift_ne (x := cornerA p) (ν := d1) (κ := ρ) hρ).symm⟩
  have hC : cornerC p ∈ siteBox z s := by
    apply mem_siteBox_of_coordwise
    intro ρ
    by_cases hρ : ρ = d2
    · subst hρ
      refine ⟨cornerD p, hD, ?_⟩
      rw [hCD]
      exact coord_shift_ne (x := cornerC p) (ν := d1) (κ := d2) hne
    · exact ⟨cornerA p, hA, (coord_shift_ne (x := cornerA p) (ν := d2) (κ := ρ) hρ).symm⟩
  exact ⟨hB, hC⟩

theorem siteBox_fill_of_antidiagonal {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (hB : cornerB p ∈ siteBox z s) (hC : cornerC p ∈ siteBox z s) :
    cornerA p ∈ siteBox z s ∧ cornerD p ∈ siteBox z s := by
  let d1 := p.2.1.1
  let d2 := p.2.1.2
  have hne : d1 ≠ d2 := ne_of_lt p.2.2
  have hCD : cornerD p = periodicLatticeShift (cornerC p) d1 := (cornerD_comm p).symm
  have hA : cornerA p ∈ siteBox z s := by
    apply mem_siteBox_of_coordwise
    intro ρ
    by_cases h1 : ρ = d1
    · subst h1
      exact ⟨cornerC p, hC, coord_shift_ne (x := cornerA p) (ν := d2) (κ := d1) hne.symm⟩
    · by_cases h2 : ρ = d2
      · subst h2
        exact ⟨cornerB p, hB, coord_shift_ne (x := cornerA p) (ν := d1) (κ := d2) hne⟩
      · exact ⟨cornerB p, hB, coord_shift_ne (x := cornerA p) (ν := d1) (κ := ρ) h1⟩
  have hD : cornerD p ∈ siteBox z s := by
    apply mem_siteBox_of_coordwise
    intro ρ
    by_cases h1 : ρ = d1
    · subst h1
      exact ⟨cornerB p, hB, (coord_shift_ne (x := cornerB p) (ν := d2) (κ := d1) hne.symm).symm⟩
    · by_cases h2 : ρ = d2
      · subst h2
        refine ⟨cornerC p, hC, ?_⟩
        rw [hCD]
        exact (coord_shift_ne (x := cornerC p) (ν := d1) (κ := d2) hne).symm
      · exact ⟨cornerB p, hB, (coord_shift_ne (x := cornerB p) (ν := d2) (κ := ρ) h2).symm⟩
  exact ⟨hA, hD⟩

/-- A vertex cover of the 4-cycle contains an opposite pair. -/
theorem opposite_of_touch {sites : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e) :
    (cornerA p ∈ sites ∧ cornerD p ∈ sites) ∨ (cornerB p ∈ sites ∧ cornerC p ∈ sites) := by
  obtain ⟨hAB, hBD, hCD, hAC⟩ := square_edges_touch ht
  by_contra h
  push_neg at h
  rcases h.1 with hA | hD
  · rcases h.2 with hB | hC
    · exact hAB.elim hA hB
    · exact hAC.elim hA hC
  · rcases h.2 with hB | hC
    · exact hBD.elim hB hD
    · exact hCD.elim hC hD

theorem touchCover_all_corners {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z s) e) :
    cornerA p ∈ siteBox z s ∧ cornerB p ∈ siteBox z s ∧
      cornerC p ∈ siteBox z s ∧ cornerD p ∈ siteBox z s := by
  rcases opposite_of_touch (sites := siteBox z s) ht with ⟨hA, hD⟩ | ⟨hB, hC⟩
  · obtain ⟨hB, hC⟩ := siteBox_fill_of_diagonal hA hD
    exact ⟨hA, hB, hC, hD⟩
  · obtain ⟨hA, hD⟩ := siteBox_fill_of_antidiagonal hB hC
    exact ⟨hA, hB, hC, hD⟩

theorem touchCover_cubeBond {z : PeriodicLatticeSite L} {s : ℕ} {p : PeriodicLatticePlaquette L}
    (ht : ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond (siteBox z s) e)
    {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    CubeBond (siteBox z s) e := by
  have hall := touchCover_all_corners ht
  rcases boundary_is_square he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨hall.1, hall.2.1⟩
  · rw [h1, h2]; exact ⟨hall.2.1, hall.2.2.2⟩
  · rw [h1, h2]; exact ⟨hall.2.2.1, hall.2.2.2⟩
  · rw [h1, h2]; exact ⟨hall.1, hall.2.2.1⟩

/-! ## Touching coverage and regularity -/

/-- Every plaquette with at least one corner in `Ω₀` has all four bonds touching one class cube. -/
def CoversPlaqCorner (ell M c k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M c k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, TouchBond sites e

theorem corner_of_cubeBond_om {S : Set (PeriodicLatticeSite L)} {p : PeriodicLatticePlaquette L}
    (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond S e) : p ∈ plaqCorner S := by
  have he : (p.1, p.2.1.1) ∈ periodicPlaquetteBoundaryEdges p := by
    simp [periodicPlaquetteBoundaryEdges]
  exact Or.inl (hp _ he).1

/-- One-corner coverage implies the frozen both-endpoint plaquette coverage.
A class cube is a `siteBox`. Touch-covering its square forces all four corners in,
hence `CubeBond`. -/
theorem CoversPlaqCorner.toFrozen {ell M c k : ℕ} {S : Tower L}
    (h : CoversPlaqCorner ell M c k S) : CoversPlaqOm0c ell M c k S := by
  intro p hp
  have hcorn : p ∈ plaqCorner (S.Om 0) := corner_of_cubeBond_om hp
  obtain ⟨sites, j, hc, ht⟩ := h p hcorn
  rcases hc.1.2.1 with ⟨z, _, rfl⟩
  refine ⟨siteBox z (c * bigSide M ell j), j, hc, ?_⟩
  intro e he
  exact touchCover_cubeBond ht he

def CurlReadsTouch (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  TouchBond sites (periodicLatticeShift x a, b) ∧ TouchBond sites (x, b) ∧
  TouchBond sites (periodicLatticeShift x b, a) ∧ TouchBond sites (x, a)

theorem CurlReads.toTouch {sites : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L} {a b : Fin 3}
    (h : CurlReads sites x a b) : CurlReadsTouch sites x a b :=
  ⟨h.1.toTouch, h.2.1.toTouch, h.2.2.1.toTouch, h.2.2.2.toTouch⟩

/-- `(3.35)+(3.36)` with `TouchBond` in place of `CubeBond`. Same quantifier order. -/
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
    apply hLap μ x
    intro ν hν
    obtain ⟨r1, r2⟩ := hreads ν hν
    exact ⟨r1.toTouch, r2.toTouch⟩

/-- Sites (`CoversOm0c`, unchanged: it quantifies over sites), one-corner plaquettes, touching bonds. -/
def ClassCoupledTouch (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0c ell M c k S ∧ CoversPlaqCorner ell M c k S ∧ PerCubeRegularTouch ell M c k S α₀ η U

theorem ClassCoupledTouch.toFrozen {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledTouch ell M c k S α₀ η U) : ClassCoupled ell M c k S α₀ η U :=
  ⟨⟨h.1, h.2.1.toFrozen⟩, h.2.2.toFrozen⟩

/-! ## Proper block domains have a one-corner plaquette with a bond in `NoEnd` -/

def fwdN (N a b : ℕ) : ℕ := (b + N - a) % N

def fwdDist (x y : PeriodicLatticeSite L) : ℕ :=
  fwdN (L 0 + 1) (x 0).val (y 0).val +
    fwdN (L 1 + 1) (x 1).val (y 1).val +
    fwdN (L 2 + 1) (x 2).val (y 2).val

theorem fwdN_eq_zero {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
    (h : fwdN N a b = 0) : a = b := by
  have haN : a ≤ N := le_of_lt ha
  have hmpos : 1 ≤ b + (N - a) := by
    have hsub : 0 < N - a := Nat.sub_pos_of_lt ha
    have h1 : 1 ≤ N - a := Nat.succ_le_of_lt hsub
    exact le_trans h1 (Nat.le_add_left _ _)
  have hm : b + N - a = b + (N - a) := Nat.add_sub_assoc haN b
  have hge : 1 ≤ b + N - a := by rw [hm]; exact hmpos
  have hlt : b + N - a < 2 * N := by omega
  have hdvd : N ∣ b + N - a := Nat.dvd_of_mod_eq_zero h
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : q = 1 := by
    have hposq : 0 < q := by
      have : q ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hq
        omega
      omega
    have hltq : q < 2 := by
      have : q * N < 2 * N := by simpa [hq] using hlt
      exact Nat.lt_of_mul_lt_mul_right this
    omega
  have : b + N - a = N := by simpa [hq1, one_mul] using hq
  omega

theorem fwdDist_eq_zero {x y : PeriodicLatticeSite L} (h : fwdDist x y = 0) : x = y := by
  have h0 : fwdN (L 0 + 1) (x 0).val (y 0).val = 0 := by
    unfold fwdDist at h; omega
  have h1 : fwdN (L 1 + 1) (x 1).val (y 1).val = 0 := by
    unfold fwdDist at h; omega
  have h2 : fwdN (L 2 + 1) (x 2).val (y 2).val = 0 := by
    unfold fwdDist at h; omega
  funext μ
  fin_cases μ
  · exact Fin.ext (fwdN_eq_zero (Nat.succ_pos _) (x 0).isLt (y 0).isLt h0)
  · exact Fin.ext (fwdN_eq_zero (Nat.succ_pos _) (x 1).isLt (y 1).isLt h1)
  · exact Fin.ext (fwdN_eq_zero (Nat.succ_pos _) (x 2).isLt (y 2).isLt h2)

theorem exists_pos_fwd {x y : PeriodicLatticeSite L} (h : 0 < fwdDist x y) :
    ∃ μ : Fin 3, 0 < fwdN (L μ + 1) (x μ).val (y μ).val := by
  by_contra hno
  push_neg at hno
  have : fwdDist x y = 0 := by
    unfold fwdDist
    have a0 := hno (0 : Fin 3)
    have a1 := hno (1 : Fin 3)
    have a2 := hno (2 : Fin 3)
    omega
  omega

theorem fwdN_pred {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
    (hpos : 0 < fwdN N a b) :
    fwdN N ((a + 1) % N) b + 1 = fwdN N a b := by
  dsimp [fwdN] at hpos ⊢
  by_cases hlt : a + 1 < N
  · have hnew : (a + 1) % N = a + 1 := Nat.mod_eq_of_lt hlt
    rw [hnew]
    have hsub : b + N - (a + 1) = b + N - a - 1 := by
      simpa [Nat.add_comm 1 a] using (Nat.sub_sub (b + N) a 1).symm
    rw [hsub]
    set m := b + N - a with hm
    have hdpos : 1 ≤ m % N := by simpa [hm] using Nat.succ_le_of_lt hpos
    have hquot : m = m / N * N + m % N := (Nat.div_add_mod m N).symm
    have hpred : m - 1 = m % N - 1 + m / N * N := by
      calc m - 1 = m / N * N + m % N - 1 := by rw [← hquot]
        _ = m / N * N + (m % N - 1) := Nat.add_sub_assoc hdpos _
        _ = m % N - 1 + m / N * N := Nat.add_comm _ _
    have hmod : (m % N - 1 + m / N * N) % N = (m % N - 1) % N :=
      Nat.add_mul_mod_self_left (m % N - 1) (m / N) N
    have hsmall : m % N - 1 < N := by
      have : m % N < N := Nat.mod_lt _ hN
      omega
    rw [hpred, hmod, Nat.mod_eq_of_lt hsmall]
    omega
  · have haeq : a = N - 1 := by omega
    have hstep : a + 1 = N := by omega
    have hnew : (a + 1) % N = 0 := by simpa [hstep] using Nat.mod_self N
    rw [hnew, Nat.sub_zero]
    have hd' : (b + N) % N = b := by
      have h := Nat.add_mul_mod_self_left b 1 N
      simpa [Nat.one_mul, Nat.mod_eq_of_lt hb] using h
    have hm : b + N - a = b + 1 := by omega
    have hltb : b + 1 < N := by
      by_contra hbad
      have heq : b + 1 = N := by omega
      have h0 : (b + N - a) % N = 0 := by
        rw [hm, heq, Nat.mod_self]
      exact (Nat.not_lt_zero 0) (h0 ▸ hpos)
    have hd : (b + N - a) % N = b + 1 := by rw [hm, Nat.mod_eq_of_lt hltb]
    rw [hd', hd]

theorem fwdDist_shift {x y : PeriodicLatticeSite L} {μ : Fin 3}
    (hpos : 0 < fwdN (L μ + 1) (x μ).val (y μ).val) :
    fwdDist (periodicLatticeShift x μ) y + 1 = fwdDist x y := by
  have hstep := fwdN_pred (Nat.succ_pos (L μ)) (x μ).isLt (y μ).isLt hpos
  fin_cases μ
  · have e1 : periodicLatticeShift x 0 1 = x 1 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (1 : Fin 3) ≠ 0)
    have e2 : periodicLatticeShift x 0 2 = x 2 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (2 : Fin 3) ≠ 0)
    unfold fwdDist
    rw [e1, e2]
    simpa using hstep
  · have e0 : periodicLatticeShift x 1 0 = x 0 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (0 : Fin 3) ≠ 1)
    have e2 : periodicLatticeShift x 1 2 = x 2 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (2 : Fin 3) ≠ 1)
    unfold fwdDist
    rw [e0, e2]
    have := hstep
    omega
  · have e0 : periodicLatticeShift x 2 0 = x 0 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (0 : Fin 3) ≠ 2)
    have e1 : periodicLatticeShift x 2 1 = x 1 :=
      AdalyFormal.StatementLaneR8.shift_ne x (by decide : (1 : Fin 3) ≠ 2)
    unfold fwdDist
    rw [e0, e1]
    have := hstep
    omega

theorem exists_exit {Ω : Set (PeriodicLatticeSite L)} {x y : PeriodicLatticeSite L}
    (hx : x ∈ Ω) (hy : y ∉ Ω) :
    ∃ z μ, z ∈ Ω ∧ periodicLatticeShift z μ ∉ Ω := by
  suffices H : ∀ d x y, fwdDist x y = d → x ∈ Ω → y ∉ Ω →
      ∃ z μ, z ∈ Ω ∧ periodicLatticeShift z μ ∉ Ω by
    exact H _ x y rfl hx hy
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x y hd hx hy
    have hpos : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      have hxy : x = y := fwdDist_eq_zero (hd.symm ▸ hd0)
      exact hy (hxy ▸ hx)
    rw [← hd] at hpos
    obtain ⟨μ, hμ⟩ := exists_pos_fwd hpos
    set z := periodicLatticeShift x μ
    by_cases hz : z ∈ Ω
    · have hlt : fwdDist z y < d := by
        have hstep := fwdDist_shift (x := x) (y := y) (μ := μ) hμ
        omega
      exact ih _ hlt z y rfl hz hy
    · exact ⟨x, μ, hx, hz⟩

theorem block_div {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) :
    ∀ μ, M ∣ L μ + 1 := by
  intro μ
  have h := hS.2.2.1 0 (Nat.zero_le _) μ
  rwa [bigSide, pow_zero, mul_one] at h

theorem block_closed_om0 {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) :
    BlockClosed M (S.Om 0) := by
  have h := hS.2.2.2.1 0 (Nat.zero_le _)
  rwa [bigSide, pow_zero, mul_one] at h

theorem class_sites_subset_om0 {ell M R f k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hc : IsClassCube ell M f k S sites j) : sites ⊆ S.Om 0 := by
  intro x hx
  rcases hc.1.2.2.1 hx with h | h
  · exact AdalyFormal.StatementLaneR8.admissible_mono hS j h.1
  · exact AdalyFormal.StatementLaneR8.admissible_mono hS (j + 1) h.1

/-- Same `M`-block as `z`, with the `ν`-coordinate moved to the start of that block. -/
def faceSite {M : ℕ} (z : PeriodicLatticeSite L) (ν : Fin 3) (_hM : 0 < M) : PeriodicLatticeSite L :=
  fun κ => ⟨if κ = ν then (z ν).val / M * M else (z κ).val, by
    by_cases hκ : κ = ν
    · rw [if_pos hκ]
      subst hκ
      exact lt_of_le_of_lt (Nat.div_mul_le_self (z κ).val M) (z κ).isLt
    · rw [if_neg hκ]
      exact (z κ).isLt⟩

theorem faceSite_val {M : ℕ} (z : PeriodicLatticeSite L) (ν : Fin 3) (hM : 0 < M) (κ : Fin 3) :
    ((faceSite z ν hM) κ).val = if κ = ν then (z ν).val / M * M else (z κ).val :=
  rfl

theorem faceSite_div {M : ℕ} (z : PeriodicLatticeSite L) (ν : Fin 3) (hM : 0 < M) (κ : Fin 3) :
    ((faceSite z ν hM) κ).val / M = (z κ).val / M := by
  rw [faceSite_val]
  by_cases hκ : κ = ν
  · rw [if_pos hκ]
    subst hκ
    exact Nat.mul_div_cancel _ hM
  · rw [if_neg hκ]

theorem faceSite_mem {M : ℕ} {Ω : Set (PeriodicLatticeSite L)} (hbc : BlockClosed M Ω)
    {z : PeriodicLatticeSite L} (hz : z ∈ Ω) (ν : Fin 3) (hM : 0 < M) :
    faceSite z ν hM ∈ Ω :=
  hbc z hz _ (faceSite_div z ν hM)

theorem faceSite_nu_val {M : ℕ} (z : PeriodicLatticeSite L) (ν : Fin 3) (hM : 0 < M) :
    ((faceSite z ν hM) ν).val = (z ν).val / M * M := by
  rw [faceSite_val, if_pos rfl]

theorem not_dvd_block_start {M q : ℕ} (hM : 2 ≤ M) : ¬ M ∣ q * M + 1 := by
  intro h
  have hM1 : M ∣ 1 := (Nat.dvd_add_right (dvd_mul_left M q)).mp h
  have : M = 1 := Nat.dvd_one.mp hM1
  omega

/-- From an exit edge of a block-closed set, a plaquette with one corner in the set and one
boundary bond with both endpoints outside. -/
theorem bad_plaq_of_exit {M : ℕ} {Ω : Set (PeriodicLatticeSite L)}
    (hbc : BlockClosed M Ω) (hdvd : ∀ μ : Fin 3, M ∣ L μ + 1) (hM : 2 ≤ M)
    {z : PeriodicLatticeSite L} {μ : Fin 3}
    (hz : z ∈ Ω) (hout : periodicLatticeShift z μ ∉ Ω) :
    ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner Ω ∧ p ∉ plaqIn Ω ∧
      ∃ e ∈ periodicPlaquetteBoundaryEdges p, NoEnd Ω e := by
  have hM0 : 0 < M := by omega
  set ν : Fin 3 := if μ = 0 then 1 else 0
  have hμν : μ ≠ ν := by
    intro h
    by_cases h0 : μ = 0
    · have hν : ν = 1 := by simp [ν, h0]
      rw [h0, hν] at h
      exact absurd h (by decide : (0 : Fin 3) ≠ 1)
    · have hν : ν = 0 := by simp [ν, h0]
      exact h0 (h.symm.trans hν)
  set w := faceSite z ν hM0
  have hw : w ∈ Ω := faceSite_mem hbc hz ν hM0
  have hsame : ∀ κ, (w κ).val / M = (z κ).val / M := faceSite_div z ν hM0
  have hwμ : (w μ).val = (z μ).val := by
    rw [faceSite_val z ν hM0 μ, if_neg hμν]
  have hstart : (w ν).val = (z ν).val / M * M := by
    simpa [w] using faceSite_nu_val z ν hM0
  have hnot : ¬ M ∣ (w ν).val + 1 := by
    rw [hstart]
    exact not_dvd_block_start (q := (z ν).val / M) hM
  have hwν_in : periodicLatticeShift w ν ∈ Ω := by
    have hdiv := AdalyFormal.StatementLaneR8.shift_sameBlock (L := L) hdvd (z := w) (ν := ν) hnot
    exact hbc w hw _ hdiv
  let wμ : PeriodicLatticeSite L := periodicLatticeShift w μ
  have hblock_out : ∀ t : PeriodicLatticeSite L,
      (∀ κ, (t κ).val / M = ((periodicLatticeShift z μ) κ).val / M) → t ∉ Ω := by
    intro t ht htin
    exact hout (hbc t htin _ fun κ => (ht κ).symm)
  have hwμ_div : ∀ κ, (wμ κ).val / M = ((periodicLatticeShift z μ) κ).val / M := by
    intro κ
    by_cases hκ : κ = μ
    · subst hκ
      have hv : (wμ μ).val = ((periodicLatticeShift z μ) μ).val := by
        simp [wμ, periodicLatticeShift, hwμ]
      rw [hv]
    · have hzw : (periodicLatticeShift z μ κ).val = (z κ).val :=
        congrArg Fin.val (AdalyFormal.StatementLaneR8.shift_ne z hκ)
      have hww : (wμ κ).val = (w κ).val :=
        congrArg Fin.val (AdalyFormal.StatementLaneR8.shift_ne w hκ)
      rw [hww, hzw, hsame κ]
  have hwμ_out : wμ ∉ Ω := hblock_out wμ hwμ_div
  let wμν : PeriodicLatticeSite L := periodicLatticeShift wμ ν
  have hwμν_div : ∀ κ, (wμν κ).val / M = (wμ κ).val / M := by
    have hνval : (wμ ν).val = (w ν).val :=
      congrArg Fin.val (AdalyFormal.StatementLaneR8.shift_ne w hμν.symm)
    have hnot' : ¬ M ∣ (wμ ν).val + 1 := by rw [hνval]; exact hnot
    simpa [wμν] using
      AdalyFormal.StatementLaneR8.shift_sameBlock (L := L) hdvd (z := wμ) (ν := ν) hnot'
  have hwμν_out : wμν ∉ Ω := hblock_out wμν (fun κ => (hwμν_div κ).trans (hwμ_div κ))
  have hbond : NoEnd Ω (wμ, ν) := ⟨hwμ_out, by simpa [wμν] using hwμν_out⟩
  have hcorn : w ∈ Ω := hw
  rcases lt_or_gt_of_ne hμν with hlt | hlt
  · refine ⟨(w, ⟨(μ, ν), hlt⟩), ?_, ?_, (wμ, ν), ?_, hbond⟩
    · exact Or.inl hcorn
    · refine not_plaqIn_of_endpoint_out ?_ (Or.inl hwμ_out)
      simp [periodicPlaquetteBoundaryEdges, wμ]
    · simp [periodicPlaquetteBoundaryEdges, wμ]
  · refine ⟨(w, ⟨(ν, μ), hlt⟩), ?_, ?_, (wμ, ν), ?_, hbond⟩
    · exact Or.inl hcorn
    · refine not_plaqIn_of_endpoint_out ?_ (Or.inl hwμ_out)
      simp [periodicPlaquetteBoundaryEdges, wμ]
    · simp [periodicPlaquetteBoundaryEdges, wμ]

theorem not_touch_class_of_noEnd {ell M R f k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    (hc : IsClassCube ell M f k S sites j) {b : Bond L} (hb : NoEnd (S.Om 0) b) :
    ¬ TouchBond sites b := by
  intro ht
  have hsub := class_sites_subset_om0 hS hc
  rcases ht with h1 | h2
  · exact hb.1 (hsub h1)
  · exact hb.2 (hsub h2)

theorem not_CoversPlaqCorner_of_proper {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hne : (S.Om 0).Nonempty) (hproper : ∃ y : PeriodicLatticeSite L, y ∉ S.Om 0) :
    ¬ CoversPlaqCorner ell M c k S := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hproper
  obtain ⟨z, μ, hz, hout⟩ := exists_exit hx hy
  obtain ⟨p, hcorn, _, e, he, hno⟩ :=
    bad_plaq_of_exit (block_closed_om0 hS) (block_div hS) hM hz hout
  intro hcov
  obtain ⟨sites, j, hc, ht⟩ := hcov p hcorn
  exact not_touch_class_of_noEnd hS hc hno (ht e he)

theorem saturated_of_coversCorner {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (h : CoversPlaqCorner ell M c k S) :
    S.Om 0 = ∅ ∨ S.Om 0 = Set.univ := by
  by_cases hne : (S.Om 0).Nonempty
  · by_cases huniv : S.Om 0 = Set.univ
    · exact Or.inr huniv
    · have hproper : ∃ y, y ∉ S.Om 0 := Set.ne_univ_iff_exists_not_mem.mp huniv
      exact absurd h (not_CoversPlaqCorner_of_proper hS hM hne hproper)
  · left
    exact Set.not_nonempty_iff_eq_empty.mp hne

theorem plaq_sets_eq_of_coversCorner {ell M R c k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (h : CoversPlaqCorner ell M c k S) :
    plaqCorner (S.Om 0) = plaqIn (S.Om 0) :=
  plaqCorner_eq_plaqIn_of_empty_or_univ (saturated_of_coversCorner hS hM h)

theorem corner_differs_on_proper {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hM : 2 ≤ M)
    (hne : (S.Om 0).Nonempty) (hproper : ∃ y, y ∉ S.Om 0) :
    ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner (S.Om 0) ∧ p ∉ plaqIn (S.Om 0) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hproper
  obtain ⟨z, μ, hz, hout⟩ := exists_exit hx hy
  obtain ⟨p, hcorn, hnot, _⟩ :=
    bad_plaq_of_exit (block_closed_om0 hS) (block_div hS) hM hz hout
  exact ⟨p, hcorn, hnot⟩

/-! ## Operator agreement once the plaquette sets are equal -/

theorem deltaKLocCLM_congr {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {P Q : Set (PeriodicLatticePlaquette L)} (h : P = Q) :
    AdalyFormal.StatementLaneR6.deltaKLocCLM U P =
      AdalyFormal.StatementLaneR6.deltaKLocCLM U Q := by
  cases h
  rfl

theorem JSU2Loc_congr {η : ℝ} {P Q : Set (PeriodicLatticePlaquette L)} (h : P = Q)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    AdalyFormal.IngredientFamily.JSU2Loc η P U =
      AdalyFormal.IngredientFamily.JSU2Loc η Q U := by
  cases h
  rfl

/-! ## The touching headline, reduced to the frozen one -/

/-- Same quantifiers as `CoercG8At`, with `ClassCoupledTouch`. The conclusion is the frozen
`InstIneq` together with equality of the plaquette sets the two readings sum over. -/
def CoercG8AtTouch (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledTouch ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
      plaqCorner (S.Om 0) = plaqIn (S.Om 0) ∧
        InstIneq ell k hell a Lu γ₀ S Lam U

def P428Core8AtTouch (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) (c : ℕ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtTouch ell M R k hell a Lu c α₀ γ₀

def P428Genuine8Touch (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8AtTouch ell M R hell a 12

/-- Frozen outer quantifiers. `Λ` is the frozen touching reading (`OnLambdaT`, `CRowIn`). -/
def P428Target8Touching : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      P428Genuine8Touch ell (ell ^ m) R (by omega) a

theorem M_ge_two_of_pow {ell m : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) : 2 ≤ ell ^ m := by
  calc 2 ≤ ell := hell
    _ = ell ^ 1 := (pow_one ell).symm
    _ ≤ ell ^ m := Nat.pow_le_pow_right (by omega) hm

/-- The consistent touching headline follows from the frozen headline.
`ClassCoupledTouch` implies `ClassCoupled`. Under `Admissible` and `M ≥ 2` it also forces
`Ω₀` empty or the whole torus, where `plaqCorner = plaqIn`, so the frozen inequality is
the one-corner-operator inequality. -/
theorem touching_of_frozen (h : P428Target8) : P428Target8Touching := by
  intro ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hside, a₀, ha₀, γ₀, hγ, hcore⟩ := hR R hRR
  refine ⟨hside, a₀, ha₀, γ₀, hγ, ?_⟩
  intro k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hU
  have hM : 2 ≤ ell ^ m := M_ge_two_of_pow hell (le_trans hm₀ hmm)
  have hCU : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U := hU.toFrozen
  have hI := hcore k hk Lu α₀ hα hsmall hT S hAd Lam hLam U hCU
  have heq := plaq_sets_eq_of_coversCorner hAd hM hU.2.1
  exact ⟨heq, hI⟩

end AdalyFormal.AHP.S1Touching

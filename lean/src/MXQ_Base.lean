import AC_Base
import ZR8Class
import GG5

/-!
# MXQ_Base -- the FAMILY reading of the class (lane mixed_20261017, round 2)

The proof of the mixed headline applies the regularity of a cube only to cubes obtained from the COVERAGE hypothesis.  So the weakest hypothesis the proof uses is:
a family `Q` of described cubes (triples `(sites, j, f)`) that covers the sites and plaquettes of `Ω₀` and on each member of which `U` is regular with that member's own factor `f`.
`CubeFam L := Set (Set (PeriodicLatticeSite L) × ℕ × ℕ)`; `CF := ∀ L, CubeFam L` (a family on every torus; only the member for the torus at hand matters).
`RegBodyH ell M b sites j α η U` is the body of `PerCubeRegular2H` (the three clauses of (3.35),(3.36) on ONE cube, bound factor `b`).
`Φ`-sets are the special case `Q L = {(sites, j, f) | f ∈ Φ ∧ IsClassCube ..}`: the mixed class of MX_F.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace MXQ.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

abbrev CubeFam (L : PeriodicLatticeExtent) : Type := Set (Set (PeriodicLatticeSite L) × ℕ × ℕ)
abbrev CF : Type := ∀ L : PeriodicLatticeExtent, CubeFam L

/-- every member of the family has factor `≥ 10` (p.396: "Here O(1) will mean a number ≥ 10"). -/
class CubeFamOK (Q : CF) : Prop where
  ge : ∀ (L : PeriodicLatticeExtent) (s : Set (PeriodicLatticeSite L)) (j f : ℕ), (s, j, f) ∈ Q L → 10 ≤ f

theorem CubeFamOK.pos {Q : CF} [h : CubeFamOK Q] {L : PeriodicLatticeExtent} {s : Set (PeriodicLatticeSite L)} {j f : ℕ}
    (hm : (s, j, f) ∈ Q L) : 0 < f := by
  have := h.ge L s j f hm; omega

/-- a described cube of the family. -/
def IsClassCubeQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  ∃ f, (sites, j, f) ∈ Q L ∧ IsClassCube ell M f k S sites j

def CoversOmcQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeQ ell M Q k S sites j ∧ x ∈ sites

def CoversPlaqQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeQ ell M Q k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e

def CoversOmQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (k : ℕ) (S : Tower L) : Prop :=
  CoversOmcQ ell M Q k S ∧ CoversPlaqQ ell M Q k S

/-- the three clauses of (3.35)+(3.36) on ONE cube (`sites`, index `j`), bound factor `b`: the body of `PerCubeRegular2H` / `PerCubeRegular2`. -/
def RegBodyH {L : PeriodicLatticeExtent} (ell M b : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, CubeBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        CubeBond sites ((x, ν) : Bond L) → CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReads sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- pin: `PerCubeRegular2H` is `RegBodyH` on every class cube of its factor. -/
theorem perCubeRegular2H_iff {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    AdalyFormal.AllC.PerCubeRegular2H ell M f b k S α₀ η U ↔
      ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j → RegBodyH ell M b sites j α₀ η U := Iff.rfl

/-- pin: the r8 `PerCubeRegular2` (bound factor = cube factor) is `RegBodyH` with `b = f`. -/
theorem perCubeRegular2_iff {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    PerCubeRegular2 ell M f k S α₀ η U ↔
      ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j → RegBodyH ell M f sites j α₀ η U := Iff.rfl

/-- every cube of the family is regular with the bound `b M α (ell^j η)^{-n}` (bound factor `b`). -/
def PerCubeRegular2HQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (b k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ Q L →
    IsClassCube ell M f k S sites j → RegBodyH ell M b sites j α₀ η U

def ClassCoupledHQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (b k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOmQ ell M Q k S ∧ PerCubeRegular2HQ ell M Q b k S α₀ η U

/-- bonds constrained by the family. -/
def ClassBondQ {L : PeriodicLatticeExtent} (ell M : ℕ) (Q : CF) (k : ℕ) (S : Tower L) (e : Bond L) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeQ ell M Q k S sites j ∧ CubeBond sites e

theorem RegBodyH.mono {L : PeriodicLatticeExtent} {ell M b : ℕ} {sites : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ β η : ℝ}
    {U : LinkCfg L} (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : RegBodyH ell M b sites j α₀ η U) : RegBodyH ell M b sites j β η U := by
  obtain ⟨g, A, hc1, hc2, hc3⟩ := h
  have hcM : (0 : ℝ) ≤ (b : ℝ) * M := by positivity
  have key : ∀ p : ℕ, (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) ≤ (b : ℝ) * M * β * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro p
    have hX : (0 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ ^ p := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ hcM) hX
  exact ⟨g, A, fun e he => ⟨(hc1 e he).1, (hc1 e he).2.1, lt_of_lt_of_le (hc1 e he).2.2 (key 1)⟩,
    fun μ ν x h1 h2 => lt_of_lt_of_le (hc2 μ ν x h1 h2) (key 2),
    fun μ x h1 => lt_of_lt_of_le (hc3 μ x h1) (key 3)⟩

/-- only the product `b M α` enters. -/
theorem RegBodyH.congr_bound {L : PeriodicLatticeExtent} {ell M b b' : ℕ} {sites : Set (PeriodicLatticeSite L)} {j : ℕ} {α₀ α₀' η : ℝ}
    {U : LinkCfg L} (h : (b : ℝ) * M * α₀ = (b' : ℝ) * M * α₀') :
    RegBodyH ell M b sites j α₀ η U ↔ RegBodyH ell M b' sites j α₀' η U := by
  unfold RegBodyH
  simp only [h]

theorem PerCubeRegular2HQ.mono {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Q : CF} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : PerCubeRegular2HQ ell M Q b k S α₀ η U) : PerCubeRegular2HQ ell M Q b k S β η U :=
  fun f sites j hm hq => (h f sites j hm hq).mono hη hαβ

theorem ClassCoupledHQ.mono {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Q : CF} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : ClassCoupledHQ ell M Q b k S α₀ η U) : ClassCoupledHQ ell M Q b k S β η U :=
  ⟨h.1, h.2.mono hη hαβ⟩

theorem ClassCoupledHQ.plaq_gaugeΦ {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Q : CF} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledHQ ell M Q b k S α₀ η U)
    (p : PeriodicLatticePlaquette L) (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) :
    PlaqGaugeAt ell M b α₀ η U p := by
  obtain ⟨sites, j, hqQ, hcb⟩ := h.1.2 p hp
  obtain ⟨f, hm, hq⟩ := hqQ
  obtain ⟨g, A, hA, -, -⟩ := h.2 f sites j hm hq
  exact ⟨g, A, j, fun e he => hA e (hcb e he)⟩

/-- rescale the cube factor: `RegBodyH` depends on `(b, α)` only through `b M α`. -/
theorem RegBodyH.toFactor {L : PeriodicLatticeExtent} {ell M b f : ℕ} (hf : 0 < f) {sites : Set (PeriodicLatticeSite L)} {j : ℕ}
    {α₀ η : ℝ} {U : LinkCfg L} (h : RegBodyH ell M b sites j α₀ η U) :
    RegBodyH ell M f sites j ((b : ℝ) * α₀ / f) η U :=
  (RegBodyH.congr_bound (b := b) (b' := f) (α₀ := α₀) (α₀' := (b : ℝ) * α₀ / f)
    (AdalyFormal.AllC.bound_eq (M := M) (b := b) hf α₀).symm).1 h

end MXQ.AllC

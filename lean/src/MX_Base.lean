import AC_Base
import AC_CF
import AC_GE2
import ZR8Class

/-!
# MX_Base -- the MIXED per-cube-factor class (lane mixed_20261017)

CMP99b p.396 (page image corpus/renders/CMP99b_p396-08.png): "for an arbitrary cube □ of the described above class ... if the index of □ is j, then
|A| < O(1)Mα₀(L^jη)^{-1} ... where O(1)M is a size of □ in T_{L^{-j}}".  The factor O(1) of a cube is its side divided by M ℓ^j: it is a property of the cube.

`Φ : Set ℕ` is the set of admitted cube factors (every member ≥ 10).  The mixed class is ALL described cubes whose factor lies in Φ:
* `IsClassCubeΦ ell M Φ k S sites j := ∃ f ∈ Φ, IsClassCube ell M f k S sites j`,
* `CoversOmΦ` : sites and plaquettes of Ω₀ lie in (resp. have all four boundary bonds in) one cube of the mixed class,
* `PerCubeRegular2HΦ ell M Φ b k S α η U := ∀ f ∈ Φ, PerCubeRegular2H ell M f b k S α η U` (each cube regular at ITS OWN factor f; bound factor b),
* `ClassCoupledHΦ := CoversOmΦ ∧ PerCubeRegular2HΦ`.
`Φ = {c}` is the fixed-factor class `ClassCoupled ell M c` (proved: `classCoupledHΦ_single`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace MXP.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.AllC (PerCubeRegular2H ClassCoupledH)

/-- admitted cube factors are numbers ≥ 10 (p.396: "Here O(1) will mean a number ≥ 10"). -/
class CubeFactorSet (Φ : Set ℕ) : Prop where
  ge : ∀ f ∈ Φ, 10 ≤ f

theorem CubeFactorSet.pos {Φ : Set ℕ} [h : CubeFactorSet Φ] {f : ℕ} (hf : f ∈ Φ) : 0 < f := by
  have := h.ge f hf; omega

/-- a class cube whose factor is one of the admitted factors. -/
def IsClassCubeΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L)
    (sites : Set (PeriodicLatticeSite L)) (j : ℕ) : Prop :=
  ∃ f ∈ Φ, IsClassCube ell M f k S sites j

/-- sites of `Ω₀` covered by mixed class cubes. -/
def CoversOmcΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeΦ ell M Φ k S sites j ∧ x ∈ sites

/-- plaquettes of `Ω₀` with all four boundary bonds in one mixed class cube. -/
def CoversPlaqΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeΦ ell M Φ k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e

def CoversOmΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) : Prop :=
  CoversOmcΦ ell M Φ k S ∧ CoversPlaqΦ ell M Φ k S

/-- every cube of the mixed class is regular with ITS OWN factor `f` (bound factor `b`). -/
def PerCubeRegular2HΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (b k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ f ∈ Φ, PerCubeRegular2H ell M f b k S α₀ η U

def ClassCoupledHΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (b k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOmΦ ell M Φ k S ∧ PerCubeRegular2HΦ ell M Φ b k S α₀ η U

/-- bonds constrained by the mixed class. -/
def ClassBondΦ {L : PeriodicLatticeExtent} (ell M : ℕ) (Φ : Set ℕ) (k : ℕ) (S : Tower L) (e : Bond L) : Prop :=
  ∃ f ∈ Φ, AdalyFormal.StatementLaneR8.ClassBond ell M f k S e

theorem IsClassCubeΦ.of_mem {L : PeriodicLatticeExtent} {ell M f k j : ℕ} {Φ : Set ℕ} {S : Tower L}
    {sites : Set (PeriodicLatticeSite L)} (hf : f ∈ Φ) (h : IsClassCube ell M f k S sites j) :
    IsClassCubeΦ ell M Φ k S sites j := ⟨f, hf, h⟩

theorem PerCubeRegular2HΦ.at {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : PerCubeRegular2HΦ ell M Φ b k S α₀ η U) (hf : f ∈ Φ) : PerCubeRegular2H ell M f b k S α₀ η U := h f hf

theorem PerCubeRegular2HΦ.mono {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : PerCubeRegular2HΦ ell M Φ b k S α₀ η U) :
    PerCubeRegular2HΦ ell M Φ b k S β η U :=
  fun f hf => AdalyFormal.AllC.PerCubeRegular2H.mono hη hαβ (h f hf)

theorem ClassCoupledHΦ.mono {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : ClassCoupledHΦ ell M Φ b k S α₀ η U) :
    ClassCoupledHΦ ell M Φ b k S β η U := ⟨h.1, h.2.mono hη hαβ⟩

/-- the singleton set is the fixed-factor hybrid class (both directions). -/
theorem isClassCubeΦ_single {L : PeriodicLatticeExtent} {ell M c k j : ℕ} {S : Tower L} {sites : Set (PeriodicLatticeSite L)} :
    IsClassCubeΦ ell M ({c} : Set ℕ) k S sites j ↔ IsClassCube ell M c k S sites j := by
  constructor
  · rintro ⟨f, hf, h⟩
    rw [Set.mem_singleton_iff] at hf; subst hf; exact h
  · intro h; exact ⟨c, rfl, h⟩

theorem classCoupledHΦ_single {L : PeriodicLatticeExtent} {ell M c b k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledHΦ ell M ({c} : Set ℕ) b k S α₀ η U ↔ ClassCoupledH ell M c b k S α₀ η U := by
  unfold ClassCoupledHΦ ClassCoupledH CoversOmΦ CoversOmcΦ CoversPlaqΦ PerCubeRegular2HΦ
    AdalyFormal.StatementLane2.CoversOm0p AdalyFormal.StatementLane2.CoversOm0c AdalyFormal.StatementLane2.CoversPlaqOm0c
  simp only [isClassCubeΦ_single, Set.mem_singleton_iff, forall_eq]

/-- the ORIGINAL class of factor `c` (bound factor `c`) is a mixed class: `Φ = {c}`. -/
theorem classCoupled_toΦ {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) : ClassCoupledHΦ ell M ({c} : Set ℕ) c k S α₀ η U :=
  classCoupledHΦ_single.2 h

/-- `gchart_of_cubeH` for a cube of the mixed class. -/
theorem gchart_of_cubeHΦ {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : PerCubeRegular2HΦ ell M Φ b k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCubeΦ ell M Φ k S sites j)
    (hsm : (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ + (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) :
    ∃ g : PeriodicLatticeSite L → AdalyFormal.Balaban.SuTwoLogExp.SU2,
      AdalyFormal.M2Glue2.GChart U g sites ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)
        ((1 + 4 * ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)) * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2)) := by
  obtain ⟨f, hf, hq⟩ := hq
  exact AdalyFormal.AllC.gchart_of_cubeH hη (hP f hf) hq hsm hell (CubeFactorSet.pos hf)

/-- `chartOn_of_cubeH` for a cube of the mixed class. -/
theorem chartOn_of_cubeHΦ {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Φ : Set ℕ} [CubeFactorSet Φ] {S : Tower L} (hell : 1 ≤ ell) {α₀ η : ℝ}
    (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2HΦ ell M Φ b k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {idx : ℕ} (hq : IsClassCubeΦ ell M Φ k S sites idx)
    {i : ℕ} (hi : i ≤ idx) {w : PeriodicLatticeSite L} {r : ℕ}
    (hball : ∀ y : PeriodicLatticeSite L, pdist w y ≤ r + 1 → y ∈ sites) :
    AdalyFormal.M2Route.ChartOn ell U η ((b : ℝ) * M * α₀) i w r := by
  obtain ⟨f, hf, hq⟩ := hq
  exact AdalyFormal.AllC.chartOn_of_cubeH hell hη hα (hP f hf) hq hi hball (CubeFactorSet.pos hf)

/-- the coupling theorem for the mixed hybrid class: every plaquette of `Ω₀` is gauge-trivialised by ONE `g` (of a cube whose factor lies in Φ), bound factor `b`. -/
theorem ClassCoupledHΦ.plaq_gaugeΦ {L : PeriodicLatticeExtent} {ell M b k : ℕ} {Φ : Set ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupledHΦ ell M Φ b k S α₀ η U)
    (p : PeriodicLatticePlaquette L) (hp : ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) :
    PlaqGaugeAt ell M b α₀ η U p := by
  obtain ⟨sites, j, hqΦ, hcb⟩ := h.1.2 p hp
  obtain ⟨f, hf, hq⟩ := hqΦ
  obtain ⟨g, A, hA, -, -⟩ := h.2 f hf sites j hq
  exact ⟨g, A, j, fun e he => hA e (hcb e he)⟩

end MXP.AllC
#print axioms MXP.AllC.classCoupledHΦ_single
#print axioms MXP.AllC.gchart_of_cubeHΦ
#print axioms MXP.AllC.chartOn_of_cubeHΦ

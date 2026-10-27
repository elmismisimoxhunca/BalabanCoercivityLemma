import ZR6A
import GG5
import MR3
import M1B

/-!
# AC_Base -- the HYBRID class `ClassCoupledH` (lane allc_20261016)

`PerCubeRegular2H ell M f b k S α η U` : exactly `PerCubeRegular2 ell M f k S α η U` (ZR2A) except that the printed bound `f M α (ell^j η)⁻ⁿ`
is written with an independent bound factor `b`: class cubes are boxes of side `f * M * ell^j` (CUBE factor `f`), the bounds are `b * M * α * (ell^j η)⁻ⁿ`
(BOUND factor `b`).  `ClassCoupledH ell M f b k S α η U := CoversOm0p ell M f k S ∧ PerCubeRegular2H ell M f b k S α η U`.

* `PerCubeRegular2H.congr_bound` : only the product `b * M * α` matters.
* `PerCubeRegular2.toH` / `PerCubeRegular2H.toOrig` : `PerCubeRegular2 ell M f .. α ..  <->  PerCubeRegular2H ell M f b .. (f*α/b) ..` (`b > 0`).
* `ClassCoupled.toH` : `ClassCoupled ell M c k S α η U -> ClassCoupledH ell M c 12 k S (c*α/12) η U` with `12 * M * (c*α/12) = c * M * α`.
Nothing here proves the lemma.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.AllC

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

/-- the cube factor is "a number >= 10" (CMP99b p.396); carried as an instance so that the transcribed lemmas need no extra plumbing. -/
class CubeFactor (fc : ℕ) : Prop where
  ge : 10 ≤ fc

theorem CubeFactor.pos {fc : ℕ} [h : CubeFactor fc] : 0 < fc := by have := h.ge; omega

/-- hybrid per-cube regularity: cubes of factor `f`, bounds with factor `b`. -/
def PerCubeRegular2H {L : PeriodicLatticeExtent} (ell M f b k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
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

/-- hybrid class hypothesis: coverage at cube factor `f`, regularity with bound factor `b`. -/
def ClassCoupledH {L : PeriodicLatticeExtent} (ell M f b k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M f k S ∧ PerCubeRegular2H ell M f b k S α₀ η U

/-- the hybrid class with `b = f` IS the original class. -/
theorem perCubeRegular2H_self {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    PerCubeRegular2H ell M f f k S α₀ η U ↔ PerCubeRegular2 ell M f k S α₀ η U := Iff.rfl

theorem classCoupledH_self {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledH ell M f f k S α₀ η U ↔ ClassCoupled ell M f k S α₀ η U := Iff.rfl

/-- only the product `b * M * α₀` enters the bounds. -/
theorem PerCubeRegular2H.congr_bound {L : PeriodicLatticeExtent} {ell M f b b' k : ℕ} {S : Tower L} {α₀ α₀' η : ℝ}
    {U : LinkCfg L} (h : (b : ℝ) * M * α₀ = (b' : ℝ) * M * α₀') :
    PerCubeRegular2H ell M f b k S α₀ η U ↔ PerCubeRegular2H ell M f b' k S α₀' η U := by
  unfold PerCubeRegular2H
  simp only [h]

theorem ClassCoupledH.congr_bound {L : PeriodicLatticeExtent} {ell M f b b' k : ℕ} {S : Tower L} {α₀ α₀' η : ℝ}
    {U : LinkCfg L} (h : (b : ℝ) * M * α₀ = (b' : ℝ) * M * α₀') :
    ClassCoupledH ell M f b k S α₀ η U ↔ ClassCoupledH ell M f b' k S α₀' η U := by
  unfold ClassCoupledH
  rw [PerCubeRegular2H.congr_bound h]

/-- entry: the original class at cube/bound factor `c` is the hybrid class with bound factor `12` at `c α₀ / 12`. -/
theorem ClassCoupled.toH {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (h : ClassCoupled ell M c k S α₀ η U) :
    ClassCoupledH ell M c 12 k S ((c : ℝ) * α₀ / 12) η U := by
  refine (ClassCoupledH.congr_bound (b := c) (b' := 12) (α₀ := α₀) (α₀' := (c : ℝ) * α₀ / 12) ?_).1 h
  push_cast; ring

/-- exit: from the hybrid class with bound factor `b > 0` back to the original class at `b α / c`... (cube factor `f`, original bound factor `f`). -/
theorem ClassCoupledH.toOrig {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hf : 0 < f) (h : ClassCoupledH ell M f b k S α₀ η U) :
    ClassCoupled ell M f k S ((b : ℝ) * α₀ / f) η U := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  refine (ClassCoupledH.congr_bound (b := b) (b' := f) (α₀ := α₀) (α₀' := (b : ℝ) * α₀ / f) ?_).1 h
  field_simp

/-- monotone in the class constant. -/
theorem PerCubeRegular2H.mono {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : PerCubeRegular2H ell M f b k S α₀ η U) :
    PerCubeRegular2H ell M f b k S β η U := by
  intro sites j hq
  obtain ⟨g, A, hc1, hc2, hc3⟩ := h sites j hq
  have hcM : (0 : ℝ) ≤ (b : ℝ) * M := by positivity
  have key : ∀ p : ℕ, (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ p) ≤ (b : ℝ) * M * β * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
    intro p
    have hX : (0 : ℝ) ≤ ((ell : ℝ) ^ j * η)⁻¹ ^ p := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαβ hcM) hX
  exact ⟨g, A, fun e he => ⟨(hc1 e he).1, (hc1 e he).2.1, lt_of_lt_of_le (hc1 e he).2.2 (key 1)⟩,
    fun μ ν x h1 h2 => lt_of_lt_of_le (hc2 μ ν x h1 h2) (key 2),
    fun μ x h1 => lt_of_lt_of_le (hc3 μ x h1) (key 3)⟩

theorem ClassCoupledH.mono {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ β η : ℝ} {U : LinkCfg L}
    (hη : 0 ≤ η) (hαβ : α₀ ≤ β) (h : ClassCoupledH ell M f b k S α₀ η U) :
    ClassCoupledH ell M f b k S β η U := ⟨h.1, h.2.mono hη hαβ⟩

/-- the rescaled constant: `f * M * (b * α / f) = b * M * α`. -/
theorem bound_eq {f b M : ℕ} (hf : 0 < f) (α : ℝ) : (f : ℝ) * M * ((b : ℝ) * α / f) = (b : ℝ) * M * α := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  field_simp

theorem PerCubeRegular2H.toOrig {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hf : 0 < f) (h : PerCubeRegular2H ell M f b k S α₀ η U) :
    PerCubeRegular2 ell M f k S ((b : ℝ) * α₀ / f) η U :=
  (PerCubeRegular2H.congr_bound (b := b) (b' := f) (α₀ := α₀) (α₀' := (b : ℝ) * α₀ / f)
    (bound_eq hf α₀).symm).1 h

theorem PerCubeRegular2.toH' {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hb : 0 < b) (h : PerCubeRegular2 ell M f k S α₀ η U) :
    PerCubeRegular2H ell M f b k S ((f : ℝ) * α₀ / b) η U :=
  (PerCubeRegular2H.congr_bound (b := f) (b' := b) (α₀ := α₀) (α₀' := (f : ℝ) * α₀ / b)
    (bound_eq hb α₀).symm).1 h

/-- `gchart_of_cube` (GG5) for the hybrid class. -/
theorem gchart_of_cubeH {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} {α₀ η : ℝ} (hη : 0 < η)
    {U : LinkCfg L} (hP : PerCubeRegular2H ell M f b k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {j : ℕ} (hq : IsClassCube ell M f k S sites j)
    (hsm : (b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹ + (b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2 ≤ 1)
    (hell : 0 < ell) (hf : 0 < f) :
    ∃ g : PeriodicLatticeSite L → AdalyFormal.Balaban.SuTwoLogExp.SU2,
      AdalyFormal.M2Glue2.GChart U g sites ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)
        ((1 + 4 * ((b : ℝ) * M * α₀ * ((ell : ℝ) ^ j)⁻¹)) * ((b : ℝ) * M * α₀ * (((ell : ℝ) ^ j)⁻¹) ^ 2)) := by
  have e := bound_eq (M := M) (b := b) hf α₀
  have := AdalyFormal.M2Glue2.gchart_of_cube hη (hP.toOrig hf) hq (by rw [e]; exact hsm) hell
  rwa [e] at this

/-- `chartOn_of_cube` (MR3) for the hybrid class. -/
theorem chartOn_of_cubeH {L : PeriodicLatticeExtent} {ell M f b k : ℕ} {S : Tower L} (hell : 1 ≤ ell) {α₀ η : ℝ}
    (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2H ell M f b k S α₀ η U)
    {sites : Set (PeriodicLatticeSite L)} {idx : ℕ} (hq : IsClassCube ell M f k S sites idx)
    {i : ℕ} (hi : i ≤ idx) {w : PeriodicLatticeSite L} {r : ℕ}
    (hball : ∀ y : PeriodicLatticeSite L, pdist w y ≤ r + 1 → y ∈ sites) (hf : 0 < f) :
    AdalyFormal.M2Route.ChartOn ell U η ((b : ℝ) * M * α₀) i w r := by
  have e := bound_eq (M := M) (b := b) hf α₀
  have hα' : 0 ≤ (b : ℝ) * α₀ / f := by positivity
  have := AdalyFormal.M2Route.chartOn_of_cube hell hη hα' (hP.toOrig hf) hq hi hball
  rwa [e] at this

/-- `M1Regular` depends on `(f, α)` only through `f * M * α`. -/
theorem m1Regular_congr_bound {L : PeriodicLatticeExtent} {ell M f f' k : ℕ} {S : Tower L} {α α' η : ℝ} {V : LinkCfg L}
    (h : (f : ℝ) * M * α = (f' : ℝ) * M * α') :
    AdalyFormal.M1.M1Regular ell M f k S α η V ↔ AdalyFormal.M1.M1Regular ell M f' k S α' η V := by
  unfold AdalyFormal.M1.M1Regular AdalyFormal.M1.M1Bounds
  simp only [h]

end AdalyFormal.AllC

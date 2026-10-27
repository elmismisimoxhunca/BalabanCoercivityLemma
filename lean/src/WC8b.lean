import WC8a
import WC7e

/-!
# WC8b -- **`qs_injective_class`**: `Q_U*` injective at the PRINTED per-cube class `PerCubeRegular2` (M2 W6 lane)

* `cubeChart_of_class` : the printed class (clauses 1, 2) on a class cube of index `i` IS a `CubeChart` on `CubeBond sites`
  with `c1 = a X`, `c2 = a X²`, `a = f M α₀`, `X = (ℓ^i η)⁻¹` (no global gauge).
* `ConeAt ell M f k S z j` : `Ball z (36 ℓ^{j+1})` lies in a class cube of index `i ≥ j - 1` (`j ≤ i + 1`).
* `ConeInCube` : this for every row (`j` = level, `z` = row base).
* `qs_injective_class` : `ConeInCube` + `PerCubeRegular2` + numerics  ==>  `Q_U*` injective.  No global gauge, no energy norm.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist IsClassCube CubeBond)
open AdalyFormal.StatementLane2 (PerCubeRegular2)
open AdalyFormal.StatementLaneR8 (Ball pdist_triangle)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.CurvBlock (CubeChart)
open AdalyFormal.W6

/-- **the printed class on a class cube is a cube chart** (clauses 1 and 2; scales of index `i`). -/
theorem cubeChart_of_class {L : PeriodicLatticeExtent} {ell M f k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hP : PerCubeRegular2 ell M f k S α₀ η U) {sites : Set (PeriodicLatticeSite L)} {i : ℕ}
    (hq : IsClassCube ell M f k S sites i) :
    Nonempty (CubeChart U (fun b : Bond L => CubeBond sites b) η
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)) ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 2))) := by
  obtain ⟨g, A, hc1, hc2, -⟩ := hP sites i hq
  exact ⟨⟨g, A, fun e he => ⟨(hc1 e he).1, (hc1 e he).2.1, (hc1 e he).2.2⟩, fun μ ν x h1 h2 => hc2 μ ν x h1 h2⟩⟩

/-- the row-cone condition at a row base `z` of level `j`: `Ball z (36 ℓ^{j+1})` lies in a class cube of index `i ≥ j - 1`. -/
def ConeAt {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L) (z : PeriodicLatticeSite L) (j : ℕ) : Prop :=
  ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M f k S sites i ∧ j ≤ i + 1 ∧
    Ball z (36 * ell ^ (j + 1)) ⊆ sites

/-- the cone condition for every row of the tower geometry -/
def ConeInCube (ell M f k : ℕ) {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell k Lu)) : Prop :=
  ∀ p : BIdx (geomOf ell k S), ConeAt ell M f k S p.2.1.1 (p.1 : ℕ)

/-- the regional class: blocked links over the cone, from a cube of index `≥ j' - 2` -/
def clsEps (ell : ℕ) (a : ℝ) (j' l : ℕ) : ℝ :=
  (ell : ℝ) ^ l * ((4 * Real.pi + 4) * a / (ell : ℝ) ^ (j' - 2))
    + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * a / (ell : ℝ) ^ (2 * (j' - 2))))

theorem clsEps_nonneg (ell : ℕ) {a : ℝ} (ha : 0 ≤ a) (j' l : ℕ) : 0 ≤ clsEps ell a j' l := by
  unfold clsEps
  have := Real.pi_pos
  positivity

/-- monotonicity in the cube index: the blocked-link bound at index `i ≥ i0` is below the bound at `i0`. -/
theorem link_bound_mono {ell : ℕ} (hell : 0 < ell) {ρ : ℝ} (hρ : 0 ≤ ρ) {i i0 : ℕ} (hi : i0 ≤ i) (l : ℕ) :
    (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ i) + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i)))
      ≤ (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ i0) + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i0))) := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hlp : (0 : ℝ) < ell := by exact_mod_cast hell
  have h1 : ρ / (ell : ℝ) ^ i ≤ ρ / (ell : ℝ) ^ i0 :=
    div_le_div_of_nonneg_left hρ (pow_pos hlp i0) (pow_le_pow_right₀ hl1 hi)
  have h2 : ρ / (ell : ℝ) ^ (2 * i) ≤ ρ / (ell : ℝ) ^ (2 * i0) :=
    div_le_div_of_nonneg_left hρ (pow_pos hlp (2 * i0)) (pow_le_pow_right₀ hl1 (by omega))
  have hp := Real.pi_pos
  have e1 : (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ i) ≤ (ell : ℝ) ^ l * (ρ / (ell : ℝ) ^ i0) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e2 : ((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i)) ≤ ((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i0)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 3 * Real.pi)
  exact add_le_add e1 e3

/-- the smallness input of `tower_link_cube`, from the single smallness `4·10^6 ℓ⁴ ρ ≤ 1` and `l ≤ i + 1`. -/
theorem hsm_of {ell : ℕ} (hell : 0 < ell) {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : 4000000 * (ell : ℝ) ^ 4 * ρ ≤ 1) {i l : ℕ}
    (hl : l ≤ i + 1) :
    4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i))) ≤ 1 := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hlp : (0 : ℝ) < ell := by exact_mod_cast hell
  have hq : ((ell : ℝ) ^ 2) ^ l ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * i) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hl1 (by omega)
  have hpos : (0 : ℝ) < (ell : ℝ) ^ (2 * i) := pow_pos hlp _
  have h1 : ((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i)) ≤ (ell : ℝ) ^ 2 * ρ := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    calc ((ell : ℝ) ^ 2) ^ l * ρ ≤ ((ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * i)) * ρ := mul_le_mul_of_nonneg_right hq hρ
      _ = (ell : ℝ) ^ 2 * ρ * (ell : ℝ) ^ (2 * i) := by ring
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4000000 * (ell : ℝ) ^ 2)
  calc 4000000 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ 2) ^ l * (ρ / (ell : ℝ) ^ (2 * i)))
      ≤ 4000000 * (ell : ℝ) ^ 2 * ((ell : ℝ) ^ 2 * ρ) := h2
    _ = 4000000 * (ell : ℝ) ^ 4 * ρ := by ring
    _ ≤ 1 := hs

section main
variable {ell M R f k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **the class gives `ChartHyp`**: per-row gauges with the blocked-link closeness `clsEps` on the cone, from `ConeInCube`. -/
theorem chartHyp_of_class (hell2 : 2 ≤ ell) (hT3 : ∀ μ, 3 ≤ Lu μ + 1) {α₀ η : ℝ} (hα0 : 0 ≤ α₀) (hη : 0 < η)
    (ha1 : (f : ℝ) * M * α₀ ≤ 1) (hsm4 : 4000000 * (ell : ℝ) ^ 4 * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀)) ≤ 1)
    (U : LinkCfg (scaleUp ell k Lu)) (hP : PerCubeRegular2 ell M f k S α₀ η U) (hcone : ConeInCube ell M f k S) :
    ∃ γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu),
      ChartHyp ell k Lu S U γ (clsEps ell ((f : ℝ) * M * α₀)) := by
  have hell : 0 < ell := by omega
  have ha0 : 0 ≤ (f : ℝ) * M * α₀ := by positivity
  have key : ∀ p : BIdx (geomOf ell k S), ∃ g : GaugeFn (scaleUp ell k Lu),
      ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
        ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
          frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform g U) l (z, μ) : SU2) : M2) - 1)
            ≤ clsEps ell ((f : ℝ) * M * α₀) j' l := by
    intro p
    obtain ⟨sites, i, hq, hi, hsub⟩ := hcone p
    obtain ⟨K⟩ := cubeChart_of_class hP hq
    refine ⟨K.g, fun j' hj1 hj2 l hlk hlj z hz hza μ => ?_⟩
    have hl : l ≤ (p.1 : ℕ) := by omega
    have hpow : ell ^ l ≤ ell ^ ((p.1 : ℕ) + 1) := Nat.pow_le_pow_right hell (by omega)
    have hcone' : ∀ w, pdist z w ≤ 14 * ell ^ l → w ∈ sites := by
      intro w hw
      apply hsub
      have h1 : pdist p.2.1.1 z ≤ 20 * ell ^ ((p.1 : ℕ) + 1) := hz
      have h2 := pdist_triangle p.2.1.1 z w
      show pdist p.2.1.1 w ≤ 36 * ell ^ ((p.1 : ℕ) + 1)
      omega
    have hl' : l ≤ i + 1 := by omega
    have hsm := hsm_of hell (by positivity : (0 : ℝ) ≤ (4 * Real.pi + 4) * ((f : ℝ) * M * α₀)) hsm4 hl'
    have h := tower_link_cube hell2 hell hT3 U sites i K hη ha0 ha1 l hlk hsm z hza μ hcone'
    have h' : frobNorm (((bgTower (GF ell k Lu) (periodicGaugeTransform K.g U) l (z, μ) : SU2) : M2) - 1)
        ≤ (ell : ℝ) ^ l * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ i)
          + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ l * ((4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ (2 * i))) := h
    refine h'.trans ?_
    unfold clsEps
    exact link_bound_mono hell (by positivity) (by omega) l
  choose γ hγ using key
  exact ⟨γ, fun p j' h1 h2 l hlk hlj z hz hza μ => hγ p j' h1 h2 l hlk hlj z hz hza μ⟩

end main

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.cubeChart_of_class
#print axioms AdalyFormal.M2W6.link_bound_mono
#print axioms AdalyFormal.M2W6.hsm_of
#print axioms AdalyFormal.M2W6.chartHyp_of_class

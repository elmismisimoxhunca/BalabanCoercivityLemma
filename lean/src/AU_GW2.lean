import AU_CUT
import GW2

open AdalyFormal.AllU (M1BoundsU M1RegularU)

/-! AU copy of GW2: M1Regular -> M1RegularU, affected declarations only (lane allc_20261016, uniform-in-c route). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1GaugeW4

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible scaleUp HT)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf CoarseLattice Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.CurvBlock (dv CubeChart cube_link cube_plaq pw)
open AdalyFormal.M1 (bstrat le_bstrat_of_mem)

variable {L : PeriodicLatticeExtent}

/-- the M1 witness, restricted to the bonds of `Ω_{j0}`, is a CB9 `CubeChart` with the printed stratum-`j0` scales. -/
def m1ChartU {ell M f k : ℕ} (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1BoundsU S ell M f k α₀ η A) (j0 : ℕ) (hj0 : j0 ≤ k) :
    CubeChart U (BIn S j0) η ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1))
      ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 2)) where
  g := g
  A := A
  hA := fun e he => ⟨hB.1 e, hU e, hB.2.1 e j0 (le_bstrat_of_mem hj0 e he.1 he.2)⟩
  hD := fun μ ν x h1 h2 =>
    hB.2.2.1 μ ν x j0 (le_bstrat_of_mem hj0 _ h1.1 h1.2) (le_bstrat_of_mem hj0 _ h2.1 h2.2)

section witness
variable {ell M f k : ℕ}

theorem m1_linkU (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1BoundsU S ell M f k α₀ η A)
    (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) (j0 : ℕ) (hj0 : j0 ≤ k) (b : Bond L)
    (h1 : b.1 ∈ S.Om j0) (h2 : periodicLatticeShift b.1 b.2 ∈ S.Om j0) :
    dv (periodicGaugeTransform g U b) ≤ (4 * Real.pi + 4) * ((f : ℝ) * M * α₀) / (ell : ℝ) ^ j0 := by
  have hK := cube_link hη (m1ChartU S U g A hU hB j0 hj0) b ⟨h1, h2⟩
  have hp : (0 : ℝ) < (ell : ℝ) ^ j0 := pow_pos (by exact_mod_cast hell) j0
  have e1 : η * ((f : ℝ) * M * α₀ * (((ell : ℝ) ^ j0 * η)⁻¹ ^ 1)) = (f : ℝ) * M * α₀ / (ell : ℝ) ^ j0 := by
    field_simp
  rw [e1] at hK
  refine hK.trans ?_
  apply div_le_div_of_nonneg_right _ hp.le
  have := Real.pi_pos
  nlinarith

end witness

section agree
variable {ell M R k : ℕ} {S : Tower L}

end agree

section regimeU
variable {ell M R f k : ℕ}

/-- `hlink` of lane C at `U^g`, in the form `rho1 / ell^j0`. -/
theorem hlink_M1U (S : Tower L) {α₀ η : ℝ} (U : LinkCfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ e : Bond L, ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = NormedSpace.exp (((η : ℂ) * Complex.I) • A e))
    (hB : M1BoundsU S ell M f k α₀ η A) (hη : 0 < η) (hell : 1 ≤ ell) (ha0 : 0 ≤ (f : ℝ) * M * α₀) :
    ∀ j0, j0 ≤ k → ∀ b : Bond L, b.1 ∈ S.Om j0 → periodicLatticeShift b.1 b.2 ∈ S.Om j0 →
      dv (periodicGaugeTransform g U b) ≤ AdalyFormal.TowerLoc.rho1 f M α₀ / (ell : ℝ) ^ j0 :=
  fun j0 hj0 b h1 h2 => m1_linkU S U g A hU hB hη hell ha0 j0 hj0 b h1 h2

end regimeU

end AdalyFormal.M1GaugeW4


import SG16
import OGP0

/-!
# OG1 -- the single geometric/gauge statement `BallCharts` (lane m2_onegap_20261015)

`RegionChart R ell M f α η i U` : on the bonds of the region `R` (both endpoints in `R`) there are a gauge `g` and a field `A` with `U^g = exp(iηA)`, `A` Hermitian traceless, and the
two first clauses of the printed regime at the SINGLE scale `ℓ^i`:  `‖A‖ < f M α (ℓ^i η)⁻¹`,  `‖η⁻¹ ΔA‖ < f M α (ℓ^i η)⁻²`  (no third-order clause, no stratum scaling).
`BallChartsAt ell M k S U C α₀ η` : for every level `j ≤ k`, every centre `w` within `3 M ℓ^j` of a point of `Ω_j` (an anchor or a patch corner), and every radius `r ≤ 7 M ℓ^j` that does not wrap the
torus (`2 r + 2 ≤ L_σ + 1`) and such that `Ball w r` lies in `Ω_{j-1}`, misses `Ω_{j+2}`, and is either small (`r ≤ 1000 ℓ^{j+1}`) or misses `Ω_{j+1}`:
the printed class `U` carries a `RegionChart` on `Ball w r` at scale `ℓ^{j-1}` and constant `C α₀`.
`BallCharts` : the `ClassFam` shape (constant `C = C(ℓ,M,R) ≥ 1` chosen before `k`, `Λ` nonempty).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.OneGap

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (Tower Admissible scaleUp TorusOK pdist HT CubeBond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.M2Skel (ClassFam)

variable {L : PeriodicLatticeExtent}

/-- the class data of one region at one scale, clauses 1-2 only -/
structure CubeData12 (ell M f : ℕ) (α η : ℝ) (sites : Set (PeriodicLatticeSite L)) (i : ℕ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ) : Prop where
  ht : ∀ e : Bond L, CubeBond sites e → HT (A e)
  c1 : ∀ e : Bond L, CubeBond sites e → frobNorm (A e) < (f : ℝ) * M * α * (((ell : ℝ) ^ i * η)⁻¹ ^ 1)
  c2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L), CubeBond sites ((x, ν) : Bond L) →
      CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
      frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) < (f : ℝ) * M * α * (((ell : ℝ) ^ i * η)⁻¹ ^ 2)

/-- a region chart at one scale -/
def RegionChart (R : Set (PeriodicLatticeSite L)) (ell M f : ℕ) (α η : ℝ) (i : ℕ) (U : LinkCfg L) : Prop :=
  ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ e : Bond L, CubeBond R e →
      ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
        = NormedSpace.exp (((η : ℂ) * Complex.I) • A e)) ∧
    CubeData12 ell M f α η R i A

/-- the region-chart statement at ONE configuration -/
def BallChartsAt (ell M k : ℕ) (S : Tower L) (U : LinkCfg L) (C α₀ η : ℝ) : Prop :=
  ∀ j : ℕ, j ≤ k → ∀ w : PeriodicLatticeSite L, (∃ x₀ ∈ S.Om j, pdist w x₀ ≤ 3 * (M * ell ^ j)) → ∀ r : ℕ, r ≤ 7 * M * ell ^ j →
    (∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1) →
    (∀ x ∈ Ball w r, x ∈ S.Om (j - 1)) → (∀ x ∈ Ball w r, x ∉ S.Om (j + 2)) →
    (r ≤ 1000 * ell ^ (j + 1) ∨ ∀ x ∈ Ball w r, x ∉ S.Om (j + 1)) →
    RegionChart (Ball w r) ell M 12 (C * α₀) η (j - 1) U

/-- **BallCharts**: the one residual statement. -/
def BallCharts : Prop :=
  ∀ (ell : ℕ), 2 ≤ ell →
    ClassFam ell ℝ (fun _ _ C => 1 ≤ C) (fun M _ k _ C S Lam U α₀ =>
      Lam.Nonempty → BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)

end AdalyFormal.OneGap

#print axioms AdalyFormal.OneGap.BallCharts

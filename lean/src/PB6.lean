import PB1
import PB2
import PB3
import PB4c
import PB5
import GN10
import GN11
import GN13

/-!
# PB6 -- `ginv_coercive_ported`: the slice-coercivity chain GN10 `ginv_coercive_flatExt` instantiated with the PORTED inputs.

Discharged here from ported theorems (modules `PGFC*`/`PSC*`, `PSiteC*`, `PNF3`, `PB1`-`PB5`):
`hflat` (PB1: scaled flat floor, `c1 = min a 1/1000`, `nsq = ell^(2k)`), `hu`, `hPoincU`, `hPoinc1` (PB2: site coercivity / Poincare under the
tower class), `hreg` (PB4c: `regTower_of_frobSup` from the tower class + chart radius `rL`; PB4 is the NJ-faithful `regTower_of_small`, which CANNOT be imported together with the site chain, see PB4c header), `hdp` (PB3: NF4 `θ = 272 α₀` from `PlaqDef α₀ U`),
`hd` (GN11), `hc` (GN13), `hQq`, `hQdrift` (PB5), `hdrift` (GN12 `phi_drift_decomp` from the three pieces).
Remaining NAMED PREMISES (hypotheses of this theorem, not proved): FlatExt (`E1, aE, bE, hQE, hEa, hEb`), the bond-composite drift `hC1`
(plan node C1, `δm`), the plaquette-defect smallness `hpl : PlaqDef α₀ U` (curvature), the chart-radius condition `hchart` (against a chart radius `rL` of `LogReg`, `exists_chart_radius`), the tower class `hU, hT`, and the two arithmetic smallness conditions `hεa`, `hsmall`.
Standard axioms only (each declaration's printed axiom line).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.PortSlice

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.SuTwoLogExp (M2)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.SliceCoerc

theorem ginv_coercive_ported (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 < a) (Lam : Set (PeriodicLatticeSite Lu))
    -- tower class (shared by hu / Poincare / RegTower / Q' drift)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : 216 * ρ ^ 2 < 1)
    (hU : frobSupBond U ≤ ρ / (ell : ℝ) ^ k)
    (hT : ∀ i, i < k → frobSupBond (bgTower (GF ell k Lu) U i) ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k)
    (rL : ℝ) (hrL : ∀ g : M2, frobNorm (g - 1) < rL → g ∈ LogReg)
    (hchart : ∀ j, j < k → (8 * (ell : ℝ) - 6) * (ρ * (ell : ℝ) ^ j / (ell : ℝ) ^ k) < rL)
    -- plaquette defect (NF4)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    -- NAMED PREMISE C1 (bond-composite drift)
    (t δm : ℝ) (ht : 0 < t) (hδm : 0 ≤ δm)
    (hC1 : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2)
    -- NAMED PREMISE FlatExt
    (aE bE : ℝ) (haE : 0 ≤ aE) (hbE : 0 ≤ bE)
    (E1 : coarseC (GF ell k Lu) →L[ℝ] SiteL2 (scaleUp ell k Lu))
    (hQE : ∀ w, Qtop (GF ell k Lu) (trivialU _) (E1 w) = w)
    (hEa : ∀ w, ‖E1 w‖ ≤ aE * ‖w‖) (hEb : ∀ w, ‖gradL2 (trivialU _) (E1 w)‖ ≤ bE * ‖w‖)
    -- constants, pinned by equations (each a computed value, none free)
    (nsq c1 e P PU δ q ε0 : ℝ)
    (hnsq : nsq = (ell : ℝ) ^ (2 * k)) (hc1 : c1 = min a 1 / 1000)
    (he : e = (1 + t) * (272 * α₀) + (1 + 1 / t) * ((4 * Real.sqrt 2 * (ρ / (ell : ℝ) ^ k)) ^ 2 + δm ^ 2))
    (hP : P = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2))
    (hPU : PU = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2)))
    (hδ : δ = Real.sqrt 12 * (ρ / (ell : ℝ) ^ k))
    (hq : q = Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3))
    (hε0 : ε0 = q * ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * (ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k))
    (hεa : ε0 * aE < 1)
    (hsmall : nsq * ((((bE + δ * aE) / (1 - ε0 * aE)) * q) * (δ * P + (((bE + δ * aE) / (1 - ε0 * aE)) * q) * P ^ 2
        * (δ + ((bE + δ * aE) / (1 - ε0 * aE)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bE + δ * aE) / (1 - ε0 * aE)) * q) * (δ * P
        + (((bE + δ * aE) / (1 - ε0 * aE)) * q) * P ^ 2 * (δ + ((bE + δ * aE) / (1 - ε0 * aE)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hell0 : 0 < ell := by omega
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
  have hnR : 0 < (ell : ℝ) ^ k := by positivity
  have hρk : 0 ≤ ρ / (ell : ℝ) ^ k := by positivity
  have hM := mM_pos a ha ell k hell
  -- RegTower
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    regTower_of_frobSup hell0 (bgTower (GF ell k Lu) U) k (fun j => ρ * (ell : ℝ) ^ j / (ell : ℝ) ^ k) hT rL hrL hchart
  have hu := hu_ported ell k Lu hell U a ha ρ hρ hρ1 hU hT
  have hPoincU := poincare_ported ell k Lu hell U a ha ρ hρ hρ1 hU hT
  have hPoinc1 := poincare_flat ell k Lu hell a ha
  -- drift pieces
  have hc' : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ‖AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (trivialU _) x)
        - AdalyFormal.StatementLaneR6.plaqMask (plaqIn (GF ell k Lu).Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x)‖
        ≤ (4 * Real.sqrt 2 * (ρ / (ell : ℝ) ^ k)) * ‖x‖ := by
    intro x
    refine le_trans (hc_of_frobSup U _ x) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by positivity)) (norm_nonneg _)
  have hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ (272 * α₀) * ‖x‖ ^ 2 :=
    fun x => theta_ported ell k Lu U hα₀ hpl x
  have hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU _) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2 := by
    intro x
    rw [he]
    exact phi_drift_decomp ell k Lu U a ha.le t ht (4 * Real.sqrt 2 * (ρ / (ell : ℝ) ^ k)) (272 * α₀) δm hc' hdp hC1 x
  have hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖ := by
    intro f; rw [hδ]; exact hd_of_frobSup U hρk hU f
  have hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖ := by
    intro f; rw [hε0, hq]
    exact hQdrift_ported ell k Lu hell0 U (fun i => ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k) hT f
  have hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖ := by
    intro f; rw [hq]; exact hQq_ported ell k Lu hell0 U f
  have hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2) := by
    intro y; rw [hc1, hnsq]; exact hflat_ported ell k Lu hell0 a ha y
  have hn : 0 < nsq := by rw [hnsq]; positivity
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.sqrt_nonneg _
  have hPU0 : 0 ≤ PU := by rw [hPU]; exact Real.sqrt_nonneg _
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hε00 : 0 ≤ ε0 := by
    rw [hε0]
    refine mul_nonneg hq0 (Finset.sum_nonneg (fun i _ => ?_))
    have : 0 ≤ (ell : ℝ) - 1 := by linarith
    positivity
  have hPoincU' : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖ := by
    intro ν hν; rw [hPU]; exact hPoincU ν hν
  have hPoinc1' : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖ := by
    intro ν hν; rw [hP]; exact hPoinc1 ν hν
  exact ginv_coercive_flatExt ell k Lu hell0 U a Lam hreg hu PU hPU0 hPoincU' nsq c1 t e P δ q aE bE ε0 hn ht.le hP0 hδ0
    hq0 haE hbE hε00 hεa hsmall hflat hdrift hPoinc1' hd E1 hQE hEa hEb hQdrift hQq x

#print axioms ginv_coercive_ported

end AdalyFormal.PortSlice

import PB6
import FE4

/-!
# ASC1 -- `ginv_coercive_ported_FE`: PB6 `ginv_coercive_ported` with FlatExt SUPPLIED by `FlatExt.flatE` (FE3).
The FlatExt block (`E1, aE, bE, hQE, hEa, hEb`) is gone: `E1 := flatE`, `aE := aFE ell k = sqrt(729 n^3)`, `bE := bFE ell k = sqrt(78732 n)`.
Premises left: C1 (`hC1`, `δm`), the tower class (`hU, hT`: ALL-edge sup, as in PB6), `hpl`, chart radius, `hεa`, `hsmall`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.AsmM0

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
open AdalyFormal.PortSlice

theorem ginv_coercive_ported_FE (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell)
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
    -- constants, pinned by equations (each a computed value, none free)
    (nsq c1 e P PU δ q ε0 : ℝ)
    (hnsq : nsq = (ell : ℝ) ^ (2 * k)) (hc1 : c1 = min a 1 / 1000)
    (he : e = (1 + t) * (272 * α₀) + (1 + 1 / t) * ((4 * Real.sqrt 2 * (ρ / (ell : ℝ) ^ k)) ^ 2 + δm ^ 2))
    (hP : P = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2))
    (hPU : PU = Real.sqrt (max 6 (16 / (3 * a)) * ((ell : ℝ) ^ k) ^ 2 / (1 - 216 * ρ ^ 2)))
    (hδ : δ = Real.sqrt 12 * (ρ / (ell : ℝ) ^ k))
    (hq : q = Real.sqrt (1 / ((ell : ℝ) ^ k) ^ 3))
    (hε0 : ε0 = q * ∑ i ∈ Finset.range k, 6 * ((ell : ℝ) - 1) * (ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ k))
    (hεa : ε0 * AdalyFormal.FlatExt.aFE ell k < 1)
    (hsmall : nsq * ((((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * q) * (δ * P + (((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * q) * P ^ 2
        * (δ + ((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * q) * (δ * P
        + (((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * q) * P ^ 2 * (δ + ((AdalyFormal.FlatExt.bFE ell k + δ * AdalyFormal.FlatExt.aFE ell k) / (1 - ε0 * AdalyFormal.FlatExt.aFE ell k)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, (by omega : 0 < ell), fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫   := ginv_coercive_ported ell k Lu hell U a ha Lam ρ hρ hρ1 hU hT rL hrL hchart α₀ hα₀ hpl t δm ht hδm hC1
    (AdalyFormal.FlatExt.aFE ell k) (AdalyFormal.FlatExt.bFE ell k) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (AdalyFormal.FlatExt.flatE ell k Lu) (AdalyFormal.FlatExt.flatE_rightInv ell k Lu (by omega))
    (AdalyFormal.FlatExt.flatE_norm_le ell k Lu (by omega)) (AdalyFormal.FlatExt.flatE_grad_norm_le ell k Lu (by omega))
    nsq c1 e P PU δ q ε0 hnsq hc1 he hP hPU hδ hq hε0 hεa hsmall x

#print axioms ginv_coercive_ported_FE

end AdalyFormal.AsmM0

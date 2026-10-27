import GN13
import FE3

/-!
# FE4 -- the slice-coercivity chain (GN10) with FlatExt SUPPLIED (FE3), and with the drift inputs GN11/GN12/GN13 plugged in

* `aFE ell k = √(729 (ell^k)³)`, `bFE ell k = √(78732 ell^k)`: the FlatExt constants of FE3 (`n = ell^k`).
* `ginv_coercive_FE`: GN10 `ginv_coercive_flatExt` with `E1 := flatE`, `aE := aFE`, `bE := bFE`; the hypotheses
  `E1, hQE, hEa, hEb, haE, hbE` are gone.
* `ginv_coercive_FE_named`: additionally `δ = √12 · frobSupBond U` (GN11) and the `Φ` drift from GN12 with the
  curl drift `δc = 4√2 · frobSupBond U` (GN13); remaining named inputs: RegTower, hu, Poincaré on `N(Q'(U))` and on
  `N(Q'(1))`, the flat inequality `c1`, the Δ'-bound `θ`, the bond-composite drift `δm` (C1), the `Q'` drift `ε0`,
  `‖Q'_k(U)‖ ≤ q`, and the smallness `hsmall`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.FlatExt

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SliceCoerc (coarseC Qtop GF PhiF ginv_coercive_flatExt hd_of_frobSup phi_drift_decomp hc_of_frobSup)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg)
open AdalyFormal.StatementLane (scaleUp)

/-- FlatExt constant `aE = √(729 n³)`, `n = ell^k`. -/
noncomputable def aFE (ell k : ℕ) : ℝ := Real.sqrt (729 * ((ell : ℝ) ^ k) ^ 3)

/-- FlatExt constant `bE = √(78732 n)`, `n = ell^k`. -/
noncomputable def bFE (ell k : ℕ) : ℝ := Real.sqrt (78732 * (ell : ℝ) ^ k)

theorem ginv_coercive_FE (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t e P δ q ε0 : ℝ) (hn : 0 < nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (hq : 0 ≤ q) (hε0 : 0 ≤ ε0) (hεa : ε0 * aFE ell k < 1)
    (hsmall : nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ :=
  ginv_coercive_flatExt ell k Lu hell U a Lam hreg hu PU hPU hPoincU nsq c1 t e P δ q (aFE ell k) (bFE ell k) ε0
    hn ht hP hδ hq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hε0 hεa hsmall hflat hdrift hPoinc1 hd
    (flatE ell k Lu) (flatE_rightInv ell k Lu hell) (flatE_norm_le ell k Lu hell) (flatE_grad_norm_le ell k Lu hell)
    hQdrift hQq x

theorem ginv_coercive_FE_named (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t θ δm e P δ q ε0 : ℝ) (hn : 0 < nsq) (ht : 0 < t) (hP : 0 ≤ P)
    (hδdef : δ = Real.sqrt 12 * frobSupBond U)
    (hedef : e = (1 + t) * θ + (1 + 1 / t) * ((4 * Real.sqrt 2 * frobSupBond U) ^ 2 + δm ^ 2))
    (hq : 0 ≤ q) (hε0 : 0 ≤ ε0) (hεa : ε0 * aFE ell k < 1)
    (hsmall : nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdp : ∀ x : BondFnL2 (scaleUp ell k Lu),
      |AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc U (plaqIn (GF ell k Lu).Om0) x x| ≤ θ * ‖x‖ ^ 2)
    (hm : ∀ x : BondFnL2 (scaleUp ell k Lu),
      ∑ p : BIdx (GF ell k Lu), a * ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) *
        ‖(bondSectorOf (GF ell k Lu) (trivialU _)).Qfull x p - (bondSectorOf (GF ell k Lu) U).Qfull x p‖ ^ 2
        ≤ δm ^ 2 * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * (δ * P
        + (((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * q) * P ^ 2
        * (δ + ((bFE ell k + δ * aFE ell k) / (1 - ε0 * aFE ell k)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hfs : 0 ≤ frobSupBond U := frobSupBond_nonneg U
  have hδ : 0 ≤ δ := by rw [hδdef]; positivity
  have hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖ := fun f => by
    rw [hδdef]; exact hd_of_frobSup U hfs le_rfl f
  have hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2 := fun x => by
    rw [hedef]
    exact phi_drift_decomp ell k Lu U a ha t ht (4 * Real.sqrt 2 * frobSupBond U) θ δm
      (fun x => hc_of_frobSup U _ x) hdp hm x
  exact ginv_coercive_FE ell k Lu hell U a Lam hreg hu PU hPU hPoincU nsq c1 t e P δ q ε0 hn ht.le hP hδ hq hε0
    hεa hsmall hflat hdrift hPoinc1 hd hQdrift hQq x

#print axioms ginv_coercive_FE
#print axioms ginv_coercive_FE_named

end AdalyFormal.FlatExt

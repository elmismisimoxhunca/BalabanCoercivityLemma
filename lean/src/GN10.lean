import GN9

/-!
# GN10 -- the M0 `Ginv` reduction with the geometric input stated at U = 1 (FlatExt)

`ginv_coercive_flatExt`: GN8 with `hext`, `hQN1` discharged by GN9 from
FlatExt `(E1, a, b)` (flat right inverse), the gradient drift `δ` and the `Q'` drift `ε0` (`ε0 a < 1`).
Remaining named inputs: `RegTower`, `hu`, Poincare on `N(Q'(U))` (`PU`) and `N(Q'(1))` (`P`), the flat inequality `c1`,
the `Φ` drift `(t, e)`, `‖Q'_k(U)‖ ≤ q`, FlatExt, `δ`, `ε0`, and the smallness `hsmall`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.StatementLane (scaleUp)

theorem ginv_coercive_flatExt (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t e P δ q aE bE ε0 : ℝ) (hn : 0 < nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (hq : 0 ≤ q) (haE : 0 ≤ aE) (hbE : 0 ≤ bE) (hε0 : 0 ≤ ε0) (hεa : ε0 * aE < 1)
    (hsmall : nsq * ((((bE + δ * aE) / (1 - ε0 * aE)) * q) * (δ * P + (((bE + δ * aE) / (1 - ε0 * aE)) * q) * P ^ 2
        * (δ + ((bE + δ * aE) / (1 - ε0 * aE)) * ε0)) + δ) ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (E1 : coarseC (GF ell k Lu) →L[ℝ] SiteL2 (scaleUp ell k Lu))
    (hQE : ∀ w, Qtop (GF ell k Lu) (trivialU _) (E1 w) = w)
    (hEa : ∀ w, ‖E1 w‖ ≤ aE * ‖w‖) (hEb : ∀ w, ‖gradL2 (trivialU _) (E1 w)‖ ≤ bE * ‖w‖)
    (hQdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((((bE + δ * aE) / (1 - ε0 * aE)) * q) * (δ * P
        + (((bE + δ * aE) / (1 - ε0 * aE)) * q) * P ^ 2 * (δ + ((bE + δ * aE) / (1 - ε0 * aE)) * ε0)) + δ) ^ 2
        - nsq * e) / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have hpos : 0 < 1 - ε0 * aE := by linarith
  have hb' : 0 ≤ (bE + δ * aE) / (1 - ε0 * aE) := div_nonneg (by positivity) hpos.le
  exact ginv_coercive_fullTower_named ell k Lu hell U a Lam hreg hu PU hPU hPoincU nsq c1 t e P δ
    ((bE + δ * aE) / (1 - ε0 * aE)) ε0 q hn ht hP hδ hb' hε0 hq hsmall hflat hdrift hPoinc1 hd
    (hext_of_flatExt ell k Lu U E1 aE bE δ ε0 haE hbE hδ hε0 hεa hQE hEa hEb hd hQdrift) hQq
    (hQN1_of_drift ell k Lu U ε0 hQdrift) x

#print axioms ginv_coercive_flatExt

end AdalyFormal.SliceCoerc

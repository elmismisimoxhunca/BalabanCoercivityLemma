import GN7

/-!
# GN8 -- the whole conditional chain on the genuine full-tower objects at NON-flat `U`

`ginv_coercive_fullTower_named`: with `cs := (c1 - n²γ² - n²e)/((1+t) n²) > 0` (all inputs of GN7) and the inputs of GN5
(`RegTower`, `hu`, Poincare on `N(Q'(U))` with constant `PU`):
  `‖x‖² ≤ max(2/cs, 2 PU²) ⟪x, Ginv x⟫`   for the statement carrier's `IngrBParams.data`, every `x ∈ E₀`.
B0 is a theorem here (`B0_fullTower`), not an input.  Every remaining input is a named inequality on genuine operators.
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

theorem ginv_coercive_fullTower_named (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (PU : ℝ) (hPU : 0 ≤ PU)
    (hPoincU : ∀ ν ∈ NQp (GF ell k Lu) U, ‖ν‖ ≤ PU * ‖gradL2 U ν‖)
    (nsq c1 t e P δ b ε q : ℝ) (hn : 0 < nsq) (ht : 0 ≤ t) (hP : 0 ≤ P) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hsmall : nsq * ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 + nsq * e < c1)
    (hflat : ∀ y : BondFnL2 (scaleUp ell k Lu),
      c1 * ‖y‖ ^ 2 ≤ nsq * (PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) y
        + ‖Rproj (GF ell k Lu) (trivialU (scaleUp ell k Lu)) (gradAdj (trivialU (scaleUp ell k Lu)) y)‖ ^ 2))
    (hdrift : ∀ x : BondFnL2 (scaleUp ell k Lu),
      PhiF ell k Lu a (trivialU (scaleUp ell k Lu)) x ≤ (1 + t) * PhiF ell k Lu a U x + e * ‖x‖ ^ 2)
    (hPoinc1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)),
      ‖ν‖ ≤ P * ‖gradL2 (trivialU (scaleUp ell k Lu)) ν‖)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hext : ∀ w : coarseC (GF ell k Lu), ∃ f, Qtop (GF ell k Lu) U f = w ∧ ‖gradL2 U f‖ ≤ b * ‖w‖)
    (hQq : ∀ f, ‖Qtop (GF ell k Lu) U f‖ ≤ q * ‖f‖)
    (hQN1 : ∀ ν ∈ NQp (GF ell k Lu) (trivialU (scaleUp ell k Lu)), ‖Qtop (GF ell k Lu) U ν‖ ≤ ε * ‖ν‖)
    (x : ↥(bondSupp (GF ell k Lu))) :
    ‖x‖ ^ 2 ≤ max (2 / ((c1 - nsq * ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 - nsq * e)
        / (1 + t) / nsq)) (2 * PU ^ 2) *
      ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫ := by
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < c1 - nsq * ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 - nsq * e := by
    linarith
  have hcs : 0 < (c1 - nsq * ((b * q) * (δ * P + (b * q) * P ^ 2 * (δ + b * ε)) + δ) ^ 2 - nsq * e)
      / (1 + t) / nsq := div_pos (div_pos h2 h1) hn
  refine ginv_coercive_ingr ell k Lu hell U a Lam hreg hu PU hPU hPoincU _ hcs (fun y hy => ?_) x
  have h := slice_coercive_cond ell k Lu U a nsq c1 t e P δ b ε q hn.le ht hP hδ hb hε hq hflat hdrift
    hPoinc1 hd hext hQq hQN1 y hy
  unfold PhiF at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hn]
  linarith

#print axioms ginv_coercive_fullTower_named

end AdalyFormal.SliceCoerc

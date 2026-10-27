import GN8

/-!
# GN9 -- the non-flat right inverse from a FLAT one (the named geometric primitive is U-independent)

`FlatExt`: a right inverse `E1` of the FLAT top-level constraint map `Q'_k(1)` (full tower) with `‖E1 w‖ ≤ a‖w‖`,
`‖D_1 E1 w‖ ≤ b‖w‖`.  (Numerics, explore/p3,p4: the minimal-energy extension has `a² ≈ 1.55 n³`, `b² ≈ 49.6 n`.)
* `hext_of_flatExt`: FlatExt + gradient drift `δ` + `Q'` drift `ε0` (`ε0 a < 1`) ⇒ right inverse of `Q'_k(U)` with energy
  `(b + δ a)/(1 - ε0 a)` (SL1 `ext_of_rightInverse`; no Neumann series).
* `hQN1_of_drift`: `‖Q'_k(U) ν‖ ≤ ε0 ‖ν‖` on `N(Q'(1))`.
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

theorem hext_of_flatExt (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))
    (E1 : coarseC (GF ell k Lu) →L[ℝ] SiteL2 (scaleUp ell k Lu)) (a b δ ε0 : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hε0 : 0 ≤ ε0) (hεa : ε0 * a < 1)
    (hQE : ∀ w, Qtop (GF ell k Lu) (trivialU _) (E1 w) = w)
    (hEa : ∀ w, ‖E1 w‖ ≤ a * ‖w‖) (hEb : ∀ w, ‖gradL2 (trivialU _) (E1 w)‖ ≤ b * ‖w‖)
    (hd : ∀ f, ‖gradL2 (trivialU (scaleUp ell k Lu)) f - gradL2 U f‖ ≤ δ * ‖f‖)
    (hdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (w : coarseC (GF ell k Lu)) :
    ∃ f, Qtop (GF ell k Lu) U f = w ∧ ‖gradL2 U f‖ ≤ (b + δ * a) / (1 - ε0 * a) * ‖w‖ := by
  have hEbU : ∀ w, ‖gradL2 U (E1 w)‖ ≤ (b + δ * a) * ‖w‖ := by
    intro w
    have h1 : ‖gradL2 U (E1 w)‖ ≤ ‖gradL2 (trivialU _) (E1 w)‖
        + ‖gradL2 (trivialU (scaleUp ell k Lu)) (E1 w) - gradL2 U (E1 w)‖ := by
      have := norm_sub_le (gradL2 (trivialU (scaleUp ell k Lu)) (E1 w))
        (gradL2 (trivialU (scaleUp ell k Lu)) (E1 w) - gradL2 U (E1 w))
      simpa using this
    have h2 := hd (E1 w)
    have h3 := mul_le_mul_of_nonneg_left (hEa w) hδ
    nlinarith [hEb w]
  have hb' : 0 ≤ b + δ * a := by positivity
  obtain ⟨f, hf, hfD, -⟩ := ext_of_rightInverse (Qtop (GF ell k Lu) (trivialU _)) (Qtop (GF ell k Lu) U) E1
    (gradL2 U) a (b + δ * a) ε0 ha hb' hε0 hεa hQE hEa hEbU hdrift w
  exact ⟨f, hf, hfD⟩

theorem hQN1_of_drift (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (ε0 : ℝ)
    (hdrift : ∀ f, ‖Qtop (GF ell k Lu) U f - Qtop (GF ell k Lu) (trivialU _) f‖ ≤ ε0 * ‖f‖)
    (ν : SiteL2 (scaleUp ell k Lu)) (hν : ν ∈ NQp (GF ell k Lu) (trivialU _)) :
    ‖Qtop (GF ell k Lu) U ν‖ ≤ ε0 * ‖ν‖ := by
  have h0 : Qtop (GF ell k Lu) (trivialU _) ν = 0 := by
    refine PiLp.ext (fun y => ?_)
    show Qlev (GF ell k Lu) (trivialU _) (GF ell k Lu).k y.1 ν = 0
    exact hν.2 _ (le_refl _) y.1 y.2
  have := hdrift ν
  rwa [h0, sub_zero] at this

#print axioms hext_of_flatExt
#print axioms hQN1_of_drift

end AdalyFormal.SliceCoerc

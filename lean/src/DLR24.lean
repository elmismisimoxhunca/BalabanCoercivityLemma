import DLR23

/-!
# DL24 -- the abstract `T, Z, W` of DL15 ARE the genuine `Tfull = R D*`, `G' R D*`, `Wop` (full tower)

For any `GamHyp G` on `(SiteL2, BondFnL2, coarseC)` whose operators are the genuine ones
(`G.D = D_U`, `G.Qp = Qtop U`, `G.Linv = G' = Gp`), and the site unit `hu`:
* `Tfull_eq_T` : `Tfull = G.T` (`T = D* − XΓ⁻¹(DX)*`, DL15), from `Rproj_eq` (DL23);
* `Wop_eq_W` : `Wop = G.W` (`W = 1 − D G' T`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)
  (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
  (G : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
  (hD : G.D = gradL2 U) (hQ : G.Qp = Qtop (GF ell k Lu) U) (hL : G.Linv = Gp (GF ell k Lu) U a)
include hu hD hQ hL

theorem Tfull_eq_T : Tfull (GF ell k Lu) U = G.T := by
  have hG1 := G.hG1
  rw [hL, hQ] at hG1
  ext1 A
  rw [Tfull, ContinuousLinearMap.comp_apply, Rproj_eq ell k Lu U a hu G.Gami hG1]
  simp only [GamHyp.T, GamHyp.F, SiteHyp.X, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp, hD, hQ, hL]
  rfl

theorem Wop_eq_W : Wop (GF ell k Lu) U a = G.W := by
  have hT := Tfull_eq_T ell k Lu U a hu G hD hQ hL
  ext1 A
  simp only [GamHyp.W, GamHyp.Z, ← hT, hD, hL, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rfl

end

#print axioms Tfull_eq_T
#print axioms Wop_eq_W

end AdalyFormal.DLayer

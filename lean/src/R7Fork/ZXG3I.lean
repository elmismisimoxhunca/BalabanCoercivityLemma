import R7Fork.ZXG3H

/-!
# G3I -- in the statement's hypothesis set, the argument `B = C B̃` of the genuine form is supported on
the embedded `𝔅` (G3H), so `(3.156)` is the form on `L²(𝔅)`:
`genForm(C B̃) = η⟨τ*B, N⁻¹ τ*B⟩ − a⟨τ*B, τ*B⟩ − 2⟨H₁D̃⁽²⁾B, J⟩`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem torusOK_one_le {ell M : ℕ} {Lu : PeriodicLatticeExtent} (h2 : 2 ≤ ell) (hT : TorusOK ell M Lu) :
    ∀ μ, 1 ≤ Lu μ := by
  intro μ
  have := hT.2.1 μ
  omega

/-- for `C B̃` in the statement's hypothesis set, the argument of the form is supported on `𝔅` -/
theorem genC_supported {ell M R k F : ℕ} (hell : 0 < ell) (hp : 2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R)
    {Lu : PeriodicLatticeExtent} (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Bt : Bond Lu → SuTwo) (hBt : OnLambdaT Lam Bt) :
    ∀ e : Bond Lu, unitBondEmb ell k Lu hell e ∉ bondsLam (gparams ell k Lu hell S U a Lam).G k →
      (WithLp.ofLp (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt) : BondFnL2 Lu)) e = 0 := by
  intro e he
  by_contra hne
  have hMR : 1 ≤ R * M := by
    have h1 : 1 ≤ R := by omega
    have h2 : 1 ≤ M := hp.2.1
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact he (Cop_support hell hT.1 (torusOK_one_le hp.1 hT) hMR hS hL _ Bt hBt e hne)

/-- `(3.156)` on the argument `C B̃`, expressed on `L²(𝔅)` only -/
theorem genForm_sector {ell M R k F : ℕ} (hell : 0 < ell) (hp : 2 ≤ ell ∧ 0 < M ∧ 10 ≤ F ∧ F + 2 ≤ R)
    {Lu : PeriodicLatticeExtent} (hT : TorusOK ell M Lu) {S : Tower (scaleUp ell k Lu)}
    (hS : Admissible ell M R k S) {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam)
    (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Bt : Bond Lu → SuTwo) (hBt : OnLambdaT Lam Bt) :
    let P := gparams ell k Lu hell S U a Lam
    let B : BondFnL2 Lu := WithLp.toLp 2 (GenP.genC P Bt)
    GenP.genForm P B =
      P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (GenP.Nmat P) (ContinuousLinearMap.adjoint P.tau B)⟫
        - P.a * ⟪ContinuousLinearMap.adjoint P.tau B, ContinuousLinearMap.adjoint P.tau B⟫
        - 2 * ⟪P.H1in (P.D2in B), P.Jf⟫ := by
  intro P B
  have hsupp := genC_supported hell hp hT hS hL U a Bt hBt
  unfold GenP.genForm GenP.firstTerm
  rw [inner_tauAdj_of_supp P B hsupp]

#print axioms genC_supported
#print axioms genForm_sector

end AdalyFormal.StatementLaneG

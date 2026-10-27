import DLR103

/-!
# DL104 -- plug-in check into MF9 `instIneq_M0_class` (class bounds at scale `ᾱ`, one gauge) with `hD2`, `hJ` DISCHARGED by DL100

`instIneq_M0_class_discharged` : MF9's hypotheses (link / plaquette bounds at `ᾱ`, the k-free smallness of `ᾱ`, KUSmall, UnitSmall)
plus the printed class `PerCubeRegular2` and the numerics package at `((1+3π)ᾱ, fMα₀)` with `eps2op·K̂ < 1` give MF9's conclusion
(`gam0M0 … (eps2op Num) (epsJfree Num) …`).  The regime for DL100 is MF9's own construction (`regime_of_bounds`, DL89), the value
`rhoM0 … = (1+3π)ᾱ` is MF9's `rhoM0_class`.  Together with DL101 (MC4), DL103 (MF7, MF11) every m0_finish / m0_corollary theorem
that took `hD2`/`hJ` as premises has a discharged form.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT PerCubeRegular2)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.M0Finish (PU UnitSmall dCM0 cBM0 gam0M0)

theorem instIneq_M0_class_discharged (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (hell2 : 2 ≤ ell)
    (U : Cfg (scaleUp ell k Lu)) (a t α : ℝ) (ha : 0 < a) (ht : 0 < t) (hα : 0 ≤ α)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hlinks : ∀ b, dv (U b) ≤ α / (ell : ℝ) ^ k)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu), dv (periodicPlaquetteHolonomy U p) ≤ α / ((ell : ℝ) ^ k) ^ 2)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * α ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * α) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * α ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * α) < min a 1 / 1000)
    (H : KUSmall ell ((1 + 3 * Real.pi) * α)) (HU : UnitSmall ell ((1 + 3 * Real.pi) * α))
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t ((1 + 3 * Real.pi) * α) ((f : ℝ) * M * α₀) θ)
    (hε'op : eps2op Num * KhatM0 ell a t ((1 + 3 * Real.pi) * α) < 1) :
    InstIneq ell k hell a Lu
      (gam0M0 ell a t ((1 + 3 * Real.pi) * α) (eps2op Num) (epsJfree Num) (dCM0 ell ((1 + 3 * Real.pi) * α))
        (cBM0 ell ((1 + 3 * Real.pi) * α)))
      (fullTower ell k Lu) Lam U := by
  have R := regime_of_bounds ell k Lu hell2 U a t α ha ht hα hstrict hlinks hplaq hcb h216 h1000 hsmallU
  have hρ := AdalyFormal.M0Finish.rhoM0_class ell k hell α
  have key : ∀ (ρ : ℝ) (hρρ : rhoM0 ell k (α / (ell : ℝ) ^ k) (α / ((ell : ℝ) ^ k) ^ 2) = ρ) (H' : KUSmall ell ρ)
      (HU' : UnitSmall ell ρ) (Num' : M0ClassNum ell a t ρ ((f : ℝ) * M * α₀) θ),
      ‖(PU ell k Lu hell U a Lam).data.Delta2 (PU ell k Lu hell U a Lam).data_laws‖ ≤ eps2op Num' / ((ell : ℝ) ^ k) ^ 2 ∧
      ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
        |⟪(PU ell k Lu hell U a Lam).H1in ((PU ell k Lu hell U a Lam).D2in
            (WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt))), (PU ell k Lu hell U a Lam).Jf⟫|
          ≤ epsJfree Num' * ‖(WithLp.toLp 2 (Cop Lam (PU ell k Lu hell U a Lam).Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by
    intro ρ hρρ H' HU' Num'
    subst hρρ
    exact dlayer_M0_class ell k Lu hell U a t _ _ R H' HU' hd Lam M f α₀ hM hf hP hsm θ Num'
  obtain ⟨hD2, hJ⟩ := key _ hρ H HU Num
  exact AdalyFormal.M0Finish.instIneq_M0_class ell k Lu hell hell2 U a t α ha ht hα hstrict hd Lam hLB hlinks hplaq hcb h216
    h1000 hsmallU H HU (eps2op Num) (epsJfree Num) (eps2op_nonneg Num) (epsJfree_nonneg Num) hε'op hD2 hJ

#print axioms instIneq_M0_class_discharged

end AdalyFormal.DLayer

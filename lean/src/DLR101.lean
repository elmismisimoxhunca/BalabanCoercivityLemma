import DLR100

/-!
# DL101 -- consumption check: MC4 `M0_class_conclusion` (m0_corollary lane) with its D-layer premise `hD` DISCHARGED by DL100

`M0_class_conclusion_discharged` : for `U` in the whole-torus printed class, the hypotheses of MC4's theorem EXCEPT `hD`, plus the
numerics package at `(ρ, β) = ((1+3π)ᾱ, 12Mα₀)` and `eps2op·K̂ < 1`, give MC4's conclusion (InstIneq with MF's constant
`gam0M0 … (eps2op Num) (epsJfree Num) …`).  `hD` is supplied by `DLayer_M0_class` at every class gauge `g` (the regime from the
link/plaquette bounds via `regime_of_bounds`, the class at `g·U` by `perCubeRegular2_gauge`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp TorusOK)
open AdalyFormal.StatementLane2 (PerCubeRegular2 perCubeRegular2_gauge)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.AsmM0 (M0RegimeR rhoM0 KhatM0 ThetaM0)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.M0Finish (UnitSmall dCM0 cBM0 gam0M0)
open AdalyFormal.M0Corollary (GlobalRegular2)

theorem epsJfree_nonneg {ell : ℕ} {a t ρ β θ : ℝ} (Num : M0ClassNum ell a t ρ β θ) : 0 ≤ epsJfree Num := by
  unfold epsJfree
  have hθ0 : 0 ≤ θ := Num.hθ.le
  have h3 : 0 ≤ CH1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
      (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 := by
    unfold CH1free
    have : 0 ≤ qBS ell a ρ := by unfold qBS; positivity
    have := Num.hc.δBS_nonneg
    have : 0 < 1 / bN1 ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
        - EN1free ell a t ρ θ Num.hc (nuPsi ell a t ρ β θ Num.hc Num.hK Num.hEG)
            (deltaPsi ell a t ρ β θ Num.hc Num.hK Num.hEG) Num.hν Num.hδ Num.hK Num.hcg1 Num.hEG1 := by
      linarith [Num.hN1]
    have := Num.hcg1
    have := Num.hc.ha
    positivity
  exact mul_nonneg (mul_nonneg (KDfree_nonneg ell) h3) (JSfree_nonneg β Num.hβ)

theorem eps2op_nonneg {ell : ℕ} {a t ρ β θ : ℝ} (Num : M0ClassNum ell a t ρ β θ) : 0 ≤ eps2op Num := by
  unfold eps2op
  have h1 := CHfree_nonneg ell a t ρ θ Num.hθ Num.hc Num.hK Num.hEG Num.hN
  have h2 := JSfree_nonneg β Num.hβ
  have h3 := K2free_nonneg ell ρ Num.hc.hell Num.hc.hρ0 Num.hK2c
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h1) h2) h3

theorem M0_class_conclusion_discharged (ell M k : ℕ) (hell2 : 2 ≤ ell) (Lu : PeriodicLatticeExtent) (hT : TorusOK ell M Lu)
    (U : LinkCfg (scaleUp ell k Lu)) (a t α₀ ᾱ : ℝ) (hle : (4 * Real.pi + 4) * (12 * M * α₀) ≤ ᾱ) (ha : 0 < a)
    (ht : 0 < t) (hα₀ : 0 < α₀) (hsm : 4 * ((12 : ℝ) * M * α₀) ≤ 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (hU : GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hcb : 4000000 * (ell : ℝ) ^ 2 * ᾱ ≤ 1)
    (h216 : 216 * ((1 + 3 * Real.pi) * ᾱ) ^ 2 < 1)
    (h1000 : (1 + 3 * Real.pi) * ᾱ ≤ 1 / (1000 * (ell : ℝ) ^ 3))
    (hsmallU : ThetaM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < min a 1 / 1000)
    (H : KUSmall ell ((1 + 3 * Real.pi) * ᾱ)) (HU : UnitSmall ell ((1 + 3 * Real.pi) * ᾱ))
    (θ : ℝ) (Num : M0ClassNum ell a t ((1 + 3 * Real.pi) * ᾱ) (((12 : ℕ) : ℝ) * M * α₀) θ)
    (hε'op : eps2op Num * KhatM0 ell a t ((1 + 3 * Real.pi) * ᾱ) < 1) :
    InstIneq ell k (by omega) a Lu
      (gam0M0 ell a t ((1 + 3 * Real.pi) * ᾱ) (eps2op Num) (epsJfree Num)
        (dCM0 ell ((1 + 3 * Real.pi) * ᾱ)) (cBM0 ell ((1 + 3 * Real.pi) * ᾱ)))
      (fullTower ell k Lu) Lam U := by
  have hell : 0 < ell := by omega
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (hT.2.2 0) (Nat.succ_pos _)
  have hpi := Real.pi_pos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hα0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  have hαᾱ : (12 : ℝ) * M * α₀ ≤ ᾱ := by nlinarith
  have hᾱ0 : 0 ≤ ᾱ := hα0.trans hαᾱ
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = (12 : ℝ) * M * α₀ := by norm_num
  have hε2s : 0 ≤ eps2op Num := eps2op_nonneg Num
  have hεJ : 0 ≤ epsJfree Num := epsJfree_nonneg Num
  refine AdalyFormal.M0Corollary.M0_class_conclusion ell M k hell2 Lu hT U a t α₀ ᾱ hle ha ht hα₀ Lam hLB hU hcb h216
    h1000 hsmallU H HU (eps2op Num) (epsJfree Num) hε2s hεJ hε'op (fun g hl hp => ?_)
  -- the D-layer at the class gauge g·U
  have hρ := AdalyFormal.M0Finish.rhoM0_class ell k hell ᾱ
  have R := regime_of_bounds ell k Lu hell2 (periodicGaugeTransform g U) a t ᾱ ha ht hᾱ0 (fun μ => hT.2.1 μ) hl hp hcb
    h216 h1000 hsmallU
  have hPV : PerCubeRegular2 ell M 12 k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ (periodicGaugeTransform g U) :=
    perCubeRegular2_gauge (AdalyFormal.M0Corollary.perCube_of_global hU) g
  have key : ∀ (ρ : ℝ) (hρρ : rhoM0 ell k (ᾱ / (ell : ℝ) ^ k) (ᾱ / ((ell : ℝ) ^ k) ^ 2) = ρ) (H' : KUSmall ell ρ)
      (HU' : UnitSmall ell ρ) (Num' : M0ClassNum ell a t ρ (((12 : ℕ) : ℝ) * M * α₀) θ),
      AdalyFormal.M0Corollary.DLayer ell k Lu hell (periodicGaugeTransform g U) a Lam (eps2op Num') (epsJfree Num') := by
    intro ρ hρρ H' HU' Num'
    subst hρρ
    exact DLayer_M0_class ell k Lu hell (periodicGaugeTransform g U) a t _ _ R H' HU' (fun μ => hT.1 μ) Lam M 12 α₀ hM
      (by norm_num) hPV (by rw [hcast]; exact hsm) θ Num'
  exact key _ hρ H HU Num

#print axioms M0_class_conclusion_discharged

end AdalyFormal.DLayer

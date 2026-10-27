import NtCvOP9

/-!
# CvOP10 -- `cpolCLM`, `MassFull` and the cleared data `AhOf`, `CbhOf` (without `Delta`, `Jf`) are analytic (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem cpolLM_polar (G : TowerGeom L) (S : BondSector G) (x y : BondFnL2 L) :
    cpolLM G S x y = (1 / 2 : ℝ) • (S.C2full (x + y) - S.C2full x - S.C2full y) := by
  have h : S.C2full (x + y) = cpolLM G S x x + cpolLM G S x y + cpolLM G S y x + cpolLM G S y y := by
    rw [← cpolLM_diag G S (x + y)]
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [h, cpolLM_symm G S y x, ← cpolLM_diag G S x, ← cpolLM_diag G S y]
  module

section Ana
variable (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ}

theorem cpolCLM_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) :
    AnalyticAt ℝ (fun t => cpolCLM G (bondSectorOf G (U t))) t0 := by
  apply analyticAt_clm_of_apply
  intro x
  apply analyticAt_clm_of_apply
  intro y
  have hC : ∀ A : BondFnL2 L, AnalyticAt ℝ (fun t => C2fullOf G (U t) A) t0 := fun A =>
    C2fullOf_analytic G U hT hk analyticAt_const
  have h := ((hC (x + y)).sub (hC x)).sub (hC y)
  have h2 := h.const_smul (c := (1 / 2 : ℝ))
  have e : (fun t => (cpolCLM G (bondSectorOf G (U t))) x y)
      = fun t => (1 / 2 : ℝ) • (C2fullOf G (U t) (x + y) - C2fullOf G (U t) x - C2fullOf G (U t) y) := by
    funext t; rw [cpolCLM_apply]; exact cpolLM_polar G (bondSectorOf G (U t)) x y
  rw [e]; exact h2

theorem MassFull_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (a : ℝ) :
    AnalyticAt ℝ (fun t => MassFull G a (bondSectorOf G (U t))) t0 := by
  have hQ := QfullOf_analytic G U hT hk
  unfold MassFull
  exact anal_comp (anal_adjoint hQ) (anal_comp analyticAt_const hQ)

theorem CbhOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => CbhOf G (U t) a (bondSectorOf G (U t))) t0 := by
  apply analyticAt_clm_of_apply
  intro x
  apply analyticAt_clm_of_apply
  intro y
  have hW := WhOf_analytic G U hT hk ha hell hout
  have hx : AnalyticAt ℝ (fun t => WhOf G (U t) a (iE G x)) t0 := anal_apply hW analyticAt_const
  have hy : AnalyticAt ℝ (fun t => WhOf G (U t) a (iE G y)) t0 := anal_apply hW analyticAt_const
  have h := anal_apply (anal_apply (cpolCLM_analytic G U hT hk) hx) hy
  have e : (fun t => (CbhOf G (U t) a (bondSectorOf G (U t))) x y)
      = fun t => (cpolCLM G (bondSectorOf G (U t))) (WhOf G (U t) a (iE G x)) (WhOf G (U t) a (iE G y)) := by
    funext t; rw [CbhOf_apply, cpolCLM_apply]
  rw [e]; exact h

end Ana

end AdalyFormal.CoverOmega.Struct

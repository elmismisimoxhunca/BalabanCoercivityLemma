import NtCvOP4

/-!
# CvOP5 -- `QfullOf`, `C2fullOf` and the polarisation `cpolCLM` are analytic along an analytic regular tower (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem analyticAt_toLp {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {f : (i : ι) → ℝ → β i} {t0 : ℝ} (h : ∀ i, AnalyticAt ℝ (f i) t0) :
    AnalyticAt ℝ (fun t => (WithLp.toLp 2 (fun i => f i t) : PiLp 2 β)) t0 := by
  have h1 : AnalyticAt ℝ (fun t => (fun i => f i t)) t0 := analyticAt_pi_iff.2 h
  have := ((PiLp.continuousLinearEquiv 2 ℝ β).symm.toContinuousLinearMap.analyticAt _).comp h1
  exact this

theorem analyticAt_ofLp_apply {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedSpace ℝ (β i)] {X : ℝ → PiLp 2 β} {t0 : ℝ} (h : AnalyticAt ℝ X t0) (i : ι) :
    AnalyticAt ℝ (fun t => (WithLp.ofLp (X t)) i) t0 := by
  have := ((PiLp.proj 2 β i).analyticAt _).comp h
  exact this

/-- the tower of `U t` is an analytic family of regular backgrounds at `t0` (levels `0, 1`). -/
def TowerOK (G : TowerGeom L) (U : ℝ → Cfg L) (t0 : ℝ) : Prop :=
  (∀ j, j < 2 → AnaFam (fun t => bgTower G (U t) j) t0) ∧
  (∀ j, j < 2 → RegBg2 (G.ell ^ j) G.ell (bgTower G (U t0) j))

variable (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ}

noncomputable def suCoordInvL : XS L →L[ℝ] BondFnL2 L := LinearMap.toContinuousLinearMap suCoordInv

theorem QlinB_apply_analytic (hT : TowerOK G U t0) {j : ℕ} (hj : j ≤ 2) {u : ℝ → XS L}
    (hu : AnalyticAt ℝ u t0) : AnalyticAt ℝ (fun t => suCoordInv (QlinCompL G.ell (bgTower G (U t)) j (u t))) t0 := by
  have h := QlinCompL_analytic G.ell (fun t => bgTower G (U t)) 2 hT.1 hT.2 j hj
  have := (suCoordInvL (L := L)).analyticAt _ |>.comp (anal_apply h hu)
  exact this

theorem QlinB_analytic (hT : TowerOK G U t0) {j : ℕ} (hj : j ≤ 2) :
    AnalyticAt ℝ (fun t => QlinB G (U t) j) t0 := by
  apply analyticAt_clm_of_apply
  intro A
  exact QlinB_apply_analytic G U hT hj analyticAt_const

theorem QfullOf_apply_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) {A : ℝ → BondFnL2 L}
    (hA : AnalyticAt ℝ A t0) : AnalyticAt ℝ (fun t => QfullOf G (U t) (A t)) t0 := by
  have hQ : ∀ p : BIdx G, AnalyticAt ℝ (fun t => (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G (U t) p.1 (A t))) p.2.1) t0 := by
    intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
    have h1 := anal_apply (QlinB_analytic G U hT hj) hA
    exact (analyticAt_ofLp_apply h1 p.2.1).const_smul (c := (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹))
  exact analyticAt_toLp hQ

theorem QfullOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) :
    AnalyticAt ℝ (fun t => QfullOf G (U t)) t0 := by
  apply analyticAt_clm_of_apply
  intro A
  exact QfullOf_apply_analytic G U hT hk analyticAt_const

theorem D2B_apply_analytic (hT : TowerOK G U t0) {j : ℕ} (hj : j ≤ 2) {u v : ℝ → BondFnL2 L}
    (hu : AnalyticAt ℝ u t0) (hv : AnalyticAt ℝ v t0) :
    AnalyticAt ℝ (fun t => D2B G (U t) j (u t) (v t)) t0 := by
  have hsu : AnalyticAt ℝ (fun t => suCoord (u t)) t0 := by
    have := (LinearMap.toContinuousLinearMap (suCoord (L := L))).analyticAt _ |>.comp hu
    exact this
  have hsv : AnalyticAt ℝ (fun t => suCoord (v t)) t0 := by
    have := (LinearMap.toContinuousLinearMap (suCoord (L := L))).analyticAt _ |>.comp hv
    exact this
  have h := D2CompL_analytic G.ell (fun t => bgTower G (U t)) 2 hT.1 hT.2 hsu hsv j hj
  have := (suCoordInvL (L := L)).analyticAt _ |>.comp h
  exact this

theorem C2fullOf_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) {A : ℝ → BondFnL2 L}
    (hA : AnalyticAt ℝ A t0) : AnalyticAt ℝ (fun t => C2fullOf G (U t) (A t)) t0 := by
  have hQ : ∀ p : BIdx G, AnalyticAt ℝ (fun t => (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G (U t) p.1 (A t))) p.2.1) t0 := by
    intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
    have h1 := (D2B_apply_analytic G U hT hj hA hA).const_smul (c := (1 / 2 : ℝ))
    have h2 : (fun t => C2rawB G (U t) p.1 (A t)) = fun t => (1 / 2 : ℝ) • D2B G (U t) p.1 (A t) (A t) := rfl
    have h3 : AnalyticAt ℝ (fun t => C2rawB G (U t) p.1 (A t)) t0 := by rw [h2]; exact h1
    exact (analyticAt_ofLp_apply h3 p.2.1).const_smul (c := (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹))
  exact analyticAt_toLp hQ

end AdalyFormal.CoverOmega.Struct

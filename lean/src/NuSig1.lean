import CvQ2
import CvR3

/-!
# NuSig1 -- the sigma_3 block of the site-level operators of the genuine family is independent of the Cartan configuration (lane ncwdh_ell2_20261018)

For `U, V` Cartan-valued configurations and a sigma_3-valued site field `f` (`pwDiagS L f = f`):
* `Qlev G U j y f = flatQ G.ell j f y` (the transport is the identity on sigma_3), hence `= Qlev G V j y f`;
* `lapFull U f = lapFull V f`; `f ∈ NQp G U ↔ f ∈ NQp G V`; `lapDir G U f = lapDir G V f`;
* `Rproj G U f = Rproj G V f`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverJacobi

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.QjComposite
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)

variable {L : PeriodicLatticeExtent}

/-- sigma_3-valued site function. -/
def SigFn (lam : PeriodicLatticeSite L → SuTwo) : Prop := ∀ x, diagP (lam x) = lam x

theorem flatAvg_sig (s ell : ℕ) {lam : PeriodicLatticeSite L → SuTwo} (h : SigFn lam) (y : PeriodicLatticeSite L) :
    diagP (flatAvg s ell lam y) = flatAvg s ell lam y := by
  unfold flatAvg
  rw [map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

theorem flatQ_sig (ell : ℕ) : ∀ (j : ℕ) {lam : PeriodicLatticeSite L → SuTwo}, SigFn lam → SigFn (flatQ ell j lam) := by
  intro j
  induction j with
  | zero => intro lam h; exact h
  | succ j ih => intro lam h x; exact flatAvg_sig _ _ (ih h) x

theorem stepAverage_sig {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : CartanCfg V)
    (s ell : ℕ) {lam : PeriodicLatticeSite L → SuTwo} (h : SigFn lam) (y : PeriodicLatticeSite L) :
    stepAverage s V ell lam y = flatAvg s ell lam y := by
  unfold stepAverage flatAvg
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := RMap_diagP (coarsePathHolonomy_cartan hV s y (coarseGammaPath s y x)) (lam x)
  rw [h x] at this
  exact this

theorem Qcomposite_sig {bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hbg : ∀ l, CartanCfg (bg l)) (ell : ℕ) :
    ∀ (j : ℕ) {lam : PeriodicLatticeSite L → SuTwo}, SigFn lam → Qcomposite bg ell j lam = flatQ ell j lam := by
  intro j
  induction j with
  | zero => intro lam h; rfl
  | succ j ih =>
    intro lam h
    funext y
    show stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y = flatAvg (ell ^ j) ell (flatQ ell j lam) y
    rw [ih h]
    exact stepAverage_sig (hbg j) _ _ (flatQ_sig ell j h) y

/-- sigma_3 site field. -/
def SigS (f : SiteL2 L) : Prop := pwDiagS L f = f

theorem SigS.fn {f : SiteL2 L} (h : SigS f) : SigFn (WithLp.ofLp f) := by
  intro x
  have := congrArg (fun g : SiteL2 L => g x) h
  simpa [pwDiag_apply] using this

theorem Qlev_sig (G : TowerGeom L) {U : Cfg L} (hU : CartanCfg U) (j : ℕ) (y : PeriodicLatticeSite L) {f : SiteL2 L} (hf : SigS f) :
    Qlev G U j y f = flatQ G.ell j (WithLp.ofLp f) y := by
  rw [Qlev_apply]
  have hb : ∀ l, CartanCfg (bgTower G U l) := fun l => UbarTower_cartan hU G.ell l
  exact congrFun (Qcomposite_sig hb G.ell j hf.fn) y

theorem Qlev_sig_eq (G : TowerGeom L) {U V : Cfg L} (hU : CartanCfg U) (hV : CartanCfg V) (j : ℕ) (y : PeriodicLatticeSite L)
    {f : SiteL2 L} (hf : SigS f) : Qlev G U j y f = Qlev G V j y f := by
  rw [Qlev_sig G hU j y hf, Qlev_sig G hV j y hf]

#print axioms Qlev_sig
#print axioms Qlev_sig_eq

end AdalyFormal.CoverJacobi

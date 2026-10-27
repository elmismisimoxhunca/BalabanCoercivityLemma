import NtCvOP7
import NtCvOS12

/-!
# CvOP8 -- `Qlev`, `Bq`, `Qpa`, `DelpA`, `Gp`, `RhOf`, `WhOf`, `gOf` are analytic along an analytic regular tower (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage Qcomposite)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

theorem stepAverage_analytic {t0 : ℝ} (s ell : ℕ) (V : ℝ → Cfg L) (hV : AnaFam V t0)
    {lam : ℝ → PeriodicLatticeSite L → SuTwo} (hlam : ∀ x, AnalyticAt ℝ (fun t => lam t x) t0)
    (y : PeriodicLatticeSite L) :
    AnalyticAt ℝ (fun t => stepAverage s (V t) ell (lam t) y) t0 := by
  unfold stepAverage
  have hsum : AnalyticAt ℝ (fun t => ∑ x ∈ stepBlockOf y s ell,
      RMap (coarsePathHolonomy s (V t) y (coarseGammaPath s y x)) (lam t x)) t0 := by
    refine Finset.analyticAt_fun_sum _ (fun x _ => ?_)
    have hW : EA (fun t => ((coarsePathHolonomy s (V t) y (coarseGammaPath s y x) : SU2) : M2)) t0 :=
      entAna_of_SGat (SGat.hol t0 s V hV _ y)
    exact RMap_analytic hW (hlam x)
  exact hsum.const_smul (c := (1 / (ell : ℝ) ^ 3))

theorem Qcomposite_analytic {t0 : ℝ} (ell : ℕ) (bg : ℝ → ℕ → Cfg L) (J : ℕ)
    (hbg : ∀ j, j < J → AnaFam (fun t => bg t j) t0) (lam : PeriodicLatticeSite L → SuTwo) :
    ∀ j, j ≤ J → ∀ y, AnalyticAt ℝ (fun t => Qcomposite (bg t) ell j lam y) t0 := by
  intro j
  induction j with
  | zero => intro _ y; exact analyticAt_const
  | succ j ih =>
      intro hj y
      have := stepAverage_analytic (ell ^ j) ell (fun t => bg t j) (hbg j (by omega)) (lam := fun t => Qcomposite (bg t) ell j lam)
        (ih (by omega)) y
      exact this

section Rows
variable (G : TowerGeom L) (U : ℝ → Cfg L) {t0 : ℝ}

theorem Qlev_analytic (hT : TowerOK G U t0) {j : ℕ} (hj : j ≤ 2) (y : PeriodicLatticeSite L) :
    AnalyticAt ℝ (fun t => Qlev G (U t) j y) t0 := by
  apply analyticAt_clm_of_apply
  intro f
  exact Qcomposite_analytic G.ell (fun t => bgTower G (U t)) 2 hT.1 (WithLp.ofLp f) j hj y

theorem Bq_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) : AnalyticAt ℝ (fun t => Bq G (U t)) t0 := by
  apply analyticAt_clm_of_apply
  intro f
  have h : ∀ p : RowIdx G, AnalyticAt ℝ (fun t => Qlev G (U t) (p.1.1 : ℕ) p.1.2 f) t0 := fun p =>
    anal_apply (Qlev_analytic G U hT (by have := p.1.1.2; omega) p.1.2) analyticAt_const
  exact analyticAt_toLp h

theorem Qpa_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (a : ℝ) :
    AnalyticAt ℝ (fun t => Qpa G (U t) a) t0 := by
  classical
  unfold Qpa
  refine Finset.analyticAt_fun_sum _ (fun j hj => Finset.analyticAt_fun_sum _ (fun y _ => ?_))
  have hjk : j ≤ 2 := by have := Finset.mem_range.1 hj; omega
  by_cases hy : y ∈ G.Lam j
  · simp only [if_pos hy]
    have h := Qlev_analytic G U hT hjk y
    exact (anal_comp (anal_adjoint h) h).const_smul (c := (ajSeq a G.ell j * (G.ell : ℝ) ^ j))
  · simp only [if_neg hy]
    exact analyticAt_const

theorem DelpA_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) (a : ℝ) :
    AnalyticAt ℝ (fun t => DelpA G (U t) a) t0 := by
  have hU : LinkEA U t0 := LinkEA_of_AnaFam (hT.1 0 (by norm_num))
  unfold DelpA
  exact anal_comp (anal_comp analyticAt_const ((lapFull_analytic hU).add (Qpa_analytic G U hT hk a))) analyticAt_const

theorem Gp_analytic (hT : TowerOK G U t0) (hk : G.k ≤ 2) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    AnalyticAt ℝ (fun t => Gp G (U t) a) t0 := by
  unfold Gp
  have hX : AnalyticAt ℝ (fun t => DelpA G (U t) a + (1 - siteMask G.Om0)) t0 :=
    (DelpA_analytic G U hT hk a).add analyticAt_const
  have hu : IsUnit (DelpA G (U t0) a + (1 - siteMask G.Om0)) := delpA_unit G (U t0) ha hell hout
  have hinv := analyticAt_inverse (𝕜 := ℝ) (A := SiteL2 L →L[ℝ] SiteL2 L) hu.unit
  rw [hu.unit_spec] at hinv
  have hc : AnalyticAt ℝ (fun t => Ring.inverse (DelpA G (U t) a + (1 - siteMask G.Om0))) t0 :=
    AnalyticAt.comp (g := Ring.inverse) (f := fun t => DelpA G (U t) a + (1 - siteMask G.Om0)) hinv hX
  exact anal_comp hc analyticAt_const

end Rows

end AdalyFormal.CoverOmega.Struct

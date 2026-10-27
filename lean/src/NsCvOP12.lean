import NsCvOP11

/-!
# CvOP12 -- the curl, `bilPlaq`, and the inner-product criterion for operator families (lane omega/near2/struct)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

namespace AdalyFormal.CoverOmega.Struct


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (M2 SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.IngredientFamilyR2 (Cfg)

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- an operator family is analytic iff all its matrix coefficients `⟪x, T y⟫` are. -/
theorem analyticAt_of_inner (T : ℝ → E →L[ℝ] E) {t0 : ℝ}
    (h : ∀ x y, AnalyticAt ℝ (fun t => ⟪x, T t y⟫) t0) : AnalyticAt ℝ T t0 := by
  apply analyticAt_clm_of_apply
  intro y
  let b := stdOrthonormalBasis ℝ E
  have e : (fun t => T t y) = fun t => ∑ i, ⟪b i, T t y⟫ • b i := by
    funext t
    exact (b.sum_repr' (T t y)).symm
  rw [e]
  exact Finset.analyticAt_fun_sum _ (fun i _ => (h (b i) y).smul analyticAt_const)

end Inner

variable {L : PeriodicLatticeExtent}

section Plaq
variable {U : ℝ → Cfg L} {t0 : ℝ}

theorem AprimeYZ_analytic (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    AnalyticAt ℝ (fun t => AprimeYZ (U t) A p) t0 := by
  unfold AprimeYZ
  exact RMap_analytic (hU _) analyticAt_const

theorem AprimeZW_analytic (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    AnalyticAt ℝ (fun t => AprimeZW (U t) A p) t0 := by
  unfold AprimeZW
  exact (RMap_analytic (hU _) analyticAt_const).neg

theorem curlValue_analytic (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    AnalyticAt ℝ (fun t => curlValueCovariant (U t) A p) t0 := by
  unfold curlValueCovariant
  exact (((analyticAt_const.add (RMap_analytic (hU _) analyticAt_const)).sub
    (RMap_analytic (hU _) analyticAt_const)).sub analyticAt_const)

theorem curlMat_EA (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    EA (fun t => curlMatLM (U t) p A) t0 := by
  have : (fun t => curlMatLM (U t) p A) = fun t => ((curlValueCovariant (U t) A p : SuTwo) : M2) := by
    funext t; exact curlMatLM_apply (U t) p A
  rw [this]; exact EA_of_suTwo (curlValue_analytic hU A p)

theorem b1_EA (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    EA (fun t => b1LM (U t) p A) t0 := by
  have : (fun t => b1LM (U t) p A) = fun t => Complex.I • ((AprimeZW (U t) A p : SuTwo) : M2) := by
    funext t; show smulILM (a1LM (U t) p A) = _; rw [smulILM_apply, a1LM_apply]
  rw [this]; exact (EA_of_suTwo (AprimeZW_analytic hU A p)).smul_const _

theorem b4_EA (hU : LinkEA U t0) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    EA (fun t => b4LM (U t) p A) t0 := by
  have : (fun t => b4LM (U t) p A) = fun t => Complex.I • ((AprimeYZ (U t) A p : SuTwo) : M2) := by
    funext t; show smulILM (a4LM (U t) p A) = _; rw [smulILM_apply, a4LM_apply]
  rw [this]; exact (EA_of_suTwo (AprimeYZ_analytic hU A p)).smul_const _

theorem b2_EA (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : EA (fun _ : ℝ => b2LM p A) t0 :=
  EA.const _

theorem b3_EA (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) : EA (fun _ : ℝ => b3LM p A) t0 :=
  EA.const _

theorem pairBil_analytic (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L)
    {f g : ℝ → (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ} (A B : Bond L → SuTwo)
    (hf : EA (fun t => f t A) t0) (hg : EA (fun t => g t B) t0) :
    AnalyticAt ℝ (fun t => pairBil (U t) p (f t) (g t) A B) t0 := by
  have hI := imHolonomy_EA hU p
  have h1 : EA (fun t => smulILM (f t A) * g t B * imHolonomy (U t) p) t0 := by
    have : (fun t => smulILM (f t A) * g t B * imHolonomy (U t) p)
        = fun t => (Complex.I • f t A) * g t B * imHolonomy (U t) p := by funext t; rw [smulILM_apply]
    rw [this]; exact (hf.smul_const _).mul hg |>.mul hI
  have h2 : EA (fun t => smulILM (g t B) * f t A * imHolonomy (U t) p) t0 := by
    have : (fun t => smulILM (g t B) * f t A * imHolonomy (U t) p)
        = fun t => (Complex.I • g t B) * f t A * imHolonomy (U t) p := by funext t; rw [smulILM_apply]
    rw [this]; exact (hg.smul_const _).mul hf |>.mul hI
  simp only [pairBil_apply]
  exact h1.trace_re.sub h2.trace_re

theorem bilPlaq_analytic (hU : LinkEA U t0) (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    AnalyticAt ℝ (fun t => bilPlaq (U t) p A B) t0 := by
  have hcA := curlMat_EA hU A p
  have hcB := curlMat_EA hU B p
  have hre := reHolonomy_EA hU p
  have hfirst : AnalyticAt ℝ (fun t => firstBilPlaq (U t) p A B) t0 := by
    simp only [firstBilPlaq_apply, smulILM_apply]
    exact (((hcA.smul_const _).mul (hcB.smul_const _)).mul (hre.sub EA.one)).trace_re
  have hsecond : AnalyticAt ℝ (fun t => secondBilPlaq (U t) p A B) t0 := by
    simp only [secondBilPlaq_apply]
    have e1 := b1_EA hU A p
    have e1' := b1_EA hU B p
    have e4 := b4_EA hU A p
    have e4' := b4_EA hU B p
    have e2 := b2_EA (t0 := t0) A p
    have e2' := b2_EA (t0 := t0) B p
    have e3 := b3_EA (t0 := t0) A p
    have e3' := b3_EA (t0 := t0) B p
    exact (((((pairBil_analytic hU p (f := fun t => b1LM (U t) p) (g := fun _ => b2LM p) A B e1 e2')).add
      (pairBil_analytic hU p (f := fun t => b1LM (U t) p) (g := fun _ => b3LM p) A B e1 e3')).add
      (pairBil_analytic hU p (f := fun t => b1LM (U t) p) (g := fun t => b4LM (U t) p) A B e1 e4')).add
      (pairBil_analytic hU p (f := fun _ => b2LM p) (g := fun _ => b3LM p) A B e2 e3')).add
      (pairBil_analytic hU p (f := fun _ => b2LM p) (g := fun t => b4LM (U t) p) A B e2 e4')
      |>.add (pairBil_analytic hU p (f := fun _ => b3LM p) (g := fun t => b4LM (U t) p) A B e3 e4')
  have : (fun t => bilPlaq (U t) p A B) = fun t => firstBilPlaq (U t) p A B + secondBilPlaq (U t) p A B := rfl
  rw [this]; exact hfirst.add hsecond

end Plaq

end AdalyFormal.CoverOmega.Struct

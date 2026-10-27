import GaugeNeumann
import NonflatSmooth

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
attribute [local instance 20000] AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo
  AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo
namespace HConstruction.G0CoerceFinal.Joint
open HConstruction.Predicate HConstruction.LocalLog HConstruction.Carrier HConstruction.Covariance
open HConstruction.SmallNFSmooth HConstruction.TransversePos HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
  (SU2 M2 su2Exp su2Log coe_mul coe_inv coe_one su2Log_antiHermitian
   su2Log_traceless su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar gammaVarStrided loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_trivialU)
open AdalySI1.ModifiedAverageDeriv
open AdalySI1.RawUbarDerivNoLoop (ubarBracket ubarSU2_eq_exp_bracket_mul_bondVar
  ubarBracket_conjTranspose ubarBracket_trace)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : PeriodicLatticeExtent} {x : E}

local instance : NormedAddCommGroup (Fine L) :=
  @Pi.normedAddCommGroup _ (fun _ : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo)
local instance : SeminormedAddCommGroup (Fine L) :=
  (inferInstance : NormedAddCommGroup (Fine L)).toSeminormedAddCommGroup
local instance : NormedSpace ℝ (Fine L) :=
  @Pi.normedSpace ℝ _ _ (fun _ : AdalyFormal.Balaban.LatticeOperators.CoarseBond L 1 => SuTwo)
    inferInstance (fun _ => AdalyFormal.Balaban.SuTwoInner.instNormedAddCommGroupSuTwo.toSeminormedAddCommGroup)
    (fun _ => AdalyFormal.Balaban.SuTwoInner.instInnerProductSpaceSuTwo.toNormedSpace)

private theorem smooth_mul {V W : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x)
    (hW : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => ((V t * W t : SU2) : M2)) x := by
  simpa only [coe_mul] using hV.mul hW

private theorem smooth_inv {V : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => (((V t)⁻¹ : SU2) : M2)) x := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.contDiffAt.comp x hV
  change ContDiffAt ℝ ⊤ (fun t => (((V t : SU2) : M2))ᴴ) x at h
  simpa only [coe_inv] using h

private theorem smooth_conj {V W : E → SU2}
    (hV : ContDiffAt ℝ ⊤ (fun t => ((V t : SU2) : M2)) x)
    (hW : ContDiffAt ℝ ⊤ (fun t => ((W t : SU2) : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => ((groupConj (V t) (W t) : SU2) : M2)) x :=
  smooth_mul (smooth_mul hV hW) (smooth_inv hV)

private theorem smooth_exp {F : E → M2}
    (hF : ContDiffAt ℝ ⊤ F x)
    (hmem : ∀ t, (F t)ᴴ = -(F t) ∧ Matrix.trace (F t) = 0) :
    ContDiffAt ℝ ⊤ (fun t => ((su2Exp (F t) : SU2) : M2)) x := by
  have heq : (fun t => ((su2Exp (F t) : SU2) : M2)) = fun t => NormedSpace.exp (F t) := by
    funext t
    exact su2Exp_coe_of_antiHerm_traceless (hmem t).1 (hmem t).2
  rw [heq]
  exact ((NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (F x)).contDiffAt).comp x hF

/-- Unlike the older fixed-background lemma, both background and fluctuation
vary, as do all accumulated path products. -/
private theorem smooth_rZero_fold {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((U t e : SU2) : M2)) x)
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (p : List (Fin 3 × Bool)) :
    ∀ (base : PeriodicLatticeSite L) (g prod : E → SU2),
      ContDiffAt ℝ ⊤ (fun t => ((g t : SU2) : M2)) x →
      ContDiffAt ℝ ⊤ (fun t => ((prod t : SU2) : M2)) x →
      ContDiffAt ℝ ⊤ (fun t => ((
        (p.foldl (rZeroPathStep (U t) (V t)) (base, g t, prod t)).2.2 : SU2) : M2)) x := by
  induction p with
  | nil => intro base g prod _ hp; exact hp
  | cons step rest ih =>
    intro base g prod hg hp
    let next := periodicLatticeStep base step
    let bond : E → SU2 := fun t => if step.2 then V t (base, step.1)
      else groupConj (U t (next, step.1))⁻¹ (V t (next, step.1))⁻¹
    have hb : ContDiffAt ℝ ⊤ (fun t => ((bond t : SU2) : M2)) x := by
      dsimp [bond]
      cases hs : step.2
      · exact smooth_conj (smooth_inv (hU _)) (smooth_inv (hV _))
      · exact hV _
    have hnew := smooth_mul hp (smooth_conj hg hb)
    have hgnew : ContDiffAt ℝ ⊤ (fun t => ((g t *
        (if step.2 then U t (base,step.1) else (U t (next,step.1))⁻¹) : SU2) : M2)) x := by
      apply smooth_mul hg
      cases hs : step.2
      · exact smooth_inv (hU _)
      · exact hU _
    exact ih next (fun t => g t * (if step.2 then U t (base, step.1) else (U t (next, step.1))⁻¹))
      (fun t => prod t * groupConj (g t) (bond t)) hgnew hnew

private theorem smooth_rZero {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((U t e : SU2) : M2)) x)
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (base : PeriodicLatticeSite L) (p : List (Fin 3 × Bool)) :
    ContDiffAt ℝ ⊤ (fun t => ((rZeroPath (U t) (V t) base p : SU2) : M2)) x :=
  smooth_rZero_fold hU hV p base (fun _ => 1) (fun _ => 1) contDiffAt_const contDiffAt_const

private theorem smooth_endpoint {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((U t e : SU2) : M2)) x)
    (hV : ∀ e, ContDiffAt ℝ ⊤ (fun t => ((V t e : SU2) : M2)) x)
    (h0 : V x = trivialU L) (ell : ℕ) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun t => ((endpointAvg (U t) (V t) ell y : SU2) : M2)) x := by
  have hlog : ∀ z, ContDiffAt ℝ ⊤
      (fun t => su2Log (rZeroPath (U t) (V t) y (AdalyFormal.Balaban.Q1Real.GammaPath y z))) x := by
    intro z
    exact contDiffAt_log_at_one (smooth_rZero hU hV y _)
      (by rw [h0, rZeroPath_trivialU_right])
  apply smooth_exp
  · exact ContDiffAt.sum (fun z hz => (hlog z).const_smul _)
  · intro t
    exact ⟨AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_conjTranspose _ _ _,
      AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_trace _ _ _⟩

/-- Actual nonlinear average with simultaneous parameter/fine-field variation. -/
def jointAverage (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond witnessL (1*2))
    (z : ℝ × H) : M2 := actualQ (nonflatU z.1) 2 (fineCoordinates z.2) c

theorem jointAverage_smooth (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond witnessL (1*2)) :
    ContDiffAt ℝ ⊤ (jointAverage c) (0,0) := by
  let U : ℝ × H → PeriodicLinkConfiguration SU2 witnessL := fun z => nonflatU z.1
  let V : ℝ × H → PeriodicLinkConfiguration SU2 witnessL := fun z => bondExp 2 (fineCoordinates z.2)
  have hU (e) : ContDiffAt ℝ ⊤ (fun z => ((U z e : SU2) : M2)) (0,0) :=
    (smooth_link_matrix e).contDiffAt.comp (0,0) contDiffAt_fst
  have hfine : ContDiffAt ℝ ⊤ (fun z : ℝ × H => fineCoordinates z.2) (0,0) :=
    (fineCoordinates (L := witnessL)).toLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp
      (0,0) contDiffAt_snd
  have hV (e) : ContDiffAt ℝ ⊤ (fun z => ((V z e : SU2) : M2)) (0,0) := by
    have h := smooth_bondExp (L := witnessL) 2 e
    have hz : (fineCoordinates : H ≃ₗ[ℝ] Fine witnessL) (0 : H) = 0 := map_zero _
    rw [← hz] at h
    have hc := h.comp (0,0) hfine
    dsimp only [Function.comp_def] at hc
    exact hc
  have hV0 : V (0,0) = trivialU witnessL := by simp only [V, map_zero, bondExp_zero]
  have hU0 : U (0,0) = trivialU witnessL := nonflatU_zero_eq_trivial
  have hguard (y) : HConstruction.SmallNF.LogGuard (loopVar 1 2 (U (0,0)) (c.1.1,c.2) y) := by
    left
    rw [hU0]
    simp [loopVar, gammaVarStrided, coarseBondVar,
      AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]
  have hraw : ContDiffAt ℝ ⊤ (fun z =>
      ((ubarSU2 1 2 (configMul (V z) (U z)) (c.1.1,c.2) : SU2) : M2)) (0,0) := by
    apply smooth_ubar_at_guard
    · intro e; exact smooth_mul (hV e) (hU e)
    · rw [hV0, configMul_trivialU_left]
      exact fun y _ => hguard y
  have hbase : ContDiffAt ℝ ⊤ (fun z =>
      ((ubarSU2 1 2 (U z) (c.1.1,c.2) : SU2) : M2)) (0,0) :=
    smooth_ubar_at_guard hU 2 _ (fun y _ => hguard y)
  have hmod : ContDiffAt ℝ ⊤ (fun z =>
      ((modifiedAverage (U z) 2 (V z) (c.1.1,c.2) : SU2) : M2)) (0,0) := by
    exact smooth_mul
      (smooth_mul (smooth_inv (smooth_endpoint hU hV hV0 2 c.1.1))
        (smooth_mul hraw (smooth_inv hbase)))
      (smooth_conj hbase (smooth_endpoint hU hV hV0 2 _))
  apply contDiffAt_log_at_one hmod
  rw [hV0, modifiedAverage_trivialU]

/-- A reusable joint-smoothness interface on ANY finite lattice, at zero fine
field. Both the input and background vary; every source logarithm gate is explicit. -/
theorem family_actualQ_smooth {U : E → PeriodicLinkConfiguration SU2 L}
    {A : E → Fine L}
    (hU : ∀ e, ContDiffAt ℝ ⊤ (fun z => ((U z e : SU2) : M2)) x)
    (hA : ContDiffAt ℝ ⊤ A x) (hA0 : A x = 0) (ell : ℕ)
    (c : AdalyFormal.Balaban.LatticeOperators.CoarseBond L (1*ell))
    (hg : ∀ y ∈ AdalyFormal.Balaban.QjComposite.stepBlockOf c.1.1 1 ell,
      HConstruction.SmallNF.LogGuard (loopVar 1 ell (U x) (c.1.1,c.2) y)) :
    ContDiffAt ℝ ⊤ (fun z => actualQ (U z) ell (A z) c) x := by
  let V : E → PeriodicLinkConfiguration SU2 L := fun z => bondExp ell (A z)
  have hV (e) : ContDiffAt ℝ ⊤ (fun z => ((V z e : SU2) : M2)) x := by
    have h := smooth_bondExp (L := L) ell e
    rw [← hA0] at h
    have hc := h.comp x hA
    dsimp only [Function.comp_def] at hc
    exact hc
  have hV0 : V x = trivialU L := by simp only [V, hA0, bondExp_zero]
  have hraw : ContDiffAt ℝ ⊤ (fun z =>
      ((ubarSU2 1 ell (configMul (V z) (U z)) (c.1.1,c.2) : SU2) : M2)) x := by
    apply smooth_ubar_at_guard
    · intro e; exact smooth_mul (hV e) (hU e)
    · rw [hV0, configMul_trivialU_left]
      exact hg
  have hbase : ContDiffAt ℝ ⊤ (fun z =>
      ((ubarSU2 1 ell (U z) (c.1.1,c.2) : SU2) : M2)) x := smooth_ubar_at_guard hU ell _ hg
  have hmod : ContDiffAt ℝ ⊤ (fun z =>
      ((modifiedAverage (U z) ell (V z) (c.1.1,c.2) : SU2) : M2)) x := by
    exact smooth_mul
      (smooth_mul (smooth_inv (smooth_endpoint hU hV hV0 ell c.1.1))
        (smooth_mul hraw (smooth_inv hbase)))
      (smooth_conj hbase (smooth_endpoint hU hV hV0 ell _))
  apply contDiffAt_log_at_one hmod
  rw [hV0, modifiedAverage_trivialU]

#print axioms jointAverage_smooth
#print axioms family_actualQ_smooth
end HConstruction.G0CoerceFinal.Joint

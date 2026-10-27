import DK3FineSource

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HConstruction.DK3.FineScale.Analytic
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv su2Exp su2Log
  su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy_trivialU)
open HConstruction.SmallNFSmooth (smooth_coarsePath)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

theorem smooth_mul {A B : E → SU2}
    (hA : ContDiffAt ℝ ⊤ (fun t => (A t : M2)) x)
    (hB : ContDiffAt ℝ ⊤ (fun t => (B t : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => ((A t * B t : SU2) : M2)) x := by
  simpa only [coe_mul] using hA.mul hB

theorem smooth_inv {A : E → SU2}
    (hA : ContDiffAt ℝ ⊤ (fun t => (A t : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => (((A t)⁻¹ : SU2) : M2)) x := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.contDiffAt.comp x hA
  change ContDiffAt ℝ ⊤ (fun t => (A t : M2)ᴴ) x at h
  simpa only [coe_inv] using h

/-- Unlike the prior smooth_ubar_at_guard, this covers s=2, not only s=1. -/
theorem smooth_ubar {L : PeriodicLatticeExtent}
    (A : E → PeriodicLinkConfiguration SU2 L)
    (hA : ∀ b, ContDiffAt ℝ ⊤ (fun t => (A t b : M2)) x)
    (h0 : A x = trivialU L) (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun t => (ubarSU2 s ell (A t) c : M2)) x := by
  have hl (y : PeriodicLatticeSite L) :
      ContDiffAt ℝ ⊤ (fun t => ((loopVar s ell (A t) c y : SU2) : M2)) x := by
    unfold loopVar gammaVarStrided coarseBondVar
    exact smooth_mul (smooth_mul (smooth_mul
      (smooth_coarsePath hA _ _ _) (smooth_coarsePath hA _ _ _))
      (smooth_inv (smooth_coarsePath hA _ _ _)))
      (smooth_inv (smooth_coarsePath hA _ _ _))
  have hz (y : PeriodicLatticeSite L) : loopVar s ell (A x) c y = 1 := by
    rw [h0]
    simp [loopVar, gammaVarStrided, coarseBondVar, coarsePathHolonomy_trivialU]
  let F : E → M2 := fun t => ∑ y ∈ stepBlockOf c.1 s ell,
    ((ell:ℚ)^3)⁻¹ • su2Log (loopVar s ell (A t) c y)
  have hf : ContDiffAt ℝ ⊤ F x := by
    apply ContDiffAt.sum
    intro y _
    exact (HConstruction.LocalLog.contDiffAt_log_at_one (hl y) (hz y)).const_smul _
  have hm (t : E) : (F t)ᴴ = -(F t) ∧ Matrix.trace (F t) = 0 :=
    ⟨AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_conjTranspose _ _ _,
      AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_trace _ _ _⟩
  have he : ContDiffAt ℝ ⊤ (fun t => (su2Exp (F t) : M2)) x := by
    have h := ((NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (F x)).contDiffAt).comp x hf
    have heq : (fun t => (su2Exp (F t) : M2)) = fun t => NormedSpace.exp (F t) := by
      funext t
      exact su2Exp_coe_of_antiHerm_traceless (hm t).1 (hm t).2
    rw [heq]
    exact h
  change ContDiffAt ℝ ⊤ (fun t => ((su2Exp (F t) * coarseBondVar s ell (A t) c : SU2) : M2)) x
  exact smooth_mul he (smooth_coarsePath hA s c.1 (List.replicate ell c.2))


open AdalySI1.Multiscale.M1
open AdalySI1.ModifiedAverageDeriv (groupConj configMul)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
variable {L : PeriodicLatticeExtent}

theorem smooth_conj {A B : E → SU2}
    (hA : ContDiffAt ℝ ⊤ (fun t => (A t : M2)) x)
    (hB : ContDiffAt ℝ ⊤ (fun t => (B t : M2)) x) :
    ContDiffAt ℝ ⊤ (fun t => (groupConj (A t) (B t) : M2)) x :=
  smooth_mul (smooth_mul hA hB) (smooth_inv hA)

theorem smooth_exp {f : E → M2} (hf : ContDiffAt ℝ ⊤ f x)
    (hm : ∀ t, (f t)ᴴ = -(f t) ∧ Matrix.trace (f t) = 0) :
    ContDiffAt ℝ ⊤ (fun t => (su2Exp (f t) : M2)) x := by
  have heq : (fun t => (su2Exp (f t) : M2)) = fun t => NormedSpace.exp (f t) := by
    funext t
    exact su2Exp_coe_of_antiHerm_traceless (hm t).1 (hm t).2
  rw [heq]
  exact ((NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (f x)).contDiffAt).comp x hf

theorem smooth_rZero_fold {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ b, ContDiffAt ℝ ⊤ (fun t => (U t b : M2)) x)
    (hV : ∀ b, ContDiffAt ℝ ⊤ (fun t => (V t b : M2)) x)
    (s : ℕ) (p : List (Fin 3)) :
    ∀ (base : PeriodicLatticeSite L) (g prod : E → SU2),
      ContDiffAt ℝ ⊤ (fun t => (g t : M2)) x →
      ContDiffAt ℝ ⊤ (fun t => (prod t : M2)) x →
      ContDiffAt ℝ ⊤ (fun t =>
        ((p.foldl (rZeroPathStepS s (U t) (V t)) (base,g t,prod t)).2.2 : M2)) x := by
  induction p with
  | nil => intro base g prod _ hp; exact hp
  | cons μ p ih =>
    intro base g prod hg hp
    exact ih (coarseShift base s μ) (fun t => g t * U t (base,μ))
      (fun t => prod t * groupConj (g t) (V t (base,μ)))
      (smooth_mul hg (hU _)) (smooth_mul hp (smooth_conj hg (hV _)))

theorem path_zero (s : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (p : List (Fin 3)) :
    rZeroPathS s U (trivialU L) base p = 1 := by
  have aux : ∀ (base : PeriodicLatticeSite L) (g : SU2),
      (p.foldl (rZeroPathStepS s U (trivialU L)) (base,g,1)).2.2 = 1 := by
    induction p with
    | nil => intros; rfl
    | cons μ p ih =>
      intro base g
      simpa only [List.foldl_cons, rZeroPathStepS, trivialU, groupConj,
        mul_one, mul_inv_cancel] using ih (coarseShift base s μ) (g * U (base,μ))
  exact aux base 1

theorem endpoint_zero (s : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (y : PeriodicLatticeSite L) :
    endpointAvgS s U (trivialU L) ell y = 1 := by
  simp [endpointAvgS, path_zero]

theorem modified_zero (s : ℕ) (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    modifiedAverageS s U ell (trivialU L) = trivialU L := by
  funext c
  simp [modifiedAverageS, endpoint_zero, groupConj,
    AdalySI1.ModifiedAverageDeriv.configMul_trivialU_left, trivialU]

theorem smooth_endpoint {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ b, ContDiffAt ℝ ⊤ (fun t => (U t b : M2)) x)
    (hV : ∀ b, ContDiffAt ℝ ⊤ (fun t => (V t b : M2)) x)
    (hV0 : V x = trivialU L) (s ell : ℕ) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun t => (endpointAvgS s (U t) (V t) ell y : M2)) x := by
  apply smooth_exp
  · apply ContDiffAt.sum
    intro z _
    apply ContDiffAt.const_smul
    apply HConstruction.LocalLog.contDiffAt_log_at_one
    · exact smooth_rZero_fold hU hV s _ y (fun _ => 1) (fun _ => 1)
        contDiffAt_const contDiffAt_const
    · rw [hV0, path_zero]
  · intro t
    exact ⟨AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_conjTranspose _ _ _,
      AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_trace _ _ _⟩

/-- Full strided modified averaging, both slots varying. All logs are paid at 1. -/
theorem smooth_modified {U V : E → PeriodicLinkConfiguration SU2 L}
    (hU : ∀ b, ContDiffAt ℝ ⊤ (fun t => (U t b : M2)) x)
    (hV : ∀ b, ContDiffAt ℝ ⊤ (fun t => (V t b : M2)) x)
    (hU0 : U x = trivialU L) (hV0 : V x = trivialU L)
    (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun t => (modifiedAverageS s (U t) ell (V t) c : M2)) x := by
  have hm : configMul (V x) (U x) = trivialU L := by
    rw [hV0, AdalySI1.ModifiedAverageDeriv.configMul_trivialU_left, hU0]
  exact smooth_mul (smooth_mul (smooth_inv (smooth_endpoint hU hV hV0 s ell c.1))
    (smooth_mul (smooth_ubar _ (fun b => smooth_mul (hV b) (hU b)) hm s ell c)
      (smooth_inv (smooth_ubar U hU hU0 s ell c))))
    (smooth_conj (smooth_ubar U hU hU0 s ell c) (smooth_endpoint hU hV hV0 s ell _))

#print axioms smooth_modified
end HConstruction.DK3.FineScale.Analytic

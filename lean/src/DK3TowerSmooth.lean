import DK3Gate
import JointAverage

/-! New analytic ingredient: smoothness of the ACTUAL single-bar tower at
arbitrary current stride, proved at U=1, then specialized to depth three. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace HConstruction.DK3
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv su2Exp su2Log
  su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy_trivialU)
open HConstruction.SmallNFSmooth (smooth_coarsePath)

private theorem smooth_mul {A B : ℝ → SU2}
    (hA : ContDiffAt ℝ ⊤ (fun t => (A t : M2)) 0)
    (hB : ContDiffAt ℝ ⊤ (fun t => (B t : M2)) 0) :
    ContDiffAt ℝ ⊤ (fun t => ((A t * B t : SU2) : M2)) 0 := by
  simpa only [coe_mul] using hA.mul hB

private theorem smooth_inv {A : ℝ → SU2}
    (hA : ContDiffAt ℝ ⊤ (fun t => (A t : M2)) 0) :
    ContDiffAt ℝ ⊤ (fun t => (((A t)⁻¹ : SU2) : M2)) 0 := by
  have h := AdalySI1.L7.conjTransposeCLM.contDiff.contDiffAt.comp 0 hA
  change ContDiffAt ℝ ⊤ (fun t => (A t : M2)ᴴ) 0 at h
  simpa only [coe_inv] using h

/-- Unlike the prior smooth_ubar_at_guard, this covers s=2, not only s=1. -/
theorem smooth_strided_ubar {L : PeriodicLatticeExtent}
    (A : ℝ → PeriodicLinkConfiguration SU2 L)
    (hA : ∀ b, ContDiffAt ℝ ⊤ (fun t => (A t b : M2)) 0)
    (h0 : A 0 = trivialU L) (s ell : ℕ) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun t => (ubarSU2 s ell (A t) c : M2)) 0 := by
  have hl (y : PeriodicLatticeSite L) :
      ContDiffAt ℝ ⊤ (fun t => ((loopVar s ell (A t) c y : SU2) : M2)) 0 := by
    unfold loopVar gammaVarStrided coarseBondVar
    exact smooth_mul (smooth_mul (smooth_mul
      (smooth_coarsePath hA _ _ _) (smooth_coarsePath hA _ _ _))
      (smooth_inv (smooth_coarsePath hA _ _ _)))
      (smooth_inv (smooth_coarsePath hA _ _ _))
  have hz (y : PeriodicLatticeSite L) : loopVar s ell (A 0) c y = 1 := by
    rw [h0]
    simp [loopVar, gammaVarStrided, coarseBondVar, coarsePathHolonomy_trivialU]
  let F : ℝ → M2 := fun t => ∑ y ∈ stepBlockOf c.1 s ell,
    ((ell:ℚ)^3)⁻¹ • su2Log (loopVar s ell (A t) c y)
  have hf : ContDiffAt ℝ ⊤ F 0 := by
    apply ContDiffAt.sum
    intro y _
    exact (HConstruction.LocalLog.contDiffAt_log_at_one (hl y) (hz y)).const_smul _
  have hm (t : ℝ) : (F t)ᴴ = -(F t) ∧ Matrix.trace (F t) = 0 :=
    ⟨AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_conjTranspose _ _ _,
      AdalySI1.RawUbarDerivNoLoop.sum_qsmul_su2Log_trace _ _ _⟩
  have he : ContDiffAt ℝ ⊤ (fun t => (su2Exp (F t) : M2)) 0 := by
    have h := ((NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (F 0)).contDiffAt).comp 0 hf
    have heq : (fun t => (su2Exp (F t) : M2)) = fun t => NormedSpace.exp (F t) := by
      funext t
      exact su2Exp_coe_of_antiHerm_traceless (hm t).1 (hm t).2
    rw [heq]
    exact h
  change ContDiffAt ℝ ⊤ (fun t => ((su2Exp (F t) * coarseBondVar s ell (A t) c : SU2) : M2)) 0
  exact smooth_mul he (smooth_coarsePath hA s c.1 (List.replicate ell c.2))

theorem smooth_tower (j : ℕ) (b : PeriodicLatticeEdge fineL) :
    ContDiffAt ℝ ⊤ (fun t => (tower t j b : M2)) 0 := by
  induction j generalizing b with
  | zero => exact (smooth_U b).contDiffAt
  | succ j ih => exact smooth_strided_ubar (fun t => tower t j) ih (tower_zero j) (2^j) 2 b

theorem smooth_V (b : PeriodicLatticeEdge unitL) :
    ContDiffAt ℝ ⊤ (fun t => (V t b : M2)) 0 := smooth_tower 3 (embed b.1,b.2)
end HConstruction.DK3

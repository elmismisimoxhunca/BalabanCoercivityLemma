import TL13b

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section tohsec
variable {D X Xt Y Yt : Type} [Fintype D] [Fintype X] [Fintype Xt] [Fintype Y] [Fintype Yt]
  [DecidableEq X] [DecidableEq Xt] [DecidableEq Y] [DecidableEq Yt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- the abstract Hilbert-space cover attached to an index cover -/
noncomputable def Cov.toH (c : Cov D Xt X) : HCov D (PiLp 2 (fun _ : X => E)) (PiLp 2 (fun _ : Xt => E)) where
  ell := c.ell
  rho := fun d => c.pull d
  rho_ell := fun d => by ext1 f; exact c.pull_ell d f
  sum_rho := by
    ext1 f
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    rw [c.sum_pull, ← c.sig_eq_adjoint_ell]
  adj_ell_ell := by
    ext1 f
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    rw [← c.sig_eq_adjoint_ell]
    exact c.sig_ell f
  rho_orth := fun d => by
    have e : ContinuousLinearMap.adjoint (c.pull d : PiLp 2 (fun _ : Xt => E) →L[ℝ] _) = liftF (⇑(c.τ d).symm) :=
      adjoint_liftF_perm (c.τ d)
    rw [e]
    constructor
    · ext1 f; exact liftF_perm_cancel (c.τ d) f
    · ext1 f
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
      ext x
      simp [liftF_apply]

theorem Desc.toH [Nonempty D] {cX : Cov D Xt X} {cY : Cov D Yt Y}
    {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)} {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)}
    (h : Desc cX cY O Ot) : HDesc cX.toH cY.toH O Ot := by
  refine ⟨h.e1, ?_, h.equi⟩
  unfold HE2 HCov.sig
  show (ContinuousLinearMap.adjoint cY.ell).comp Ot = O.comp (ContinuousLinearMap.adjoint cX.ell)
  rw [← cX.sig_eq_adjoint_ell, ← cY.sig_eq_adjoint_ell]
  exact h.e2

end tohsec

end AdalyFormal.Thin

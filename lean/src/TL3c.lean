import TL3b

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section desc2
variable {D X Xt Y Yt : Type} [Fintype D] [Fintype X] [Fintype Xt] [Fintype Y] [Fintype Yt]
  [DecidableEq X] [DecidableEq Xt] [DecidableEq Y] [DecidableEq Yt]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {cX : Cov D Xt X} {cY : Cov D Yt Y}

theorem Cov.ell_eq_adjoint_sig (c : Cov D Xt X) :
    (c.ell : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Xt => E)) = ContinuousLinearMap.adjoint c.sig :=
  (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (fun f g => c.inner_ell_left f g)

theorem Cov.sig_eq_adjoint_ell (c : Cov D Xt X) :
    (c.sig : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : X => E)) = ContinuousLinearMap.adjoint c.ell := by
  rw [c.ell_eq_adjoint_sig, ContinuousLinearMap.adjoint_adjoint]

theorem Desc.adjoint {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : Y => E)}
    {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Yt => E)} (h : Desc cX cY O Ot) :
    Desc cY cX (ContinuousLinearMap.adjoint O) (ContinuousLinearMap.adjoint Ot) := by
  constructor
  · unfold E1
    have := congrArg ContinuousLinearMap.adjoint h.e2
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ← cY.ell_eq_adjoint_sig, ← cX.ell_eq_adjoint_sig] at this
    exact this
  · unfold E2
    have := congrArg ContinuousLinearMap.adjoint h.e1
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ← cX.sig_eq_adjoint_ell, ← cY.sig_eq_adjoint_ell] at this
    exact this
  · intro d
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    obtain ⟨hPY, hPYs⟩ := cY.pull_orth (E := E) d
    obtain ⟨hPX, hPXs⟩ := cX.pull_orth (E := E) d
    -- A* Q* g = P* A* g
    have h' : ∀ g, ContinuousLinearMap.adjoint Ot (ContinuousLinearMap.adjoint (cY.pull d) g) =
        ContinuousLinearMap.adjoint (cX.pull d) (ContinuousLinearMap.adjoint Ot g) := by
      intro g
      have := congrArg ContinuousLinearMap.adjoint (h.equi d)
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at this
      exact (congrArg (fun T => T g) this).symm
    have h1 := h' (cY.pull d f)
    have e1 : ContinuousLinearMap.adjoint (cY.pull d) (cY.pull d f) = f := congrArg (fun T => T f) hPYs
    rw [e1] at h1
    have e2 := congrArg (fun T => T (ContinuousLinearMap.adjoint Ot (cY.pull d f))) hPX
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e2
    rw [← h1] at e2
    exact e2.symm

theorem isUnit_of_desc [Nonempty D] {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : X => E)}
    {Ot' : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Xt => E)}
    (h : E1 cX cX O Ot') (hu : IsUnit Ot') : IsUnit O := by
  have hinj : Function.Injective O := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : Ot' (cX.ell f) = 0 := by
      have := congrArg (fun T => T f) h
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, hf, map_zero]
    have h2 : cX.ell f = 0 := by
      have hb := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
      exact hb (by rw [h1, map_zero])
    exact cX.ell_inj (by rw [h2, map_zero])
  let Ol : (PiLp 2 fun _ : X => E) →ₗ[ℝ] PiLp 2 fun _ : X => E := O
  have hinj' : Function.Injective Ol := hinj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, (LinearMap.injective_iff_surjective (f := Ol)).mp hinj'⟩

theorem Desc.inverse [Nonempty D] {O : PiLp 2 (fun _ : X => E) →L[ℝ] PiLp 2 (fun _ : X => E)}
    {Ot : PiLp 2 (fun _ : Xt => E) →L[ℝ] PiLp 2 (fun _ : Xt => E)} (h : Desc cX cX O Ot) (hu : IsUnit Ot) :
    IsUnit O ∧ Desc cX cX (Ring.inverse O) (Ring.inverse Ot) := by
  have huO := isUnit_of_desc h.e1 hu
  refine ⟨huO, ?_, ?_, ?_⟩
  · -- E1
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    have hO : O (Ring.inverse O f) = f := by
      obtain ⟨u, hu'⟩ := huO
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.mul_inv f
    have hOt : ∀ g, Ring.inverse Ot (Ot g) = g := by
      intro g
      obtain ⟨u, hu'⟩ := hu
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.inv_mul g
    have := congrArg (fun T => T (Ring.inverse O f)) h.e1
    simp only [ContinuousLinearMap.comp_apply, hO] at this
    rw [← this, hOt]
  · -- E2
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    have hOt : Ot (Ring.inverse Ot f) = f := by
      obtain ⟨u, hu'⟩ := hu
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.mul_inv f
    have hO : ∀ g, Ring.inverse O (O g) = g := by
      intro g
      obtain ⟨u, hu'⟩ := huO
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.inv_mul g
    have := congrArg (fun T => T (Ring.inverse Ot f)) h.e2
    simp only [ContinuousLinearMap.comp_apply, hOt] at this
    rw [this, hO]
  · intro d
    ext1 f
    simp only [ContinuousLinearMap.comp_apply]
    have hOt : ∀ g, Ring.inverse Ot (Ot g) = g := by
      intro g
      obtain ⟨u, hu'⟩ := hu
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.inv_mul g
    have hOt' : Ot (Ring.inverse Ot f) = f := by
      obtain ⟨u, hu'⟩ := hu
      rw [← hu', Ring.inverse_unit]
      exact ContinuousLinearMap.ext_iff.mp u.mul_inv f
    have := congrArg (fun T => T (Ring.inverse Ot f)) (h.equi d)
    simp only [ContinuousLinearMap.comp_apply, hOt'] at this
    -- Ot (pull d (Ot⁻¹ f)) = pull d f
    rw [← this, hOt]

end desc2

end AdalyFormal.Thin

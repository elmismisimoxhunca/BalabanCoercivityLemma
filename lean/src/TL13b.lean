import TL13a

set_option autoImplicit false
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace

section hdesc2
variable {D : Type} [Fintype D]
variable {H Ht K Kt : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Ht] [InnerProductSpace ℝ Ht] [FiniteDimensional ℝ Ht]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup Kt] [InnerProductSpace ℝ Kt] [FiniteDimensional ℝ Kt]
variable {cX : HCov D H Ht} {cY : HCov D K Kt}

theorem HCov.ell_inj [Nonempty D] (c : HCov D H Ht) : Function.Injective c.ell := by
  intro f g hfg
  have h1 := congrArg (fun T => T f) c.adj_ell_ell
  have h2 := congrArg (fun T => T g) c.adj_ell_ell
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [hfg] at h1
  have hN : (Fintype.card D : ℝ) ≠ 0 := by
    have : 0 < Fintype.card D := Fintype.card_pos
    positivity
  have : (Fintype.card D : ℝ) • f = (Fintype.card D : ℝ) • g := by rw [← h1, ← h2]
  exact smul_right_injective _ hN this

theorem he2_of_he1_equi [Nonempty D] {O : H →L[ℝ] K} {Ot : Ht →L[ℝ] Kt}
    (h1 : HE1 cX cY O Ot) (he : HEqui cX cY Ot) : HE2 cX cY O Ot := by
  ext1 f
  apply cY.ell_inj
  have a1 : cY.ell (cY.sig (Ot f)) = ∑ d, cY.rho d (Ot f) := by
    have := congrArg (fun T => T (Ot f)) cY.sum_rho
    simpa using this.symm
  have a2 : ∑ d, cY.rho d (Ot f) = ∑ d, Ot (cX.rho d f) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    exact (congrArg (fun T => T f) (he d)).symm
  have a3 : ∑ d, Ot (cX.rho d f) = Ot (cX.ell (cX.sig f)) := by
    rw [← map_sum]
    have := congrArg (fun T => T f) cX.sum_rho
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply] at this
    rw [this]
  have a4 : Ot (cX.ell (cX.sig f)) = cY.ell (O (cX.sig f)) := congrArg (fun T => T (cX.sig f)) h1
  simp only [ContinuousLinearMap.comp_apply]
  rw [a1, a2, a3, a4]

theorem hdesc_of_he1_equi [Nonempty D] {O : H →L[ℝ] K} {Ot : Ht →L[ℝ] Kt}
    (h1 : HE1 cX cY O Ot) (he : HEqui cX cY Ot) : HDesc cX cY O Ot := ⟨h1, he2_of_he1_equi h1 he, he⟩

theorem hisUnit_of_he1 [Nonempty D] {cX : HCov D H Ht} {O : H →L[ℝ] H} {Ot : Ht →L[ℝ] Ht}
    (h : HE1 cX cX O Ot) (hu : IsUnit Ot) : IsUnit O := by
  have hinj : Function.Injective O := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : Ot (cX.ell f) = 0 := by
      have := congrArg (fun T => T f) h
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, hf, map_zero]
    have h2 : cX.ell f = 0 := by
      have hb := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
      exact hb (by rw [h1, map_zero])
    exact cX.ell_inj (by rw [h2, map_zero])
  let Ol : H →ₗ[ℝ] H := O
  have hinj' : Function.Injective Ol := hinj
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, (LinearMap.injective_iff_surjective (f := Ol)).mp hinj'⟩

theorem HDesc.inverse [Nonempty D] {cX : HCov D H Ht} {O : H →L[ℝ] H} {Ot : Ht →L[ℝ] Ht} (h : HDesc cX cX O Ot) (hu : IsUnit Ot) :
    IsUnit O ∧ HDesc cX cX (Ring.inverse O) (Ring.inverse Ot) := by
  have huO := hisUnit_of_he1 h.e1 hu
  refine ⟨huO, ?_, ?_, ?_⟩
  · ext1 f
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
  · ext1 f
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
    rw [← this, hOt]

end hdesc2

end AdalyFormal.Thin

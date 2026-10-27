import DLR22

/-!
# DL23 -- the gauge-fixing projection: `R = 1 − XΓ⁻¹X*` for the genuine `Rproj` (full tower), hence `T = R D*` and `W = Wop`

`X = G'Qtop*` (`G' = Gp`), `Γ = X*X`, `Gi` any two-sided inverse of `Γ`.
* `Gp_sym` : `G'` is self-adjoint;  `adjX_apply` : `X* v = Qtop (G' v)`.
* **`Rproj_eq`** : `R v = v − X Γ⁻¹ X* v` (orthogonal-projection characterisation: `R v ∈ Δ_U N(Q')` with witness `λ = G'(Rv)`,
  `Qtop λ = X*v − ΓΓ⁻¹X*v = 0`; `v − Rv = G'Qtop*z ⊥ Δ_U N(Q')` since `⟪G'Qtop*z, Δ_Uμ⟫ = ⟪z, Qtop μ⟫ = 0`).
* `Tfull_eq_T` : for a `GamHyp` with the genuine operators, `Tfull = T` (DL15);  `Wop_eq_W` : `Wop = W` (DL15).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu)) (a : ℝ)

theorem DelpA_sym (f g : SiteL2 (scaleUp ell k Lu)) :
    ⟪DelpA (GF ell k Lu) U a f, g⟫ = ⟪f, DelpA (GF ell k Lu) U a g⟫ := by
  rw [DelpA_eq_L, DelpA_eq_L]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

variable (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
include hu

theorem Gp_sym (f g : SiteL2 (scaleUp ell k Lu)) :
    ⟪Gp (GF ell k Lu) U a f, g⟫ = ⟪f, Gp (GF ell k Lu) U a g⟫ := by
  have h := DelpA_sym ell k Lu U a (Gp (GF ell k Lu) U a f) (Gp (GF ell k Lu) U a g)
  rw [Gp_right ell k Lu U a hu, Gp_right ell k Lu U a hu] at h
  rw [← h]

theorem Gp_adjoint : ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a) = Gp (GF ell k Lu) U a := by
  ext1 f
  refine ext_inner_left ℝ (fun g => ?_)
  rw [ContinuousLinearMap.adjoint_inner_right, Gp_sym ell k Lu U a hu]

/-- `X* v = Qtop (G' v)` -/
theorem adjX_apply (v : SiteL2 (scaleUp ell k Lu)) :
    ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U)) v
      = Qtop (GF ell k Lu) U (Gp (GF ell k Lu) U a v) := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, Gp_adjoint ell k Lu U a hu]
  rfl

theorem Qtop_of_NQp (μ : SiteL2 (scaleUp ell k Lu)) (hμ : μ ∈ NQp (GF ell k Lu) U) : Qtop (GF ell k Lu) U μ = 0 := by
  refine PiLp.ext (fun y => ?_)
  show Qlev (GF ell k Lu) U (GF ell k Lu).k y.1 μ = 0
  exact hμ.2 _ le_rfl y.1 y.2

/-- **the gauge-fixing projection in closed form** -/
theorem Rproj_eq (Gi : coarseC (GF ell k Lu) →L[ℝ] coarseC (GF ell k Lu))
    (hG1 : ∀ u, (ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))
      ∘L (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))) (Gi u) = u)
    (v : SiteL2 (scaleUp ell k Lu)) :
    Rproj (GF ell k Lu) U v
      = v - (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U))
          (Gi (ContinuousLinearMap.adjoint (Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U)) v)) := by
  set X := Gp (GF ell k Lu) U a ∘L ContinuousLinearMap.adjoint (Qtop (GF ell k Lu) U) with hX
  set z := Gi (ContinuousLinearMap.adjoint X v) with hz
  have hOm := AdalyFormal.SliceCoerc.fullTower_Om0 ell k Lu
  show (RImage (GF ell k Lu) U).starProjection v = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · -- `v − Xz ∈ Δ_U N(Q')`
    set lam := Gp (GF ell k Lu) U a (v - X z) with hlam
    have hQ : Qtop (GF ell k Lu) U lam = 0 := by
      have e1 : Qtop (GF ell k Lu) U lam = ContinuousLinearMap.adjoint X (v - X z) := by
        rw [adjX_apply ell k Lu U a hu]
      rw [e1, map_sub]
      have e2 : ContinuousLinearMap.adjoint X (X z) = ContinuousLinearMap.adjoint X v := by
        have := hG1 (ContinuousLinearMap.adjoint X v)
        rw [ContinuousLinearMap.comp_apply] at this
        rw [hz]; exact this
      rw [e2, sub_self]
    have hmem : lam ∈ NQp (GF ell k Lu) U := AdalyFormal.SliceCoerc.mem_NQp_of_Qtop ell k Lu U lam hQ
    refine Submodule.mem_map.mpr ⟨lam, hmem, ?_⟩
    show lapDir (GF ell k Lu) U lam = v - X z
    rw [AdalyFormal.SliceCoerc.lapDir_univ (GF ell k Lu) hOm U lam]
    have h1 : DelpA (GF ell k Lu) U a lam = lapFull U lam := by
      rw [DelpA_eq_L]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hQ,
        map_zero, smul_zero, add_zero]
      rfl
    rw [← h1, hlam, Gp_right ell k Lu U a hu]
  · intro w hw
    obtain ⟨μ, hμ, hμw⟩ := Submodule.mem_map.mp hw
    rw [← hμw]
    show ⟪v - (v - X z), lapDir (GF ell k Lu) U μ⟫ = 0
    rw [sub_sub_cancel, AdalyFormal.SliceCoerc.lapDir_univ (GF ell k Lu) hOm U μ]
    have hQμ := Qtop_of_NQp ell k Lu U a hu μ hμ
    have h1 : lapFull U μ = DelpA (GF ell k Lu) U a μ := by
      rw [DelpA_eq_L]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, hQμ,
        map_zero, smul_zero, add_zero]
      rfl
    rw [h1, ← DelpA_sym, hX, ContinuousLinearMap.comp_apply, Gp_right ell k Lu U a hu,
      ContinuousLinearMap.adjoint_inner_left, hQμ, inner_zero_right]

end

#print axioms DelpA_sym
#print axioms Gp_sym
#print axioms Gp_adjoint
#print axioms adjX_apply
#print axioms Qtop_of_NQp
#print axioms Rproj_eq

end AdalyFormal.DLayer

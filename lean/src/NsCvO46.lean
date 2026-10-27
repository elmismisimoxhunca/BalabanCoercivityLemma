import NsCvO45

/-!
# CvO46 -- `Dpi`, `T`, `Mass`, hence `Ginv`, on Z-fields of `E_0` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

/-- `pE` fixes elements of `E_0` (it is the orthogonal projection). -/
theorem pE_of_mem (G : TowerGeom L) (y : BondFnL2 L) (hy : y ∈ bondSupp G) : ((pE G y : ↥(bondSupp G)) : BondFnL2 L) = y := by
  have : pE G y = ⟨y, hy⟩ := by
    apply ext_inner_left ℝ
    intro u
    rw [pE_inner_right]
    rfl
  rw [this]

/-- the adjoint of `Wop` fixes divergence-free fields. -/
theorem adjoint_Wop_of_div (G : TowerGeom L) (U : Cfg L) (a : ℝ) (v : BondFnL2 L) (hv : gradAdj U v = 0) :
    ContinuousLinearMap.adjoint (Wop G U a) v = v := by
  apply ext_inner_left ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply, inner_sub_left]
  have : (inner ℝ (gradL2 U (Gp G U a (Rproj G U (gradAdj U w)))) v : ℝ) = 0 := by
    have h := ContinuousLinearMap.adjoint_inner_right (gradL2 U) (Gp G U a (Rproj G U (gradAdj U w))) v
    unfold gradAdj at hv
    rw [← h, hv, inner_zero_right]
  rw [this, sub_zero]

open Classical in
/-- `DpiFull` on a Z-field. -/
theorem DpiFull_zfield (G : TowerGeom L) (U : Cfg L) (hU : CartanCfg U) (a : ℝ) (f : ℕ → ℝ) (ω : ℕ → ℝ)
    (hω : ∀ x : PeriodicLatticeSite L, (if (x, q01) ∈ plaqIn G.Om0 then holCos U (x, q01) else 0) = ω (x 0).val) :
    DpiFull G U a (zfield f) = zfield (zprof (L 0) ω f) := by
  unfold DpiFull
  simp only [ContinuousLinearMap.comp_apply]
  rw [Wop_zfield G U hU a f]
  have hD : Delta G U (zfield f) = zfield (zprof (L 0) ω f) := delta_zfield hU (plaqIn G.Om0) ω hω f
  rw [hD]
  exact adjoint_Wop_of_div G U a _ (gradAdj_zfield hU _)

#print axioms pE_of_mem
#print axioms adjoint_Wop_of_div
#print axioms DpiFull_zfield

end AdalyFormal.CoverOmega

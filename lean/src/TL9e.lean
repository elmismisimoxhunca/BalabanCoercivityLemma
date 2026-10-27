import TL9d

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section qpa
variable {L : PeriodicLatticeExtent}

open Classical in
theorem Qpa_eq (G : TowerGeom L) (U : Cfg L) (a : ℝ) :
    Qpa G U a = (ContinuousLinearMap.adjoint (QlevStack G U)).comp
      ((diagOp (E := SuTwo) (fun p : LamIdx G => ajSeq a G.ell p.1 * (G.ell : ℝ) ^ (p.1 : ℕ))).comp (QlevStack G U)) := by
  ext1 f
  refine ext_inner_left ℝ (fun u => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, inner_diagOp]
  simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range (fun j => ∑ y : PeriodicLatticeSite L,
    ⟪u, (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) • ((ContinuousLinearMap.adjoint (Qlev G U j y)).comp (Qlev G U j y)) else 0) f⟫) (G.k + 1)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have key : ∀ y : PeriodicLatticeSite L, ⟪u, (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ (j : ℕ)) •
      ((ContinuousLinearMap.adjoint (Qlev G U j y)).comp (Qlev G U j y)) else 0) f⟫ =
      if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ (j : ℕ)) * ⟪Qlev G U j y u, Qlev G U j y f⟫ else 0 := by
    intro y
    split_ifs
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_right,
        ContinuousLinearMap.adjoint_inner_right]
    · simp
  simp only [key]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (Finset.univ.filter (fun y => y ∈ G.Lam j)) (p := fun y => y ∈ G.Lam j) (by simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rfl

end qpa

end AdalyFormal.Thin

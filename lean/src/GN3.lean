import GN2
import ZXR2Ops3

/-!
# GN3 -- genuine objects, whole torus (`Ω₀ = univ`): the slice, B1, and the gauge part of `A`

* `Rproj_eq_zero_iff`: `R_U s = 0 ↔ ⟪D_U s, D_U ν⟫ = 0 ∀ ν ∈ N(Q'_U)`  (R2Ops1 `Rproj` = orthogonal projection
  onto `Δ_U N(Q')`): the slice `ker(R D*)` = fields whose divergence is `D`-harmonic relative to `N(Q')`.
* `slice_of_Wop`: `R_U D_U* (W A) = 0` (every `A' = W A` lies in the slice).
* `B1_form` (ANY `Ω₀`; no `hOm`): GIVEN the B0 identity `Q(U) D_U ν = 0` on `N(Q'_U)` (hypothesis `hB0`, NOT proved here),
  `⟪A,Δ_π A⟫ + ‖TA‖² + ⟪A,Q*aQ A⟫ = ⟪WA, Δ WA⟫ + ‖TA‖² + ⟪WA, Q*aQ WA⟫`   (the GC1/B1 identity).
* `gauge_part_le`: Poincare on `N(Q'_U)` (`‖ν‖ ≤ P‖D_U ν‖`) gives `‖A - W A‖ ≤ P ‖T A‖`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.SliceCoerc

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {L : PeriodicLatticeExtent}

theorem Rproj_eq_zero_iff (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (s : SiteL2 L) :
    Rproj G U s = 0 ↔ ∀ ν ∈ NQp G U, ⟪gradL2 U s, gradL2 U ν⟫ = 0 := by
  have hlap : ∀ ν : SiteL2 L, ⟪lapDir G U ν, s⟫ = ⟪gradL2 U s, gradL2 U ν⟫ := by
    intro ν
    rw [lapDir_univ G hOm, lapFull, ContinuousLinearMap.comp_apply, gradAdj,
      ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  constructor
  · intro h ν hν
    rw [← hlap]
    exact h (lapDir G U ν) (Submodule.mem_map_of_mem hν)
  · intro h u hu
    obtain ⟨ν, hν, rfl⟩ := Submodule.mem_map.mp hu
    show ⟪lapDir G U ν, s⟫ = 0
    rw [hlap]; exact h ν hν

theorem slice_of_Wop (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (x : BondFnL2 L) :
    Rproj G U (gradAdj U (Wop G U a x)) = 0 := by
  rw [gradAdj_Wop G hOm U a hu x, map_sub, Rproj_idem, sub_self]

theorem B1_form (G : TowerGeom L) (U : Cfg L) (a : ℝ) (S : BondSector G)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (hB0 : ∀ ν ∈ NQp G U, S.Qfull (gradL2 U ν) = 0) (A : BondFnL2 L) :
    ⟪A, DpiFull G U a A⟫ + ‖Tfull G U A‖ ^ 2 + ⟪A, MassFull G a S A⟫
      = ⟪Wop G U a A, Delta G U (Wop G U a A)⟫ + ‖Tfull G U A‖ ^ 2
        + ⟪Wop G U a A, MassFull G a S (Wop G U a A)⟫ := by
  have hlam := (Gp_Rproj_mem G U a hu (gradAdj U A)).1
  have hQ : S.Qfull (Wop G U a A) = S.Qfull A := by
    simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, map_sub, hB0 _ hlam, sub_zero]
  have hM : ⟪Wop G U a A, MassFull G a S (Wop G U a A)⟫ = ⟪A, MassFull G a S A⟫ := by
    rw [inner_MassFull, inner_MassFull, hQ]
  rw [hM, inner_DpiFull]
  rfl

theorem gauge_part_le (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0))) (P : ℝ) (hP : 0 ≤ P)
    (hPoinc : ∀ ν ∈ NQp G U, ‖ν‖ ≤ P * ‖gradL2 U ν‖) (A : BondFnL2 L) :
    ‖A - Wop G U a A‖ ≤ P * ‖Tfull G U A‖ := by
  set ν := Gp G U a (Rproj G U (gradAdj U A)) with hνdef
  have hν : ν ∈ NQp G U := (Gp_Rproj_mem G U a hu (gradAdj U A)).1
  have hdiff : A - Wop G U a A = gradL2 U ν := by
    simp only [Wop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, hνdef]
    abel
  have hT : Tfull G U A = Rproj G U (gradAdj U A) := rfl
  have h2 : ‖gradL2 U ν‖ ^ 2 = ⟪ν, Rproj G U (gradAdj U A)⟫ :=
    norm_grad_Gp_Rproj_sq G hOm U a hu (gradAdj U A)
  have h3 : ‖gradL2 U ν‖ ^ 2 ≤ P * ‖gradL2 U ν‖ * ‖Tfull G U A‖ := by
    rw [h2, hT]
    calc ⟪ν, Rproj G U (gradAdj U A)⟫ ≤ ‖ν‖ * ‖Rproj G U (gradAdj U A)‖ := real_inner_le_norm _ _
      _ ≤ P * ‖gradL2 U ν‖ * ‖Rproj G U (gradAdj U A)‖ :=
        mul_le_mul_of_nonneg_right (hPoinc ν hν) (norm_nonneg _)
  rw [hdiff]
  rcases eq_or_lt_of_le (norm_nonneg (gradL2 U ν)) with h | h
  · rw [← h]; exact mul_nonneg hP (norm_nonneg _)
  · nlinarith [norm_nonneg (Tfull G U A)]

#print axioms Rproj_eq_zero_iff
#print axioms slice_of_Wop
#print axioms B1_form
#print axioms gauge_part_le

end AdalyFormal.SliceCoerc

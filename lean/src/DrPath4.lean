import DrPath3
import DrBracket2

/-!
# DrPath4 -- the exterior-path separation criterion without a sign assumption on the coupling.
Same path hypotheses as `exterior_path_separation` (DrPath3), but the operator conditions are: `Ginv_lit` a UNIT on `[ta, tb]`, `Ginv_lit(ta) - Delta2_loc` positive semidefinite,
`Ginv_lit(tb) - Delta2_loc` with a negative direction.  Covers the case where the shifted pencil becomes singular AFTER `Ginv_lit` has crossed (then `Ginv_lit` has a negative
eigenvalue there but is still a unit).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Residual

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- abstract form (no lattice objects). -/
theorem sep_abstract_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : ℝ → (E →L[ℝ] E)) (Δ0 : E →L[ℝ] E) (G1 : ℝ → (E →L[ℝ] E)) (hc : Continuous M)
    (hs : ∀ t x y, ⟪M t x, y⟫ = ⟪x, M t y⟫) (hΔ : ∀ x y, ⟪Δ0 x, y⟫ = ⟪x, Δ0 y⟫)
    (hG1 : ∀ t, IsUnit (M t) → G1 t = M t - Δ0)
    (ta tb : ℝ) (hab : ta < tb) (hu : ∀ t ∈ Icc ta tb, IsUnit (M t))
    (h0 : AdalyFormal.D1Literal.PSD (M ta - Δ0)) (v : E) (hv : ⟪v, (M tb - Δ0) v⟫ < 0) :
    ∃ t : ℝ, ta ≤ t ∧ t < tb ∧ IsUnit (M t) ∧ ¬ IsUnit (G1 t) := by
  obtain ⟨t, ht0, htT, hu', hnu⟩ := pencil_bracket_unit M Δ0 hc hs hΔ ta tb hab hu h0 v hv
  refine ⟨t, ht0, htT, hu', ?_⟩
  rw [hG1 t hu']
  exact hnu

section path
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu)) (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)), e ∉ Zb (S.Om 0) → U t e = U 0 e)

include hS hell hroom hUU in
/-- **exterior-path separation criterion, both signs.** -/
theorem exterior_path_separation_unit (hcont : ContFam U) (hWD0 : WellDefAt selIn selIn (Ppt hell0 S a Lam U 0))
    (c : ℕ) (α₀ η : ℝ) (hcl : ClassCoupled ell M c k S α₀ η (U 0))
    (ta tb : ℝ) (hab : ta < tb)
    (hu : ∀ t ∈ Icc ta tb, IsUnit (GinvLit hell0 S a Lam U t))
    (h0 : AdalyFormal.D1Literal.PSD (GinvLit hell0 S a Lam U ta - DeltaLoc0 hell0 S a Lam U))
    (v : E0 S) (hv : ⟪v, (GinvLit hell0 S a Lam U tb - DeltaLoc0 hell0 S a Lam U) v⟫ < 0) :
    ∃ t : ℝ, ta ≤ t ∧ t < tb ∧ ClassCoupled ell M c k S α₀ η (U t) ∧
      IsUnit (GinvLit hell0 S a Lam U t) ∧ ¬ IsUnit (G1Lit hell0 S a Lam U t) := by
  obtain ⟨t, ht0, htT, hu', hnu⟩ := sep_abstract_unit (GinvLit hell0 S a Lam U) (DeltaLoc0 hell0 S a Lam U) (G1Lit hell0 S a Lam U)
    (GinvLit_cont hell0 hS hell hroom a Lam U hUU hcont)
    (fun t x y => (dataS selAll selAll (Ppt hell0 S a Lam U t)).Ginv_symm (dataS_laws selAll selAll (Ppt hell0 S a Lam U t)) x y)
    (((dataS selIn selIn (Ppt hell0 S a Lam U 0)).Delta2_spec (dataS_laws selIn selIn (Ppt hell0 S a Lam U 0))).1)
    (fun t hu => G1Lit_eq hell0 hS hell hroom a Lam U hUU hWD0 t hu)
    ta tb hab hu h0 v hv
  exact ⟨t, ht0, htT, classCoupled_path hS hell hroom U hUU c α₀ η hcl t, hu', hnu⟩

end path

#print axioms sep_abstract_unit
#print axioms exterior_path_separation_unit

end AdalyFormal.D1Residual

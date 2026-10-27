import GdGen2

/-!
# GdGen3 -- `TwoData` for the literal and the localised data at an ARBITRARY configuration.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section gen
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS in
/-- a plaquette near `x` is in `plaqIn Ω₀` when `x` is within `1` of an `Ω₁`-site (collar `6 ≤ R M`). -/
theorem plaq_near_in {w x : PeriodicLatticeSite P.Lf} (hw : w ∈ P.S.Om 1) (hxw : pdist x w ≤ 1)
    (h6 : 6 ≤ R * M) {q : PeriodicLatticePlaquette P.Lf} (hq : pdist q.1 x ≤ 1) :
    q ∈ plaqIn (P.S.Om 0) := by
  intro e he
  obtain ⟨n1, n2⟩ := edge_ends_near he
  have key : ∀ c, pdist c q.1 ≤ 2 → c ∈ P.S.Om 0 := by
    intro c hc
    refine near_om1 hS hw ?_ (Nat.zero_le _)
    have h1 := AdalyFormal.StatementLaneR8.pdist_triangle c q.1 x
    have h2 := AdalyFormal.StatementLaneR8.pdist_triangle c x w
    omega
  exact ⟨key _ n1, key _ n2⟩

include hS hell0 hroom in
theorem JfS_eq_near (sJ sJ' : PlaqSel) (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hsJ' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ' L G)
    (b : Bond P.Lf) (hb1 : b ∈ bondsOm0 P.G) (hb2 : b ∉ bondsLam P.G 0) :
    (WithLp.ofLp (JfS sJ P)) b = (WithLp.ofLp (JfS sJ' P)) b := by
  have h6 : 6 ≤ R * M := by omega
  have hq : ∀ q : PeriodicLatticePlaquette P.Lf, pdist q.1 b.1 ≤ 1 → q ∈ plaqIn (P.S.Om 0) := by
    intro q hq
    rcases endpoint_om1 hell0 hS b hb1 hb2 with hw | hw
    · exact plaq_near_in P hS hw (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega) h6 hq
    · exact plaq_near_in P hS hw (AdalyFormal.StatementLaneR8.pdist_shift_le b.1 b.2) h6 hq
  have hJ : AdalyFormal.IngredientFamily.JfieldLoc (sJ _ P.G) P.U b.1 b.2 =
      AdalyFormal.IngredientFamily.JfieldLoc (sJ' _ P.G) P.U b.1 b.2 :=
    JfieldLoc_congr_sets _ _ _ _ _ (fun q hq' => ⟨fun _ => hsJ' _ _ (hq q hq'), fun _ => hsJ _ _ (hq q hq')⟩)
  unfold JfS
  show -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b) = -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ' _ P.G) P.U b)
  congr 1
  apply Subtype.ext
  show ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • AdalyFormal.IngredientFamily.JfieldLoc (sJ _ P.G) P.U b.1 b.2 =
    ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • AdalyFormal.IngredientFamily.JfieldLoc (sJ' _ P.G) P.U b.1 b.2
  rw [hJ]

include hS hell0 hroom in
theorem Ginv_eq_on_V (sD sJ sD' sJ' : PlaqSel) (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsD' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD' L G) {x : ↥(bondSupp P.G)}
    (hx : x ∈ V0 P.G) : (dataS sD sJ P).Ginv x = (dataS sD' sJ' P).Ginv x := by
  have h4 : 4 ≤ R * M := by omega
  have hΔ : DeltaS sD P.G P.U (Wop P.G P.U P.a (iE P.G x)) = DeltaS sD' P.G P.U (Wop P.G P.U P.a (iE P.G x)) := by
    unfold DeltaS
    refine deltaK_set_congr _ _ _ (fun p hpq e he => ?_)
    have hnot : p ∉ plaqIn (P.S.Om 0) := by
      intro hp
      exact hpq ⟨fun _ => hsD' _ _ hp, fun _ => hsD _ _ hp⟩
    exact Wop_zero_on_notIn hS hell0 h4 P.U P.a x hx hnot e he
  have hD : DpiFullS sD P.G P.U P.a (iE P.G x) = DpiFullS sD' P.G P.U P.a (iE P.G x) := by
    unfold DpiFullS
    simp only [ContinuousLinearMap.comp_apply]
    rw [hΔ]
  rw [dataS_Ginv_eq, dataS_Ginv_eq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [hD]

#print axioms plaq_near_in
#print axioms JfS_eq_near
#print axioms Ginv_eq_on_V

end gen

end AdalyFormal.D1Guarded

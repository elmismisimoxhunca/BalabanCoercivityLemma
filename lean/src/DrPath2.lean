import DrPath1
import DrBracket
import ZT6B

/-!
# DrPath2 -- the exterior-path separation criterion for the real operators

Let `U : ℝ → Cfg` be a continuous path of link configurations that agrees off the bonds with no endpoint in `Ω₀` (an "exterior-only" path).
Write `P t` for the parameter point with link configuration `U t`, `M t := Ginv_lit(P t)` and `Δ0 := Delta2_loc(P 0)`.
Then (all machine-checked below):
* `M` is continuous and symmetric, `Δ2_loc(P t) = Δ0` and `WellDefAt selIn selIn (P t) ↔ WellDefAt selIn selIn (P 0)` for every `t`;
* `ClassCoupled` is invariant along the path;
* if `M t` is coercive on `[0,T]`, `M 0 - Δ0` is positive semidefinite and `M T - Δ0` has a negative direction, then at some `t < T`
  the configuration `U t` is in class, `IsUnit Ginv_lit` holds and `IsUnit G1inv_lit` FAILS.
These are hypotheses about operators, not consequences of the class; this file proves the implication, not the hypotheses.
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

/-- equal data have equal `Delta2` (proof irrelevance in the `Laws` argument). -/
theorem Delta2_congr_data {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup S]
    [InnerProductSpace ℝ S] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {D D' : BaseDataS E S F} (h : D = D')
    (hL : D.Laws) (hL' : D'.Laws) : D.Delta2 hL = D'.Delta2 hL' := by
  subst h; rfl

/-- the parameter point at path time `t`. -/
noncomputable abbrev Ppt {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (U : ℝ → Cfg (scaleUp ell k Lu)) (t : ℝ) : IngrBParams :=
  gparams ell k Lu hell0 S (U t) a Lam

section path
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)}
  (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu)) (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)), e ∉ Zb (S.Om 0) → U t e = U 0 e)

include hS hell hroom hUU in
theorem loc_data_const (t : ℝ) :
    dataS selIn selIn (Ppt hell0 S a Lam U t) = dataS selIn selIn (Ppt hell0 S a Lam U 0) := by
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U 0 e = U t e :=
    fun e he => (hUU t e (fun hz => Zb_not_bothIn _ hz he)).symm
  exact dataS_loc_congr (Ppt hell0 S a Lam U 0) hS hell hroom (U t) hBoth

include hS hell hroom hUU in
theorem Delta2_loc_const (t : ℝ) :
    (dataS selIn selIn (Ppt hell0 S a Lam U t)).Delta2 (dataS_laws selIn selIn (Ppt hell0 S a Lam U t)) =
      (dataS selIn selIn (Ppt hell0 S a Lam U 0)).Delta2 (dataS_laws selIn selIn (Ppt hell0 S a Lam U 0)) :=
  Delta2_congr_data (loc_data_const hell0 hS hell hroom a Lam U hUU t) _ _

include hS hell hroom hUU in
theorem G1invS_loc_const (t : ℝ) :
    G1invS selIn selIn (Ppt hell0 S a Lam U t) = G1invS selIn selIn (Ppt hell0 S a Lam U 0) := by
  have h := loc_data_const hell0 hS hell hroom a Lam U hUU t
  have hspec := G1invS_spec selIn selIn (Ppt hell0 S a Lam U t)
  rw [h] at hspec
  exact (dataS selIn selIn (Ppt hell0 S a Lam U 0)).G1inv_unique hspec (G1invS_spec selIn selIn (Ppt hell0 S a Lam U 0))

include hS hell hroom hUU in
theorem WellDefAt_loc_const (t : ℝ) (h0 : WellDefAt selIn selIn (Ppt hell0 S a Lam U 0)) :
    WellDefAt selIn selIn (Ppt hell0 S a Lam U t) := by
  have h := loc_data_const hell0 hS hell hroom a Lam U hUU t
  have hG := G1invS_loc_const hell0 hS hell hroom a Lam U hUU t
  obtain ⟨h1, h2, h3⟩ := h0
  refine ⟨?_, ?_, ?_⟩
  · rw [h]; exact h1
  · rw [hG]; exact h2
  · unfold GenS.NmatS
    rw [h, hG]; exact h3

include hS hell hroom hUU in
theorem classCoupled_path (c : ℕ) (α₀ η : ℝ) (h0 : ClassCoupled ell M c k S α₀ η (U 0)) (t : ℝ) :
    ClassCoupled ell M c k S α₀ η (U t) := by
  refine ⟨h0.1, ?_⟩
  refine perCubeRegular2_congr hS.1 (fun e he => ?_) h0.2
  exact (hUU t e (fun hz => Zb_not_bothIn _ hz he)).symm

end path

#print axioms Delta2_congr_data
#print axioms loc_data_const
#print axioms Delta2_loc_const
#print axioms G1invS_loc_const
#print axioms WellDefAt_loc_const
#print axioms classCoupled_path

end AdalyFormal.D1Residual

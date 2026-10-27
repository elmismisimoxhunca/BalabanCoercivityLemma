import ZGU1J

/-!
# GU1K -- NON-VACUITY of the closed point for EVERY `k`: at the unit torus `L10` (10 sites/direction),
`ell = 2`, `M = 1`, any `R`, any `10 ≤ F`, any `α₀ > 0`, any `a > 0`, the hypotheses of `CoercGenAt`
(TorusOK, Admissible, CoversOm0, LambdaOK, per-cube regularity of the flat `U`) all hold on
`(fullTower 2 k L10, Λ = univ, U = 1)` and there is a NONZERO `B̃ ∈ Λ̃`; `WellDef` is proved.
(G3B did this for `k = 0` only; its `flat_perCubeRegularMix` hard-coded `k = 0`.)
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- the flat configuration is per-cube regular at EVERY level `k` (Mix class) -/
theorem flat_perCubeRegularMix_k (F k : ℕ) {α₀ : ℝ} (hα : 0 < α₀) {L : PeriodicLatticeExtent}
    (S : Tower L) :
    PerCubeRegularMix 2 1 F k S α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ (flatCfg : LinkCfg L) :=
  flat_perCubeRegularMix F k hα S

/-- **r5 NON-VACUITY AT EVERY `k ≥ 1`**: at `L10`, `ell = 2`, `M = 1`, any `R`, any `α₀ > 0`, any `a > 0`, all hypotheses of the r5 inner
claim hold on `(fullTower 2 k L10, Λ = univ, U = 1)` with the fixed cube factor `12`, there is a NONZERO `B̃ ∈ Λ̃`, and `WellDef` is proved. -/
theorem genuine_point_nonvacuous_k5 (k : ℕ) (hk : 1 ≤ k) (R : ℕ) (a : ℝ) (ha : 0 < a) {α₀ : ℝ}
    (hα : 0 < α₀) :
    TorusOK 2 1 L10 ∧
    Admissible 2 1 R k (fullTower 2 k L10) ∧
    CoversOm0p 2 1 12 k (fullTower 2 k L10) ∧
    LambdaOK (Lu := L10) (Lf := scaleUp 2 k L10) 2 1 R k (fullTower 2 k L10) Set.univ ∧
    PerCubeRegular2 2 1 12 k (fullTower 2 k L10) α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹
      (flatCfg : LinkCfg (scaleUp 2 k L10)) ∧
    GenP.WellDef (gparams 2 k L10 (by norm_num) (fullTower 2 k L10) flatCfg a Set.univ) ∧
    ∃ Bt : Bond L10 → SuTwo, OnLambdaTildeIn Set.univ 2 Bt ∧ OnLambdaT Set.univ Bt ∧
      OnLambda Set.univ Bt ∧ 0 < bondEnergy Bt := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ (L10 μ + 1) := by intro μ; simp [L10]
  have hN : ∀ μ : Fin 3, 1 ≤ L10 μ := by intro μ; simp [L10]
  obtain ⟨h1, h2, h3, h4, h5, hB⟩ := genuine_point_hyps k hk R hα
  exact ⟨h1, h2, h3, h4, h5, PK_wellDef 2 k L10 (by norm_num) a Set.univ hN hdvd ha, hB⟩

/-- strict positivity of the genuine form on `C B̃`, at every `k` (generic torus) -/
theorem genForm_pos_of (k : ℕ) (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (a : ℝ) (ha : 0 < a) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt)
    (hpos : 0 < bondEnergy Bt) :
    0 < GenP.genForm (PK 2 k Lu (by norm_num) a Set.univ)
        (WithLp.toLp 2 (GenP.genC (PK 2 k Lu (by norm_num) a Set.univ) Bt)) := by
  have := floor_all_k k Lu hL hd a ha Bt hBt
  have h2 : 0 < (1 / 1728 : ℝ) * bondEnergy Bt := by positivity
  linarith

#print axioms flat_perCubeRegularMix_k
#print axioms genuine_point_nonvacuous_k5
#print axioms genForm_pos_of

end AdalyFormal.GenuineU1

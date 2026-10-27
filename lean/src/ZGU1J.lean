import ZGU1I

/-!
# GU1J -- THE CLOSED POINT FOR ALL `k`: flat `U`, full tower, `Λ = univ`, `ell = 2`, any `a > 0`, any unit
torus `4 ≤ Lu μ`, `2 ∣ Lu μ + 1`:
   `WellDef`  ∧  `∀ B̃ ∈ Λ̃,  (1/1728)‖B̃‖² ≤ genForm(C B̃)`        (GENUINE `genForm`, `genC`).
Plus: the hypotheses of `CoercGenAt` are satisfied at this point for every `k` (non-vacuity at `L10`).
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

/-- **THE CLOSED POINT, ALL LEVELS `k`** (statement shape of `CoercGenAt`'s conclusion). -/
theorem closed_point_all_k (k : ℕ) (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (a : ℝ) (ha : 0 < a) :
    GenP.WellDef (gparams 2 k Lu (by norm_num) (fullTower 2 k Lu) flatCfg a Set.univ) ∧
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt →
      OnLambdaT (Set.univ : Set (PeriodicLatticeSite Lu)) Bt →
      (1 / 1728 : ℝ) * bondEnergy Bt ≤
        GenP.genForm (gparams 2 k Lu (by norm_num) (fullTower 2 k Lu) flatCfg a Set.univ)
          (WithLp.toLp 2 (GenP.genC (gparams 2 k Lu (by norm_num) (fullTower 2 k Lu) flatCfg a Set.univ) Bt)) := by
  have hN : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hL μ; omega
  have hW : GenP.WellDef (PK 2 k Lu (by norm_num) a Set.univ) :=
    PK_wellDef 2 k Lu (by norm_num) a Set.univ hN hd ha
  exact ⟨hW, fun Bt h1 _ => floor_cond k Lu hL hd (by norm_num) a hW.2.1 hW.2.2 Bt h1⟩

/-- the same, for the print's class `Λ̃` read without the second clause, and in the both-endpoint form
is inherited (the class only shrinks); here just the bare floor -/
theorem floor_all_k (k : ℕ) (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (a : ℝ) (ha : 0 < a) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt) :
    (1 / 1728 : ℝ) * bondEnergy Bt ≤
      GenP.genForm (PK 2 k Lu (by norm_num) a Set.univ)
        (WithLp.toLp 2 (GenP.genC (PK 2 k Lu (by norm_num) a Set.univ) Bt)) := by
  have hN : ∀ μ, 1 ≤ Lu μ := fun μ => by have := hL μ; omega
  have hW := PK_wellDef 2 k Lu (by norm_num) a Set.univ hN hd ha
  exact floor_cond k Lu hL hd (by norm_num) a hW.2.1 hW.2.2 Bt hBt

#print axioms closed_point_all_k
#print axioms floor_all_k

end AdalyFormal.GenuineU1

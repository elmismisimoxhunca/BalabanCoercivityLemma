import ZXG3M
import ZXG3G
import ZXG3E

/-!
# G3N -- packaging: the CLOSED-POINT INSTANCE of the conclusion of `P428Genuine`'s inner statement
`CoercGenAt`, at `(ell, M, k) = (2, ·, 0)`, full tower, `Λ = univ`, flat `U`:
  `WellDef` AND `∀ B̃ ∈ Λ̃ (touching class), (1/1728)‖B̃‖² ≤ (3.156)(C B̃)`,
for every unit torus `Lu` with `4 ≤ Lu μ`, `2 ∣ Lu μ + 1`, every `a > 0`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem closed_point_instance (Lu : PeriodicLatticeExtent) (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) (a : ℝ) (ha : 0 < a) :
    GenP.WellDef (gparams 2 0 Lu (by norm_num) (fullTower 2 0 Lu) flatCfg a Set.univ) ∧
    ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu)) 2 Bt →
      OnLambdaT (Set.univ : Set (PeriodicLatticeSite Lu)) Bt →
      (1 / 1728 : ℝ) * bondEnergy Bt ≤
        GenP.genForm (gparams 2 0 Lu (by norm_num) (fullTower 2 0 Lu) flatCfg a Set.univ)
          (WithLp.toLp 2 (GenP.genC (gparams 2 0 Lu (by norm_num) (fullTower 2 0 Lu) flatCfg a Set.univ) Bt)) :=
  ⟨P0_wellDef 2 Lu (by norm_num) a Set.univ hd ha,
   fun Bt h1 _ => closed_point_coerc Lu hL hd (by norm_num) a ha Bt h1⟩

#print axioms closed_point_instance

end AdalyFormal.StatementLaneG

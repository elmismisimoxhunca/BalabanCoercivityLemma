import R7Fork.DM11

/-!
# DM12 -- the exact equivalence for EVERY flat admissible tower with a nonzero class element:
`InstIneq (1/1728) <-> IsUnit G1inv`  (general form of `DM9.tt_instIneq_iff_G1inv_unit`).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem instIneq_iff_G1inv_unit {k : ℕ} {Lu : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) {M R : ℕ} (hRM : 3 ≤ R * M) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (S : Tower (scaleUp 2 k Lu)) (hS : Admissible 2 M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLam : LambdaOK2 2 M R k S Lam)
    (hne : ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) :
    InstIneq 2 k hell a Lu (1 / 1728 : ℝ) S Lam flatCfg ↔
      IsUnit (gparams 2 k Lu hell S flatCfg a Lam).G1inv := by
  constructor
  · intro hI
    have hN := unit_N_of_instIneq hell a (1 / 1728) ha (by norm_num) S Lam hI hne
    have hbi := bidx_nonempty_of_class hell (fun μ => by have := hL μ; omega) (le_trans (by norm_num) hRM)
      hS hLam.1 hne
    exact unit_G1inv_of_unit_N _ hbi hN
  · exact fun hG => closed_point_proper hL hd hRM hell a ha S hS Lam hLam hG

#print axioms instIneq_iff_G1inv_unit

end AdalyFormal.DirichletMono

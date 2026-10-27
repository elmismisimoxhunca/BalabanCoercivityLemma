import R7Fork.DM7f

/-!
# DM8 -- `closed_point_proper`: the U=1 floor at a proper (multi-stratum, `Omega_0 != torus`) tower under the SINGLE hypothesis `IsUnit G1inv`.
**[SUPERSEDED IN PLACE (S75, 2026-10-10): `IsUnit G1inv` is now a theorem (`DM13i.isUnit_G1inv_proper`); the unconditional statement is `DM14.closed_point_proper_unconditional`. Retained as history.]**
(`IsUnit N` is a THEOREM here: `isUnit_Nmat_of_G1inv`; `H0` bijective is `hb_flat`.)
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (TT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

theorem closed_point_proper {k : ℕ} {Lu : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) {M R : ℕ} (hRM : 3 ≤ R * M) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (S : Tower (scaleUp 2 k Lu)) (hS : Admissible 2 M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLam : LambdaOK2 2 M R k S Lam)
    (hG : IsUnit (gparams 2 k Lu hell S flatCfg a Lam).G1inv) :
    InstIneq 2 k hell a Lu (1 / 1728 : ℝ) S Lam flatCfg :=
  closed_point_proper_cond hL hd hRM hell a ha S hS Lam hLam hG
    (isUnit_Nmat_of_G1inv (gparams 2 k Lu hell S flatCfg a Lam) rfl ha.le hS hG)

theorem tt_floor {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (hG : IsUnit (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)).G1inv) :
    InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg := by
  obtain ⟨h4, hd, hRM, hadm, hLam, -, -⟩ := tt_hypotheses hLu
  exact closed_point_proper h4 hd hRM hell a ha _ hadm _ hLam hG

#print axioms closed_point_proper
#print axioms tt_floor

end AdalyFormal.DirichletMono

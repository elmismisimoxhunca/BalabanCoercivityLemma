import R7Fork.DM13i
import R7Fork.DM12

/-!
# DM14 -- THE UNCONDITIONAL FLAT FLOOR AT PROPER TOWERS (frozen statement, flat `U`, `ell = 2`).
`IsUnit G1inv` is now a theorem (`DM13i.isUnit_G1inv_proper`), so `closed_point_proper` loses its only hypothesis beyond the printed ones.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (TT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2

/-- **THE FLOOR AT EVERY PROPER (multi-stratum) TOWER, flat `U`**: no `IsUnit` hypothesis. -/
theorem closed_point_proper_unconditional {k : ℕ} {Lu : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) {M R : ℕ} (hRM : 3 ≤ R * M) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (S : Tower (scaleUp 2 k Lu)) (hS : Admissible 2 M R k S)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLam : LambdaOK2 2 M R k S Lam) :
    InstIneq 2 k hell a Lu (1 / 1728 : ℝ) S Lam flatCfg :=
  closed_point_proper hL hd hRM hell a ha S hS Lam hLam
    (isUnit_G1inv_proper (gparams 2 k Lu hell S flatCfg a Lam) rfl hS hRM ha (fun μ => by show 1 ≤ Lu μ; have := hL μ; omega))

/-- `WellDef` (hb, `IsUnit G1inv`, `IsUnit N`) at every flat admissible tower -/
theorem proper_wellDef {k : ℕ} {Lu : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ Lu μ)
    (hd : ∀ μ, 2 ∣ Lu μ + 1) {M R : ℕ} (hRM : 3 ≤ R * M) (hell : 0 < 2) (a : ℝ) (ha : 0 < a)
    (S : Tower (scaleUp 2 k Lu)) (hS : Admissible 2 M R k S) (Lam : Set (PeriodicLatticeSite Lu)) :
    GenP.WellDef (gparams 2 k Lu hell S flatCfg a Lam) := by
  have hG := isUnit_G1inv_proper (gparams 2 k Lu hell S flatCfg a Lam) rfl hS hRM ha
    (fun μ => by show 1 ≤ Lu μ; have := hL μ; omega)
  exact ⟨IngrBParams.hb_flat (gparams 2 k Lu hell S flatCfg a Lam) rfl hd, hG,
    isUnit_Nmat_of_G1inv (gparams 2 k Lu hell S flatCfg a Lam) rfl ha.le hS hG⟩

/-- the multi-stratum proper tower `TT` (`k = 1, ell = 2, M = 2, R = 6`, `Omega_0 != torus`, `Lambda' != empty`): the frozen inequality holds -/
theorem tt_instIneq {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hell : 0 < 2) (a : ℝ) (ha : 0 < a) :
    InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg := by
  obtain ⟨h4, hd, hRM, hadm, hLam, -, -⟩ := tt_hypotheses hLu
  exact closed_point_proper_unconditional h4 hd hRM hell a ha _ hadm _ hLam

#print axioms closed_point_proper_unconditional
#print axioms proper_wellDef
#print axioms tt_instIneq

end AdalyFormal.DirichletMono

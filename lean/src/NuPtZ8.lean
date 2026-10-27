import NuPtZ6
import NuU2

/-!
# NuPtZ8 -- the four units and `Qs`-injectivity at the flat point `t = 0` of the dir-0 staggered path, `ell ≥ 2` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open AdalyFormal.CoverOmega
open AdalyFormal.CoverNested
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG

section
variable [CfData]
variable {ell M R : ℕ}

theorem stag0Pt_zero_flat (ell M R : ℕ) (hell : 0 < ell) (a : ℝ) :
    gparams ell 2 (neLu M R) hell (neS ell M R) (stag0Cfg (neC0 ell M R) 0) a (neLam M R) =
      AdalyFormal.CoverOmegaTwo.PF ell M R hell a := by
  have : (stag0Cfg (L := AdalyFormal.StatementLane.scaleUp ell 2 (neLu M R)) (neC0 ell M R) 0) = flatCfg := by
    rw [stag0Cfg_zero]; rfl
  rw [this]

theorem unitsFour_flat_two (hell2 : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) (ha : 0 < a) :
    UnitsFour (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) 0) a (neLam M R)) := by
  have hP : AdalyFormal.CoverOmegaTwo.PGeo ell M R := AdalyFormal.CoverOmegaTwo.pgeo hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  rw [stag0Pt_zero_flat]
  exact AdalyFormal.CoverOmegaTwo.pt_unitsFour (AdalyFormal.CoverOmegaTwo.PF ell M R hell a) rfl
    (fun x h0 => AdalyFormal.CoverOmegaTwo.ginv_definite hP hell a ha x h0) (AdalyFormal.CoverOmegaTwo.qs_injective hP hell a)

theorem qs_injective_flat_two (hell2 : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a : ℝ) :
    ∀ y : FSp (geomOf ell 2 (neS ell M R)), (gparams ell 2 (neLu M R) (by omega) (neS ell M R) (stag0Cfg (neC0 ell M R) 0) a (neLam M R)).data.Qs y = 0 → y = 0 := by
  have hP : AdalyFormal.CoverOmegaTwo.PGeo ell M R := AdalyFormal.CoverOmegaTwo.pgeo hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have key : ∀ P : IngrBParams, P = AdalyFormal.CoverOmegaTwo.PF ell M R hell a → ∀ y : FSp P.G, P.data.Qs y = 0 → y = 0 := by
    rintro P rfl y hy
    exact (injective_iff_map_eq_zero _).mp (AdalyFormal.CoverOmegaTwo.qs_injective hP hell a) y hy
  exact key _ (stag0Pt_zero_flat ell M R hell a)

#print axioms unitsFour_flat_two
#print axioms qs_injective_flat_two

end

end AdalyFormal.NcwdhTwo

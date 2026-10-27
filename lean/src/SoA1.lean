import SoM3
import SoCov5
import SoD0
import SoPtZ8
import CaT2d

/-!
# SoA1 -- the constant-family granting-existence body that keeps SITE coverage and per-cube regularity but drops plaquette coverage FAILS at every even `ell`, `c ≥ 10`
  whenever `ell ∣ 2 (c - 1)` and `2 (c-1)/ell ≥ 9` (lane sites_only_20261019)

`not_familyTorusSitesConstAt_S` : for `ell ≥ 3` even, `c ≥ 10`, `w ≥ 10` with `ell (w - 1) = 2 (c - 1)`, and every `a > 0`, `¬ FamilyTorusSitesConstAt c ell _ a`.
The refuting configurations live on the nested slab tower `neS ell M R` of `NsCvNe2` with the `CfData` instance carrying the THIN WIDTH `w` (not the class factor): every site of `Ω₀` is in a
class cube of factor `c` (`covSitesF_so`), the direction-0 staggered family at the central bond `soC ell M R c` is per-cube regular for the factor-`c` class (`so_stag0_class`, because that single
bond is in no class cube), and the pattern competitor of `SoK1` makes `genForm < γ * bondEnergy` (`main_neg_S`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NcwdhTwo
open MXQ.AllC
open NcwdhFam
open CovAssume (FamilyTorusSitesConstAt)

/-- **the sites-only body fails** (even `ell ≥ 3`, thin width `w` decoupled from the class factor `c` by `ell (w-1) = 2 (c-1)`). -/
theorem not_familyTorusSitesConstAt_S (c ell : ℕ) (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hc : 10 ≤ c) (w : ℕ) (hw : 10 ≤ w)
    (hrel : ell * (w - 1) = 2 * (c - 1)) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusSitesConstAt c ell (by omega) a := by
  letI : CfData := ⟨w, hw⟩
  have hrel' : SoRel ell c := hrel
  have hell2 : 2 ≤ ell := by omega
  have hell0 : 0 < ell := by omega
  rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩
  set m := max m₁ 2 with hm
  have hm1 : m₁ ≤ m := le_max_left _ _
  have hm2 : 2 ≤ m := le_max_right _ _
  set M := ell ^ m with hMdef
  have hMdvd : ell ∣ M := dvd_pow_self ell (by omega)
  have hMe2 : ell * ell ≤ M := by
    calc ell * ell = ell ^ 2 := (pow_two ell).symm
      _ ≤ ell ^ m := Nat.pow_le_pow_right hell0 hm2
  have hM : 0 < M := by nlinarith
  set R := max (max R₁ c) 1 with hRdef
  have hRR : R₁ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRc : c ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hMpos : (0 : ℝ) < ((M : ℕ) : ℝ) := by exact_mod_cast hM
  set α₀ : ℝ := a₀ / ((c : ℝ) * ((M : ℕ) : ℝ)) with hα₀
  have hα : 0 < α₀ := by positivity
  have hle : (c : ℝ) * ((M : ℕ) : ℝ) * α₀ ≤ a₀ := by
    rw [hα₀, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  have hCp := cpos_soC hell2 hM hR1 hrel' hc
  obtain ⟨uE, hpar, hlo, hhi, t, ht, hW, hneg⟩ :=
    main_neg_S hell3 hE hMdvd hMe2 hR1 hrel' hc ha
      (qs_injective_flat_two hell2 hMdvd hM hR1 a) (unitsFour_flat_two hell2 hMdvd hM hR1 a ha)
  have hreg : PerCubeRegularF ell M (constFam c (scaleUp ell 2 (neLu M R))) 2 (neS ell M R) α₀ ((ell : ℝ) ^ 2)⁻¹
      (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (soC ell M R c) t) :=
    perCubeRegularF_constFam_iff.2 (so_stag0_class hell2 hM hR1 hrel' hc t hα)
  have hcov := covSitesF_so hell2 hM hR1 hrel' hc hRc
  have key := hF m hm1 R hRR 2 (by norm_num) (neLu M R) α₀ hα hle (torusOK_ne_two hell2 hMdvd hM)
    (neS ell M R) (ne_admissible_two hell2 hM hR1) (neLam M R) (lambdaOK2_ne_two hell2 hMdvd hM hR1)
    (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (soC ell M R c) t) ⟨hcov, hreg⟩ hW (Bpatf ell uE)
    (onLambdaTildeIn_Bpat ell uE hell2 hpar) (onLambdaT_Bpat ell uE hlo hhi)
  exact absurd key (not_le.2 (lt_of_lt_of_le hneg (mul_nonneg hγ.le (AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _))))

#print axioms not_familyTorusSitesConstAt_S

end AdalyFormal.SitesOnly

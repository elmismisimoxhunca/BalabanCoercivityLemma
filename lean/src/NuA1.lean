import NuM3
import NtAll

/-!
# NuA1 -- `ncwdh_fails_two` (lane ncwdh_ell2_20261018)

`failAtCS_two`   : for `M = 2^m ≥ 4` (indeed `2 ∣ M`, `4 ≤ M`) and `R ≥ 1`, `FailAtCS 2 M R _ a` (the witness tower/torus/`Λ` exposed).
`failEllCS_two`  : `FailEllCS 2 _ a`.
`ncwdh_fails_two`: `FailsAtEll c 2 _ a` for every `c ≥ 10`, `a > 0` (the unforked `FailsAtEll` of `NsCS1`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverNested
open AdalyFormal.NcwdhStrong
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.NcwdhTwo
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

section
variable [CfData]

theorem failAtCS_two {M R : ℕ} (hdvd : 2 ∣ M) (hM4 : 4 ≤ M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    FailAtCS 2 M R (by norm_num) a := by
  have hM : 0 < M := by omega
  obtain ⟨uE, hpar, hlo, hhi, t, ht, hW, hneg⟩ := main_neg_two hdvd hM4 hR ha
    (qs_injective_flat_two (le_refl 2) hdvd hM hR a) (unitsFour_flat_two (le_refl 2) hdvd hM hR a ha)
  intro α hα γ hγ
  refine ⟨torusOK_ne_two (le_refl 2) hdvd hM, ne_admissible_two (le_refl 2) hM hR, lambdaOK2_ne_two (le_refl 2) hdvd hM hR,
    stag0Cfg (neC0 2 M R) t, stag0_class hM hR t hα, hW, Bpatf uE, onLambdaTildeIn_Bpat uE hpar, onLambdaT_Bpat uE hlo hhi, ?_⟩
  exact lt_of_lt_of_le hneg (mul_nonneg hγ.le (AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _))

theorem failEllCS_two {a : ℝ} (ha : 0 < a) : FailEllCS 2 (by norm_num) a := by
  intro m₀
  refine ⟨max m₀ 2, le_max_left _ _, fun R₀ => ⟨max R₀ 1, le_max_left _ _, ?_⟩⟩
  have hm2 : 2 ≤ max m₀ 2 := le_max_right _ _
  have hdvd : 2 ∣ 2 ^ (max m₀ 2) := dvd_pow_self 2 (by omega)
  have h4 : 4 ≤ 2 ^ (max m₀ 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (max m₀ 2) := Nat.pow_le_pow_right (by norm_num) hm2
  exact failAtCS_two hdvd h4 (le_max_right _ _) ha

end

theorem ncwdh_fails_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) : FailsAtEll c 2 (le_refl 2) a := by
  letI : CfData := ⟨c, hc⟩
  refine failsAtEll_of_failEllC (by omega) (le_refl 2) ?_
  intro m₀
  obtain ⟨m, hm, hR⟩ := failEllCS_two ha m₀
  exact ⟨m, hm, fun R₀ => by
    obtain ⟨R, hRR, hf⟩ := hR R₀
    exact ⟨R, hRR, hf.toFailAtC⟩⟩

#print axioms failAtCS_two
#print axioms ncwdh_fails_two

end NcwdhFam

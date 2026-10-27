import NuA2

/-!
# NuA3 -- the constant-family witness at `ell = 2`, and the combination with `NtAll` for every `ell ≥ 2` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.NcwdhStrong
open AdalyFormal.NcwdhTwo
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (shift_val_N)
open MXQ.AllC
open MXQ.Total

theorem failEllC_two (c : ℕ) (hc : 10 ≤ c) {a : ℝ} (ha : 0 < a) : FailEllC c 2 (by norm_num) a := by
  letI : CfData := ⟨c, hc⟩
  intro m₀
  obtain ⟨m, hm, hR⟩ := failEllCS_two ha m₀
  exact ⟨m, hm, fun R₀ => by
    obtain ⟨R, hRR, hf⟩ := hR R₀
    exact ⟨R, hRR, hf.toFailAtC⟩⟩

theorem not_familyTorusNCConstAt_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusNCConstAt c 2 (le_refl 2) a := by
  rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩
  have hfe : FailEllC c 2 (by norm_num) a := failEllC_two c hc ha
  obtain ⟨m, hm, hR⟩ := hfe m₁
  obtain ⟨R, hRR, hfail⟩ := hR R₁
  have hMpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    have : 0 < 2 ^ m := pow_pos (by norm_num) m
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hα : 0 < a₀ / ((c : ℝ) * ((2 ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((2 ^ m : ℕ) : ℝ) * (a₀ / ((c : ℝ) * ((2 ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hfail _ hα γ₀ hγ
  have key := hF m hm R hRR k hk Lu _ hα hle hT S hS Lam hL U (perCubeRegularF_constFam_iff.2 hU) hW Bt h1 h2
  exact absurd key (not_le.2 hlt)

section
variable [CfData]

theorem exists_uncovered_bond_two {M R : ℕ} (hM : 0 < M) (hR : 1 ≤ R) :
    ∃ b : Bond (scaleUp 2 2 (neLu M R)), CubeBond ((neS 2 M R).Om 0) b ∧
      ∀ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 (neLu M R)))) (j : ℕ),
        IsClassCube 2 M CfData.cf 2 (neS 2 M R) sites j → ¬ CubeBond sites b := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two (ell := 2) (le_refl 2) hM hR
  have hN := ne_scaleUp (ell := 2) (R := R) (by norm_num) hM
  have hNdef : neN 2 M R = 4 * (2 * (2 * (R * M))) + 2 * (CfData.cf * (2 * (2 * M))) + 6 * (2 * (2 * M)) := rfl
  have hcf := CfData.hcf
  have e1 : CfData.cf * (2 * (2 * M)) = 2 * (CfData.cf * (2 * M)) := by ring
  have hc2M : 10 * (2 * M) ≤ CfData.cf * (2 * M) := Nat.mul_le_mul_right _ hcf
  have hN1 : 1 < neN 2 M R := by omega
  have hCN : neC0 2 M R + 1 < neN 2 M R := by simp only [neC0, neA']; omega
  let x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then neC0 2 M R else 0, by have := hN μ; split_ifs <;> omega⟩
  have hx0 : (x 0).val = neC0 2 M R := by simp [x]
  have hv : ((periodicLatticeShift x 0) 0).val = neC0 2 M R + 1 := by
    rw [shift_val_N hN hN1, if_pos rfl, hx0]; exact Nat.mod_eq_of_lt hCN
  refine ⟨(x, 0), ⟨om0_of_val hM hR _ (Or.inl hx0), om0_of_val hM hR _ (Or.inr hv)⟩, fun sites j hq hb => ?_⟩
  exact ne2_bond_uncovered hM hR x hx0 sites j hq hb

end

/-- the refuting configurations for the constant family at `ell = 2`, as a statement. -/
def ConstFamWitnessTwo (c : ℕ) (a : ℝ) : Prop :=
  ∀ (a₀ γ : ℝ), 0 < a₀ → 0 < γ → ∀ (m₁ R₁ : ℕ),
    ∃ m : ℕ, m₁ ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧ ∃ Lu : PeriodicLatticeExtent, ∃ α₀ : ℝ, 0 < α₀ ∧
      (c : ℝ) * ((2 ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ TorusOK 2 (2 ^ m) Lu ∧
      ∃ S : Tower (scaleUp 2 2 Lu), Admissible 2 (2 ^ m) R 2 S ∧
      ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 2 (2 ^ m) R 2 S Lam ∧
      ∃ U : LinkCfg (scaleUp 2 2 Lu),
        (∃ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 Lu))) (j : ℕ), IsClassCube 2 (2 ^ m) c 2 S sites j) ∧
        PerCubeRegularF 2 (2 ^ m) (constFam c (scaleUp 2 2 Lu)) 2 S α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ U ∧
        GenP.WellDefG (gparams 2 2 Lu (by norm_num) S U a Lam) ∧
        (∃ b : Bond (scaleUp 2 2 Lu), CubeBond (S.Om 0) b ∧
          ∀ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 Lu))) (j : ℕ), IsClassCube 2 (2 ^ m) c 2 S sites j → ¬ CubeBond sites b) ∧
        ¬ CovPlaqF 2 (2 ^ m) (constFam c (scaleUp 2 2 Lu)) 2 S ∧
        ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧
          GenP.genForm (gparams 2 2 Lu (by norm_num) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams 2 2 Lu (by norm_num) S U a Lam) Bt)) < γ * bondEnergy Bt

theorem constFam_witness_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) : ConstFamWitnessTwo c a := by
  intro a₀ γ ha₀ hγ m₁ R₁
  letI : CfData := ⟨c, hc⟩
  obtain ⟨m, hm, hR⟩ := failEllCS_two ha m₁
  obtain ⟨R, hRR, hfail⟩ := hR (max (max R₁ c) 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hRR
  have hRc : c ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRR
  have hMpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    have : 0 < 2 ^ m := pow_pos (by norm_num) m
    exact_mod_cast this
  have hM : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hα : 0 < a₀ / ((c : ℝ) * ((2 ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((2 ^ m : ℕ) : ℝ) * (a₀ / ((c : ℝ) * ((2 ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨hT, hA, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hfail _ hα γ hγ
  refine ⟨m, hm, R, le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRR, neLu (2 ^ m) R, _, hα, hle, hT,
    neS 2 (2 ^ m) R, hA, neLam (2 ^ m) R, hL, U, exists_classCube_ne_two (le_refl 2) hM hR1 hRc,
    perCubeRegularF_constFam_iff.2 hU, hW, exists_uncovered_bond_two hM hR1, not_covPlaqF_two hM hR1, Bt, h1, h2, hlt⟩

/-- **all `ell ≥ 2`**: the coverage-free headline fails at every `c ≥ 10`, `a > 0`. -/
theorem ncwdh_fails_ge_two (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FailsAtEll c ell hell a := by
  rcases (show ell = 2 ∨ 3 ≤ ell by omega) with rfl | h3
  · exact ncwdh_fails_two c hc a ha
  · exact ncwdh_fails_all c hc ell h3 a ha

theorem famConst_ge_two (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusNCConstAt c ell hell a := by
  rcases (show ell = 2 ∨ 3 ≤ ell by omega) with rfl | h3
  · exact not_familyTorusNCConstAt_two c hc a ha
  · exact (famConst_all c hc ell h3 a ha).1

#print axioms failEllC_two
#print axioms not_familyTorusNCConstAt_two
#print axioms constFam_witness_two
#print axioms ncwdh_fails_ge_two
#print axioms famConst_ge_two

end NcwdhFam

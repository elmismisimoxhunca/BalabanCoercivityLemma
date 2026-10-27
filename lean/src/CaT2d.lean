import CaT2c
import CaT1

/-!
# CaT2d -- site coverage at `ell = 2` on the witness tower, and plaquette coverage separately necessary (lane cov_assume_20261019)

* `covSite_exists` / `covSitesF_two` : for `M > 0`, `R ≥ cf` (`cf ≥ 10`), every site of `Ω₀` of `neS 2 M R` lies in a class cube of factor `cf`:
  `CovSitesF 2 M (constFam cf _) 2 (neS 2 M R)`  (the six cases are `CaT2c`).
* `ConstFamWitnessTwoS` / `constFam_witness_two_sites` : the refuting configurations of `ConstFamWitnessTwo` (same parameters) additionally satisfy `CovSitesF`.
* `FamilyTorusSitesConstAt` : the constant-family body at `ell` with class hypothesis `CovSitesF ∧ PerCubeRegularF` (plaquette coverage dropped).
* `covPlaq_separately_necessary_two` : at `ell = 2`, `FamilyTorusCovConstAt` holds and `FamilyTorusSitesConstAt` fails.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace CovAssume

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.NcwdhStrong
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open MXQ.AllC
open MXQ.Total
open NcwdhFam

section
variable [CfData]

theorem covSite_exists {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R))) (hx : x ∈ (neS 2 M R).Om 0) : CovEx M R x := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  rw [neS_om0] at hx
  obtain ⟨hx1, hx2⟩ := hx
  by_cases c1 : (x 0).val < neP1 2 M R
  · exact cov_L0left hM hR x hx1 c1
  by_cases c6 : neQ1 2 M R ≤ (x 0).val
  · exact cov_L0right hM hR x c6 hx2
  by_cases th : neA' 2 M R ≤ (x 0).val ∧ (x 0).val < neB' 2 M R
  · by_cases hC : (x 0).val < 4 * (R * M) + 2 * M + 2 * (CfData.cf * M)
    · exact cov_thinL hM hR x th.1 hC
    · exact cov_thinR hM hR x (by omega) th.2
  by_cases fat : neA 2 M R ≤ (x 0).val ∧ (x 0).val < neB 2 M R
  · exact cov_fat hM hR x fat.1 fat.2
  · exact cov_lev1 hM hR x (by omega) (by omega) th fat

/-- **site coverage at `ell = 2` on the explicit tower `neS 2 M R`** (the nested slab tower of NsCvNe2; this is the only tower treated): every site of `Ω₀` lies in a class cube of factor `cf`, for `M > 0`, `R ≥ cf`. Nothing is claimed for other admissible towers. -/
theorem covSitesF_two {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) :
    CovSitesF 2 M (constFam CfData.cf (scaleUp 2 2 (neLu M R))) 2 (neS 2 M R) := by
  intro x hx
  obtain ⟨sites, j, hq, hxs⟩ := covSite_exists hM hR x hx
  exact ⟨sites, j, ⟨CfData.cf, mem_constFam.2 rfl, hq⟩, hxs⟩

/-- the covered set is not empty and contains thin-component sites: `Ω₀` of the witness tower has a site in `[A', B')`. -/
theorem om0_thin_site_two {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) :
    ∃ x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)), x ∈ (neS 2 M R).Om 0 ∧
      neA' 2 M R ≤ (x 0).val ∧ (x 0).val < neB' 2 M R := by
  obtain ⟨eP0, eP1, eA', eB', eA, eB, eQ1, eQ0, eN⟩ := ne2_vals (M := M) (R := R)
  have hcf := CfData.hcf
  have hc10 : 10 * M ≤ CfData.cf * M := Nat.mul_le_mul_right M hcf
  have hRM : M ≤ R * M := Nat.le_mul_of_pos_left M (by omega)
  have hN := ne_scaleUp (ell := 2) (R := R) (by norm_num) hM
  let x : PeriodicLatticeSite (scaleUp 2 2 (neLu M R)) :=
    fun μ => ⟨if μ = 0 then neA' 2 M R else 0, by have := hN μ; split_ifs <;> omega⟩
  have hx0 : (x 0).val = neA' 2 M R := by simp [x]
  exact ⟨x, by rw [neS_om0]; omega, by omega, by omega⟩

end

/-- `ConstFamWitnessTwo` (NuA3) verbatim, with the one conjunct `CovSitesF 2 (2 ^ m) (constFam c _) 2 S` added after `WellDefG`. -/
def ConstFamWitnessTwoS (c : ℕ) (a : ℝ) : Prop :=
  ∀ (a₀ γ : ℝ), 0 < a₀ → 0 < γ → ∀ (m₁ R₁ : ℕ),
    ∃ m : ℕ, m₁ ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧ ∃ Lu : PeriodicLatticeExtent, ∃ α₀ : ℝ, 0 < α₀ ∧
      (c : ℝ) * ((2 ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ TorusOK 2 (2 ^ m) Lu ∧
      ∃ S : Tower (scaleUp 2 2 Lu), Admissible 2 (2 ^ m) R 2 S ∧
      ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 2 (2 ^ m) R 2 S Lam ∧
      ∃ U : LinkCfg (scaleUp 2 2 Lu),
        (∃ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 Lu))) (j : ℕ), IsClassCube 2 (2 ^ m) c 2 S sites j) ∧
        PerCubeRegularF 2 (2 ^ m) (constFam c (scaleUp 2 2 Lu)) 2 S α₀ (((2 : ℕ) : ℝ) ^ 2)⁻¹ U ∧
        GenP.WellDefG (gparams 2 2 Lu (by norm_num) S U a Lam) ∧
        CovSitesF 2 (2 ^ m) (constFam c (scaleUp 2 2 Lu)) 2 S ∧
        (∃ b : Bond (scaleUp 2 2 Lu), CubeBond (S.Om 0) b ∧
          ∀ (sites : Set (PeriodicLatticeSite (scaleUp 2 2 Lu))) (j : ℕ), IsClassCube 2 (2 ^ m) c 2 S sites j → ¬ CubeBond sites b) ∧
        ¬ CovPlaqF 2 (2 ^ m) (constFam c (scaleUp 2 2 Lu)) 2 S ∧
        ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧
          GenP.genForm (gparams 2 2 Lu (by norm_num) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams 2 2 Lu (by norm_num) S U a Lam) Bt)) < γ * bondEnergy Bt

theorem constFam_witness_two_sites (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) : ConstFamWitnessTwoS c a := by
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
    perCubeRegularF_constFam_iff.2 hU, hW, covSitesF_two hM hRc, exists_uncovered_bond_two hM hR1, not_covPlaqF_two hM hR1, Bt, h1, h2, hlt⟩

/-- the constant-family body with the class hypothesis `CovSitesF ∧ PerCubeRegularF` (site coverage and per-cube regularity kept; plaquette coverage dropped). -/
def FamilyTorusSitesConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S ∧
              PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

/-- at `ell = 2` the statement keeping site coverage and per-cube regularity (no plaquette coverage) fails, for every `c ≥ 10`, `a > 0`. -/
theorem not_familyTorusSitesConstAt_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    ¬ FamilyTorusSitesConstAt c 2 (le_refl 2) a := by
  rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩
  obtain ⟨m, hm, R, hRR, Lu, α₀, hα, hle, hT, S, hS, Lam, hL, U, -, hreg, hW, hcs, -, -, Bt, h1, h2, hlt⟩ :=
    constFam_witness_two_sites c hc a ha a₀ γ₀ ha₀ hγ m₁ R₁
  have key := hF m hm R hRR 2 (by norm_num) Lu α₀ hα hle hT S hS Lam hL U ⟨hcs, hreg⟩ hW Bt h1 h2
  exact absurd key (not_le.2 hlt)

/-- the body with both coverage clauses holds at `ell = 2` and the body with site coverage and per-cube regularity only (plaquette coverage dropped) fails, for the constant family `constFam c`, `c ≥ 10`, every `a > 0`. (Statement about these two bodies only.) -/
theorem covPlaq_separately_necessary_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c 2 (le_refl 2) a ∧ ¬ FamilyTorusSitesConstAt c 2 (le_refl 2) a :=
  ⟨familyTorusCovConstAt_of_proved hc 2 (le_refl 2) a ha, not_familyTorusSitesConstAt_two c hc a ha⟩

#print axioms covSite_exists
#print axioms covSitesF_two
#print axioms om0_thin_site_two
#print axioms constFam_witness_two_sites
#print axioms not_familyTorusSitesConstAt_two
#print axioms covPlaq_separately_necessary_two

end CovAssume

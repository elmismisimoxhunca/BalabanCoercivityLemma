import CsA1
import CaT2d

/-!
# CsA2 -- which coverage clause is needed, for every `ell ≥ 2` (lane cov_split_20261019)

* `FamilyTorusPlaqConstAt` : the constant-family body with class hypothesis `CovPlaqF ∧ PerCubeRegularF` (plaquette coverage and per-cube regularity; site coverage dropped).
* `familyTorusPlaqConstAt_iff_cov` : it is LOGICALLY EQUIVALENT to `FamilyTorusCovConstAt` (both coverage clauses), by `CsA1.covPlaqF_imp_covSitesF` (no analytic input).
* `familyTorusPlaqConstAt_holds` : it holds, every `ell ≥ 2`, `c ≥ 10`, `a > 0`.
* `plaq_witness_full_not_plaq` : the `ell ≥ 3` refuting configurations (`ConstFamWitnessFull`, uncovered site) also violate `CovPlaqF`.
* `split_table_two`, `split_table_ge_three` : the table.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace CovSplit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open MXQ.AllC
open MXQ.Total
open NcwdhFam
open CovAssume
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.NcwdhStrong

/-- the constant-family body with the class hypothesis `CovPlaqF ∧ PerCubeRegularF` (plaquette coverage and per-cube regularity kept; site coverage dropped). -/
def FamilyTorusPlaqConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            CovPlaqF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S ∧
              PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

theorem two_le_pow {ell m : ℕ} (hell : 2 ≤ ell) (hm : 1 ≤ m) : 2 ≤ ell ^ m :=
  le_trans hell (Nat.le_self_pow (by omega) ell)

/-- on an admissible tower with `2 ≤ M`, the family class hypothesis `ClassCoupledF` (both coverage clauses and regularity) is the same as `CovPlaqF ∧ PerCubeRegularF`. -/
theorem classCoupledF_iff_plaq {L : PeriodicLatticeExtent} {ell M R k : ℕ} {F : CubeFam L} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L}
    (hA : Admissible ell M R k S) (hM : 2 ≤ M) :
    ClassCoupledF ell M F k S α₀ η U ↔ CovPlaqF ell M F k S ∧ PerCubeRegularF ell M F k S α₀ η U := by
  constructor
  · intro h
    obtain ⟨-, hp, hr⟩ := classCoupledF_split.1 h
    exact ⟨hp, hr⟩
  · rintro ⟨hp, hr⟩
    exact classCoupledF_split.2 ⟨covPlaqF_imp_covSitesF hA hM hp, hp, hr⟩

/-- the body keeping plaquette coverage is equivalent to the body keeping both clauses (pure logic + `covPlaqF_imp_covSitesF`). -/
theorem familyTorusPlaqConstAt_iff_cov (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) :
    FamilyTorusPlaqConstAt c ell hell a ↔ FamilyTorusCovConstAt c ell hell a := by
  constructor
  · rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, H⟩
    refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
    intro m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U hcl
    obtain ⟨-, hp, hr⟩ := classCoupledF_split.1 hcl
    exact H m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U ⟨hp, hr⟩
  · rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, H⟩
    refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
    intro m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U ⟨hp, hr⟩
    exact H m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U
      (classCoupledF_split.2 ⟨covPlaqF_imp_covSitesF hS (two_le_pow hell (le_trans hm₁ hm)) hp, hp, hr⟩)

/-- **the plaquette-only body holds**, every `ell ≥ 2`, `c ≥ 10`, `a > 0`. -/
theorem familyTorusPlaqConstAt_holds {c : ℕ} (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FamilyTorusPlaqConstAt c ell hell a :=
  (familyTorusPlaqConstAt_iff_cov c ell hell a).2 (familyTorusCovConstAt_of_proved hc ell hell a ha)

/-- the site-coverage body implies the both-clause body (the hypothesis class of the former contains that of the latter). -/
theorem familyTorusSitesConstAt_imp_cov (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) :
    FamilyTorusSitesConstAt c ell hell a → FamilyTorusCovConstAt c ell hell a := by
  rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, H⟩
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, ?_⟩
  intro m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U hcl
  obtain ⟨hs, -, hr⟩ := classCoupledF_split.1 hcl
  exact H m hm R hR k hk Lu α₀ hα hcm hT S hS Lam hL U ⟨hs, hr⟩

/-- the `ell ≥ 3` refuting configurations: `NtFam4.ConstFamWitnessFull` with the extra conjuncts `1 ≤ m` and `¬ CovPlaqF`. -/
def ConstFamWitnessFullP (c ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) : Prop :=
  ∀ (a₀ γ : ℝ), 0 < a₀ → 0 < γ → ∀ (m₁ R₁ : ℕ),
    ∃ m : ℕ, m₁ ≤ m ∧ 1 ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧ ∃ Lu : PeriodicLatticeExtent, ∃ α₀ : ℝ, 0 < α₀ ∧
      (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ TorusOK ell (ell ^ m) Lu ∧
      ∃ S : Tower (scaleUp ell 2 Lu), Admissible ell (ell ^ m) R 2 S ∧
      ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R 2 S Lam ∧
      ∃ U : LinkCfg (scaleUp ell 2 Lu),
        (∃ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c 2 S sites j) ∧
        PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell 2 Lu)) 2 S α₀ ((ell : ℝ) ^ 2)⁻¹ U ∧
        GenP.WellDefG (gparams ell 2 Lu (by omega) S U a Lam) ∧
        (∃ x ∈ S.Om 0, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c 2 S sites j → x ∉ sites) ∧
        ¬ CovSitesF ell (ell ^ m) (constFam c (scaleUp ell 2 Lu)) 2 S ∧
        ¬ CovPlaqF ell (ell ^ m) (constFam c (scaleUp ell 2 Lu)) 2 S ∧
        ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
          GenP.genForm (gparams ell 2 Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell 2 Lu (by omega) S U a Lam) Bt)) < γ * bondEnergy Bt

/-- at `ell ≥ 3` the refuting configurations of `NtFam4.ConstFamWitnessFull` violate BOTH coverage clauses. -/
theorem plaq_witness_full_not_plaq (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) (ha : 0 < a) :
    ConstFamWitnessFullP c ell hell3 a := by
  intro a₀ γ ha₀ hγ m₁ R₁
  obtain ⟨m, hm, R, hR, Lu, α₀, hα, hle, hT, S, hS, Lam, hL, U, hcube, hreg, hW, hx, hns, Bt, h1, h2, hlt⟩ :=
    (famConst_all c hc ell hell3 a ha).2 a₀ γ ha₀ hγ (max m₁ 1) R₁
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, le_trans (le_max_left _ _) hm, hm1, R, hR, Lu, α₀, hα, hle, hT, S, hS, Lam, hL, U, hcube, hreg, hW, hx, hns, ?_, Bt, h1, h2, hlt⟩
  intro hp
  exact hns (covPlaqF_imp_covSitesF hS (two_le_pow (by omega) hm1) hp)

/-- `ell = 2`: both-clause and plaquette-only bodies hold; site-only and coverage-free bodies fail. -/
theorem split_table_two (c : ℕ) (hc : 10 ≤ c) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c 2 (le_refl 2) a ∧ FamilyTorusPlaqConstAt c 2 (le_refl 2) a ∧
      ¬ FamilyTorusSitesConstAt c 2 (le_refl 2) a ∧ ¬ FamilyTorusNCConstAt c 2 (le_refl 2) a :=
  ⟨familyTorusCovConstAt_of_proved hc 2 (le_refl 2) a ha, familyTorusPlaqConstAt_holds hc 2 (le_refl 2) a ha,
    not_familyTorusSitesConstAt_two c hc a ha, famConst_ge_two c hc 2 (le_refl 2) a ha⟩

/-- `ell ≥ 3`: both-clause and plaquette-only bodies hold; the coverage-free body fails, and its refuting configurations violate both coverage clauses.
(The site-only body at `ell ≥ 3` is NOT decided here.) -/
theorem split_table_ge_three (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c ell (by omega) a ∧ FamilyTorusPlaqConstAt c ell (by omega) a ∧
      ¬ FamilyTorusNCConstAt c ell (by omega) a ∧ ConstFamWitnessFullP c ell hell3 a :=
  ⟨familyTorusCovConstAt_of_proved hc ell (by omega) a ha, familyTorusPlaqConstAt_holds hc ell (by omega) a ha,
    famConst_ge_two c hc ell (by omega) a ha, plaq_witness_full_not_plaq c hc ell hell3 a ha⟩

/-- the converse of `covPlaqF_imp_covSitesF` fails: on the explicit `ell = 2` tower `neS 2 M R` site coverage holds and plaquette coverage fails. -/
theorem sites_not_imp_plaq [CfData] {M R : ℕ} (hM : 0 < M) (hR : CfData.cf ≤ R) :
    CovSitesF 2 M (constFam CfData.cf (scaleUp 2 2 (neLu M R))) 2 (neS 2 M R) ∧
      ¬ CovPlaqF 2 M (constFam CfData.cf (scaleUp 2 2 (neLu M R))) 2 (neS 2 M R) :=
  ⟨covSitesF_two hM hR, not_covPlaqF_two hM (le_trans (by have := CfData.hcf; omega) hR)⟩

#print axioms covPlaqF_imp_covSitesF
#print axioms classCoupledF_iff_plaq
#print axioms familyTorusPlaqConstAt_iff_cov
#print axioms familyTorusPlaqConstAt_holds
#print axioms familyTorusSitesConstAt_imp_cov
#print axioms plaq_witness_full_not_plaq
#print axioms split_table_two
#print axioms split_table_ge_three
#print axioms sites_not_imp_plaq

end CovSplit

import NfFam

/-!
# NfFam2 -- the constant-family form (lane ncwdh_family_20261018, response to prosecution finding D1)

`NfFam.not_P428Target8FamilyTorusNC` quantifies over EVERY family `F`, so it is partly cheap (F = ∅ also refutes it).  Here the family is FIXED by the statement:
`constFam c` = the family of ALL triples `(s, j, c)` (every described cube at factor `c`).  Reading: even when every class cube carries the same factor `c ≥ 10` and is regular,
without coverage the inequality fails.  `perCubeRegularF_constFam_iff` pins `PerCubeRegularF (constFam c) ↔ PerCubeRegular2 .. c ..` (false for `F = ∅`).
Part (2): at the refuting configuration, the two coverage clauses do NOT both hold for `constFam c` (`witness_not_both_coverage`); which one fails is not exposed by the witness.
-/
set_option autoImplicit false

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.CoverStrong
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open MXQ.AllC
open MXQ.Total
open AdalyFormal.NcwdhStrong

/-- every described cube at factor `c`. -/
def constFam (c : ℕ) (L : PeriodicLatticeExtent) : CubeFam L := {t | t.2.2 = c}

theorem mem_constFam {c : ℕ} {L : PeriodicLatticeExtent} {s : Set (PeriodicLatticeSite L)} {j f : ℕ} :
    (s, j, f) ∈ constFam c L ↔ f = c := Iff.rfl

/-- PIN: regularity of every member of `constFam c` is `PerCubeRegular2` at factor `c` (fails for `∅`). -/
theorem perCubeRegularF_constFam_iff {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    PerCubeRegularF ell M (constFam c L) k S α₀ η U ↔ PerCubeRegular2 ell M c k S α₀ η U := by
  rw [perCubeRegular2_iff]
  constructor
  · intro h sites j hq; exact h c sites j rfl hq
  · intro h f sites j hm hq
    have hf : f = c := mem_constFam.1 hm
    rw [hf] at hq ⊢
    exact h sites j hq

/-- the body of the coverage-free family headline with the family FIXED to `constFam c`. -/
def FamilyTorusNCConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

/-- the all-families body at `(ell, a)` implies the constant-family body at every `c ≥ 10`. -/
theorem familyTorusNCAt.toConst {c : ℕ} (hc : 10 ≤ c) {ell : ℕ} {hell : 2 ≤ ell} {a : ℝ}
    (h : FamilyTorusNCAt ell hell a) : FamilyTorusNCConstAt c ell hell a := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := h
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα hle hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R hR k hk Lu α₀ hα (constFam c (scaleUp ell k Lu))
    (fun s j f hmem => by
      have hf : f = c := mem_constFam.1 hmem
      rw [hf]; exact ⟨hc, hle⟩) hT S hS Lam hL U hU

/-- **(1)** with the family fixed to the constant-`c` family: for every `c ≥ 10`, `ell ≥ 3` with `StagOK`, `a > 0`, no constants make the body hold. -/
theorem not_familyTorusNCConstAt (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : AdalyFormal.CoverOmega.StagOK ell)
    (a : ℝ) (ha : 0 < a) : ¬ FamilyTorusNCConstAt c ell (by omega) a := by
  rintro ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩
  have hfe : FailEllC c ell (by omega) a := by
    letI : CfData := ⟨c, hc⟩
    exact AdalyFormal.CoverOmega.Struct.failEllC_ok ell hell3 hE a ha
  obtain ⟨m, hm, hR⟩ := hfe m₁
  obtain ⟨R, hRR, hfail⟩ := hR R₁
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hα : 0 < a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * (a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hfail _ hα γ₀ hγ
  have key := hF m hm R hRR k hk Lu _ hα hle hT S hS Lam hL U (perCubeRegularF_constFam_iff.2 hU) hW Bt h1 h2
  exact absurd key (not_le.2 hlt)

theorem not_P428Target8FamilyTorusNC_const : ¬ FamilyTorusNCConstAt 12 4 (by norm_num) 1 :=
  not_familyTorusNCConstAt 12 (by norm_num) 4 (by norm_num) (Or.inl (by norm_num)) 1 one_pos

/-- **(2)** at refuting configurations (any constants `a₀, γ`, any lower bounds `m₁, R₁`): the printed objects exist, every class cube of factor `c` is regular,
the inequality fails at `γ`, and the two coverage clauses do NOT both hold for `constFam c`.  (Which of the two fails is not exposed by the witness.) -/
theorem witness_not_both_coverage (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : AdalyFormal.CoverOmega.StagOK ell)
    (a : ℝ) (ha : 0 < a) (a₀ γ : ℝ) (ha₀ : 0 < a₀) (hγ : 0 < γ) (m₁ R₁ : ℕ) :
    ∃ m : ℕ, m₁ ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧ ∃ k : ℕ, 1 ≤ k ∧ ∃ Lu : PeriodicLatticeExtent, ∃ α₀ : ℝ, 0 < α₀ ∧
      (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ TorusOK ell (ell ^ m) Lu ∧
      ∃ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S ∧
      ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R k S Lam ∧
      ∃ U : LinkCfg (scaleUp ell k Lu),
        PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
        GenP.WellDefG (gparams ell k Lu (by omega) S U a Lam) ∧
        ¬ (CovSitesF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S ∧ CovPlaqF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S) ∧
        ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
          GenP.genForm (gparams ell k Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell k Lu (by omega) S U a Lam) Bt)) < γ * bondEnergy Bt := by
  obtain ⟨m₁', hm₁', R₁', a₀', ha₀', γ₀', hγ₀', hF'⟩ := p428Target8FamilyTorus ell (by omega) a ha
  have hfe : FailEllC c ell (by omega) a := by
    letI : CfData := ⟨c, hc⟩
    exact AdalyFormal.CoverOmega.Struct.failEllC_ok ell hell3 hE a ha
  obtain ⟨m, hm, hR⟩ := hfe (max m₁ m₁')
  obtain ⟨R, hRR, hfail⟩ := hR (max R₁ R₁')
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  set b : ℝ := min a₀ a₀' with hb
  have hbpos : 0 < b := lt_min ha₀ ha₀'
  set g : ℝ := min γ γ₀' with hg
  have hgpos : 0 < g := lt_min hγ hγ₀'
  have hα : 0 < b / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * (b / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ))) ≤ b := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨k, hk, Lu, hT, S, hS, Lam, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hfail _ hα g hgpos
  have hmm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hmm2 : m₁' ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨m, hmm1, R, le_trans (le_max_left _ _) hRR, k, hk, Lu, _, hα, le_trans hle (min_le_left _ _), hT, S, hS, Lam, hL, U,
    perCubeRegularF_constFam_iff.2 hU, hW, ?_, Bt, h1, h2, lt_of_lt_of_le hlt (mul_le_mul_of_nonneg_right (min_le_left _ _) (AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _))⟩
  rintro ⟨hcs, hcp⟩
  have hcc : ClassCoupledF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S _ ((ell : ℝ) ^ k)⁻¹ U :=
    classCoupledF_split.2 ⟨hcs, hcp, perCubeRegularF_constFam_iff.2 hU⟩
  have key := (hF' m hmm2 R (le_trans (le_max_right _ _) hRR) k hk Lu _ hα (constFam c (scaleUp ell k Lu))
    (fun s j f hmem => by
      have hf : f = c := mem_constFam.1 hmem
      rw [hf]; exact ⟨hc, le_trans hle (min_le_right _ _)⟩) hT S hS Lam hL U hcc).2 Bt h1 h2
  have h3 : g * bondEnergy Bt ≤ γ₀' * bondEnergy Bt :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (AdalyFormal.Balaban.RegularUPerturbation.bondEnergy_nonneg _)
  linarith

#print axioms perCubeRegularF_constFam_iff
#print axioms familyTorusNCAt.toConst
#print axioms not_familyTorusNCConstAt
#print axioms not_P428Target8FamilyTorusNC_const
#print axioms witness_not_both_coverage

end NcwdhFam

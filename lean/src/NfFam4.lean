import NfFam3

/-!
# NfFam4 -- the full constant-family refutation: class cube present, site coverage fails (lane ncwdh_family_20261018, response to VERDICT2)

`constFam_witness_full`: for every c ≥ 10, ell ≥ 3 with `StagOK ell`, a > 0, any constants `a₀, γ > 0` and any lower bounds `m₁, R₁`, there is a refuting configuration on the nested slab tower (`k = 2`) with
(i) a class cube of factor `c` (`IsClassCube ell M c 2 S sites j`), (ii) every class cube of factor `c` regular (`PerCubeRegularF (constFam c)`, `c M α₀ ≤ a₀`), (iii) `WellDefG`, (iv) a competitor `Bt` with `genForm < γ * bondEnergy Bt`,
(v) a site of `Ω₀` lying in no class cube (so `CovSitesF .. (constFam c)` FAILS: the clause that fails is site coverage).  Regime of (i): `R ≥ c`, class cube of index 1.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega.Struct
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open MXQ.AllC
open MXQ.Total

/-- the refuting configurations for the constant family, as a statement. -/
def ConstFamWitnessFull (c ell : ℕ) (hell3 : 3 ≤ ell) (a : ℝ) : Prop :=
  ∀ (a₀ γ : ℝ), 0 < a₀ → 0 < γ → ∀ (m₁ R₁ : ℕ),
    ∃ m : ℕ, m₁ ≤ m ∧ ∃ R : ℕ, R₁ ≤ R ∧ ∃ Lu : PeriodicLatticeExtent, ∃ α₀ : ℝ, 0 < α₀ ∧
      (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ ∧ TorusOK ell (ell ^ m) Lu ∧
      ∃ S : Tower (scaleUp ell 2 Lu), Admissible ell (ell ^ m) R 2 S ∧
      ∃ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R 2 S Lam ∧
      ∃ U : LinkCfg (scaleUp ell 2 Lu),
        (∃ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c 2 S sites j) ∧
        PerCubeRegularF ell (ell ^ m) (constFam c (scaleUp ell 2 Lu)) 2 S α₀ ((ell : ℝ) ^ 2)⁻¹ U ∧
        GenP.WellDefG (gparams ell 2 Lu (by omega) S U a Lam) ∧
        (∃ x ∈ S.Om 0, ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 Lu))) (j : ℕ), IsClassCube ell (ell ^ m) c 2 S sites j → x ∉ sites) ∧
        ¬ CovSitesF ell (ell ^ m) (constFam c (scaleUp ell 2 Lu)) 2 S ∧
        ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧
          GenP.genForm (gparams ell 2 Lu (by omega) S U a Lam)
            (WithLp.toLp 2 (GenP.genC (gparams ell 2 Lu (by omega) S U a Lam) Bt)) < γ * bondEnergy Bt

theorem constFam_witness_full (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : AdalyFormal.CoverOmega.StagOK ell)
    (a : ℝ) (ha : 0 < a) : ConstFamWitnessFull c ell hell3 a := by
  intro a₀ γ ha₀ hγ m₁ R₁
  letI : CfData := ⟨c, hc⟩
  obtain ⟨m, hm, hR⟩ := failEllCS_ok ell hell3 hE a ha m₁
  obtain ⟨R, hRR, hfail⟩ := hR (max (max R₁ c) 1)
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hRR
  have hRc : c ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRR
  have hMpos : (0 : ℝ) < ((ell ^ m : ℕ) : ℝ) := by
    have : 0 < ell ^ m := pow_pos (by omega) m
    exact_mod_cast this
  have hM : 0 < ell ^ m := pow_pos (by omega) m
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hα : 0 < a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ)) := by positivity
  have hle : (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * (a₀ / ((c : ℝ) * ((ell ^ m : ℕ) : ℝ))) ≤ a₀ := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  obtain ⟨hT, hA, hL, U, hU, hW, Bt, h1, h2, hlt⟩ := hfail _ hα γ hγ
  -- the uncovered site on the layer `x₀ = neC`
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell3 hM hR1
  obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := ell ^ m) hell3
  have hN := ne_scaleUp (ell := ell) (R := R) (by omega) hM
  have hCN : neC ell (ell ^ m) R < neN ell (ell ^ m) R := by
    simp only [neC, neA', neN]; omega
  let x : PeriodicLatticeSite (scaleUp ell 2 (neLu (ell ^ m) R)) :=
    fun μ => ⟨if μ = 0 then neC ell (ell ^ m) R else 0, by have := hN μ; split_ifs <;> omega⟩
  have hx0 : (x 0).val = neC ell (ell ^ m) R := by simp [x]
  have hunc : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell 2 (neLu (ell ^ m) R)))) (j : ℕ),
      IsClassCube ell (ell ^ m) c 2 (neS ell (ell ^ m) R) sites j → x ∉ sites :=
    fun sites j hq => ne_layer_uncovered hell3 hM hR1 x hx0 sites j hq
  refine ⟨m, hm, R, le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRR, neLu (ell ^ m) R, _, hα, hle, hT, neS ell (ell ^ m) R, hA,
    neLam (ell ^ m) R, hL, U, exists_classCube_ne hell3 hM hR1 hRc, perCubeRegularF_constFam_iff.2 hU, hW,
    ⟨x, (ne_layer_mem hell3 hM hR1 x hx0).2, hunc⟩, ?_, Bt, h1, h2, hlt⟩
  intro hcov
  obtain ⟨sites, j, ⟨f, hmem, hq⟩, hxs⟩ := hcov x (ne_layer_mem hell3 hM hR1 x hx0).2
  have hf : f = c := mem_constFam.1 hmem
  rw [hf] at hq
  exact hunc sites j hq hxs

/-- **headline, constant family**: the body fails for `constFam c`, AND the refuting configurations have a class cube, all class cubes regular, `WellDefG`, an uncovered site of `Ω₀`, and a failing competitor. -/
theorem constFam_headline (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : AdalyFormal.CoverOmega.StagOK ell)
    (a : ℝ) (ha : 0 < a) : ¬ FamilyTorusNCConstAt c ell (by omega) a ∧ ConstFamWitnessFull c ell hell3 a :=
  ⟨not_familyTorusNCConstAt c hc ell hell3 hE a ha, constFam_witness_full c hc ell hell3 hE a ha⟩

#print axioms constFam_witness_full
#print axioms constFam_headline

end NcwdhFam

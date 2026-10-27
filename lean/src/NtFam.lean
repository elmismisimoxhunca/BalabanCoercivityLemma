import MXQ_Tor
import NtCvOS16

/-!
# NfFam -- the per-cube family headline WITHOUT coverage FAILS (lane ncwdh_family_20261018)

`P428Target8FamilyTorusNC` is `MXQ.Total.P428Target8FamilyTorus` with exactly two changes (mirroring `CvS1.P428Target8NCWDH`):
(1) `ClassCoupledF` is replaced by its third conjunct only (per-member regularity; the site-coverage and plaquette-coverage conjuncts removed);
(2) the conclusion `InstAtWD` (= `WellDefG ∧ InstIneq`) is replaced by `CvS1.InstIneqWDH` (= `WellDefG → InstIneq`).
Everything else (constants m₁, R₁, a₀, γ₀ before m, R; the family F chosen after k, Lu, m, R, α₀; per-member `10 ≤ f` and `f M α₀ ≤ a₀`) is literally as in FamilyTorus.
-/
set_option autoImplicit false

namespace NcwdhFam

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC
open MXQ.Total
open AdalyFormal.CoverStrong (InstIneqWDH)
open AdalyFormal.NcwdhStrong

/-- first conjunct of `ClassCoupledF`: site coverage of `Ω₀`. -/
def CovSitesF {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) : Prop :=
  ∀ x ∈ S.Om 0, ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeF ell M F k S sites j ∧ x ∈ sites

/-- second conjunct of `ClassCoupledF`: plaquette coverage. -/
def CovPlaqF {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L, (∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond (S.Om 0) e) →
    ∃ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCubeF ell M F k S sites j ∧
      ∀ e ∈ periodicPlaquetteBoundaryEdges p, CubeBond sites e

/-- third conjunct of `ClassCoupledF`: every described cube of `F` is regular with its own factor. -/
def PerCubeRegularF {L : PeriodicLatticeExtent} (ell M : ℕ) (F : CubeFam L) (k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (f : ℕ) (sites : Set (PeriodicLatticeSite L)) (j : ℕ), (sites, j, f) ∈ F →
    IsClassCube ell M f k S sites j → RegBodyH ell M f sites j α₀ η U

/-- PIN: `ClassCoupledF` is exactly the two coverage clauses plus `PerCubeRegularF`; the NC class hypothesis is the third. -/
theorem classCoupledF_split {L : PeriodicLatticeExtent} {ell M : ℕ} {F : CubeFam L} {k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledF ell M F k S α₀ η U ↔ CovSitesF ell M F k S ∧ CovPlaqF ell M F k S ∧ PerCubeRegularF ell M F k S α₀ η U := Iff.rfl

/-- the per-`(ell, a)` body of the coverage-free family headline. -/
def FamilyTorusNCAt (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            PerCubeRegularF ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

/-- **the coverage-free family headline (WellDefG as hypothesis).** -/
def P428Target8FamilyTorusNC : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FamilyTorusNCAt ell hell a

/-- PIN: the headline is the `∀ ell a` of the per-`(ell, a)` body. -/
theorem familyTorusNC_iff : P428Target8FamilyTorusNC ↔ ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FamilyTorusNCAt ell hell a := Iff.rfl

/-- the per-`(ell, a)` form: for EVERY cube factor `c ≥ 10` (the constant family), every `ell ≥ 3` with `StagOK`, every `a > 0`. -/
theorem not_familyTorusNCAt (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell3 : 3 ≤ ell) (hE : AdalyFormal.CoverOmega.StagOK ell)
    (a : ℝ) (ha : 0 < a) : ¬ FamilyTorusNCAt ell (by omega) a := by
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
  have key := hF m hm R hRR k hk Lu _ hα
    {t | t.2.2 = c}
    (fun s j f hmem => by
      have hf : f = c := hmem
      rw [hf]; exact ⟨hc, hle⟩)
    hT S hS Lam hL U
    (fun f sites j hmem hq => by
      have hf : f = c := hmem
      rw [hf] at hq ⊢
      exact (perCubeRegular2_iff.1 hU) sites j hq) hW Bt h1 h2
  exact absurd key (not_le.2 hlt)

/-- **`¬ P428Target8FamilyTorusNC`.** -/
theorem not_P428Target8FamilyTorusNC : ¬ P428Target8FamilyTorusNC := fun H =>
  not_familyTorusNCAt 12 (by norm_num) 4 (by norm_num) (Or.inl (by norm_num)) 1 one_pos (H 4 (by norm_num) 1 one_pos)

#print axioms classCoupledF_split
#print axioms not_familyTorusNCAt
#print axioms not_P428Target8FamilyTorusNC

end NcwdhFam

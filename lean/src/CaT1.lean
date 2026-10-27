import NtFam2
import TT_F
import NsCS1

/-!
# CaT1 -- the coverage-assuming statement in the granting-existence (WDH) form (lane cov_assume_20261019)

`NcwdhBodyAt c ell hell a` (NsCS1) is the coverage-free body with `WellDefG` as a hypothesis of the conclusion.  Here the SAME body is stated with the class
hypothesis `ClassCoupled ell M c k S α₀ η U` (ZR6A:124 = `CoversOm0p ∧ PerCubeRegular2`, i.e. BOTH coverage clauses retained, one cube factor `c` in all three
conjuncts) instead of `PerCubeRegular2 ell M c k S α₀ η U`.  Nothing else is changed: `SidePow6`, the `∃ m₀ ∀ m ∃ R₀ ∀ R` shape, `∃ a₀ γ₀` after `R`, `c·M·α₀ ≤ a₀`, `InstIneqWDH`.

* `CoercG8AtNCWDHcov`, `P428Core8NCWDHcovc`, `P428Genuine8NCWDHcovc`, `NcwdhCovBodyAt`, `P428Target8NCWDHcov` : the statement.
* `p428Target8NCWDHcov_of_total` : proved from `AdalyFormal.Total.p428Target8Total` (weakening `WellDefG ∧ ineq` to `WellDefG → ineq`), for every `c ≥ 10`.
* the family forms: `FamilyTorusCovAt` (any family `F`, class `ClassCoupledF`) and `FamilyTorusCovConstAt c` (`F = constFam c`), both proved from `MXQ.Total.p428Target8FamilyTorus`.
* `classCoupledF_constFam_iff` : `ClassCoupledF (constFam c) ↔ ClassCoupled c` (the two class predicates agree for the constant family).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace CovAssume

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.NoCover
open AdalyFormal.CoverStrong
open AdalyFormal.NcwdhStrong
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC
open MXQ.Total
open NcwdhFam

/-- `CvS1.CoercG8AtNCWDH` with `PerCubeRegular2` replaced by `ClassCoupled` (both coverage clauses retained). -/
def CoercG8AtNCWDHcov (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqWDH ell k hell a Lu γ₀ S Lam U

/-- `P428Core8NCWDHc` with the covering inner claim. -/
def P428Core8NCWDHcovc (c ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (c : ℝ) * M * α₀ ≤ a₀ →
      CoercG8AtNCWDHcov ell M R k hell a Lu c α₀ γ₀

/-- `P428Genuine8NCWDHc` with the covering core. -/
def P428Genuine8NCWDHcovc (c ell M R : ℕ) (hell : 0 < ell) (a : ℝ) : Prop :=
  SidePow6 ell M a ∧ P428Core8NCWDHcovc c ell M R hell a

/-- `NcwdhBodyAt` with the covering class: the per-`(ell, a)` body of the coverage-assuming granting-existence statement. -/
def NcwdhCovBodyAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
  ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    P428Genuine8NCWDHcovc c ell (ell ^ m) R (by omega) a

/-- the coverage-assuming headline at cube factor `c`. -/
def P428Target8NCWDHcov (c : ℕ) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → NcwdhCovBodyAt c ell hell a

/-- PIN: the covering inner claim is the coverage-free one with the class hypothesis `CoversOm0p ∧ PerCubeRegular2` in place of `PerCubeRegular2`. -/
theorem coercCov_iff {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {c : ℕ} {α₀ γ₀ : ℝ} :
    CoercG8AtNCWDHcov ell M R k hell a Lu c α₀ γ₀ ↔
      (TorusOK ell M Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)),
          CoversOm0p ell M c k S ∧ PerCubeRegular2 ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          InstIneqWDH ell k hell a Lu γ₀ S Lam U) := Iff.rfl

/-- PIN: both coverage clauses are inside `CoversOm0p`. -/
theorem coversOm0p_def {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} :
    CoversOm0p ell M c k S ↔ CoversOm0c ell M c k S ∧ CoversPlaqOm0c ell M c k S := Iff.rfl

/-- the coverage-free inner claim implies the covering inner claim (retaining coverage only adds hypotheses). -/
theorem coercNC_imp_cov {ell M R k : ℕ} {hell : 0 < ell} {a : ℝ} {Lu : PeriodicLatticeExtent} {c : ℕ} {α₀ γ₀ : ℝ}
    (h : CoercG8AtNCWDH ell M R k hell a Lu c α₀ γ₀) : CoercG8AtNCWDHcov ell M R k hell a Lu c α₀ γ₀ :=
  fun hT S hS Lam hL U hU => h hT S hS Lam hL U hU.2

/-- **the coverage-assuming granting-existence statement holds** (every cube factor `c ≥ 10`), by weakening `p428Target8Total`. -/
theorem p428Target8NCWDHcov_of_total (c : ℕ) (hc : 10 ≤ c) : P428Target8NCWDHcov c := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := AdalyFormal.Total.p428Target8Total ell hell a ha
  refine ⟨m₁, hm₁, fun m hm => ⟨R₁, fun R hR => ⟨⟨hell, ⟨m, le_trans hm₁ hm, rfl⟩, ha⟩, a₀, ha₀, γ₀, hγ, ?_⟩⟩⟩
  intro k hk Lu α₀ hα hle hTor S hS Lam hL U hU hW
  exact ((hT c hc m hm R hR k hk Lu α₀ hα hle) hTor S hS Lam hL U hU).2

/-- every `ell ≥ 2`, every `c ≥ 10`, every `a > 0` (the per-`(ell, a)` form). -/
theorem ncwdhCovBodyAt_of_total (c : ℕ) (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    NcwdhCovBodyAt c ell hell a := p428Target8NCWDHcov_of_total c hc ell hell a ha

/-! ## the family forms -/

/-- `FamilyTorusNCAt` with `ClassCoupledF` (both coverage clauses and per-member regularity) in place of `PerCubeRegularF`. -/
def FamilyTorusCovAt (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        ∀ F : CubeFam (scaleUp ell k Lu),
          (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledF ell (ell ^ m) F k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

theorem familyTorusCovAt_of_proved (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) : FamilyTorusCovAt ell hell a := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := p428Target8FamilyTorus ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU hW =>
    (hF m hm R hR k hk Lu α₀ hα F hFs hT S hS Lam hL U hU).2⟩

/-- `FamilyTorusNCConstAt` with `ClassCoupledF (constFam c)` in place of `PerCubeRegularF (constFam c)`. -/
def FamilyTorusCovConstAt (c ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) : Prop :=
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledF ell (ell ^ m) (constFam c (scaleUp ell k Lu)) k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqWDH ell k (by omega) a Lu γ₀ S Lam U

theorem familyTorusCovConstAt_of_proved {c : ℕ} (hc : 10 ≤ c) (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 0 < a) :
    FamilyTorusCovConstAt c ell hell a := by
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hF⟩ := familyTorusCovAt_of_proved ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα hle hT S hS Lam hL U hU => ?_⟩
  exact hF m hm R hR k hk Lu α₀ hα (constFam c (scaleUp ell k Lu))
    (fun s j f hmem => by
      have hf : f = c := mem_constFam.1 hmem
      rw [hf]; exact ⟨hc, hle⟩) hT S hS Lam hL U hU

/-- PIN: for the constant family, the family class predicate is the single-factor `ClassCoupled`. -/
theorem classCoupledF_constFam_iff {L : PeriodicLatticeExtent} {ell M c k : ℕ} {S : Tower L} {α₀ η : ℝ} {U : LinkCfg L} :
    ClassCoupledF ell M (constFam c L) k S α₀ η U ↔ ClassCoupled ell M c k S α₀ η U := by
  have hI : ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      IsClassCubeF ell M (constFam c L) k S sites j ↔ IsClassCube ell M c k S sites j := by
    intro sites j
    constructor
    · rintro ⟨f, hf, hq⟩
      have : f = c := mem_constFam.1 hf
      rw [this] at hq; exact hq
    · intro hq; exact ⟨c, rfl, hq⟩
  rw [classCoupledF_split, ClassCoupled, coversOm0p_def, CoversOm0c, CoversPlaqOm0c, CovSitesF, CovPlaqF,
    perCubeRegularF_constFam_iff]
  simp only [hI]
  tauto

/-- the family-constant statement and the single-factor statement have the same hypothesis at each point. -/
theorem familyTorusCovConstAt_iff_classCoupled {c ell : ℕ} {hell : 2 ≤ ell} {a : ℝ} :
    FamilyTorusCovConstAt c ell hell a ↔
      ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (c : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
            CoercG8AtNCWDHcov ell (ell ^ m) R k (by omega) a Lu c α₀ γ₀ := by
  unfold FamilyTorusCovConstAt CoercG8AtNCWDHcov
  simp only [classCoupledF_constFam_iff]

#print axioms coercCov_iff
#print axioms coversOm0p_def
#print axioms coercNC_imp_cov
#print axioms p428Target8NCWDHcov_of_total
#print axioms ncwdhCovBodyAt_of_total
#print axioms familyTorusCovAt_of_proved
#print axioms familyTorusCovConstAt_of_proved
#print axioms classCoupledF_constFam_iff
#print axioms familyTorusCovConstAt_iff_classCoupled

end CovAssume

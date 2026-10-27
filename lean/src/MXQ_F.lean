import MXQ_B
import MXQ_C

/-!
# MXQ_F -- **`P428Target8Family`**: the family reading (lane mixed_20261017, round 2)

The mixed headline (`MX_F.P428Target8Mixed`) assumes that EVERY described cube of every admitted factor is regular.  The proof only applies the regularity of a cube to cubes obtained from the COVERAGE hypothesis.
`P428Target8Family` assumes only: a family `Fm` of described cubes (triples `(sites, j, f)`, factor `f ≥ 10`, no other restriction) that covers the sites and plaquettes of `Ω₀`, each member regular with ITS OWN printed bound `f M α (ell^j η)^{-n}`
(`ClassCoupledQ`, MXQ_Orig), per-member smallness `f M α₀ ≤ a₀`.  Constants `m₁, R₁, a₀, γ₀` are chosen before the family.
* `p428Target8Family : P428Target8Family`,
* `P428Target8Family.toMixed : MXP.Total.P428Target8Mixed` (`Fm L = {(s, j, f) | f ∈ Φ}`), hence `.toTotal`.
-/
set_option autoImplicit false

namespace MXQ.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXQ.AllC

/-- the inner claim for a family class. -/
def CoercG8AtWDFamily (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (Fm : CF) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledQ ell M Fm k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstAtWD ell k hell a Lu γ₀ S Lam U

/-- **the family headline.** -/
def P428Target8Family : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Fm : CF, CubeFamOK Fm → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ (L : PeriodicLatticeExtent) (s : Set (PeriodicLatticeSite L)) (j f : ℕ), (s, j, f) ∈ Fm L → (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          CoercG8AtWDFamily ell (ell ^ m) R k (by omega) a Lu Fm α₀ γ₀

theorem fieldsTQ :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKT ell (by omega) a) ∧ OpLayerThickT ∧ ClassRightInvT := by
  have hB : BallChartsGT := ballChartsGT_proved
  have hRI : ClassRightInvT := classRightInvT_of_cov hB (classRightInvCovT hB)
  exact ⟨fun _ hell a ha => fieldsKT_of_ball (ballChartsT_of_G hB) hell a ha, opLayerThickT_of hB hRI, hRI⟩

/-- **`P428Target8Family`, proved.** -/
theorem p428Target8Family : P428Target8Family := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hcore⟩ := strong_coreTM fieldsTQ.1 fieldsTQ.2.1 fieldsTQ.2.2 hell (by omega) ha
  refine ⟨m₀, hm₀, R₀, a₀, ha₀, γ₀, hγ, fun Fm hFm m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT S hS Lam hL U hU
  obtain ⟨hI, hW⟩ := hcore Fm hFm m hm R hR k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

end MXQ.Total

#print axioms MXQ.Total.p428Target8Family

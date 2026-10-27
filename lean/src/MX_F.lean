import MX_B
import MX_C
import TT_F

/-!
# MX_F -- **`P428Target8Mixed`**: the per-cube factor reading of Balaban's class (lane mixed_20261017)

CMP99b p.396 (page image `corpus/renders/CMP99b_p396-08.png`): "for an arbitrary cube □ of the described above class ... if the index of □ is j, then |A| < O(1)Mα₀(L^jη)^{-1} ...
where O(1)M is a size of □ in T_{L^{-j}}": the number `O(1) ≥ 10` is a property of the cube (its side divided by `M ℓ^j`).

`Φ : Set ℕ` is ANY set of admitted cube factors (every member `≥ 10`, no upper bound, no finiteness).  The mixed class is ALL described cubes whose factor lies in `Φ`, each regular with ITS OWN
printed bound (`PerCubeRegularΦ`), and the sites and plaquettes of `Ω₀` are covered by such cubes (`CoversOmΦ`).  Smallness is per cube: `f M α₀ ≤ a₀` for every `f ∈ Φ`.
All four constants `m₁, R₁, a₀, γ₀` are chosen before `Φ`.

* `p428Target8Mixed : P428Target8Mixed`,
* `P428Target8Mixed.toTotal : AdalyFormal.Total.P428Target8Total`  (`Φ = {c}`; `classCoupledΦ_single`).
-/
set_option autoImplicit false

namespace MXP.Total

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open MXP.AllC

/-- the inner claim for the mixed class (the r8 `CoercG8AtWD` with `ClassCoupled ell M c` replaced by `ClassCoupledΦ ell M Φ`). -/
def CoercG8AtWDMixed (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (Φ : Set ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupledΦ ell M Φ k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstAtWD ell k hell a Lu γ₀ S Lam U

/-- **the mixed per-cube-factor headline.** -/
def P428Target8Mixed : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Φ : Set ℕ, (∀ f ∈ Φ, 10 ≤ f) → ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (∀ f ∈ Φ, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) →
          CoercG8AtWDMixed ell (ell ^ m) R k (by omega) a Lu Φ α₀ γ₀

theorem fieldsTM :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKT ell (by omega) a) ∧ OpLayerThickT ∧ ClassRightInvT := by
  have hB : BallChartsGT := ballChartsGT_proved
  have hRI : ClassRightInvT := classRightInvT_of_cov hB (classRightInvCovT hB)
  exact ⟨fun _ hell a ha => fieldsKT_of_ball (ballChartsT_of_G hB) hell a ha, opLayerThickT_of hB hRI, hRI⟩

/-- **`P428Target8Mixed`, proved.** -/
theorem p428Target8Mixed : P428Target8Mixed := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hcore⟩ := strong_coreTM fieldsTM.1 fieldsTM.2.1 fieldsTM.2.2 hell (by omega) ha
  refine ⟨m₀, hm₀, R₀, a₀, ha₀, γ₀, hγ, fun Φ hΦ m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT S hS Lam hL U hU
  obtain ⟨hI, hW⟩ := hcore Φ hΦ m hm R hR k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

/-- `Mixed ⟹ Total` (`Φ = {c}`). -/
theorem P428Target8Mixed.toTotal (h : P428Target8Mixed) : AdalyFormal.Total.P428Target8Total := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, hT⟩ := h ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun c hc m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT' S hS Lam hL U hU
  exact hT {c} (fun f hf => by rw [Set.mem_singleton_iff] at hf; omega) m hm R hR k hk Lu α₀ hα
    (fun f hf => by rw [Set.mem_singleton_iff] at hf; subst hf; exact h2) hT' S hS Lam hL U (classCoupledΦ_single.2 hU)

theorem p428Target8Total_fromMixed : AdalyFormal.Total.P428Target8Total := p428Target8Mixed.toTotal

end MXP.Total

#print axioms MXP.Total.p428Target8Mixed
#print axioms MXP.Total.P428Target8Mixed.toTotal
#print axioms MXP.Total.p428Target8Total_fromMixed

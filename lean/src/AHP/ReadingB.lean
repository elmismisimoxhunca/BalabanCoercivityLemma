import THL6
import RB2

set_option autoImplicit false

namespace AdalyFormal.Fidelity.SheetVariants

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.ThinLayer (AdmNoBase Target8Layer)
open AdalyFormal.RBridge (Om0Unit)

def ReadingBTower {L : PeriodicLatticeExtent}
    (ell M R k : ℕ) (S : Tower L) : Prop :=
  AdmNoBase ell M R k S ∧ S.Om 0 = Om0Unit ell M R k (S.Om 1)

def P428Target8_ReadingB : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        SidePow6 ell (ell ^ m) a ∧
        ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
          ∀ k : ℕ, 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ),
            0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
            TorusOK ell (ell ^ m) Lu →
            ∀ S : Tower (scaleUp ell k Lu), ReadingBTower ell (ell ^ m) R k S →
            ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R k S Lam →
            ∀ U : LinkCfg (scaleUp ell k Lu),
              ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
                InstIneq ell k (by omega) a Lu γ₀ S Lam U

/-- Restrict the same layer headline to the reading-B tower predicate. -/
theorem readingB_of_layer : Target8Layer → P428Target8_ReadingB := by
  intro h ell hell a ha
  obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
  refine ⟨m₀, hm₀, fun m hmm => ?_⟩
  obtain ⟨R₀, hR⟩ := hm m hmm
  refine ⟨R₀, fun R hRR => ?_⟩
  obtain ⟨hp, a₀, ha₀, γ₀, hγ₀, hc⟩ := hR R hRR
  refine ⟨hp, a₀, ha₀, γ₀, hγ₀,
    fun k hk Lu α₀ hα hcap hTor S hS Lam hLam U hU => ?_⟩
  exact hc k hk Lu α₀ hα hcap hTor S hS.1 Lam hLam U hU

end AdalyFormal.Fidelity.SheetVariants


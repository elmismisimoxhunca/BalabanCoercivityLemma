import ZT5A
import AdalyFormal.Balaban.RMapLipschitz

set_option autoImplicit false

namespace AdalyFormal.Fidelity.SheetVariants

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm)

noncomputable def bondEnergyHS {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, frobSq (A b : Matrix (Fin 2) (Fin 2) ℂ)

def InstIneqHS (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergyHS Bt ≤
      GenP.genForm (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

def CoercG8AtHS (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
    ∀ S : Tower (scaleUp ell k Lu), Admissible ell M R k S →
    ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam →
    ∀ U : LinkCfg (scaleUp ell k Lu),
      ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        InstIneqHS ell k hell a Lu γ₀ S Lam U

def P428Target8_HS : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        SidePow6 ell (ell ^ m) a ∧
        ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
          ∀ k : ℕ, 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ),
            0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
              CoercG8AtHS ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀

theorem bondEnergyHS_eq_two {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) :
    bondEnergyHS A = 2 * bondEnergy A := by
  unfold bondEnergyHS bondEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [AdalyFormal.Balaban.RMapLipschitz.norm_sq_eq_half_frobSq]
  ring

theorem instIneqHS_iff (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) :
    InstIneqHS ell k hell a Lu (γ / 2) S Lam U ↔
      InstIneq ell k hell a Lu γ S Lam U := by
  have hscale : ∀ x : ℝ, γ / 2 * (2 * x) = γ * x := by
    intro x
    ring
  simp only [InstIneqHS, InstIneq, bondEnergyHS_eq_two, hscale]

theorem target_iff_hs : P428Target8 ↔ P428Target8_HS := by
  constructor
  · intro h ell hell a ha
    obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
    refine ⟨m₀, hm₀, ?_⟩
    intro m hmm
    obtain ⟨R₀, hR⟩ := hm m hmm
    refine ⟨R₀, ?_⟩
    intro R hRR
    obtain ⟨hs, a₀, ha₀, γ, hγ, hc⟩ := hR R hRR
    refine ⟨hs, a₀, ha₀, γ / 2, div_pos hγ (by norm_num), ?_⟩
    intro k hk Lu α₀ hα hcap ht S hS Lam hLam U hU
    apply (instIneqHS_iff ell k (by omega) a Lu γ S Lam U).mpr
    exact hc k hk Lu α₀ hα hcap ht S hS Lam hLam U hU
  · intro h ell hell a ha
    obtain ⟨m₀, hm₀, hm⟩ := h ell hell a ha
    refine ⟨m₀, hm₀, ?_⟩
    intro m hmm
    obtain ⟨R₀, hR⟩ := hm m hmm
    refine ⟨R₀, ?_⟩
    intro R hRR
    obtain ⟨hs, a₀, ha₀, γ, hγ, hc⟩ := hR R hRR
    refine ⟨hs, a₀, ha₀, 2 * γ, mul_pos (by norm_num) hγ, ?_⟩
    intro k hk Lu α₀ hα hcap ht S hS Lam hLam U hU
    apply (instIneqHS_iff ell k (by omega) a Lu (2 * γ) S Lam U).mp
    simpa only [show (2 * γ) / 2 = γ by ring] using
      hc k hk Lu α₀ hα hcap ht S hS Lam hLam U hU

end AdalyFormal.Fidelity.SheetVariants


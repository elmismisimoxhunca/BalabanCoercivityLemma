import DLR97

/-!
# DL98 -- the existential constants of `M0Core_general` cannot empty its domain: for EVERY `a₀ > 0` the class contains a curved field

* `M0Core_domain_curved ℓ M k a₀` (`2 ≤ ℓ`, `1 ≤ M`, `0 < a₀`): on the torus `LuLM ℓ M = (16ℓM)³` the amplitude
  `α₀ = min(a₀,1)/(12M)` satisfies `0 < α₀`, `12Mα₀ ≤ a₀`; the MC8 sine field `UwLM ℓ M k a₀` is in `GlobalRegular2 ℓ M 12 k α₀ ℓ⁻ᵏ`
  (all three printed clauses), is CURVED, and `Λ̃(univ)` contains a nonzero field (`tildeSeed`).
* `M0CoreBody ℓ M hell a a₀ γ₀` : the body of MC2's `M0Core` at a GIVEN pair `(a₀, γ₀)`, copied verbatim;
  `M0Core_iff_body` (`Iff.rfl`) is the kernel's check that `M0Core ℓ M hell a ↔ ∃ a₀ > 0, ∃ γ₀ > 0, M0CoreBody … a₀ γ₀`.
* **`M0Core_general_witnessed ℓ M a`** (`2 ≤ ℓ`, `1 ≤ M`, `0 < a`) : there is ONE pair `a₀ > 0`, `γ₀ > 0` such that
  (i) `M0CoreBody ℓ M _ a a₀ γ₀` holds (so this pair witnesses `M0Core`), AND (ii) for every `k ≥ 1` the `∀`-domain of that
  body AT THIS `a₀` contains the curved sine field `UwLM ℓ M k a₀` (TorusOK, `0 < α₀`, `12Mα₀ ≤ a₀`, `GlobalRegular2`, ∃ curved
  plaquette), at which `InstIneq` holds with this `γ₀` and the printed form is STRICTLY POSITIVE on a nonzero `B̃ ∈ Λ̃`.
  The link between the pair of (i) and the domain facts of (ii) is in the TYPE (one `∃`, one conjunction).
  (Revision 2026-10-13: the previous type had a fresh `∃ a₀ γ₀` whose link to `M0Core_general` was only in the proof;
  nested-verifier finding F1.)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp TorusOK)
open AdalyFormal.StatementLane2 (Ufield OnLambdaT)
open AdalyFormal.StatementLaneG (InstIneq gparams)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M0Corollary (GlobalRegular2)

/-- the torus `(16ℓM)³` -/
def LuLM (ell M : ℕ) : PeriodicLatticeExtent := fun _ => 16 * ell * M - 1

theorem LuLM_succ (ell M : ℕ) (hell : 1 ≤ ell) (hM : 1 ≤ M) (μ : Fin 3) : LuLM ell M μ + 1 = 16 * ell * M := by
  show 16 * ell * M - 1 + 1 = 16 * ell * M
  have : 1 ≤ 16 * ell * M := by nlinarith
  omega

theorem torusOK_LuLM (ell M : ℕ) (hell : 2 ≤ ell) (hM : 1 ≤ M) : TorusOK ell M (LuLM ell M) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
  · rw [LuLM_succ ell M (by omega) hM μ]; exact ⟨16 * M, by ring⟩
  · rw [LuLM_succ ell M (by omega) hM μ]; nlinarith
  · rw [LuLM_succ ell M (by omega) hM μ]; exact ⟨16 * ell, by ring⟩

/-- the amplitude: `12 M α₀ = min(a₀, 1)` -/
noncomputable def α₀LM (M : ℕ) (a₀ : ℝ) : ℝ := min a₀ 1 / (12 * M)

/-- the sine field of MC8 on `(16ℓM)³`, amplitude `min(a₀,1)/2` -/
noncomputable def UwLM (ell M k : ℕ) (a₀ : ℝ) : LinkCfg (scaleUp ell k (LuLM ell M)) :=
  Ufield ((ell : ℝ) ^ k)⁻¹ (AdalyFormal.M0Corollary.chiP (scaleUp ell k (LuLM ell M)) ((12 : ℝ) * M * α₀LM M a₀ / 2))

theorem βLM_eq (M : ℕ) (hM : 1 ≤ M) (a₀ : ℝ) : (12 : ℝ) * M * α₀LM M a₀ = min a₀ 1 := by
  unfold α₀LM
  have : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp

theorem M0Core_domain_curved (ell M k : ℕ) (hell : 2 ≤ ell) (hM : 1 ≤ M) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    TorusOK ell M (LuLM ell M) ∧ 0 < α₀LM M a₀ ∧ (12 : ℝ) * M * α₀LM M a₀ ≤ a₀ ∧
    GlobalRegular2 ell M 12 k (α₀LM M a₀) ((ell : ℝ) ^ k)⁻¹ (UwLM ell M k a₀) ∧
    (∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)), 0 < dv (periodicPlaquetteHolonomy (UwLM ell M k a₀) p)) ∧
    (∃ Bt : Bond (LuLM ell M) → SuTwo,
      AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) ell Bt ∧
      OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) Bt ∧ 0 < bondEnergy Bt) := by
  have hell0 : 0 < ell := by omega
  have hT := torusOK_LuLM ell M hell hM
  have hβ := βLM_eq M hM a₀
  have hm0 : 0 < min a₀ 1 := lt_min ha₀ one_pos
  have hα : 0 < α₀LM M a₀ := by
    unfold α₀LM; have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  have h16 : 16 ≤ LuLM ell M 0 + 1 := by rw [LuLM_succ ell M (by omega) hM 0]; nlinarith
  have hpos : 0 < (12 : ℝ) * M * α₀LM M a₀ := by rw [hβ]; exact hm0
  have hG : GlobalRegular2 ell M 12 k (α₀LM M a₀) ((ell : ℝ) ^ k)⁻¹ (UwLM ell M k a₀) :=
    AdalyFormal.M0Corollary.sine_globalRegular2 ell M k hell0 (LuLM ell M) h16 (α₀LM M a₀) hpos
  have hAc1 : (12 : ℝ) * M * α₀LM M a₀ / 2 < 1 := by rw [hβ]; have := min_le_right a₀ 1; linarith
  have hn1 : (1 : ℝ) ≤ (ell : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hell0)
  have hcurv : ∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)),
      0 < dv (periodicPlaquetteHolonomy (UwLM ell M k a₀) p) := by
    refine AdalyFormal.M0Corollary.sine_curved (scaleUp ell k (LuLM ell M)) _ _ (by positivity) hAc1 (by positivity)
      (inv_le_one_of_one_le₀ hn1) ?_
    have := AdalyFormal.IngredientFamilyR2.scaleUp_succ ell k (LuLM ell M) hell0 0
    have h2 : 1 ≤ ell ^ k := Nat.one_le_pow _ _ hell0
    rw [this, LuLM_succ ell M (by omega) hM 0]
    have h3 : 3 ≤ 16 * ell * M := by nlinarith
    calc 3 ≤ 16 * ell * M := h3
      _ ≤ 16 * ell * M * ell ^ k := Nat.le_mul_of_pos_right _ (by positivity)
  have hdvd : ∀ μ : Fin 3, ell ∣ (LuLM ell M μ + 1) := fun μ => by
    rw [LuLM_succ ell M (by omega) hM μ]; exact ⟨16 * M, by ring⟩
  obtain ⟨Bt, hBt, hpB⟩ := AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := LuLM ell M) (ell := ell)
    hell hdvd
  refine ⟨hT, hα, by rw [hβ]; exact min_le_left a₀ 1, hG, hcurv, Bt,
    (AdalyFormal.StatementLane.onLambdaTildeIn_univ ell Bt).mpr hBt, fun b hb => absurd (Or.inl (Set.mem_univ _)) hb, hpB⟩

/-- the body of MC2's `M0Core` at a given pair `(a₀, γ₀)` (verbatim copy of MC2.lean's `M0Core` after its two `∃`) -/
def M0CoreBody (ell M : ℕ) (hell : 0 < ell) (a a₀ γ₀ : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent), TorusOK ell M Lu →
    ∀ (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * M * α₀ ≤ a₀ →
    ∀ (U : LinkCfg (scaleUp ell k Lu)), GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹ U →
      InstIneq ell k hell a Lu γ₀ (fullTower ell k Lu) Set.univ U

/-- the kernel's check that `M0CoreBody` IS the body of MC2's `M0Core` -/
theorem M0Core_iff_body (ell M : ℕ) (hell : 0 < ell) (a : ℝ) :
    AdalyFormal.M0Corollary.M0Core ell M hell a ↔ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ M0CoreBody ell M hell a a₀ γ₀ :=
  Iff.rfl

/-- **one pair `(a₀, γ₀)` witnesses `M0Core` AND, at that `a₀`, the domain contains a curved field where the conclusion holds
with that `γ₀` and the printed form is strictly positive** -/
theorem M0Core_general_witnessed (ell M : ℕ) (hell : 2 ≤ ell) (hM : 1 ≤ M) (a : ℝ) (ha : 0 < a) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ M0CoreBody ell M (by omega) a a₀ γ₀ ∧
      ∀ k : ℕ, 1 ≤ k →
        TorusOK ell M (LuLM ell M) ∧ 0 < α₀LM M a₀ ∧ (12 : ℝ) * M * α₀LM M a₀ ≤ a₀ ∧
        GlobalRegular2 ell M 12 k (α₀LM M a₀) ((ell : ℝ) ^ k)⁻¹ (UwLM ell M k a₀) ∧
        (∃ p : PeriodicLatticePlaquette (scaleUp ell k (LuLM ell M)),
          0 < dv (periodicPlaquetteHolonomy (UwLM ell M k a₀) p)) ∧
        InstIneq ell k (by omega) a (LuLM ell M) γ₀ (fullTower ell k (LuLM ell M)) Set.univ (UwLM ell M k a₀) ∧
        ∃ Bt : Bond (LuLM ell M) → SuTwo,
          AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) ell Bt ∧
          OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuLM ell M))) Bt ∧ 0 < bondEnergy Bt ∧
          0 < AdalyFormal.StatementLaneG.GenP.genForm
            (gparams ell k (LuLM ell M) (by omega) (fullTower ell k (LuLM ell M)) (UwLM ell M k a₀) a Set.univ)
            (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC
              (gparams ell k (LuLM ell M) (by omega) (fullTower ell k (LuLM ell M)) (UwLM ell M k a₀) a Set.univ) Bt)) := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, hall⟩ := (M0Core_iff_body ell M (by omega) a).mp (M0Core_general ell M hell a ha)
  refine ⟨a₀, ha₀, γ₀, hγ₀, hall, fun k hk => ?_⟩
  obtain ⟨hT, hα, hsm, hG, hcurv, Bt, h1, h2, hpB⟩ := M0Core_domain_curved ell M k hell hM a₀ ha₀
  have hI := hall k hk (LuLM ell M) hT (α₀LM M a₀) hα hsm (UwLM ell M k a₀) hG
  exact ⟨hT, hα, hsm, hG, hcurv, hI, Bt, h1, h2, hpB, lt_of_lt_of_le (by positivity) (hI Bt h1 h2)⟩

/-- the pair of `M0Core_general_witnessed` witnesses `M0Core` (read off the type, no new content) -/
theorem M0Core_of_witnessed (ell M : ℕ) (hell : 2 ≤ ell) (hM : 1 ≤ M) (a : ℝ) (ha : 0 < a) :
    AdalyFormal.M0Corollary.M0Core ell M (by omega) a := by
  obtain ⟨a₀, ha₀, γ₀, hγ₀, hbody, -⟩ := M0Core_general_witnessed ell M hell hM a ha
  exact (M0Core_iff_body ell M (by omega) a).mpr ⟨a₀, ha₀, γ₀, hγ₀, hbody⟩

#print axioms torusOK_LuLM
#print axioms M0Core_domain_curved
#print axioms M0Core_iff_body
#print axioms M0Core_general_witnessed
#print axioms M0Core_of_witnessed

end AdalyFormal.DLayer

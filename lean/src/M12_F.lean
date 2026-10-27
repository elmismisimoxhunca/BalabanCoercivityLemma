import MXQ_Br
import MXQ_Tor
import MX_NV

/-!
# M12_F -- the factors {12, 12*ell} instance of the Mixed / Family headlines (lane mixed12_20261019)

No new analysis: `Φ := {12, 12*ell}` is chosen AFTER `(ell, a)` and after the constants `(m₁,R₁,a₀,γ₀)`, which the Mixed and Family headlines
quantify before `Φ` / `Fm`.  Smallness: `∀ f ∈ Φ, f·ell^m·α₀ ≤ a₀` is equivalent to the single inequality `12·ell·ell^m·α₀ ≤ a₀`.
-/
set_option autoImplicit false

namespace M12

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- the factor set. -/
def Phi12 (ell : ℕ) : Set ℕ := {12, 12 * ell}

theorem phi12_ge (ell : ℕ) (hell : 2 ≤ ell) : ∀ f ∈ Phi12 ell, 10 ≤ f := by
  intro f hf
  rcases hf with rfl | rfl <;> omega

theorem phi12_small (ell m : ℕ) (hell : 2 ≤ ell) (α₀ a₀ : ℝ) (hα : 0 < α₀) :
    (∀ f ∈ Phi12 ell, (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ↔
      (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ := by
  have hM : (0 : ℝ) ≤ ((ell ^ m : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hMα : 0 ≤ ((ell ^ m : ℕ) : ℝ) * α₀ := mul_nonneg hM hα.le
  constructor
  · intro h
    have := h (12 * ell) (Or.inr rfl)
    push_cast at this ⊢
    exact this
  · intro h f hf
    rcases hf with rfl | rfl
    · have e : (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ = (12 * (ell : ℝ)) * (((ell ^ m : ℕ) : ℝ) * α₀) := by ring
      have e2 : ((12 : ℕ) : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = 12 * (((ell ^ m : ℕ) : ℝ) * α₀) := by push_cast; ring
      rw [e2]
      rw [e] at h
      nlinarith
    · push_cast at h ⊢
      exact h

/-- **Headline (Mixed form).** -/
def P428Target8Factors12 : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          MXP.Total.CoercG8AtWDMixed ell (ell ^ m) R k (by omega) a Lu (Phi12 ell) α₀ γ₀

theorem p428Target8_factors_12_12ell : P428Target8Factors12 := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, h⟩ := MXP.Total.p428Target8Mixed ell hell a ha
  exact ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα hs =>
    h (Phi12 ell) (phi12_ge ell hell) m hm R hR k hk Lu α₀ hα ((phi12_small ell m hell α₀ a₀ hα).2 hs)⟩

/-- **Headline (Family form: each class cube carries its own factor from `{12, 12*ell}`; the family is arbitrary).** -/
def P428Target8Factors12Family : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ, ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Fm : MXQ.AllC.CF,
        (∀ (L : PeriodicLatticeExtent) (s : Set (PeriodicLatticeSite L)) (j f : ℕ), (s, j, f) ∈ Fm L → f = 12 ∨ f = 12 * ell) →
        ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 * (ell : ℝ)) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          MXQ.Total.CoercG8AtWDFamily ell (ell ^ m) R k (by omega) a Lu Fm α₀ γ₀

theorem p428Target8_factors_12_12ell_family : P428Target8Factors12Family := by
  intro ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, h⟩ := MXQ.Total.p428Target8Family ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun Fm hFm m hm R hR k hk Lu α₀ hα hs => ?_⟩
  have hmem : ∀ L s j f, (s, j, f) ∈ Fm L → f ∈ Phi12 ell := fun L s j f hx => hFm L s j f hx
  refine h Fm ⟨fun L s j f hx => phi12_ge ell hell f (hmem L s j f hx)⟩ m hm R hR k hk Lu α₀ hα
    (fun L s j f hx => ?_)
  exact (phi12_small ell m hell α₀ a₀ hα).2 hs f (hmem L s j f hx)

/-- the Mixed form is implied by nothing weaker: the Family form gives the Mixed form back (`Fm = famPhi Φ`). -/
theorem family_gives_mixed12 : P428Target8Factors12Family → P428Target8Factors12 := by
  intro hF ell hell a ha
  obtain ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, h⟩ := hF ell hell a ha
  refine ⟨m₁, hm₁, R₁, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα hs hT S hS Lam hL U hU => ?_⟩
  exact h (MXQ.Total.famPhi (Phi12 ell)) (fun L s j f hx => hx) m hm R hR k hk Lu α₀ hα hs hT S hS Lam hL U
    (MXQ.Total.classCoupledΦ_toQ hU)

/-- non-vacuity: at `Φ = {12, 12*ell}` the full tower on a torus `Lu μ = M-1` with `ell^m = M` satisfies Admissible, `LambdaOK2 univ`, `ClassCoupledΦ` for every `Ufield` with small `χ` (χ = 0 included). -/
theorem factors12_hyps_nonvacuous (ell m R k : ℕ) (hell : 2 ≤ ell) (hk : 1 ≤ k) {α₀ : ℝ} (hα : 0 < α₀)
    (χ : AdalyFormal.Balaban.AdmissibleSubspace.Bond (AdalyFormal.StatementLane.scaleUp ell k (fun _ : Fin 3 => ell ^ m - 1)) → ℝ)
    (hχ : ∀ e, |χ e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10) :
    ∃ Lu : PeriodicLatticeExtent, (∀ μ : Fin 3, ell ^ m ∣ Lu μ + 1) ∧
      ∃ (χ' : AdalyFormal.Balaban.AdmissibleSubspace.Bond (AdalyFormal.StatementLane.scaleUp ell k Lu) → ℝ),
      MXP.AllC.ClassCoupledΦ ell (ell ^ m) (Phi12 ell) k (AdalyFormal.IngredientFamilyR2.fullTower ell k Lu) α₀ (((ell : ℝ) ^ k)⁻¹)
        (AdalyFormal.StatementLane2.Ufield (((ell : ℝ) ^ k)⁻¹) χ') := by
  have hpos : 0 < ell ^ m := pow_pos (by omega) m
  have hT : ∀ μ : Fin 3, ell ^ m ∣ (fun _ : Fin 3 => ell ^ m - 1) μ + 1 := by
    intro μ; simp only; rw [Nat.sub_add_cancel hpos]
  obtain ⟨-, -, h⟩ := MXP.AllC.mixed_hyps_nonvacuous ell (ell ^ m) R k (Phi12 ell) ⟨12, Or.inl rfl⟩ (phi12_ge ell hell)
    (by omega) hpos (fun _ : Fin 3 => ell ^ m - 1) hT hα hk χ hχ
  exact ⟨_, hT, χ, h⟩

end M12

#print axioms M12.p428Target8_factors_12_12ell
#print axioms M12.p428Target8_factors_12_12ell_family
#print axioms M12.family_gives_mixed12
#print axioms M12.phi12_small
#print axioms M12.factors12_hyps_nonvacuous

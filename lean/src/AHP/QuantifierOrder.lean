import TT_F

set_option autoImplicit false

namespace AdalyFormal.Fidelity.SheetVariants

open AdalyFormal.StatementLaneG

/-- Re-export of the existing implication. Total chooses thresholds and constants
before `c,m,R`, covers every `c ≥ 10` rather than 12, and includes well-definedness. -/
theorem total_imp_frozen : AdalyFormal.Total.P428Target8Total → P428Target8 :=
  AdalyFormal.Total.P428Target8Total.toTarget

/-- Separation of unrestricted natural-number quantifier patterns only;
this is not non-implication between the actual coercivity propositions. -/
theorem threshold_order_toy :
    (∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → m ≤ R) ∧
    ¬ (∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ,
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → m ≤ R) := by
  constructor
  · exact ⟨1, by omega, fun m _ => ⟨m, fun _ hR => hR⟩⟩
  · rintro ⟨m₁, _, R₁, h⟩
    have hbad := h (m₁ + R₁ + 1) (by omega) R₁ (by omega)
    omega

end AdalyFormal.Fidelity.SheetVariants


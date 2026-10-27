import SoPar
set_option autoImplicit false
namespace SolSitesAffine
-- A fixed principal-log branch contributes an integer offset to each block.
-- This lemma concerns the arithmetic model only; it does not formalize blocking.
theorem fixed_branch_no_nearby (ell : ℕ) (hodd : ell % 2 = 1) (h : ℕ → ℕ → ℤ)
    (hstep : ∀ x y, h (x+1) y = h x y + 1 ∨ h (x+1) y = h x y - 1)
    (τ₁ τ₂ : ℝ) (hne : τ₁ ≠ τ₂) (S₀ S₁ : ℤ)
    (hS₀ : S₀ = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h i j)
    (hS₁ : S₁ = ∑ i ∈ Finset.range ell, ∑ j ∈ Finset.range ell, h (ell+i) j)
    (hnear : |τ₁-τ₂| * (|(S₀:ℝ)| + |(S₁:ℝ)|) < 2*Real.pi*(ell:ℝ)^2)
    (K : ℤ → ℤ)
    (h₁ : ∀ q ∈ ({S₀,S₁}:Set ℤ), ∃ m : ℤ, τ₁*q = 2*Real.pi*(ell:ℝ)^2*m + 2*Real.pi*K q)
    (h₂ : ∀ q ∈ ({S₀,S₁}:Set ℤ), ∃ m : ℤ, τ₂*q = 2*Real.pi*(ell:ℝ)^2*m + 2*Real.pi*K q) : False := by
  apply AdalyFormal.SitesOnly.no_nearby_tau_odd ell hodd h hstep (τ₁-τ₂) 0 (sub_ne_zero.mpr hne) S₀ S₁ hS₀ hS₁
  · simpa using hnear
  · intro q hq
    obtain ⟨m₁,e₁⟩ := h₁ q hq
    obtain ⟨m₂,e₂⟩ := h₂ q hq
    refine ⟨m₁-m₂, ?_⟩
    push_cast
    nlinarith
  · intro q hq
    exact ⟨0, by simp⟩
#print axioms fixed_branch_no_nearby
end SolSitesAffine

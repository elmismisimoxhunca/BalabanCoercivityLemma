import PGFC23

/-!
# SC1 -- the SCALED-norm formulation of the `hunit` chain.

Print (CMP99b): the mass term is `a (L^j η)^{d-2} |Q_j A (b)|²` (3.16), `(3.24)`, the form `⟨A,Δ_a A⟩` is a
sum of `η^d`-weighted `L²`-pairings (p.393, "⟨λ,λ'⟩ = Σ η^d tr λ λ'"), and the second-order perturbation obeys
`|(Δ^{(2)}A)(b)| ≤ O(1) M α₀ (L^j η)^{-2} |A|`, `b ∈ Λ_j` (3.137, p.423).  Both the mass and the `Δ^{(2)}` bound
carry the level-`j` factor `(L^jη)^{-2}`.  With `η = 1` (unit fine lattice) and the single level `j = k` of the
repo instance this is `ell^{-2k}`.  So the print compares coercivity and `‖Δ^{(2)}‖` in the SCALED form
`ell^{2k}·⟨x, Ginv x⟩ ≥ c'‖x‖²`, `ell^{2k}‖Δ²‖ ≤ ε'`, `ε' < c'`.

* `unit_of_chain_scaled`: `unit_of_chain` restated in the scaled constants `(c', ε')` (any `IngrBParams`).
* `scaled_iff`: the scaled and plain coercivity statements are the same statement with `c' = c·ell^{2k}`.
* flat: `flat_scaled_ceiling`: every scaled coercivity constant of the flat `G₁⁻¹` is `≤ a` (k-uniform ceiling).
Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1

namespace AdalyFormal.ScaledCoercivity

/-- scale factor `n² = (ell^k)²` -/
noncomputable def nsq (P : IngrBParams) : ℝ := ((P.ell : ℝ) ^ P.k) ^ 2

theorem nsq_pos (P : IngrBParams) : 0 < nsq P := by
  have : (0 : ℝ) < P.ell := by exact_mod_cast P.hell
  unfold nsq; positivity

/-- `unit_of_chain` in the scaled constants -/
theorem unit_of_chain_scaled (P : IngrBParams) (hτ : Function.Bijective P.tau) {c' ε' : ℝ}
    (hcε : ε' < c')
    (hc : ∀ x, c' * ‖x‖ ^ 2 ≤ nsq P * ⟪x, P.data.Ginv x⟫)
    (hε : nsq P * ‖P.data.Delta2 P.data_laws‖ ≤ ε')
    (hQs : Function.Injective P.data.Qs) (hη : 0 < P.eta) :
    IsUnit ((P.Qin.comp P.G1in).comp (ContinuousLinearMap.adjoint P.Qin)) := by
  have hN := nsq_pos P
  refine IngrBParams.unit_of_chain P hτ (c := c' / nsq P) (ε := ε' / nsq P)
    (div_lt_div_of_pos_right hcε hN) (fun x => ?_) ?_ hQs hη
  · rw [div_mul_eq_mul_div, div_le_iff₀ hN]
    simpa [mul_comm] using hc x
  · rw [le_div_iff₀ hN]; simpa [mul_comm] using hε

theorem scaled_iff (P : IngrBParams) (c : ℝ) :
    (∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, P.data.Ginv x⟫) ↔
    (∀ x, (c * nsq P) * ‖x‖ ^ 2 ≤ nsq P * ⟪x, P.data.Ginv x⟫) := by
  have hN := nsq_pos P
  constructor
  · intro h x
    have := mul_le_mul_of_nonneg_left (h x) hN.le
    linarith [this]
  · intro h x
    have := h x
    have h2 : nsq P * (c * ‖x‖ ^ 2) ≤ nsq P * ⟪x, P.data.Ginv x⟫ := by linarith
    exact le_of_mul_le_mul_left h2 hN

/-- flat: every scaled coercivity constant is `≤ a`, uniformly in `k` -/
theorem flat_scaled_ceiling (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hN : ∀ μ, 1 ≤ Lu μ) (c' : ℝ)
    (hc : ∀ x : ↥(bondSupp (PK ell k Lu hell a Lam).G),
      c' * ‖x‖ ^ 2 ≤ ((ell : ℝ) ^ (2 * k)) * ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫) :
    c' ≤ a := by
  have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have hc2 : ∀ x : ↥(bondSupp (PK ell k Lu hell a Lam).G),
      (c' / (ell : ℝ) ^ (2 * k)) * ‖x‖ ^ 2 ≤ ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫ := by
    intro x
    rw [div_mul_eq_mul_div, div_le_iff₀ hp]
    simpa [mul_comm] using hc x
  have := FlatCoercivity.coercivity_constant_le ell k Lu hell a Lam hN _ hc2
  rwa [div_mul_cancel₀ _ hp.ne'] at this

#print axioms unit_of_chain_scaled
#print axioms scaled_iff
#print axioms flat_scaled_ceiling

end AdalyFormal.ScaledCoercivity

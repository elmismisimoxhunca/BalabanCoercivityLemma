import PGFC1

/-!
# GFC2 -- interface to the `hunit` chain (`IngrBParams.unit_of_chain`, ingredient lane R2Wire2)

* `ginv_form_eq_G1inv`: at flat `U`, `⟨x, data.Ginv x⟩ = ⟨x, G₁⁻¹ x⟩` (J = 0, Δ² = 0).
* `hunit_of_coercive`: ANY positive coercivity constant `c` of `G₁⁻¹` yields `hunit` (the `unit_of_chain` call with
  `ε = 0`).  (`PK_hunit` of genuine_u1 is this with the compactness constant.)
* `hunit_chain_threshold`: the `unit_of_chain` hypotheses `(c, ε)` with `ε < c` at level `k` force
  `ε · ell^{2k} < a` (because of `coercivity_constant_le`): the smallness budget for `‖Δ^{(2)}‖` at level `k`
  is at most `a / ell^{2k}`; in particular it is NOT `k`-uniform.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatCoercivity

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Ingr)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))
local notation "PP" => PK ell k Lu hell a Lam

theorem ginv_form_eq_G1inv (x : ↥(bondSupp (PP).G)) :
    ⟪x, (PP).data.Ginv x⟫ = ⟪x, (PP).G1inv x⟫ := by
  have hJ : (PP).data.J = 0 := by
    show (pE (PP).G) (PP).Jf = 0
    rw [Jf_flat (PP) rfl]; exact map_zero _
  have h2 := (PP).G1inv_spec.form x
  rw [BaseDataS.K_eq, hJ, inner_zero_right, mul_zero, sub_zero] at h2
  rw [h2]

/-- `hunit` from ANY positive coercivity constant of `G₁⁻¹` (flat, full tower, any `k`) -/
theorem hunit_of_coercive (hN : ∀ μ, 1 ≤ Lu μ) (c : ℝ) (hc : 0 < c)
    (hco : ∀ x : ↥(bondSupp (PP).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PP).G1inv x⟫) :
    IsUnit (((PP).Qin.comp (PP).G1in).comp (ContinuousLinearMap.adjoint (PP).Qin)) := by
  have hτ : Function.Bijective (PP).tau := IngrBParams.tau_bijective _ (PK_fullSupp ell k Lu hell a Lam)
  refine IngrBParams.unit_of_chain (PP) hτ (c := c) (ε := 0) hc (fun x => ?_) ?_
    (PK_Qs_injective ell k Lu hell a Lam) (IngrBParams.eta_pos _)
  · rw [ginv_form_eq_G1inv ell k Lu hell a Lam x]; exact hco x
  · rw [PK_Delta2_zero]; exact le_of_eq ContinuousLinearMap.opNorm_zero

/-- the `unit_of_chain` budget: any admissible `(c, ε)` with `ε < c` has `ε · ell^{2k} < a`. -/
theorem hunit_chain_threshold (hN : ∀ μ, 1 ≤ Lu μ) (c ε : ℝ) (hcε : ε < c)
    (hc : ∀ x : ↥(bondSupp (PP).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PP).data.Ginv x⟫) (hε : 0 ≤ ε) :
    ε * (ell : ℝ) ^ (2 * k) < a := by
  have hc' : ∀ x : ↥(bondSupp (PP).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PP).G1inv x⟫ := fun x => by
    rw [← ginv_form_eq_G1inv ell k Lu hell a Lam x]; exact hc x
  have h1 := coercivity_constant_le ell k Lu hell a Lam hN c hc'
  have hp : (0 : ℝ) < (ell : ℝ) ^ (2 * k) := by
    have : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  calc ε * (ell : ℝ) ^ (2 * k) < c * (ell : ℝ) ^ (2 * k) := mul_lt_mul_of_pos_right hcε hp
    _ ≤ a := h1

end

#print axioms ginv_form_eq_G1inv
#print axioms hunit_of_coercive
#print axioms hunit_chain_threshold

end AdalyFormal.FlatCoercivity

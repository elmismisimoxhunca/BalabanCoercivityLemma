import PGFC22
import PGFC2

/-!
# GFC23 -- CAPSTONE: the flat `G₁⁻¹ = Δ_a(1)` of the genuine objects.
(i) a coercivity constant exists that is INDEPENDENT of the unit torus `Lu` and of `Λ`;
(ii) every coercivity constant at level `k` is `≤ a / ell^{2k}` (so NO `k`-uniform constant);
(iii) the `hunit` consumer (`unit_of_chain`) is fed by the volume-free constant.
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

namespace AdalyFormal.FlatCoercivity

theorem flat_G1inv_characterisation (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a) :
    (∃ c : ℝ, 0 < c ∧ ∀ (Lu : PeriodicLatticeExtent) (Lam : Set (PeriodicLatticeSite Lu))
      (x : ↥(bondSupp (PK ell k Lu hell a Lam).G)), c * ‖x‖ ^ 2 ≤ ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫) ∧
    (∀ (Lu : PeriodicLatticeExtent) (hN : ∀ μ, 1 ≤ Lu μ) (Lam : Set (PeriodicLatticeSite Lu)) (c : ℝ),
      (∀ x : ↥(bondSupp (PK ell k Lu hell a Lam).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫) →
        c * (ell : ℝ) ^ (2 * k) ≤ a) :=
  ⟨G1inv_coercive_volume_free ell k hell a ha,
   fun Lu hN Lam c hc => coercivity_constant_le ell k Lu hell a Lam hN c hc⟩

/-- the volume-free constant feeds `hunit` (flat, full tower, any `Lu`, `Λ`) -/
theorem hunit_volume_free (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Lu : PeriodicLatticeExtent) (hN : ∀ μ, 1 ≤ Lu μ) (Lam : Set (PeriodicLatticeSite Lu)),
      (∀ x : ↥(bondSupp (PK ell k Lu hell a Lam).G), c * ‖x‖ ^ 2 ≤ ⟪x, (PK ell k Lu hell a Lam).G1inv x⟫) ∧
      IsUnit ((((PK ell k Lu hell a Lam).Qin.comp (PK ell k Lu hell a Lam).G1in).comp
        (ContinuousLinearMap.adjoint (PK ell k Lu hell a Lam).Qin))) := by
  obtain ⟨c, hc, h⟩ := G1inv_coercive_volume_free ell k hell a ha
  refine ⟨c, hc, fun Lu hN Lam => ⟨h Lu Lam, ?_⟩⟩
  exact hunit_of_coercive ell k Lu hell a Lam hN c hc (h Lu Lam)

#print axioms flat_G1inv_characterisation
#print axioms hunit_volume_free

end AdalyFormal.FlatCoercivity

import UC4

/-!
# UC5 -- side conditions of `unit_floor_M1charts` that do not depend on the configuration (lane m2_unit_20261014)

* `partOK_of_torusOK` : under the statement's `TorusOK ℓ M Lu` with `M = ℓ^(m+1)`, the partition mesh `Mc = ℓ^m = M/ℓ` satisfies
  `PartOK Lu Mc` (so the partition exists on EVERY admissible unit torus, including `L_μ + 1 = M`).
* `charts_trivial_of_M1Regular` : if `U` itself is `M1Regular`, the chart choice `γ = 1`, `V = U` meets every chart hypothesis
  of `unit_floor_M1charts` about `(γ, V)` (the agreement hypotheses hold on every ball): the per-chart interface is
  non-vacuous, and it reduces to M1 when a global gauge exists.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.StatementLane (Tower scaleUp TorusOK)
open AdalyFormal.StatementLaneR8 (Ball AgreeAt)

theorem partOK_of_torusOK {ell m : ℕ} {Lu : PeriodicLatticeExtent} (hell2 : 2 ≤ ell)
    (hT : TorusOK ell (ell ^ (m + 1)) Lu) : PartOK Lu (ell ^ m) := by
  have hell : 0 < ell := by omega
  refine ⟨pow_pos hell m, fun μ => ?_, fun μ => ?_⟩
  · exact dvd_trans (pow_dvd_pow ell (Nat.le_succ m)) (hT.2.2 μ)
  · obtain ⟨c, hc⟩ := hT.2.2 μ
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
    have h1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
    rw [hc, pow_succ]
    have hp : 0 < ell ^ m := pow_pos hell m
    calc 2 * ell ^ m ≤ ell * ell ^ m := Nat.mul_le_mul_right _ hell2
      _ = ell ^ m * ell := by ring
      _ ≤ ell ^ m * ell * c := Nat.le_mul_of_pos_right _ h1

theorem charts_trivial_of_M1Regular {ell M k : ℕ} {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell k Lu))
    (α₀ : ℝ) (U : LinkCfg (scaleUp ell k Lu))
    (hU : AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (W : Set (PeriodicLatticeSite (scaleUp ell k Lu))) :
    AdalyFormal.M1.M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U ∧
      AgreeAt W (periodicGaugeTransform (fun _ => (1 : SU2)) U) U :=
  ⟨hU, agree_one W U⟩

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.partOK_of_torusOK
#print axioms AdalyFormal.M2Unit.charts_trivial_of_M1Regular

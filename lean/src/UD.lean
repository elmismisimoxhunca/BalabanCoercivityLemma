import UC

/-!
# UD -- the REDUCTION of `ZT5A.P428Target8Unif` to the uniform ball charts (lane unif_20261016)

* `fieldsU` : the three field inputs of `strong_coreU` from `BallChartsGU`.
* `unifStrong_of_ballChartsGU : BallChartsGU → P428Target8UnifStrong` (`a₀, γ₀` uniform in `M, R`, conclusion `WellDefG ∧` inequality).
* `unif_of_ballChartsGU : BallChartsGU → ZT5A.P428Target8Unif`.
`BallChartsGU` is NOT proved here (the residual).  The existing chain proves it with `C = CC ℓ M + 56 M ~ M²` and `s ~ M⁻²`
(`M2BallCharts.ballChartsG`), which is where its `a₀ ~ M⁻⁴` comes from (see NOTES.md).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

theorem fieldsU (hB : BallChartsGU) :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKU ell (by omega) a) ∧ OpLayerThickU ∧ ClassRightInvU :=
  ⟨fun _ hell a ha => fieldsKU_of_ball (ballChartsU_of_G hB) hell a ha,
    opLayerThickU_of hB (classRightInvU_of_cov hB (classRightInvCovU hB)),
    classRightInvU_of_cov hB (classRightInvCovU hB)⟩

/-- **REDUCTION**: uniform ball charts give `a₀, γ₀` uniform in `M, R` (with `WellDefG`). -/
theorem unifStrong_of_ballChartsGU (hB : BallChartsGU) : P428Target8UnifStrong := by
  intro ell hell a ha
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hc⟩ := strong_coreU (fieldsU hB).1 (fieldsU hB).2.1 (fieldsU hB).2.2 hell (by omega) ha
  refine ⟨m₀, hm₀, R₀, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα h2 hT S hS Lam hL U hU => ?_⟩
  obtain ⟨hI, hW⟩ := hc m hm R hR k hk Lu α₀ hα (by simpa using h2) hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

/-- **REDUCTION** to the ZT5A statement. -/
theorem unif_of_ballChartsGU (hB : BallChartsGU) : P428Target8Unif := (unifStrong_of_ballChartsGU hB).toUnif

end AdalyFormal.UnifLane

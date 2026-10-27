import UMC
import UMG
import UW13

/-!
# UMF -- **`P428Target8Max` (SVS) and `P428Target8UnifStrong`, proved** (lane unif_20261016, milestone 7)

* `p428Target8UnifStrong_proved : UnifLane.P428Target8UnifStrong` (`a₀, γ₀` uniform in `M, R`, conclusion `CoercG8AtWD` at `c = 12`).
* `ballChartsGUH_proved : BallChartsGUH fc` for every cube factor `fc ≥ 10` (from `UMG` + `UMZ`).
* `fieldsUH` : the three field inputs of `strong_coreUC` at `fc`.
* `p428Target8Max_proved : StrongVariants.P428Target8Max`: for every `ell ≥ 2`, `a > 0`, `c ≥ 10` (fixed first), thresholds `m₁, R₁` and
  `a₀, γ₀` (depending on `ell, a, c`) uniform over `m ≥ m₁`, `R ≥ R₁`, conclusion `CoercG8AtWD` at cube factor `c`, smallness `c M α₀ ≤ a₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.UnifMax

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.AllC (CubeFactor)

/-- **step 1**: the uniform strong statement at `c = 12`. -/
theorem p428Target8UnifStrong_proved : AdalyFormal.UnifLane.P428Target8UnifStrong :=
  AdalyFormal.UnifLane.unifStrong_of_ballChartsGU AdalyFormal.UnifLane.Z.ballChartsGU_proved

variable {fc : ℕ} [CubeFactor fc]

theorem ballChartsGUH_proved : BallChartsGUH fc := ballChartsGUH_of_cover coverGeomUH coverGeomBoxUH

theorem fieldsUH (hB : BallChartsGUH fc) :
    (∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → FieldsKUH ell fc (by omega) a) ∧ OpLayerThickUH fc ∧ ClassRightInvUH fc :=
  ⟨fun _ hell a ha => fieldsKU_of_ball (ballChartsU_of_G hB) hell a ha,
    opLayerThickU_of hB (classRightInvU_of_cov hB (classRightInvCovU hB)),
    classRightInvU_of_cov hB (classRightInvCovU hB)⟩

end AdalyFormal.UnifMax

namespace AdalyFormal.UnifMax
open AdalyFormal.StatementLaneG
open AdalyFormal.AllC (CubeFactor)

/-- **`SVS.P428Target8Max`, proved.** -/
theorem p428Target8Max_proved : AdalyFormal.StrongVariants.P428Target8Max := by
  intro ell hell a ha c hc
  haveI : CubeFactor c := ⟨hc⟩
  have hF := fieldsUH (fc := c) ballChartsGUH_proved
  obtain ⟨γ₀, hγ, m₀, hm₀, R₀, a₀, ha₀, hcore⟩ := strong_coreUC (fc := c) hF.1 hF.2.1 hF.2.2 hell (by omega) ha
  refine ⟨m₀, hm₀, R₀, a₀, ha₀, γ₀, hγ, fun m hm R hR k hk Lu α₀ hα h2 => ?_⟩
  intro hT S hS Lam hL U hU
  obtain ⟨hI, hW⟩ := hcore m hm R hR k hk Lu α₀ hα h2 hT S hS Lam hL U hU
  exact ⟨hW, hI⟩

end AdalyFormal.UnifMax


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## L. The soft premise closed; the reductions of this round -/
section Close

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (twistU twistP twistA twistD)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation
  not_cofinalTwistSeparation_of_goalPos1)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- **Round 1's soft premise `InteriorSoft` holds**, for every scale and every even radius `≥ 18`. -/
theorem interiorSoft_proved : InteriorSoft :=
  interiorSoft_of_admissible (fun _ _ hq hR => dil_admissible hq hR)

/-- **Main reduction of this round**: the zero-curvature crossing data of the left twist refute
the guarded all-plaquette reading; no soft premise remains. -/
theorem goalNeg2_of_vacuumLeftSpectral (hc : VacuumLeftSpectral) : GoalNeg2 :=
  goalNeg2_of_interiorSoft_vacuumLeftSpectral interiorSoft_proved hc

/-- The positive reading forbids it. -/
theorem not_vacuumLeftSpectral_of_goalPos1 (h : GoalPos1) : ¬ VacuumLeftSpectral :=
  fun hc => goalNeg2_of_vacuumLeftSpectral hc (goalPos2_iff_goalPos1.mpr h)

/-- **Zero-curvature regularity of the round-8 twist family** (round 1's
`ZeroCurvatureRegularity`), for every scale and every even radius `≥ 18`. -/
theorem zeroCurvatureRegularity_proved {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, ZeroCurvatureRegularity q R D₁ := by
  obtain ⟨D₁, hA, hW, hD⟩ := interiorSoft_proved q R hq hR hR18
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  refine ⟨D₁, fun t => ?_, ?_⟩
  · exact extA_joint_tendsto hq hR (by nlinarith) (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0))
      (AdalyFormal.D1Literal.contFam_Uth _) (by rw [hV0]; exact hA) (by rw [hV0]; exact hW) t
  · show Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) 0))
      (𝓝[>] 0) (𝓝 D₁)
    rw [hV0]
    exact hD

/-- The zero-curvature, spectral part of round 8's premise: for cofinal dyadic scales and,
for each, cofinal even radii `≥ 18`, the vacuum crossing data of the round-8 twist for the
first-order coefficient of its correction.  NOT proved here. -/
def CofinalTwistVacuumCrossing : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ D₁ : TwistSpace (2 ^ j) R →L[ℝ] TwistSpace (2 ^ j) R,
      Tendsto (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) (𝓝[>] 0) (𝓝 D₁) →
        VacuumCrossing (2 ^ j) R D₁

/-- **`X → CofinalTwistSeparation`** (round 8's target), with `X` purely spectral at zero
curvature. -/
theorem cofinalTwistSeparation_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_cofinalVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  obtain ⟨D₁, hreg⟩ := zeroCurvatureRegularity_proved (q := 2 ^ j) (by positivity) hR hR18
  exact ⟨R, hRR, hR, hR18, D₁, hreg, hc D₁ hreg.2⟩

theorem goalNeg2_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCrossing h)

theorem not_twistVacuumCrossing_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistVacuumCrossing :=
  fun h' => not_cofinalTwistSeparation_of_goalPos1 h (cofinalTwistSeparation_of_twistVacuumCrossing h')

/-! ### The remaining premises with the first-order coefficient written out

`vacCoupling q R J' v = 2⟪H₀ C²₀(W₀ v), J'⟫`: the flat (vacuum) constrained inverse `H₀`, the flat
second jet `C²₀` of the flat dressing `W₀ v`, and the curvature derivative `J'` of the localized
source (`IsSourceDerivative`, which exists: `dil_J_tendsto`).  By `dil_D1_form` this is the
quadratic form of the first-order coefficient `D₁`. -/

/-- The flat localized data of the dilated tower. -/
noncomputable abbrev flatData (q R : ℕ) :=
  dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R))

/-- The explicit vacuum coupling form `2⟪H₀ C²₀(W₀ v), J'⟫`. -/
noncomputable def vacCoupling (q R : ℕ) (J' : TwistSpace q R) (v : TwistSpace q R) : ℝ :=
  2 * ⟪(flatData q R).H (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))), J'⟫

/-- `J'` is the curvature derivative of the localized source of the curved dilated family. -/
def IsSourceDerivative (q R : ℕ) (J' : TwistSpace q R) : Prop :=
  Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
    (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')

/-- Crossing data of a vacuum carrier path, with the explicit coupling form.  NOT proved here. -/
def CouplingCrossing (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) :
    Prop :=
  ∃ (t₀ : ℝ) (X' : TwistSpace q R →L[ℝ] TwistSpace q R),
    HasDerivAt (fun t => extA q R 0 (V t)) X' t₀ ∧
    (∃ v, extA q R 0 (V t₀) v = 0 ∧ v ≠ 0) ∧
    (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0) ∧
    ((∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → vacCoupling q R J' v < 0) ∨
      (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → 0 < vacCoupling q R J' v))

/-- The left-twist premise with the explicit coupling form.  NOT proved here. -/
def VacuumLeftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (leftTwist (2 ^ j) R) J'

theorem pathCrossing_of_couplingCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) (hJ : IsSourceDerivative q R J')
    (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁))
    (h : CouplingCrossing q R V J') : PathCrossing q R V D₁ := by
  obtain ⟨t₀, X', hder, hne, hslope, hsign⟩ := h
  have hform : ∀ v, ⟪v, D₁ v⟫ = vacCoupling q R J' v := fun v =>
    dil_D1_form hq (dil_admissible hq hR) hR16 D₁ hD₁ J' hJ v
  refine ⟨t₀, X', hder, hne, hslope, ?_⟩
  rcases hsign with h | h
  · exact Or.inl (fun v hv hv0 => by rw [hform]; exact h v hv hv0)
  · exact Or.inr (fun v hv hv0 => by rw [hform]; exact h v hv hv0)

theorem vacuumLeftSpectral_of_coupling (h : VacuumLeftCoupling) : VacuumLeftSpectral := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁ (hc J' hJ')

/-- **The reduction with every ingredient explicit**: the zero-curvature left-twist crossing
data, with the explicit coupling form, refute the guarded all-plaquette reading. -/
theorem goalNeg2_of_vacuumLeftCoupling (h : VacuumLeftCoupling) : GoalNeg2 :=
  goalNeg2_of_vacuumLeftSpectral (vacuumLeftSpectral_of_coupling h)

/-- The round-8 twist premise with the explicit coupling form.  NOT proved here. -/
def CofinalTwistVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossing (2 ^ j) R (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0)) J'

/-- **`X → CofinalTwistSeparation`** with `X` the explicit zero-curvature coupling data of the
round-8 twist. -/
theorem cofinalTwistSeparation_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_twistVacuumCrossing
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun D₁ hD₁ => ?_⟩
  obtain ⟨J', hJ'⟩ := dil_J_tendsto (2 ^ j) R
  have hV0 : AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0 = 1 :=
    AdalyFormal.D1Literal.Uth_zero _
  have hD₁' : Tendsto (fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
    have e : (fun ε : ℝ => ε⁻¹ • twistD (2 ^ j) R ε 1 0) =
        fun ε : ℝ => ε⁻¹ • extD (2 ^ j) R ε (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0) 0) :=
      rfl
    rw [e, hV0] at hD₁
    exact hD₁
  exact pathCrossing_of_couplingCrossing (by positivity) hR (by omega) _ J' hJ' D₁ hD₁' (hc J' hJ')

theorem goalNeg2_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCoupling h)

end Close

end AdalyFormal.Round9.Guarded.AnalyticR2

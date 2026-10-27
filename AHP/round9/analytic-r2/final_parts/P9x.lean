
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## O. The angle derivative of the vacuum carrier is computed, not assumed

At zero curvature the links of `dilU q R 0 (V t)` are those of `V t` on the exterior bonds and
trivial elsewhere.  For the left twist and for the round-8 twist they are smooth in the angle
(`uMat t = exp(i t σ₃)`, round 1's `Ug_coe`), so by the frozen exterior path formula and
section N the vacuum carrier `t ↦ extA q R 0 (V t)` is differentiable at every angle.  The
crossing premise can therefore use `deriv` instead of asserting a derivative.  At angle `0`
both twists are trivial and the vacuum carrier is positive definite (section M), so a crossing
angle is never `0`. -/
section VacuumSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (Ug)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (exterior_carrier_path)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

theorem uMat_contDiff : ContDiff ℝ ⊤ (fun t : ℝ => AdalyFormal.D1Literal.uMat t) := by
  have e : (fun t : ℝ => AdalyFormal.D1Literal.uMat t) = fun t => ((Ug t : SU2) : M2) := by
    funext t
    exact (AdalyFormal.Round9.Guarded.AnalyticR1.Ug_coe t).symm
  rw [e]
  exact contDiff_iff_contDiffAt.mpr contDiffAt_Ug

/-- Smooth exterior links give smooth links of the vacuum family. -/
theorem vac_smooth (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : ∀ e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0),
      ContDiff ℝ ⊤ (fun t => ((V t e : SU2) : M2))) :
    SmoothFam (fun t => dilU q R 0 (V t)) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    exact hV e he
  · simp only [dilU, if_neg he]
    exact contDiff_const

theorem leftTwist_vac_smooth (q R : ℕ) : SmoothFam (fun t => dilU q R 0 (leftTwist q R t)) := by
  classical
  refine vac_smooth q R _ (fun e _ => ?_)
  by_cases hl : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) ∧ (e.1 0).val < 4 * q
  · simp only [leftTwist, if_pos hl]
    show ContDiff ℝ ⊤ fun t => AdalyFormal.D1Literal.uMat t
    exact uMat_contDiff
  · simp only [leftTwist, if_neg hl]
    exact contDiff_const

theorem Uth_vac_smooth (q R : ℕ) :
    SmoothFam (fun t => dilU q R 0 (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t)) := by
  classical
  refine vac_smooth q R _ (fun e he => ?_)
  simp only [AdalyFormal.D1Literal.Uth, if_pos he]
  show ContDiff ℝ ⊤ fun t => AdalyFormal.D1Literal.uMat t
  exact uMat_contDiff

end VacuumSmooth

section VacuumDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (exterior_carrier_path)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The angle derivative of the vacuum carrier exists at every angle along any exterior path with
smooth links (frozen exterior path formula, round 5's `exterior_carrier_path`, and section N). -/
theorem hasDerivAt_extA_vac {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : SmoothFam (fun t => dilU q R 0 (V t)))
    (t₀ : ℝ) :
    HasDerivAt (fun t => extA q R 0 (V t)) (deriv (fun t => extA q R 0 (V t)) t₀) t₀ := by
  let G := geomOf 2 1 (dilTower q R)
  let U : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) := fun t => dilU q R 0 (V t)
  have h : (fun t => extA q R 0 (V t)) = fun t => extA q R 0 (V 0) +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) 1)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) 1))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) U (fun s e he => dilU_agree q R 0 (V s) (V 0) e he) selAll t
  rw [h]
  exact hasDerivAt_path_formula (fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ)
    (contDiff_deltaKLocCLM hV _) (pE G) (Wop G (U 0) 1) (iE G) (extA q R 0 (V 0)) t₀

/-- The vacuum carrier with trivial exterior field is positive definite. -/
theorem extA_vac_one_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (v : TwistSpace q R) (hv : v ≠ 0) :
    0 < ⟪v, extA q R 0 1 v⟫ := by
  have e : extA q R 0 1 = (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num)
      (dilTower q R) (fun _ => 1) 1 (dilLam q R))).Ginv := by
    show (dataS selAll selAll (gparams 2 1 (dilLu q R) _ (dilTower q R) (dilU q R 0 1) 1
      (dilLam q R))).Ginv = _
    rw [dilU_zero q R]
  rw [e]
  exact dil_flat_all_pos hq hR v hv

/-- The left-twisted vacuum carrier starts positive definite: no crossing at angle `0`. -/
theorem leftTwist_crossing_ne_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) {t₀ : ℝ}
    (h : ∃ v, extA q R 0 (leftTwist q R t₀) v = 0 ∧ v ≠ 0) : t₀ ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, hv0⟩ := h
  rw [leftTwist_zero] at hv
  have hp := extA_vac_one_pos hq hR v hv0
  rw [hv, inner_zero_right] at hp
  exact lt_irrefl _ hp

/-- The same for the round-8 twist. -/
theorem Uth_crossing_ne_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) {t₀ : ℝ}
    (h : ∃ v, extA q R 0 (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t₀) v = 0 ∧ v ≠ 0) :
    t₀ ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, hv0⟩ := h
  rw [AdalyFormal.D1Literal.Uth_zero] at hv
  have hv' : extA q R 0 1 v = 0 := hv
  have hp := extA_vac_one_pos hq hR v hv0
  rw [hv', inner_zero_right] at hp
  exact lt_irrefl _ hp

/-- Crossing data of a vacuum carrier path, with the angle derivative computed (`deriv`) and the
explicit coupling form.  NOT proved here. -/
def CouplingCrossingD (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (J' : TwistSpace q R) :
    Prop :=
  ∃ t₀ : ℝ,
    (∃ v, extA q R 0 (V t₀) v = 0 ∧ v ≠ 0) ∧
    (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → ⟪v, deriv (fun t => extA q R 0 (V t)) t₀ v⟫ < 0) ∧
    ((∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → vacCoupling q R J' v < 0) ∨
      (∀ v, extA q R 0 (V t₀) v = 0 → v ≠ 0 → 0 < vacCoupling q R J' v))

theorem couplingCrossing_of_D {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : SmoothFam (fun t => dilU q R 0 (V t)))
    (J' : TwistSpace q R) (h : CouplingCrossingD q R V J') : CouplingCrossing q R V J' := by
  obtain ⟨t₀, hne, hslope, hsign⟩ := h
  exact ⟨t₀, _, hasDerivAt_extA_vac hq hR hroom V hV t₀, hne, hslope, hsign⟩

/-- The left-twist premise with the derivative computed and the coupling explicit.  NOT proved
here. -/
def VacuumLeftCouplingD : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossingD (2 ^ j) R (leftTwist (2 ^ j) R) J'

theorem vacuumLeftCoupling_of_D (h : VacuumLeftCouplingD) : VacuumLeftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun J' hJ' => ?_⟩
  have hq : 0 < 2 ^ j := by positivity
  exact couplingCrossing_of_D hq hR (by nlinarith) _ (leftTwist_vac_smooth _ R) J' (hc J' hJ')

/-- **Headline reduction of this round**: `X → GoalNeg2`, with `X` the zero-curvature crossing
data of the left twist: a singular angle, the computed angle derivative negative definite on
the kernel, and the explicit coupling `2⟪H₀ C²₀(W₀ v), J'⟫` definite on the kernel. -/
theorem goalNeg2_of_vacuumLeftCouplingD (h : VacuumLeftCouplingD) : GoalNeg2 :=
  goalNeg2_of_vacuumLeftCoupling (vacuumLeftCoupling_of_D h)

theorem not_vacuumLeftCouplingD_of_goalPos1 (h : GoalPos1) : ¬ VacuumLeftCouplingD :=
  fun h' => not_vacuumLeftSpectral_of_goalPos1 h
    (vacuumLeftSpectral_of_coupling (vacuumLeftCoupling_of_D h'))

/-- The round-8 twist premise with the derivative computed.  NOT proved here. -/
def CofinalTwistVacuumCouplingD : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ J' : TwistSpace (2 ^ j) R, IsSourceDerivative (2 ^ j) R J' →
      CouplingCrossingD (2 ^ j) R (AdalyFormal.D1Literal.Uth ((dilTower (2 ^ j) R).Om 0)) J'

theorem twistVacuumCoupling_of_D (h : CofinalTwistVacuumCouplingD) : CofinalTwistVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun J' hJ' => ?_⟩
  have hq : 0 < 2 ^ j := by positivity
  exact couplingCrossing_of_D hq hR (by nlinarith) _ (Uth_vac_smooth _ R) J' (hc J' hJ')

/-- **`X → CofinalTwistSeparation`** with `X` the zero-curvature crossing data of the round-8
twist (derivative computed, coupling explicit). -/
theorem cofinalTwistSeparation_of_twistVacuumCouplingD (h : CofinalTwistVacuumCouplingD) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_twistVacuumCoupling (twistVacuumCoupling_of_D h)

theorem goalNeg2_of_twistVacuumCouplingD (h : CofinalTwistVacuumCouplingD) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_twistVacuumCouplingD h)

end VacuumDeriv

end AdalyFormal.Round9.Guarded.AnalyticR2


/-!
Round 9.2, qualitative route, second part: the soft premise is a theorem for every profile.

The analytic route's appendices (`AnalyticR1`, `AnalyticR2`, copied verbatim above from
`AHP/round9/analytic-r1/Appendix.lean` and `AHP/round9/analytic-r2/Appendix.lean`) contain a
generic theory of smooth curvature families based at the trivial background
(`AnalyticR2.dataFam`, `continuousAt_Ginv_dataS`, `continuousAt_H`, `tendsto_Delta2_div`,
`exists_source_derivative`), and the unit `AnalyticR2.dil_flat_unit` of the flat localized
carrier at every scale and radius.  Here that theory is instantiated at the interior family
`ε ↦ maskedU (ε f) 1` of an ARBITRARY profile `f`, with the two-sided limit.  This proves this
round's soft premise `QualitativeR2.InteriorSoft q R f (corrDeriv q R f)` for every `f`, every
`q > 0` and every even `R ≥ 16`, where `corrDeriv q R f` is the actual derivative at `0` of the
localized correction.  The canonical vacuum crossing of the twist holds at every instance.

The premise that remains is one statement per instance: the first-order coefficient
`corrDeriv` is definite, of either sign, on the kernel of the vacuum carrier of the round-8
twist at its canonical crossing (`CofinalCanonicalCoupling`; free-profile form
`CofinalAnyProfileCoupling`; explicit form `CofinalExplicitCoupling` with the analytic route's
coupling `2⟪H₀ C²₀(W₀ u), J'⟫`; complex-line form `CofinalExplicitU1`).  Nothing here proves
a pinned goal.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (PSD)

/-! ## A. The interior family of an arbitrary profile: smooth, flat at `ε = 0` -/

section BulkFamily

open scoped Matrix.Norms.Frobenius

/-- The interior family of the profile `f` (curvature `ε f` on the bonds touching `Ω₀`,
trivial exterior), as a curvature family. -/
noncomputable abbrev bulkV (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun ε => QualitativeR2.bulkU q R f ε

theorem bulkU_link_contDiff (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((QualitativeR2.bulkU q R f ε e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [QualitativeR2.bulkU, maskedU, if_pos he]
    exact contDiff_const
  · simp only [QualitativeR2.bulkU, maskedU, if_neg he]
    have hl : ContDiff ℝ ⊤ (fun ε : ℝ => ε * f e) := contDiff_id.mul contDiff_const
    refine contDiff_iff_contDiffAt.mpr (fun ε => ?_)
    have h := (AnalyticR2.contDiffAt_Ug (ε * f e)).comp ε hl.contDiffAt
    exact h

theorem bulkV_smooth (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.SmoothAt0 (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).contDiffAt

theorem bulkV_contFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AdalyFormal.D1Literal.ContFam (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).continuous

end BulkFamily

theorem bulkU_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.bulkU q R f 0 = fun _ => 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, zero_mul, Ug_zero, ite_self]

theorem bulk_dataFam_zero (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1
        (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (QualitativeR2.bulkU q R f 0) 1
    (dilLam q R)) = _
  rw [bulkU_zero]

theorem bulk_dataFam_zero_eq (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (AnalyticR2.dilV q R) 1
        (dilLam q R) 0 := by
  rw [bulk_dataFam_zero, AnalyticR2.dataFam_dil_zero]

theorem bulkD_eq_dataFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    QualitativeR2.bulkD q R f ε =
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
        (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl

theorem bulkA_eq_dataFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    QualitativeR2.bulkA q R f ε =
      (AnalyticR2.dataFam selAll selAll (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
        (dilLam q R) ε).Ginv := rfl

/-! ## B. Continuity at the flat interior and the first-order coefficient -/

theorem bulk_LP0 {q R : ℕ} (hq : 0 < q) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) :=
  AnalyticR2.dil_LP_unit q R hq _

theorem bulk_Gam0 {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AnalyticR2.Gam (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact AnalyticR2.dil_Gam_unit hS

theorem bulk_reg0 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (bulkV q R f 0) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact RegBg_flat _ _

theorem bulk_W_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1) 0 :=
  AnalyticR2.continuousAt_Wop (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)

theorem bulk_T_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_Tfull (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)

theorem bulk_Q_cont (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_QfullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f)

theorem bulk_carrier_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0 :=
  AnalyticR2.continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (bulkV q R f) 1
    (dilLam q R) (bulkV_contFam q R f) (bulk_W_cont hq hS f) (bulk_T_cont hq hS f)
    (bulk_Q_cont q R f)

theorem bulk_H_cont {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Q) 0 := by
    show ContinuousAt (fun ε => (QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
      (iE (geomOf 2 1 (dilTower q R)))) 0
    exact AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Qs) 0 := by
    show ContinuousAt (fun ε => ContinuousLinearMap.adjoint
      ((QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
        (iE (geomOf 2 1 (dilTower q R))))) 0
    exact AnalyticR2.cont_adjoint.continuousAt.comp
      (AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const)
  have hB0 : IsUnit (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Ginv := by
    rw [bulk_dataFam_zero]
    exact AnalyticR2.dil_flat_unit hq (by omega)
  have hN0 : IsUnit (((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Q.comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).G).comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).Qs) := by
    rw [bulk_dataFam_zero_eq]
    exact AnalyticR2.dil_N0_unit hq hR16 hS
  exact AnalyticR2.continuousAt_H
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (bulk_carrier_cont hq hS f selIn selIn) hQc hQsc hB0 hN0

theorem bulk_C2_tendsto {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (A : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    Tendsto (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).C2 A) (𝓝 0)
      (𝓝 ((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).C2 A)) := by
  show Tendsto (fun ε => C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1 (iE (geomOf 2 1 (dilTower q R)) A))) (𝓝 0)
    (𝓝 (C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f 0)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1 (iE (geomOf 2 1 (dilTower q R)) A))))
  exact AnalyticR2.tendsto_C2fullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f) (AnalyticR2.tendsto_clm_apply₂ (bulk_W_cont hq hS f) tendsto_const_nhds)

/-- The localized source of the interior family has a curvature derivative (two-sided). -/
theorem bulk_J_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ J' : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε => ε⁻¹ • (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := AnalyticR2.exists_source_derivative (bulkV q R f) (bulkV_smooth q R f)
    (bulkU_zero q R f) (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  show Tendsto (fun ε : ℝ => ε⁻¹ • pE (geomOf 2 1 (dilTower q R))
      (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (bulkV q R f ε) b)))) (𝓝[≠] 0)
    (𝓝 (pE (geomOf 2 1 (dilTower q R)) J'))
  simp only [← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'

/-- `Δ⁽²⁾(ε)/ε` converges as `ε → 0` from both sides, for every profile. -/
theorem bulk_exists_D1 {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ D₁ : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε : ℝ => ε⁻¹ • QualitativeR2.bulkD q R f ε) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := bulk_J_tendsto q R f
  obtain ⟨D₁, hD₁⟩ := AnalyticR2.tendsto_Delta2_div
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkV q R f ε) 1 (dilLam q R)))
    (bulk_H_cont hq hR16 hS f) (bulk_C2_tendsto hq hS f) J' hJ
  refine ⟨D₁, ?_⟩
  simp only [bulkD_eq_dataFam]
  exact hD₁

/-- At zero curvature the correction of the interior family vanishes. -/
theorem bulkD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : QualitativeR2.bulkD q R f 0 = 0 := by
  rw [← QualitativeR2.pathD_base q R (QualitativeR2.uthPath_zero q R) f 0]
  exact pathD_zero hq hR h3 (uthPath q R) f 1 0

/-- **The correction of the interior family is differentiable at the flat interior**, for every
profile. -/
theorem bulk_hasDerivAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) De 0 := by
  obtain ⟨D₁, hD₁⟩ := bulk_exists_D1 hq hR16 (dil_admissible hq hR) f
  have hq1 : 1 ≤ q := hq
  have h3 : 3 ≤ R * (2*q) := by nlinarith
  have h0 := bulkD_zero hq hR h3 f
  refine ⟨D₁, (hasDerivAt_iff_tendsto_slope_zero (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε)
    (f' := D₁) (x := 0)).mpr ?_⟩
  refine hD₁.congr' (Filter.Eventually.of_forall (fun t => ?_))
  simp only [zero_add, h0, sub_zero]

/-- The actual first-order coefficient of the localized correction along the interior family of
the profile `f`. -/
noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0

theorem hasDerivAt_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) 0 := by
  obtain ⟨De, h⟩ := bulk_hasDerivAt hq hR hR16 f
  have e : corrDeriv q R f = De :=
    HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (f' := De) (x := 0) h
  rw [e]
  exact h

/-- **This round's soft premise is a theorem**, for every profile, every scale `q > 0` and every
even radius `R ≥ 16`. -/
theorem interiorSoft_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.InteriorSoft q R f (corrDeriv q R f) := by
  have hS := dil_admissible hq hR
  refine ⟨?_, bulk_W_cont hq hS f, hasDerivAt_corrDeriv hq hR hR16 f⟩
  show ContinuousAt (fun ε => (AnalyticR2.dataFam selAll selAll (by norm_num : 0 < 2)
    (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0
  exact bulk_carrier_cont hq hS f selAll selAll

theorem interiorSoft_exists {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      QualitativeR2.InteriorSoft q R f De :=
  ⟨_, interiorSoft_corrDeriv hq hR hR16 f⟩

/-! ## C. The canonical crossing at every instance -/

/-- The flat localized carrier is a unit at every scale and radius (analytic route). -/
theorem flat_loc_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (QualitativeR2.flatP q R)).Ginv :=
  AnalyticR2.dil_flat_unit hq hR

/-- **Unconditional, at every instance.**  For every scale `q > 0` and every even `R ≥ 18` the
vacuum carrier of the round-8 twist crosses at its canonical angle, forwards and backwards. -/
theorem twist_vacuum_crossing_all {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    QualitativeR2.VacuumCrossesAt q R (uthPath q R) (QualitativeR2.vacEdge q R (uthPath q R)) ∧
    QualitativeR2.VacuumCrossesAt q R (QualitativeR2.uthPathNeg q R)
      (QualitativeR2.vacEdge q R (QualitativeR2.uthPathNeg q R)) := by
  have hq1 : 1 ≤ q := hq
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  have hloc := flat_loc_unit hq (by omega : 1 ≤ R)
  exact ⟨QualitativeR2.vacuum_crossing hq hR hroom (uthPath_cont _ _)
      (QualitativeR2.uthPath_anFam _ _)
      (QualitativeR2.vacA_pd_zero (QualitativeR2.uthPath_zero _ _) hloc)
      (QualitativeR2.vacA_uth_pi_negative hq hR hroom),
    QualitativeR2.vacuum_crossing hq hR hroom (QualitativeR2.uthPathNeg_cont _ _)
      (QualitativeR2.uthPathNeg_anFam _ _)
      (QualitativeR2.vacA_pd_zero (QualitativeR2.uthPathNeg_zero _ _) hloc)
      (QualitativeR2.vacA_uthNeg_pi_negative hq hR hroom)⟩

/-! ## D. The reduced premise: the coupling alone -/

/-- **Per instance.**  For every scale `q > 0` and every even `R ≥ 18`: if the actual first-order
coefficient of the single-defect correction is definite, of either sign, on the kernel of the
vacuum carrier at the canonical crossing of the round-8 twist, then the literal round-8 family
separates at every small positive curvature. -/
theorem twistSeparation_eventually_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R)
    (hc : QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε :=
  QualitativeR2.twistSeparation_eventually hq hR hR18 (flat_loc_unit hq (by omega))
    (QualitativeR2.twistSoftCoupling_of_fwd
      ⟨corrDeriv q R (dilMask q R), interiorSoft_corrDeriv hq hR (by omega) _, hc⟩)

/-- **X (literal family).**  For cofinal dyadic scales and, for each, cofinal even radii
`≥ 18`: the actual first-order coefficient of the single-defect correction is definite, of
either sign, on the kernel of the vacuum carrier of the round-8 twist at its canonical
crossing.  NOT proved here. -/
def CofinalCanonicalCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R (dilMask (2^j) R))

/-- **Main reduction: `X → CofinalTwistSeparation`** (round 8's target). -/
theorem cofinalTwistSeparation_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  obtain ⟨ε₀, hε₀, hall⟩ := twistSeparation_eventually_of_coupling (by positivity) hR hR18 hc
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

/-- **Main reduction: `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalCanonicalCoupling h)

theorem not_cofinalCanonicalCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalCanonicalCoupling :=
  fun h' => goalNeg2_of_cofinalCanonicalCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands: at every large scale and every large even radius the
first-order coupling is NOT definite on the canonical vacuum kernel. -/
theorem goalPos1_forces_degenerate_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
        (corrDeriv (2^j) R (dilMask (2^j) R)) := by
  have h' := not_cofinalCanonicalCoupling_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  exact ⟨R, hRR, hR2, hR18, not_not.mp hR4⟩

/-- At one instance, the reduced premise of the first part of this round
(`QualitativeR2.TwistSoftCouplingFwd`: soft regularity and a definite coupling) is exactly the
coupling clause for the actual derivative: its soft clause is a theorem, and any derivative in it
is `corrDeriv`. -/
theorem twistSoftCouplingFwd_iff {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R) :
    QualitativeR2.TwistSoftCouplingFwd q R ↔
      QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  constructor
  · rintro ⟨De, hs, hc⟩
    have e : De = corrDeriv q R (dilMask q R) :=
      HasDerivAt.unique (f := fun ε : ℝ => QualitativeR2.bulkD q R (dilMask q R) ε) (f₀' := De)
        (f₁' := corrDeriv q R (dilMask q R)) (x := 0) hs.2.2
        (hasDerivAt_corrDeriv hq hR hR16 (dilMask q R))
    rw [← e]
    exact hc
  · intro hc
    exact ⟨_, interiorSoft_corrDeriv hq hR hR16 _, hc⟩

/-- `CofinalCanonicalCoupling` is the first part's `CofinalTwistSoftCouplingFwd` with its soft
clause removed. -/
theorem cofinalCanonicalCoupling_iff :
    CofinalCanonicalCoupling ↔ QualitativeR2.CofinalTwistSoftCouplingFwd := by
  constructor
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, (twistSoftCouplingFwd_iff (by positivity) hR (by omega)).mpr hc⟩
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, (twistSoftCouplingFwd_iff (by positivity) hR (by omega)).mp hc⟩

/-! ## E. Free profile -/

theorem bulkU_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkU q R (fun e => c * f e) ε = QualitativeR2.bulkU q R f (c * ε) := by
  unfold QualitativeR2.bulkU
  congr 1
  funext e
  ring

theorem bulkD_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkD q R (fun e => c * f e) ε = QualitativeR2.bulkD q R f (c * ε) := by
  have hd : dataS selIn selIn (QualitativeR2.bulkP q R (fun e => c * f e) ε) =
      dataS selIn selIn (QualitativeR2.bulkP q R f (c * ε)) := by
    unfold QualitativeR2.bulkP
    rw [bulkU_smul]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- Rescaling the profile rescales the first-order coefficient. -/
theorem corrDeriv_smul {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ) :
    corrDeriv q R (fun e => c * f e) = c • corrDeriv q R f := by
  have h1 := hasDerivAt_corrDeriv hq hR hR16 f
  have hl : HasDerivAt (fun ε : ℝ => c * ε) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h1' : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) (c * 0) := by
    rw [mul_zero]
    exact h1
  have h2 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f (c * ε)) (c • corrDeriv q R f) 0 :=
    HasDerivAt.scomp (g₁ := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (h := fun ε : ℝ => c * ε)
      0 h1' hl
  have e : (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε) =
      fun ε => QualitativeR2.bulkD q R f (c * ε) := funext (bulkD_smul q R f c)
  have h3 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
      (c • corrDeriv q R f) 0 := by
    rw [e]
    exact h2
  exact HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
    (f' := c • corrDeriv q R f) (x := 0) h3

/-- A definite coupling stays definite under a nonzero rescaling. -/
theorem canonicalCoupling_smul {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    {c : ℝ} (hc : c ≠ 0) (h : QualitativeR2.CanonicalCoupling q R V De) :
    QualitativeR2.CanonicalCoupling q R V (c • De) := by
  obtain ⟨c₀, hc₀, hs⟩ := h
  have e : ∀ u, ⟪u, (c • De) u⟫ = c * ⟪u, De u⟫ := fun u => by
    rw [smul_apply, real_inner_smul_right]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hc' : 0 ≤ -c := by linarith
    refine ⟨(-c) * c₀, mul_pos (neg_pos.mpr hneg) hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hc'
      rw [e]
      nlinarith [h1]
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hc'
      rw [e]
      nlinarith [h1]
  · refine ⟨c * c₀, mul_pos hpos hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hpos.le
      rw [e]
      nlinarith [h1]
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hpos.le
      rw [e]
      nlinarith [h1]

/-- **X (free profile, weakest form).**  For cofinal dyadic scales and, for each, cofinal even
radii `≥ 18`: SOME interior profile has a first-order coefficient that is definite, of either
sign, on the kernel of the vacuum carrier at the canonical crossing of the round-8 twist.
NOT proved here. -/
def CofinalAnyProfileCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
      QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)

/-- Every profile has a positive multiple within the class bound `|f| ≤ 1`. -/
theorem exists_profile_scale {L : PeriodicLatticeExtent} (f : Bond L → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ e, |c * f e| ≤ 1 := by
  have hs0 : 0 ≤ ∑ e, |f e| := Finset.sum_nonneg (fun e _ => abs_nonneg (f e))
  have hpos : (0 : ℝ) < 1 + ∑ e, |f e| := by linarith
  refine ⟨1 / (1 + ∑ e, |f e|), one_div_pos.mpr hpos, fun e => ?_⟩
  have h1 : |f e| ≤ ∑ e, |f e| :=
    Finset.single_le_sum (f := fun e => |f e|) (fun e _ => abs_nonneg (f e)) (Finset.mem_univ e)
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpos), one_div, inv_mul_le_iff₀ hpos]
  linarith

/-- Any profile with a definite coupling, rescaled into the class bound, gives round 9.2's
weakest premise at that instance. -/
theorem pathSoftCoupling_of_profile {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hc : QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R f)) :
    QualitativeR2.PathSoftCoupling q R := by
  obtain ⟨c, hcpos, hcb⟩ := exists_profile_scale f
  refine ⟨fun e => c * f e, hcb, corrDeriv q R (fun e => c * f e),
    interiorSoft_corrDeriv hq hR hR16 _, Or.inl ?_⟩
  rw [corrDeriv_smul hq hR hR16 f c]
  exact canonicalCoupling_smul hcpos.ne' hc

theorem cofinalPathSoftCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    QualitativeR2.CofinalPathSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, pathSoftCoupling_of_profile (by positivity) hR (by omega) f hc⟩

/-- **Main reduction (weakest premise): `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalAnyProfileCoupling (h : CofinalAnyProfileCoupling) : GoalNeg2 :=
  QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling (cofinalPathSoftCoupling_of_anyProfile h)

theorem not_cofinalAnyProfileCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalAnyProfileCoupling :=
  fun h' => goalNeg2_of_cofinalAnyProfileCoupling h' (goalPos2_iff_goalPos1.mpr h)

theorem cofinalAnyProfileCoupling_of_canonical (h : CofinalCanonicalCoupling) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, dilMask (2^j) R, hc⟩

/-- What the positive reading demands, over all profiles: at every large scale and every large
even radius, NO interior profile has a definite first-order coupling on the canonical vacuum
kernel. -/
theorem goalPos1_forces_degenerate_profiles (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f) := by
  have h' := not_cofinalAnyProfileCoupling_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨f, hf⟩ := not_forall.mp hR4
  exact ⟨R, hRR, hR2, hR18, f, not_not.mp hf⟩

/-! ## F. The explicit coupling `2⟪H₀ C²₀(W₀ u), J'⟫` (analytic route) -/

theorem bulkU_dilMask (q R : ℕ) (ε : ℝ) :
    QualitativeR2.bulkU q R (dilMask q R) ε = dilU q R ε 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, dilU, dilMask]
  split_ifs <;> first | rfl | simp

theorem bulkD_dilMask (q R : ℕ) (ε : ℝ) :
    QualitativeR2.bulkD q R (dilMask q R) ε = AnalyticR1.extD q R ε 1 := by
  have hd : dataS selIn selIn (QualitativeR2.bulkP q R (dilMask q R) ε) =
      dataS selIn selIn (AnalyticR1.extP q R ε 1) := by
    unfold QualitativeR2.bulkP AnalyticR1.extP
    rw [bulkU_dilMask]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- The quadratic form of the actual first-order coefficient of the single-defect correction is
the analytic route's explicit vacuum coupling `2⟪H₀ C²₀(W₀ u), J'⟫`. -/
theorem corrDeriv_dilMask_form {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (J' : AnalyticR1.TwistSpace q R) (hJ : AnalyticR2.IsSourceDerivative q R J')
    (u : AnalyticR1.TwistSpace q R) :
    ⟪u, corrDeriv q R (dilMask q R) u⟫ = AnalyticR2.vacCoupling q R J' u := by
  have hD := hasDerivAt_corrDeriv hq hR hR16 (dilMask q R)
  have hq1 : 1 ≤ q := hq
  have h3 : 3 ≤ R * (2*q) := by nlinarith
  have h0 : AnalyticR1.extD q R 0 1 = 0 := by
    rw [← bulkD_dilMask]
    exact bulkD_zero hq hR h3 (dilMask q R)
  have hT : Tendsto (fun ε : ℝ => ε⁻¹ • AnalyticR1.extD q R ε 1) (𝓝[>] 0)
      (𝓝 (corrDeriv q R (dilMask q R))) := by
    refine (HasDerivAt.tendsto_slope_zero_right
      (f := fun ε : ℝ => QualitativeR2.bulkD q R (dilMask q R) ε)
      (f' := corrDeriv q R (dilMask q R)) (x := 0) hD).congr'
      (Filter.Eventually.of_forall (fun t => ?_))
    simp only [zero_add, bulkD_dilMask, h0, sub_zero]
  exact AnalyticR2.dil_D1_form hq (dil_admissible hq hR) hR16 _ hT J' hJ u

/-- **X at one instance, explicit form.**  For the curvature derivative `J'` of the localized
source, the explicit coupling `2⟪H₀ C²₀(W₀ u), J'⟫` is definite, of either sign, on the kernel
of the vacuum carrier at the canonical crossing of the round-8 twist.  NOT proved here. -/
def ExplicitCoupling (q R : ℕ) : Prop :=
  ∀ J' : AnalyticR1.TwistSpace q R, AnalyticR2.IsSourceDerivative q R J' →
    ∃ c : ℝ, 0 < c ∧
      ((∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
          c * ‖u‖ ^ 2 ≤ AnalyticR2.vacCoupling q R J' u) ∨
        (∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
          c * ‖u‖ ^ 2 ≤ -AnalyticR2.vacCoupling q R J' u))

theorem canonicalCoupling_of_explicit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitCoupling q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  obtain ⟨J', hJ'⟩ := AnalyticR2.dil_J_tendsto q R
  obtain ⟨c, hc, hp | hn⟩ := h J' hJ'
  · exact ⟨c, hc, Or.inl (fun u hu => by
      rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u]; exact hp u hu)⟩
  · exact ⟨c, hc, Or.inr (fun u hu => by
      rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u]; exact hn u hu)⟩

def CofinalExplicitCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ExplicitCoupling (2^j) R

theorem cofinalCanonicalCoupling_of_explicit (h : CofinalExplicitCoupling) :
    CofinalCanonicalCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicit (by positivity) hR (by omega) hc⟩

theorem cofinalTwistSeparation_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_cofinalCanonicalCoupling (cofinalCanonicalCoupling_of_explicit h)

theorem goalNeg2_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalCanonicalCoupling (cofinalCanonicalCoupling_of_explicit h)

/-- **X at one instance, complex-line form.**  The canonical forward vacuum kernel is the complex
line of one charged vector `u₀` (`J (J u₀) = -u₀`, `J` the quarter rotation), and the explicit
coupling of `u₀` is nonzero: round 8's `c₁(q,R) ≠ 0`.  NOT proved here. -/
def ExplicitU1 (q R : ℕ) : Prop :=
  ∃ u₀ : AnalyticR1.TwistSpace q R, u₀ ≠ 0 ∧
    vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u₀ = 0 ∧
    adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
    (∀ u, vacA q R (uthPath q R) 1 (QualitativeR2.vacEdge q R (uthPath q R)) u = 0 →
      u ∈ Submodule.span ℝ {u₀,
        adEL (QualitativeR2.rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀}) ∧
    ∀ J' : AnalyticR1.TwistSpace q R, AnalyticR2.IsSourceDerivative q R J' →
      AnalyticR2.vacCoupling q R J' u₀ ≠ 0

theorem canonicalCoupling_of_explicitU1 {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitU1 q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R)) := by
  obtain ⟨u₀, hu₀, hk, hJJ, hK, hc⟩ := h
  obtain ⟨J', hJ'⟩ := AnalyticR2.dil_J_tendsto q R
  refine QualitativeR2.canonicalCoupling_of_U1 (hasDerivAt_corrDeriv hq hR hR16 (dilMask q R))
    ⟨u₀, hu₀, hk, hJJ, hK, ?_⟩
  rw [corrDeriv_dilMask_form hq hR hR16 J' hJ' u₀]
  exact hc J' hJ'

def CofinalExplicitU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ ExplicitU1 (2^j) R

theorem goalNeg2_of_cofinalExplicitU1 (h : CofinalExplicitU1) : GoalNeg2 := by
  apply goalNeg2_of_cofinalCanonicalCoupling
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicitU1 (by positivity) hR (by omega) hc⟩

theorem cofinalTwistSeparation_of_cofinalExplicitU1 (h : CofinalExplicitU1) :
    CofinalTwistSeparation := by
  apply cofinalTwistSeparation_of_cofinalCanonicalCoupling
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hc⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, canonicalCoupling_of_explicitU1 (by positivity) hR (by omega) hc⟩

/-! ## G. Any analytic exterior path -/

/-- **X (weakest form, over exterior paths and profiles).**  For cofinal dyadic scales and, for
each, cofinal even radii `≥ 18`: SOME continuous, real-analytic exterior path starting at the
trivial field, whose vacuum carrier has a negative direction at angle `π`, and SOME interior
profile, whose first-order coefficient is definite, of either sign, on the kernel of the vacuum
carrier at the canonical crossing of that path.  NOT proved here. -/
def CofinalAnyPathCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
      QualitativeR2.AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R f)

theorem cofinalVacuumCoupling_of_anyPath (h : CofinalAnyPathCoupling) : CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, f, hc⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨c, hcpos, hcb⟩ := exists_profile_scale f
  have hc' : QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R (fun e => c * f e)) := by
    rw [corrDeriv_smul hq hR (by omega) f c]
    exact canonicalCoupling_smul hcpos.ne' hc
  exact ⟨R, hRR, hR, hR18, V, hVc, fun e => c * f e, hcb,
    QualitativeR2.vacuumCoupling_of_soft hq hR hroom hVc hVa hV0 (flat_loc_unit hq (by omega))
      hneg (interiorSoft_corrDeriv hq hR (by omega) _) hc'⟩

/-- **Main reduction (weakest premise over paths and profiles): `X → GoalNeg2`.** -/
theorem goalNeg2_of_cofinalAnyPathCoupling (h : CofinalAnyPathCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_anyPath h)

theorem not_cofinalAnyPathCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalAnyPathCoupling :=
  fun h' => goalNeg2_of_cofinalAnyPathCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- The round-8 twist is such a path. -/
theorem cofinalAnyPathCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    CofinalAnyPathCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hc⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont _ _, QualitativeR2.uthPath_anFam _ _,
    QualitativeR2.uthPath_zero _ _, QualitativeR2.vacA_uth_pi_negative hq hR hroom, f, hc⟩

end AdalyFormal.Round9.Guarded.QualitativeR2Joint

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_link_contDiff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV_smooth
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV_contFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero_eq
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkA_eq_dataFam
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_LP0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_Gam0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_reg0
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_W_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_T_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_Q_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_carrier_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_J_tendsto
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_exists_D1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_zero
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_hasDerivAt
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_exists
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.flat_loc_unit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twist_vacuum_crossing_all
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalCanonicalCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_coupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSoftCouplingFwd_iff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_iff
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.pathSoftCoupling_of_profile
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalAnyProfileCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyProfileCoupling_of_canonical
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_profiles
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_dilMask
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_dilMask
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitU1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalAnyPathCoupling_of_goalPos1
#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyPathCoupling_of_anyProfile

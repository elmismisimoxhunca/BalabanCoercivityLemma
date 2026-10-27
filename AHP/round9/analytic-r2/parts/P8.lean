
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

section Final

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace extP extA extD InteriorRegularity InteriorSoft)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

/-- the curved dilated family. -/
noncomputable abbrev dilV (q R : ℕ) : ℝ → Cfg (scaleUp 2 1 (dilLu q R)) := fun ε => dilU q R ε 1

theorem dataFam_dil_zero (sD sJ : PlaqSel) (q R : ℕ) :
    dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (dilU q R 0 1) 1 (dilLam q R)) = _
  rw [dilU_zero]

theorem dil_B0_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  exact dil_flat_unit hq hR

theorem dil_B0_psd {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    AdalyFormal.D1Literal.PSD
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  intro v
  by_cases hv : v = 0
  · rw [hv, inner_zero_left]
  · exact (dil_flat_pos hq hR v hv).le

theorem dil_Qs0_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs := by
  rw [dataFam_dil_zero]
  exact dil_Qs_inj hq hR16 hS

theorem dil_N0_unit {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Q.comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).G).comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs) := by
  set D0 := dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0
  have hL : D0.Laws := dataS_laws selIn selIn _
  obtain ⟨m, hm, hmc⟩ := AdalyFormal.D1Literal.psd_coercive D0.Ginv (D0.Ginv_symm hL)
    (dil_B0_psd hq (by omega)) (dil_B0_unit hq (by omega))
  exact isUnit_Q_inv_Qs (D0.Ginv_symm hL) hm hmc D0.Q_adj (dil_Qs0_inj hq hR16 hS)

theorem extA_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extA q R ε 1 = (dataFam selAll selAll (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv := rfl

theorem extD_eq_dataFam (q R : ℕ) (ε : ℝ) :
    extD q R ε 1 = (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl

theorem C2_dataFam (q R : ℕ) (ε : ℝ) (A : TwistSpace q R) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).C2 A =
      C2fullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)
        (Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1 (iE (geomOf 2 1 (dilTower q R)) A)) := rfl

theorem J_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).J =
      pE (geomOf 2 1 (dilTower q R)) (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (dilV q R ε) b))) := rfl

theorem Q_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Q =
      (QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R))) := rfl

theorem Qs_dataFam (q R : ℕ) (ε : ℝ) :
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) ε).Qs =
      ContinuousLinearMap.adjoint
        ((QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)).comp (iE (geomOf 2 1 (dilTower q R)))) := rfl

section DilCont
variable {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))

omit hq hS in
theorem dil_reg0 (q R : ℕ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (dilV q R 0) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact RegBg_flat _ _

omit hq hS in
theorem dil_LP0 (hq : 0 < q) : IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) :=
  dil_LP_unit q R hq _

omit hq hS in
theorem dil_Gam0 (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (dilV q R 0) 1) := by
  rw [show dilV q R 0 = fun _ => 1 from dilU_zero q R]; exact dil_Gam_unit hS

include hq hS in
theorem dil_W_cont : ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (dilV q R ε) 1) 0 :=
  continuousAt_Wop (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

include hq hS in
theorem dil_T_cont : ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_Tfull (dilU_contFam q R) (geomOf 2 1 (dilTower q R)) rfl 1 (dil_LP0 hq) (dil_wq_pos q R)
    (dil_Gam0 hS)

omit hq hS in
theorem dil_Q_cont (q R : ℕ) : ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (dilV q R ε)) 0 :=
  continuousAt_QfullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)

include hq hS in
theorem dil_carrier_cont (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Ginv) 0 :=
  continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (dilV q R) 1 (dilLam q R)
    (dilU_contFam q R) (dil_W_cont hq hS) (dil_T_cont hq hS) (dil_Q_cont q R)

include hq hS in
theorem dil_tendsto_extA :
    Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) := by
  simp only [extA_eq_dataFam]
  exact (dil_carrier_cont hq hS selAll selAll).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_tendsto_W :
    Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
      (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) :=
  (dil_W_cont hq hS).tendsto.mono_left nhdsWithin_le_nhds

include hq hS in
theorem dil_H_cont (hR : 16 ≤ R) :
    ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Q) 0 := by
    simp only [Q_dataFam]
    exact continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Qs) 0 := by
    simp only [Qs_dataFam]
    exact cont_adjoint.continuousAt.comp (continuousAt_clm_comp (dil_Q_cont q R) continuousAt_const)
  exact continuousAt_H _ (dil_carrier_cont hq hS selIn selIn) hQc hQsc (dil_B0_unit hq (by omega))
    (dil_N0_unit hq hR hS)

include hq hS in
theorem dil_C2_tendsto (A : TwistSpace q R) :
    Tendsto (fun ε => (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).C2 A) (𝓝 0) (𝓝 ((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (dilV q R) 1 (dilLam q R) 0).C2 A)) := by
  simp only [C2_dataFam]
  exact tendsto_C2fullOf (dilV q R) (dilU_smooth q R) (geomOf 2 1 (dilTower q R)) rfl (dil_reg0 q R)
    (tendsto_clm_apply₂ (dil_W_cont hq hS) tendsto_const_nhds)

omit hq hS in
theorem dil_J_tendsto (q R : ℕ) : ∃ J' : TwistSpace q R,
    Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := exists_source_derivative (dilV q R) (dilU_smooth q R) (dilU_zero q R)
    (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  simp only [J_dataFam, ← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'

include hq hS in
theorem dil_exists_D1 (hR : 16 ≤ R) : ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R,
    Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := dil_J_tendsto q R
  have hH := dil_H_cont hq hS hR
  have hC2 := dil_C2_tendsto hq hS
  obtain ⟨D₁, hD₁⟩ := tendsto_Delta2_div
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))) hH hC2 J' hJ
  refine ⟨D₁, ?_⟩
  simp only [extD_eq_dataFam]
  exact hD₁.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))

include hq hS in
/-- **The first-order coefficient, explicitly.**  Any limit `D₁` of `extD(ε)/ε` has the quadratic form
`A ↦ 2⟪H₀ C²₀(W₀ A), J'⟫`: `H₀`, `C²₀`, `W₀` are the flat (vacuum) constrained inverse, second
jet and dressing of the localized data, and `J'` the curvature derivative of the source. -/
theorem dil_D1_form (hR : 16 ≤ R) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)) (J' : TwistSpace q R)
    (hJ : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')) (A : TwistSpace q R) :
    ⟪A, D₁ A⟫ = 2 * ⟪(dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).H
      (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
        (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) A))), J'⟫ := by
  have hD₁' : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).Delta2 (dataS_laws selIn selIn
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R))))
      (𝓝[>] 0) (𝓝 D₁) := by
    simp only [← extD_eq_dataFam]
    exact hD₁
  have h := limit_Delta2_div_form
    (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilV q R ε) 1 (dilLam q R)))
    (dil_H_cont hq hS hR) (dil_C2_tendsto hq hS) J' hJ D₁ hD₁' A
  rw [h, dataFam_dil_zero]
  rfl

end DilCont

/-- **Soft regularity of the curved dilated family at zero curvature**, for every scale and every
even radius `≥ 18`, given admissibility of the tower: the carrier and `W` are continuous at `ε = 0`
and `Δ⁽²⁾(ε)/ε` converges. -/
theorem interiorRegularity_of_admissible {q R : ℕ} (hq : 0 < q) (hR : 18 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁ := by
  obtain ⟨D₁, hD₁⟩ := dil_exists_D1 hq hS (by omega)
  exact ⟨D₁, dil_tendsto_extA hq hS, dil_tendsto_W hq hS, hD₁⟩

/-- `InteriorSoft` (round 1), given admissibility of the dilated towers. -/
theorem interiorSoft_of_admissible
    (hS : ∀ q R : ℕ, 0 < q → 2 ∣ R → Admissible 2 (2 * q) R 1 (dilTower q R)) : InteriorSoft :=
  fun q R hq hR hR18 => interiorRegularity_of_admissible hq hR18 (hS q R hq hR)

end Final

end AdalyFormal.Round9.Guarded.AnalyticR2

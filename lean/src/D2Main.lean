import D2Lit

/-!
# D2Main -- the masked reading: collapse, path `Uth`, `Ginv` along the path, continuity, flat positivity, and the abstract non-unit theorem given a negative direction at `θ = π`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.StatementLaneR6

theorem genFormM_collapse (sD sJ : PlaqSel) (bs : BondSel) (P : IngrBParams) (h : ¬ IsUnit (dataM sD sJ bs P).Ginv)
    (B : BondFnL2 P.Lu) : GenM.genFormM sD sJ bs P B = -P.a * ⟪B, B⟫ := by
  have hL := dataM_laws sD sJ bs P
  have hG := G1invM_spec sD sJ bs P
  have hN : GenM.NmatM sD sJ bs P = 0 := by
    unfold GenM.NmatM
    rw [gen_G1_zero _ hL h hG]
    simp only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  have hH : H1inM sD sJ bs P = 0 := by
    unfold H1inM
    rw [gen_H1_zero _ hL h hG]
    simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
  unfold GenM.genFormM GenM.firstTermM
  rw [hN, hH, Ring.inverse_zero]
  simp

theorem not_InstIneqM_of_not_unit (sD sJ : PlaqSel) (bs : BondSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 ≤ a)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (hγ : 0 < γ₀)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu))
    (hnu : ¬ IsUnit (dataM sD sJ bs (gparams ell k Lu hell S U a Lam)).Ginv)
    (Bt : Bond Lu → SuTwo) (h1 : OnLambdaTildeIn Lam ell Bt) (h2 : OnLambdaT Lam Bt)
    (hE : 0 < bondEnergy Bt) :
    ¬ InstIneqM sD sJ bs ell k hell a Lu γ₀ S Lam U := by
  intro hI
  have h := hI Bt h1 h2
  rw [genFormM_collapse sD sJ bs _ hnu] at h
  have hB : 0 ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt) : BondFnL2 Lu),
      WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt)⟫ := real_inner_self_nonneg
  have : (gparams ell k Lu hell S U a Lam).a = a := rfl
  rw [this] at h
  nlinarith [mul_pos hγ hE, mul_nonneg ha hB]

theorem E0_DpiM_inner {L : PeriodicLatticeExtent} (sD : PlaqSel) (bs : BondSel) (G : TowerGeom L) (U : Cfg L) (a : ℝ) (w : ↥(bondSupp G)) :
    ⟪w, ((pE G).comp ((DpiFullM sD bs G U a).comp (iE G))) w⟫ =
      ⟪Wop G U a (iE G w), DeltaM sD bs G U (Wop G U a (iE G w))⟫ := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_right]
  unfold DpiFullM
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

section path
variable (sJ : PlaqSel) (bs : BondSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

/-- the masked literal `Ginv` at `θ`. -/
noncomputable def FthM (θ : ℝ) : ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) :=
  (dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam θ)).Ginv

theorem FthM_diff (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (θ : ℝ) :
    FthM sJ bs hell0 a Lam (S := S) θ = FthM sJ bs hell0 a Lam (S := S) 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a)).comp
        (((DeltaM selAll bs (geomOf ell k S) (Uth (S.Om 0) θ)) -
          (DeltaM selAll bs (geomOf ell k S) (Uth (S.Om 0) 0))).comp
          (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a))).comp (iE (geomOf ell k S))) := by
  have hUU : ∀ e : Bond (scaleUp ell k Lu), e ∉ Zb (S.Om 0) → Uth (S.Om 0) θ e = Uth (S.Om 0) 0 e :=
    fun e he => Uth_eq_off_Z _ _ _ e he
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → Uth (S.Om 0) θ e = Uth (S.Om 0) 0 e :=
    fun e he => hUU e (fun hz => Zb_not_bothIn _ hz he)
  have hW := Wop_congr_Z hS hell hroom hUU a
  have hT := Tfull_congr hS hell hroom hBoth
  have hsec := sector_congr hS hell hroom hBoth
  unfold FthM Pth BaseDataS.Ginv dataM
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullM, hW, hT, hsec]
  ext1 y
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub]
  abel

theorem FthM_symm (θ : ℝ) (u v : ↥(bondSupp (geomOf ell k S))) :
    ⟪FthM sJ bs hell0 a Lam (S := S) θ u, v⟫ = ⟪u, FthM sJ bs hell0 a Lam (S := S) θ v⟫ :=
  (dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam θ)).Ginv_symm (dataM_laws selAll sJ bs _) u v

theorem FthM_cont (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) :
    Continuous fun θ => FthM sJ bs hell0 a Lam (S := S) θ := by
  have h : (fun θ => FthM sJ bs hell0 a Lam (S := S) θ) = fun θ => FthM sJ bs hell0 a Lam (S := S) 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a)).comp
        (((DeltaM selAll bs (geomOf ell k S) (Uth (S.Om 0) θ)) -
          (DeltaM selAll bs (geomOf ell k S) (Uth (S.Om 0) 0))).comp
          (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a))).comp (iE (geomOf ell k S))) := by
    funext θ; exact FthM_diff sJ bs hell0 a Lam hS hell hroom θ
  rw [h]
  have hd : Continuous fun θ => DeltaM selAll bs (geomOf ell k S) (Uth (S.Om 0) θ) := by
    have h0 : Continuous fun θ => deltaKLocCLM (Uth (S.Om 0) θ) (Set.univ : Set (PeriodicLatticePlaquette (scaleUp ell k Lu))) :=
      cont_deltaKLocCLM (contFam_Uth _) _
    exact Continuous.clm_comp continuous_const (Continuous.clm_comp h0 continuous_const)
  refine continuous_const.add (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

theorem FthM_zero_psd (ha : 0 ≤ a) : PSD (FthM sJ bs hell0 a Lam (S := S) 0) := by
  intro (w : ↥(bondSupp (Pth ell k Lu hell0 S a Lam 0).G))
  show 0 ≤ ⟪w, (dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam 0)).Ginv w⟫
  rw [BaseDataS.inner_Ginv]
  have h1 : 0 ≤ ⟪w, (dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam 0)).Dpi w⟫ := by
    have e := E0_DpiM_inner selAll bs (geomOf ell k S) (Uth (S.Om 0) 0) a w
    have : Uth (S.Om 0) 0 = AdalyFormal.Balaban.DeltaPrime.trivialU := by rw [Uth_zero]; rfl
    refine le_of_le_of_eq ?_ e.symm
    unfold DeltaM DeltaS selAll
    simp only [ContinuousLinearMap.comp_apply]
    rw [this, ← bondMask_symm]
    exact deltaKLocCLM_flat_nonneg _ _
  have h2 : 0 ≤ ‖(dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam 0)).T w‖ ^ 2 := by positivity
  have h3 : 0 ≤ ⟪w, (dataM selAll sJ bs (Pth ell k Lu hell0 S a Lam 0)).Mass w⟫ := by
    have e := E0_Mass_inner (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) 0)) w
    refine le_of_le_of_eq ?_ e.symm
    refine Finset.sum_nonneg (fun p _ => ?_)
    have : (0 : ℝ) ≤ ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) := by positivity
    positivity
  linarith

/-- if the masked `Ginv` has a negative direction at `θ = π`, some `θ ∈ [0,π)` makes it a non-unit. -/
theorem exists_nonunit_GinvM (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (ha : 0 ≤ a)
    (hneg : ∃ v : ↥(bondSupp (geomOf ell k S)), ⟪v, FthM sJ bs hell0 a Lam (S := S) Real.pi v⟫ < 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ¬ IsUnit (dataM selAll sJ bs (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)).Ginv := by
  obtain ⟨v, hv⟩ := hneg
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_path (fun t => FthM sJ bs hell0 a Lam (S := S) t)
    (FthM_cont sJ bs hell0 a Lam hS hell hroom) (fun t u v => FthM_symm sJ bs hell0 a Lam t u v)
    (FthM_zero_psd sJ bs hell0 a Lam ha) Real.pi Real.pi_pos v hv
  exact ⟨θ, h0, h1, hnu⟩

end path

#print axioms genFormM_collapse
#print axioms exists_nonunit_GinvM

end AdalyFormal.D1Literal

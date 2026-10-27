import D1Mass
import D1IVT

/-!
# D1Main -- along `U_θ` the literal `Ginv` is PSD at `θ = 0`, has a negative direction at `θ = π`, hence is NOT a unit at some `θ ∈ [0,π)`.
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
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6

section generic
variable {L : PeriodicLatticeExtent} (sD : PlaqSel)

theorem E0_Dpi_inner (G : TowerGeom L) (U : Cfg L) (a : ℝ) (w : ↥(bondSupp G)) :
    ⟪w, ((pE G).comp ((DpiFullS sD G U a).comp (iE G))) w⟫ =
      ⟪Wop G U a (iE G w), DeltaS sD G U (Wop G U a (iE G w))⟫ := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_right]
  unfold DpiFullS
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem E0_Mass_inner (G : TowerGeom L) (a : ℝ) (S : BondSector G) (w : ↥(bondSupp G)) :
    ⟪w, ((pE G).comp ((MassFull G a S).comp (iE G))) w⟫ =
      ∑ p : BIdx G, a * (G.ell : ℝ) ^ (p.1 : ℕ) * ‖S.Qfull (iE G w) p‖ ^ 2 := by
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_right, inner_MassFull]

end generic

section
variable (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))

theorem Fth_symm (θ : ℝ) (u v : ↥(bondSupp (geomOf ell k S))) :
    ⟪Fth sJ ell k Lu hell0 S a Lam θ u, v⟫ = ⟪u, Fth sJ ell k Lu hell0 S a Lam θ v⟫ :=
  (dataS selAll sJ (Pth ell k Lu hell0 S a Lam θ)).Ginv_symm (dataS_laws selAll sJ _) u v

theorem Fth_cont (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) :
    Continuous fun θ => Fth sJ ell k Lu hell0 S a Lam θ := by
  have h : (fun θ => Fth sJ ell k Lu hell0 S a Lam θ) = fun θ => Fth sJ ell k Lu hell0 S a Lam 0 +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a)).comp
        (((deltaKLocCLM (Uth (S.Om 0) θ) Set.univ) - (deltaKLocCLM (Uth (S.Om 0) 0) Set.univ)).comp
          (Wop (geomOf ell k S) (Uth (S.Om 0) 0) a))).comp (iE (geomOf ell k S))) := by
    funext θ; exact Fth_diff sJ hell0 hS hell hroom a Lam θ
  rw [h]
  have hd : Continuous fun θ => deltaKLocCLM (Uth (S.Om 0) θ) (Set.univ : Set (PeriodicLatticePlaquette (scaleUp ell k Lu))) :=
    cont_deltaKLocCLM (contFam_Uth _) _
  refine continuous_const.add (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

theorem Fth_zero_psd (ha : 0 ≤ a) : PSD (Fth sJ ell k Lu hell0 S a Lam 0) := by
  intro (w : ↥(bondSupp (Pth ell k Lu hell0 S a Lam 0).G))
  show 0 ≤ ⟪w, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).Ginv w⟫
  rw [BaseDataS.inner_Ginv]
  have h1 : 0 ≤ ⟪w, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).Dpi w⟫ := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) (Uth (S.Om 0) 0) a w
    have : Uth (S.Om 0) 0 = AdalyFormal.Balaban.DeltaPrime.trivialU := by rw [Uth_zero]; rfl
    refine le_of_le_of_eq ?_ e.symm
    unfold DeltaS selAll
    rw [this]
    exact deltaKLocCLM_flat_nonneg _ _
  have h2 : 0 ≤ ‖(dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).T w‖ ^ 2 := by positivity
  have h3 : 0 ≤ ⟪w, (dataS selAll sJ (Pth ell k Lu hell0 S a Lam 0)).Mass w⟫ := by
    have e := E0_Mass_inner (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) 0)) w
    refine le_of_le_of_eq ?_ e.symm
    refine Finset.sum_nonneg (fun p _ => ?_)
    have : (0 : ℝ) ≤ ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) := by positivity
    positivity
  linarith


theorem sing_mem_bondSupp (G : TowerGeom (scaleUp ell k Lu)) {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hx : x ∈ G.Om0)
    (X : SuTwo) : sing (x, (0 : Fin 3)) X ∈ bondSupp G := by
  intro b hb
  by_contra hne
  apply hb
  have : b = (x, (0 : Fin 3)) := by
    by_contra h
    exact hne (sing_apply_ne _ _ h)
  rw [this]
  exact Or.inl hx

theorem Fth_pi_neg (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x) (ha : 0 ≤ a) (ha4 : a < 4)
    (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)), ⟪v, Fth sJ ell k Lu hell0 S a Lam Real.pi v⟫ < 0 := by
  have hRM : 3 ≤ R * M := by omega
  have h9 : 9 * ell ≤ R * M := by omega
  have hmem : sing (x, (0 : Fin 3)) X ∈ bondSupp (geomOf ell k S) := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  refine ⟨⟨sing (x, (0 : Fin 3)) X, hmem⟩, ?_⟩
  have hn : 0 < hsInner X X := by
    have h0 : 0 ≤ hsInner X X := real_inner_self_nonneg (x := X)
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm) hX
  show ⟪(⟨sing (x, (0 : Fin 3)) X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
    (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Ginv ⟨sing (x, (0 : Fin 3)) X, hmem⟩⟫ < 0
  rw [BaseDataS.inner_Ginv]
  have hDpi : ⟪(⟨sing (x, (0 : Fin 3)) X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Dpi ⟨sing (x, (0 : Fin 3)) X, hmem⟩⟫ = -4 * hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) (Uth (S.Om 0) Real.pi) a ⟨sing (x, (0 : Fin 3)) X, hmem⟩
    refine e.trans ?_
    have hW : Wop (geomOf ell k S) (Uth (S.Om 0) Real.pi) a (iE (geomOf ell k S) ⟨sing (x, (0 : Fin 3)) X, hmem⟩) = sing (x, (0 : Fin 3)) X :=
      Wop_sing hS hRM hbd _ a X
    rw [hW]
    exact hbd.delta_pi X
  have hT : (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).T ⟨sing (x, (0 : Fin 3)) X, hmem⟩ = 0 := by
    show (Tfull (geomOf ell k S) (Uth (S.Om 0) Real.pi)) (iE (geomOf ell k S) ⟨sing (x, (0 : Fin 3)) X, hmem⟩) = 0
    exact Tfull_sing_zero hS hRM hbd _ X
  have hM : ⟪(⟨sing (x, (0 : Fin 3)) X, hmem⟩ : ↥(bondSupp (Pth ell k Lu hell0 S a Lam Real.pi).G)),
      (dataS selAll sJ (Pth ell k Lu hell0 S a Lam Real.pi)).Mass ⟨sing (x, (0 : Fin 3)) X, hmem⟩⟫ ≤ a * hsInner X X := by
    have e := E0_Mass_inner (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi)) ⟨sing (x, (0 : Fin 3)) X, hmem⟩
    have e2 : ⟪(⟨sing (x, (0 : Fin 3)) X, hmem⟩ : ↥(bondSupp (geomOf ell k S))), ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
        (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi))).comp (iE (geomOf ell k S)))) ⟨sing (x, (0 : Fin 3)) X, hmem⟩⟫
        = ⟪sing (x, (0 : Fin 3)) X, MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) Real.pi)) (sing (x, (0 : Fin 3)) X)⟫ := by
      simp only [ContinuousLinearMap.comp_apply]
      rw [pE_inner_right]; rfl
    refine le_trans (le_of_eq e2) ?_
    exact Mass_sing_le hS hell h9 hbd _ a ha X
  rw [hDpi, hT]
  simp only [norm_zero]
  nlinarith


/-- **the in-class point with non-unit literal `Ginv`.** -/
theorem exists_nonunit_Ginv (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x) (ha : 0 ≤ a) (ha4 : a < 4) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi ∧
      ¬ IsUnit (dataS selAll sJ (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)).Ginv := by
  obtain ⟨v, hv⟩ := Fth_pi_neg sJ hell0 a Lam hS hell hroom hbd ha ha4 AdalyFormal.Balaban.CovariantOperators.suTwoWitness
    AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero
  obtain ⟨θ, h0, h1, hnu⟩ := exists_nonunit_path (fun t => Fth sJ ell k Lu hell0 S a Lam t)
    (Fth_cont sJ hell0 a Lam hS hell hroom) (fun t u v => Fth_symm sJ hell0 a Lam t u v)
    (Fth_zero_psd sJ hell0 a Lam ha) Real.pi Real.pi_pos v hv
  exact ⟨θ, h0, h1, hnu⟩

end

#print axioms exists_nonunit_Ginv

end AdalyFormal.D1Literal

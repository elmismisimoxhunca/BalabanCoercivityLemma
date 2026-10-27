import CvS3b

/-!
# CvS3c -- on the CvN6 tip instance the printed inequality does not depend on the tip link wherever every printed object exists
(lane cover_strong_20261016)

Instance: `tipP ell M R v a Λ` with `Λ = ncLam M R` (the tip instance of CvN6), `3 ≤ ell`, `ell ∣ M`, `9 ell + 1 ≤ R`,
`17 ell ≤ R M`, `a > 0`.
* `tip_genC_eq`: `C` (3.157) is the same for every `v` (it reads `U` only within `4 ell` of `Ω₁`); `tip_H0_eq`: so is `H₀`.
* **`tip_genForm_const`**: if `G⁻¹` and `Q G Q*` are invertible at `v` and at `v'`, then `genForm(C B̃)` takes the same value at
  `v` and `v'`, for every `B̃` (CvS2b `tip_genForm_eq` + CvS3a `inv_form_congr` + CvS3b `tip_Ginv_compress`).
* **`tip_InstIneq_const`**: if `WellDefG` holds at `v` and at `v'`, the printed inequality holds at `v` iff it holds at `v'` (every `γ₀`).
* **`tip_no_strong_failure`**: if `WellDefG` holds at `U ≡ 1` and the printed inequality holds there, then it holds at EVERY `v` at which
  `WellDefG` holds.  So the tip instance has a strong failure (all printed objects exist, inequality fails) only if it already has one at
  the constant configuration.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverStrong

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.StatementLaneR8 (LocHyp unit_row_emb bgTower_congr QlinStepL_congr_bg suCoordFInv_apply_congr
  Cop_congr_rows H0_congr_rows AgreeAt Ball)
open AdalyFormal.NoCover
open AdalyFormal.GeneralClass
open AdalyFormal.CoverNec (FarAgree QfullOf_congr_far rhoT_one)

/-! ## the level-0 coordinate projection of `𝔅` -/

/-- `π`: keep the level-0 coordinates of `z ∈ L²(𝔅)`, zero the others. -/
noncomputable def lvl0Proj {L : PeriodicLatticeExtent} (G : TowerGeom L) : FSp G →L[ℝ] FSp G :=
  diagW G (fun p => if (p.1 : ℕ) = 0 then 1 else 0)

theorem lvl0Proj_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (a b : FSp G) :
    ⟪lvl0Proj G a, b⟫ = ⟪a, lvl0Proj G b⟫ := diagW_symm G _ a b

theorem lvl0Proj_eq_zero_iff {L : PeriodicLatticeExtent} (G : TowerGeom L) (z : FSp G) :
    lvl0Proj G z = 0 ↔ Lvl0Zero G z := by
  constructor
  · intro h p hp
    have h1 : (WithLp.ofLp (lvl0Proj G z)) p = 0 := by rw [h]; rfl
    have h2 : (WithLp.ofLp (lvl0Proj G z)) p = (if (p.1 : ℕ) = 0 then (1 : ℝ) else 0) • (WithLp.ofLp z) p := rfl
    rw [h2, if_pos hp, one_smul] at h1
    exact h1
  · intro h
    refine PiLp.ext (fun p => ?_)
    simp only [lvl0Proj, diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, PiLp.zero_apply]
    split_ifs with hp
    · rw [h p hp, smul_zero]
    · rw [zero_smul]

section Tip
variable {ell M R : ℕ} (hell : 3 ≤ ell) (hell0 : 0 < ell) (hM : 0 < M) (hR : 9 * ell + 1 ≤ R)
  (hdvd : ell ∣ M) (hroom : 17 * ell ≤ R * M)
include hell hell0 hM hR hdvd hroom

theorem tip_locHyp : LocHyp ell M R 1 (gcS ell M R) (ncLam M R) :=
  ⟨gc_admissible hell0 hM, le_rfl, by omega, hroom, lambdaOK2_gc hell hdvd hM (by omega)⟩

theorem tip_unitBgU_agree (v : SU2c) (a : ℝ) {c : CoarseBond (ncLu M R) ell} (hc : CRowIn ell (ncLam M R) c) :
    AgreeAt (Ball c.1.1 (4 * (1 * ell))) (tipP ell M R hell0 hM v a (ncLam M R)).unitBgU
      (tipP ell M R hell0 hM 1 a (ncLam M R)).unitBgU := by
  intro z hz μ
  have hemb := unit_row_emb (tip_locHyp hell hell0 hM hR hdvd hroom) hc hz
  have hU1 : Ut ell M R hell0 hM 1 = fun _ => 1 := Ut_one ell M R hell0 hM
  have hF := tip_farAgree hell hell0 hM hR (r := 4 * ell) (by omega) v
  show bgTower (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v) 1 (embY ell 1 (ncLu M R) hell0 z, μ) =
    bgTower (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1) 1 (embY ell 1 (ncLu M R) hell0 z, μ)
  rw [hU1]
  refine bgTower_congr (geomOf ell 1 (gcS ell M R)) hell0 1 _ ?_ μ
  rw [show AdalyFormal.StatementLaneR8.rhoT (geomOf ell 1 (gcS ell M R)).ell 1 = 4 * ell from rhoT_one ell]
  exact hF _ hemb

theorem tip_Q1_rows (v : SU2c) (a : ℝ) (B : Bond (ncLu M R) → SuTwo) {c : CoarseBond (ncLu M R) ell}
    (hc : CRowIn ell (ncLam M R) c) :
    (tipP ell M R hell0 hM v a (ncLam M R)).Q1 B c = (tipP ell M R hell0 hM 1 a (ncLam M R)).Q1 B c := by
  have hrow := QlinStepL_congr_bg 1 ell one_pos (c.1.1, c.2) (tip_unitBgU_agree hell hell0 hM hR hdvd hroom v a hc)
    (AdalyFormal.IngredientFamilyR2.suCoordF B)
  show ((ell : ℝ)⁻¹) • (AdalyFormal.IngredientFamilyR2.suCoordFInv (AdalyFormal.IngredientFamilyR2.QlinStepL 1 ell
      (tipP ell M R hell0 hM v a (ncLam M R)).unitBgU (AdalyFormal.IngredientFamilyR2.suCoordF B))) (c.1.1, c.2)
    = ((ell : ℝ)⁻¹) • (AdalyFormal.IngredientFamilyR2.suCoordFInv (AdalyFormal.IngredientFamilyR2.QlinStepL 1 ell
      (tipP ell M R hell0 hM 1 a (ncLam M R)).unitBgU (AdalyFormal.IngredientFamilyR2.suCoordF B))) (c.1.1, c.2)
  rw [suCoordFInv_apply_congr hrow]

theorem tip_genC_eq (v : SU2c) (a : ℝ) :
    GenP.genC (tipP ell M R hell0 hM v a (ncLam M R)) = GenP.genC (tipP ell M R hell0 hM 1 a (ncLam M R)) :=
  Cop_congr_rows (ncLam M R) (fun B c hc => tip_Q1_rows hell hell0 hM hR hdvd hroom v a B hc)

theorem tip_H0_eq (v : SU2c) (a : ℝ) :
    H0 (ncLam M R) (tipP ell M R hell0 hM v a (ncLam M R)).Q1 = H0 (ncLam M R) (tipP ell M R hell0 hM 1 a (ncLam M R)).Q1 :=
  H0_congr_rows (ncLam M R) (fun B c hc => tip_Q1_rows hell hell0 hM hR hdvd hroom v a B hc)

theorem tip_dataQ_eq (v : SU2c) (a : ℝ) :
    (tipP ell M R hell0 hM v a (ncLam M R)).data.Q = (tipP ell M R hell0 hM 1 a (ncLam M R)).data.Q := by
  have h1 := QfullOf_congr_far hell0 (tip_farAgree hell hell0 hM hR (r := 9 * ell) le_rfl v)
  have h2 := QfullOf_congr_far hell0 (tip_farAgree hell hell0 hM hR (r := 9 * ell) le_rfl 1)
  show (QfullOf (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM v)).comp (iE _) =
    (QfullOf (geomOf ell 1 (gcS ell M R)) (Ut ell M R hell0 hM 1)).comp (iE _)
  rw [h1, h2]

/-- the first term of (3.156) at `y = τ*B`: equal at any two link values where `G⁻¹` and `Q G Q*` are invertible. -/
theorem tip_inv_form_eq {a : ℝ} (ha : 0 < a) (v v' : SU2c)
    (hG : IsUnit (tipP ell M R hell0 hM v a (ncLam M R)).data.Ginv)
    (hN : IsUnit (((tipP ell M R hell0 hM v a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v a (ncLam M R)).data.G).comp
      (tipP ell M R hell0 hM v a (ncLam M R)).data.Qs))
    (hG' : IsUnit (tipP ell M R hell0 hM v' a (ncLam M R)).data.Ginv)
    (hN' : IsUnit (((tipP ell M R hell0 hM v' a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v' a (ncLam M R)).data.G).comp
      (tipP ell M R hell0 hM v' a (ncLam M R)).data.Qs))
    (B : BondFnL2 (ncLu M R)) :
    ⟪ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v a (ncLam M R)).tau B,
      Ring.inverse (((tipP ell M R hell0 hM v a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v a (ncLam M R)).data.G).comp
        (tipP ell M R hell0 hM v a (ncLam M R)).data.Qs)
        (ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v a (ncLam M R)).tau B)⟫ =
    ⟪ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v' a (ncLam M R)).tau B,
      Ring.inverse (((tipP ell M R hell0 hM v' a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v' a (ncLam M R)).data.G).comp
        (tipP ell M R hell0 hM v' a (ncLam M R)).data.Qs)
        (ContinuousLinearMap.adjoint (tipP ell M R hell0 hM v' a (ncLam M R)).tau B)⟫ := by
  set P1 := tipP ell M R hell0 hM 1 a (ncLam M R) with hP1
  have hQv := tip_dataQ_eq hell hell0 hM hR hdvd hroom v a
  have hQv' := tip_dataQ_eq hell hell0 hM hR hdvd hroom v' a
  have hQsv : (tipP ell M R hell0 hM v a (ncLam M R)).data.Qs = ContinuousLinearMap.adjoint P1.data.Q := by
    rw [← hQv]; rfl
  have hQsv' : (tipP ell M R hell0 hM v' a (ncLam M R)).data.Qs = ContinuousLinearMap.adjoint P1.data.Q := by
    rw [← hQv']; rfl
  have htau : (tipP ell M R hell0 hM v a (ncLam M R)).tau = P1.tau := rfl
  have htau' : (tipP ell M R hell0 hM v' a (ncLam M R)).tau = P1.tau := rfl
  have hGd : (tipP ell M R hell0 hM v a (ncLam M R)).data.G = Ring.inverse (tipP ell M R hell0 hM v a (ncLam M R)).data.Ginv := rfl
  have hGd' : (tipP ell M R hell0 hM v' a (ncLam M R)).data.G = Ring.inverse (tipP ell M R hell0 hM v' a (ncLam M R)).data.Ginv := rfl
  rw [hQv, hQsv, hGd] at hN ⊢
  rw [hQv', hQsv', hGd'] at hN' ⊢
  rw [htau, htau']
  refine inv_form_congr P1.data.Q _ _ (lvl0Proj P1.G) (lvl0Proj_symm P1.G) hG hG' hN hN' ?_ _ ?_
  · intro x hx x' hx'
    have hz : ∀ (z : ↥(bondSupp P1.G)), lvl0Proj P1.G (P1.data.Q z) = 0 →
        ∀ b, b ∈ bondsLam (geomOf ell 1 (gcS ell M R)) 0 → (WithLp.ofLp (iE _ z)) b = 0 := by
      intro z hz0 b hb
      have h0 := (lvl0Proj_eq_zero_iff P1.G _).mp hz0 ⟨0, ⟨b, hb⟩⟩ rfl
      rwa [data_Q_lvl0 P1 z _ rfl] at h0
    rw [inner_sub_right,
      tip_Ginv_compress hell hell0 hM hR ha v' (ncLam M R) x x' (hz x hx) (hz x' hx'),
      tip_Ginv_compress hell hell0 hM hR ha v (ncLam M R) x x' (hz x hx) (hz x' hx'), sub_self]
  · exact (lvl0Proj_eq_zero_iff P1.G _).mpr (tau_adj_lvl0 P1 le_rfl B)

/-- **`genForm (C B̃)` is the same at any two link values where `G⁻¹` and `Q G Q*` are invertible.** -/
theorem tip_genForm_const {a : ℝ} (ha : 0 < a) (v v' : SU2c)
    (hG : IsUnit (tipP ell M R hell0 hM v a (ncLam M R)).data.Ginv)
    (hN : IsUnit (((tipP ell M R hell0 hM v a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v a (ncLam M R)).data.G).comp
      (tipP ell M R hell0 hM v a (ncLam M R)).data.Qs))
    (hG' : IsUnit (tipP ell M R hell0 hM v' a (ncLam M R)).data.Ginv)
    (hN' : IsUnit (((tipP ell M R hell0 hM v' a (ncLam M R)).data.Q.comp (tipP ell M R hell0 hM v' a (ncLam M R)).data.G).comp
      (tipP ell M R hell0 hM v' a (ncLam M R)).data.Qs))
    (Bt : Bond (ncLu M R) → SuTwo) :
    GenP.genForm (tipP ell M R hell0 hM v a (ncLam M R))
        (WithLp.toLp 2 (GenP.genC (tipP ell M R hell0 hM v a (ncLam M R)) Bt)) =
      GenP.genForm (tipP ell M R hell0 hM v' a (ncLam M R))
        (WithLp.toLp 2 (GenP.genC (tipP ell M R hell0 hM v' a (ncLam M R)) Bt)) := by
  rw [tip_genC_eq hell hell0 hM hR hdvd hroom v a, tip_genC_eq hell hell0 hM hR hdvd hroom v' a,
    tip_genForm_eq hell hell0 hM hR v a (ncLam M R), tip_genForm_eq hell hell0 hM hR v' a (ncLam M R),
    tip_inv_form_eq hell hell0 hM hR hdvd hroom ha v v' hG hN hG' hN']
  rfl

/-- **the printed inequality is the same statement at any two link values where every printed object exists.** -/
theorem tip_InstIneq_const {a : ℝ} (ha : 0 < a) (v v' : SU2c)
    (hW : GenP.WellDefG (tipP ell M R hell0 hM v a (ncLam M R)))
    (hW' : GenP.WellDefG (tipP ell M R hell0 hM v' a (ncLam M R))) (γ₀ : ℝ) :
    InstIneq ell 1 hell0 a (ncLu M R) γ₀ (gcS ell M R) (ncLam M R) (Ut ell M R hell0 hM v) ↔
      InstIneq ell 1 hell0 a (ncLu M R) γ₀ (gcS ell M R) (ncLam M R) (Ut ell M R hell0 hM v') := by
  have hF : ∀ Bt, GenP.genForm (tipP ell M R hell0 hM v a (ncLam M R))
        (WithLp.toLp 2 (GenP.genC (tipP ell M R hell0 hM v a (ncLam M R)) Bt)) =
      GenP.genForm (tipP ell M R hell0 hM v' a (ncLam M R))
        (WithLp.toLp 2 (GenP.genC (tipP ell M R hell0 hM v' a (ncLam M R)) Bt)) :=
    tip_genForm_const hell hell0 hM hR hdvd hroom ha v v' hW.2.2.1 hW.2.2.2 hW'.2.2.1 hW'.2.2.2
  constructor
  · intro h Bt h1 h2
    rw [← hF Bt]
    exact h Bt h1 h2
  · intro h Bt h1 h2
    rw [hF Bt]
    exact h Bt h1 h2

/-- **no strong failure on the tip instance unless at `U ≡ 1`**: if every printed object exists at `U ≡ 1` and the printed
inequality holds there, it holds at every link value where every printed object exists. -/
theorem tip_no_strong_failure {a : ℝ} (ha : 0 < a) (γ₀ : ℝ)
    (hW1 : GenP.WellDefG (tipP ell M R hell0 hM 1 a (ncLam M R)))
    (hI1 : InstIneq ell 1 hell0 a (ncLu M R) γ₀ (gcS ell M R) (ncLam M R) (fun _ => 1)) (v : SU2c)
    (hW : GenP.WellDefG (tipP ell M R hell0 hM v a (ncLam M R))) :
    InstIneq ell 1 hell0 a (ncLu M R) γ₀ (gcS ell M R) (ncLam M R) (Ut ell M R hell0 hM v) := by
  have hU1 : Ut ell M R hell0 hM 1 = fun _ => 1 := Ut_one ell M R hell0 hM
  have := (tip_InstIneq_const hell hell0 hM hR hdvd hroom ha v 1 hW hW1 γ₀).mpr
  rw [hU1] at this
  exact this hI1

end Tip

#print axioms lvl0Proj_symm
#print axioms lvl0Proj_eq_zero_iff
#print axioms tip_locHyp
#print axioms tip_unitBgU_agree
#print axioms tip_Q1_rows
#print axioms tip_genC_eq
#print axioms tip_H0_eq
#print axioms tip_dataQ_eq
#print axioms tip_inv_form_eq
#print axioms tip_genForm_const
#print axioms tip_InstIneq_const
#print axioms tip_no_strong_failure

end AdalyFormal.CoverStrong

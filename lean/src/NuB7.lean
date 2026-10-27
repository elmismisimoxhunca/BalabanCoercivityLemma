import NuB6

/-!
# NuB7 -- `monotone_perp`: `w ↦ <y, N(w)⁻¹ y>` is monotone on intervals of units, for `Ad_h`-fixed `y` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.StatementLaneG
open scoped RealInnerProductSpace

section
variable [CfData]
variable {ell M R : ℕ}
local notation "GG" => geomOf ell 2 (neS ell M R)

theorem monotone_perp (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a)
    {lo hi : ℝ} (hlo : -1 < lo) (hhi : hi ≤ 1)
    (hinj : ∀ y : FSp (geomOf ell 2 (neS ell M R)), (Pt ell M R (by omega) (neC0 ell M R) 0 a).data.Qs y = 0 → y = 0)
    (hunit : ∀ w ∈ Set.Icc lo hi, IsUnit (Pt ell M R (by omega) (neC0 ell M R) (tOf w) a).G1inv ∧
      IsUnit (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) (tOf w) a)))
    (y : FSp (geomOf ell 2 (neS ell M R))) (hy : TFc (geomOf ell 2 (neS ell M R)) y = y) :
    MonotoneOn (fun w => ⟪y, Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) (tOf w) a)) y⟫) (Set.Icc lo hi) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have h0 : |(0 : ℝ)| < Real.pi / 2 := by rw [abs_zero]; positivity
  -- the family
  let P : ℝ → IngrBParams := fun w => Pt ell M R hell (neC0 ell M R) (tOf w) a
  have hPt : ∀ w, -1 < w → |tOf w| < Real.pi / 2 := fun w hw => abs_tOf_lt hw
  have hU : ∀ w, CartanCfg (P w).U := fun w => stag0Cfg_cartan _ _
  -- equivariance of all ingredients
  have hEqv : ∀ w, BaseEqv (adEL (hGauge (P w).Lf) (P w).G) (adSL (hGauge (P w).Lf)) (adFL (hGauge (P w).Lf) (P w).G) (P w).data (P w).data :=
    fun w => baseEqv_hGauge (P w) (hU w)
  -- the pencil on the fixed space
  have hAs : ∀ w (x z : ↥(bondSupp GG)), ⟪(P w).G1inv x, z⟫ = ⟪x, (P w).G1inv z⟫ := fun w x z => (P w).G1inv_spec.symm x z
  have hAc : ∀ w (x : ↥(bondSupp GG)), (P w).G1inv (TEc GG x) = TEc GG ((P w).G1inv x) := by
    intro w x
    exact (hEqv w).G1inv (P w).G1inv_spec (P w).G1inv_spec x
  obtain ⟨H0, B, hH0s, hBs, hBpsd, hH0c, hBc, hAff⟩ := AdalyNcwdhTwo.Bridge.pencil_exists (TE := TEc GG) (TEc_sq GG)
    (fun x z => TEc_sym GG x z) (fun w => (P w).G1inv) hAs hAc (betaForm ell M R a)
    (fun x _ => bPl_nonneg _ _ _) (Set.Ioc (-1) 1) (by constructor <;> norm_num)
    (by
      intro w hw x x' hx hx'
      have h1 := G1inv_affine hell2 hE hdvd hM hR ha (hPt w hw.1) x' x hx' hx
      rw [cos_tOf hw.1.le hw.2] at h1
      have h2 : (P 1).G1inv = (Pt ell M R hell (neC0 ell M R) 0 a).G1inv := by
        show (Pt ell M R hell (neC0 ell M R) (tOf 1) a).G1inv = _
        rw [tOf_one]
      show ⟪x', (P w).G1inv x⟫ = ⟪x', (P 1).G1inv x⟫ + (w - 1) * betaForm ell M R a x' x
      rw [h2]; exact h1)
  have hw1 : ∀ w ∈ Set.Icc lo hi, -1 < w ∧ w ≤ 1 := fun w hw => ⟨lt_of_lt_of_le hlo hw.1, le_trans hw.2 hhi⟩
  have hQadj : ∀ w x y, ⟪(P w).data.Q x, y⟫ = ⟪x, (P w).data.Qs y⟫ := fun w => (P w).data.Q_adj
  have hQ : ∀ w ∈ Set.Icc lo hi, ∀ x : ↥(bondSupp GG), TEc GG x = x → (P w).data.Q x = (P 1).data.Q x := by
    intro w hw x hx
    have hxs : SigB (WithLp.ofLp (x : BondFnL2 (scaleUp ell 2 (neLu M R)))) := (TEc_fixed_iff GG x).mp hx
    exact Qfull_sig_indep hell2 hE hdvd hM hR (hPt w (hw1 w hw).1) (by rw [show tOf 1 = 0 from tOf_one]; exact h0)
      hxs
  have hP1 : ∀ w ∈ Set.Icc lo hi, ∀ y : FSp GG, TFc GG y = y → (P w).data.Qs y = (P 1).data.Qs y := by
    intro w hw y hy
    exact AdalyNcwdhTwo.Bridge.Qs_fixed_of_Q (TE := TEc GG) (TF := TFc GG) (TEc_sq GG) (TFc_sq GG) (fun x z => TFc_sym GG x z) (hQadj w) (hQadj 1)
      (fun x => (hEqv w).Q x) (fun x => (hEqv 1).Q x) (fun x hx => hQ w hw x hx) hy
  have hmain := AdalyNcwdhTwo.Bridge.monotone_bridge (TE := TEc GG) (TF := TFc GG) (TEc_sq GG) (fun x z => TEc_sym GG x z) (TFc_sq GG)
    hH0s hBs hBpsd hH0c hBc (Q0 := (P 1).data.Q) (Q0s := (P 1).data.Qs) (hQadj 1)
    (fun x => (hEqv 1).Q x) (fun y => (hEqv 1).Qs y)
    (by
      have key : ∀ s : ℝ, s = 0 → ∀ y : FSp GG, (Pt ell M R hell (neC0 ell M R) s a).data.Qs y = 0 → y = 0 := by
        rintro s rfl; exact hinj
      exact key (tOf 1) tOf_one)
    (fun w => (P w).G1inv) (fun w => (P w).data.Q) (fun w => (P w).data.Qs) (lo := lo) (hi := hi)
    (fun w hw x => hAc w x)
    (fun w hw x hx => hAff w (hw1 w hw |> fun h => ⟨h.1, h.2⟩) x hx)
    hQ hP1 (fun w hw x => (hEqv w).Q x) (fun w hw y => (hEqv w).Qs y)
    (fun w hw => by
      obtain ⟨h1, h2⟩ := hunit w hw
      refine ⟨h1, ?_⟩
      have := Nmat_eq (P w)
      rw [← this]; exact h2) y hy
  have hfun : (fun w => ⟪y, Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) (tOf w) a)) y⟫) =
      (fun w => ⟪y, Ring.inverse ((P w).data.Q.comp ((Ring.inverse (P w).G1inv).comp (P w).data.Qs)) y⟫) :=
    funext fun w => by rw [Nmat_eq]
  rw [hfun]; exact hmain

end

end AdalyFormal.NcwdhTwo

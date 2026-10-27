import GdSG2

/-!
# GdSG3 -- `InstIneqSG2` and `InstIneqSG` on the boundary-twist family.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy bondEnergy_nonneg)

theorem bondEnergy_eq_zero {L : PeriodicLatticeExtent} {Bt : Bond L → SuTwo} (h : bondEnergy Bt = 0) : Bt = 0 := by
  unfold bondEnergy at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖Bt b‖)).mp h
  funext b
  have hb := this b (Finset.mem_univ b)
  have : ‖Bt b‖ = 0 := by nlinarith [norm_nonneg (Bt b)]
  exact norm_eq_zero.mp this

/-- on the twist family `genFormS 0 = 0`. -/
theorem genFormS_theta_zero (sD sJ : PlaqSel) (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell : 0 < P.ell)
    (h3 : 3 ≤ R * M) (θ : ℝ) (hU : P.U = Uth (P.S.Om 0) θ) (hk : 1 ≤ P.k) :
    GenS.genFormS sD sJ P (0 : BondFnL2 P.Lu) = 0 := by
  rw [genFormS_theta sD sJ P hS hell h3 θ hU hk 0]
  simp [GenS.firstTermS]

/-- **the full-guard literal inequality on the boundary-twist family**, from the localised inequality at the flat point. -/
theorem InstIneqSG2_twist (sJ : PlaqSel) {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) (hk : 1 ≤ k)
    {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK2 ell M R k S Lam) {a γ₀ : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ₀) (θ : ℝ)
    (hloc : InstIneqS selIn selIn ell k hell0 a Lu γ₀ S Lam (Uth (S.Om 0) 0)) :
    InstIneqSG2 selAll sJ ell k hell0 a Lu γ₀ S Lam (Uth (S.Om 0) θ) := by
  intro hWD Bt h1 h2
  have h3 : 3 ≤ R * M := by omega
  have hC : GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) = GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam) :=
    genC_congr (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam) (M := M) (R := R) ⟨hS, hk, hell, hroom, hL⟩ (Uth (S.Om 0) 0)
      (fun e he => by
        show Uth (S.Om 0) θ e = Uth (S.Om 0) 0 e
        rw [Uth_one_of_base _ θ e he.1, Uth_one_of_base _ 0 e he.1])
  rw [← hC]
  have hlocB := hloc Bt h1 h2
  by_cases hu : IsUnit (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv ∧
      IsUnit (GenS.NmatS selIn selIn (Pth ell k Lu hell0 S a Lam 0))
  · have hft := firstTerm_twist_ge sJ hell0 hS hk hell hroom ha Lam θ hWD hu
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt))
    have hf1 := genFormS_theta selAll sJ (Pth ell k Lu hell0 S a Lam θ) hS hell0 h3 θ rfl hk
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt))
    have hf2 := genFormS_theta selIn selIn (Pth ell k Lu hell0 S a Lam 0) hS hell0 h3 0 rfl hk
      (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt))
    -- restate everything on the nose
    have hf1' : GenS.genFormS selAll sJ (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) =
        GenS.firstTermS selAll sJ (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) -
        a * ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu),
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu)⟫ := hf1
    have hf2' : GenS.genFormS selIn selIn (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) =
        GenS.firstTermS selIn selIn (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) -
        a * ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu),
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu)⟫ := hf2
    have hft' : GenS.firstTermS selIn selIn (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) ≤
        GenS.firstTermS selAll sJ (gparams ell k Lu hell0 S (Uth (S.Om 0) θ) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) := hft
    have hlocB' : γ₀ * bondEnergy Bt ≤ GenS.genFormS selIn selIn (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) := hlocB
    rw [hf1']
    rw [hf2'] at hlocB'
    linarith
  · have hcol : GenS.genFormS selIn selIn (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt)) =
        -a * ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu),
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu)⟫ := by
      by_cases hM : IsUnit (dataS selIn selIn (Pth ell k Lu hell0 S a Lam 0)).Ginv
      · exact genFormS_collapse_N selIn selIn (Pth ell k Lu hell0 S a Lam 0) (fun hN => hu ⟨hM, hN⟩) _
      · exact genFormS_collapse selIn selIn (Pth ell k Lu hell0 S a Lam 0) hM _
    rw [hcol] at hlocB
    have hB0 : (0 : ℝ) ≤ ⟪(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu),
          (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) Bt) : BondFnL2 Lu)⟫ := real_inner_self_nonneg
    have hE : bondEnergy Bt ≤ 0 := by
      by_contra hpos
      push Not at hpos
      nlinarith [mul_pos hγ hpos, mul_nonneg ha hB0]
    have hBt : Bt = 0 := bondEnergy_eq_zero (le_antisymm hE (bondEnergy_nonneg Bt))
    subst hBt
    have hE0 : bondEnergy (0 : Bond Lu → SuTwo) = 0 := by
      unfold bondEnergy
      exact Finset.sum_eq_zero (fun b _ => by simp)
    rw [hE0, mul_zero]
    have hB0' : (WithLp.toLp 2 ((GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam)) 0) :
        BondFnL2 (Pth ell k Lu hell0 S a Lam θ).Lu) = 0 := by
      rw [map_zero]; rfl
    have hz : GenS.genFormS selAll sJ (Pth ell k Lu hell0 S a Lam θ)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell0 S (Uth (S.Om 0) 0) a Lam) 0)) = 0 :=
      (congrArg (GenS.genFormS selAll sJ (Pth ell k Lu hell0 S a Lam θ)) hB0').trans
        (genFormS_theta_zero selAll sJ (Pth ell k Lu hell0 S a Lam θ) hS hell0 h3 θ rfl hk)
    exact hz.ge

#print axioms bondEnergy_eq_zero
#print axioms genFormS_theta_zero
#print axioms InstIneqSG2_twist

end AdalyFormal.D1Guarded

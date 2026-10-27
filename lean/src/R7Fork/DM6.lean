import R7Fork.DM5
import R7Fork.ZT5D

/-!
# DM6 -- (a) NECESSITY: `InstIneq` at a flat tower forces `IsUnit N` (otherwise `Ring.inverse N = 0` and `genForm B = -a ||B||^2`);
(b) MUST-FIRE for the class: `B~ = iota_D w` (a field on the dropped bonds, violating the dropped-bond clause of `Lambda~`) has `C B~ = 0`,
 hence `genForm(C B~) = 0 < gamma0 ||B~||^2`: the clause `B~ = 0 on dropped bonds` is load-bearing at EVERY tower/`Lambda` with `Lambda' != empty`;
(c) the hypotheses of `closed_point_proper_cond` are SATISFIED (all but the two units) at the proper multi-stratum tower `TT` of `ZT5D`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.IngredientFamily (q1SU2)

/-- if `N = Q G1 Q*` is not a unit, `Ring.inverse N = 0` and the form is `-a ||B||^2` (flat `J = 0`) -/
theorem genForm_not_unit (P : IngrBParams) (hJ : P.Jf = 0) (hN : ¬ IsUnit (GenP.Nmat P)) (B : BondFnL2 P.Lu) :
    GenP.genForm P B = - P.a * ‖B‖ ^ 2 := by
  unfold GenP.genForm GenP.firstTerm
  rw [Ring.inverse_non_unit _ hN, hJ, inner_zero_right, mul_zero, sub_zero]
  simp [real_inner_self_eq_norm_sq]

/-- (a) necessity of `IsUnit N`: a nonzero class element and the inequality force invertibility -/
theorem unit_N_of_instIneq {ell k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (a γ₀ : ℝ) (ha : 0 < a)
    (hγ : 0 < γ₀) (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (hI : InstIneq ell k hell a Lu γ₀ S Lam flatCfg)
    (hne : ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) :
    IsUnit (GenP.Nmat (gparams ell k Lu hell S flatCfg a Lam)) := by
  by_contra hN
  obtain ⟨Bt, h1, h2, h3⟩ := hne
  have h := hI Bt h1 h2
  rw [genForm_not_unit _ (Jf_flat _ rfl) hN] at h
  have : 0 ≤ ‖(WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S flatCfg a Lam) Bt) :
      BondFnL2 (gparams ell k Lu hell S flatCfg a Lam).Lu)‖ ^ 2 := sq_nonneg _
  have h4 : 0 < γ₀ * bondEnergy Bt := mul_pos hγ h3
  nlinarith [mul_nonneg ha.le this]

theorem genForm_zero (P : IngrBParams) : GenP.genForm P (0 : BondFnL2 P.Lu) = 0 := by
  have hD : P.D2in (0 : BondFnL2 P.Lu) = 0 := by
    have := P.D2in_quad 0 (0 : BondFnL2 P.Lu)
    simpa using this
  unfold GenP.genForm GenP.firstTerm
  rw [hD]
  simp

theorem Cop_iotaD {L : PeriodicLatticeExtent} {ell : ℕ} (Lam : Set (PeriodicLatticeSite L))
    (Q : (Bond L → SuTwo) →ₗ[ℝ] (AdalyFormal.Balaban.LatticeOperators.CoarseBond L ell → SuTwo))
    (hb : Function.Bijective (H0 Lam Q)) (w : Dset L ell Lam → SuTwo) :
    Cop Lam Q (iotaD ell Lam w) = 0 := by
  have h1 : rhoD ell Lam (Q (iotaD ell Lam w)) = H0 Lam Q w := rfl
  have h2 : H0inv Lam Q (H0 Lam Q w) = w := by
    unfold H0inv
    rw [dif_pos hb]
    exact (LinearEquiv.ofBijective (H0 Lam Q) hb).symm_apply_apply w
  have h3 : hLift Lam Q (Q (iotaD ell Lam w)) = iotaD ell Lam w := by
    show iotaD ell Lam (H0inv Lam Q (rhoD ell Lam (Q (iotaD ell Lam w)))) = _
    rw [h1, h2]
  show iotaD ell Lam w - hLift Lam Q (Q (iotaD ell Lam w)) = 0
  rw [h3, sub_self]

/-- (b) the dropped-bond clause of `Lambda~` is load-bearing: a field on the dropped bonds has `genForm (C ·) = 0`.
Statement: for any flat parameter set with `H0` bijective, `genForm P (C (iota_D w)) = 0` for EVERY `w`. -/
theorem genForm_C_iotaD (P : IngrBParams) (hb : Function.Bijective (H0 P.Lam P.Q1))
    (w : Dset P.Lu P.ell P.Lam → SuTwo) :
    GenP.genForm P (WithLp.toLp 2 (GenP.genC P (iotaD P.ell P.Lam w))) = 0 := by
  have : GenP.genC P (iotaD P.ell P.Lam w) = 0 := Cop_iotaD P.Lam P.Q1 hb w
  rw [this]
  exact genForm_zero P

/-- the dropped bonds are pairwise distinct -/
theorem iotaD_energy_pos {ell : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent} (hdvd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (w : Dset Lu ell Lam → SuTwo) (c : Dset Lu ell Lam) (hc : w c ≠ 0) :
    0 < bondEnergy (iotaD ell Lam w) := by
  have hinj := AdalyFormal.Balaban.FullReparamC.droppedBondLast_injective (L := Lu) hell hdvd
  have h1 := iotaD_apply_dropped Lam hinj w c
  unfold bondEnergy
  have hle : ‖iotaD ell Lam w (droppedBondLast ell c.1)‖ ^ 2 ≤ ∑ b : Bond Lu, ‖iotaD ell Lam w b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Bond Lu => ‖iotaD ell Lam w b‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ _)
  rw [h1] at hle
  have : 0 < ‖w c‖ ^ 2 := by positivity
  linarith

#print axioms genForm_not_unit
#print axioms unit_N_of_instIneq
#print axioms genForm_C_iotaD
#print axioms iotaD_energy_pos

end AdalyFormal.DirichletMono

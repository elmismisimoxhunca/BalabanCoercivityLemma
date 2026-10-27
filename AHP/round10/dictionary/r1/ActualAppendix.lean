/-! Actual round-9 named operators. No GoalNeg2 closure is claimed. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Actual
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round6.Guarded.ClosedFormR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The finite-curvature correction commutes, not only its quadratic form. -/
theorem bulkD_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) (u : TwistSpace q R) :
    bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (bulkD q R f ε u) :=
  comm_of_quad _ _ ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
    (dataS_laws selIn selIn _)).1 (bulkD_rot q R α f ε) u

/-- Unconditional equivariance of the actual corrDeriv, at every q,R,profile.
At admissible q,R it is a genuine derivative by round 9; no new premise. -/
theorem corrDeriv_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (corrDeriv q R f u) :=
  deriv_comm (fun ε : ℝ => bulkD q R f ε) _ (fun ε => bulkD_U1 q R f ε α) 0 u

/-- This is the form identity to combine with round 9's
corrDeriv_dilMask_form for the explicit H0-C2-J' pairing. -/
theorem corrDeriv_U1_form (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    ⟪adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u,
      corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)⟫ =
      ⟪u, corrDeriv q R f u⟫ := by
  rw [corrDeriv_U1, LinearIsometryEquiv.inner_map_map]

theorem corrDeriv_no_charge_cross (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u v : TwistSpace q R)
    (hu : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u = u)
    (hv : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) v = -v) :
    ⟪u, corrDeriv q R f v⟫ = 0 :=
  opposite_charge_cross_zero _ _ (corrDeriv_U1 q R f (Real.pi / 2)) hu hv

/-- The actual localized B at every curvature, not a formal model matrix. -/
theorem bulkB_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) (u : TwistSpace q R) :
    (dataS selIn selIn (bulkP q R f ε)).Ginv (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((dataS selIn selIn (bulkP q R f ε)).Ginv u) :=
  localized_comm (by norm_num : 0 < 2) (dilTower q R) (bulkU q R f ε) 1
    (dilLam q R) (rotGauge α) (rot_bulkU q R α f ε) u

/-- The vacuum kernel splits orthogonally into neutral and charged parts.
This says nothing about either part's dimension or whether it vanishes. -/
theorem vacuum_kernel_charge_split (q R : ℕ) (t : ℝ) (u : TwistSpace q R)
    (hu : vacA q R (uthPath q R) 1 t u = 0) :
    ∃ up um : TwistSpace q R, u = up + um ∧
      adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) up = up ∧
      adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) um = -um ∧
      ⟪up, um⟫ = 0 ∧ vacA q R (uthPath q R) 1 t up = 0 ∧ vacA q R (uthPath q R) 1 t um = 0 :=
  involution_kernel_split _ _ (half_carrier_twice _) (vacA_rot q R (Real.pi / 2) t) hu

/-- Concrete two-site action: equivariance of the actual all-plaquette
UNDRESSED Hessian. Translation of W,Q,T remains a separate obligation. -/
theorem twist_deltaK_twoSite {q : ℕ} (hq : 0 < q) (R : ℕ) (ε t : ℝ)
    (μ : Fin 3) (hμ : μ ≠ 0) (u : BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    AdalyFormal.StatementLaneR6.deltaKLocCLM (twistU q R ε t) Set.univ
      (bondPullback (twoSite q R μ) u) =
    bondPullback (twoSite q R μ)
      (AdalyFormal.StatementLaneR6.deltaKLocCLM (twistU q R ε t) Set.univ u) := by
  have hU : Translation.cfgPullback (twoSite q R μ) (twistU q R ε t) = twistU q R ε t := by
    funext e
    exact twistU_twoSite hq R ε t μ hμ e
  exact Translation.deltaK_all_comm (twoSite q R μ) (twistU q R ε t) hU u

#print axioms bulkD_U1
#print axioms corrDeriv_U1
#print axioms corrDeriv_U1_form
#print axioms corrDeriv_no_charge_cross
#print axioms bulkB_U1
#print axioms vacuum_kernel_charge_split
#print axioms twist_deltaK_twoSite
end AdalyFormal.Round10.Dictionary.Actual

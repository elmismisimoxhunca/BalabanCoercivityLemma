import DrEquiv
import ZXR2Flat6
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-! Verbatim operative declarations from D1Lit.lean:29-101. -/
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)

def selIn : PlaqSel := fun _ G => plaqIn G.Om0

def selAll : PlaqSel := fun _ _ => Set.univ

section Selectors
variable (sD sJ : PlaqSel)

noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)

noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))

theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _

section Ops
variable (P : IngrBParams)

noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))

noncomputable def dataS : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) }

theorem dataS_laws : (dataS sD sJ P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _



end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin


namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin

open Classical
def dilLu (q R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * (R * q) + 8 * q - 1 else 4 * q - 1

def dilTower (q R : ℕ) : Tower (scaleUp 2 1 (dilLu q R)) where
  Om j := if j = 0 then {x | 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q}
    else if j = 1 then {x | 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q}
    else ∅

def dilLam (q R : ℕ) : Set (PeriodicLatticeSite (dilLu q R)) :=
  {x | 3 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 3 * (R * q) + 6 * q}

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

end AdalyFormal.Round4.Guarded.RefuteR1

#print axioms AdalyFormal.Round4.Guarded.RefuteR1.dilLu

#print axioms AdalyFormal.Round4.Guarded.RefuteR1.dilTower

#print axioms AdalyFormal.Round4.Guarded.RefuteR1.dilLam

#print axioms AdalyFormal.Round4.Guarded.RefuteR1.dilPattern

#print axioms AdalyFormal.Round4.Guarded.RefuteR1.dilU


namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

open Classical
noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)

end AdalyFormal.Round5.Guarded.IVTR2

#print axioms AdalyFormal.Round5.Guarded.IVTR2.maskedU


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2

open Classical
noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

end AdalyFormal.Round9.Guarded.Qualitative

#print axioms AdalyFormal.Round9.Guarded.Qualitative.dilMask


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
theorem Ug_coe_uMat (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

noncomputable def bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (fun _ => 1)

noncomputable def bulkP (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)

noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α

theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem uθ_conj (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s * (AdalyFormal.D1Literal.uθ α)⁻¹ =
      AdalyFormal.D1Literal.uθ s := by
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem Ug_eq_uθ (s : ℝ) : Ug s = AdalyFormal.D1Literal.uθ s :=
  Subtype.ext (Ug_coe_uMat s)

theorem rot_maskedU (q R : ℕ) (α : ℝ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform (rotGauge α) (maskedU q R g V) =
      maskedU q R g (periodicGaugeTransform (rotGauge α) V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, rotGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, rotGauge, Ug_eq_uθ]
    exact uθ_conj α (g e)

theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem rot_bulkU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform (rotGauge α) (bulkU q R f ε) = bulkU q R f ε := by
  unfold bulkU
  rw [rot_maskedU, rot_trivial]

end AdalyFormal.Round9.Guarded.QualitativeR2

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.Ug_coe_uMat

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.bulkU

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.bulkP

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.uθ_comm

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.uθ_conj

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.Ug_eq_uθ

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.rot_maskedU

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.rot_trivial

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2.rot_bulkU


namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2

open Classical
theorem bulkU_dilMask (q R : ℕ) (ε : ℝ) :
    QualitativeR2.bulkU q R (dilMask q R) ε = dilU q R ε 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, dilU, dilMask]
  split_ifs <;> first | rfl | simp

end AdalyFormal.Round9.Guarded.QualitativeR2Joint

#print axioms AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkU_dilMask


namespace AdalyFormal.Round9.Guarded.AnalyticR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

end AdalyFormal.Round9.Guarded.AnalyticR1

#print axioms AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace


namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1

open Classical
noncomputable def dataFam (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ℝ → BaseDataS ↥(bondSupp (geomOf ell k S)) (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  fun ε => dataS sD sJ (gparams ell k Lu hell S (V ε) a Lam)

noncomputable abbrev dilV (q R : ℕ) : ℝ → Cfg (scaleUp 2 1 (dilLu q R)) := fun ε => dilU q R ε 1

noncomputable abbrev flatData (q R : ℕ) :=
  dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R))

noncomputable def vacCoupling (q R : ℕ) (J' : TwistSpace q R) (v : TwistSpace q R) : ℝ :=
  2 * ⟪(flatData q R).H (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))), J'⟫

def IsSourceDerivative (q R : ℕ) (J' : TwistSpace q R) : Prop :=
  Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
    (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')

end AdalyFormal.Round9.Guarded.AnalyticR2

#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dataFam

#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dilV

#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.flatData

#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling

#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.IsSourceDerivative


namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.D1Literal

open Classical
theorem half_rotation_matrix : (uθ (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I, 0; 0, -Complex.I] := by
  change uMat (Real.pi / 2) = _
  simp only [uMat, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [show -((Real.pi : ℂ) / 2 * Complex.I) = -Real.pi / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

end AdalyFormal.Round10.Dictionary

#print axioms AdalyFormal.Round10.Dictionary.half_rotation_matrix

/-! Exact scalar stencil for the frozen localized source of a diagonal phase field. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.PhaseSource
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily
open AdalyFormal.D1Literal (uθ uMat)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}

theorem phase_zero : uθ 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uθ, uMat]

theorem phase_mul (a b : ℝ) : uθ a * uθ b = uθ (a + b) := by
  apply Subtype.ext
  show uMat a * uMat b = uMat (a + b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, add_mul, Complex.exp_add]
  all_goals ring

theorem phase_inv (a : ℝ) : (uθ a)⁻¹ = uθ (-a) := by
  apply mul_left_cancel (a := uθ a)
  rw [mul_inv_cancel, phase_mul, add_neg_cancel, phase_zero]

def phase (f : Bond L → ℝ) : Cfg L := fun b => uθ (f b)

def circulation (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  f (p.1, p.2.1.1) + f (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
    f (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - f (p.1, p.2.1.2)

theorem holonomy_phase (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    holonomyElem (phase f) p = uθ (circulation f p) := by
  simp [holonomyElem, periodicPlaquetteHolonomy, phase, phase_inv, phase_mul, circulation,
    sub_eq_add_neg]

def hermDiag (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(r : ℂ), 0; 0, -(r : ℂ)]

theorem hermDiag_zero : hermDiag 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag]

theorem im_phase (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    imHolonomy (phase f) p = hermDiag (Real.sin (circulation f p)) := by
  rw [imHolonomy, holonomyElemInv, holonomy_phase, phase_inv]
  change (1 / (2 * Complex.I) : ℂ) • (uMat (circulation f p) - uMat (-circulation f p)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermDiag, uMat, Matrix.smul_apply, ← neg_mul, Complex.exp_mul_I]
  all_goals ring_nf; simp [Complex.I_sq]

theorem hermDiag_trace (r : ℝ) : Matrix.trace (hermDiag r) = 0 := by
  simp [hermDiag, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem hermDiag_neg (r : ℝ) : -hermDiag r = hermDiag (-r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag]

theorem hermDiag_sub (r s : ℝ) : hermDiag r - hermDiag s = hermDiag (r - s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag, sub_eq_add_neg, add_comm]

theorem conj_phase_hermDiag (t r : ℝ) : conjByAmbient (uθ t)⁻¹ (hermDiag r) = hermDiag r := by
  rw [phase_inv]
  simp only [conjByAmbient_apply]
  change uMat (-t) * hermDiag r * (uMat (-t))ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, hermDiag, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, ← Complex.exp_conj, Complex.exp_neg]
  all_goals field_simp

/-- Antisymmetric extension, with exactly the localized plaquette selector. -/
def oriented (P : Set (PeriodicLatticePlaquette L)) (g : PeriodicLatticePlaquette L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) : ℝ := by
  classical
  exact if h : ν < μ then (if (x, ⟨(ν, μ), h⟩) ∈ P then g (x, ⟨(ν, μ), h⟩) else 0)
    else if h' : μ < ν then (if (x, ⟨(μ, ν), h'⟩) ∈ P then -g (x, ⟨(μ, ν), h'⟩) else 0)
    else 0

def scalarDiv (g : Fin 3 → Fin 3 → PeriodicLatticeSite L → ℝ) (b : Bond L) : ℝ :=
  ∑ ν : Fin 3, if ν = b.2 then 0 else g ν b.2 (periodicLatticeShiftBack b.1 ν) - g ν b.2 b.1

def sourceScalar (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) : ℝ :=
  scalarDiv (oriented P (fun p => Real.sin (circulation f p))) b

def linearSourceScalar (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) : ℝ :=
  scalarDiv (oriented P (circulation f)) b

theorem FnuMuLoc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) :
    FnuMuLoc P (phase f) ν μ x = hermDiag (oriented P (fun p => Real.sin (circulation f p)) ν μ x) := by
  classical
  have hh (p : PeriodicLatticePlaquette L) : piProj (imHolonomy (phase f) p) =
      hermDiag (Real.sin (circulation f p)) := by
    rw [im_phase, piProj_eq_self_of_trace_zero (hermDiag_trace _)]
  unfold FnuMuLoc oriented
  split_ifs <;> simp only [hh, hermDiag_neg, hermDiag_zero]

theorem DstarDir_phase (f : Bond L → ℝ) (ν : Fin 3) (g : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) :
    DstarDir (phase f) ν (fun y => hermDiag (g y)) x =
      hermDiag (g (periodicLatticeShiftBack x ν) - g x) := by
  unfold DstarDir phase
  rw [conj_phase_hermDiag, hermDiag_sub]

theorem hermDiag_sum {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    hermDiag (∑ i, g i) = ∑ i, hermDiag (g i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag, Matrix.sum_apply]

theorem JfieldLoc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (b : Bond L) : JfieldLoc P (phase f) b.1 b.2 = hermDiag (sourceScalar P f b) := by
  unfold JfieldLoc sourceScalar scalarDiv
  simp_rw [FnuMuLoc_phase, DstarDir_phase]
  rw [hermDiag_sum]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs <;> simp [hermDiag_zero]

/-- The frozen source has the positive sign and no missing factor at mesh one. -/
theorem JSU2Loc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) :
    -(JSU2Loc 1 P (phase f) b) = sourceScalar P f b • pauliE3 := by
  apply Subtype.ext
  change -(((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (phase f) b.1 b.2) = _
  rw [JfieldLoc_phase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermDiag, pauliE3, suTwoWitness, suTwoWitnessVal, mul_comm]

theorem circulation_smul (f : Bond L → ℝ) (t : ℝ) (p : PeriodicLatticePlaquette L) :
    circulation (fun b => t * f b) p = t * circulation f p := by
  unfold circulation
  ring

theorem oriented_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ => oriented P (fun p => Real.sin (circulation (fun b => t * f b) p)) ν μ x)
      (oriented P (circulation f) ν μ x) 0 := by
  classical
  have hs (p : PeriodicLatticePlaquette L) :
      HasDerivAt (fun t : ℝ => Real.sin (circulation (fun b => t * f b) p)) (circulation f p) 0 := by
    simp_rw [circulation_smul]
    convert (((hasDerivAt_id (0 : ℝ)).mul_const (circulation f p)).sin) using 1 <;> simp
  unfold oriented
  split_ifs
  · exact hs _
  · exact hasDerivAt_const _ _
  · exact (hs _).neg
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _

theorem sourceScalar_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) :
    HasDerivAt (fun t : ℝ => sourceScalar P (fun b => t * f b) b) (linearSourceScalar P f b) 0 := by
  classical
  unfold sourceScalar linearSourceScalar scalarDiv
  apply HasDerivAt.fun_sum
  intro ν _
  by_cases h : ν = b.2
  · simp only [h, if_true]
    exact hasDerivAt_const _ _
  · simp only [h, if_false]
    exact (oriented_hasDerivAt P f ν b.2 _).sub (oriented_hasDerivAt P f ν b.2 _)

/-- Actual full-lattice linearized source, before projection to the touching carrier. -/
def sourceLinear (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => linearSourceScalar P f b • pauliE3)

theorem sourceField_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => t * f b)) b)) : BondFnL2 L))
      (sourceLinear P f) 0 := by
  simp_rw [JSU2Loc_phase]
  have hp : HasDerivAt (fun t : ℝ => fun b : Bond L => sourceScalar P (fun b => t * f b) b • pauliE3)
      (fun b : Bond L => linearSourceScalar P f b • pauliE3) 0 :=
    hasDerivAt_pi.mpr (fun b => (sourceScalar_hasDerivAt P f b).smul_const pauliE3)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Bond L => SuTwo)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hp

theorem sourceField_zero (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => (0 : ℝ) * f b)) b)) : BondFnL2 L) = 0 := by
  have hu : phase (fun b => (0 : ℝ) * f b) = (fun _ => 1) := by
    funext b
    simp only [phase, zero_mul, phase_zero]
  rw [hu]
  apply PiLp.ext
  intro b
  exact neg_eq_zero.mpr (JSU2Loc_trivial 1 P b)

/-- Abstract helper avoids the two concrete AddCommGroup instance paths. -/
theorem tendsto_div_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (h0 : f 0 = 0) (hd : HasDerivAt f v 0) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ • f t) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
  have ht := hd.tendsto_slope_zero
  simpa only [zero_add, h0, sub_zero] using ht

theorem sourceField_tendsto (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ •
      (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => t * f b)) b)) : BondFnL2 L))
      (nhdsWithin 0 {0}ᶜ) (nhds (sourceLinear P f)) :=
  tendsto_div_of_hasDerivAt_zero _ _ (sourceField_zero P f) (sourceField_hasDerivAt P f)

#print axioms sourceField_zero
#print axioms tendsto_div_of_hasDerivAt_zero
#print axioms sourceField_tendsto
#print axioms oriented
#print axioms scalarDiv
#print axioms sourceScalar
#print axioms linearSourceScalar
#print axioms FnuMuLoc_phase
#print axioms DstarDir_phase
#print axioms hermDiag_sum
#print axioms JfieldLoc_phase
#print axioms JSU2Loc_phase
#print axioms circulation_smul
#print axioms oriented_hasDerivAt
#print axioms sourceScalar_hasDerivAt
#print axioms sourceLinear
#print axioms sourceField_hasDerivAt
#print axioms phase_zero
#print axioms phase_mul
#print axioms phase_inv
#print axioms phase
#print axioms circulation
#print axioms holonomy_phase
#print axioms hermDiag
#print axioms hermDiag_zero
#print axioms im_phase
#print axioms hermDiag_trace
#print axioms hermDiag_neg
#print axioms hermDiag_sub
#print axioms conj_phase_hermDiag
end AdalyFormal.Round10.Dictionary.PhaseSource

/-! Inverse-free certificates for the actual frozen constrained source multiplier.
The hypotheses about the two units are the flat-point facts supplied by round 9.
The certificate identities themselves still have to be checked on a physical lift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.KKT
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The full constraint matrix, not a boundary compression. -/
def N (D : BaseDataS E S F) : F →L[ℝ] F := (D.Q.comp D.G).comp D.Qs

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [FiniteDimensional ℝ F] in
theorem Q_H (D : BaseDataS E S F) (hN : IsUnit (N D)) (z : F) : D.Q (D.H z) = z := by
  have h := congrArg (fun A : F →L[ℝ] F => A z) (Ring.mul_inverse_cancel (N D) hN)
  exact h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ S] [FiniteDimensional ℝ F] in
theorem Ginv_H (D : BaseDataS E S F) (hB : IsUnit D.Ginv) (z : F) :
    D.Ginv (D.H z) = D.Qs (Ring.inverse (N D) z) := by
  have h := congrArg (fun A : E →L[ℝ] E => A (D.Qs (Ring.inverse (N D) z)))
    (Ring.mul_inverse_cancel D.Ginv hB)
  exact h

/-- A primal residual and a multiplier, checked WITHOUT evaluating any inverse,
identify H*J exactly. This is sufficient for every quadratic jet simultaneously. -/
theorem source_of_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h : F)
    (hx : D.Q x = 0) (hr : D.Ginv x + D.Qs h = J) :
    ContinuousLinearMap.adjoint D.H J = h := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right, ← hr, inner_add_right]
  have hz : ⟪D.H z, D.Ginv x⟫ = 0 := by
    rw [← D.Ginv_symm hL, Ginv_H D hB, real_inner_comm, ← D.Q_adj, hx, inner_zero_left]
  rw [hz, zero_add, ← D.Q_adj, Q_H D hN]

/-- Equivalent weak certificate: only the residual paired with all vectors is needed. -/
theorem source_of_weak_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h : F)
    (hx : D.Q x = 0)
    (hr : ∀ y : E, ⟪y, D.Ginv x⟫ + ⟪D.Q y, h⟫ = ⟪y, J⟫) :
    ContinuousLinearMap.adjoint D.H J = h := by
  apply source_of_certificate D hL hB hN J x h hx
  apply ext_inner_left ℝ
  intro y
  rw [inner_add_right, ← D.Q_adj]
  exact hr y

/-- Pairing version needs no external translation or kernel-simplicity hypothesis. -/
theorem coupling_of_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h z : F)
    (hx : D.Q x = 0) (hr : D.Ginv x + D.Qs h = J) :
    2 * ⟪D.H z, J⟫ = 2 * ⟪z, h⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, source_of_certificate D hL hB hN J x h hx hr]

/-- Normalization of the one-dimensional candidate. The physical lift is not
asserted here. If x has two-site entries (a/2,-a/2), the path Laplacian contributes
(3a+left)/2 and -(3a+right)/2. Q* contributes h/8 on both entries. -/
theorem two_site_residual_iff (a left right h d : ℝ) :
    ((3 * a + left) / 2 + h / 8 = d / 2 ∧
     -(3 * a + right) / 2 + h / 8 = -d / 4) ↔
    (6 * a + left + right = (3 / 2 : ℝ) * d ∧
     h = d - 2 * left + 2 * right) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The pair-average constraint is exact with this normalization. -/
theorem alternating_pair_constraint (a : ℝ) : ((a / 2) + (-a / 2)) / 2 = 0 := by ring

/-- The finite recurrence plus multiplier formula gives both fine-site residuals. -/
theorem recurrence_fine_residuals (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j < n + 1, 6 * a j + (if j = 0 then 0 else a (j - 1)) + a (j + 1) =
      if j = 0 then (3 / 2 : ℝ) else 0) (j : ℕ) (hj : j < n + 1) :
    let l := if j = 0 then 0 else a (j - 1)
    let d : ℝ := if j = 0 then 1 else 0
    let h := d - 2 * l + 2 * a (j + 1)
    ((3 * a j + l) / 2 + h / 8 = d / 2 ∧
      -(3 * a j + a (j + 1)) / 2 + h / 8 = -d / 4) := by
  dsimp only
  apply (two_site_residual_iff _ _ _ _ _).mpr
  refine ⟨?_, rfl⟩
  have hh := ha j hj
  split_ifs at * <;> linarith

#print axioms N
#print axioms Q_H
#print axioms Ginv_H
#print axioms source_of_certificate
#print axioms source_of_weak_certificate
#print axioms coupling_of_certificate
#print axioms two_site_residual_iff
#print axioms alternating_pair_constraint
#print axioms recurrence_fine_residuals
end AdalyFormal.Round10.Dictionary.KKT

/-! Neutral source dictionary on the actual frozen family. No spectral claim. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Source
open scoped RealInnerProductSpace Topology
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal (uθ)

/-- The localized source itself, not its quadratic correction, is fixed. -/
theorem bulkSource_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) :
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R))
      (dataS selIn selIn (bulkP q R f ε)).J = (dataS selIn selIn (bulkP q R f ε)).J := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) (rotGauge α)
  rw [rot_bulkU] at h
  exact h.J.symm

/-- This consumes exactly the already-proved round-9 source-derivative predicate. -/
theorem sourceDerivative_U1 (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (α : ℝ) :
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) J' = J' := by
  let D := dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R)
  let A := adEL (rotGauge α) (geomOf 2 1 (dilTower q R))
  have hf (ε : ℝ) : A (D ε).J = (D ε).J := by
    have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
      (dilTower q R) 1 (dilLam q R) (dilU q R ε 1) (rotGauge α)
    have hu : periodicGaugeTransform (rotGauge α) (dilU q R ε 1) = dilU q R ε 1 := by
      rw [← bulkU_dilMask, rot_bulkU]
    rw [hu] at h
    exact h.J.symm
  change Tendsto (fun ε : ℝ => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J') at hJ
  have ht := A.continuous.continuousAt.tendsto.comp hJ
  change Tendsto (fun ε : ℝ => A (ε⁻¹ • (D ε).J)) (𝓝[≠] 0) (𝓝 (A J')) at ht
  simp only [map_smul, hf] at ht
  exact tendsto_nhds_unique ht hJ

/-- H at the flat point intertwines the full diagonal phase group. -/
theorem flatH_U1 (q R : ℕ) (α : ℝ) (z : FSp (geomOf 2 1 (dilTower q R))) :
    (flatData q R).H (adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) z) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).H z) := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  exact h.H z

/-- No inverse of a compressed block is used: this is the adjoint of full H. -/
def neutralSource (q R : ℕ) (J' : TwistSpace q R) : FSp (geomOf 2 1 (dilTower q R)) :=
  ContinuousLinearMap.adjoint (flatData q R).H J'

theorem neutralSource_U1 (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (α : ℝ) :
    adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) (neutralSource q R J') =
      neutralSource q R J' := by
  have h := adjoint_eqv (adFL (rotGauge α) (geomOf 2 1 (dilTower q R)))
    (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)))
    (flatData q R).H (flatData q R).H (flatH_U1 q R α) J'
  rw [sourceDerivative_U1 q R J' hJ α] at h
  exact h.symm

/-- The coefficient is in the orthonormal frozen Pauli basis, not an arbitrary scale. -/
def neutralCoord (X : SuTwo) : ℝ := ⟪pauliE3, X⟫

theorem half_fixed_offdiag (X : SuTwo) (h : RMap (uθ (Real.pi / 2)) X = X) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
  have hentry : ((RMap (uθ (Real.pi / 2)) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
      -(X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, mul_assoc]
    ring_nf
    simp [Complex.I_sq]
  rw [h] at hentry
  linear_combination (1 / 2 : ℂ) * hentry

theorem neutral_of_half_fixed (X : SuTwo) (h : RMap (uθ (Real.pi / 2)) X = X) :
    X = neutralCoord X • pauliE3 := by
  have hd := suTwo_decompose X
  rw [half_fixed_offdiag X h] at hd
  simp only [Complex.zero_im, Complex.zero_re, zero_smul, zero_add] at hd
  have hc : neutralCoord X = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im := by
    unfold neutralCoord
    conv_lhs => rw [hd]
    rw [inner_smul_right]
    change _ * hsInner pauliE3 pauliE3 = _
    rw [hsInner_e3_e3, mul_one]
  rw [hc]
  exact hd

theorem neutralSource_component (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (p : BIdx (geomOf 2 1 (dilTower q R))) :
    neutralSource q R J' p = neutralCoord (neutralSource q R J' p) • pauliE3 := by
  apply neutral_of_half_fixed
  have h := congrArg (fun z : FSp (geomOf 2 1 (dilTower q R)) => z p)
    (neutralSource_U1 q R J' hJ (Real.pi / 2))
  exact h

/-- Exact finite sum for the pinned analytic coupling, with physical normalization intact. -/
theorem vacCoupling_neutral_sum (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (v : TwistSpace q R) :
    vacCoupling q R J' v = 2 * ∑ p : BIdx (geomOf 2 1 (dilTower q R)),
      neutralCoord (neutralSource q R J' p) *
      neutralCoord (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
        (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v)) p) := by
  unfold vacCoupling
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change 2 * ⟪_, neutralSource q R J'⟫ = _
  congr 1
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs => rw [neutralSource_component q R J' hJ p]
  rw [inner_smul_right, real_inner_comm]
  rfl

/-- Name for the actual dressed flat quadratic jet. -/
abbrev vacJet (q R : ℕ) (v : TwistSpace q R) : FSp (geomOf 2 1 (dilTower q R)) :=
  C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))

/-- Level zero contributes no quadratic jet, for every geometry and background. -/
theorem C2_level_zero {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (x : BondFnL2 L) (p : BIdx G) (hp : (p.1 : ℕ) = 0) : C2fullOf G U x p = 0 := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (C2rawB G U p.1 x) p.2.1 = 0
  have hz : C2rawB G U (p.1 : ℕ) x = 0 := by
    rw [hp, C2rawB_eq, C2CompL_zero, map_zero]
  rw [hz]
  simp

/-- All physical coarse bonds and their actual PiLp normalization remain in this sum. -/
theorem vacCoupling_neutral_top_sum (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (v : TwistSpace q R) :
    vacCoupling q R J' v = 2 * ∑ p : BIdx (geomOf 2 1 (dilTower q R)) with (p.1 : ℕ) = 1,
      neutralCoord (neutralSource q R J' p) * neutralCoord (vacJet q R v p) := by
  classical
  rw [vacCoupling_neutral_sum q R J' hJ v, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (p.1 : ℕ) = 1
  · rw [if_pos hp]
  · rw [if_neg hp]
    have hp0 : (p.1 : ℕ) = 0 := by
      have ht := p.1.isLt
      change (p.1 : ℕ) < 2 at ht
      omega
    rw [C2_level_zero _ _ _ p hp0]
    simp [neutralCoord]

/-- Explicit vacuum coupling phase invariance; unlike round 1 this statement
is about the actual H0-C2-J' expression itself. -/
theorem vacCoupling_U1 (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (α : ℝ) (v : TwistSpace q R) :
    vacCoupling q R J' (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) v) =
      vacCoupling q R J' v := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  change 2 * ⟪(flatData q R).H ((flatData q R).C2
    (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) v)), J'⟫ =
    2 * ⟪(flatData q R).H ((flatData q R).C2 v), J'⟫
  have hc : (flatData q R).C2 (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) v) =
      adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).C2 v) := h.C2 v
  rw [hc, flatH_U1]
  conv_lhs => rw [← sourceDerivative_U1 q R J' hJ α]
  rw [LinearIsometryEquiv.inner_map_map]

/-- Specialization of the inverse-free certificate to the frozen flat family. -/
theorem flat_source_of_certificate (q R : ℕ) (J' x : TwistSpace q R)
    (h : FSp (geomOf 2 1 (dilTower q R)))
    (hB : IsUnit (flatData q R).Ginv) (hN : IsUnit (KKT.N (flatData q R)))
    (hx : (flatData q R).Q x = 0)
    (hr : (flatData q R).Ginv x + (flatData q R).Qs h = J') :
    neutralSource q R J' = h :=
  KKT.source_of_certificate (flatData q R) (dataS_laws selIn selIn _) hB hN J' x h hx hr

theorem vacCoupling_of_certificate (q R : ℕ) (J' x v : TwistSpace q R)
    (h : FSp (geomOf 2 1 (dilTower q R)))
    (hB : IsUnit (flatData q R).Ginv) (hN : IsUnit (KKT.N (flatData q R)))
    (hx : (flatData q R).Q x = 0)
    (hr : (flatData q R).Ginv x + (flatData q R).Qs h = J') :
    vacCoupling q R J' v = 2 * ⟪vacJet q R v, h⟫ :=
  KKT.coupling_of_certificate (flatData q R) (dataS_laws selIn selIn _) hB hN J' x h
    (vacJet q R v) hx hr

/-- Zero the freely specified exterior, exactly as bulkU does. -/
def interiorProfile (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ := by
  classical
  exact if b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then 0 else f b

theorem bulkU_phase (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    bulkU q R f ε = PhaseSource.phase (fun b => ε * interiorProfile q R f b) := by
  classical
  funext b
  unfold bulkU AdalyFormal.Round5.Guarded.IVTR2.maskedU PhaseSource.phase interiorProfile
  by_cases hb : b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [hb, if_true, mul_zero, PhaseSource.phase_zero]
  · simp only [hb, if_false, Ug_eq_uθ]

def profileSourceStencil (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : TwistSpace q R :=
  pE (geomOf 2 1 (dilTower q R))
    (PhaseSource.sourceLinear (plaqIn ((dilTower q R).Om 0)) (interiorProfile q R f))

/-- Explicit two-sided first-order limit of the actual localized source, every profile. -/
theorem bulkSource_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (dataS selIn selIn (bulkP q R f ε)).J)
      (𝓝[≠] 0) (𝓝 (profileSourceStencil q R f)) := by
  show Tendsto (fun ε : ℝ => ε⁻¹ • pE (geomOf 2 1 (dilTower q R))
    (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
      (plaqIn ((dilTower q R).Om 0)) (bulkU q R f ε) b)))) (𝓝[≠] 0)
    (𝓝 (profileSourceStencil q R f))
  simp only [bulkU_phase, ← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp
    (PhaseSource.sourceField_tendsto (plaqIn ((dilTower q R).Om 0)) (interiorProfile q R f))

theorem bulkSource_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    (dataS selIn selIn (bulkP q R f 0)).J = 0 := by
  have hu : bulkU q R f 0 = (fun _ => 1) := by
    rw [bulkU_phase]
    funext b
    exact (by simp only [PhaseSource.phase, zero_mul, PhaseSource.phase_zero])
  change pE (geomOf 2 1 (dilTower q R)) (WithLp.toLp 2 (fun b =>
    -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn ((dilTower q R).Om 0)) (bulkU q R f 0) b))) = 0
  rw [hu]
  have hz : (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
      (plaqIn ((dilTower q R).Om 0)) (fun _ => 1) b)) : BondFnL2 (scaleUp 2 1 (dilLu q R))) = 0 := by
    apply PiLp.ext
    intro b
    exact neg_eq_zero.mpr (AdalyFormal.IngredientFamily.JSU2Loc_trivial 1 _ b)
  rw [hz, map_zero]

/-- The actual canonical J' is this explicit, finite difference source. -/
abbrev canonicalSourceStencil (q R : ℕ) : TwistSpace q R := profileSourceStencil q R (dilMask q R)

theorem canonical_isSourceDerivative (q R : ℕ) : IsSourceDerivative q R (canonicalSourceStencil q R) := by
  have ht := bulkSource_tendsto q R (dilMask q R)
  change Tendsto (fun ε : ℝ => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2)
    (dilTower q R) (dilV q R) 1 (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 (canonicalSourceStencil q R))
  have he (ε : ℝ) : (dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (dilV q R) 1 (dilLam q R) ε).J =
      (dataS selIn selIn (bulkP q R (dilMask q R) ε)).J := by
    unfold dataFam dilV bulkP
    rw [bulkU_dilMask]
  simp only [he]
  exact ht

theorem sourceDerivative_eq_stencil (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') : J' = canonicalSourceStencil q R :=
  tendsto_nhds_unique hJ (canonical_isSourceDerivative q R)

#print axioms interiorProfile
#print axioms bulkU_phase
#print axioms profileSourceStencil
#print axioms bulkSource_tendsto
#print axioms bulkSource_zero
#print axioms canonicalSourceStencil
#print axioms canonical_isSourceDerivative
#print axioms sourceDerivative_eq_stencil
#print axioms vacJet
#print axioms C2_level_zero
#print axioms vacCoupling_neutral_top_sum
#print axioms vacCoupling_U1
#print axioms flat_source_of_certificate
#print axioms vacCoupling_of_certificate
#print axioms bulkSource_U1
#print axioms sourceDerivative_U1
#print axioms flatH_U1
#print axioms neutralSource
#print axioms neutralSource_U1
#print axioms neutralCoord
#print axioms half_fixed_offdiag
#print axioms neutral_of_half_fixed
#print axioms neutralSource_component
#print axioms vacCoupling_neutral_sum
end AdalyFormal.Round10.Dictionary.Source

/-! Summation by parts for the actual diagonal source stencil. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.SourceEnergy
open scoped BigOperators RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.PhaseSource
variable {L : PeriodicLatticeExtent}
attribute [local instance] Classical.propDecidable

theorem sum_backward (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * g (periodicLatticeShiftBack x ν)) =
      ∑ x, f (periodicLatticeShift x ν) * g x := by
  have h := Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) ν)
    (fun x => f x * g (periodicLatticeShiftBack x ν))
  simpa only [periodicLatticeShiftEquiv_apply, periodicLatticeShiftBack_shift] using h.symm

theorem sum_backward_diff (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * (g (periodicLatticeShiftBack x ν) - g x)) =
      ∑ x, (f (periodicLatticeShift x ν) - f x) * g x := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, sum_backward]

theorem sum_dirs (f : PeriodicPlaquetteDirections → ℝ) :
    ∑ d, f d = f ⟨(0,1), by decide⟩ + f ⟨(0,2), by decide⟩ + f ⟨(1,2), by decide⟩ := by
  have hu : (Finset.univ : Finset PeriodicPlaquetteDirections) =
      {⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(1,2), by decide⟩} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

theorem oriented_diag (P : Set (PeriodicLatticePlaquette L))
    (g : PeriodicLatticePlaquette L → ℝ) (ν : Fin 3) (x : PeriodicLatticeSite L) :
    oriented P g ν ν x = 0 := by
  simp [oriented]

theorem div_sum (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) :
    (∑ b : Bond L, f b * scalarDiv (oriented P g) b) =
      ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
        (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [scalarDiv, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : ν = μ
  · subst ν
    simp only [ite_true, mul_zero, oriented_diag, Finset.sum_const_zero]
  · simp only [if_neg h]
    exact sum_backward_diff (fun x => f (x, μ)) (oriented P g ν μ) ν

theorem oriented_curl_point (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) (x : PeriodicLatticeSite L) :
    (∑ μ : Fin 3, ∑ ν : Fin 3,
      (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x) =
    ∑ d : PeriodicPlaquetteDirections, if (x,d) ∈ P then circulation f (x,d) * g (x,d) else 0 := by
  classical
  have h01 : oriented P g 0 1 x = if (x, ⟨(0,1), by decide⟩) ∈ P then g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h02 : oriented P g 0 2 x = if (x, ⟨(0,2), by decide⟩) ∈ P then g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h12 : oriented P g 1 2 x = if (x, ⟨(1,2), by decide⟩) ∈ P then g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  have h10 : oriented P g 1 0 x = if (x, ⟨(0,1), by decide⟩) ∈ P then -g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h20 : oriented P g 2 0 x = if (x, ⟨(0,2), by decide⟩) ∈ P then -g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h21 : oriented P g 2 1 x = if (x, ⟨(1,2), by decide⟩) ∈ P then -g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  rw [sum_dirs]
  simp only [Fin.sum_univ_three, oriented_diag, h01, h02, h12, h10, h20, h21, circulation]
  split_ifs <;> ring

/-- Exact localized Stokes identity; no boundary term on the physical torus. -/
theorem source_sbp (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b : Bond L, f b * linearSourceScalar P g b) =
      ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p * circulation g p else 0 := by
  classical
  change (∑ b : Bond L, f b * scalarDiv (oriented P (circulation g)) b) = _
  rw [div_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => oriented_curl_point P f (circulation g) x)

theorem source_reciprocity (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b, f b * linearSourceScalar P g b) = ∑ b, g b * linearSourceScalar P f b := by
  rw [source_sbp, source_sbp]
  simp only [mul_comm]

def curlEnergy (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p ^ 2 else 0

theorem source_energy (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    (∑ b, f b * linearSourceScalar P f b) = curlEnergy P f := by
  rw [source_sbp]
  simp only [curlEnergy, pow_two]

theorem curlEnergy_nonneg (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 ≤ curlEnergy P f := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity

theorem curlEnergy_eq_zero_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    curlEnergy P f = 0 ↔ ∀ p ∈ P, circulation f p = 0 := by
  classical
  unfold curlEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  constructor
  · intro h p hp
    have hz := h p (Finset.mem_univ p)
    simpa only [if_pos hp, sq_eq_zero_iff] using hz
  · intro h p _
    by_cases hp : p ∈ P
    · simp only [if_pos hp, h p hp, zero_pow (by decide : 2 ≠ 0)]
    · simp only [if_neg hp]

theorem curlEnergy_pos_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 < curlEnergy P f ↔ ∃ p ∈ P, circulation f p ≠ 0 := by
  have h : 0 < curlEnergy P f ↔ curlEnergy P f ≠ 0 :=
    lt_iff_le_and_ne.trans (and_iff_right (curlEnergy_nonneg P f)) |>.trans ne_comm
  rw [h, ne_eq, curlEnergy_eq_zero_iff]
  simp only [not_forall, exists_prop]

def neutralCoordinate (w : BondFnL2 L) (b : Bond L) : ℝ := ⟪pauliE3, w b⟫

/-- The R2 source stencil is the actual positive scalar curl-square operator. -/
theorem inner_sourceLinear (P : Set (PeriodicLatticePlaquette L))
    (w : BondFnL2 L) (f : Bond L → ℝ) :
    ⟪w, sourceLinear P f⟫ = ∑ p : PeriodicLatticePlaquette L,
      if p ∈ P then circulation (neutralCoordinate w) p * circulation f p else 0 := by
  rw [PiLp.inner_apply]
  have h (b : Bond L) : ⟪w b, sourceLinear P f b⟫ =
      neutralCoordinate w b * linearSourceScalar P f b := by
    change ⟪w b, linearSourceScalar P f b • pauliE3⟫ = _
    rw [inner_smul_right, real_inner_comm]
    exact mul_comm _ _
  simp_rw [h]
  exact source_sbp P (neutralCoordinate w) f

#print axioms sum_backward
#print axioms sum_backward_diff
#print axioms sum_dirs
#print axioms oriented_diag
#print axioms div_sum
#print axioms oriented_curl_point
#print axioms source_sbp
#print axioms source_reciprocity
#print axioms curlEnergy
#print axioms source_energy
#print axioms curlEnergy_nonneg
#print axioms curlEnergy_eq_zero_iff
#print axioms curlEnergy_pos_iff
#print axioms neutralCoordinate
#print axioms inner_sourceLinear
end AdalyFormal.Round10.Dictionary.SourceEnergy

/-! Free-profile coupling as a positive physical curl energy. No crossing nonvanishing is asserted. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.FreeSource
open scoped BigOperators RealInnerProductSpace Topology Matrix
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Dictionary.PhaseSource
attribute [local instance] Classical.propDecidable

variable {L : PeriodicLatticeExtent}

theorem circulation_congr_boundary (f g : Bond L → ℝ) (p : PeriodicLatticePlaquette L)
    (h : ∀ b ∈ periodicPlaquetteBoundaryEdges p, f b = g b) :
    circulation f p = circulation g p := by
  unfold circulation
  rw [h (p.1,p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges]),
    h (periodicLatticeShift p.1 p.2.1.1,p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges]),
    h (periodicLatticeShift p.1 p.2.1.2,p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges]),
    h (p.1,p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])]

/-- Interior zeroing is invisible to every selected physical plaquette. -/
theorem circulation_interiorProfile (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : p ∈ plaqIn ((dilTower q R).Om 0)) :
    circulation (interiorProfile q R f) p = circulation f p := by
  apply circulation_congr_boundary
  intro b hb
  have hbp := hp b hb
  have hz : b ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := by
    intro h
    exact h.1 hbp.1
  simp only [interiorProfile, if_neg hz]

/-- Neutral scalar part of the FULL constrained lift of the actual quadratic jet. -/
def responseProfile (q R : ℕ) (u : TwistSpace q R)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ :=
  neutralCoordinate (iE (geomOf 2 1 (dilTower q R))
    ((flatData q R).H (vacJet q R u))) b

/-- Explicit form already used in the round-9 first-order coupling bridges. -/
def profileCoupling (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (u : TwistSpace q R) : ℝ := vacCoupling q R (profileSourceStencil q R f) u

/-- Exact frozen-operator identity for EVERY profile and every physical carrier vector.
The sum has no Bloch normalization, compressed inverse or model recurrence. -/
theorem profileCoupling_curl (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = 2 *
      ∑ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        if p ∈ plaqIn ((dilTower q R).Om 0) then
          circulation (responseProfile q R u) p * circulation f p else 0 := by
  unfold profileCoupling vacCoupling profileSourceStencil
  rw [pE_inner_right, inner_sourceLinear]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ plaqIn ((dilTower q R).Om 0)
  · rw [if_pos hp, if_pos hp, circulation_interiorProfile q R f p hp]
    rfl
  · simp only [if_neg hp]

/-- An adaptive profile has a manifestly nonnegative actual explicit coupling. -/
theorem adaptive_energy (q R : ℕ) (u : TwistSpace q R) :
    profileCoupling q R (responseProfile q R u) u =
      2 * curlEnergy (plaqIn ((dilTower q R).Om 0)) (responseProfile q R u) := by
  rw [profileCoupling_curl]
  simp only [curlEnergy, pow_two]

theorem adaptive_nonneg (q R : ℕ) (u : TwistSpace q R) :
    0 ≤ profileCoupling q R (responseProfile q R u) u := by
  rw [adaptive_energy]
  exact mul_nonneg (by norm_num) (curlEnergy_nonneg _ _)

/-- This is the exact remaining per-vector detection obstruction, not its proof. -/
def CurlDetected (q R : ℕ) (u : TwistSpace q R) : Prop :=
  ∃ p ∈ plaqIn ((dilTower q R).Om 0), circulation (responseProfile q R u) p ≠ 0

theorem adaptive_pos_iff (q R : ℕ) (u : TwistSpace q R) :
    0 < profileCoupling q R (responseProfile q R u) u ↔ CurlDetected q R u := by
  rw [adaptive_energy, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2), curlEnergy_pos_iff]
  rfl

/-- Exact controllability criterion over ALL freely allowed real profiles. -/
theorem exists_profile_iff_curlDetected (q R : ℕ) (u : TwistSpace q R) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, profileCoupling q R f u ≠ 0) ↔
      CurlDetected q R u := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hn
    have hz : ∀ p ∈ plaqIn ((dilTower q R).Om 0), circulation (responseProfile q R u) p = 0 := by
      simpa only [CurlDetected, not_exists, not_and, not_not] using hn
    apply hf
    rw [profileCoupling_curl]
    have hs : (∑ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        if p ∈ plaqIn ((dilTower q R).Om 0) then
          circulation (responseProfile q R u) p * circulation f p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      split_ifs with hp
      · rw [hz p hp, zero_mul]
      · rfl
    rw [hs, mul_zero]
  · intro h
    exact ⟨responseProfile q R u, ne_of_gt ((adaptive_pos_iff q R u).mpr h)⟩

/-- Equivalently, ALL free profiles vanish precisely at a curl-free neutral lift. -/
theorem all_profiles_zero_iff (q R : ℕ) (u : TwistSpace q R) :
    (∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, profileCoupling q R f u = 0) ↔
      ∀ p ∈ plaqIn ((dilTower q R).Om 0), circulation (responseProfile q R u) p = 0 := by
  have h := not_congr (exists_profile_iff_curlDetected q R u)
  simpa only [CurlDetected, not_exists, not_and, not_not] using h

/-- The explicit profile is genuinely supported on the touching-bond carrier. -/
theorem responseProfile_off (q R : ℕ) (u : TwistSpace q R)
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hb : b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    responseProfile q R u b = 0 := by
  have hn : b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
    rintro (h | h)
    · exact hb.1 h
    · exact hb.2 h
  have hz := ((flatData q R).H (vacJet q R u)).property b hn
  change ⟪pauliE3, ((flatData q R).H (vacJet q R u)).val b⟫ = 0
  rw [hz, inner_zero_right]

/-- No additional profile masking is needed for the adaptive profile. -/
theorem responseProfile_interior (q R : ℕ) (u : TwistSpace q R) :
    interiorProfile q R (responseProfile q R u) = responseProfile q R u := by
  funext b
  by_cases hb : b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [interiorProfile, if_pos hb, responseProfile_off q R u b hb]
  · simp only [interiorProfile, if_neg hb]

/-- Full QH identity at the physical quadratic jet, requiring only the actual N unit. -/
theorem liftJet_Q (q R : ℕ) (hN : IsUnit (KKT.N (flatData q R))) (u : TwistSpace q R) :
    (flatData q R).Q ((flatData q R).H (vacJet q R u)) = vacJet q R u :=
  KKT.Q_H _ hN _

theorem fixed_of_slope_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (f : ℝ → E) (v : E)
    (ht : Tendsto (fun ε : ℝ => ε⁻¹ • f ε) (𝓝[≠] 0) (𝓝 v))
    (hf : ∀ ε, A (f ε) = f ε) : A v = v := by
  have h := (A.continuous.tendsto v).comp ht
  simp only [Function.comp_def, map_smul, hf] at h
  exact tendsto_nhds_unique h ht

theorem phase_axis_fixed (α : ℝ) : RMap (AdalyFormal.D1Literal.uθ α) pauliE3 = pauliE3 := by
  apply Subtype.ext
  rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply]
  change AdalyFormal.D1Literal.uMat α * _ * (AdalyFormal.D1Literal.uMat α)ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, pauliE3,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      ← Complex.exp_conj, Complex.exp_neg]
  all_goals field_simp

theorem sourceLinear_U1 (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (α : ℝ) :
    adBL (rotGauge α) (sourceLinear P f) = sourceLinear P f := by
  apply PiLp.ext
  intro b
  change RMap (AdalyFormal.D1Literal.uθ α) (linearSourceScalar P f b • pauliE3) =
    linearSourceScalar P f b • pauliE3
  rw [map_smul, phase_axis_fixed]

/-- Any profile's explicit source is fixed by all constant diagonal phases. -/
theorem profileSource_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (α : ℝ) :
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (profileSourceStencil q R f) =
      profileSourceStencil q R f := by
  unfold profileSourceStencil
  rw [← pE_adBL, sourceLinear_U1]

/-- Invariance of the explicit free-profile coupling, independent of spectral claims. -/
theorem profileCoupling_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      profileCoupling q R f u := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  change 2 * ⟪(flatData q R).H ((flatData q R).C2
    (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)), profileSourceStencil q R f⟫ =
    2 * ⟪(flatData q R).H ((flatData q R).C2 u), profileSourceStencil q R f⟫
  have hc : (flatData q R).C2 (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).C2 u) := h.C2 u
  rw [hc, flatH_U1]
  conv_lhs => rw [← profileSource_U1 q R f α]
  rw [LinearIsometryEquiv.inner_map_map]

/-- Propagated free-profile sources are neutral before any sector reduction. -/
theorem profileNeutralSource_U1 (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (α : ℝ) :
    adFL (rotGauge α) (geomOf 2 1 (dilTower q R))
      (neutralSource q R (profileSourceStencil q R f)) =
      neutralSource q R (profileSourceStencil q R f) := by
  have h := adjoint_eqv (adFL (rotGauge α) (geomOf 2 1 (dilTower q R)))
    (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)))
    (flatData q R).H (flatData q R).H (flatH_U1 q R α) (profileSourceStencil q R f)
  rw [profileSource_U1] at h
  exact h.symm

theorem profileNeutralSource_component (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (p : BIdx (geomOf 2 1 (dilTower q R))) :
    neutralSource q R (profileSourceStencil q R f) p =
      neutralCoord (neutralSource q R (profileSourceStencil q R f) p) • pauliE3 := by
  apply neutral_of_half_fixed
  exact congrArg (fun z : FSp (geomOf 2 1 (dilTower q R)) => z p)
    (profileNeutralSource_U1 q R f (Real.pi / 2))

/-- The physical level-one source/jet sum now covers arbitrary profiles. -/
theorem profileCoupling_neutral_top_sum (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = 2 * ∑ p : BIdx (geomOf 2 1 (dilTower q R)) with (p.1 : ℕ) = 1,
      neutralCoord (neutralSource q R (profileSourceStencil q R f) p) *
        neutralCoord (vacJet q R u p) := by
  unfold profileCoupling vacCoupling
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change 2 * ⟪vacJet q R u, neutralSource q R (profileSourceStencil q R f)⟫ = _
  congr 1
  rw [PiLp.inner_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (p.1 : ℕ) = 1
  · rw [if_pos hp]
    conv_lhs => rw [profileNeutralSource_component]
    rw [inner_smul_right, real_inner_comm]
    rfl
  · rw [if_neg hp]
    have hp0 : (p.1 : ℕ) = 0 := by
      have ht := p.1.isLt
      change (p.1 : ℕ) < 2 at ht
      omega
    rw [C2_level_zero _ _ _ p hp0, inner_zero_left]

/-- R1 half-turn calculation, restated here for the scalar-neutral interface. -/
theorem half_twice (X : SuTwo) :
    RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2))
      (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) X) = X := by
  apply Subtype.ext
  rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply,
    AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply,
    AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

/-- Averaging the half turn is the exact orthogonal neutral projection. -/
theorem half_average (X : SuTwo) :
    (1 / 2 : ℝ) • (X + RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) X) =
      neutralCoord X • pauliE3 := by
  let Y := (1 / 2 : ℝ) • (X + RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) X)
  have hf : RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) Y = Y := by
    dsimp only [Y]
    rw [map_smul, map_add, half_twice, add_comm]
  have hi : ⟪pauliE3, RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) X⟫ = ⟪pauliE3, X⟫ := by
    have h := inner_RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) pauliE3 X
    rw [phase_axis_fixed] at h
    exact h
  have hc : neutralCoord Y = neutralCoord X := by
    unfold Y neutralCoord
    rw [inner_smul_right, inner_add_right, hi]
    ring
  calc Y = neutralCoord Y • pauliE3 := neutral_of_half_fixed Y hf
       _ = neutralCoord X • pauliE3 := by rw [hc]

/-- Actual carrier Q intertwines all diagonal phases at the flat point. -/
theorem flatQ_U1 (q R : ℕ) (α : ℝ) (x : TwistSpace q R) :
    (flatData q R).Q (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) x) =
      adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).Q x) := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  exact h.Q x

/-- Physical neutral field corresponding to the adaptive profile. -/
def responseField (q R : ℕ) (u : TwistSpace q R) : BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
  WithLp.toLp 2 (fun b => responseProfile q R u b • pauliE3)

theorem responseField_half (q R : ℕ) (u : TwistSpace q R) :
    responseField q R u = iE (geomOf 2 1 (dilTower q R))
      ((1 / 2 : ℝ) • ((flatData q R).H (vacJet q R u) +
        adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R))
          ((flatData q R).H (vacJet q R u)))) := by
  apply PiLp.ext
  intro b
  change neutralCoord (((flatData q R).H (vacJet q R u)).val b) • pauliE3 =
    (1 / 2 : ℝ) • ((((flatData q R).H (vacJet q R u)).val b) +
      RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) (((flatData q R).H (vacJet q R u)).val b))
  exact (half_average _).symm

/-- Q of the physical adaptive field is exactly the neutral part of the original jet.
Only the full, already-known flat constraint unit is required. -/
theorem responseField_Q (q R : ℕ) (hN : IsUnit (KKT.N (flatData q R)))
    (u : TwistSpace q R) (p : BIdx (geomOf 2 1 (dilTower q R))) :
    QfullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1) (responseField q R u) p =
      neutralCoord (vacJet q R u p) • pauliE3 := by
  rw [responseField_half]
  change (flatData q R).Q
      ((1 / 2 : ℝ) • ((flatData q R).H (vacJet q R u) +
        adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R))
          ((flatData q R).H (vacJet q R u)))) p = _
  rw [map_smul, map_add, flatQ_U1, liftJet_Q q R hN]
  change (1 / 2 : ℝ) • (vacJet q R u p +
    RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) (vacJet q R u p)) = _
  exact half_average _

theorem Q_level_zero {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)
    (x : BondFnL2 L) (p : BIdx G) (hp : (p.1 : ℕ) = 0) :
    QfullOf G U x p = x p.2.1 := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • QlinB G U (p.1 : ℕ) x p.2.1 = _
  have hq : QlinB G U (p.1 : ℕ) x = x := by rw [hp, QlinB_zero]
  have hs : (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) = 1 := by rw [hp]; norm_num
  rw [hq, hs, one_smul]

/-- Every level-zero constraint row is an exact zero of the adaptive scalar profile. -/
theorem responseProfile_level_zero (q R : ℕ) (hN : IsUnit (KKT.N (flatData q R)))
    (u : TwistSpace q R) (p : BIdx (geomOf 2 1 (dilTower q R))) (hp : (p.1 : ℕ) = 0) :
    responseProfile q R u p.2.1 = 0 := by
  have h := responseField_Q q R hN u p
  rw [Q_level_zero _ _ _ p hp, C2_level_zero _ _ _ p hp] at h
  have h' := congrArg (fun X : SuTwo => ⟪pauliE3, X⟫) h
  change ⟪pauliE3, responseProfile q R u p.2.1 • pauliE3⟫ = ⟪pauliE3, neutralCoord 0 • pauliE3⟫ at h'
  rw [inner_smul_right, inner_smul_right] at h'
  change responseProfile q R u p.2.1 * hsInner pauliE3 pauliE3 =
    neutralCoord 0 * hsInner pauliE3 pauliE3 at h'
  simpa only [hsInner_e3_e3, mul_one, neutralCoord, inner_zero_right] using h'

#print axioms profileNeutralSource_U1
#print axioms profileNeutralSource_component
#print axioms profileCoupling_neutral_top_sum
#print axioms half_twice
#print axioms half_average
#print axioms flatQ_U1
#print axioms responseField
#print axioms responseField_half
#print axioms responseField_Q
#print axioms Q_level_zero
#print axioms responseProfile_level_zero
#print axioms circulation_congr_boundary
#print axioms circulation_interiorProfile
#print axioms responseProfile
#print axioms profileCoupling
#print axioms profileCoupling_curl
#print axioms adaptive_energy
#print axioms adaptive_nonneg
#print axioms CurlDetected
#print axioms adaptive_pos_iff
#print axioms exists_profile_iff_curlDetected
#print axioms all_profiles_zero_iff
#print axioms responseProfile_off
#print axioms responseProfile_interior
#print axioms liftJet_Q
#print axioms fixed_of_slope_limit
#print axioms phase_axis_fixed
#print axioms sourceLinear_U1
#print axioms profileSource_U1
#print axioms profileCoupling_U1
end AdalyFormal.Round10.Dictionary.FreeSource


/-! Finite transverse flux and normalized two-site blocking.
The field-to-array identification is kept separate from these finite identities. -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.Round10.Nonvanishing.Flux

open Finset

variable {T : Type*} [Fintype T]

/-- Tangential flux through a longitudinal layer. -/
def flux (b : ℕ → T → ℝ) (x : ℕ) : ℝ := ∑ t, b x t

/-- Oriented 0-mu plaquette stencil, with periodic tangential shift `s`. -/
def curl (s : T ≃ T) (a b : ℕ → T → ℝ) (x : ℕ) (t : T) : ℝ :=
  a x t + b (x+1) t - a x (s t) - b x t

/-- Transverse divergence cancels exactly, not asymptotically. -/
theorem sum_curl (s : T ≃ T) (a b : ℕ → T → ℝ) (x : ℕ) :
    ∑ t, curl s a b x t = flux b (x+1) - flux b x := by
  have hs : ∑ t, a x (s t) = ∑ t, a x t := Equiv.sum_comp s (a x)
  simp only [curl, Finset.sum_sub_distrib, Finset.sum_add_distrib, flux]
  rw [hs]
  ring

/-- Zero plaquette curl makes layer flux constant on a finite interval. -/
theorem flux_eq_of_curl_zero (s : T ≃ T) (a b : ℕ → T → ℝ) (l n : ℕ)
    (hc : ∀ x, l ≤ x → x < l+n → ∀ t, curl s a b x t = 0) :
    flux b (l+n) = flux b l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun x hxl hxn => hc x hxl (by omega))
    have hz : ∑ t, curl s a b (l+n) t = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      exact hc (l+n) (by omega) (by omega) t
    rw [sum_curl] at hz
    have : flux b (l+n+1) = flux b (l+n) := sub_eq_zero.mp hz
    simpa [Nat.add_assoc] using this.trans hprev

/-- One zero-flux collar layer is enough. No pointwise gauge choice is required. -/
theorem flux_zero_of_curl_zero (s : T ≃ T) (a b : ℕ → T → ℝ) (l h : ℕ)
    (hl : flux b l = 0)
    (hc : ∀ x, l ≤ x → x < h → ∀ t, curl s a b x t = 0)
    (x : ℕ) (hxl : l ≤ x) (hxh : x ≤ h) : flux b x = 0 := by
  have he := flux_eq_of_curl_zero s a b l (x-l)
    (fun y hyl hyx => hc y hyl (by omega))
  rw [Nat.add_sub_of_le hxl] at he
  exact he.trans hl

/-- Sum of the normalized level-one tangential rows at one longitudinal block. -/
noncomputable def coarseFlux (b : ℕ → T → ℝ) (p : ℕ) : ℝ :=
  (1/8 : ℝ) * (flux b p + flux b (p+1))

/-- A nonzero coarse tangential flux forces a nonzero interior plaquette curl. -/
theorem exists_curl_of_coarseFlux (s : T ≃ T) (a b : ℕ → T → ℝ) (l p : ℕ)
    (hlp : l ≤ p) (hl : flux b l = 0) (hb : coarseFlux b p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  classical
  by_contra hn
  have hc : ∀ x, l ≤ x → x < p+1 → ∀ t, curl s a b x t = 0 := by
    intro x hxl hxp t
    by_contra ht
    exact hn ⟨x,hxl,hxp,t,ht⟩
  have h0 := flux_zero_of_curl_zero s a b l (p+1) hl hc p hlp (by omega)
  have h1 := flux_zero_of_curl_zero s a b l (p+1) hl hc (p+1) (by omega) le_rfl
  apply hb
  simp [coarseFlux,h0,h1]

/-- The same conclusion for any nonzero prescribed multiple of the physical flux. -/
theorem exists_curl_of_jet (s : T ≃ T) (a b : ℕ → T → ℝ) (l p : ℕ)
    (jet factor : ℝ) (hlp : l ≤ p) (hl : flux b l = 0)
    (hdict : jet = factor * coarseFlux b p) (hj : jet ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  apply exists_curl_of_coarseFlux s a b l p hlp hl
  intro hz
  apply hj
  rw [hdict,hz,mul_zero]

section Tiling
variable {C O : Type*} [Fintype C] [Fintype O]

/-- The printed ell=2 row sum: eight sites and two path links, coefficient 1/16.
A transverse tiling accounts for the four transverse offsets. -/
noncomputable def blockRow (tile : C × O ≃ T) (s : T ≃ T)
    (b : ℕ → T → ℝ) (p : ℕ) (c : C) : ℝ :=
  (1/16 : ℝ) * ∑ o, (b p (tile (c,o)) + b p (s (tile (c,o))) +
    b (p+1) (tile (c,o)) + b (p+1) (s (tile (c,o))))

/-- The exact physical normalization is 1/8 times two layer fluxes.
The transverse cardinality is already in the sum; no Bloch normalization occurs. -/
theorem sum_blockRow (tile : C × O ≃ T) (s : T ≃ T)
    (b : ℕ → T → ℝ) (p : ℕ) :
    ∑ c, blockRow tile s b p c = coarseFlux b p := by
  have hsum (f : T → ℝ) : (∑ c, ∑ o, f (tile (c,o))) = ∑ t, f t := by
    calc
      _ = ∑ co : C × O, f (tile co) := (Fintype.sum_prod_type (fun co : C × O => f (tile co))).symm
      _ = _ := Equiv.sum_comp tile f
  have hs (x : ℕ) : (∑ t, b x (s t)) = ∑ t, b x t := Equiv.sum_comp s (b x)
  simp only [blockRow, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum (b p),hsum (fun t => b p (s t)),hsum (b (p+1)),
    hsum (fun t => b (p+1) (s t)),hs,hs]
  simp only [coarseFlux,flux]
  ring

/-- Direct finite-array interface for the genuine level-one blocking formula. -/
theorem exists_curl_of_blockRows (tile : C × O ≃ T) (s : T ≃ T)
    (a b : ℕ → T → ℝ) (l p : ℕ) (hlp : l ≤ p) (hl : flux b l = 0)
    (hb : (∑ c, blockRow tile s b p c) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t, curl s a b x t ≠ 0 := by
  apply exists_curl_of_coarseFlux s a b l p hlp hl
  simpa [sum_blockRow] using hb
end Tiling

#print axioms flux
#print axioms curl
#print axioms sum_curl
#print axioms flux_eq_of_curl_zero
#print axioms flux_zero_of_curl_zero
#print axioms coarseFlux
#print axioms exists_curl_of_coarseFlux
#print axioms exists_curl_of_jet
#print axioms blockRow
#print axioms sum_blockRow
#print axioms exists_curl_of_blockRows
end AdalyFormal.Round10.Nonvanishing.Flux

namespace AdalyFormal.Round10.Nonvanishing.TorusFlux

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Round10.Nonvanishing.Flux

variable {L : PeriodicLatticeExtent}

abbrev Slice (L : PeriodicLatticeExtent) := Fin (L 1+1) × Fin (L 2+1)

/-- The actual physical transverse section, with the longitudinal index periodic. -/
def site (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticeSite L := by
  intro μ
  refine Fin.cases (Fin.ofNat (L 0+1) x) ?_ μ
  intro ν
  refine Fin.cases t.1 ?_ ν
  intro κ
  refine Fin.cases t.2 ?_ κ
  intro j
  exact Fin.elim0 j

@[simp] theorem site_zero (x : ℕ) (t : Slice L) : site L x t 0 = Fin.ofNat (L 0+1) x := rfl
@[simp] theorem site_one (x : ℕ) (t : Slice L) : site L x t 1 = t.1 := rfl
@[simp] theorem site_two (x : ℕ) (t : Slice L) : site L x t 2 = t.2 := rfl

/-- Unit translation on the actual first transverse circle. -/
def shift1 (L : PeriodicLatticeExtent) : Slice L ≃ Slice L where
  toFun t := (t.1+1,t.2)
  invFun t := (t.1-1,t.2)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

/-- Unit translation on the actual second transverse circle. -/
def shift2 (L : PeriodicLatticeExtent) : Slice L ≃ Slice L where
  toFun t := (t.1,t.2+1)
  invFun t := (t.1,t.2-1)
  left_inv t := by ext <;> simp
  right_inv t := by ext <;> simp

@[simp] theorem shift_site_zero (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 0 = site L (x+1) t := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift]
  apply Fin.ext
  change (x % (L 0+1) + 1 % (L 0+1)) % (L 0+1) = (x+1) % (L 0+1)
  exact (Nat.add_mod x 1 (L 0+1)).symm

@[simp] theorem shift_site_one (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 1 = site L x (shift1 L t) := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift,shift1]

@[simp] theorem shift_site_two (x : ℕ) (t : Slice L) :
    periodicLatticeShift (site L x t) 2 = site L x (shift2 L t) := by
  funext μ
  fin_cases μ <;> simp [periodicLatticeShift,shift2]

/-- A physical scalar bond field restricted to the indicated layer and direction. -/
def component (A : Bond L → ℝ) (μ : Fin 3) (x : ℕ) (t : Slice L) : ℝ :=
  A (site L x t,μ)

def plaq01 (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticePlaquette L :=
  (site L x t,⟨(0,1),by decide⟩)

def plaq02 (L : PeriodicLatticeExtent) (x : ℕ) (t : Slice L) : PeriodicLatticePlaquette L :=
  (site L x t,⟨(0,2),by decide⟩)

/-- No replacement curl: this is the frozen physical oriented plaquette formula. -/
theorem curl01 (A : Bond L → ℝ) (x : ℕ) (t : Slice L) :
    curlValue A (plaq01 L x t) = curl (shift1 L) (component A 0) (component A 1) x t := by
  simp [curlValue,plaq01,curl,component]

theorem curl02 (A : Bond L → ℝ) (x : ℕ) (t : Slice L) :
    curlValue A (plaq02 L x t) = curl (shift2 L) (component A 0) (component A 2) x t := by
  simp [curlValue,plaq02,curl,component]

/-- Exact physical transverse divergence theorem in the 0-1 plane. -/
theorem sum_curl01 (A : Bond L → ℝ) (x : ℕ) :
    ∑ t : Slice L, curlValue A (plaq01 L x t) =
      flux (component A 1) (x+1) - flux (component A 1) x := by
  simp_rw [curl01]
  exact sum_curl _ _ _ _

theorem sum_curl02 (A : Bond L → ℝ) (x : ℕ) :
    ∑ t : Slice L, curlValue A (plaq02 L x t) =
      flux (component A 2) (x+1) - flux (component A 2) x := by
  simp_rw [curl02]
  exact sum_curl _ _ _ _

/-- Nonzero physical coarse tangential flux forces a physical nonzero plaquette curl. -/
theorem exists_curl01 (A : Bond L → ℝ) (l p : ℕ) (hlp : l ≤ p)
    (hl : flux (component A 1) l = 0)
    (hb : coarseFlux (component A 1) p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L, curlValue A (plaq01 L x t) ≠ 0 := by
  simpa only [curl01] using
    exists_curl_of_coarseFlux (shift1 L) (component A 0) (component A 1) l p hlp hl hb

theorem exists_curl02 (A : Bond L → ℝ) (l p : ℕ) (hlp : l ≤ p)
    (hl : flux (component A 2) l = 0)
    (hb : coarseFlux (component A 2) p ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L, curlValue A (plaq02 L x t) ≠ 0 := by
  simpa only [curl02] using
    exists_curl_of_coarseFlux (shift2 L) (component A 0) (component A 2) l p hlp hl hb

/-- The collar hypothesis can be supplied by zero level-zero rows. -/
theorem flux_zero_of_layer_zero (A : Bond L → ℝ) (μ : Fin 3) (l : ℕ)
    (h : ∀ t : Slice L, A (site L l t,μ) = 0) : flux (component A μ) l = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  exact h t

#print axioms Slice
#print axioms site
#print axioms site_zero
#print axioms site_one
#print axioms site_two
#print axioms shift1
#print axioms shift2
#print axioms shift_site_zero
#print axioms shift_site_one
#print axioms shift_site_two
#print axioms component
#print axioms plaq01
#print axioms plaq02
#print axioms curl01
#print axioms curl02
#print axioms sum_curl01
#print axioms sum_curl02
#print axioms exists_curl01
#print axioms exists_curl02
#print axioms flux_zero_of_layer_zero
end AdalyFormal.Round10.Nonvanishing.TorusFlux

namespace AdalyFormal.Round10.Nonvanishing.Coordinate
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
variable {L : PeriodicLatticeExtent}
section Cube
variable {E : Type*} [AddCommGroup E]
def cube (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) : E :=
  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, g (a + i) (b + j) (c + k)
end Cube

def mkS (L : PeriodicLatticeExtent) (a b c : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨(![a, b, c] μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem mkS_val (a b c : ℕ) (μ : Fin 3) : ((mkS L a b c) μ).val = (![a, b, c] μ) % (L μ + 1) := rfl

theorem mkS_val0 (a b c : ℕ) : ((mkS L a b c) 0).val = a % (L 0 + 1) := rfl

theorem mkS_val1 (a b c : ℕ) : ((mkS L a b c) 1).val = b % (L 1 + 1) := rfl

theorem mkS_val2 (a b c : ℕ) : ((mkS L a b c) 2).val = c % (L 2 + 1) := rfl

theorem mkS_eta (x : PeriodicLatticeSite L) : mkS L (x 0).val (x 1).val (x 2).val = x := by
  funext μ
  apply Fin.ext
  rw [mkS_val]
  fin_cases μ
  · simp [Nat.mod_eq_of_lt (x 0).isLt]
  · simp [Nat.mod_eq_of_lt (x 1).isLt]
  · simp [Nat.mod_eq_of_lt (x 2).isLt]

theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  simp [periodicLatticeShift, Fin.val_add]

theorem shift_val_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν) = x ν := by
  simp [periodicLatticeShift, Function.update_of_ne h]

theorem shift_mkS1 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 1 = mkS L a (b + 1) c := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 1
  · subst h
    rw [shift_val_self, mkS_val1, mkS_val1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all

theorem mkS_mem_block (Y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1)
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) :
    mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k) ∈ blockOf Y n := by
  rw [mem_blockOf]
  intro μ
  have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
  fin_cases μ
  · simp only [Fin.zero_eta, mkS_val0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.mk_one, mkS_val1]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.reduceFinMk, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem sum_block_eq_cube {E : Type*} [AddCommGroup E] [Module ℝ E] (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (F : PeriodicLatticeSite L → E) :
    ∑ x ∈ blockOf Y n, F x = cube (fun a b c => F (mkS L a b c)) n (Y 0).val (Y 1).val (Y 2).val := by
  classical
  unfold cube
  have e : ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, F (mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k))
      = ∑ p ∈ range n ×ˢ (range n ×ˢ range n), F (mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2)) := by
    simp only [Finset.sum_product]
  rw [e]
  symm
  refine Finset.sum_nbij' (fun p => mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2))
    (fun x => ((x 0).val - (Y 0).val, (x 1).val - (Y 1).val, (x 2).val - (Y 2).val)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mkS_mem_block Y n hfit _ _ _ hp.1 hp.2.1 hp.2.2
  · intro x hx
    rw [mem_blockOf] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have := hx 0; omega
    · have := hx 1; omega
    · have := hx 2; omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
    simp only [mkS_val0, mkS_val1, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp
  · intro x hx
    rw [mem_blockOf] at hx
    have a0 := hx 0; have a1 := hx 1; have a2 := hx 2
    have e0 : (Y 0).val + ((x 0).val - (Y 0).val) = (x 0).val := by omega
    have e1 : (Y 1).val + ((x 1).val - (Y 1).val) = (x 1).val := by omega
    have e2 : (Y 2).val + ((x 2).val - (Y 2).val) = (x 2).val := by omega
    simp only [e0, e1, e2]
    exact mkS_eta x
  · intro p hp
    rfl

#print axioms cube
#print axioms mkS
#print axioms mkS_val
#print axioms mkS_val0
#print axioms mkS_val1
#print axioms mkS_val2
#print axioms mkS_eta
#print axioms shift_val_self
#print axioms shift_val_ne
#print axioms shift_mkS1
#print axioms mkS_mem_block
#print axioms sum_block_eq_cube
end AdalyFormal.Round10.Nonvanishing.Coordinate

namespace AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (qOnePathSum longBondValue_ell2)
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0 mkS_val1 mkS_val2 sum_block_eq_cube cube shift_mkS1)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux

variable {L : PeriodicLatticeExtent} {ny nz : ℕ}

/-- Four transverse fine offsets per physical coarse cell. -/
def tiling (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1) :
    (Fin ny × Fin nz) × (Fin 2 × Fin 2) ≃ Slice L :=
  (Equiv.prodProdProdComm (Fin ny) (Fin nz) (Fin 2) (Fin 2)).trans
    ((finProdFinEquiv.trans (finCongr hy)).prodCongr
      (finProdFinEquiv.trans (finCongr hz)))

theorem site_tiling (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (x : ℕ) (c : Fin ny × Fin nz) (o : Fin 2 × Fin 2) :
    site L x (tiling hy hz (c,o)) = mkS L x (2*c.1.val+o.1.val) (2*c.2.val+o.2.val) := by
  funext μ
  apply Fin.ext
  fin_cases μ
  · simp [mkS]
  · have hlt : 2*c.1.val+o.1.val < L 1+1 := by omega
    change o.1.val + 2*c.1.val = (2*c.1.val+o.1.val) % (L 1+1)
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · have hlt : 2*c.2.val+o.2.val < L 2+1 := by omega
    change o.2.val + 2*c.2.val = (2*c.2.val+o.2.val) % (L 2+1)
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- Actual even-site coarse bond, not a substituted one-cell torus. -/
def row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (c : Fin ny × Fin nz) : CoarseBond L 2 :=
  (⟨mkS L p (2*c.1.val) (2*c.2.val),by
    rw [mem_CoarseLattice]
    intro μ
    have hpy : 2*c.1.val < L 1+1 := by omega
    have hpz : 2*c.2.val < L 2+1 := by omega
    fin_cases μ
    · simpa [mkS_val0,Nat.mod_eq_of_lt (show p < L 0+1 by omega)] using heven
    · simp [mkS_val1,Nat.mod_eq_of_lt hpy]
    · simp [mkS_val2,Nat.mod_eq_of_lt hpz]⟩,1)

/-- The exact frozen normalized scalar blocking row equals the finite-array row. -/
theorem qOnePathSum_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (A : Bond L → ℝ) (c : Fin ny × Fin nz) :
    qOnePathSum 2 A (row hy hz p hp heven c) =
      blockRow (tiling hy hz) (shift1 L) (component A 1) p c := by
  have hp0 : p < L 0+1 := by omega
  have hy0 : 2*c.1.val < L 1+1 := by omega
  have hz0 : 2*c.2.val < L 2+1 := by omega
  have hfit : ∀ μ, ((mkS L p (2*c.1.val) (2*c.2.val)) μ).val+2 ≤ L μ+1 := by
    intro μ
    fin_cases μ
    · simpa [mkS_val0,Nat.mod_eq_of_lt hp0] using hp
    · change (2*c.1.val) % (L 1+1) + 2 ≤ L 1+1
      rw [Nat.mod_eq_of_lt hy0]
      omega
    · change (2*c.2.val) % (L 2+1) + 2 ≤ L 2+1
      rw [Nat.mod_eq_of_lt hz0]
      omega
  simp only [qOnePathSum,row,longBondValue_ell2]
  rw [sum_block_eq_cube _ 2 hfit]
  simp only [mkS_val0,mkS_val1,mkS_val2,Nat.mod_eq_of_lt hp0,
    Nat.mod_eq_of_lt hy0,Nat.mod_eq_of_lt hz0]
  simp only [blockRow,component,← shift_site_one,site_tiling,shift_mkS1]
  simp [cube,Finset.sum_range_succ,Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

/-- Sum over all physical even transverse cells, with the exact level-one factor. -/
theorem sum_qOnePathSum_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (A : Bond L → ℝ) :
    ∑ c : Fin ny × Fin nz, qOnePathSum 2 A (row hy hz p hp heven c) =
      coarseFlux (component A 1) p := by
  simp_rw [qOnePathSum_row]
  exact sum_blockRow _ _ _ _

/-- A nonzero sum of genuine scalar Q1 rows forces nonzero actual curl. -/
theorem exists_curl_of_qOnePathSum (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0) (A : Bond L → ℝ)
    (l : ℕ) (hlp : l ≤ p) (hl : flux (component A 1) l = 0)
    (hb : (∑ c : Fin ny × Fin nz, qOnePathSum 2 A (row hy hz p hp heven c)) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L,
      AdalyFormal.Balaban.LatticeOperators.curlValue A (plaq01 L x t) ≠ 0 := by
  apply exists_curl01 A l p hlp hl
  simpa [sum_qOnePathSum_row] using hb

open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

/-- Functionals commute with the actual flat Q1 jet, including its 1/2 factor. -/
theorem sum_Q1jet_row (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : Bond L → SuTwo) (φ : SuTwo →ₗ[ℝ] ℝ) :
    ∑ c : Fin ny × Fin nz, φ (Q1jet 2 flatCfg A (row hy hz p hp heven c)) =
      coarseFlux (component (fun e => φ (A e)) 1) p := by
  simp_rw [Q1jet_flat 2 (by decide) hdiv,AdalyFormal.IngredientFamily.q1SU2_functional]
  exact sum_qOnePathSum_row hy hz p hp heven _

/-- A level-one full-tower row is exactly the normalized Q1 jet. -/
theorem Qfull_level_one (G : TowerGeom L) (hG : G.ell = 2) (U : Cfg L)
    (A : BondFnL2 L) (p : BIdx G) (hp : (p.1 : ℕ) = 1)
    (c : CoarseBond L 2) (hc : p.2.1 = (c.1.1,c.2)) :
    QfullOf G U A p = Q1jet 2 U (fun e => A e) c := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 = _
  rw [hc,hp,QlinB_apply]
  simp only [QlinCompL,bgTower,AdalyFormal.Balaban.UbarTowerCov.UbarTower,
    hG,pow_zero,pow_one,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply]
  rfl

/-- Exact sum identity for genuine frozen full-tower rows on a transverse layer.
Only row membership/indexing is supplied; no Fourier or source-column formula is assumed. -/
theorem sum_Qfull_level_one (G : TowerGeom L) (hG : G.ell = 2)
    (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : BondFnL2 L) (φ : SuTwo →ₗ[ℝ] ℝ)
    (idx : Fin ny × Fin nz → BIdx G)
    (hi : ∀ c, ((idx c).1 : ℕ) = 1)
    (hb : ∀ c, (idx c).2.1 = ((row hy hz p hp heven c).1.1,1)) :
    ∑ c : Fin ny × Fin nz, φ (QfullOf G flatCfg A (idx c)) =
      coarseFlux (component (fun e => φ (A e)) 1) p := by
  have he (c : Fin ny × Fin nz) :=
    Qfull_level_one G hG flatCfg A (idx c) (hi c) (row hy hz p hp heven c) (hb c)
  simp_rw [he]
  exact sum_Q1jet_row hy hz p hp heven hdiv _ φ

/-- Nonzero aggregated genuine top jet implies nonzero curl of a constrained lift.
The constraint equality is the QH=1 application, kept explicit here. -/
theorem exists_curl_of_constrained_jet (G : TowerGeom L) (hG : G.ell = 2)
    (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : BondFnL2 L) (φ : SuTwo →ₗ[ℝ] ℝ)
    (z : FSp G) (idx : Fin ny × Fin nz → BIdx G)
    (hi : ∀ c, ((idx c).1 : ℕ) = 1)
    (hb : ∀ c, (idx c).2.1 = ((row hy hz p hp heven c).1.1,1))
    (hQ : QfullOf G flatCfg A = z)
    (l : ℕ) (hlp : l ≤ p)
    (hl : flux (component (fun e => φ (A e)) 1) l = 0)
    (hzjet : (∑ c : Fin ny × Fin nz, φ (z (idx c))) ≠ 0) :
    ∃ x, l ≤ x ∧ x < p+1 ∧ ∃ t : Slice L,
      AdalyFormal.Balaban.LatticeOperators.curlValue (fun e => φ (A e)) (plaq01 L x t) ≠ 0 := by
  apply exists_curl01 (fun e => φ (A e)) l p hlp hl
  have he := sum_Qfull_level_one G hG hy hz p hp heven hdiv A φ idx hi hb
  rw [hQ] at he
  exact he ▸ hzjet

/-- The level-zero constraint is literally the fine bond value. -/
theorem Qfull_level_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (p : BIdx G) (hp : (p.1 : ℕ) = 0) : QfullOf G U A p = A p.2.1 := by
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 = _
  have he : QlinB G U p.1 A = A := by simpa only [hp] using QlinB_zero G U A
  rw [he]
  simp [hp]

/-- The actual quadratic jet is zero at every level-zero row. -/
theorem C2full_level_zero (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L)
    (p : BIdx G) (hp : (p.1 : ℕ) = 0) : C2fullOf G U A p = 0 := by
  have he : C2rawB G U p.1 A = 0 := by
    rw [C2rawB_eq]
    simp only [hp,C2CompL_zero,map_zero]
  change (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 = 0
  rw [he]
  simp

/-- QH=1 and the zero level-zero jet give the collar flux hypothesis automatically,
provided the collar bonds are identified as actual level-zero rows. -/
theorem collar_flux_zero (G : TowerGeom L) (U : Cfg L) (A v : BondFnL2 L)
    (hQ : QfullOf G U A = C2fullOf G U v) (φ : SuTwo →ₗ[ℝ] ℝ)
    (l : ℕ) (μ : Fin 3) (idx0 : Slice L → BIdx G)
    (hi : ∀ t, ((idx0 t).1 : ℕ) = 0)
    (hb : ∀ t, (idx0 t).2.1 = (site L l t,μ)) :
    flux (component (fun e => φ (A e)) μ) l = 0 := by
  apply flux_zero_of_layer_zero
  intro t
  have he := congrArg (fun z : FSp G => z (idx0 t)) hQ
  rw [Qfull_level_zero G U A (idx0 t) (hi t),
    C2full_level_zero G U v (idx0 t) (hi t),hb] at he
  rw [he,map_zero]

#print axioms Qfull_level_zero
#print axioms C2full_level_zero
#print axioms collar_flux_zero
#print axioms sum_Q1jet_row
#print axioms Qfull_level_one
#print axioms sum_Qfull_level_one
#print axioms exists_curl_of_constrained_jet
#print axioms tiling
#print axioms site_tiling
#print axioms row
#print axioms qOnePathSum_row
#print axioms sum_qOnePathSum_row
#print axioms exists_curl_of_qOnePathSum
end AdalyFormal.Round10.Nonvanishing.PhysicalBlocking
namespace AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

#print axioms dilLu
#print axioms dilTower
#print axioms dil_unit_size
#print axioms dil_fine_size
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round10.Nonvanishing.DilatedFlux

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0)
open AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

abbrev L (q R : ℕ) := scaleUp 2 1 (dilLu q R)
abbrev G (q R : ℕ) := geomOf 2 1 (dilTower q R)
def blockCount (q R : ℕ) : ℕ := 4*q*(R+1)
def blockBase (q R j : ℕ) : ℕ := 2*(R*q)+4*q+2*j

theorem side_one {q : ℕ} (hq : 0 < q) (R : ℕ) : (4*q)*2 = L q R 1+1 := by
  rw [dil_fine_size hq,if_neg (show (1 : Fin 3) ≠ 0 by decide)]
  omega

theorem side_two {q : ℕ} (hq : 0 < q) (R : ℕ) : (4*q)*2 = L q R 2+1 := by
  rw [dil_fine_size hq,if_neg (show (2 : Fin 3) ≠ 0 by decide)]
  omega

theorem blockBase_even (q R j : ℕ) : blockBase q R j % 2 = 0 := by
  simp [blockBase,Nat.add_mod,Nat.mul_mod]

theorem blockBase_bounds {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R) :
    2*(R*q)+4*q ≤ blockBase q R j ∧
    blockBase q R j+2 ≤ 10*(R*q)+12*q ∧
    blockBase q R j+2 ≤ L q R 0+1 := by
  have hc : blockCount q R = 4*(R*q)+4*q := by unfold blockCount; ring
  rw [hc] at hj
  rw [dil_fine_size hq]
  norm_num
  unfold blockBase
  omega

theorem two_dvd_sides {q : ℕ} (hq : 0 < q) (R : ℕ) : ∀ μ, 2 ∣ L q R μ+1 := by
  intro μ
  rw [dil_fine_size hq]
  split <;> omega

/-- Actual top-level row at every physical even transverse site. -/
def topIdx {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) : BIdx (G q R) :=
  let r := row (side_one hq R) (side_two hq R) (blockBase q R j)
    (blockBase_bounds hq hj).2.2 (blockBase_even q R j) c
  ⟨⟨1,by change 1 < 1+1; decide⟩,⟨(r.1.1,1),by
    refine ⟨Or.inl ?_,?_⟩
    · change (∀ μ : Fin 3, 2^1 ∣ (r.1.1 μ).val) ∧ r.1.1 ∈ (dilTower q R).Om 1 ∧
        r.1.1 ∉ (dilTower q R).Om 2
      refine ⟨?_,?_,?_⟩
      · have he := mem_CoarseLattice.mp r.1.2
        intro μ
        simpa using Nat.dvd_of_mod_eq_zero (he μ)
      · have hbounds := blockBase_bounds hq hj
        change 2*(R*q)+4*q ≤ (r.1.1 0).val ∧ (r.1.1 0).val < 10*(R*q)+12*q
        change 2*(R*q)+4*q ≤ blockBase q R j % (L q R 0+1) ∧
          blockBase q R j % (L q R 0+1) < 10*(R*q)+12*q
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp [dilTower]
    · intro hh
      rcases hh with hh | hh
      · exact not_OmGe_of_lt (G := G q R) (j := 2) (by change 1 < 2; decide) _ hh
      · exact not_OmGe_of_lt (G := G q R) (j := 2) (by change 1 < 2; decide) _ hh⟩⟩

@[simp] theorem topIdx_level {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) : ((topIdx hq hj c).1 : ℕ) = 1 := rfl

@[simp] theorem topIdx_bond {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (c : Fin (4*q) × Fin (4*q)) :
    (topIdx hq hj c).2.1 =
      ((row (side_one hq R) (side_two hq R) (blockBase q R j)
        (blockBase_bounds hq hj).2.2 (blockBase_even q R j) c).1.1,1) := rfl

/-- Omega_1 cannot reach the left collar through a positive-size block. -/
theorem not_OmGe_one {q R : ℕ} {x : PeriodicLatticeSite (L q R)}
    (hx : (x 0).val < 2*(R*q)+4*q) : ¬ OmGe (G q R) 1 x := by
  rintro ⟨i,hi,hik,y,hy,hyx⟩
  have he : i = 1 := by change i ≤ 1 at hik; omega
  subst i
  have hy0 : 2*(R*q)+4*q ≤ (y 0).val := hy.2.1.1
  have := (hyx 0).1
  omega

/-- The direction-1 bonds at the first Omega_0 layer are genuine level-zero rows. -/
def collarIdx {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : BIdx (G q R) :=
  ⟨⟨0,by change 0 < 1+1; decide⟩,⟨(site (L q R) (4*q) t,1),by
    have hmul : 0 < R*q := Nat.mul_pos hR hq
    have hside : L q R 0+1 = 12*(R*q)+16*q := by
      simpa [L] using dil_fine_size hq R 0
    have hx : (site (L q R) (4*q) t 0).val = 4*q := by
      change (4*q) % (L q R 0+1) = 4*q
      rw [Nat.mod_eq_of_lt (by omega)]
    refine ⟨Or.inl ?_,?_⟩
    · change (∀ μ, 2^0 ∣ (site (L q R) (4*q) t μ).val) ∧
        site (L q R) (4*q) t ∈ (dilTower q R).Om 0 ∧
        site (L q R) (4*q) t ∉ (dilTower q R).Om 1
      refine ⟨by simp,?_,?_⟩
      · change 4*q ≤ (site (L q R) (4*q) t 0).val ∧
          (site (L q R) (4*q) t 0).val < 12*(R*q)+12*q
        rw [hx]
        omega
      · change ¬ (2*(R*q)+4*q ≤ (site (L q R) (4*q) t 0).val ∧
          (site (L q R) (4*q) t 0).val < 10*(R*q)+12*q)
        rw [hx]
        omega
    · intro hh
      rcases hh with hh | hh
      · exact not_OmGe_one (by rw [hx]; omega) hh
      · apply not_OmGe_one (x := coarseShift (site (L q R) (4*q) t) 1 1) _ hh
        simpa [coarseShift,site_zero] using
          (show (4*q) % (L q R 0+1) < 2*(R*q)+4*q by
            change (site (L q R) (4*q) t 0).val < _
            rw [hx]; omega)⟩⟩

@[simp] theorem collarIdx_level {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : ((collarIdx hq hR t).1 : ℕ) = 0 := rfl

@[simp] theorem collarIdx_bond {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (t : Slice (L q R)) : (collarIdx hq hR t).2.1 = (site (L q R) (4*q) t,1) := rfl

/-- Every plaquette located between this collar and the selected top block lies inside Omega_0. -/
theorem plaq01_in {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hj : j < blockCount q R) {x : ℕ} (hxl : 4*q ≤ x) (hxp : x < blockBase q R j+1)
    (t : Slice (L q R)) : plaq01 (L q R) x t ∈ plaqIn ((dilTower q R).Om 0) := by
  have hbounds := blockBase_bounds hq hj
  have hmul : 0 < R*q := Nat.mul_pos hR hq
  have hside : L q R 0+1 = 12*(R*q)+16*q := by
    simpa [L] using dil_fine_size hq R 0
  have hx : x < L q R 0+1 := by omega
  have hx1 : x+1 < L q R 0+1 := by omega
  simp [plaqIn,periodicPlaquetteBoundaryEdges,plaq01,dilTower,
    shift_site_zero,shift_site_one,site_zero,
    Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hx1]
  omega

/-- Physical sum of the actual quadratic top jet, retaining its 1/2 normalization. -/
noncomputable def jetAggregate {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (φ : SuTwo →ₗ[ℝ] ℝ) (v : BondFnL2 (L q R)) : ℝ :=
  ∑ c : Fin (4*q) × Fin (4*q), φ (C2fullOf (G q R) flatCfg v (topIdx hq hj c))

/-- For the actual dilated geometry, a nonzero aggregated top jet detects localized curl.
This theorem does NOT assert that a vacuum crossing vector has a nonzero aggregate. -/
theorem localized_curl_of_jetAggregate {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hj : j < blockCount q R) (φ : SuTwo →ₗ[ℝ] ℝ) (A v : BondFnL2 (L q R))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v)
    (hne : jetAggregate hq hj φ v ≠ 0) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), curlValue (fun e => φ (A e)) p ≠ 0 := by
  have hz := collar_flux_zero (G q R) flatCfg A v hQ φ (4*q) 1
    (collarIdx hq hR) (collarIdx_level hq hR) (collarIdx_bond hq hR)
  obtain ⟨x,hxl,hxp,t,ht⟩ := exists_curl_of_constrained_jet (G q R) rfl
    (side_one hq R) (side_two hq R) (blockBase q R j) (blockBase_bounds hq hj).2.2
    (blockBase_even q R j) (two_dvd_sides hq R) A φ (C2fullOf (G q R) flatCfg v)
    (topIdx hq hj) (topIdx_level hq hj) (topIdx_bond hq hj) hQ (4*q)
    (by unfold blockBase; omega) hz hne
  exact ⟨plaq01 (L q R) x t,plaq01_in hq hR hj hxl hxp t,ht⟩

open scoped RealInnerProductSpace
open AdalyFormal.Balaban.SuTwoInner (pauliE3)

noncomputable def neutralFunctional : SuTwo →ₗ[ℝ] ℝ where
  toFun X := ⟪pauliE3,X⟫
  map_add' _ _ := inner_add_right _ _ _
  map_smul' _ _ := inner_smul_right _ _ _

/-- A concrete remaining per-vector nondegeneracy target, not asserted here. -/
def TopJetDetected {q : ℕ} (hq : 0 < q) (R : ℕ) (u : ↥(bondSupp (G q R))) : Prop :=
  ∃ j : ℕ, ∃ hj : j < blockCount q R,
    jetAggregate hq hj neutralFunctional
      (Wop (G q R) flatCfg 1 (iE (G q R) u)) ≠ 0

/-- The missing jet nondegeneracy suffices for the neutral localized curl criterion. -/
theorem neutral_localized_curl_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (A : BondFnL2 (L q R)) (u : ↥(bondSupp (G q R)))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg
      (Wop (G q R) flatCfg 1 (iE (G q R) u)))
    (hjet : TopJetDetected hq R u) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), curlValue (fun e => ⟪pauliE3,A e⟫) p ≠ 0 := by
  obtain ⟨j,hj,hne⟩ := hjet
  exact localized_curl_of_jetAggregate hq hR hj neutralFunctional A
    (Wop (G q R) flatCfg 1 (iE (G q R) u)) hQ hne

#print axioms neutralFunctional
#print axioms TopJetDetected
#print axioms neutral_localized_curl_of_topJet
#print axioms L
#print axioms G
#print axioms blockCount
#print axioms blockBase
#print axioms side_one
#print axioms side_two
#print axioms blockBase_even
#print axioms blockBase_bounds
#print axioms two_dvd_sides
#print axioms topIdx
#print axioms topIdx_level
#print axioms topIdx_bond
#print axioms not_OmGe_one
#print axioms collarIdx
#print axioms collarIdx_level
#print axioms collarIdx_bond
#print axioms plaq01_in
#print axioms jetAggregate
#print axioms localized_curl_of_jetAggregate
end AdalyFormal.Round10.Nonvanishing.DilatedFlux

/-! Combined actual-operator application of the physical transverse-flux theorem.
The nonzero jet and full flat N unit remain explicit hypotheses. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.JetDetection
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Nonvanishing.DilatedFlux

/-- The fixed norm-one diagonal Pauli coordinate, as a real linear functional. -/
def neutralFunctional : SuTwo →ₗ[ℝ] ℝ where
  toFun := neutralCoord
  map_add' := fun x y => inner_add_right pauliE3 x y
  map_smul' := by
    intro c x
    change ⟪pauliE3, c • x⟫ = c * ⟪pauliE3, x⟫
    exact inner_smul_right _ _ _

/-- Sum of the genuine normalized top jet over all physical even transverse cells.
There is no cell-isometry or cell-normalization assumption in this definition. -/
def physicalJetAggregate {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (u : TwistSpace q R) : ℝ :=
  jetAggregate hq hj neutralFunctional
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) u))

/-- The source-column recurrence is not needed: an aggregated nonzero actual jet
forces detection by an allowed interior profile via the FULL constrained lift. -/
theorem curlDetected_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) : CurlDetected q R u := by
  let A := iE (geomOf 2 1 (dilTower q R)) ((flatData q R).H (vacJet q R u))
  let v := Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1
    (iE (geomOf 2 1 (dilTower q R)) u)
  have hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v :=
    liftJet_Q q R hN u
  obtain ⟨p, hp, hc⟩ := localized_curl_of_jetAggregate hq hR hj neutralFunctional A v hQ hne
  exact ⟨p, hp, hc⟩

/-- The specific physical adaptive profile has strictly positive explicit coupling. -/
theorem adaptive_pos_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) :
    0 < profileCoupling q R (responseProfile q R u) u :=
  (adaptive_pos_iff q R u).mpr (curlDetected_of_physicalJet hq hR hN hj u hne)

/-- A free profile exists, but this does not choose one common profile for a
higher-dimensional kernel. Assembly's whole-kernel criterion is still required. -/
theorem exists_profile_of_physicalJet {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hne : physicalJetAggregate hq hj u ≠ 0) :
    ∃ f, profileCoupling q R f u ≠ 0 :=
  (exists_profile_iff_curlDetected q R u).mpr (curlDetected_of_physicalJet hq hR hN hj u hne)

/-- The two tracks use the same physical aggregate, definitionally. -/
theorem topJetDetected_iff {q : ℕ} (hq : 0 < q) (R : ℕ) (u : TwistSpace q R) :
    TopJetDetected hq R u ↔ ∃ j : ℕ, ∃ hj : j < blockCount q R,
      physicalJetAggregate hq hj u ≠ 0 := Iff.rfl

/-- Final joint hand-off: the only source-detection input left is the genuine
crossing-jet nondegeneracy; no source-column or normalization premise remains. -/
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (u : TwistSpace q R) (hjet : TopJetDetected hq R u) : CurlDetected q R u := by
  obtain ⟨j, hj, hne⟩ := (topJetDetected_iff hq R u).mp hjet
  exact curlDetected_of_physicalJet hq hR hN hj u hne

#print axioms topJetDetected_iff
#print axioms curlDetected_of_topJet
#print axioms neutralFunctional
#print axioms physicalJetAggregate
#print axioms curlDetected_of_physicalJet
#print axioms adaptive_pos_of_physicalJet
#print axioms exists_profile_of_physicalJet
end AdalyFormal.Round10.Dictionary.JetDetection
namespace AdalyFormal.Round3.Guarded.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)


end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h

theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R) := by
  have hp : 4*q ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by ring⟩
  have hq' : 4*q ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by ring⟩
  have hlo : 2*q ∣ 4*q := ⟨2, by ring⟩
  have hhi : 2*q ∣ 12*(R*q)+12*q := ⟨6*R+6, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
      omega
    · simp [dilTower, h0] at hx
  · intro j hj
    simp [dilTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [dil_fine_size hq]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp only [bigSide, pow_zero, pow_one, mul_one, hμ, ↓reduceIte]
    · exact ⟨6*R+8, by ring⟩
    · exact ⟨4, by ring⟩
    · exact ⟨3*R+4, by ring⟩
    · exact ⟨2, by ring⟩
  · intro j hj x hx y hy
    interval_cases j
    · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change 4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q
      apply iv_block (by omega : 0 < 2*q) hlo hhi _ hx
      simpa [bigSide] using hy 0
    · change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      apply iv_block (by omega : 0 < 4*q) hp hq' _ hx
      simpa [bigSide, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy 0
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hxb := dil_fine_bound hq R x
      have hpd := zero_coord_le_pdist x y
      simp only [dil_fine_size hq, ↓reduceIte] at hpd
      have hcoord : 2*(R*q) < pcd (12*(R*q)+16*q) (x 0).val (y 0).val := by
        unfold pcd; split_ifs <;> omega
      have heq : R * bigSide (2*q) 2 0 = 2*(R*q) := by simp [bigSide]; ring
      rw [heq]; exact lt_of_lt_of_le hcoord hpd
    · simp [dilTower] at hy
  · intro x
    change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ↔ _
    have hrm : R*(2*q) = 2*(R*q) := by ring
    constructor
    · intro hx
      let v := if (x 0).val < 2*(R*q)+4*q then 2*(R*q)+4*q
        else if (x 0).val < 10*(R*q)+12*q then (x 0).val else 10*(R*q)+12*q-1
      have hv : v < scaleUp 2 1 (dilLu q R) 0 + 1 := by
        rw [dil_fine_size hq, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2*(R*q)+4*q ≤ v ∧ v < 10*(R*q)+12*q
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, dil_fine_size hq, ↓reduceIte, hrm]
          have hc := pcd_clamp (N := 12*(R*q)+16*q) (a := (x 0).val)
            (lo := 2*(R*q)+4*q) (hi := 10*(R*q)+12*q) (D := 2*(R*q))
            (by omega) (by omega) (dil_fine_bound hq R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ; rw [Function.update_of_ne hμ, pcd_self']
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [dil_fine_size hq, ↓reduceIte, hrm] at hcoord
      have hn := pcd_near (dil_fine_bound hq R z) hy
        (show 2*(R*q) ≤ 2*(R*q)+4*q by omega)
        (show 10*(R*q)+12*q+2*(R*q) ≤ 12*(R*q)+16*q by omega) hcoord
      have hzmem : 4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q := by omega
      exact iv_block (by omega : 0 < 2*q) hlo hhi (hz 0).symm hzmem


end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
variable {L : PeriodicLatticeExtent}
theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl

theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl

theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_G_ell (q R : ℕ) : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl

theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]

theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)


end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## J. The flat localized carrier of the dilated tower is positive definite

At the trivial background `⟪x, B x⟫ = ‖χ curl x‖² + ‖T x‖² + Σ a ℓʲ ‖Q x‖²` (`B` the localized
carrier).  If it vanishes, `x` is curl-free on the plaquettes of `Ω₀`, vanishes on every bond not
touching `Ω₁` (level-0 rows of `Q`), and has vanishing level-1 rows.  Integrating `x` along the
longitudinal lines from the left boundary gives a site field `ξ` with `x = D ξ` on the bonds
before the right edge; the level-1 rows telescope along the longitudinal chain of blocks from the
left collar (where `ξ = 0`) to the right collar (where `ξ` is a transverse constant), so the
constant is `0`, `ξ ∈ N(Q')` and `x = D ξ` everywhere; then `T (D ξ) = 0` forces `D ξ = 0`
(the frozen `final_step` argument, copied). -/
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

/-! ### Frozen `NsPtD2.final_step` (outside the `DrEquiv` closure), copied verbatim. -/

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]

theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]

theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

/-! ### Coordinates of the dilated tower -/

variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h

theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]

theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega

theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega

theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl

theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl

theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]

theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]

theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]

theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega

theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega

/-! ### The kernel argument -/

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega

include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb

/-- the site with longitudinal coordinate replaced by `u`. -/
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))

omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu

omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]

omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]

omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]

omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]

omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]

omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]

/-- the longitudinal potential. -/
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)

include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]

include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]

include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]

include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega

include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk

/-- the right-edge value of the potential, a function of the transverse coordinates. -/
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))

include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]

omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]

include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h

omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]

include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]

omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]

include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum

include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)

include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h

include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]

include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel

include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## K. Assembly: the soft premise `InteriorSoft` of round 1 holds -/
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

/-- The flat localized carrier form is a sum of three squares (frozen `NsPtD1.flat_ginv_form`,
outside the `DrEquiv` closure, restated for the pinned localized assembly). -/
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl

/-- The flat localized carrier of the dilated tower is positive definite. -/
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA

theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩

end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2



namespace AdalyFormal.Round13.Detection
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.KKT

/-- The genuine full constraint matrix in the top-jet dictionary is a unit.
This is a flat-point prerequisite, not crossing-jet nonvanishing. -/
theorem flat_N_unit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    IsUnit (N (flatData q R)) := by
  let D := flatData q R
  have hL : D.Laws := dataS_laws selIn selIn _
  have hB : IsUnit D.Ginv := dil_flat_unit hq (by omega)
  have hp : AdalyFormal.D1Literal.PSD D.Ginv := by
    intro x
    by_cases hx : x = 0
    · rw [hx, inner_zero_left]
    · exact (dil_flat_pos hq (by omega) x hx).le
  have hQs : Function.Injective D.Qs :=
    dil_Qs_inj hq (by omega) (dil_admissible hq hR)
  obtain ⟨m, hm, hmc⟩ := AdalyFormal.D1Literal.psd_coercive
    D.Ginv (D.Ginv_symm hL) hp hB
  exact isUnit_Q_inv_Qs (D.Ginv_symm hL) hm hmc D.Q_adj hQs

/-- In particular, the nested dyadic/even family has no missing flat N guard. -/
theorem cofinal_flat_N_units :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      IsUnit (N (flatData (2^j) R)) := by
  intro j₀
  refine ⟨j₀, le_rfl, fun R₀ => ?_⟩
  let R := 2 * (R₀ + 9)
  have he : 2 ∣ R := dvd_mul_right 2 (R₀ + 9)
  have h18 : 18 ≤ R := by dsimp [R]; omega
  exact ⟨R, by dsimp [R]; omega, he, h18, flat_N_unit (by positivity) he h18⟩

#print axioms flat_N_unit
#print axioms cofinal_flat_N_units
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs_inj
end AdalyFormal.Round13.Detection

namespace AdalyFormal.Round13.Detection
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.JetDetection
open AdalyFormal.Round10.Nonvanishing.DilatedFlux

/-- The full flat N-unit guard is discharged, for all required scales/radii.
The genuine nonzero top jet is still an explicit hypothesis. -/
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (u : TwistSpace q R) (hjet : TopJetDetected hq R u) :
    CurlDetected q R u :=
  AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet hq (by omega)
    (flat_N_unit hq hR hR18) u hjet

/-- A sign-controlled sum of the ACTUAL normalized frozen top row suffices.
This is a sufficient sign interface, not a proof that the crossing satisfies it. -/
theorem curlDetected_of_signed_top_row {q R j : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (hj : j < blockCount q R)
    (u : TwistSpace q R) (sign : ℝ)
    (hcell : ∀ c : Fin (4*q) × Fin (4*q),
      0 ≤ sign * AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional
        (C2fullOf (G q R) flatCfg
          (Wop (G q R) flatCfg 1 (iE (G q R) u)) (topIdx hq hj c)))
    (hone : ∃ c : Fin (4*q) × Fin (4*q),
      0 < sign * AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional
        (C2fullOf (G q R) flatCfg
          (Wop (G q R) flatCfg 1 (iE (G q R) u)) (topIdx hq hj c))) :
    CurlDetected q R u := by
  apply curlDetected_of_topJet hq hR hR18 u
  refine ⟨j, hj, ?_⟩
  have hp : 0 < sign * jetAggregate hq hj
      AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional
      (Wop (G q R) flatCfg 1 (iE (G q R) u)) := by
    rw [jetAggregate, Finset.mul_sum]
    apply Finset.sum_pos'
    · intro c _
      exact hcell c
    · obtain ⟨c, hc⟩ := hone
      exact ⟨c, Finset.mem_univ c, hc⟩
  intro hz
  rw [hz, mul_zero] at hp
  exact lt_irrefl 0 hp

#print axioms curlDetected_of_topJet
#print axioms curlDetected_of_signed_top_row
end AdalyFormal.Round13.Detection

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

theorem flipMat_mem :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Matrix.det_fin_two]

/-- `w = [[0,1],[-1,0]] ∈ SU(2)`. -/
noncomputable def flipElt : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨!![0, 1; -1, 0], flipMat_mem⟩

/-- The constant gauge transformation by `w`. -/
noncomputable def flipGauge {L : PeriodicLatticeExtent} : GaugeFn L := fun _ => flipElt

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! Exact global-color selection rules for the frozen flat dressed quadratic jet. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Color
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt flipGauge)
open AdalyFormal.Round10.Dictionary.Source (neutralCoord neutral_of_half_fixed)
open AdalyFormal.D1Literal (uθ)

section Quadratic
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

theorem quad_even {Q : X → Y} (hQ : IsQuadMap Q) (x : X) : Q (-x) = Q x := by
  simpa only [neg_one_smul, neg_one_sq, one_smul] using hQ.smul_sq (-1 : ℝ) x

theorem quad_zero {Q : X → Y} (hQ : IsQuadMap Q) : Q 0 = 0 := by
  simpa using hQ.smul_sq (0 : ℝ) (0 : X)

theorem quad_parallelogram {Q : X → Y} (hQ : IsQuadMap Q) (x y : X) :
    Q (x + y) + Q (x - y) = (2 : ℝ) • Q x + (2 : ℝ) • Q y := by
  obtain ⟨B, hB⟩ := hQ
  simp only [hB, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem quad_add_of_invariant {Q : X → Y} (hQ : IsQuadMap Q) (J : X →ₗ[ℝ] X)
    (hJ : ∀ x, Q (J x) = Q x) {x y : X} (hx : J x = x) (hy : J y = -y) :
    Q (x + y) = Q x + Q y := by
  have he : Q (x - y) = Q (x + y) := by
    have h := hJ (x + y)
    simpa only [map_add, hx, hy, ← sub_eq_add_neg] using h
  have h := quad_parallelogram hQ x y
  rw [he] at h
  have hh : (2 : ℝ) • (Q (x + y) - (Q x + Q y)) = 0 := by
    calc
      _ = (Q (x + y) + Q (x + y)) - ((2 : ℝ) • Q x + (2 : ℝ) • Q y) := by module
      _ = 0 := sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by norm_num))

theorem quad_zero_of_anti_fixed {Q : X → Y} (hQ : IsQuadMap Q) (J : X →ₗ[ℝ] X)
    (hJ : ∀ x, Q (J x) = -Q x) {x : X} (hx : J x = x ∨ J x = -x) : Q x = 0 := by
  have hh : Q x = -Q x := by
    rcases hx with hx | hx
    · simpa only [hx] using hJ x
    · simpa only [hx, quad_even hQ] using hJ x
  have h2 : (2 : ℝ) • Q x = 0 := by
    rw [two_smul]
    exact (congrArg (fun y => y + Q x) hh).trans (neg_add_cancel (Q x))
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- On two color lines with zero self-jets, the actual jet is purely mixed. -/
theorem quad_mixed_scaling {Q : X → Y} (hQ : IsQuadMap Q) {x y : X}
    (hx : Q x = 0) (hy : Q y = 0) (a b : ℝ) :
    Q (a • x + b • y) = (a * b) • Q (x + y) := by
  obtain ⟨B, hB⟩ := hQ
  rw [hB] at hx hy
  simp only [hB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hx, hy, smul_zero, zero_add, add_zero]
  module
end Quadratic

variable {L : PeriodicLatticeExtent}

def constGauge (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : GaugeFn L := fun _ => g

theorem const_trivial (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicGaugeTransform (constGauge (L := L) g) (fun _ => 1) = fun _ => 1 := by
  funext b
  change g * 1 * g⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

def halfE (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) :=
  adEL (constGauge (uθ (Real.pi / 2))) G

def flipE (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) := adEL flipGauge G

def flatJet (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) : FSp G :=
  C2fullOf G (fun _ => 1) (Wop G (fun _ => 1) a (iE G u))

theorem flatJet_quad (G : TowerGeom L) (a : ℝ) : IsQuadMap (flatJet G a) :=
  (C2fullOf_quad G (fun _ => 1)).comp_linear
    (((Wop G (fun _ => 1) a).comp (iE G)).toLinearMap)

theorem flatJet_gauge (G : TowerGeom L) (a : ℝ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (u : ↥(bondSupp G)) :
    flatJet G a (adEL (constGauge g) G u) = adFL (constGauge g) G (flatJet G a u) := by
  have hw := Wop_gauge G (constGauge g) (fun _ => 1) a (iE G u)
  have hc := C2fullOf_gauge G (fun _ => 1) (constGauge g)
    (Wop G (fun _ => 1) a (iE G u))
  rw [const_trivial] at hw hc
  unfold flatJet
  rw [iE_adEL, hw, hc]

theorem flip_matrix (X : SuTwo) :
    ((RMap flipElt X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(X : Matrix (Fin 2) (Fin 2) ℂ) 1 1, -(X : Matrix (Fin 2) (Fin 2) ℂ) 1 0;
      -(X : Matrix (Fin 2) (Fin 2) ℂ) 0 1, (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0] := by
  rw [RMap_coe_apply]
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * _ *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem flip_axis : RMap flipElt pauliE3 = -pauliE3 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliE3, AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
    AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal]

theorem half_axis : RMap (uθ (Real.pi / 2)) pauliE3 = pauliE3 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE3, AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_neutral (X : SuTwo) (hX : RMap (uθ (Real.pi / 2)) X = X) :
    RMap flipElt X = -X := by
  rw [neutral_of_half_fixed X hX, map_smul, flip_axis, smul_neg]

theorem two_fixed_zero (X : SuTwo) (hh : RMap (uθ (Real.pi / 2)) X = X)
    (hf : RMap flipElt X = X) : X = 0 := by
  have hn := flip_neutral X hh
  rw [hf] at hn
  have h2 : (2 : ℝ) • X = 0 := by
    rw [two_smul]
    exact (congrArg (fun y => y + X) hn).trans (neg_add_cancel X)
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem halfE_flip_on_fixed (G : TowerGeom L) (u : ↥(bondSupp G)) (hu : halfE G u = u) :
    flipE G u = -u := by
  apply Subtype.ext
  apply PiLp.ext
  intro b
  apply flip_neutral
  exact congrArg (fun v : ↥(bondSupp G) => (v : BondFnL2 L) b) hu

/-- A neutral carrier input has zero FULL quadratic jet, before any source pairing. -/
theorem flatJet_neutral_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = u) : flatJet G a u = 0 := by
  have hh := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hh
  rw [hu] at hh
  have hf := flatJet_gauge G a flipElt u
  change flatJet G a (flipE G u) = _ at hf
  rw [halfE_flip_on_fixed G u hu, quad_even (flatJet_quad G a)] at hf
  apply PiLp.ext
  intro p
  apply two_fixed_zero
  · exact (congrArg (fun v : FSp G => v p) hh).symm
  · exact (congrArg (fun v : FSp G => v p) hf).symm

/-- A charged carrier input has a neutral quadratic jet. -/
theorem flatJet_charged_neutral (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) (p : BIdx G) :
    flatJet G a u p = neutralCoord (flatJet G a u p) • pauliE3 := by
  apply neutral_of_half_fixed
  have hh := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hh
  rw [hu, quad_even (flatJet_quad G a)] at hh
  exact (congrArg (fun v : FSp G => v p) hh).symm

/-- Within the charged carrier, either single real color has zero full jet. -/
theorem flatJet_single_color_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hh : halfE G u = -u) (hf : flipE G u = u ∨ flipE G u = -u) :
    flatJet G a u = 0 := by
  have hhalf := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hhalf
  rw [hh, quad_even (flatJet_quad G a)] at hhalf
  have hflip := flatJet_gauge G a flipElt u
  change flatJet G a (flipE G u) = _ at hflip
  rcases hf with hf | hf
  all_goals
    rw [hf] at hflip
    try rw [quad_even (flatJet_quad G a)] at hflip
    apply PiLp.ext
    intro p
    apply two_fixed_zero
    · exact (congrArg (fun v : FSp G => v p) hhalf).symm
    · exact (congrArg (fun v : FSp G => v p) hflip).symm

end AdalyFormal.Round10.Dictionary.Color
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_even
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_parallelogram
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_add_of_invariant
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_zero_of_anti_fixed
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_mixed_scaling
#print axioms AdalyFormal.Round10.Dictionary.Color.constGauge
#print axioms AdalyFormal.Round10.Dictionary.Color.const_trivial
#print axioms AdalyFormal.Round10.Dictionary.Color.halfE
#print axioms AdalyFormal.Round10.Dictionary.Color.flipE
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_quad
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_gauge
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_matrix
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_axis
#print axioms AdalyFormal.Round10.Dictionary.Color.half_axis
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_neutral
#print axioms AdalyFormal.Round10.Dictionary.Color.two_fixed_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.halfE_flip_on_fixed
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_neutral_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_charged_neutral
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_single_color_zero

namespace AdalyFormal.Round10.Dictionary.ColorObstruction
open AdalyFormal.Balaban.CovariantOperators (RMap RMap_coe_apply)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt)
open AdalyFormal.Round10.Dictionary.Color
theorem half_pauliE1 : RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE1, pauliE1Val, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_pauliE1 : RMap flipElt pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliE1, pauliE1Val]


end AdalyFormal.Round10.Dictionary.ColorObstruction


/-! Exact alternating-area expansion of a two-color quadratic map.
This is algebra, not a nonvanishing assertion for any crossing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.Round13.Detection.Area
open AdalyFormal.IngredientFamilyR2
open Finset
variable {S X Y : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

/-- Zero pure-color terms leave a bilinear mixed term. -/
theorem mixed_bilinear (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y, ∀ f g, Q (a f + b g) = B f g := by
  obtain ⟨β, hβ⟩ := hQ
  refine ⟨β.compl₁₂ a b + β.flip.compl₁₂ a b, ?_⟩
  intro f g
  have ha' := ha f
  have hb' := hb g
  rw [hβ] at ha' hb'
  rw [hβ]
  simp only [map_add, LinearMap.add_apply, ha', hb', zero_add, add_zero,
    LinearMap.compl₁₂_apply, LinearMap.flip_apply]
  exact add_comm _ _

/-- Quarter-color rotation makes that bilinear term alternating. -/
theorem mixed_alternating (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y,
      (∀ f g, Q (a f + b g) = B f g) ∧ (∀ f g, B g f = -B f g) := by
  obtain ⟨B, hB⟩ := mixed_bilinear Q hQ a b ha hb
  refine ⟨B, hB, ?_⟩
  intro f g
  have h := hrot f g
  rw [sub_eq_add_neg, ← map_neg b, hB, map_neg, hB] at h
  exact neg_eq_iff_eq_neg.mp h

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coefficient is the actual value of the mixed map on two scalar atoms. -/
theorem bilinear_matrix (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (f g : I → ℝ) :
    B f g = ∑ i : I, ∑ j : I,
      (f i * g j) • B (Pi.single i 1) (Pi.single j 1) := by
  have he (f : I → ℝ) : f = ∑ i : I, f i • Pi.single i 1 := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [he f, he g]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

/-- Ordered-pair convention: the factor 1/2 pays for counting each pair twice. -/
theorem bilinear_area (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (hskew : ∀ f g, B g f = -B f g) (f g : I → ℝ) :
    B f g = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • B (Pi.single i 1) (Pi.single j 1) := by
  have he : (∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • B (Pi.single i 1) (Pi.single j 1)) =
      B f g - B g f := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← bilinear_matrix, ← bilinear_matrix]
  rw [he, hskew f g, sub_neg_eq_add, ← two_smul ℝ (B f g), smul_smul]
  norm_num

/-- Full finite alternating-area dictionary; it does not supply a nonzero area. -/
theorem quadratic_area (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : (I → ℝ) →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) (f g : I → ℝ) :
    Q (a f + b g) = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • Q (a (Pi.single i 1) + b (Pi.single j 1)) := by
  obtain ⟨B, hB, hskew⟩ := mixed_alternating Q hQ a b ha hb hrot
  simp_rw [hB]
  exact bilinear_area B hskew f g

#print axioms mixed_bilinear
#print axioms mixed_alternating
#print axioms bilinear_matrix
#print axioms bilinear_area
#print axioms quadratic_area
end AdalyFormal.Round13.Detection.Area

namespace AdalyFormal.Round13.Detection.ColorArea
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.GaugeCov
open AdalyFormal.D1Literal (uθ uMat)
open AdalyFormal.Round10.Dictionary.Color
open AdalyFormal.Round10.Dictionary.ColorObstruction
open AdalyFormal.Round10.Dictionary.Source (neutralCoord)
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt)
variable {L : PeriodicLatticeExtent}
attribute [local instance] Classical.propDecidable

/-- The full scalar bond array is masked to the actual touching-bond carrier.
Atoms at bonds outside that carrier are identically zero, not omitted silently. -/
def colorCarrier (G : TowerGeom L) (X : SuTwo) : (Bond L → ℝ) →ₗ[ℝ] ↥(bondSupp G) where
  toFun f := ⟨WithLp.toLp 2 (fun e => if e ∈ bondsOm0 G then f e • X else 0), by
    intro e he
    simp [he]⟩
  map_add' f g := by
    apply Subtype.ext
    apply PiLp.ext
    intro e
    by_cases he : e ∈ bondsOm0 G <;> simp [he, add_smul]
  map_smul' r f := by
    apply Subtype.ext
    apply PiLp.ext
    intro e
    by_cases he : e ∈ bondsOm0 G <;> simp [he, smul_smul]

@[simp] theorem colorCarrier_apply (G : TowerGeom L) (X : SuTwo)
    (f : Bond L → ℝ) (e : Bond L) :
    ((colorCarrier G X f : ↥(bondSupp G)) : BondFnL2 L) e =
      if e ∈ bondsOm0 G then f e • X else 0 := rfl

theorem colorCarrier_gauge (G : TowerGeom L) (X : SuTwo) (f : Bond L → ℝ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    adEL (constGauge g) G (colorCarrier G X f) = colorCarrier G (RMap g X) f := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  change RMap g (if e ∈ bondsOm0 G then f e • X else 0) = _
  by_cases he : e ∈ bondsOm0 G <;> simp [he, map_smul]

theorem colorCarrier_neg (G : TowerGeom L) (X : SuTwo) (f : Bond L → ℝ) :
    colorCarrier G (-X) f = -colorCarrier G X f := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  by_cases he : e ∈ bondsOm0 G <;> simp [he]

theorem half_pauliE2 : RMap (uθ (Real.pi / 2)) pauliE2 = -pauliE2 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE2, AdalyFormal.Balaban.CovariantOperators.witnessM,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_pauliE2 : RMap flipElt pauliE2 = pauliE2 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE2, AdalyFormal.Balaban.CovariantOperators.witnessM]

/-- The quarter rotation is used exactly, not through a numerical phase. -/
theorem quarter_pauliE1 : RMap (uθ (Real.pi / 4)) pauliE1 = -pauliE2 := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change uMat (Real.pi / 4) * (pauliE1 : Matrix (Fin 2) (Fin 2) ℂ) *
    (uMat (Real.pi / 4))ᴴ = _
  have hp : Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
    rw [← Complex.exp_add]
    convert Complex.exp_pi_div_two_mul_I using 1
    congr 1
    ring
  have hm : Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) *
      Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) = -Complex.I := by
    rw [← Complex.exp_add]
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, pauliE1, pauliE1Val, pauliE2, AdalyFormal.Balaban.CovariantOperators.witnessM,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ofReal_div,
      ← Complex.exp_conj, map_neg, map_mul, map_ofNat]
  · calc
      _ = Complex.I * (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
          Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)) := by ring
      _ = _ := by rw [hp]; simp
  · calc
      _ = Complex.I * (Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) *
          Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I))) := by ring
      _ = _ := by rw [hm]; simp


theorem quarter_pauliE2 : RMap (uθ (Real.pi / 4)) pauliE2 = pauliE1 := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change uMat (Real.pi / 4) * (pauliE2 : Matrix (Fin 2) (Fin 2) ℂ) *
    (uMat (Real.pi / 4))ᴴ = _
  have hp : Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
    rw [← Complex.exp_add]
    convert Complex.exp_pi_div_two_mul_I using 1
    congr 1
    ring
  have hm : Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) *
      Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) = -Complex.I := by
    rw [← Complex.exp_add]
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, pauliE1, pauliE1Val, pauliE2, AdalyFormal.Balaban.CovariantOperators.witnessM,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ofReal_div,
      ← Complex.exp_conj, map_neg, map_mul, map_ofNat, hp, hm]

theorem color_one_zero (G : TowerGeom L) (a : ℝ) (f : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 f) = 0 := by
  apply flatJet_single_color_zero
  · change adEL (constGauge _) G _ = _
    rw [colorCarrier_gauge, half_pauliE1, colorCarrier_neg]
  · right
    change adEL (constGauge flipElt) G _ = _
    rw [colorCarrier_gauge, flip_pauliE1, colorCarrier_neg]

theorem color_two_zero (G : TowerGeom L) (a : ℝ) (g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE2 g) = 0 := by
  apply flatJet_single_color_zero
  · change adEL (constGauge _) G _ = _
    rw [colorCarrier_gauge, half_pauliE2, colorCarrier_neg]
  · left
    change adEL (constGauge flipElt) G _ = _
    rw [colorCarrier_gauge, flip_pauliE2]

theorem color_sum_charged (G : TowerGeom L) (f g : Bond L → ℝ) :
    halfE G (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) =
      -(colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) := by
  change adEL (constGauge _) G _ = _
  rw [map_add, colorCarrier_gauge, colorCarrier_gauge, half_pauliE1, half_pauliE2,
    colorCarrier_neg, colorCarrier_neg, neg_add]

theorem quarter_axis : RMap (uθ (Real.pi / 4)) pauliE3 = pauliE3 := by
  apply Subtype.ext
  rw [RMap_coe_apply]
  change uMat (Real.pi / 4) * (pauliE3 : Matrix (Fin 2) (Fin 2) ℂ) *
    (uMat (Real.pi / 4))ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, pauliE3, AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.ofReal_div,
      ← Complex.exp_conj, Complex.exp_neg, map_ofNat]
  all_goals field_simp

theorem flatJet_color_quarter (G : TowerGeom L) (a : ℝ) (f g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 g - colorCarrier G pauliE2 f) =
      flatJet G a (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) := by
  have h := flatJet_gauge G a (uθ (Real.pi / 4))
    (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g)
  rw [map_add, colorCarrier_gauge, colorCarrier_gauge, quarter_pauliE1, quarter_pauliE2,
    colorCarrier_neg, add_comm, ← sub_eq_add_neg] at h
  rw [h]
  apply PiLp.ext
  intro p
  change RMap (uθ (Real.pi / 4))
    (flatJet G a (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) p) = _
  rw [flatJet_charged_neutral G a _ (color_sum_charged G f g) p, map_smul, quarter_axis]

/-- Exact finite area formula for the ENTIRE genuine dressed jet.
The coefficient fields are actual two-bond experiments, not free parameters. -/
theorem flatJet_area (G : TowerGeom L) (a : ℝ) (f g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) =
      (1 / 2 : ℝ) • ∑ e : Bond L, ∑ d : Bond L,
        (f e * g d - g e * f d) •
          flatJet G a (colorCarrier G pauliE1 (Pi.single e 1) +
            colorCarrier G pauliE2 (Pi.single d 1)) := by
  classical
  exact Area.quadratic_area (flatJet G a) (flatJet_quad G a)
    (colorCarrier G pauliE1) (colorCarrier G pauliE2)
    (color_one_zero G a) (color_two_zero G a) (flatJet_color_quarter G a) f g

/-- Physical scalar color coordinates; Pauli E1 is the imaginary charged entry. -/
def imagPart (G : TowerGeom L) (u : ↥(bondSupp G)) (e : Bond L) : ℝ :=
  (((u : BondFnL2 L) e : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 |>.im

def realPart (G : TowerGeom L) (u : ↥(bondSupp G)) (e : Bond L) : ℝ :=
  (((u : BondFnL2 L) e : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 |>.re

theorem half_negative_diag (X : SuTwo) (hX : RMap (uθ (Real.pi / 2)) X = -X) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by
  have he := congrArg (fun Y : SuTwo => (Y : Matrix (Fin 2) (Fin 2) ℂ) 0 0) hX
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix] at he
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, mul_assoc, mul_comm] at he
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul] at he
  linear_combination (-1 / 2 : ℂ) * he

/-- Every charged physical carrier vector is exactly the two scalar colors used above. -/
theorem carrier_color_decompose (G : TowerGeom L) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) :
    u = colorCarrier G pauliE1 (imagPart G u) + colorCarrier G pauliE2 (realPart G u) := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  change (u : BondFnL2 L) e =
    (if e ∈ bondsOm0 G then imagPart G u e • pauliE1 else 0) +
    (if e ∈ bondsOm0 G then realPart G u e • pauliE2 else 0)
  by_cases he : e ∈ bondsOm0 G
  · simp only [if_pos he]
    have hh : RMap (uθ (Real.pi / 2)) ((u : BondFnL2 L) e) = -((u : BondFnL2 L) e) :=
      congrArg (fun w : ↥(bondSupp G) => (w : BondFnL2 L) e) hu
    have hd := suTwo_decompose ((u : BondFnL2 L) e)
    rw [half_negative_diag _ hh] at hd
    simpa only [Complex.zero_im, zero_smul, add_zero, imagPart, realPart] using hd
  · simp only [if_neg he, zero_add]
    exact u.property e he

/-- Canonical skew coefficients of the actual complete jet, at a genuine BIdx row. -/
def areaCoefficient (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e d : Bond L) : ℝ :=
  neutralCoord (flatJet G a
    (colorCarrier G pauliE1 (Pi.single e 1) + colorCarrier G pauliE2 (Pi.single d 1)) p)

theorem areaCoefficient_skew (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e d : Bond L) :
    areaCoefficient G a p d e = -areaCoefficient G a p e d := by
  classical
  obtain ⟨B, hB, hskew⟩ := Area.mixed_alternating (flatJet G a) (flatJet_quad G a)
    (colorCarrier G pauliE1) (colorCarrier G pauliE2)
    (color_one_zero G a) (color_two_zero G a) (flatJet_color_quarter G a)
  unfold areaCoefficient
  rw [hB, hB, hskew (Pi.single e 1) (Pi.single d 1)]
  simp [neutralCoord]

theorem areaCoefficient_diagonal (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e : Bond L) :
    areaCoefficient G a p e e = 0 := by
  have h := areaCoefficient_skew G a p e e
  linarith

/-- Exact actual-row formula for an arbitrary charged carrier, with W and C2 retained. -/
theorem neutralJet_area (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) (p : BIdx G) :
    neutralCoord (flatJet G a u p) = (1 / 2 : ℝ) * ∑ e : Bond L, ∑ d : Bond L,
      (imagPart G u e * realPart G u d - realPart G u e * imagPart G u d) *
        areaCoefficient G a p e d := by
  classical
  have h := flatJet_area G a (imagPart G u) (realPart G u)
  rw [← carrier_color_decompose G u hu] at h
  have hp := congrArg (fun z : FSp G => neutralCoord (z p)) h
  simpa only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, neutralCoord, inner_smul_right,
    inner_sum, smul_eq_mul, areaCoefficient] using hp

#print axioms imagPart
#print axioms realPart
#print axioms half_negative_diag
#print axioms carrier_color_decompose
#print axioms areaCoefficient
#print axioms areaCoefficient_skew
#print axioms areaCoefficient_diagonal
#print axioms neutralJet_area
#print axioms colorCarrier
#print axioms colorCarrier_apply
#print axioms colorCarrier_gauge
#print axioms colorCarrier_neg
#print axioms half_pauliE2
#print axioms flip_pauliE2
#print axioms quarter_pauliE1
#print axioms quarter_pauliE2
#print axioms color_one_zero
#print axioms color_two_zero
#print axioms color_sum_charged
#print axioms quarter_axis
#print axioms flatJet_color_quarter
#print axioms flatJet_area
end AdalyFormal.Round13.Detection.ColorArea

namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t


end AdalyFormal.Round9.Guarded.Qualitative
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open Set
open AdalyFormal.D1Literal (PSD)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

end AdalyFormal.Round9.Guarded.QualitativeR2



namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi


end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})


end AdalyFormal.Round10.Assembly.R2



namespace AdalyFormal.Round12.Kernel.Actual
theorem uθ_add (s t : ℝ) : AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ t =
    AdalyFormal.D1Literal.uθ (s + t) := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat t =
    AdalyFormal.D1Literal.uMat (s + t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ofReal_add, mul_add, Complex.exp_add, neg_add_rev, mul_comm]

end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round13.Detection.PhysicalArea
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.D1Literal (uθ)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Dictionary.Color
open AdalyFormal.Round10.Dictionary.Source (neutralCoord)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Dictionary.JetDetection (physicalJetAggregate topJetDetected_iff)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round13.Detection.ColorArea

/-- Actual transverse sum of the genuine two-bond coefficients. -/
def aggregateCoefficient {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (e d : Bond (L q R)) : ℝ :=
  ∑ c : Fin (4*q) × Fin (4*q), areaCoefficient (G q R) 1 (topIdx hq hj c) e d

/-- One finite, physically normalized alternating-area sum, without eigenvector normalization. -/
def areaSum {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (u : TwistSpace q R) : ℝ :=
  ∑ e : Bond (L q R), ∑ d : Bond (L q R),
    (imagPart (G q R) u e * realPart (G q R) u d -
      realPart (G q R) u e * imagPart (G q R) u d) * aggregateCoefficient hq hj e d

theorem aggregateCoefficient_skew {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (e d : Bond (L q R)) : aggregateCoefficient hq hj d e = -aggregateCoefficient hq hj e d := by
  unfold aggregateCoefficient
  calc
    _ = ∑ c : Fin (4*q) × Fin (4*q), -areaCoefficient (G q R) 1 (topIdx hq hj c) e d :=
      Finset.sum_congr rfl (fun c _ => areaCoefficient_skew (G q R) 1 (topIdx hq hj c) e d)
    _ = _ := by rw [Finset.sum_neg_distrib]

theorem aggregateCoefficient_diagonal {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (e : Bond (L q R)) : aggregateCoefficient hq hj e e = 0 := by
  simp [aggregateCoefficient, areaCoefficient_diagonal]

/-- Exact equality for the original physical aggregate; this does NOT assert it is nonzero. -/
theorem physicalJetAggregate_area {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hu : halfE (G q R) u = -u) :
    physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u := by
  classical
  change (∑ c : Fin (4*q) × Fin (4*q),
    neutralCoord (flatJet (G q R) 1 u (topIdx hq hj c))) = _
  simp_rw [neutralJet_area (G q R) 1 u hu]
  rw [← Finset.mul_sum]
  congr 1
  unfold areaSum aggregateCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]

/-- Chargedness in the ORIGINAL KernelLine supplies the color hypothesis, not detection. -/
theorem kernelLine_half {q R : ℕ}
    (V : ℝ → LinkCfg (L q R)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    halfE (G q R) u = -u := by
  have he : halfE (G q R) u =
      adEL (rotGauge (Real.pi / 4)) (G q R)
        (adEL (rotGauge (Real.pi / 4)) (G q R) u) := by
    apply Subtype.ext
    apply PiLp.ext
    intro e
    change RMap (uθ (Real.pi / 2)) ((u : BondFnL2 (L q R)) e) =
      RMap (uθ (Real.pi / 4)) (RMap (uθ (Real.pi / 4)) ((u : BondFnL2 (L q R)) e))
    rw [RMap_mul_apply, AdalyFormal.Round12.Kernel.Actual.uθ_add,
      show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring]
  exact he.trans hline.2.2.1

/-- The actual crossing generator satisfies this exact alternating-area dictionary. -/
theorem crossing_physicalJetAggregate_area {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (V : ℝ → LinkCfg (L q R))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u :=
  physicalJetAggregate_area hq hj u (kernelLine_half V u hline)

/-- No actual nonvanishing is inferred from the kernel line in this equivalence. -/
theorem crossing_topJet_iff_area {q R : ℕ} (hq : 0 < q)
    (V : ℝ → LinkCfg (L q R)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    TopJetDetected hq R u ↔ ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0 := by
  rw [topJetDetected_iff hq R u]
  apply exists_congr
  intro j
  apply exists_congr
  intro hj
  rw [crossing_physicalJetAggregate_area hq hj V u hline]
  simp

/-- Conditional handoff using the flat N unit proved in R1. The area seed is STILL required. -/
theorem crossing_curlDetected_of_area {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (V : ℝ → LinkCfg (L q R))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (harea : ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0) :
    CurlDetected q R u :=
  AdalyFormal.Round13.Detection.curlDetected_of_topJet hq hR hR18 u
    ((crossing_topJet_iff_area hq V u hline).mpr harea)

#print axioms aggregateCoefficient
#print axioms areaSum
#print axioms aggregateCoefficient_skew
#print axioms aggregateCoefficient_diagonal
#print axioms physicalJetAggregate_area
#print axioms kernelLine_half
#print axioms crossing_physicalJetAggregate_area
#print axioms crossing_topJet_iff_area
#print axioms crossing_curlDetected_of_area
end AdalyFormal.Round13.Detection.PhysicalArea

/-! A generator-only reduction of P3.  These response-line lemmas are copied
from the compiled round-12 charged-line argument; the new theorems at the end
reduce the universal detection statement to one area-detected generator. -/
namespace AdalyFormal.Round12.Kernel.Response
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem quadratic_on_charged_line (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    Q (a • u + b • J u) = (a^2+b^2) • Q u := by
  obtain ⟨B, hB⟩ := hQ
  have he := hJ u
  have hm := hJ (u + J u)
  rw [map_add, hu] at hm
  simp only [hB, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply] at he hm
  have hc : B u (J u) + B (J u) u = 0 := by
    have hh : (2 : ℝ) • (B u (J u) + B (J u) u) = 0 := by
      calc
        _ = (B u u + B (J u) u + (B u (J u) + B (J u) (J u))) -
            (B (J u) (J u) + -B u (J u) + -(B (J u) u + -B u u)) := by module
        _ = 0 := sub_eq_zero.mpr hm.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  simp only [hB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  calc
    _ = (a^2) • B u u + (b^2) • B (J u) (J u) +
        (a*b) • (B u (J u) + B (J u) u) := by module
    _ = (a^2+b^2) • B u u := by rw [hc, smul_zero, add_zero, he, add_smul]

theorem norm_sq_on_charged_line (J : E ≃ₗᵢ[ℝ] E)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    ‖a • u + b • J u‖^2 = (a^2+b^2) * ‖u‖^2 := by
  have h := J.inner_map_map u (J u)
  rw [hu, inner_neg_right] at h
  have hc := real_inner_comm (J u) u
  have hz : ⟪u,J u⟫ = 0 := by linarith
  have hz' : ⟪J u,u⟫ = 0 := by linarith
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hz, hz', J.inner_map_map, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  ring

theorem response_eq_norm_ratio (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) :
    Q v = (‖v‖^2 / ‖u‖^2) • Q u := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [quadratic_on_charged_line Q hQ J hJ u hu,
    norm_sq_on_charged_line J u hu]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))]

#print axioms quadratic_on_charged_line
#print axioms norm_sq_on_charged_line
#print axioms response_eq_norm_ratio
end AdalyFormal.Round12.Kernel.Response

namespace AdalyFormal.Round10.Assembly.R4
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy

noncomputable section

abbrev ProfileSpace (q R : ℕ) := EuclideanSpace ℝ (Bond (scaleUp 2 1 (dilLu q R)))

def responseGradient (q R : ℕ) (u : TwistSpace q R) : ProfileSpace q R :=
  WithLp.toLp 2 (fun b => 2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
    (Dictionary.FreeSource.responseProfile q R u) b)

theorem profileCoupling_gradient (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = ⟪(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫ := by
  classical
  rw [profileCoupling_curl, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change 2 * (∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then
    circulation (Dictionary.FreeSource.responseProfile q R u) p * circulation f p else 0) =
    ∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b
  rw [show (∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b) =
    2 * ∑ b, f b * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring]
  rw [source_sbp]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem responseGradient_ne_zero_iff (q R : ℕ) (u : TwistSpace q R) :
    responseGradient q R u ≠ 0 ↔ CurlDetected q R u := by
  rw [← exists_profile_iff_curlDetected]
  constructor
  · intro h
    refine ⟨fun b => responseGradient q R u b, ?_⟩
    rw [profileCoupling_gradient]
    exact ne_of_gt (real_inner_self_pos.mpr h)
  · rintro ⟨f, hf⟩ hz
    apply hf
    rw [profileCoupling_gradient, hz, inner_zero_right]

end

#print axioms responseGradient
#print axioms profileCoupling_gradient
#print axioms responseGradient_ne_zero_iff
end AdalyFormal.Round10.Assembly.R4

namespace AdalyFormal.Round12.Kernel.ResponseActual
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round10.Assembly.R4
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round12.Kernel.Response

theorem double_inner_linear {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a • x,y⟫ = a * (2 * ⟪x,y⟫) := by
  rw [real_inner_smul_left]; ring

theorem profileCoupling_quad (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsQuadMap (profileCoupling q R f) := by
  let G := geomOf 2 1 (dilTower q R)
  let M : FSp G →ₗ[ℝ] ℝ :=
    { toFun := fun z => 2 * ⟪(flatData q R).H z, profileSourceStencil q R f⟫
      map_add' := by intros; simp only [map_add, inner_add_left]; ring
      map_smul' := by
        intro c z
        change 2 * ⟪(flatData q R).H (c • z), profileSourceStencil q R f⟫ =
          c * (2 * ⟪(flatData q R).H z, profileSourceStencil q R f⟫)
        rw [map_smul]
        exact double_inner_linear (X := TwistSpace q R) _ _ c }
  exact ((C2fullOf_quad G (fun _ => 1)).comp_linear
    (((Wop G (fun _ => 1) 1).comp (iE G)).toLinearMap)).map_linear M

theorem responseGradient_on_line (q R : ℕ) (u : TwistSpace q R)
    (hu : u ≠ 0)
    (hJu : adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u) = -u)
    (v : TwistSpace q R)
    (hv : v ∈ Submodule.span ℝ {u,
      adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u}) :
    responseGradient q R v = (‖v‖^2 / ‖u‖^2) • responseGradient q R u := by
  apply ext_inner_left ℝ
  intro f
  rw [inner_smul_right, ← profileCoupling_gradient q R (fun b => f b),
    ← profileCoupling_gradient q R (fun b => f b)]
  exact response_eq_norm_ratio (profileCoupling q R (fun b => f b))
    (profileCoupling_quad q R _) (adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)))
    (profileCoupling_U1 q R _ (Real.pi/4)) u hJu hu v hv

theorem all_kernel_detected_of_generator (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (hu : CurlDetected q R u) (v : TwistSpace q R)
    (hv : vacA q R V 1 (vacEdge q R V) v = 0) (hne : v ≠ 0) :
    CurlDetected q R v := by
  apply (responseGradient_ne_zero_iff q R v).mp
  rw [responseGradient_on_line q R u hline.1 hline.2.2.1 v (hline.2.2.2 v hv)]
  exact smul_ne_zero (div_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hline.1)))
    ((responseGradient_ne_zero_iff q R u).mpr hu)

#print axioms double_inner_linear
#print axioms profileCoupling_quad
#print axioms responseGradient_on_line
#print axioms all_kernel_detected_of_generator
end AdalyFormal.Round12.Kernel.ResponseActual

namespace AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (uθ)
variable {L : PeriodicLatticeExtent}

/-- The four transverse links incident to one site. -/
def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
/-- The equal-sign exterior star used by the original right-star family. -/
noncomputable def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1

#print axioms starLinks
#print axioms starPath
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1

/-- The designated right boundary site, copied verbatim. -/
noncomputable def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

#print axioms rightSite
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.Path

/-- The canonical right-exterior-star path, copied verbatim. -/
noncomputable def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)

#print axioms rightStar
end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)

/-- The original P3 statement, copied verbatim from the round-13 assembly. -/
def P3 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u

#print axioms P3
end AdalyFormal.Round13.Assembly.R1

namespace AdalyFormal.Round13.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)

/-- The original nested CofinalP3 statement, copied verbatim. -/
def CofinalP3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u

#print axioms CofinalP3
end AdalyFormal.Round13.Assembly.R2

namespace AdalyFormal.Round14.Transfer.Physical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
open AdalyFormal.Round13.Detection.PhysicalArea
open AdalyFormal.Round12.Kernel.ResponseActual

/-- One detected generator at every admissible instance. -/
def DetectedRightStar : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧ CurlDetected q R u

/-- The sharper area-seed interface: only one crossing generator and one
physical top row are required at each instance. -/
def AreaSeedRightStar : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0

theorem detectedRightStar_of_areaSeed (h : AreaSeedRightStar) : DetectedRightStar := by
  intro q R hq hR hR18
  obtain ⟨u,hline,j,hj,harea⟩ := h hq hR hR18
  exact ⟨u,hline,crossing_curlDetected_of_area hq hR hR18 _ u hline ⟨j,hj,harea⟩⟩

/-- Detecting one generator detects every vector satisfying the original
KernelLine predicate. -/
theorem p3_of_detectedRightStar (h : DetectedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3 := by
  intro q R hq hR hR18 v hv
  obtain ⟨u,hline,hu⟩ := h hq hR hR18
  exact all_kernel_detected_of_generator q R _ u hline hu v hv.2.1 hv.1

theorem p3_of_areaSeed (h : AreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R1.P3 :=
  p3_of_detectedRightStar (detectedRightStar_of_areaSeed h)

/-- Nested form of the same existential area seed. -/
def CofinalAreaSeedRightStar : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
        areaSum (by positivity : 0 < 2^j) hk u ≠ 0

/-- The nested existential area seed already gives the original universal
CofinalP3; no second, independently chosen detected family is intersected. -/
theorem cofinalP3_of_areaSeed (h : CofinalAreaSeedRightStar) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3 := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,u,hline,k,hk,harea⟩ := hRs R₀
  refine ⟨R,hR0,hR,hR18,?_⟩
  have hu := crossing_curlDetected_of_area (by positivity) hR hR18 _ u hline ⟨k,hk,harea⟩
  intro v hv
  exact all_kernel_detected_of_generator (2^j) R _ u hline hu v hv.2.1 hv.1

#print axioms DetectedRightStar
#print axioms AreaSeedRightStar
#print axioms detectedRightStar_of_areaSeed
#print axioms p3_of_detectedRightStar
#print axioms p3_of_areaSeed
#print axioms CofinalAreaSeedRightStar
#print axioms cofinalP3_of_areaSeed
end AdalyFormal.Round14.Transfer.Physical

/-! The scalar Laurent interface is repeated here so this physical join remains
a compact standalone file, with no import of an AHP artifact. -/
namespace AdalyFormal.Round14.Transfer

noncomputable section

open Polynomial

def laurent (r A B C : ℝ) (n : ℕ) : ℝ := A*r^n+B+C*(r⁻¹)^n

theorem eval_ne_zero_eventually {K : Type*} [Field K]
    (p : K[X]) (hp : p ≠ 0) (a : ℕ → K) (ha : Function.Injective a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (a n) ≠ 0 := by
  have hfin : Set.Finite (a ⁻¹' {x : K | p.IsRoot x}) :=
    Set.Finite.preimage (fun _ _ _ _ h => ha h) (Polynomial.finite_setOf_isRoot hp)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N+1, fun n hn hzero => ?_⟩
  have hnN : n ≤ N := hN hzero
  omega

def laurentPolynomial (A B C : ℝ) : ℝ[X] :=
  Polynomial.C A*X^2+Polynomial.C B*X+Polynomial.C C

theorem laurentPolynomial_ne_zero {A B C : ℝ}
    (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) : laurentPolynomial A B C ≠ 0 := by
  intro hp
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hp
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hp
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hp
  simp [laurentPolynomial] at h0 h1 h2
  rcases h with hA | hB | hC
  · exact hA h2
  · exact hB h1
  · exact hC h0

theorem laurent_mul_pow {r : ℝ} (hr : r ≠ 0) (A B C : ℝ) (n : ℕ) :
    r^n * laurent r A B C n = (laurentPolynomial A B C).eval (r^n) := by
  have hp : r^n * (r⁻¹)^n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hr, one_pow]
  simp only [laurent, laurentPolynomial, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  calc
    _ = A*(r^n)^2+B*r^n+C*(r^n*(r⁻¹)^n) := by ring
    _ = _ := by rw [hp]; ring

theorem laurent_eventually_ne_zero {r A B C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → laurent r A B C n ≠ 0 := by
  have hr : r ≠ 0 := ne_of_gt hr0
  have ha : Function.Injective (fun n : ℕ => r^n) :=
    (pow_right_strictAnti₀ hr0 hr1).injective
  obtain ⟨N, hN⟩ := eval_ne_zero_eventually (laurentPolynomial A B C)
    (laurentPolynomial_ne_zero h) (fun n : ℕ => r^n) ha
  refine ⟨N, fun n hn hz => hN n hn ?_⟩
  rw [← laurent_mul_pow hr A B C n, hz, mul_zero]

theorem laurent_cofinal_ne_zero {r A B C : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (h : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ laurent r A B C n ≠ 0 := by
  obtain ⟨N₀, hN₀⟩ := laurent_eventually_ne_zero hr0 hr1 h
  intro N
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

def RadiusLaurentData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r A B C : ℝ, 0 < r ∧ r < 1 ∧ (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
    ∀ n : ℕ, observable q (2*(n+9)) = laurent r A B C n

end

#print axioms laurent
#print axioms eval_ne_zero_eventually
#print axioms laurentPolynomial
#print axioms laurentPolynomial_ne_zero
#print axioms laurent_mul_pow
#print axioms laurent_eventually_ne_zero
#print axioms laurent_cofinal_ne_zero
#print axioms RadiusLaurentData
end AdalyFormal.Round14.Transfer

namespace AdalyFormal.Round14.Transfer.Physical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Round12.Noncancel.RightFamily (rightStar)
open AdalyFormal.Round13.Detection.PhysicalArea
open AdalyFormal.Round12.Kernel.ResponseActual
open AdalyFormal.Round14.Transfer

/-- The exact remaining transfer certificate.  For each sufficiently large
dyadic scale it supplies one actual area observable on the even-radius
progression, a nonzero three-term Laurent representation, and a crossing
generator realizing that observable at the same radius and physical top row. -/
def CofinalLaurentAreaSeed : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
    RadiusLaurentData observable (2^j) ∧
    ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
      KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
        areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))

/-- The actual Laurent transfer certificate proves the original CofinalP3.
This theorem is conditional on the preceding definition; it is not a physical
collar computation or a proof of P3. -/
theorem cofinalP3_of_laurentAreaSeed (h : CofinalLaurentAreaSeed) :
    AdalyFormal.Round13.Assembly.R2.CofinalP3 := by
  apply cofinalP3_of_areaSeed
  intro j₀
  obtain ⟨j,hj,observable,hdata,hident⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨r,A,B,C,hr0,hr1,hcoef,hform⟩ := hdata
  obtain ⟨n,hn,hz⟩ := laurent_cofinal_ne_zero hr0 hr1 hcoef R₀
  obtain ⟨u,hline,k,hk,heq⟩ := hident n
  refine ⟨2*(n+9),by omega,⟨n+9,rfl⟩,by omega,u,hline,k,hk,?_⟩
  rw [heq,hform n]
  exact hz

#print axioms CofinalLaurentAreaSeed
#print axioms cofinalP3_of_laurentAreaSeed
end AdalyFormal.Round14.Transfer.Physical

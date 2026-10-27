import DrEquiv
import ZXR2Flat6
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

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

end AdalyFormal.Round10.Dictionary.FreeSource


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

#print axioms pathU
noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

#print axioms pathP
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

#print axioms pathA
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

#print axioms uthPath
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

#print axioms vacA

end AdalyFormal.Round9.Guarded.Qualitative


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

#print axioms bulkD
theorem bulkD_rot (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)⟫ = ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) (rotGauge α) u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [rot_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

#print axioms bulkD_rot

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0

#print axioms corrDeriv

end AdalyFormal.Round9.Guarded.QualitativeR2Joint


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2 := by
  have h01' : ⟪u₀, J u₀⟫ = -⟪u₀, J u₀⟫ := by
    calc ⟪u₀, J u₀⟫ = ⟪J u₀, J (J u₀)⟫ := (hJ _ _).symm
      _ = ⟪J u₀, -u₀⟫ := by rw [hJJ]
      _ = -⟪J u₀, u₀⟫ := inner_neg_right _ _
      _ = -⟪u₀, J u₀⟫ := by rw [real_inner_comm u₀ (J u₀)]
  have h01 : ⟪u₀, J u₀⟫ = 0 := by linarith
  have h10 : ⟪J u₀, u₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hJn : ⟪J u₀, J u₀⟫ = ⟪u₀, u₀⟫ := hJ u₀ u₀
  have e1 : ⟪J u₀, M u₀⟫ = ⟪u₀, M (J u₀)⟫ :=
    (hM (J u₀) u₀).symm.trans (real_inner_comm u₀ (M (J u₀)))
  have h1 : ⟪u₀, M (J u₀)⟫ = -⟪u₀, M (J u₀)⟫ := by
    calc ⟪u₀, M (J u₀)⟫ = ⟪J u₀, J (M (J u₀))⟫ := (hJ _ _).symm
      _ = ⟪J u₀, M (J (J u₀))⟫ := by rw [hMJ (J u₀)]
      _ = ⟪J u₀, M (-u₀)⟫ := by rw [hJJ]
      _ = -⟪J u₀, M u₀⟫ := by rw [map_neg, inner_neg_right]
      _ = -⟪u₀, M (J u₀)⟫ := by rw [e1]
  have hc1 : ⟪u₀, M (J u₀)⟫ = 0 := by linarith
  have hc2 : ⟪J u₀, M u₀⟫ = 0 := by rw [e1]; exact hc1
  have hd : ⟪J u₀, M (J u₀)⟫ = ⟪u₀, M u₀⟫ := by rw [hMJ u₀]; exact hJ _ _
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  refine ⟨⟪u₀, M u₀⟫ / ‖u₀‖ ^ 2, fun u hu => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hform : ⟪a • u₀ + b • J u₀, M (a • u₀ + b • J u₀)⟫ =
      (a ^ 2 + b ^ 2) * ⟪u₀, M u₀⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hc1, hc2, hd]
    ring
  have hnorm : ‖a • u₀ + b • J u₀‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hJn, h01, h10]
    ring
  rw [hform, hnorm, div_mul_eq_mul_div, eq_div_iff hn.ne']
  ring

#print axioms scalar_on_complex_line

end AdalyFormal.Round9.Guarded.Qualitative


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.D1Literal (PSD)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

#print axioms psdEdge

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

#print axioms vacEdge
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

#print axioms CanonicalCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {L : PeriodicLatticeExtent}
open AdalyFormal.D1Literal (SU2m)

def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

#print axioms AnM
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

#print axioms AnFam

end AdalyFormal.Round9.Guarded.QualitativeR2


namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

def CofinalAnyProfileCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
      QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)

#print axioms CofinalAnyProfileCoupling
def CofinalAnyPathCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
      QualitativeR2.AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R f)

#print axioms CofinalAnyPathCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2Joint


namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem comm_of_quad (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫)
    (hq : ∀ x, ⟪J x, T (J x)⟫ = ⟪x, T x⟫) (y : E) :
    T (J y) = J (T y) := by
  have hb (x : E) : ⟪J x, T (J y)⟫ = ⟪x, T y⟫ := by
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, T (J x)⟫ = ⟪J x, T (J y)⟫ := by
      rw [← hs, real_inner_comm]
    have hs2 : ⟪y, T x⟫ = ⟪x, T y⟫ := by rw [← hs, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  apply ext_inner_left ℝ
  intro v
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb, J.inner_map_map]

#print axioms comm_of_quad
theorem deriv_comm (D : ℝ → E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ t x, D t (J x) = J (D t x)) (t : ℝ) (x : E) :
    deriv D t (J x) = J (deriv D t x) := by
  by_cases hd : DifferentiableAt ℝ D t
  · have hd' : HasDerivAt D (deriv D t) t := hd.hasDerivAt
    let L : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (J x)
    let M : (E →L[ℝ] E) →L[ℝ] E :=
      J.toLinearIsometry.toContinuousLinearMap.comp (ContinuousLinearMap.apply ℝ E x)
    have hl := L.hasFDerivAt.comp_hasDerivAt t hd'
    have hm := M.hasFDerivAt.comp_hasDerivAt t hd'
    have he : (fun s => L (D s)) = fun s => M (D s) := funext (fun s => h s x)
    change HasDerivAt (fun s => L (D s)) (L (deriv D t)) t at hl
    rw [he] at hl
    exact hl.unique hm
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

#print axioms deriv_comm

end AdalyFormal.Round10.Dictionary


namespace AdalyFormal.Round10.Dictionary.Actual
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

theorem bulkD_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) (u : TwistSpace q R) :
    bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (bulkD q R f ε u) :=
  comm_of_quad _ _ ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
    (dataS_laws selIn selIn _)).1 (bulkD_rot q R α f ε) u

#print axioms bulkD_U1
theorem corrDeriv_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (corrDeriv q R f u) :=
  deriv_comm (fun ε : ℝ => bulkD q R f ε) _ (fun ε => bulkD_U1 q R f ε α) 0 u

#print axioms corrDeriv_U1

end AdalyFormal.Round10.Dictionary.Actual


namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

theorem deriv_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ℝ → E →L[ℝ] E) (hs : ∀ t x y, ⟪D t x, y⟫ = ⟪x, D t y⟫)
    (t : ℝ) (x y : E) : ⟪deriv D t x, y⟫ = ⟪x, deriv D t y⟫ := by
  by_cases hd : DifferentiableAt ℝ D t
  · have hd' : HasDerivAt D (deriv D t) t := hd.hasDerivAt
    let L := (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ E x)
    let M := (innerSL ℝ x).comp (ContinuousLinearMap.apply ℝ E y)
    have hl := L.hasFDerivAt.comp_hasDerivAt t hd'
    have hm := M.hasFDerivAt.comp_hasDerivAt t hd'
    have he : (fun s => L (D s)) = fun s => M (D s) := by
      funext s
      exact (real_inner_comm (D s x) y).trans (hs s x y)
    change HasDerivAt (fun s => L (D s)) (L (deriv D t)) t at hl
    rw [he] at hl
    exact (real_inner_comm y (deriv D t x)).trans (hl.unique hm)
  · rw [deriv_zero_of_not_differentiableAt hd]
    simp

#print axioms deriv_symmetric
theorem corrDeriv_symmetric (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (x y : TwistSpace q R) :
    ⟪corrDeriv q R f x, y⟫ = ⟪x, corrDeriv q R f y⟫ :=
  deriv_symmetric (fun ε => bulkD q R f ε)
    (fun ε => ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
      (dataS_laws selIn selIn _)).1) 0 x y

#print axioms corrDeriv_symmetric
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

#print axioms KernelLine
theorem canonicalCoupling_of_line {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u₀ : TwistSpace q R)
    (hline : KernelLine q R V u₀) (hc : ⟪u₀, corrDeriv q R f u₀⟫ ≠ 0) :
    CanonicalCoupling q R V (corrDeriv q R f) := by
  obtain ⟨hu₀, -, hJJ, hK⟩ := hline
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  let Jop : TwistSpace q R →L[ℝ] TwistSpace q R :=
    J.toLinearIsometry.toContinuousLinearMap
  obtain ⟨l, hl⟩ := scalar_on_complex_line (corrDeriv q R f) Jop
    (corrDeriv_symmetric q R f) (fun x y => J.inner_map_map x y)
    (fun x => Dictionary.Actual.corrDeriv_U1 q R f (Real.pi / 4) x) u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, Jop u₀} := Submodule.subset_span (by simp)
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc
    rw [hl u₀ hmem, h0, zero_mul]
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · refine ⟨-l, by linarith, Or.inr (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith
  · refine ⟨l, hpos, Or.inl (fun u hu => ?_)⟩
    exact le_of_eq (hl u (hK u hu)).symm

#print axioms canonicalCoupling_of_line

end AdalyFormal.Round10.Assembly.R2


namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open Filter Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open ContinuousLinearMap

theorem tendsto_clm_apply₂ {α : Type*} {l : Filter α} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E →L[ℝ] F} {x : α → E}
    {f₀ : E →L[ℝ] F} {x₀ : E} (hf : Tendsto f l (𝓝 f₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => f a (x a)) l (𝓝 (f₀ x₀)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (f₀, x₀)).comp (hf.prodMk_nhds hx)

#print axioms tendsto_clm_apply₂
theorem tendsto_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) (A : E) :
    Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 (2 * ⟪(D 0).H ((D 0).C2 A), J'⟫)) := by
  have e : ∀ ε : ℝ, ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫
      = 2 * ⟪(D ε).H ((D ε).C2 A), ε⁻¹ • (D ε).J⟫ := by
    intro ε
    rw [smul_apply, real_inner_smul_right, ((D ε).Delta2_spec (hL ε)).2 A,
      real_inner_smul_right]
    ring
  simp only [e]
  have hHC : Tendsto (fun ε => (D ε).H ((D ε).C2 A)) (𝓝[≠] 0) (𝓝 ((D 0).H ((D 0).C2 A))) :=
    tendsto_clm_apply₂ (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hC2 A).mono_left nhdsWithin_le_nhds)
  exact (Filter.Tendsto.inner (𝕜 := ℝ) hHC hJ).const_mul (2 : ℝ)

#print axioms tendsto_Delta2_div_form
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
  have h1 : Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[>] 0) (𝓝 ⟪A, D₁ A⟫) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_clm_apply₂ hD₁ tendsto_const_nhds))
  have h2 := (tendsto_Delta2_div_form D hL hH hC2 J' hJ A).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  exact tendsto_nhds_unique h1 h2

#print axioms limit_Delta2_div_form

end AdalyFormal.Round9.Guarded.AnalyticR2

/-! Actual charged-input neutrality and the associated physical scalar profile.
These facts contain no spectral nonvanishing claim. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner

/-- The quarter-phase action squared is the half-phase action on the actual carrier. -/
theorem quarter_twice (q R : ℕ) (u : TwistSpace q R) :
    adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u := by
  apply Subtype.ext
  apply PiLp.ext
  intro b
  change RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4))
    (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4)) ((u : BondFnL2 _) b)) =
    RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) ((u : BondFnL2 _) b)
  rw [RMap_mul_apply, AdalyFormal.Round10.Dictionary.PhaseSource.phase_mul]
  rw [show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring]

/-- The actual dressed blocking jet is even; this uses its frozen bilinear witness. -/
theorem vacJet_neg (q R : ℕ) (u : TwistSpace q R) : vacJet q R (-u) = vacJet q R u := by
  unfold vacJet
  simp only [map_neg]
  have h := (C2fullOf_quad (geomOf 2 1 (dilTower q R)) (fun _ => 1)).smul_sq (-1 : ℝ)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) u))
  simpa only [neg_one_smul, neg_one_sq, one_smul] using h

/-- Charge of the input forces neutrality of its actual quadratic jet. -/
theorem vacJet_half_fixed (q R : ℕ) (u : TwistSpace q R)
    (hu : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u = -u) :
    adFL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) (vacJet q R u) =
      vacJet q R u := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge (Real.pi / 2))
  rw [rot_trivial] at h
  have hc := h.C2 u
  change vacJet q R (adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u) = _ at hc
  rw [hu, vacJet_neg] at hc
  exact hc.symm

/-- H is the full constrained inverse map, not an inverse of a compressed block. -/
def responseField (q R : ℕ) (u : TwistSpace q R) : TwistSpace q R :=
  (flatData q R).H (vacJet q R u)

theorem responseField_half_fixed (q R : ℕ) (u : TwistSpace q R)
    (hu : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u = -u) :
    adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) (responseField q R u) =
      responseField q R u := by
  rw [responseField, ← flatH_U1, vacJet_half_fixed q R u hu]

/-- A physical profile, defined on every fine bond with no Bloch-cell normalization. -/
def responseProfile (q R : ℕ) (u : TwistSpace q R)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ :=
  neutralCoord ((responseField q R u : BondFnL2 _) b)

theorem responseField_component (q R : ℕ) (u : TwistSpace q R)
    (hu : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u = -u)
    (b : Bond (scaleUp 2 1 (dilLu q R))) :
    (responseField q R u : BondFnL2 _) b = responseProfile q R u b • pauliE3 := by
  apply neutral_of_half_fixed
  have h := congrArg (fun x : TwistSpace q R => (x : BondFnL2 _) b)
    (responseField_half_fixed q R u hu)
  exact h

/-- Exterior masking does not change this profile: H takes values in the actual carrier. -/
theorem responseProfile_interior (q R : ℕ) (u : TwistSpace q R) :
    interiorProfile q R (responseProfile q R u) = responseProfile q R u := by
  classical
  funext b
  unfold interiorProfile
  split_ifs with hb
  · have hz : (responseField q R u : BondFnL2 _) b = 0 := by
      apply (responseField q R u).property b
      change ¬ (b.1 ∈ (dilTower q R).Om 0 ∨
        periodicLatticeShift b.1 b.2 ∈ (dilTower q R).Om 0)
      exact not_or.mpr hb
    simp [responseProfile, hz, neutralCoord]
  · rfl

/-- Exact identity between the physical profile lift and H applied to the dressed jet. -/
theorem responseProfile_lift (q R : ℕ) (u : TwistSpace q R)
    (hu : adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) u = -u) :
    (WithLp.toLp 2 (fun b => responseProfile q R u b • pauliE3) : BondFnL2 _) =
      iE (geomOf 2 1 (dilTower q R)) (responseField q R u) := by
  apply PiLp.ext
  intro b
  exact (responseField_component q R u hu b).symm

#print axioms quarter_twice
#print axioms vacJet_neg
#print axioms vacJet_half_fixed
#print axioms responseField
#print axioms responseField_half_fixed
#print axioms responseProfile
#print axioms responseField_component
#print axioms responseProfile_interior
#print axioms responseProfile_lift
end AdalyFormal.Round10.Assembly.R3

/-! Exact derivative/explicit-form glue and free-path cofinal bookkeeping.
ProfileRegular packages only the three regularity facts already compiled in round 9.
The final historical application of those facts is kept separate from this compact harness. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
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
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource (profileCoupling CurlDetected)
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- The explicit R3 profile agrees definitionally with the dictionary's physical profile. -/
theorem responseProfile_eq (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R u = Dictionary.FreeSource.responseProfile q R u := rfl

/-- Fixed carrier types avoid dependent elaboration through the varying background. -/
abbrev profileData (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    BaseDataS (TwistSpace q R) (SiteL2 (scaleUp 2 1 (dilLu q R)))
      (FSp (geomOf 2 1 (dilTower q R))) := dataS selIn selIn (bulkP q R f ε)

/-- Already-proved round-9 inputs, retained visibly instead of using uncompiled stand-ins. -/
def ProfileRegular (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ContinuousAt (fun ε : ℝ => (profileData q R f ε).H) 0 ∧
  (∀ u : TwistSpace q R, Tendsto (fun ε : ℝ => (profileData q R f ε).C2 u)
    (𝓝 0) (𝓝 ((profileData q R f 0).C2 u))) ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f) 0

def RegularityFacts : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f

/-- Source vanishing proves flat correction vanishing without any radius assumptions. -/
theorem bulkD_zero_source (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    bulkD q R f 0 = 0 := by
  have hs := (profileData q R f 0).Delta2_spec (dataS_laws selIn selIn _)
  apply symm_unique hs.1
    (S2 := (0 : TwistSpace q R →L[ℝ] TwistSpace q R))
    (fun x y => by simp only [zero_apply, inner_zero_left, inner_zero_right])
  intro u
  rw [hs.2 u, bulkSource_zero]
  change 2 * ⟪(profileData q R f 0).H ((profileData q R f 0).C2 u),
    (0 : TwistSpace q R)⟫ = ⟪u, (0 : TwistSpace q R)⟫
  rw [inner_zero_right, inner_zero_right, mul_zero]

theorem bulkData_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    dataS selIn selIn (bulkP q R f 0) = flatData q R := by
  have hu : bulkU q R f 0 = (fun _ => 1) := by
    rw [bulkU_phase]
    funext b
    simp only [Dictionary.PhaseSource.phase, zero_mul, Dictionary.PhaseSource.phase_zero]
  unfold bulkP
  rw [hu]

/-- Exact actual derivative identification for an arbitrary profile, using only
round-9 regularity and the unconditional R2 source stencil limit. -/
theorem corrDeriv_profile_form (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hr : ProfileRegular q R f)
    (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u := by
  have ht := Dictionary.PhaseSource.tendsto_div_of_hasDerivAt_zero
    (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f)
    (bulkD_zero_source q R f) hr.2.2
  have h := limit_Delta2_div_form
    (profileData q R f) (fun _ => dataS_laws selIn selIn _) 
    hr.1 hr.2.1 (profileSourceStencil q R f) (bulkSource_tendsto q R f)
    (corrDeriv q R f)
    (ht.mono_left (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))) u
  change ⟪u, corrDeriv q R f u⟫ =
    2 * ⟪(dataS selIn selIn (bulkP q R f 0)).H
      ((dataS selIn selIn (bulkP q R f 0)).C2 u), profileSourceStencil q R f⟫ at h
  rw [bulkData_zero] at h
  exact h

/-- The whole kernel is essential; the adaptive profile is chosen from its generator. -/
theorem canonicalCoupling_of_curlDetected {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (hcurl : CurlDetected q R u)
    (hr : ProfileRegular q R (Dictionary.FreeSource.responseProfile q R u)) :
    CanonicalCoupling q R V
      (corrDeriv q R (Dictionary.FreeSource.responseProfile q R u)) := by
  apply canonicalCoupling_of_line V _ u hline
  rw [corrDeriv_profile_form q R _ hr u]
  exact ne_of_gt ((Dictionary.FreeSource.adaptive_pos_iff q R u).mpr hcurl)

/-- This is the NEW missing geometric premise on the canonical path. No source
recurrence, cancellation estimate, Fourier normalization or derivative occurs in it. -/
def CofinalCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R (uthPath (2^j) R) u ∧
      CurlDetected (2^j) R u

/-- The free path may be left-only or otherwise asymmetric, but its start and
negative direction must be proved for that same path. -/
def CofinalAnyPathCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u

theorem cofinalAnyProfileCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalCurlLine) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, u, hline, hcurl⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, Dictionary.FreeSource.responseProfile (2^j) R u,
    canonicalCoupling_of_curlDetected (uthPath _ _) u hline hcurl
      (hr (2^j) R (by positivity) hR hR18 _)⟩

theorem cofinalAnyPathCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalAnyPathCurlLine) :
    CofinalAnyPathCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, u, hline, hcurl⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
    Dictionary.FreeSource.responseProfile (2^j) R u,
    canonicalCoupling_of_curlDetected V u hline hcurl
      (hr (2^j) R (by positivity) hR hR18 _)⟩

#print axioms responseProfile_eq
#print axioms profileData
#print axioms ProfileRegular
#print axioms RegularityFacts
#print axioms bulkD_zero_source
#print axioms bulkData_zero
#print axioms corrDeriv_profile_form
#print axioms canonicalCoupling_of_curlDetected
#print axioms CofinalCurlLine
#print axioms CofinalAnyPathCurlLine
#print axioms cofinalAnyProfileCoupling_of_curlLine
#print axioms cofinalAnyPathCoupling_of_curlLine
end AdalyFormal.Round10.Assembly.R3


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

#print axioms neutralFunctional
#print axioms physicalJetAggregate
#print axioms curlDetected_of_physicalJet
#print axioms adaptive_pos_of_physicalJet
#print axioms exists_profile_of_physicalJet
end AdalyFormal.Round10.Dictionary.JetDetection

/-! Cofinal bookkeeping consuming dictionary/nonvanishing R3's compiled physical
jet-to-curl theorem. No new proof of that theorem is duplicated here. -/
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative (uthPath vacA)
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round10.Dictionary.JetDetection
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- These units are known in round 9; kept explicit in the compact harness. -/
def FlatConstraintUnits : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R → IsUnit (Dictionary.KKT.N (flatData q R))

/-- New geometric hand-off: nonzero aggregate at ONE actual block, together with
whole-kernel containment, at nested cofinal scales. This proposition is NOT proved. -/
def CofinalJetLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, R2.KernelLine (2^j) R (uthPath (2^j) R) u ∧
      ∃ (i : ℕ) (hi : i < blockCount (2^j) R),
        physicalJetAggregate (q := 2^j) (by positivity) hi u ≠ 0

def CofinalAnyPathJetLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, R2.KernelLine (2^j) R V u ∧
        ∃ (i : ℕ) (hi : i < blockCount (2^j) R),
          physicalJetAggregate (q := 2^j) (by positivity) hi u ≠ 0

theorem cofinalCurlLine_of_jetLine (hN : FlatConstraintUnits) (h : CofinalJetLine) :
    CofinalCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,u,hline,i,hi,hjet⟩ := hRs R₀
  refine ⟨R,hRR,hR,hR18,u,hline,?_⟩
  exact curlDetected_of_physicalJet (by positivity) (by omega)
    (hN (2^j) R (by positivity) hR hR18) hi u hjet

theorem cofinalAnyPathCurlLine_of_jetLine (hN : FlatConstraintUnits)
    (h : CofinalAnyPathJetLine) : CofinalAnyPathCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,V,hVc,hVa,hV0,hneg,u,hline,i,hi,hjet⟩ := hRs R₀
  refine ⟨R,hRR,hR,hR18,V,hVc,hVa,hV0,hneg,u,hline,?_⟩
  exact curlDetected_of_physicalJet (by positivity) (by omega)
    (hN (2^j) R (by positivity) hR hR18) hi u hjet

#print axioms FlatConstraintUnits
#print axioms CofinalJetLine
#print axioms CofinalAnyPathJetLine
#print axioms cofinalCurlLine_of_jetLine
#print axioms cofinalAnyPathCurlLine_of_jetLine
end AdalyFormal.Round10.Assembly.R3

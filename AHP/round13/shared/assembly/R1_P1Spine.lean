import DrPath3
import DrEquiv
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

/-! Quadratic responses on a charged line: the unit response hull is a singleton. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round12.Kernel.Response
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quarter-turn invariant quadratic map is radial on each charged complex line. -/
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

/-- The isometric quarter-turn gives the matching norm identity. -/
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

/-- A generator determines every vector response in its charged span. -/
theorem response_eq_norm_ratio (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) :
    Q v = (‖v‖^2 / ‖u‖^2) • Q u := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [quadratic_on_charged_line Q hQ J hJ u hu,
    norm_sq_on_charged_line J u hu]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))]

/-- Every nonzero vector in this span is visible iff the generator is visible. -/
theorem response_ne_zero_iff (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) (hvn : v ≠ 0) :
    Q v ≠ 0 ↔ Q u ≠ 0 := by
  rw [response_eq_norm_ratio Q hQ J hJ u hu hne v hv, smul_ne_zero_iff]
  simp [pow_ne_zero _ (norm_ne_zero_iff.mpr hvn),
    pow_ne_zero _ (norm_ne_zero_iff.mpr hne)]

/-- Unit responses of an arbitrary nonzero subspace contained in the charged line
are a SINGLE point, not merely contained in a pointed cone. -/
theorem unit_response_image (K : Submodule ℝ E) (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0) (huk : u ∈ K)
    (hK : K ≤ Submodule.span ℝ ({u,J u} : Set E)) :
    Q '' {v | v ∈ K ∧ ‖v‖ = 1} = {(‖u‖^2)⁻¹ • Q u} := by
  ext w
  constructor
  · rintro ⟨v,⟨hv,hvn⟩,rfl⟩
    rw [Set.mem_singleton_iff, response_eq_norm_ratio Q hQ J hJ u hu hne v (hK hv), hvn]
    simp
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    refine ⟨‖u‖⁻¹ • u, ⟨K.smul_mem _ huk, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]
    · rw [hQ.smul_sq, inv_pow]

#print axioms quadratic_on_charged_line
#print axioms norm_sq_on_charged_line
#print axioms response_eq_norm_ratio
#print axioms response_ne_zero_iff
#print axioms unit_response_image
end AdalyFormal.Round12.Kernel.Response

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


namespace AdalyFormal.Round9.Guarded.QualitativeR2
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
variable {L : PeriodicLatticeExtent}
open AdalyFormal.D1Literal (SU2m)
def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

#print axioms AnM
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

#print axioms AnFam


end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round10.Assembly.R4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def responseHull (K : Submodule ℝ E) (Q : E → F) : Set F :=
  closedConvexHull ℝ (Q '' {u | u ∈ K ∧ ‖u‖ = 1})

end AdalyFormal.Round10.Assembly.R4

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
abbrev ProfileSpace (q R : ℕ) := EuclideanSpace ℝ (Bond (scaleUp 2 1 (dilLu q R)))

/-- The exact physical curl-adjoint-curl response, including the coupling factor 2. -/
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

theorem double_inner_smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a ^ 2 • x, y⟫ = a ^ 2 * (2 * ⟪x, y⟫) := by
  rw [real_inner_smul_left]
  ring

theorem profileCoupling_smul_input (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (a • u) = a ^ 2 * profileCoupling q R f u := by
  unfold profileCoupling AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling
  simp only [map_smul]
  rw [(C2fullOf_quad (geomOf 2 1 (dilTower q R)) (fun _ => 1)).smul_sq]
  simp only [map_smul]
  exact double_inner_smul (X := TwistSpace q R)
    ((flatData q R).H (vacJet q R u)) (profileSourceStencil q R f) a

theorem responseGradient_smul (q R : ℕ) (a : ℝ) (u : TwistSpace q R) :
    responseGradient q R (a • u) = a ^ 2 • responseGradient q R u := by
  apply ext_inner_left ℝ
  intro f
  rw [inner_smul_right, ← profileCoupling_gradient q R (fun b => f b),
    ← profileCoupling_gradient q R (fun b => f b), profileCoupling_smul_input]

/-- Entire actual crossing kernel; no charged-line or character restriction. -/
def crossingKernel (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R) := (vacA q R V 1 (vacEdge q R V)).ker

/-- This condition is NOT proved for any cofinal family. It rules out convex
cancellation among all unit kernel response gradients, not just individual zeros. -/
def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  (0 : ProfileSpace q R) ∉ responseHull (crossingKernel q R V) (responseGradient q R)

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

/-- Necessary detection on every nonzero vector of the complete crossing kernel. -/
def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V


end AdalyFormal.Round10.Assembly.R4

namespace AdalyFormal.Round10.Assembly.R3
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
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
def CofinalAnyPathCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u


end AdalyFormal.Round10.Assembly.R3

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
open AdalyFormal.Round10.Assembly.R3
open AdalyFormal.Round10.Assembly.R4
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round12.Kernel.Response

theorem double_inner_linear {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a • x,y⟫ = a * (2 * ⟪x,y⟫) := by
  rw [real_inner_smul_left]; ring

/-- Quadraticity of the actual explicit free-profile form; no derivative or regularity. -/
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

/-- Every actual response gradient in the charged line is a nonnegative scalar
multiple of the generator's response, with the exact norm ratio. -/
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

/-- Full physical unit-kernel responses collapse to one point under the ORIGINAL
KernelLine predicate. No regularity, sector screen, or extra gauge hypothesis. -/
theorem responseHull_singleton (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    responseHull (crossingKernel q R V) (responseGradient q R) =
      {(‖u‖^2)⁻¹ • responseGradient q R u} := by
  have himage : responseGradient q R ''
      {v | v ∈ crossingKernel q R V ∧ ‖v‖ = 1} =
      {(‖u‖^2)⁻¹ • responseGradient q R u} := by
    ext z
    constructor
    · rintro ⟨v,⟨hv,hn⟩,rfl⟩
      rw [Set.mem_singleton_iff,
        responseGradient_on_line q R u hline.1 hline.2.2.1 v (hline.2.2.2 v hv), hn]
      simp
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨‖u‖⁻¹ • u, ⟨(crossingKernel q R V).smul_mem _ hline.2.1, ?_⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hline.1)]
      · rw [responseGradient_smul, inv_pow]
  rw [responseHull, himage, closedConvexHull_eq_closure_convexHull, convexHull_singleton,
    isClosed_singleton.closure_eq]

/-- Exact detection/noncancellation equivalence on a whole charged kernel line.
Unlike the old derivative-based sufficient bridge, this needs no RegularityFacts. -/
theorem noCancellation_iff_curlDetected_of_kernelLine (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    NoResponseCancellation q R V ↔ CurlDetected q R u := by
  rw [NoResponseCancellation, responseHull_singleton q R V u hline,
    Set.mem_singleton_iff, eq_comm]
  change (‖u‖^2)⁻¹ • responseGradient q R u ≠ 0 ↔ CurlDetected q R u
  rw [smul_ne_zero_iff, responseGradient_ne_zero_iff]
  simp [hline.1]

/-- Detecting the generator excludes ALL zero-response kernel fields, not only
the historical oneColor example. The generator detection remains explicit. -/
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

/-- Conditional exclusion of EVERY nonzero zero-full-jet field from this kernel.
Unlike the R1 oneColor exclusion, no support or color-eigenvector assumption is used. -/
theorem zeroJet_not_crossing_of_detected_line (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (hu : CurlDetected q R u) (v : TwistSpace q R)
    (hne : v ≠ 0) (hz : vacJet q R v = 0) :
    vacA q R V 1 (vacEdge q R V) v ≠ 0 := by
  intro hv
  have hdet := all_kernel_detected_of_generator q R V u hline hu v hv hne
  obtain ⟨f,hf⟩ := (exists_profile_iff_curlDetected q R v).mpr hdet
  apply hf
  change 2 * ⟪(flatData q R).H (vacJet q R v), profileSourceStencil q R f⟫ = 0
  rw [hz, map_zero, inner_zero_left, mul_zero]

/-- Direct bridge into the EXACT requested cofinal premise. This is an implication,
not a proof of its cofinal hypothesis. It removes the old regularity join here. -/
theorem cofinal_noCancellation_of_curlLine
    (h : CofinalAnyPathCurlLine) : CofinalAnyPathNoResponseCancellation := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,V,hcont,han,hzero,hneg,u,hline,hcurl⟩ := hRs R₀
  exact ⟨R,hRR,hR,hR18,V,hcont,han,hzero,hneg,
    (noCancellation_iff_curlDetected_of_kernelLine (2^j) R V u hline).mpr hcurl⟩

#print axioms double_inner_linear
#print axioms profileCoupling_quad
#print axioms responseGradient_on_line
#print axioms responseHull_singleton
#print axioms noCancellation_iff_curlDetected_of_kernelLine
#print axioms all_kernel_detected_of_generator
#print axioms zeroJet_not_crossing_of_detected_line
#print axioms cofinal_noCancellation_of_curlLine
#print axioms AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
#print axioms AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine
#print axioms AdalyFormal.Round10.Assembly.R2.KernelLine
end AdalyFormal.Round12.Kernel.ResponseActual

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
open AdalyFormal.Round2.Guarded.Pin

open Classical

theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

end AdalyFormal.Round4.Guarded.RefuteR1
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]

end AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace

namespace AdalyFormal.Round12.Kernel

section SpectralExclusion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive energy on the discarded projection excludes every discarded kernel component.
The projection need not be orthogonal; its commutation and positivity are explicit. -/
theorem kernel_concentrates (A : E →L[ℝ] E) (P : E →L[ℝ] E)
    (hcomm : ∀ x, A (P x) = P (A x))
    (hpos : ∀ x, x ≠ 0 → P x = 0 → 0 < ⟪x, A x⟫)
    (hidem : ∀ x, P (P x) = P x) (u : E) (hu : A u = 0) :
    P u = u := by
  have hk : A (u - P u) = 0 := by simp [map_sub, hcomm, hu]
  have hp : P (u - P u) = 0 := by simp [map_sub, hidem]
  have hz : u - P u = 0 := by
    by_contra hn
    have hh := hpos (u - P u) hn hp
    simp only [hk, inner_zero_right] at hh
    exact (lt_irrefl 0) hh
  exact (sub_eq_zero.mp hz).symm

/-- Opposite real characters cannot occur in a common nonzero vector. -/
theorem opposite_character_disjoint (T F : E →ₗ[ℝ] E)
    (J : E →ₗ[ℝ] E) (a b : ℝ) (hb : b ≠ 0)
    (hTF : ∀ x, T (F x) = F (T x))
    (hFJ : ∀ x, F (J x) = -J (F x))
    (hJ : Function.Injective J) (u : E)
    (hu : T u = a • u + b • J u)
    (hFu : T (F u) = a • F u + b • J (F u)) : F u = 0 := by
  have h : (2 * b) • J (F u) = 0 := by
    have he := hTF u
    rw [hu, map_add, map_smul, map_smul, hFJ, hFu] at he
    have hz : b • J (F u) = -(b • J (F u)) := by
      simpa only [smul_neg] using (add_left_cancel he)
    calc
      (2 * b) • J (F u) = b • J (F u) + b • J (F u) := by
        rw [show (2 * b) = b + b by ring, add_smul]
      _ = 0 := by conv_lhs => lhs; rw [hz]
                  exact neg_add_cancel _
  have hj : J (F u) = 0 := (smul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hb)
  exact hJ (by simpa using hj)

/-- A non-real translation character contains no nonzero flip eigenvector.
This is the precise obstruction to importing a one-real-color invisible field. -/
theorem no_flip_eigenvector (T F J : E →ₗ[ℝ] E) (a b c : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hTF : ∀ x, T (F x) = F (T x))
    (hFJ : ∀ x, F (J x) = -J (F x))
    (hJ : Function.Injective J) (u : E)
    (hu : T u = a • u + b • J u) (hFu : F u = c • u) : u = 0 := by
  have hchar : T (F u) = a • F u + b • J (F u) := by
    rw [hFu, map_smul, hu, smul_add, map_smul]
    module
  have hz := opposite_character_disjoint T F J a b hb hTF hFJ hJ u hu hchar
  rw [hFu] at hz
  exact (smul_eq_zero.mp hz).resolve_left hc

/-- The charged plane generated by a nonzero vector has exactly real dimension two. -/
theorem charged_span_finrank (J : E ≃ₗᵢ[ℝ] E) (u : E) (hu : u ≠ 0)
    (hJJ : J (J u) = -u) :
    Module.finrank ℝ (Submodule.span ℝ ({u, J u} : Set E)) = 2 := by
  have horth : ⟪u, J u⟫ = 0 := by
    have h := J.inner_map_map u (J u)
    rw [hJJ, inner_neg_right, real_inner_comm u (J u)] at h
    linarith
  have hJn : J u ≠ 0 := by simpa using hu
  have hind : LinearIndependent ℝ ![u, J u] := by
    rw [linearIndependent_fin2]
    refine ⟨hJn, fun a ha => ?_⟩
    have hh := congrArg (fun x => ⟪u, x⟫) ha
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      inner_smul_right, horth, mul_zero] at hh
    exact hu (inner_self_eq_zero.mp hh.symm)
  have hrange : Set.range ![u, J u] = ({u, J u} : Set E) := by
    ext x
    simp [or_comm]
  have hdim := finrank_span_eq_card hind
  rw [hrange] at hdim
  simpa using hdim

/-- A global real nullity bound of two plus one charged kernel vector identifies
its entire kernel. A bound on only a selected Fourier block is insufficient. -/
theorem kernel_eq_charged_span [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hcomm : ∀ x, A (J x) = J (A x))
    (u : E) (hu : u ≠ 0) (hAu : A u = 0) (hJJ : J (J u) = -u)
    (hdim : Module.finrank ℝ A.ker ≤ 2) :
    A.ker = Submodule.span ℝ ({u, J u} : Set E) := by
  have hle : Submodule.span ℝ ({u, J u} : Set E) ≤ A.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x; exact hAu
    · have hx' : x = J u := Set.mem_singleton_iff.mp h
      subst x
      change A (J u) = 0
      rw [hcomm, hAu, map_zero]
  exact (Submodule.eq_of_le_of_finrank_le hle (by
    rw [charged_span_finrank J u hu hJJ]
    exact hdim)).symm

/-- Positivity when one boundary observable vanishes makes that observable
injective on the full kernel. This bypasses all spatial-character decomposition. -/
theorem boundary_observable_injective {B : Type*} [AddCommGroup B] [Module ℝ B]
    (A : E →L[ℝ] E) (r : E →ₗ[ℝ] B)
    (hpos : ∀ u : E, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
    Function.Injective (r.comp A.ker.subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hn
  have hr : r ((x : E) - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have ha : A ((x : E) - y) = 0 := by
    rw [map_sub, show A (x : E) = 0 from x.property,
      show A (y : E) = 0 from y.property, sub_self]
  have hh := hpos ((x : E) - y) hn hr
  simp only [ha, inner_zero_right, lt_self_iff_false] at hh

/-- A complex boundary coordinate supplies the global real-nullity bound two
once positivity on its zero hyperplane is proved for the physical carrier. -/
theorem kernel_finrank_le_two_of_boundary (A : E →L[ℝ] E) (r : E →ₗ[ℝ] ℂ)
    (hpos : ∀ u : E, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
    Module.finrank ℝ A.ker ≤ 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (boundary_observable_injective A r hpos)
  simpa only [Complex.finrank_real_complex] using h

/-- Injectivity of the boundary observable propagates its charged rotation law
to the entire kernel, eliminating a separate neutral-sector exclusion step. -/
theorem charged_of_boundary (A : E →L[ℝ] E) (J : E →ₗ[ℝ] E)
    (r : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ x, A (J x) = J (A x))
    (hpos : ∀ x : E, x ≠ 0 → r x = 0 → 0 < ⟪x, A x⟫)
    (hcoord : ∀ x, r (J (J x)) = -r x)
    (u : E) (hAu : A u = 0) : J (J u) = -u := by
  have hj : A (J (J u)) = 0 := by rw [hcomm, hcomm, hAu, map_zero, map_zero]
  have hn : A (-u) = 0 := by rw [map_neg, hAu, neg_zero]
  have he : (⟨J (J u), hj⟩ : A.ker) = ⟨-u, hn⟩ := by
    apply boundary_observable_injective A r hpos
    change r (J (J u)) = r (-u)
    rw [hcoord, map_neg]
  exact congrArg Subtype.val he

/-- Whole-kernel line identification from a single complex boundary observable.
All physical work is in the explicit positivity and charged-witness hypotheses. -/
theorem kernel_eq_charged_span_of_boundary [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E) (r : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ x, A (J x) = J (A x))
    (hpos : ∀ x : E, x ≠ 0 → r x = 0 → 0 < ⟪x, A x⟫)
    (u : E) (hu : u ≠ 0) (hAu : A u = 0) (hJJ : J (J u) = -u) :
    A.ker = Submodule.span ℝ ({u, J u} : Set E) :=
  kernel_eq_charged_span A J hcomm u hu hAu hJJ
    (kernel_finrank_le_two_of_boundary A r hpos)

end SpectralExclusion

section BoundaryCertificate
variable {𝕜 : Type*} [Field 𝕜]
variable {E B : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup B] [Module 𝕜 B]

/-- Exact boundary restriction/reconstruction identifies the complete kernel,
not only a selected eigenvector. No surjectivity onto a numerical block is implicit. -/
def kernelBoundaryEquiv (A : E →ₗ[𝕜] E) (S : B →ₗ[𝕜] B)
    (restrict : E →ₗ[𝕜] B) (lift : B →ₗ[𝕜] E)
    (hres : ∀ u, A u = 0 → S (restrict u) = 0)
    (hlift : ∀ b, S b = 0 → A (lift b) = 0)
    (hleft : ∀ u, A u = 0 → lift (restrict u) = u)
    (hright : ∀ b, S b = 0 → restrict (lift b) = b) :
    LinearMap.ker A ≃ₗ[𝕜] LinearMap.ker S where
  toFun u := ⟨restrict u, hres u u.property⟩
  invFun b := ⟨lift b, hlift b b.property⟩
  left_inv u := Subtype.ext (hleft u u.property)
  right_inv b := Subtype.ext (hright b b.property)
  map_add' _ _ := Subtype.ext (map_add restrict _ _)
  map_smul' _ _ := Subtype.ext (map_smul restrict _ _)

theorem kernel_finrank_eq_boundary (A : E →ₗ[𝕜] E) (S : B →ₗ[𝕜] B)
    (restrict : E →ₗ[𝕜] B) (lift : B →ₗ[𝕜] E)
    (hres : ∀ u, A u = 0 → S (restrict u) = 0)
    (hlift : ∀ b, S b = 0 → A (lift b) = 0)
    (hleft : ∀ u, A u = 0 → lift (restrict u) = u)
    (hright : ∀ b, S b = 0 → restrict (lift b) = b) :
    Module.finrank 𝕜 (LinearMap.ker A) = Module.finrank 𝕜 (LinearMap.ker S) :=
  (kernelBoundaryEquiv A S restrict lift hres hlift hleft hright).finrank_eq
end BoundaryCertificate

#print axioms kernel_concentrates
#print axioms opposite_character_disjoint
#print axioms no_flip_eigenvector
#print axioms charged_span_finrank
#print axioms kernel_eq_charged_span
#print axioms boundary_observable_injective
#print axioms kernel_finrank_le_two_of_boundary
#print axioms charged_of_boundary
#print axioms kernel_eq_charged_span_of_boundary
#print axioms kernelBoundaryEquiv
#print axioms kernel_finrank_eq_boundary
end AdalyFormal.Round12.Kernel

namespace AdalyFormal.Round10.Dictionary.ColorObstruction
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
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.D1Literal (sing sing_apply sing_apply_self)
/-- Physical fine site on the left face of Omega0. -/
def interiorSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 4*q else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem interiorSite_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    interiorSite hq R ∈ (dilTower q R).Om 0 := by
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  simp only [interiorSite, ↓reduceIte]
  omega

def oneColor {q : ℕ} (hq : 0 < q) (R : ℕ) : TwistSpace q R :=
  ⟨sing (interiorSite hq R, (0 : Fin 3)) pauliE1,
    AdalyFormal.D1Literal.sing_mem_bondSupp _ (interiorSite_mem hq R) pauliE1⟩

theorem oneColor_ne_zero {q : ℕ} (hq : 0 < q) (R : ℕ) : oneColor hq R ≠ 0 := by
  intro h
  have he := congrArg (fun u : TwistSpace q R => (u : BondFnL2 _) (interiorSite hq R, 0)) h
  change sing _ pauliE1 _ = 0 at he
  rw [sing_apply_self] at he
  have hi := hsInner_e1_e1
  rw [he] at hi
  norm_num [hsInner] at hi


end AdalyFormal.Round10.Dictionary.ColorObstruction


namespace AdalyFormal.Round12.Kernel.Actual
open scoped RealInnerProductSpace
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
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 RMap RMap_coe_apply RMap_mul_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- The physical charged entry at one actual touching-bond coordinate. -/
def chargedCoordinate (q R : ℕ) (b : Bond (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →ₗ[ℝ] ℂ where
  toFun u := ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  map_add' u v := rfl
  map_smul' c u := by
    change ((c : ℂ) * _) = _
    rfl

theorem vacA_rot_of_fixed (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (α t : ℝ)
    (hV : periodicGaugeTransform (rotGauge α) (V t) = V t)
    (u : TwistSpace q R) :
    vacA q R V 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R V 1 t u) := by
  have h := AdalyFormal.Round10.Dictionary.Ginv_all_gauge
    (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R V (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) u
  have hp : periodicGaugeTransform (rotGauge α) (pathU q R V (fun _ => 0) 0 t) =
      pathU q R V (fun _ => 0) 0 t := by
    unfold pathU
    rw [rot_maskedU, hV]
  rw [hp] at h
  exact h

theorem uθ_add (s t : ℝ) : AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ t =
    AdalyFormal.D1Literal.uθ (s + t) := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat t =
    AdalyFormal.D1Literal.uMat (s + t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ofReal_add, mul_add, Complex.exp_add, neg_add_rev, mul_comm]

/-- The only coordinate identity needed to exclude neutral kernel vectors. -/
theorem chargedCoordinate_quarter_twice (q R : ℕ)
    (b : Bond (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R) :
    chargedCoordinate q R b
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
        (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u)) =
      -chargedCoordinate q R b u := by
  change (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4))
    (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4))
      ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b)) :
        Matrix (Fin 2) (Fin 2) ℂ) 0 1 = _
  rw [RMap_mul_apply, uθ_add,
    show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
    RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  simp [chargedCoordinate, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring_nf
  simp [Complex.I_sq]

/-- Exact application to the original KernelLine, without asserting positivity
for any physical path. Chargedness is derived, not assumed. -/
theorem kernelLine_of_boundary_positive (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hAu : vacA q R V 1 (vacEdge q R V) u = 0) :
    KernelLine q R V u := by
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  have hcomm := vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV
  have hJJ : J (J u) = -u := charged_of_boundary
    (vacA q R V 1 (vacEdge q R V)) J.toLinearMap (chargedCoordinate q R b)
    hcomm hpos (chargedCoordinate_quarter_twice q R b) u hAu
  refine ⟨hu, hAu, hJJ, fun x hx => ?_⟩
  have hk := kernel_eq_charged_span_of_boundary
    (vacA q R V 1 (vacEdge q R V))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)))
    (chargedCoordinate q R b)
    (vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV)
    hpos u hu hAu hJJ
  rw [← hk]
  exact hx

/-- The original line predicate really gives real nullity two, once the
actual carrier preserves the quarter turn. -/
theorem kernelLine_finrank (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2 := by
  let A := vacA q R V 1 (vacEdge q R V)
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  have hk : A.ker = Submodule.span ℝ ({u, J u} : Set (TwistSpace q R)) := by
    apply le_antisymm
    · exact fun x hx => hline.2.2.2 x hx
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with h | h
      · subst x; exact hline.2.1
      · have hx' : x = J u := Set.mem_singleton_iff.mp h
        subst x
        change A (J u) = 0
        rw [vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV u,
          hline.2.1, map_zero]
  change Module.finrank ℝ A.ker = 2
  rw [hk]
  exact charged_span_finrank J u hline.1 hline.2.2.1

/-- The constructed one-color field cannot be inserted merely because it is
charged: every nonzero kernel vector must have a nonzero central charged entry. -/
theorem crossing_coordinate_ne_zero (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hAu : vacA q R V 1 (vacEdge q R V) u = 0) :
    chargedCoordinate q R b u ≠ 0 := by
  intro hz
  have hh := hpos u hu hz
  simp only [hAu, inner_zero_right, lt_self_iff_false] at hh

/-- Excludes the specific historical charged-invisible witness, conditionally
on physical boundary-zero positivity. This is not exclusion of all zero-jet fields. -/
theorem oneColor_not_crossing {q : ℕ} (hq : 0 < q) (R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hb : b ≠ (AdalyFormal.Round10.Dictionary.ColorObstruction.interiorSite hq R, 0))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫) :
    vacA q R V 1 (vacEdge q R V)
      (AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor hq R) ≠ 0 := by
  intro ha
  apply crossing_coordinate_ne_zero q R V b hpos _
    (AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_ne_zero hq R) ha
  change ((AdalyFormal.D1Literal.sing _ AdalyFormal.Balaban.SuTwoInner.pauliE1 b :
    Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0
  rw [AdalyFormal.D1Literal.sing_apply_ne _ _ hb]
  rfl

#print axioms oneColor_not_crossing
#print axioms AdalyFormal.Round10.Dictionary.ColorObstruction.interiorSite
#print axioms AdalyFormal.Round10.Dictionary.ColorObstruction.interiorSite_mem
#print axioms AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor
#print axioms AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_ne_zero
#print axioms kernelLine_finrank
#print axioms crossing_coordinate_ne_zero
#print axioms chargedCoordinate
#print axioms vacA_rot_of_fixed
#print axioms uθ_add
#print axioms chargedCoordinate_quarter_twice
#print axioms kernelLine_of_boundary_positive
end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Set
open AdalyFormal.D1Literal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
theorem abs_inner_le_opNorm (N : E →L[ℝ] E) (x : E) : |⟪x, N x⟫| ≤ ‖N‖ * ‖x‖ ^ 2 := by
  calc |⟪x, N x⟫| ≤ ‖x‖ * ‖N x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖N‖ * ‖x‖) := by gcongr; exact N.le_opNorm x
    _ = ‖N‖ * ‖x‖ ^ 2 := by ring

/-- A positive semidefinite unit is positive definite. -/
theorem pos_of_psd_unit (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (hu : IsUnit X) (x : E) (hx : x ≠ 0) : 0 < ⟪x, X x⟫ := by
  rcases (hp x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hk := psd_kernel X hs hp x h.symm
    have hinj : Function.Injective X := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    exact hx (hinj (by rw [hk, map_zero]))

/-- A positive definite operator is a unit. -/
theorem unit_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  have hi : Function.Injective X := (injective_iff_map_eq_zero X).mpr (by
    intro v hv
    by_contra hn
    have h := hpd v hn
    rw [hv, inner_zero_right] at h
    exact (lt_irrefl 0) h)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective (f := (show E →ₗ[ℝ] E from X))).mp hi⟩

omit [FiniteDimensional ℝ E] in
theorem psd_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro v
  by_cases hv : v = 0
  · rw [hv]; simp
  · exact (hpd v hv).le

/-- Positive definiteness is open along a continuous symmetric path. -/
theorem eventually_pd {A : ℝ → E →L[ℝ] E} (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ : ℝ)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t₀| < δ → ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A t₀) (hs t₀) (psd_of_pd _ hpd) (unit_of_pd _ hpd)
  have hct : ContinuousAt A t₀ := hc.continuousAt
  rw [Metric.continuousAt_iff] at hct
  obtain ⟨δ, hδ, hb⟩ := hct (m / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs' x hx => ?_⟩
  have hd : dist (A s) (A t₀) < m / 2 := hb (by rw [Real.dist_eq]; exact hs')
  rw [dist_eq_norm] at hd
  have h1 := hmc x
  have h2 := abs_inner_le_opNorm (A s - A t₀) x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have e : ⟪x, A s x⟫ = ⟪x, A t₀ x⟫ + ⟪x, (A s - A t₀) x⟫ := by
    rw [show (A s - A t₀) x = A s x - A t₀ x from rfl, inner_sub_right]; ring
  have h3 : ‖A s - A t₀‖ * ‖x‖ ^ 2 ≤ m / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hd.le hx2.le
  rw [e]
  have := (abs_le.mp h2).1
  nlinarith


/-- Continuity and endpoint signs already give a singular PSD edge strictly
between the endpoints. No isolated-nonunit hypothesis is needed for these clauses. -/
theorem psdEdge_singular_without_isolation (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)} with hS
  have hts' : psdEdge A t₀ t₁ = sSup S := rfl
  set ts := psdEdge A t₀ t₁ with hts
  have hpsd0 : PSD (A t₀) := psd_of_pd _ hpd
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01.le⟩, fun s hs' => by
    rw [le_antisymm hs'.2 hs'.1]; exact hpsd0⟩
  have hne : S.Nonempty := ⟨t₀, h0S⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hts0 : t₀ ≤ ts := by rw [hts']; exact le_csSup hbdd h0S
  have hts1 : ts ≤ t₁ := by rw [hts']; exact csSup_le hne (fun t ht => ht.1.2)
  obtain ⟨δ, hδ, hpdn⟩ := eventually_pd hc hs t₀ hpd
  have hδS : min (t₀ + δ / 2) t₁ ∈ S := by
    refine ⟨⟨le_min (by linarith) h01.le, min_le_right _ _⟩, fun s hs' => ?_⟩
    have hs1 : s ≤ t₀ + δ / 2 := le_trans hs'.2 (min_le_left _ _)
    exact psd_of_pd _ (hpdn s (by rw [abs_lt]; constructor <;> linarith [hs'.1]))
  have hts0' : t₀ < ts := by
    have h1 : t₀ < min (t₀ + δ / 2) t₁ := lt_min (by linarith) h01
    have h2 : min (t₀ + δ / 2) t₁ ≤ ts := by rw [hts']; exact le_csSup hbdd hδS
    linarith
  have hlt : ∀ s, t₀ ≤ s → s < ts → PSD (A s) := by
    intro s hs0 hs1
    rw [hts'] at hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hpsd_ts : PSD (A ts) := by
    intro v
    have hsub : Ico t₀ ts ⊆ {s : ℝ | 0 ≤ ⟪v, A s v⟫} := fun s hs' => hlt s hs'.1 hs'.2 v
    have hcl : IsClosed {s : ℝ | 0 ≤ ⟪v, A s v⟫} := isClosed_le continuous_const (by fun_prop)
    have hcs := hcl.closure_subset_iff.mpr hsub
    exact hcs (by rw [closure_Ico hts0'.ne]; exact ⟨hts0, le_rfl⟩)
  have hle : ∀ s, t₀ ≤ s → s ≤ ts → PSD (A s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have hts1' : ts < t₁ := by
    rcases hts1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts w
      rw [h] at this
      linarith
  have haft : ∀ η : ℝ, 0 < η → ∃ s, ts < s ∧ s < ts + η ∧ ∃ v, ⟪v, A s v⟫ < 0 := by
    intro η hη
    set t' := min (ts + η / 2) t₁ with ht'
    have ht'1 : ts < t' := lt_min (by linarith) hts1'
    have hnot : t' ∉ S := by
      intro h
      have : t' ≤ ts := by rw [hts']; exact le_csSup hbdd h
      linarith
    have hnall : ¬ ∀ s ∈ Icc t₀ t', PSD (A s) := fun hall =>
      hnot ⟨⟨by linarith, min_le_right _ _⟩, hall⟩
    push Not at hnall
    obtain ⟨s, hs', hns⟩ := hnall
    have hsts : ts < s := by
      by_contra hcon
      push Not at hcon
      exact hns (hle s hs'.1 hcon)
    have hst' : s < ts + η := lt_of_le_of_lt (le_trans hs'.2 (min_le_left _ _)) (by linarith)
    unfold PSD at hns
    push Not at hns
    exact ⟨s, hsts, hst', hns⟩
  have hnu : ¬ IsUnit (A ts) := by
    intro hu
    have hpdts : ∀ x, x ≠ 0 → 0 < ⟪x, A ts x⟫ := fun x hx =>
      pos_of_psd_unit _ (hs ts) hpsd_ts hu x hx
    obtain ⟨δ', hδ', hb⟩ := eventually_pd hc hs ts hpdts
    obtain ⟨s, h1, h2, v, hv⟩ := haft δ' hδ'
    have hsd := hb s (by rw [abs_lt]; constructor <;> linarith)
    by_cases hv0 : v = 0
    · rw [hv0] at hv; simp at hv
    · linarith [hsd v hv0]
  exact ⟨hts0', hts1', hpsd_ts, hnu, hle, haft⟩

#print axioms psdEdge_singular_without_isolation
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Kernel.Crossing
open scoped RealInnerProductSpace Topology
open Set
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A negative direction at T cuts off the initial PSD interval, so increasing
the endpoint beyond T cannot change its supremum. No continuity is needed here. -/
theorem psdEdge_same_after_negative (A : ℝ → E →L[ℝ] E)
    {a T b : ℝ} (haT : a ≤ T) (hTb : T ≤ b) (w : E) (hw : ⟪w,A T w⟫ < 0) :
    psdEdge A a b = psdEdge A a T := by
  unfold psdEdge
  congr 1
  ext t
  constructor
  · rintro ⟨ht,hall⟩
    have htT : t < T := by
      by_contra h
      have hp := hall T ⟨haT, le_of_not_gt h⟩ w
      linarith
    exact ⟨⟨ht.1,htT.le⟩,hall⟩
  · rintro ⟨ht,hall⟩
    exact ⟨⟨ht.1,ht.2.trans hTb⟩,hall⟩

/-- A non-unit finite-dimensional endomorphism has a nonzero kernel witness. -/
theorem exists_kernel_of_nonunit [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : ¬ IsUnit A) : ∃ u, u ≠ 0 ∧ A u = 0 := by
  by_contra hn
  push_neg at hn
  have hi : Function.Injective A := (injective_iff_map_eq_zero A).mpr (by
    intro u hu
    by_contra hne
    exact hn u hne hu)
  exact h (ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi,(LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi⟩)

#print axioms psdEdge_same_after_negative
#print axioms exists_kernel_of_nonunit
end AdalyFormal.Round12.Kernel.Crossing

namespace AdalyFormal.Round12.Kernel.CrossingActual
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Round12.Kernel.Crossing
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- Exact canonical crossing and COMPLETE real nullity two from a physical
negative half-pi trial and a trace-zero positivity estimate throughout the interval.
These two physical inputs are explicit, not established by this theorem. -/
theorem kernelLine_exists_before_halfpi (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hc : Continuous (vacA q R V 1))
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x,vacA q R V 1 0 x⟫)
    (hw : ∃ w, ⟪w,vacA q R V 1 (Real.pi/2) w⟫ < 0)
    (hV : ∀ t, periodicGaugeTransform (rotGauge (Real.pi/4)) (V t) = V t)
    (hp : ∀ t, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace q R,
      x ≠ 0 → chargedCoordinate q R b x = 0 → 0 < ⟪x,vacA q R V 1 t x⟫) :
    0 < vacEdge q R V ∧ vacEdge q R V < Real.pi/2 ∧
      ∃ u : TwistSpace q R, KernelLine q R V u ∧
        Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2 := by
  obtain ⟨w,hw⟩ := hw
  have hs : ∀ t x y, ⟪vacA q R V 1 t x,y⟫ = ⟪x,vacA q R V 1 t y⟫ := by
    intro t x y
    exact (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll
      AdalyFormal.D1Literal.selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (AdalyFormal.D1Literal.dataS_laws _ _ _) x y
  have heq : vacEdge q R V = psdEdge (vacA q R V 1) 0 (Real.pi/2) :=
    psdEdge_same_after_negative _ (by positivity) (by linarith [Real.pi_pos]) w hw
  obtain ⟨h0,ht,_,hn,_,_⟩ := psdEdge_singular_without_isolation
    (vacA q R V 1) hc hs (by positivity : (0:ℝ) < Real.pi/2) hpd w hw
  rw [← heq] at h0 ht hn
  obtain ⟨u,hu,hAu⟩ := exists_kernel_of_nonunit _ hn
  have hl := kernelLine_of_boundary_positive q R V b (hV _) (hp _ h0 ht) u hu hAu
  exact ⟨h0,ht,u,hl,kernelLine_finrank q R V (hV _) u hl⟩

#print axioms kernelLine_exists_before_halfpi
end AdalyFormal.Round12.Kernel.CrossingActual

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

#print axioms AnM
#print axioms AnFam
#print axioms analyticAt_exp_I
#print axioms anM_uMat
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
variable {L : PeriodicLatticeExtent}

/-- The four transverse links incident to one site (when transverse side lengths exceed two). -/
def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
/-- Equal-sign exterior star; unlike the translation-invariant twist, the support is local. -/
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1

theorem starPath_zero (x : PeriodicLatticeSite L) : starPath x 0 = fun _ => 1 := by
  funext e
  simp [starPath, uθ_zero]

theorem starPath_cont (x : PeriodicLatticeSite L) : ContFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    change Continuous fun t => uMat t
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [starPath, h, if_false]
    exact continuous_const

theorem starPath_an (x : PeriodicLatticeSite L) : AnFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    show AnM fun t => uMat t
    exact anM_uMat
  · intro t i j
    simp only [starPath, h, if_false]
    exact analyticAt_const

theorem starLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om)) :
    starLinks x ⊆ Zb Om := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change z = x at hz
    subst z
    exact ⟨hx, fun h => hx ((htrans x ν hν).mp h)⟩
  · exact ⟨fun h => hx (hz ▸ (htrans z ν hν).mpr h), fun h => hx (hz ▸ h)⟩

theorem starPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => he (starLinks_exterior Om x hx htrans h)
  simp [starPath, hh]

theorem starPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => (starLinks_exterior Om x hx htrans h).1 he
  simp [starPath, hh]

theorem starPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    starPath x t (z,0) = 1 := by simp [starPath, starLinks]

/-- Use the exterior site immediately to the right of a frozen boundary point. -/
theorem star_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) x t
  have h2 : starPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t := by
    simp [starPath, starLinks, hν]
  have h3 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [h1,h2,h3,h4]
  simp

theorem star_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : starPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starPath, starLinks, hν, hs]
  have h3 := starPath_normal (periodicLatticeShift x 0) x t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp

/-- A genuine negative endpoint on the frozen all-plaquette carrier, for the local star.
This does not locate the first crossing below pi/2 or prove jet detection. -/
theorem star_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := starPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact starPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith

#print axioms starLinks
#print axioms starPath
#print axioms starPath_zero
#print axioms starPath_cont
#print axioms starPath_an
#print axioms starLinks_exterior
#print axioms starPath_off_exterior
#print axioms starPath_interior
#print axioms starPath_normal
#print axioms star_holonomy1
#print axioms star_holonomy2
#print axioms star_negative_endpoint
end AdalyFormal.Round12.Noncancel.Path

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

theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]


#print axioms dil_admissible
end AdalyFormal.Round4.Guarded.RefuteR1

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
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega


#print axioms rightSite_bd
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.Path

/-- One consistently chosen family: the right exterior star, never reflected from a left computation. -/
def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)

theorem rightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    rightStar hq R 0 = fun _ => 1 := starPath_zero _

theorem rightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AdalyFormal.D1Literal.ContFam (rightStar hq R) := starPath_cont _

theorem rightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AnFam (rightStar hq R) := starPath_an _

theorem rightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    rightStar hq R t e = 1 :=
  starPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e he

/-- The exterior masking in the ORIGINAL pathU is exactly transparent to this star. -/
theorem pathU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (rightStar hq R) f 0 t = rightStar hq R t := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp [pathU,maskedU,he]
  · rw [rightStar_off_exterior hq R t e he]
    simp [pathU,maskedU,he,Ug_zero]

theorem dilU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) :
    dilU q R 0 (rightStar hq R t) = rightStar hq R t := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp [dilU,he]
  · rw [rightStar_off_exterior hq R t e he]
    simp [dilU,he,Ug_zero]

/-- Exact equality with the original vacuum carrier, not just a same-shaped matrix. -/
theorem vacA_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (rightStar hq R) a t =
      (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (rightStar hq R t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_rightStar]
  rfl

/-- Actual negative pi endpoint for EVERY positive scale and even radius >=18. -/
theorem rightStar_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0 := by
  rw [vacA_rightStar]
  exact star_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero

/-- The nested dyadic/even quantifiers and ALL path-validity clauses are now
proved for this right-star family. Response noncancellation is deliberately absent. -/
theorem cofinal_rightStar_paths :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
        AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
        (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := dvd_mul_right _ _
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  have hq : 0 < 2^j₀ := by positivity
  exact ⟨R,by dsimp [R]; omega,hR,hR18,rightStar hq R,
    rightStar_cont hq R,rightStar_an hq R,rightStar_zero hq R,
    rightStar_negative hq hR hR18⟩

#print axioms rightStar
#print axioms rightStar_zero
#print axioms rightStar_cont
#print axioms rightStar_an
#print axioms rightStar_off_exterior
#print axioms pathU_rightStar
#print axioms dilU_rightStar
#print axioms vacA_rightStar
#print axioms rightStar_negative
#print axioms cofinal_rightStar_paths
end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round12.Noncancel.Gauge
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round12.Noncancel.Path

/- Verbatim frozen-operator covariance argument from R1_Dictionary.lean. -/
theorem uθ_comm (α s : ℝ) : uθ α * uθ s = uθ s * uθ α := by
  apply Subtype.ext
  show uMat α * uMat s = uMat s * uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem starPath_fixed {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (starPath x t) = starPath x t := by
  funext e
  change uθ α * starPath x t e * (uθ α)⁻¹ = starPath x t e
  by_cases he : e ∈ starLinks x
  · simp only [starPath,he,if_true]
    rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
  · simp [starPath,he]


end AdalyFormal.Round12.Noncancel.Gauge

namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Assembly.R3 (CofinalAnyPathCurlLine)
open AdalyFormal.Round10.Assembly.R4 (CofinalAnyPathNoResponseCancellation)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Kernel.Actual (chargedCoordinate)
open AdalyFormal.Round12.Noncancel.RightFamily

/- The three exact physical propositions are definitions, NOT inhabitants. -/
def P1 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0

def P2 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

def P3 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u

/-- Explicit integration obligations; these are not physical conjectures. -/
def StartInputs : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →
    Continuous (vacA q R (rightStar hq R) 1) ∧
    (∀ x : TwistSpace q R, x ≠ 0 →
      0 < ⟪x, vacA q R (rightStar hq R) 1 0 x⟫)

/-- Verbatim nested cofinal right-family remainder from round-12 notes B. -/
def CofinalRightStarCurlLine : Prop :=
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u

/-- Same-instance quarter gauge is unconditional. -/
theorem rightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (rightStar hq R t) = rightStar hq R t :=
  AdalyFormal.Round12.Noncancel.Gauge.starPath_fixed _ t α

/-- Conditional instance join: P1/P2 produce the SAME canonical line tested by P3. -/
theorem detected_line_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3)
    {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      CurlDetected q R u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2 := by
  obtain ⟨hc,hpd⟩ := hs hq hR hR18
  obtain ⟨h0,ht,u,hl,hfin⟩ :=
    AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi
      q R (rightStar hq R) (rightSite hq R,0) hc hpd (h1 hq hR hR18)
      (fun t => rightStar_fixed hq R t (Real.pi/4)) (h2 hq hR hR18)
  exact ⟨h0,ht,u,hl,h3 hq hR hR18 u hl,hfin⟩

/-- Conditional all-instance estimates preserve the nested dyadic/radius order. -/
theorem cofinalRightStarCurlLine_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalRightStarCurlLine := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := dvd_mul_right _ _
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  obtain ⟨_,_,u,hl,hd,_⟩ := detected_line_of_physicalInputs hs h1 h2 h3
    (by positivity : 0 < 2^j₀) hR hR18
  exact ⟨R,by dsimp [R]; omega,hR,hR18,u,hl,hd⟩

/-- The path clauses hold at the very scales/radii chosen by the supplied line
premise. Intersecting independently chosen cofinal subsequences is not used. -/
theorem cofinalAnyPathCurlLine_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,u,hl,hd⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  exact ⟨R,hR0,hR,hR18,rightStar hq R,rightStar_cont hq R,
    rightStar_an hq R,rightStar_zero hq R,rightStar_negative hq hR hR18,u,hl,hd⟩

/-- Direct round-12 response bridge; no RegularityFacts premise. -/
theorem cofinalNoCancellation_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathNoResponseCancellation :=
  AdalyFormal.Round12.Kernel.ResponseActual.cofinal_noCancellation_of_curlLine
    (cofinalAnyPathCurlLine_of_rightStar h)

/-- Conditional reduction only, not an unconditional response-hull theorem. -/
theorem cofinalNoCancellation_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_rightStar
    (cofinalRightStarCurlLine_of_physicalInputs hs h1 h2 h3)

#print axioms P1
#print axioms P2
#print axioms P3
#print axioms StartInputs
#print axioms CofinalRightStarCurlLine
#print axioms rightStar_fixed
#print axioms detected_line_of_physicalInputs
#print axioms cofinalRightStarCurlLine_of_physicalInputs
#print axioms cofinalAnyPathCurlLine_of_rightStar
#print axioms cofinalNoCancellation_of_rightStar
#print axioms cofinalNoCancellation_of_physicalInputs
end AdalyFormal.Round13.Assembly.R1

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Round4.Guarded.RefuteR1
variable {L : PeriodicLatticeExtent}
theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl

theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl
theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl
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
end FlatCarrier
end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
theorem inner_Ginv_dataS (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G)
        (Wop P.G P.U P.a (iE P.G x))⟫ + ‖(dataS sD sJ P).T x‖ ^ 2 +
      ⟪x, (dataS sD sJ P).Mass x⟫ := by
  have hD : ⟪x, (dataS sD sJ P).Dpi x⟫ = ⟪Wop P.G P.U P.a (iE P.G x),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x⟫ = _
    simp only [ContinuousLinearMap.comp_apply, DpiFullS, DeltaS]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [BaseDataS.inner_Ginv, hD]

/-- At the trivial background the plaquette Hessian is monotone in the plaquette set. -/
theorem flat_delta_le_univ {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (y : BondFnL2 L) :
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) P y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) Set.univ y⟫ := by
  have h1 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU P _ _
  have h2 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU Set.univ _ _
  change ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y⟫ ≤
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y⟫
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, h1, h2, add_zero, add_zero,
    AdalyFormal.StatementLaneR6.plaqMask_univ]
  simp only [PiLp.inner_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp only [hp, if_true, le_refl]
  · simp only [hp, if_false, inner_zero_left]
    exact real_inner_self_nonneg

theorem Ginv_loc_le_all_flat (P : IngrBParams) (hU : P.U = fun _ => 1)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [inner_Ginv_dataS, inner_Ginv_dataS]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have key : ∀ y, ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selIn _ P.G) y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selAll _ P.G) y⟫ := by
    intro y
    rw [hU]
    exact flat_delta_le_univ _ y
  linarith [key (Wop P.G P.U P.a (iE P.G x))]
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round12.Noncancel.RightFamily

/-- The actual right-star full carrier is continuous, by the frozen exterior-path theorem. -/
theorem rightStar_vacA_cont {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    Continuous (vacA q R (rightStar hq R) 1) := by
  have hc := AdalyFormal.D1Residual.GinvLit_cont (by norm_num : 0 < 2)
    (dil_admissible hq hR) (by norm_num) (by nlinarith : 17*2 ≤ R*(2*q))
    1 (dilLam q R) (rightStar hq R)
    (fun t e he => (rightStar_off_exterior hq R t e he).trans
      (rightStar_off_exterior hq R 0 e he).symm)
    (rightStar_cont hq R)
  have heq : vacA q R (rightStar hq R) 1 =
      AdalyFormal.D1Residual.GinvLit (by norm_num : 0 < 2)
        (dilTower q R) 1 (dilLam q R) (rightStar hq R) := by
    funext t
    exact vacA_rightStar hq R 1 t
  rw [heq]
  exact hc

/-- Full-carrier strict positivity at zero, not a Schur or charged-block estimate. -/
theorem rightStar_vacA_pd_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : TwistSpace q R) (hx : x ≠ 0) :
    0 < ⟪x, vacA q R (rightStar hq R) 1 0 x⟫ := by
  rw [vacA_rightStar, rightStar_zero]
  have hp := AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos hq hR x hx
  have hm := Ginv_loc_le_all_flat
    (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R)) rfl x
  exact lt_of_lt_of_le hp hm

/-- The two former integration inputs are now discharged unconditionally. -/
theorem startInputs : StartInputs := by
  intro q R hq hR hR18
  exact ⟨rightStar_vacA_cont hq hR hR18,
    rightStar_vacA_pd_zero hq (by omega)⟩

/-- The only hypotheses here are the EXACT three open physical propositions.
This is a reduction, not an inhabitant of any of those propositions. -/
theorem cofinalNoCancellation_of_P1_P2_P3 (h1 : P1) (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_physicalInputs startInputs h1 h2 h3

/-- Joint nested quantifiers: all three physical clauses at the SAME scale/radius.
Separately cofinal assertions would not justify taking an intersection. -/
def CofinalPhysicalInputs : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    (∃ w : TwistSpace (2^j) R,
      ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0) ∧
    (∀ t : ℝ, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace (2^j) R,
      x ≠ 0 → AdalyFormal.Round12.Kernel.Actual.chargedCoordinate (2^j) R
        (AdalyFormal.Round5.Guarded.IVTR2.rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫) ∧
    (∀ u : TwistSpace (2^j) R,
      AdalyFormal.Round10.Assembly.R2.KernelLine (2^j) R (rightStar (by positivity) R) u →
      AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected (2^j) R u)

/-- Cofinal physical input version of the reduction; no uniform all-q assertion is required. -/
theorem cofinalRightStarCurlLine_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    CofinalRightStarCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,hw,hp,hd⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  obtain ⟨hc,hpd⟩ := startInputs hq hR hR18
  obtain ⟨_,_,u,hl,_⟩ :=
    AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi
      (2^j) R (rightStar hq R)
      (AdalyFormal.Round5.Guarded.IVTR2.rightSite hq R,0) hc hpd hw
      (fun t => rightStar_fixed hq R t (Real.pi/4)) hp
  exact ⟨R,hR0,hR,hR18,u,hl,hd u hl⟩

theorem cofinalNoCancellation_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_rightStar (cofinalRightStarCurlLine_of_cofinalPhysical h)

#print axioms CofinalPhysicalInputs
#print axioms cofinalRightStarCurlLine_of_cofinalPhysical
#print axioms cofinalNoCancellation_of_cofinalPhysical
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_kernel
#print axioms AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos
#print axioms rightStar_vacA_cont
#print axioms rightStar_vacA_pd_zero
#print axioms startInputs
#print axioms cofinalNoCancellation_of_P1_P2_P3
end AdalyFormal.Round13.Assembly.R1

/-! Actual boundary dressing and gauge-fixing identities, for all carrier fields.
The results do not assert a crossing or response noncancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack gradCovariantAdjointValue)
variable {L : PeriodicLatticeExtent}

/-- The exact dressing potential is zero outside the first coarse region.
This includes the whole collar and does not require an inverse-unit premise. -/
theorem potential_zero_off_om1 {ell k : ℕ} (S : Tower L) (U : Cfg L)
    (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 1) :
    (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U f)) x = 0 := by
  by_cases hx0 : x ∈ S.Om 0
  · apply Gp_Rproj_lam0
    exact ⟨fun μ => by simp, hx0, by simpa using hx⟩
  · exact Gp_Rproj_out _ _ _ _ hx0

/-- W agrees pointwise with the original field on every bond with both endpoints
outside Omega_1. This is not restricted to a single-bond test field. -/
theorem Wop_eq_on_collar {ell k : ℕ} (S : Tower L) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) (e : Bond L)
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  have hz : (gradL2 U (Gp (geomOf ell k S) U a
      (Rproj (geomOf ell k S) U (gradAdj U A)))) e = 0 := by
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [potential_zero_off_om1 S U a _ h0, potential_zero_off_om1 S U a _ h1]
    simp
  change A e - (gradL2 U (Gp (geomOf ell k S) U a
    (Rproj (geomOf ell k S) U (gradAdj U A)))) e = A e
  rw [hz, sub_zero]

/-- Every omitted plaquette is in the collar. Therefore its four dressed atoms
are exactly the four raw atoms, for an arbitrary fine field. -/
theorem Wop_eq_on_omitted {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R*M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  obtain ⟨h0,h1⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  exact Wop_eq_on_collar S U a A e h0 h1

/-- A single bond of arbitrary orientation has divergence supported at its endpoints. -/
theorem gradAdj_sing_support (U : Cfg L) (e : Bond L) (X : SuTwo)
    (z : PeriodicLatticeSite L) (hz0 : z ≠ e.1)
    (hz1 : z ≠ periodicLatticeShift e.1 e.2) :
    gradAdj U (sing e X) z = 0 := by
  rw [show gradAdj U (sing e X) z = (WithLp.ofLp (gradAdj U (sing e X))) z from rfl,
    gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h0 : (WithLp.ofLp (sing e X)) (z,μ) = 0 :=
    sing_apply_ne _ _ (fun h => hz0 (congrArg Prod.fst h))
  have h1 : (WithLp.ofLp (sing e X)) (periodicLatticeShiftBack z μ,μ) = 0 := by
    apply sing_apply_ne
    intro h
    have hμ : μ = e.2 := congrArg Prod.snd h
    have hx : periodicLatticeShiftBack z μ = e.1 := congrArg Prod.fst h
    apply hz1
    rw [← hx, ← hμ, periodicLatticeShift_shiftBack]
  rw [h0,h1]
  simp

/-- On a finite-radius boundary patch, a raw single-bond field has zero gauge term.
The same exterior witness can be used for any orientation, including tangential leaves. -/
theorem Tfull_sing_zero_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Tfull (geomOf ell k S) U (sing e X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : z = e.1 ∨ z = periodicLatticeShift e.1 e.2
  · have huz : u z = 0 := by
      apply RImage_support S U hu z
      intro y hy hy1
      have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) x hx y hy1
      have hxz : pdist x z ≤ d := by
        rcases hz with rfl | rfl
        · exact h0
        · exact h1
      have hyz : pdist z y ≤ 1 := hy
      have ht := pdist_triangle x z y
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hcl
      omega
    rw [huz]
    simp
  · push Not at hz
    rw [gradAdj_sing_support U e X z hz.1 hz.2]
    simp

theorem Wop_sing_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (a : ℝ) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Wop (geomOf ell k S) U a (sing e X) = sing e X := by
  have ht := Tfull_sing_zero_near hS hd U e X x hx h0 h1
  unfold Tfull at ht
  simp only [ContinuousLinearMap.comp_apply] at ht
  unfold Wop
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [ht]
  simp

#print axioms potential_zero_off_om1
#print axioms Wop_eq_on_collar
#print axioms Wop_eq_on_omitted
#print axioms gradAdj_sing_support
#print axioms Tfull_sing_zero_near
#print axioms Wop_sing_near
end AdalyFormal.Round12.Noncancel.Boundary

/-! The frozen mass contains each distinct level-zero leaf mass with its exact weight.
These are actual carrier estimates, not entries of a numerical Schur matrix. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Mass
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
variable {L : PeriodicLatticeExtent}

def rowZero (G : TowerGeom L) (e : Bond L) (he : e ∈ bondsLam G 0) : BIdx G :=
  ⟨⟨0,Nat.zero_lt_succ _⟩,e,he⟩

theorem Qfull_rowZero (G : TowerGeom L) (U : Cfg L)
    (e : Bond L) (he : e ∈ bondsLam G 0) (A : BondFnL2 L) :
    QfullOf G U A (rowZero G e he) = A e := by
  change (((G.ell : ℝ)^0)⁻¹) • (QlinB G U 0 A) e = _
  rw [QlinB_zero]
  simp

/-- Geometric membership of any touching collar bond in the actual level-zero rows. -/
theorem collar_levelZero {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (e : Bond L)
    (ht : e ∈ bondsOm0 (geomOf ell k S))
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    e ∈ bondsLam (geomOf ell k S) 0 := by
  by_contra h
  rcases endpoint_om1 hell hS e ht h with h | h
  · exact h0 h
  · exact h1 h

/-- Any selected finite family of DISTINCT physical level-zero bonds can be
removed from the mass, leaving a nonnegative remainder. -/
theorem leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    a * ∑ e ∈ leaves, ‖A e‖^2 ≤ ⟪A,MassFull G a (bondSectorOf G U) A⟫ := by
  classical
  let f : BIdx G → ℝ := fun p => a*(G.ell : ℝ)^(p.1 : ℕ)*‖QfullOf G U A p‖^2
  let r : {e // e ∈ leaves} → BIdx G := fun e => rowZero G e.val (hl e.val e.property)
  have hinj : Function.Injective r := by
    intro e e' h
    apply Subtype.ext
    exact congrArg (fun p : BIdx G => p.2.val) h
  have hterm (e : {e // e ∈ leaves}) : f (r e) = a * ‖A e.val‖^2 := by
    change a*(G.ell : ℝ)^0*‖QfullOf G U A (rowZero G e.val (hl e.val e.property))‖^2 = _
    rw [Qfull_rowZero]
    simp
  have hsum : (∑ e : {e // e ∈ leaves}, f (r e)) = a * ∑ e ∈ leaves, ‖A e‖^2 := by
    rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort leaves (fun e => ‖A e‖^2)
  have hn : ∀ p, 0 ≤ f p := fun p => mul_nonneg (mul_nonneg ha (by positivity)) (sq_nonneg _)
  rw [inner_MassFull]
  change _ ≤ ∑ p, f p
  rw [← hsum, ← Finset.sum_image (fun x _ y _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hn p)

/-- The same estimate on the actual touching-bond carrier. -/
theorem carrier_leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (u : ↥(bondSupp G)) :
    a * ∑ e ∈ leaves, ‖(iE G u) e‖^2 ≤
      ⟪u, pE G (MassFull G a (bondSectorOf G U) (iE G u))⟫ := by
  rw [pE_inner_right]
  exact leaf_mass_le G U a ha leaves hl (iE G u)

/-- An actual finite decomposition of the mass with a nonnegative remainder. -/
theorem mass_split (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    ∃ rest : ℝ, 0 ≤ rest ∧ ⟪A,MassFull G a (bondSectorOf G U) A⟫ =
      rest + a * ∑ e ∈ leaves, ‖A e‖^2 := by
  refine ⟨⟪A,MassFull G a (bondSectorOf G U) A⟫ - a*∑ e ∈ leaves, ‖A e‖^2,
    sub_nonneg.mpr (leaf_mass_le G U a ha leaves hl A), ?_⟩
  ring

#print axioms rowZero
#print axioms Qfull_rowZero
#print axioms collar_levelZero
#print axioms leaf_mass_le
#print axioms carrier_leaf_mass_le
#print axioms mass_split
end AdalyFormal.Round12.Noncancel.Mass

/-! Finite exterior-star estimates and a whole-kernel trace criterion.
No application to a physical crossing is asserted by this file. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Star
open scoped RealInnerProductSpace

/-- Two ordered charged contributions to one plaquette. -/
def pairForm (c s : ℝ) (y z : ℂ) : ℝ :=
  c * Complex.normSq (y + z) + 2 * s * (star y * z).im

/-- Three ordered charged contributions; the fourth (exterior) field is zero. -/
def tripleForm (c s : ℝ) (x y z : ℂ) : ℝ :=
  c * Complex.normSq (x + y + z) +
    2 * s * ((star x * y).im + (star x * z).im + (star y * z).im)

theorem tripleForm_zero_left (c s : ℝ) (y z : ℂ) :
    tripleForm c s 0 y z = pairForm c s y z := by
  simp [tripleForm, pairForm]

theorem tripleForm_zero_middle (c s : ℝ) (x z : ℂ) :
    tripleForm c s x 0 z = pairForm c s x z := by
  simp [tripleForm, pairForm]

theorem tripleForm_zero_right (c s : ℝ) (x y : ℂ) :
    tripleForm c s x y 0 = pairForm c s x y := by
  simp [tripleForm, pairForm]

/-- Exact completion of the square, with the two leaf mass terms retained. -/
theorem pair_completion (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    Complex.normSq y + Complex.normSq z + pairForm c s y z =
      c * (Complex.normSq y + Complex.normSq z) +
        Complex.normSq (y + ((c : ℂ) - (s : ℂ) * Complex.I) * z) := by
  simp only [pairForm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im,
    congrArg (fun a : ℝ => a * z.re^2) hcs,
    congrArg (fun a : ℝ => a * z.im^2) hcs]

theorem pair_mass_lower (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    c * (Complex.normSq y + Complex.normSq z) ≤
      Complex.normSq y + Complex.normSq z + pairForm c s y z := by
  rw [pair_completion c s hcs]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

/-- Number of arms is arbitrary. Only a positive base form and disjoint leaf masses enter. -/
theorem star_mass_lower {ι : Type*} [Fintype ι]
    (c s rest : ℝ) (hc : c ≤ 1) (hr : 0 ≤ rest) (hcs : c^2 + s^2 = 1)
    (y z : ι → ℂ) :
    c * (rest + ∑ i, (Complex.normSq (y i) + Complex.normSq (z i))) ≤
      rest + ∑ i, (Complex.normSq (y i) + Complex.normSq (z i) +
        pairForm c s (y i) (z i)) := by
  have h := Finset.sum_le_sum (fun (i : ι) (_ : i ∈ Finset.univ) =>
    pair_mass_lower c s hcs (y i) (z i))
  rw [← Finset.mul_sum] at h
  have hh : c * rest ≤ rest := by nlinarith
  nlinarith

section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single complex trace is injective on the whole kernel if its zero fiber is positive. -/
theorem trace_ne_zero (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    {u : E} (hu : A u = 0) (hne : u ≠ 0) : l u ≠ 0 := by
  intro hl
  have h := hp u hl hne
  simp only [hu, inner_zero_right, lt_self_iff_false] at h

theorem trace_kernel_injective (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫) :
    Function.Injective (fun u : A.ker => l u) := by
  intro u v huv
  change l (u : E) = l (v : E) at huv
  apply Subtype.ext
  by_contra h
  have hne : (u : E) - v ≠ 0 := sub_ne_zero.mpr h
  have ha : A ((u : E) - v) = 0 := by
    rw [map_sub, u.property, v.property, sub_self]
  exact trace_ne_zero A l hp ha hne (by rw [map_sub, huv, sub_self])

/-- U(1) plus one injective trace gives the entire charged line; no character screen. -/
theorem kernel_line_of_trace (A J : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ u, A (J u) = J (A u))
    (htrace : ∀ u, l (J u) = Complex.I * l u)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    (u₀ : E) (hu₀ : A u₀ = 0) (hne : u₀ ≠ 0) :
    J (J u₀) = -u₀ ∧
      ∀ u, A u = 0 → u ∈ Submodule.span ℝ {u₀, J u₀} := by
  have hzero (v : E) (ha : A v = 0) (hl : l v = 0) : v = 0 := by
    by_contra hn
    exact trace_ne_zero A l hp ha hn hl
  have hJu : A (J u₀) = 0 := by rw [hcomm, hu₀, map_zero]
  have hJl : A (J (J u₀)) = 0 := by rw [hcomm, hJu, map_zero]
  have ht : l u₀ ≠ 0 := trace_ne_zero A l hp hu₀ hne
  constructor
  · apply eq_neg_of_add_eq_zero_left
    apply hzero
    · rw [map_add, hJl, hu₀, add_zero]
    · rw [map_add, htrace, htrace, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
        neg_add_cancel]
  · intro u hu
    let a : ℂ := l u / l u₀
    have hac : a * l u₀ = l u := div_mul_cancel₀ _ ht
    have hlin : l (a.re • u₀ + a.im • J u₀) = l u := by
      rw [map_add, map_smul, map_smul, htrace]
      change (a.re : ℂ) * l u₀ + (a.im : ℂ) * (Complex.I * l u₀) = l u
      calc
        _ = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) * l u₀ := by ring
        _ = a * l u₀ := by rw [Complex.re_add_im]
        _ = l u := hac
    have heq : u = a.re • u₀ + a.im • J u₀ := by
      apply sub_eq_zero.mp
      apply hzero
      · rw [map_sub, hu, map_add, map_smul, map_smul, hu₀, hJu,
          smul_zero, smul_zero, add_zero, sub_zero]
      · rw [map_sub, hlin, sub_self]
    rw [heq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The precise local-star input sufficient for the positivity clause above. -/
theorem positive_on_trace_zero {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ) (rest : E → ℝ)
    (y z : E → ι → ℂ) (c s : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcs : c^2 + s^2 = 1) (hr : ∀ u, 0 ≤ rest u)
    (hbase : ∀ u, u ≠ 0 →
      0 < rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i)))
    (hform : ∀ u, l u = 0 → ⟪u, A u⟫ =
      rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i) +
        pairForm c s (y u i) (z u i))) :
    ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫ := by
  intro u hl hn
  rw [hform u hl]
  exact lt_of_lt_of_le (mul_pos hc (hbase u hn))
    (star_mass_lower c s (rest u) hc1 (hr u) hcs (y u) (z u))
end Kernel

/-- Exact rational test energy on the proposed four-arm boundary star at pi/2.
The 16 comes from four leaf masses and twelve untwisted plaquettes.
The last two terms add one tangential boundary bond. Physical identification is separate. -/
def starTrialEnergy (a b : ℝ) : ℝ := 1 + 16*a^2 - 8*a - 2*b + 4*b^2

theorem starTrial_null : starTrialEnergy (1/4) 0 = 0 := by
  norm_num [starTrialEnergy]

theorem starTrial_negative : starTrialEnergy (1/4) (1/4) = -1/4 := by
  norm_num [starTrialEnergy]

#print axioms pairForm
#print axioms tripleForm
#print axioms tripleForm_zero_left
#print axioms tripleForm_zero_middle
#print axioms tripleForm_zero_right
#print axioms pair_completion
#print axioms pair_mass_lower
#print axioms star_mass_lower
#print axioms trace_ne_zero
#print axioms trace_kernel_injective
#print axioms kernel_line_of_trace
#print axioms positive_on_trace_zero
#print axioms starTrialEnergy
#print axioms starTrial_null
#print axioms starTrial_negative
end AdalyFormal.Round12.Noncancel.Star

/-! Exact frozen per-plaquette formula. These hypotheses specify transported
bond values and holonomy entries, not a replacement operator. -/
namespace AdalyFormal.Round12.Noncancel.Plaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star

/-- Matrix of a charged Lie-algebra element, with its actual upper-right coordinate. -/
def chargedMat (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, z; -star z, 0]
def realHol (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (c : ℂ) • 1
def imagHol (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(s : ℂ), 0; 0, -(s : ℂ)]

theorem chargedMat_add (y z : ℂ) : chargedMat (y+z) = chargedMat y + chargedMat z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chargedMat, add_comm]

theorem chargedMat_zero : chargedMat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chargedMat]

theorem charged_inner (X : SuTwo) (z : ℂ)
    (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) = chargedMat z) :
    ⟪X, X⟫ = Complex.normSq z := by
  change hsInner X X = _
  rw [hsInner_entries, hX]
  simp [chargedMat, Complex.normSq_apply, Complex.mul_re]
  ring

theorem first_atom (c : ℝ) (z : ℂ) :
    (Matrix.trace (smulILM (chargedMat z) * smulILM (chargedMat z) *
      (realHol c - 1))).re = 2*(c-1)*Complex.normSq z := by
  simp [chargedMat, realHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem comm_atom (s : ℝ) (y z : ℂ) :
    (Matrix.trace (smulILM (smulILM (chargedMat y)) * smulILM (chargedMat z) *
      imagHol s)).re -
    (Matrix.trace (smulILM (smulILM (chargedMat z)) * smulILM (chargedMat y) *
      imagHol s)).re = 4*s*(star y*z).im := by
  simp [chargedMat, imagHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]
  ring

variable {L : PeriodicLatticeExtent}

theorem curl_atoms (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM U p A = a1LM U p A + a2LM p A + a3LM p A + a4LM U p A := by
  rw [curlMatLM_apply, a1LM_apply, a2LM_apply, a3LM_apply, a4LM_apply,
    ← sum_Aprime_eq_curl]
  change (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = _
  abel

/-- Source normalization is exactly one half of the raw frozen diagonal bilPlaq. -/
theorem frozen_three_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = chargedMat y) (h4 : a4LM U p A = chargedMat z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z := by
  have hc : curlMatLM U p A = chargedMat (x+y+z) := by
    rw [curl_atoms, h1, h2, h3, h4, add_zero, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z) := charged_inner _ _ hc
  rw [hn, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply,
    hr, hi, hc, h1, h2, h3, h4, map_zero, mul_zero, zero_mul, Matrix.trace_zero,
    Complex.zero_re, sub_zero, add_zero]
  rw [first_atom, comm_atom, comm_atom, comm_atom]
  unfold tripleForm
  ring

/-- Right-boundary version, with the exterior (fourth) atom zero. -/
theorem frozen_three_form_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z := by
  have hc : curlMatLM U p A = chargedMat (x+y+z) := by
    rw [curl_atoms, h1, h2, h3, h4, add_zero, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z) := charged_inner _ _ hc
  rw [hn, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply,
    hr, hi, hc, h1, h2, h3, h4, map_zero, mul_zero, zero_mul, Matrix.trace_zero,
    Complex.zero_re, sub_zero, add_zero]
  rw [first_atom, comm_atom, comm_atom, comm_atom]
  unfold tripleForm
  ring

/-- Left boundary: the first normal atom and the exterior second atom vanish. -/
theorem frozen_two_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = 0) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = chargedMat y) (h4 : a4LM U p A = chargedMat z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = pairForm c s y z := by
  rw [← tripleForm_zero_left]
  exact frozen_three_form U p A c s 0 y z hr hi
    (h1.trans chargedMat_zero.symm) h2 h3 h4

#print axioms chargedMat
#print axioms realHol
#print axioms imagHol
#print axioms chargedMat_add
#print axioms chargedMat_zero
#print axioms charged_inner
#print axioms first_atom
#print axioms comm_atom
#print axioms curl_atoms
#print axioms frozen_three_form
#print axioms frozen_three_form_right
#print axioms frozen_two_form
end AdalyFormal.Round12.Noncancel.Plaquette


namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

abbrev Fine (q R : ℕ) := scaleUp 2 1 (dilLu q R)

theorem seven_le_side {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    7 ≤ Fine q R μ + 1 := by
  rw [dil_fine_size hq]
  split_ifs <;> omega

/-- A seven-site coordinate box centered at the actual right boundary point. -/
def patchSite {q : ℕ} (hq : 0 < q) (R : ℕ) (v : Fin 3 → Fin 7) :
    PeriodicLatticeSite (Fine q R) :=
  fun μ => rightSite hq R μ + (Fin.castLE (seven_le_side hq R μ) (v μ) - 3)

theorem patchSite_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (patchSite hq R) := by
  intro v w h
  funext μ
  have he := congrFun h μ
  dsimp [patchSite] at he
  have he' := add_left_cancel he
  have he'' := sub_left_inj.mp he'
  exact Fin.ext (congrArg (fun a : Fin (Fine q R μ+1) => a.val) he'')

theorem castLE_add_one {n : ℕ} (hn : 7 ≤ n+1) (v : Fin 7) (hv : v.val < 6) :
    Fin.castLE hn (v + 1) = Fin.castLE hn v + (1 : Fin (n+1)) := by
  apply Fin.ext
  simp only [Fin.val_castLE, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega : 1 < 7), Nat.mod_eq_of_lt (by omega : 1 < n+1),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < 7),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < n+1)]

theorem patchSite_shift {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    periodicLatticeShift (patchSite hq R v) μ =
      patchSite hq R (Function.update v μ (v μ + 1)) := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp only [periodicLatticeShift, Function.update_self, patchSite]
    rw [castLE_add_one _ _ hv]
    abel
  · simp [periodicLatticeShift, patchSite, Function.update_of_ne h]

def centerCoord : Fin 3 → Fin 7 := ![3,3,3]

theorem patchSite_center {q : ℕ} (hq : 0 < q) (R : ℕ) :
    patchSite hq R centerCoord = rightSite hq R := by
  funext μ
  have hc : Fin.castLE (seven_le_side hq R μ) (centerCoord μ) = (3 : Fin (Fine q R μ+1)) := by
    apply Fin.ext
    have hμ : 3 < Fine q R μ+1 := lt_of_lt_of_le (by decide) (seven_le_side hq R μ)
    have hv : (centerCoord μ).val = 3 := by fin_cases μ <;> rfl
    change (centerCoord μ).val = 3 % (Fine q R μ+1)
    rw [hv, Nat.mod_eq_of_lt hμ]
  simp [patchSite, hc]

/-- Six distinct physical bonds; index 5 is the essential tangent correction. -/
def trialCoord : Fin 6 → (Fin 3 → Fin 7) :=
  ![![3,3,3], ![3,4,3], ![3,2,3], ![3,3,4], ![3,3,2], ![3,3,3]]
def trialDir : Fin 6 → Fin 3 := ![0,0,0,0,0,1]
def trialBond {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) : Bond (Fine q R) :=
  (patchSite hq R (trialCoord i), trialDir i)

theorem trialBond_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (trialBond hq R) := by
  intro i j h
  have hc := patchSite_injective hq R (congrArg Prod.fst h)
  have hd := congrArg Prod.snd h
  change trialDir i = trialDir j at hd
  fin_cases i <;> fin_cases j <;> simp_all [trialCoord, trialDir, funext_iff, Fin.forall_fin_succ]

/-- Charged Lie-algebra vector with its actual upper-right matrix entry z. -/
def charged (z : ℂ) : SuTwo :=
  ⟨!![0,z;-star z,0], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩

theorem charged_norm (z : ℂ) : ‖charged z‖^2 = Complex.normSq z := by
  rw [← real_inner_self_eq_norm_sq]
  change hsInner (charged z) (charged z) = _
  rw [hsInner_self_entries]
  simp [charged]

def trialAmplitude : Fin 6 → ℂ :=
  ![1, -Complex.I/4, Complex.I/4, -Complex.I/4, Complex.I/4, -Complex.I/4]

def trialField {q : ℕ} (hq : 0 < q) (R : ℕ) : BondFnL2 (Fine q R) :=
  ∑ i : Fin 6, sing (trialBond hq R i) (charged (trialAmplitude i))

theorem trialField_apply {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R)) :
    trialField hq R e = ∑ i : Fin 6,
      if e = trialBond hq R i then charged (trialAmplitude i) else 0 := by
  simp [trialField, sing_apply]

theorem trialField_at {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialField hq R (trialBond hq R i) = charged (trialAmplitude i) := by
  rw [trialField_apply]
  simp only [(trialBond_injective hq R).eq_iff]
  simp

theorem trialField_support {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R))
    (he : trialField hq R e ≠ 0) : ∃ i : Fin 6, e = trialBond hq R i := by
  by_contra h
  push Not at h
  apply he
  rw [trialField_apply]
  simp [h]

theorem trialField_norm {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialField hq R‖^2 = (21/16 : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hs : (∑ e : Bond (Fine q R), ‖trialField hq R e‖^2) =
      ∑ i : Fin 6, ‖trialField hq R (trialBond hq R i)‖^2 := by
    rw [← Finset.sum_image (f := fun e : Bond (Fine q R) => ‖trialField hq R e‖^2)
      (s := Finset.univ) (g := trialBond hq R)
      (fun i _ j _ h => trialBond_injective hq R h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hz : trialField hq R e = 0 := by
      by_contra hn
      obtain ⟨i,rfl⟩ := trialField_support hq R e hn
      exact he (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp [hz]
  rw [hs]
  simp only [trialField_at, charged_norm]
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply]

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.patchSite_injective
#print axioms AdalyFormal.Round13.Trial.patchSite_shift
#print axioms AdalyFormal.Round13.Trial.patchSite_center
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.charged_norm
#print axioms AdalyFormal.Round13.Trial.trialField_at
#print axioms AdalyFormal.Round13.Trial.trialField_support
#print axioms AdalyFormal.Round13.Trial.trialField_norm

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

theorem trial_sites {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (fun i : Fin 6 => (trialBond hq R i).1) =
      ![rightSite hq R, periodicLatticeShift (rightSite hq R) 1,
        periodicLatticeShiftBack (rightSite hq R) 1,
        periodicLatticeShift (rightSite hq R) 2,
        periodicLatticeShiftBack (rightSite hq R) 2, rightSite hq R] := by
  have hp1 := patchSite_shift hq R centerCoord 1 (by decide)
  have hp2 := patchSite_shift hq R centerCoord 2 (by decide)
  have hm1 := patchSite_shift hq R (trialCoord 2) 1 (by decide)
  have hm2 := patchSite_shift hq R (trialCoord 4) 2 (by decide)
  rw [patchSite_center] at hp1 hp2
  have hu1 : Function.update centerCoord 1 (centerCoord 1+1) = trialCoord 1 := by decide
  have hu2 : Function.update centerCoord 2 (centerCoord 2+1) = trialCoord 3 := by decide
  have hd1 : Function.update (trialCoord 2) 1 (trialCoord 2 1+1) = centerCoord := by decide
  have hd2 : Function.update (trialCoord 4) 2 (trialCoord 4 2+1) = centerCoord := by decide
  rw [hu1] at hp1
  rw [hu2] at hp2
  rw [hd1, patchSite_center] at hm1
  rw [hd2, patchSite_center] at hm2
  have hm1' := congrArg (fun z => periodicLatticeShiftBack z 1) hm1
  have hm2' := congrArg (fun z => periodicLatticeShiftBack z 2) hm2
  rw [periodicLatticeShiftBack_shift] at hm1' hm2'
  funext i
  fin_cases i
  · exact patchSite_center hq R
  · exact hp1.symm
  · exact hm1'
  · exact hp2.symm
  · exact hm2'
  · exact patchSite_center hq R

theorem trial_start_near {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (rightSite hq R) (trialBond hq R i).1 ≤ 1 := by
  have h := congrFun (trial_sites hq R) i
  rw [h]
  fin_cases i
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega

theorem trial_start_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    ((trialBond hq R i).1 0).val = 12*(R*q)+12*q-1 := by
  have hv : trialCoord i 0 = (3 : Fin 7) := by fin_cases i <;> rfl
  have hc : Fin.castLE (seven_le_side hq R 0) (3 : Fin 7) = (3 : Fin (Fine q R 0+1)) := by
    apply Fin.ext
    change 3 = 3 % (Fine q R 0+1)
    rw [Nat.mod_eq_of_lt (by have := seven_le_side hq R 0; omega)]
  simp [trialBond, patchSite, hv, hc, rightSite]

theorem trial_touch {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialBond hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  apply Or.inl
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  rw [trial_start_zero]
  omega

theorem trial_collar {q R : ℕ} (hq : 0 < q) (hR18 : 18 ≤ R) (i : Fin 6) :
    (trialBond hq R i).1 ∉ (dilTower q R).Om 1 ∧
      periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2 ∉
        (dilTower q R).Om 1 := by
  have hr : 18*q ≤ R*q := Nat.mul_le_mul_right q hR18
  constructor
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [trial_start_zero]
    omega
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [dil_shift_zero hq, trial_start_zero]
    split_ifs
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · omega

theorem trial_levelZero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (i : Fin 6) :
    trialBond hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 :=
  collar_levelZero (dil_admissible hq hR) (by norm_num) _ (trial_touch hq R i)
    (trial_collar hq hR18 i).1 (trial_collar hq hR18 i).2

theorem trialField_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialField hq R ∈ bondSupp (geomOf 2 1 (dilTower q R)) := by
  intro e he
  by_contra hn
  obtain ⟨i,rfl⟩ := trialField_support hq R e hn
  exact he (trial_touch hq R i)

def trialVector {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) := ⟨trialField hq R,trialField_mem hq R⟩

theorem trial_near_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (periodicLatticeShift (rightSite hq R) 0) (trialBond hq R i).1 ≤ 2 ∧
    pdist (periodicLatticeShift (rightSite hq R) 0)
      (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2) ≤ 3 := by
  have h1 : pdist (periodicLatticeShift (rightSite hq R) 0) (rightSite hq R) ≤ 1 := by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]
    exact pdist_shift_le _ _
  have h2 := trial_start_near hq R i
  have ht := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (rightSite hq R) (trialBond hq R i).1
  have h3 := pdist_shift_le (trialBond hq R i).1 (trialBond hq R i).2
  have ht' := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (trialBond hq R i).1 (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2)
  omega

theorem trialField_hsupp {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∀ e : Bond (Fine q R), trialField hq R e ≠ 0 →
      ∃ w : PeriodicLatticeSite (Fine q R), w ∉ (dilTower q R).Om 0 ∧ pdist e.1 w ≤ 2 := by
  intro e he
  obtain ⟨i,rfl⟩ := trialField_support hq R e he
  exact ⟨periodicLatticeShift (rightSite hq R) 0, (rightSite_bd hq R).hx', by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact (trial_near_exterior hq R i).1⟩

/-- All positive-level physical blocking rows vanish, for arbitrary background U. -/
theorem trial_higher_rows_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ 1)
    {b : Bond (Fine q R)} (hb : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) j) :
    QlinB (geomOf 2 1 (dilTower q R)) U j (trialField hq R) b = 0 := by
  exact QlinB_supp_zero (dil_admissible hq hR) (by norm_num) (by nlinarith)
    U (trialField hq R) (trialField_hsupp hq R) hj hjk hb

theorem trial_mass_upper {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ ≤ (21/16 : ℝ) := by
  have h := Mass_supp_le (dil_admissible hq hR) (by norm_num) (by nlinarith)
    U 1 (by norm_num) (trialField hq R) (trialField_hsupp hq R)
  simpa only [trialField_norm, one_mul] using h

/-- Exact physical mass, not a lower estimate: the frozen higher rows contribute zero. -/
theorem trial_mass_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ = (21/16 : ℝ) := by
  apply le_antisymm (trial_mass_upper hq hR hR18 U)
  have h := leaf_mass_le (geomOf 2 1 (dilTower q R)) U 1 (by norm_num)
    (Finset.univ.image (trialBond hq R)) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact trial_levelZero hq hR hR18 i) (trialField hq R)
  rw [Finset.sum_image (fun i _ j _ h => trialBond_injective hq R h)] at h
  simp only [one_mul, trialField_at, charged_norm] at h
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply] at h ⊢
  exact h

theorem trial_T_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) : Tfull (geomOf 2 1 (dilTower q R)) U (trialField hq R) = 0 := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact Tfull_sing_zero_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2

theorem trial_W_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) (a : ℝ) :
    Wop (geomOf 2 1 (dilTower q R)) U a (trialField hq R) = trialField hq R := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Wop_sing_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U a _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.trial_sites
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.trialField_norm
#print axioms AdalyFormal.Round13.Trial.trialField_mem
#print axioms AdalyFormal.Round13.Trial.trial_higher_rows_zero
#print axioms AdalyFormal.Round13.Trial.trial_mass_upper
#print axioms AdalyFormal.Round13.Trial.trial_mass_eq
#print axioms AdalyFormal.Round13.Trial.trial_T_zero
#print axioms AdalyFormal.Round13.Trial.trial_W_eq

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open Classical

def stepCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ+1)
def backCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ-1)

theorem patchSite_back {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : 0 < (v μ).val) :
    periodicLatticeShiftBack (patchSite hq R v) μ = patchSite hq R (backCoord v μ) := by
  have hb : ((backCoord v μ) μ).val < 6 := by
    simp only [backCoord, Function.update_self]
    have hvlt := (v μ).isLt
    rw [Fin.val_sub]
    norm_num
    omega
  have h := patchSite_shift hq R (backCoord v μ) μ hb
  have hu : Function.update (backCoord v μ) μ ((backCoord v μ) μ+1) = v := by
    simp [backCoord]
  rw [hu] at h
  have hh := congrArg (fun z => periodicLatticeShiftBack z μ) h
  rw [periodicLatticeShiftBack_shift] at hh
  exact hh.symm

def d02 : PeriodicPlaquetteDirections := ⟨(0,2),by decide⟩
def d12 : PeriodicPlaquetteDirections := ⟨(1,2),by decide⟩

def trialPlaqPattern : Fin 19 → ((Fin 3 → Fin 7) × PeriodicPlaquetteDirections) :=
  ![(![2,3,3],d01), (![3,1,3],d01), (![3,2,2],d01), (![3,2,2],d02),
    (![3,2,3],d01), (![3,2,3],d02), (![3,2,4],d01), (![3,3,1],d02),
    (![3,3,2],d01), (![3,3,2],d02), (![3,3,2],d12), (![3,3,3],d01),
    (![3,3,3],d02), (![3,3,3],d12), (![3,3,4],d01), (![3,3,4],d02),
    (![3,4,2],d02), (![3,4,3],d01), (![3,4,3],d02)]

def trialPlaq {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) : PeriodicLatticePlaquette (Fine q R) :=
  (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2)

theorem trialPlaqPattern_injective : Function.Injective trialPlaqPattern := by decide

theorem trialPlaq_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (trialPlaq hq R) := by
  intro i j h
  apply trialPlaqPattern_injective
  exact Prod.ext (patchSite_injective hq R (congrArg Prod.fst h))
    (congrArg (fun p : PeriodicLatticePlaquette (Fine q R) => p.2) h)

theorem pattern_front : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    (d.1.1 = trialDir i ∨ d.1.2 = trialDir i) →
      ∃ k : Fin 19, trialPlaqPattern k = (trialCoord i,d) := by decide

theorem pattern_back1 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.1 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.2,d) := by decide

theorem pattern_back2 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.2 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.1,d) := by decide

theorem trialCoord_positive (i : Fin 6) (μ : Fin 3) : 0 < (trialCoord i μ).val := by
  fin_cases i <;> fin_cases μ <;> decide

theorem front_mem {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i ∨ d.1.2 = trialDir i) :
    (patchSite hq R (trialCoord i),d) ∈ Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_front i d hd
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

theorem back_mem1 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.2,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back1 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

theorem back_mem2 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.2 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.1,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back2 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩

/-- All plaquettes outside the explicit nineteen have exactly zero frozen contribution,
for every background, not only for the right star. -/
theorem trial_plaq_zero_off {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R))
    (p : PeriodicLatticePlaquette (Fine q R)) (hp : p ∉ Finset.univ.image (trialPlaq hq R)) :
    contrib U (WithLp.ofLp (trialField hq R)) p = 0 := by
  have hc : curlValueCovariant U (WithLp.ofLp (trialField hq R)) p = 0 ∧
      bilPlaq U p (WithLp.ofLp (trialField hq R)) (WithLp.ofLp (trialField hq R)) = 0 := by
    apply curl_bil_zero
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.2 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem1 hq R i p.2 hd)
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inr hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inl hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.1 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem2 hq R i p.2 hd)
  unfold contrib
  rw [hc.1, hc.2]
  change ⟪(0 : SuTwo), 0⟫ + (1/2 : ℝ)*0 = 0
  simp

/-- Exact enumeration of the FROZEN all-plaquette form. No integer-lattice surrogate. -/
theorem trial_delta_sum {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R)) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ (trialField hq R)⟫ =
      ∑ i : Fin 19, contrib U (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) := by
  rw [delta_form_sum]
  change (∑ p, contrib U (WithLp.ofLp (trialField hq R)) p) = _
  rw [← Finset.sum_image (f := contrib U (WithLp.ofLp (trialField hq R)))
    (s := Finset.univ) (g := trialPlaq hq R)
    (fun i _ j _ h => trialPlaq_injective hq R h)]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => trial_plaq_zero_off hq R U p hp)

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.patchSite_back
#print axioms AdalyFormal.Round13.Trial.trialPlaq_injective
#print axioms AdalyFormal.Round13.Trial.pattern_front
#print axioms AdalyFormal.Round13.Trial.pattern_back1
#print axioms AdalyFormal.Round13.Trial.pattern_back2
#print axioms AdalyFormal.Round13.Trial.trial_plaq_zero_off
#print axioms AdalyFormal.Round13.Trial.trial_delta_sum

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

def quadForm (c s : ℝ) (x y z w : ℂ) : ℝ :=
  c * Complex.normSq (x+y+z+w) + 2*s*((star x*y).im+(star x*z).im+
    (star x*w).im+(star y*z).im+(star y*w).im+(star z*w).im)

/-- Four-atom extension of the copied frozen three-atom identity. -/
theorem frozen_four_form {L : PeriodicLatticeExtent} (U : Cfg L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z w : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = chargedMat w) :
    contrib U A p = quadForm c s x y z w := by
  have hc : curlMatLM U p A = chargedMat (x+y+z+w) := by
    rw [curl_atoms, h1, h2, h3, h4, chargedMat_add, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z+w) := charged_inner _ _ hc
  unfold contrib
  change ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ + _ = _
  rw [hn, bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4]
  rw [first_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom]
  unfold quadForm
  ring

def anchorCoord : Fin 3 → Fin 7 := ![4,3,3]

theorem star_anchor {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (rightSite hq R) 0 = patchSite hq R anchorCoord := by
  have h := patchSite_shift hq R centerCoord 0 (by decide)
  rw [patchSite_center] at h
  have he : Function.update centerCoord 0 (centerCoord 0+1) = anchorCoord := by decide
  simpa only [he] using h

def localStar (v : Fin 3 → Fin 7) (μ : Fin 3) : Prop :=
  μ ≠ 0 ∧ (v = anchorCoord ∨ stepCoord v μ = anchorCoord)

theorem rightStar_patch {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    rightStar hq R t (patchSite hq R v,μ) =
      if localStar v μ then uθ t else 1 := by
  unfold rightStar starPath starLinks
  simp only [Set.mem_setOf_eq, star_anchor, patchSite_shift hq R v μ hv,
    (patchSite_injective hq R).eq_iff, localStar, stepCoord]
  split_ifs <;> rfl

def localField (v : Fin 3 → Fin 7) (μ : Fin 3) : SuTwo :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then charged (trialAmplitude i) else 0

theorem trialField_patch {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) :
    trialField hq R (patchSite hq R v,μ) = localField v μ := by
  rw [trialField_apply]
  simp only [trialBond, Prod.mk.injEq, (patchSite_injective hq R).eq_iff, localField]

theorem charged_zero : charged 0 = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]

theorem charged_neg (z : ℂ) : -charged z = charged (-z) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]

def isCurved (i : Fin 19) : Bool := decide (i = 4 ∨ i = 9 ∨ i = 11 ∨ i = 12)

theorem pattern_room (i : Fin 19) (μ : Fin 3) : ((trialPlaqPattern i).1 μ).val < 5 := by
  fin_cases i <;> fin_cases μ <;> decide

theorem pattern_base_flat (i : Fin 19) :
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1 ∧
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2 := by
  revert i
  unfold localStar
  decide

theorem pattern_shift_links (i : Fin 19) :
    (localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2 ↔ isCurved i = true) ∧
    ¬ localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1 := by
  revert i
  unfold localStar
  decide

theorem trial_base_links {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.1) = 1 ∧
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.2) = 1 := by
  have hm := pattern_room i (trialPlaqPattern i).2.1.1
  have hn := pattern_room i (trialPlaqPattern i).2.1.2
  change rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.1) = 1 ∧
    rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.2) = 1
  rw [rightStar_patch hq R t _ _ (by omega), rightStar_patch hq R t _ _ (by omega)]
  simp only [(pattern_base_flat i).1,(pattern_base_flat i).2,↓reduceIte,and_self]

theorem trial_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    holonomyElem (rightStar hq R t) (trialPlaq hq R i) =
      if isCurved i then uθ t else 1 := by
  have hb := trial_base_links hq R t i
  unfold holonomyElem periodicPlaquetteHolonomy
  dsimp only
  rw [hb.1,hb.2]
  change 1 * rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.1,
        (trialPlaqPattern i).2.1.2) *
      (rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.2,
        (trialPlaqPattern i).2.1.1))⁻¹ * 1⁻¹ = _
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega)]
  have h1 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2).val < 6 := by
    fin_cases i <;> decide
  have h2 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1).val < 6 := by
    fin_cases i <;> decide
  have he1 := rightStar_patch hq R t _ _ h1
  have he2 := rightStar_patch hq R t _ _ h2
  have hp := pattern_shift_links i
  dsimp only [stepCoord] at he1 he2 hp
  rw [he1,he2]
  simp only [hp.1, hp.2, ↓reduceIte, inv_one, mul_one, one_mul]

theorem uhalf_coe : ((uθ (Real.pi/2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I,0;0,-Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uθ,uMat,Complex.ofReal_div,Complex.exp_pi_div_two_mul_I,Complex.exp_neg]

theorem trial_hol_parts {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    reHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = realHol (if isCurved i then 0 else 1) ∧
    imHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = imagHol (if isCurved i then 1 else 0) := by
  have he := trial_holonomy hq R (Real.pi/2) i
  have hinv : ((holonomyElemInv (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem (rightStar hq R (Real.pi/2))
        (trialPlaq hq R i) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  unfold reHolonomy imHolonomy
  rw [hinv,he]
  cases hc : isCurved i <;> simp only [hc, Bool.false_eq_true, ↓reduceIte, uhalf_coe]
  all_goals constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [realHol,imagHol,Matrix.star_apply,Matrix.ofNat_apply,Complex.ext_iff,Complex.div_re,Complex.div_im]

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.frozen_four_form
#print axioms AdalyFormal.Round13.Trial.rightStar_patch
#print axioms AdalyFormal.Round13.Trial.trial_base_links
#print axioms AdalyFormal.Round13.Trial.trial_holonomy
#print axioms AdalyFormal.Round13.Trial.trial_hol_parts

namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

theorem charged_add (z w : ℂ) : charged (z+w) = charged z + charged w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged,add_comm]

def chargedHom : ℂ →+ SuTwo where
  toFun := charged
  map_zero' := charged_zero
  map_add' := charged_add

def localAmplitude (v : Fin 3 → Fin 7) (μ : Fin 3) : ℂ :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then trialAmplitude i else 0

theorem localField_amplitude (v : Fin 3 → Fin 7) (μ : Fin 3) :
    localField v μ = charged (localAmplitude v μ) := by
  unfold localField localAmplitude
  change _ = chargedHom _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [chargedHom,charged_zero]

theorem trial_edge_values {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    trialField hq R ((trialPlaq hq R i).1, μ) = charged (localAmplitude v μ) ∧
    trialField hq R ((trialPlaq hq R i).1, ν) = charged (localAmplitude v ν) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 ν,μ) =
      charged (localAmplitude (stepCoord v ν) μ) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 μ,ν) =
      charged (localAmplitude (stepCoord v μ) ν) := by
  dsimp only [trialPlaq]
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega)]
  simp only [trialField_patch,localField_amplitude,stepCoord,and_self]

theorem trial_atom_values {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    a1LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (-localAmplitude (stepCoord v ν) μ) ∧
    a2LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (-localAmplitude v ν) ∧
    a3LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (localAmplitude v μ) ∧
    a4LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (localAmplitude (stepCoord v μ) ν) := by
  have hb := trial_base_links hq R t i
  have he := trial_edge_values hq R i
  dsimp only [trialPlaq] at hb he
  dsimp only at ⊢
  constructor
  · rw [a1LM_apply]
    unfold AprimeZW
    dsimp only [trialPlaq]
    rw [hb.2, he.2.2.1, AdalyFormal.Balaban.CovariantOperators.RMap_one, LinearMap.id_apply, charged_neg]
    rfl
  constructor
  · rw [a2LM_apply]
    unfold AprimeWX
    dsimp only [trialPlaq]
    rw [he.2.1,charged_neg]
    rfl
  constructor
  · rw [a3LM_apply]
    unfold AprimeXY
    dsimp only [trialPlaq]
    rw [he.1]
    rfl
  · rw [a4LM_apply]
    unfold AprimeYZ
    dsimp only [trialPlaq]
    rw [hb.1,he.2.2.2,AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rfl

def localQuad (i : Fin 19) : ℝ :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (stepCoord v ν) μ) (-localAmplitude v ν)
    (localAmplitude v μ) (localAmplitude (stepCoord v μ) ν)

theorem trial_contrib_quad {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) =
      localQuad i := by
  have h := trial_atom_values hq R (Real.pi/2) i
  have hh := trial_hol_parts hq R i
  exact frozen_four_form _ _ _ _ _ _ _ _ _ hh.1 hh.2 h.1 h.2.1 h.2.2.1 h.2.2.2

def plaqNumerator : Fin 19 → ℝ := ![1,1,1,1,-8,1,1,1,1,-8,1,-16,-8,1,1,1,1,1,1]

def edgePattern (i : Fin 19) : Fin 4 → ((Fin 3 → Fin 7) × Fin 3) :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  ![(v,μ),(stepCoord v μ,ν),(stepCoord v ν,μ),(v,ν)]

/-- Exact incidence table, checked by kernel reduction over finite index types. -/
def edgeIndex : Fin 19 → Fin 4 → Option (Fin 6) :=
  ![![none,some 5,none,none], ![none,none,some 2,none],
    ![none,none,some 4,none], ![none,none,some 2,none],
    ![some 2,none,some 0,none], ![some 2,none,none,none],
    ![none,none,some 3,none], ![none,none,some 4,none],
    ![some 4,none,none,none], ![some 4,none,some 0,none],
    ![none,none,some 5,none], ![some 0,none,some 1,some 5],
    ![some 0,none,some 3,none], ![some 5,none,none,none],
    ![some 3,none,none,none], ![some 3,none,none,none],
    ![none,none,some 1,none], ![some 1,none,none,none], ![some 1,none,none,none]]

theorem edgeIndex_spec : ∀ (i : Fin 19) (k : Fin 4) (j : Fin 6),
    ((edgePattern i k).1 = trialCoord j ∧ (edgePattern i k).2 = trialDir j) ↔
      edgeIndex i k = some j := by decide

theorem localAmplitude_edge (i : Fin 19) (k : Fin 4) :
    localAmplitude (edgePattern i k).1 (edgePattern i k).2 =
      (edgeIndex i k).elim 0 trialAmplitude := by
  unfold localAmplitude
  simp only [edgeIndex_spec]
  cases h : edgeIndex i k <;> simp [h]

theorem localQuad_value (i : Fin 19) : localQuad i = plaqNumerator i / 16 := by
  change quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (edgePattern i 2).1 (edgePattern i 2).2)
    (-localAmplitude (edgePattern i 3).1 (edgePattern i 3).2)
    (localAmplitude (edgePattern i 0).1 (edgePattern i 0).2)
    (localAmplitude (edgePattern i 1).1 (edgePattern i 1).2) = _
  rw [localAmplitude_edge,localAmplitude_edge,localAmplitude_edge,localAmplitude_edge]
  fin_cases i
  · change quadForm 1 0 (-(0)) (-(0)) (0) (-Complex.I/4) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(-Complex.I/4)) (1) (0) = (-16 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(0)) (1) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]

/-- Exact actual frozen all-plaquette value for the periodic six-bond trial. -/
theorem trial_delta_value {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (rightStar hq R (Real.pi/2)) Set.univ (trialField hq R)⟫ = (-25/16 : ℝ) := by
  rw [trial_delta_sum]
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [plaqNumerator,Fin.sum_univ_succ]

/-- The four curved plaquettes have exact total -5/2. -/
theorem trial_curved_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)
      else 0) = (-5/2 : ℝ) := by
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [Fin.sum_univ_succ,isCurved,plaqNumerator,Fin.ext_iff]

/-- The remaining fifteen plaquettes have exact total 15/16. -/
theorem trial_flat_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then 0 else
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)) =
        (15/16 : ℝ) := by
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [Fin.sum_univ_succ,isCurved,plaqNumerator,Fin.ext_iff]

/-- The exact energy is -1/4 on the ORIGINAL vacuum carrier, at every admissible q,R. -/
theorem trial_carrier_energy {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R, vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ) := by
  rw [vacA_rightStar, BaseDataS.inner_Ginv]
  have hd : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Dpi (trialVector hq R)⟫ = (-25/16 : ℝ) := by
    have e := E0_Dpi_inner selAll (geomOf 2 1 (dilTower q R))
      (rightStar hq R (Real.pi/2)) 1 (trialVector hq R)
    refine e.trans ?_
    change ⟪Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R),
      DeltaS selAll (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2))
        (Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R))⟫ = _
    rw [trial_W_eq hq hR hR18]
    exact trial_delta_value hq R
  have ht : (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).T (trialVector hq R) = 0 :=
    trial_T_zero hq hR hR18 _
  have hm : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Mass (trialVector hq R)⟫ = (21/16 : ℝ) := by
    change ⟪trialVector hq R, pE (geomOf 2 1 (dilTower q R))
      (MassFull (geomOf 2 1 (dilTower q R)) 1 (bondSectorOf (geomOf 2 1 (dilTower q R))
        (rightStar hq R (Real.pi/2))) (iE (geomOf 2 1 (dilTower q R)) (trialVector hq R)))⟫ = _
    rw [pE_inner_right]
    exact trial_mass_eq hq hR hR18 _
  rw [hd,ht,hm]
  norm_num

/-- P1, with its exact all-instance quantifiers; no physical estimate is a premise. -/
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0 := by
  intro q R hq hR hR18
  exact ⟨trialVector hq R, by rw [trial_carrier_energy hq hR hR18]; norm_num⟩

theorem cofinal_rightStar_negative_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ w : TwistSpace (2^j) R,
        ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0 := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  refine ⟨2*(R₀+18),by omega,dvd_mul_right _ _,by omega,?_⟩
  exact rightStar_negative_halfpi (by positivity) (dvd_mul_right _ _) (by omega)

end AdalyFormal.Round13.Trial
#print axioms AdalyFormal.Round13.Trial.trial_edge_values
#print axioms AdalyFormal.Round13.Trial.trial_atom_values
#print axioms AdalyFormal.Round13.Trial.localQuad_value
#print axioms AdalyFormal.Round13.Trial.trial_contrib_quad
#print axioms AdalyFormal.Round13.Trial.trial_delta_value
#print axioms AdalyFormal.Round13.Trial.trial_carrier_energy
#print axioms AdalyFormal.Round13.Trial.rightStar_negative_halfpi
#print axioms AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi

#print axioms AdalyFormal.Round13.Trial.Fine
#print axioms AdalyFormal.Round13.Trial.seven_le_side
#print axioms AdalyFormal.Round13.Trial.patchSite
#print axioms AdalyFormal.Round13.Trial.patchSite_injective
#print axioms AdalyFormal.Round13.Trial.castLE_add_one
#print axioms AdalyFormal.Round13.Trial.patchSite_shift
#print axioms AdalyFormal.Round13.Trial.centerCoord
#print axioms AdalyFormal.Round13.Trial.patchSite_center
#print axioms AdalyFormal.Round13.Trial.trialCoord
#print axioms AdalyFormal.Round13.Trial.trialDir
#print axioms AdalyFormal.Round13.Trial.trialBond
#print axioms AdalyFormal.Round13.Trial.trialBond_injective
#print axioms AdalyFormal.Round13.Trial.charged
#print axioms AdalyFormal.Round13.Trial.charged_norm
#print axioms AdalyFormal.Round13.Trial.trialAmplitude
#print axioms AdalyFormal.Round13.Trial.trialField
#print axioms AdalyFormal.Round13.Trial.trialField_apply
#print axioms AdalyFormal.Round13.Trial.trialField_at
#print axioms AdalyFormal.Round13.Trial.trialField_support
#print axioms AdalyFormal.Round13.Trial.trialField_norm
#print axioms AdalyFormal.Round13.Trial.trial_sites
#print axioms AdalyFormal.Round13.Trial.trial_start_near
#print axioms AdalyFormal.Round13.Trial.trial_start_zero
#print axioms AdalyFormal.Round13.Trial.trial_touch
#print axioms AdalyFormal.Round13.Trial.trial_collar
#print axioms AdalyFormal.Round13.Trial.trial_levelZero
#print axioms AdalyFormal.Round13.Trial.trialField_mem
#print axioms AdalyFormal.Round13.Trial.trialVector
#print axioms AdalyFormal.Round13.Trial.trial_near_exterior
#print axioms AdalyFormal.Round13.Trial.trialField_hsupp
#print axioms AdalyFormal.Round13.Trial.trial_higher_rows_zero
#print axioms AdalyFormal.Round13.Trial.trial_mass_upper
#print axioms AdalyFormal.Round13.Trial.trial_mass_eq
#print axioms AdalyFormal.Round13.Trial.trial_T_zero
#print axioms AdalyFormal.Round13.Trial.trial_W_eq
#print axioms AdalyFormal.Round13.Trial.stepCoord
#print axioms AdalyFormal.Round13.Trial.backCoord
#print axioms AdalyFormal.Round13.Trial.patchSite_back
#print axioms AdalyFormal.Round13.Trial.d02
#print axioms AdalyFormal.Round13.Trial.d12
#print axioms AdalyFormal.Round13.Trial.trialPlaqPattern
#print axioms AdalyFormal.Round13.Trial.trialPlaq
#print axioms AdalyFormal.Round13.Trial.trialPlaqPattern_injective
#print axioms AdalyFormal.Round13.Trial.trialPlaq_injective
#print axioms AdalyFormal.Round13.Trial.pattern_front
#print axioms AdalyFormal.Round13.Trial.pattern_back1
#print axioms AdalyFormal.Round13.Trial.pattern_back2
#print axioms AdalyFormal.Round13.Trial.trialCoord_positive
#print axioms AdalyFormal.Round13.Trial.front_mem
#print axioms AdalyFormal.Round13.Trial.back_mem1
#print axioms AdalyFormal.Round13.Trial.back_mem2
#print axioms AdalyFormal.Round13.Trial.trial_plaq_zero_off
#print axioms AdalyFormal.Round13.Trial.trial_delta_sum
#print axioms AdalyFormal.Round13.Trial.quadForm
#print axioms AdalyFormal.Round13.Trial.frozen_four_form
#print axioms AdalyFormal.Round13.Trial.anchorCoord
#print axioms AdalyFormal.Round13.Trial.star_anchor
#print axioms AdalyFormal.Round13.Trial.localStar
#print axioms AdalyFormal.Round13.Trial.rightStar_patch
#print axioms AdalyFormal.Round13.Trial.localField
#print axioms AdalyFormal.Round13.Trial.trialField_patch
#print axioms AdalyFormal.Round13.Trial.charged_zero
#print axioms AdalyFormal.Round13.Trial.charged_neg
#print axioms AdalyFormal.Round13.Trial.isCurved
#print axioms AdalyFormal.Round13.Trial.pattern_room
#print axioms AdalyFormal.Round13.Trial.pattern_base_flat
#print axioms AdalyFormal.Round13.Trial.pattern_shift_links
#print axioms AdalyFormal.Round13.Trial.trial_base_links
#print axioms AdalyFormal.Round13.Trial.trial_holonomy
#print axioms AdalyFormal.Round13.Trial.uhalf_coe
#print axioms AdalyFormal.Round13.Trial.trial_hol_parts
#print axioms AdalyFormal.Round13.Trial.charged_add
#print axioms AdalyFormal.Round13.Trial.chargedHom
#print axioms AdalyFormal.Round13.Trial.localAmplitude
#print axioms AdalyFormal.Round13.Trial.localField_amplitude
#print axioms AdalyFormal.Round13.Trial.trial_edge_values
#print axioms AdalyFormal.Round13.Trial.trial_atom_values
#print axioms AdalyFormal.Round13.Trial.localQuad
#print axioms AdalyFormal.Round13.Trial.trial_contrib_quad
#print axioms AdalyFormal.Round13.Trial.plaqNumerator
#print axioms AdalyFormal.Round13.Trial.edgePattern
#print axioms AdalyFormal.Round13.Trial.edgeIndex
#print axioms AdalyFormal.Round13.Trial.edgeIndex_spec
#print axioms AdalyFormal.Round13.Trial.localAmplitude_edge
#print axioms AdalyFormal.Round13.Trial.localQuad_value
#print axioms AdalyFormal.Round13.Trial.trial_delta_value
#print axioms AdalyFormal.Round13.Trial.trial_curved_energy
#print axioms AdalyFormal.Round13.Trial.trial_flat_energy
#print axioms AdalyFormal.Round13.Trial.trial_carrier_energy
#print axioms AdalyFormal.Round13.Trial.rightStar_negative_halfpi
#print axioms AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi


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
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Kernel.Crossing

/-- Exact P1, supplied by the compiled physical six-bond trial. -/
theorem p1 : P1 := AdalyFormal.Round13.Trial.rightStar_negative_halfpi

/-- Unconditional canonical crossing, strictly before half pi, and a nonzero
actual kernel vector. This does NOT assert a charged line or jet detection. -/
theorem rightStar_crossing_before_halfpi {q R : ℕ} (hq : 0 < q)
    (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    AdalyFormal.D1Literal.PSD
      (vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R))) ∧
    ¬ IsUnit (vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R))) ∧
    ∃ u : TwistSpace q R, u ≠ 0 ∧
      vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R)) u = 0 := by
  obtain ⟨w,hw⟩ := p1 hq hR hR18
  have hs : ∀ t x y, ⟪vacA q R (rightStar hq R) 1 t x,y⟫ =
      ⟪x,vacA q R (rightStar hq R) 1 t y⟫ := by
    intro t x y
    exact (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll
      AdalyFormal.D1Literal.selAll
        (pathP q R (rightStar hq R) (fun _ => 0) 0 1 t)).Ginv_symm
      (AdalyFormal.D1Literal.dataS_laws _ _ _) x y
  have heq : vacEdge q R (rightStar hq R) =
      psdEdge (vacA q R (rightStar hq R) 1) 0 (Real.pi/2) :=
    psdEdge_same_after_negative _ (by positivity) (by linarith [Real.pi_pos]) w hw
  obtain ⟨h0,ht,hpsd,hn,_,_⟩ := psdEdge_singular_without_isolation
    (vacA q R (rightStar hq R) 1) (rightStar_vacA_cont hq hR hR18) hs
    (by positivity : (0:ℝ) < Real.pi/2)
    (rightStar_vacA_pd_zero hq (by omega)) w hw
  rw [← heq] at h0 ht hpsd hn
  exact ⟨h0,ht,hpsd,hn,exists_kernel_of_nonunit _ hn⟩

/-- P1 is no longer a hypothesis. P2 and P3 are still unproved physical inputs. -/
theorem cofinalNoCancellation_of_P2_P3 (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_P1_P2_P3 p1 h2 h3

/-- Joint nested cofinal P2/P3 remainder at one consistently RIGHT star. -/
def CofinalP2P3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    (∀ t : ℝ, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace (2^j) R,
      x ≠ 0 → AdalyFormal.Round12.Kernel.Actual.chargedCoordinate (2^j) R
        (rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫) ∧
    (∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u)

/-- The all-instance P1 supplies the trial at whichever indices P2/P3 select. -/
theorem cofinalPhysical_of_cofinalP2P3 (h : CofinalP2P3) : CofinalPhysicalInputs := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,hp,hd⟩ := hRs R₀
  exact ⟨R,hR0,hR,hR18,p1 (by positivity) hR hR18,hp,hd⟩

theorem cofinalNoCancellation_of_cofinalP2P3 (h : CofinalP2P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_cofinalPhysical (cofinalPhysical_of_cofinalP2P3 h)

#print axioms p1
#print axioms rightStar_crossing_before_halfpi
#print axioms cofinalNoCancellation_of_P2_P3
#print axioms CofinalP2P3
#print axioms cofinalPhysical_of_cofinalP2P3
#print axioms cofinalNoCancellation_of_cofinalP2P3
end AdalyFormal.Round13.Assembly.R1

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

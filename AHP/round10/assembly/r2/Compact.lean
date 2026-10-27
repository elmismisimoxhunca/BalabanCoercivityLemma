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
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

open Classical
noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)

end AdalyFormal.Round5.Guarded.IVTR2


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
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2

open Classical
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
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

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

noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

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

end AdalyFormal.Round9.Guarded.QualitativeR2


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
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0

end AdalyFormal.Round9.Guarded.QualitativeR2Joint


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
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

end AdalyFormal.Round9.Guarded.AnalyticR1

namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
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

open Classical
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

end AdalyFormal.Round9.Guarded.QualitativeR2


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
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
def CofinalAnyProfileCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
      QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)

end AdalyFormal.Round9.Guarded.QualitativeR2Joint

namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
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

end AdalyFormal.Round10.Dictionary


namespace AdalyFormal.Round10.Dictionary.Actual
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
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

open Classical
theorem bulkD_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ε α : ℝ) (u : TwistSpace q R) :
    bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (bulkD q R f ε u) :=
  comm_of_quad _ _ ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
    (dataS_laws selIn selIn _)).1 (bulkD_rot q R α f ε) u

theorem corrDeriv_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (corrDeriv q R f u) :=
  deriv_comm (fun ε : ℝ => bulkD q R f ε) _ (fun ε => bulkD_U1 q R f ε α) 0 u

end AdalyFormal.Round10.Dictionary.Actual


/-!
Finite neutral-source estimate, independent of any operator dictionary.
The tridiagonal source equations and a bound on the block jets imply nonvanishing.
This file does not assert that the frozen operators satisfy those hypotheses.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing

open Finset

/-- Zero-padded left neighbor. -/
def left (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else a (j - 1)

/-- The source multiplier from the neutral tridiagonal reduction. -/
def sourceWeight (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 1 else 0) - 2 * left a j + 2 * a (j + 1)

/-- Half the coupling, in the finite block reduction. -/
def sourcePairing (n : ℕ) (a v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), sourceWeight a j * v j

lemma sum_left_abs (n : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ range (n + 1), |left a j|) = ∑ j ∈ range n, |a j| := by
  rw [sum_range_succ']
  simp [left]

lemma sum_right_abs (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0) :
    (∑ j ∈ range (n + 1), |a (j + 1)|) =
      (∑ j ∈ range (n + 1), |a j|) - |a 0| := by
  have h := sum_range_succ' (fun j => |a j|) (n + 1)
  rw [sum_range_succ, ha, abs_zero, add_zero] at h
  linarith

lemma neighbor_sum_bound (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0) :
    (∑ j ∈ range (n + 1), |left a j|) +
        (∑ j ∈ range (n + 1), |a (j + 1)|) ≤
      2 * (∑ j ∈ range (n + 1), |a j|) - |a 0| := by
  rw [sum_left_abs, sum_right_abs n a ha]
  have h : (∑ j ∈ range n, |a j|) ≤ ∑ j ∈ range (n + 1), |a j| := by
    rw [sum_range_succ]
    exact le_add_of_nonneg_right (abs_nonneg _)
  linarith

/-- An l1 estimate for the exact finite tridiagonal source, with no sign assumptions. -/
theorem source_l1_bound (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) :
    2 * ((∑ j ∈ range (n + 1), |left a j|) +
      (∑ j ∈ range (n + 1), |a (j + 1)|)) ≤ (15 / 19 : ℝ) := by
  let S := ∑ j ∈ range (n + 1), |a j|
  let L := ∑ j ∈ range (n + 1), |left a j|
  let U := ∑ j ∈ range (n + 1), |a (j + 1)|
  have hpoint (j : ℕ) (hj : j ∈ range (n + 1)) :
      6 * |a j| ≤ (if j = 0 then (3 / 2 : ℝ) else 0) + |left a j| + |a (j + 1)| := by
    have e : 6 * a j = (if j = 0 then (3 / 2 : ℝ) else 0) - left a j - a (j + 1) := by
      have := heq j (mem_range.mp hj)
      linarith
    calc
      6 * |a j| = |6 * a j| := by rw [abs_mul]; norm_num
      _ = |(if j = 0 then (3 / 2 : ℝ) else 0) - left a j - a (j + 1)| := congrArg abs e
      _ ≤ |(if j = 0 then (3 / 2 : ℝ) else 0) - left a j| + |a (j + 1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((if j = 0 then (3 / 2 : ℝ) else 0) - left a j) (-a (j + 1))
      _ ≤ |(if j = 0 then (3 / 2 : ℝ) else 0)| + |left a j| + |a (j + 1)| := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (if j = 0 then (3 / 2 : ℝ) else 0) (-left a j)
      _ = _ := by split_ifs <;> norm_num
  have hs := sum_le_sum hpoint
  have htotal : 6 * S ≤ (3 / 2 : ℝ) + L + U := by
    simpa [S, L, U, sum_add_distrib, ← mul_sum] using hs
  have hnb : L + U ≤ 2 * S - |a 0| := neighbor_sum_bound n a ha
  have hroot : (3 / 2 : ℝ) ≤ 6 * |a 0| + |a 1| := by
    have e := heq 0 (by omega)
    simp [left] at e
    calc
      (3 / 2 : ℝ) = |6 * a 0 + a 1| := by rw [e]; norm_num
      _ ≤ |6 * a 0| + |a 1| := abs_add_le _ _
      _ = _ := by rw [abs_mul]; norm_num
  have hfirst : |a 1| ≤ U := by
    exact single_le_sum (fun j _ => abs_nonneg (a (j + 1))) (by simp : 0 ∈ range (n + 1))
  have hu : U = S - |a 0| := sum_right_abs n a ha
  change 2 * (L + U) ≤ (15 / 19 : ℝ)
  linarith

lemma sourcePairing_decompose (n : ℕ) (a v : ℕ → ℝ) :
    sourcePairing n a v = v 0 +
      ∑ j ∈ range (n + 1), (-2 * left a j + 2 * a (j + 1)) * v j := by
  unfold sourcePairing sourceWeight
  simp_rw [show ∀ j : ℕ,
    ((if j = 0 then (1 : ℝ) else 0) - 2 * left a j + 2 * a (j + 1)) * v j =
    (if j = 0 then v 0 else 0) + (-2 * left a j + 2 * a (j + 1)) * v j by
      intro j
      split_ifs with hj <;> simp_all
      all_goals ring]
  simp [sum_add_distrib]

/-- A uniform relative error, using only the finite source equations and jet domination. -/
theorem sourcePairing_error (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) :
    |sourcePairing n a v - v 0| ≤ (15 / 19 : ℝ) * |v 0| := by
  rw [sourcePairing_decompose]
  have hpoint (j : ℕ) (hj : j ∈ range (n + 1)) :
      |(-2 * left a j + 2 * a (j + 1)) * v j| ≤
        (2 * (|left a j| + |a (j + 1)|)) * |v 0| := by
    rw [abs_mul]
    apply mul_le_mul _ (hv j (mem_range.mp hj)) (abs_nonneg _) (by positivity)
    calc
      |-2 * left a j + 2 * a (j + 1)| ≤ |-2 * left a j| + |2 * a (j + 1)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]; norm_num; ring
  have hs := sum_le_sum hpoint
  have hb := mul_le_mul_of_nonneg_right (source_l1_bound n a ha heq) (abs_nonneg (v 0))
  have hh := abs_sum_le_sum_abs
    (fun j : ℕ => (-2 * left a j + 2 * a (j + 1)) * v j) (range (n + 1))
  have hs' : (∑ j ∈ range (n + 1), |(-2 * left a j + 2 * a (j + 1)) * v j|) ≤
      (2 * ((∑ j ∈ range (n + 1), |left a j|) +
        (∑ j ∈ range (n + 1), |a (j + 1)|))) * |v 0| := by
    simpa only [← sum_mul, ← mul_sum, ← sum_add_distrib] using hs
  have h := hh.trans (hs'.trans hb)
  simpa only [add_sub_cancel_left] using h

/-- The cancellation margin is at least 4/19 of the first jet. -/
theorem sourcePairing_lower (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) :
    (4 / 19 : ℝ) * |v 0| ≤ |sourcePairing n a v| := by
  have he := sourcePairing_error n a v ha heq hv
  have ht := abs_add_le (v 0 - sourcePairing n a v) (sourcePairing n a v)
  rw [sub_add_cancel, abs_sub_comm] at ht
  linarith

/-- The finite source's first coefficient is positive, without a limiting calculation. -/
theorem sourceWeight_zero_lower (n : ℕ) (a : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) :
    (4 / 19 : ℝ) ≤ sourceWeight a 0 := by
  let v : ℕ → ℝ := fun j => if j = 0 then 1 else 0
  have hv : ∀ j < n + 1, |v j| ≤ |v 0| := by
    intro j _
    simp only [v, if_pos rfl, abs_one]
    split_ifs <;> norm_num
  have he := sourcePairing_error n a v ha heq hv
  have hp : sourcePairing n a v = sourceWeight a 0 := by
    simp [sourcePairing, v]
  rw [hp] at he
  have ht := (abs_le.mp he).1
  norm_num [v] at ht
  linarith

/-- Nonvanishing of the block coupling; all block-identification premises stay explicit. -/
theorem sourcePairing_ne_zero (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) (hzero : v 0 ≠ 0) :
    sourcePairing n a v ≠ 0 := by
  intro hz
  have h := sourcePairing_error n a v ha heq hv
  rw [hz, zero_sub, abs_neg] at h
  have hp := abs_pos.mpr hzero
  linarith

/-- The same bound gives a fixed sign relative to the first jet. -/
theorem sourcePairing_same_sign (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) (hzero : v 0 ≠ 0) :
    0 < sourcePairing n a v * v 0 := by
  have he := sourcePairing_error n a v ha heq hv
  have hl := (abs_le.mp he).1
  have hu := (abs_le.mp he).2
  rcases lt_or_gt_of_ne hzero with hn | hp
  · rw [abs_of_neg hn] at hl hu
    exact mul_pos_of_neg_of_neg (by linarith) hn
  · rw [abs_of_pos hp] at hl hu
    exact mul_pos (by linarith) hp

/-- Explicit dictionary interface: these are unproved properties of the actual block. -/
def BlockSourceData (coupling : ℝ) : Prop :=
  ∃ (n : ℕ) (a v : ℕ → ℝ) (factor : ℝ),
    a (n + 1) = 0 ∧
    (∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) ∧
    (∀ j < n + 1, |v j| ≤ |v 0|) ∧ v 0 ≠ 0 ∧
    factor ≠ 0 ∧ coupling = factor * sourcePairing n a v

/-- A block identification with the stated jet bounds suffices. It is not supplied here. -/
theorem coupling_ne_zero_of_blockSourceData (coupling : ℝ)
    (h : BlockSourceData coupling) : coupling ≠ 0 := by
  obtain ⟨n, a, v, factor, ha, heq, hv, hzero, hf, hform⟩ := h
  rw [hform]
  exact mul_ne_zero hf (sourcePairing_ne_zero n a v ha heq hv hzero)

#print axioms left
#print axioms sourceWeight
#print axioms sourcePairing
#print axioms sum_left_abs
#print axioms sum_right_abs
#print axioms neighbor_sum_bound
#print axioms source_l1_bound
#print axioms sourcePairing_decompose
#print axioms sourcePairing_error
#print axioms sourcePairing_lower
#print axioms sourceWeight_zero_lower
#print axioms sourcePairing_ne_zero
#print axioms sourcePairing_same_sign
#print axioms BlockSourceData
#print axioms coupling_ne_zero_of_blockSourceData

end AdalyFormal.Round10.Nonvanishing


open Filter
open scoped Topology

namespace AdalyFormal.Round10.Assembly

/-- A nonzero normalized limit forces eventual nonvanishing of the numerator.
No lower bound on the normalization, and no sign, is required. -/
theorem eventually_ne_zero_of_normalized_limit {z s : ℕ → ℝ} {K : ℝ}
    (hK : K ≠ 0) (hlim : Tendsto (fun n => z n / s n) atTop (𝓝 K)) :
    ∀ᶠ n in atTop, z n ≠ 0 := by
  have h : ∀ᶠ n in atTop, z n / s n ≠ 0 :=
    hlim.eventually (eventually_ne_nhds hK)
  filter_upwards [h] with n hn
  intro hz
  apply hn
  simp [hz]

/-- An eventual assertion along an unbounded radius sequence gives a cofinal
assertion in the physical radius. The threshold may depend on every fixed scale. -/
theorem cofinal_of_eventual_subsequence {P : ℕ → Prop} {r : ℕ → ℕ}
    (hr : ∀ n, n ≤ r n) (hP : ∀ᶠ n in atTop, P (r n)) :
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ P R := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  intro R₀
  let n := max R₀ N
  exact ⟨r n, le_trans (le_max_left R₀ N) (hr n), hN n (le_max_right R₀ N)⟩

/-- A useful explicit even-radius progression. -/
theorem even_radius_progression (n : ℕ) :
    n ≤ 2 * (n + 9) ∧ 2 ∣ 2 * (n + 9) ∧ 18 ≤ 2 * (n + 9) := by
  exact ⟨by omega, dvd_mul_right 2 (n + 9), by omega⟩

/-- Nested cofinality does not require a single radius threshold valid for all
scales. This lemma permits any exponent subsequence lying above its index. -/
theorem nested_cofinal_of_eventual {P : ℕ → ℕ → Prop}
    (j : ℕ → ℕ) (r : ℕ → ℕ → ℕ)
    (hj : ∀ n, n ≤ j n) (hr : ∀ n m, m ≤ r n m)
    (hP : ∀ n, ∀ᶠ m in atTop, P (j n) (r n m)) :
    ∀ j₀ : ℕ, ∃ j' : ℕ, j₀ ≤ j' ∧ ∀ R₀ : ℕ,
      ∃ R : ℕ, R₀ ≤ R ∧ P j' R := by
  intro j₀
  exact ⟨j j₀, hj j₀, cofinal_of_eventual_subsequence (hr j₀) (hP j₀)⟩

#print axioms eventually_ne_zero_of_normalized_limit
#print axioms cofinal_of_eventual_subsequence
#print axioms even_radius_progression
#print axioms nested_cofinal_of_eventual

end AdalyFormal.Round10.Assembly


/-!
Finite Dirichlet-chain source response.  This is an exact scalar block theorem,
not an identification of the frozen lattice operators or a crossing theorem.
Unlike a fixed-source estimate, it permits the source site to be selected.
-/
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

/-- Dirichlet fine Laplacian on interior indices 1 through n. -/
def lap (y : ℕ → ℝ) (i : ℕ) : ℝ := 2 * y (i + 1) - y i - y (i + 2)

/-- Energy including the two exterior Dirichlet edges. -/
def energy (n : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), (y (i + 1) - y i) ^ 2

lemma energy_nonneg (n : ℕ) (y : ℕ → ℝ) : 0 ≤ energy n y := by
  exact sum_nonneg fun i _ => sq_nonneg _

/-- Summation by parts, retaining both boundary terms. -/
theorem energy_identity (n : ℕ) (y : ℕ → ℝ) :
    energy n y = (∑ i ∈ range n, y (i + 1) * lap y i) +
      y 0 * (y 0 - y 1) + y (n + 1) * (y (n + 1) - y n) := by
  induction n with
  | zero => simp [energy, lap]; ring
  | succ n ih =>
    unfold energy at ih ⊢
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [lap]
    ring

/-- Zero energy and one zero endpoint force every interior entry to vanish. -/
theorem eq_zero_of_energy_zero (n : ℕ) (y : ℕ → ℝ)
    (hleft : y 0 = 0) (he : energy n y = 0) :
    ∀ k ≤ n + 1, y k = 0 := by
  have hd : ∀ i < n + 1, y (i + 1) = y i := by
    intro i hi
    have hsq : (y (i + 1) - y i) ^ 2 ≤ energy n y :=
      single_le_sum (fun j _ => sq_nonneg (y (j + 1) - y j)) (mem_range.mpr hi)
    have hz : y (i + 1) - y i = 0 := by nlinarith [sq_nonneg (y (i + 1) - y i)]
    linarith
  intro k hk
  induction k with
  | zero => exact hleft
  | succ k ih =>
    rw [hd k (by omega), ih (by omega)]

/-- A nonzero coarse two-site average entails strictly positive fine energy. -/
theorem energy_pos_of_average_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hne : ∃ j < n, b j ≠ 0) : 0 < energy (2*n) y := by
  apply lt_of_le_of_ne (energy_nonneg _ _)
  intro he
  have hz := eq_zero_of_energy_zero (2*n) y hleft he.symm
  obtain ⟨j, hj, hb⟩ := hne
  have h := havg j hj
  rw [hz (2*j+1) (by omega), hz (2*j+2) (by omega)] at h
  exact hb (by linarith)

lemma sum_pair (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ range (2*n), f i) = ∑ j ∈ range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2*n+1)+1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

/-- Stationarity under opposite changes of the two entries of each block. -/
def Stationary (n : ℕ) (y : ℕ → ℝ) : Prop :=
  ∀ j < n, lap y (2*j) = lap y (2*j+1)

/-- The selected even-site source response of the constrained lift. -/
def response (y : ℕ → ℝ) (j : ℕ) : ℝ := lap y (2*j)

/-- The effective source response has exactly half the fine Dirichlet energy. -/
theorem response_energy (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) :
    2 * (∑ j ∈ range n, b j * response y j) = energy (2*n) y := by
  rw [energy_identity, hleft, hright]
  simp only [zero_mul, add_zero]
  rw [sum_pair, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hs := hstat j (mem_range.mp hj)
  have ha := havg j (mem_range.mp hj)
  simp only [response]
  rw [show 2*j+1+1 = 2*j+2 by omega, ← hs]
  rw [← add_mul, ha]
  ring

/-- No nonzero coarse jet vector is annihilated by every even-site source. -/
theorem response_pos (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ j ∈ range n, b j * response y j := by
  have hp := energy_pos_of_average_ne_zero n y b hleft havg hne
  have he := response_energy n y b hleft hright havg hstat
  linarith

/-- A single source site already suffices; no bound between different jets is needed. -/
theorem exists_response_ne_zero (n : ℕ) (y b : ℕ → ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0) :
    ∃ j < n, response y j ≠ 0 := by
  by_contra h
  push Not at h
  have hp := response_pos n y b hleft hright havg hstat hne
  have hz : (∑ j ∈ range n, b j * response y j) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [h j (mem_range.mp hj), mul_zero]
  linarith

/-- Abstract dictionary interface. The actual equality with the source pairing is
separate from the finite-chain theorem, so it cannot silently discharge the dictionary. -/
theorem exists_coupling_ne_zero (n : ℕ) (y b coupling : ℕ → ℝ) (factor : ℝ)
    (hleft : y 0 = 0) (hright : y (2*n+1) = 0)
    (havg : ∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j)
    (hstat : Stationary n y) (hne : ∃ j < n, b j ≠ 0)
    (hfactor : factor ≠ 0)
    (hdict : ∀ j < n, coupling j = factor * response y j) :
    ∃ j < n, coupling j ≠ 0 := by
  obtain ⟨j, hj, hn⟩ := exists_response_ne_zero n y b hleft hright havg hstat hne
  refine ⟨j, hj, ?_⟩
  rw [hdict j hj]
  exact mul_ne_zero hfactor hn

#print axioms lap
#print axioms energy
#print axioms energy_nonneg
#print axioms energy_identity
#print axioms eq_zero_of_energy_zero
#print axioms energy_pos_of_average_ne_zero
#print axioms sum_pair
#print axioms Stationary
#print axioms response
#print axioms response_energy
#print axioms response_pos
#print axioms exists_response_ne_zero
#print axioms exists_coupling_ne_zero

end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

/-- Zero padding of a finite vector to the right. -/
def pad {n : ℕ} (a : Fin n → ℝ) (j : ℕ) : ℝ := if h : j < n then a ⟨j,h⟩ else 0

/-- Left Dirichlet value for block sequences. -/
def prev (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else a (j-1)

/-- The exact finite tridiagonal system, with both boundary values zero. -/
def tri (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun a j := 6*a j + prev (pad a) j + pad a ((j : ℕ)+1)
  map_add' a b := by
    funext j
    simp only [Pi.add_apply, prev, pad]
    split_ifs <;> (try simp_all) <;> ring
  map_smul' c a := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, prev, pad]
    split_ifs <;> (try simp_all) <;> ring

lemma pad_abs_le {n : ℕ} (a : Fin n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ j, |a j| ≤ M) (j : ℕ) : |pad a j| ≤ M := by
  unfold pad
  split_ifs
  · exact h _
  · simpa using hM

/-- Strict diagonal dominance proves injectivity, including all chain lengths. -/
theorem tri_injective (n : ℕ) : Function.Injective (tri n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_cases hn : n = 0
  · subst n
    ext j
    exact Fin.elim0 j
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, _, hk⟩ := (univ : Finset (Fin n)).exists_max_image (fun j => |a j|) univ_nonempty
  have hm : ∀ j, |a j| ≤ |a k| := fun j => hk j (mem_univ _)
  have hl : |prev (pad a) k| ≤ |a k| := by
    unfold prev
    split_ifs
    · simp
    · exact pad_abs_le a _ (abs_nonneg _) hm _
  have hr := pad_abs_le a _ (abs_nonneg (a k)) hm ((k : ℕ)+1)
  have he : 6*a k + prev (pad a) k + pad a ((k : ℕ)+1) = 0 := congrFun ha k
  have he' : 6*a k = -(prev (pad a) k + pad a ((k : ℕ)+1)) := by linarith
  have hb : 6*|a k| ≤ |prev (pad a) k| + |pad a ((k : ℕ)+1)| := by
    calc
      6*|a k| = |6*a k| := by rw [abs_mul]; norm_num
      _ = |prev (pad a) k + pad a ((k : ℕ)+1)| := by rw [he', abs_neg]
      _ ≤ _ := abs_add_le _ _
  have hz : |a k| = 0 := by linarith [abs_nonneg (a k)]
  funext j
  exact abs_eq_zero.mp (le_antisymm (by simpa [hz] using hm j) (abs_nonneg _))

/-- Every exact finite tridiagonal right-hand side has a solution. -/
theorem exists_tri_solution (n : ℕ) (r : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, a n = 0 ∧
      ∀ j < n, 6*a j + prev a j + a (j+1) = r j := by
  obtain ⟨a, ha⟩ := (tri n).surjective_of_injective (tri_injective n) (fun j => r j)
  refine ⟨pad a, by simp [pad], ?_⟩
  intro j hj
  have he := congrFun ha ⟨j,hj⟩
  simpa only [tri, LinearMap.coe_mk, AddHom.coe_mk, pad, dif_pos hj] using he

/-- Fine lift of block averages b and alternating block amplitudes a. -/
def blockLift (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then
    (if k = 0 then 0 else b (k/2-1) - a (k/2-1))
  else b (k/2) + a (k/2)

lemma blockLift_zero (a b : ℕ → ℝ) : blockLift a b 0 = 0 := by simp [blockLift]

lemma blockLift_even (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j) = prev b j - prev a j := by
  by_cases hj : j = 0
  · subst j; simp [blockLift, prev]
  · simp [blockLift, prev, hj, show 2*j ≠ 0 by omega]

lemma blockLift_first (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+1) = b j + a j := by
  simp [blockLift, show (2*j+1)/2 = j by omega]

lemma blockLift_second (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+2) = b j - a j := by
  simp [blockLift]

lemma blockLift_average (a b : ℕ → ℝ) (j : ℕ) :
    blockLift a b (2*j+1) + blockLift a b (2*j+2) = 2*b j := by
  rw [blockLift_first, blockLift_second]
  ring

/-- The explicit finite source-response formula. -/
theorem blockLift_response (a b : ℕ → ℝ) (j : ℕ) :
    response (blockLift a b) j = b j - prev b j + 3*a j + prev a j := by
  unfold response lap
  rw [blockLift_first, blockLift_even, blockLift_second]
  ring

/-- The tridiagonal equation is precisely stationarity of the constrained lift. -/
theorem blockLift_stationary (n : ℕ) (a b : ℕ → ℝ)
    (heq : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1)) :
    Stationary n (blockLift a b) := by
  intro j hj
  have he := heq j hj
  unfold lap
  rw [blockLift_first, blockLift_even, blockLift_second,
    show 2*j+1+2 = 2*(j+1)+1 by omega, blockLift_first]
  linarith

/-- A stationary lift exists for every finite sequence of coarse averages. -/
theorem exists_stationary_lift (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0) :
    ∃ y : ℕ → ℝ, y 0 = 0 ∧ y (2*n+1) = 0 ∧
      (∀ j < n, y (2*j+1) + y (2*j+2) = 2*b j) ∧ Stationary n y := by
  obtain ⟨a, ha, heq⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  refine ⟨blockLift a b, blockLift_zero a b, ?_, ?_, blockLift_stationary n a b heq⟩
  · rw [blockLift_first, hb, ha, add_zero]
  · intro j _; exact blockLift_average a b j

/-- The concrete tridiagonal response is positive definite on coarse block data. -/
theorem tridiagonal_response_pos (n : ℕ) (a b : ℕ → ℝ)
    (ha : a n = 0) (hb : b n = 0)
    (heq : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1))
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ j ∈ range n, b j * (b j - prev b j + 3*a j + prev a j) := by
  have hp := response_pos n (blockLift a b) b (blockLift_zero a b)
    (by rw [blockLift_first, hb, ha, add_zero])
    (fun j _ => blockLift_average a b j) (blockLift_stationary n a b heq) hne
  simpa only [blockLift_response] using hp

#print axioms pad
#print axioms prev
#print axioms tri
#print axioms pad_abs_le
#print axioms tri_injective
#print axioms exists_tri_solution
#print axioms blockLift
#print axioms blockLift_zero
#print axioms blockLift_even
#print axioms blockLift_first
#print axioms blockLift_second
#print axioms blockLift_average
#print axioms blockLift_response
#print axioms blockLift_stationary
#print axioms exists_stationary_lift
#print axioms tridiagonal_response_pos

end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

lemma sum_prev_mul (n : ℕ) (a b : ℕ → ℝ) (hb : b n = 0) :
    (∑ j ∈ range n, prev a j * b j) = ∑ j ∈ range n, a j * b (j+1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [prev, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, zero_mul, add_zero]
    rw [sum_range_succ, hb, mul_zero, add_zero]

lemma sum_next_mul (n : ℕ) (a b : ℕ → ℝ) (ha : a n = 0) :
    (∑ j ∈ range n, a (j+1) * b j) = ∑ j ∈ range n, a j * prev b j := by
  simpa only [mul_comm] using (sum_prev_mul n b a ha).symm

lemma tri_pairing_symm (n : ℕ) (a c : ℕ → ℝ) (ha : a n = 0) (hc : c n = 0) :
    (∑ j ∈ range n, a j * (6*c j + prev c j + c (j+1))) =
      ∑ j ∈ range n, (6*a j + prev a j + a (j+1)) * c j := by
  simp_rw [mul_add, add_mul]
  simp only [sum_add_distrib]
  have h₁ := sum_prev_mul n a c hc
  have h₂ := sum_next_mul n a c ha
  have hm : (∑ j ∈ range n, a j * (6*c j)) = ∑ j ∈ range n, (6*a j)*c j := by
    apply sum_congr rfl
    intro j _
    ring
  rw [h₁, h₂, hm]
  ring

lemma sum_delta (n i : ℕ) (b : ℕ → ℝ) (hi : i < n) :
    (∑ j ∈ range n, (if j = i then (1 : ℝ) else 0) * b j) = b i := by
  simp [hi]

lemma sum_prev_delta (n i : ℕ) (b : ℕ → ℝ) (hi : i < n) :
    (∑ j ∈ range n, (if j+1 = i then (1 : ℝ) else 0) * b j) = prev b i := by
  by_cases hz : i = 0
  · subst i; simp [prev]
  · have he : ∀ j : ℕ, j+1 = i ↔ j = i-1 := by intro j; omega
    simp_rw [he]
    simp [prev, hz, show i-1 < n by omega]

/-- One even-site defect, anywhere in the core; the first site is the old source. -/
noncomputable def sourceRhs (i j : ℕ) : ℝ :=
  (3/2 : ℝ) * (if j = i then 1 else 0) +
  (1/2 : ℝ) * (if j+1 = i then 1 else 0)

/-- Exact finite tridiagonal amplitude for a selected source site. -/
noncomputable def sourceAmplitude (n i : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_tri_solution n (sourceRhs i))

lemma sourceAmplitude_boundary (n i : ℕ) : sourceAmplitude n i n = 0 :=
  (Classical.choose_spec (exists_tri_solution n (sourceRhs i))).1

lemma sourceAmplitude_equation (n i : ℕ) :
    ∀ j < n, 6*sourceAmplitude n i j + prev (sourceAmplitude n i) j +
      sourceAmplitude n i (j+1) = sourceRhs i j :=
  (Classical.choose_spec (exists_tri_solution n (sourceRhs i))).2

/-- The exact source multiplier, with no limiting or floating-point constants. -/
def columnWeight (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  (if j = i then 1 else 0) - (if j+1 = i then 1 else 0) -
    2*prev a j + 2*a (j+1)

/-- Half-coupling to the source at site i. -/
noncomputable def sourceResponse (n i : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, columnWeight (sourceAmplitude n i) i j * b j

lemma columnWeight_first (a : ℕ → ℝ) (j : ℕ) :
    columnWeight a 0 j = (if j = 0 then 1 else 0) - 2*prev a j + 2*a (j+1) := by
  simp [columnWeight]

/-- Reciprocity identifies the source sum with the local Dirichlet response. -/
theorem column_pairing (n i : ℕ) (a c b : ℕ → ℝ) (hi : i < n)
    (ha : a n = 0) (hc : c n = 0) (hb : b n = 0)
    (hsource : ∀ j < n, 6*c j + prev c j + c (j+1) = sourceRhs i j)
    (hlift : ∀ j < n, 6*a j + prev a j + a (j+1) = prev b j - b (j+1)) :
    (∑ j ∈ range n, columnWeight c i j * b j) =
      b i - prev b i + 3*a i + prev a i := by
  have he : (∑ j ∈ range n, c j * (prev b j - b (j+1))) =
      (3/2 : ℝ)*a i + (1/2 : ℝ)*prev a i := by
    calc
      _ = ∑ j ∈ range n, c j * (6*a j + prev a j + a (j+1)) := by
        apply sum_congr rfl
        intro j hj
        rw [hlift j (mem_range.mp hj)]
      _ = ∑ j ∈ range n, (6*c j + prev c j + c (j+1))*a j :=
        tri_pairing_symm n c a hc ha
      _ = ∑ j ∈ range n, sourceRhs i j * a j := by
        apply sum_congr rfl
        intro j hj
        rw [hsource j (mem_range.mp hj)]
      _ = _ := by
        simp only [sourceRhs, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
        rw [sum_delta n i a hi, sum_prev_delta n i a hi]
  have he' : (∑ j ∈ range n, c (j+1)*b j) -
      (∑ j ∈ range n, prev c j*b j) = (3/2 : ℝ)*a i + (1/2 : ℝ)*prev a i := by
    rw [sum_next_mul n c b hc, sum_prev_mul n c b hb]
    simpa only [mul_sub, sum_sub_distrib] using he
  simp only [columnWeight, sub_mul, add_mul, sum_add_distrib, sum_sub_distrib,
    mul_assoc, ← mul_sum]
  rw [sum_delta n i b hi, sum_prev_delta n i b hi]
  linarith

/-- The entire source-response matrix is positive definite for every finite length. -/
theorem sourceResponse_pos (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ i ∈ range n, b i * sourceResponse n i b := by
  obtain ⟨a, ha, heq⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  have hp := tridiagonal_response_pos n a b ha hb heq hne
  have hd : ∀ i < n, sourceResponse n i b = b i - prev b i + 3*a i + prev a i := by
    intro i hi
    exact column_pairing n i a (sourceAmplitude n i) b hi ha
      (sourceAmplitude_boundary n i) hb (sourceAmplitude_equation n i) heq
  convert hp using 1
  apply sum_congr rfl
  intro i hi
  rw [hd i (mem_range.mp hi)]

/-- For every nonzero finite jet vector, at least one single-site source couples.
No jet domination or sign hypothesis occurs. -/
theorem exists_sourceResponse_ne_zero (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    ∃ i < n, sourceResponse n i b ≠ 0 := by
  by_contra h
  push Not at h
  have hp := sourceResponse_pos n b hb hne
  have hz : (∑ i ∈ range n, b i * sourceResponse n i b) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [h i (mem_range.mp hi), mul_zero]
  linarith

/-- The only remaining hypotheses here are the actual block dictionary and a nonzero
jet. The theorem by itself does not provide either for a vacuum crossing vector. -/
theorem exists_actual_coupling_of_source_dictionary (n : ℕ) (b coupling : ℕ → ℝ)
    (factor : ℝ) (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hdict : ∀ i < n, coupling i = factor * sourceResponse n i b) :
    ∃ i < n, coupling i ≠ 0 := by
  obtain ⟨i, hi, hr⟩ := exists_sourceResponse_ne_zero n b hb hne
  refine ⟨i, hi, ?_⟩
  rw [hdict i hi]
  exact mul_ne_zero hf hr

/-- Choice-independent hand-off: the dictionary may supply its own source amplitudes.
Any family satisfying the displayed finite equations separates every nonzero jet vector. -/
theorem source_columns_separate (n : ℕ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j) :
    ∃ i < n, (∑ j ∈ range n, columnWeight (c i) i j * b j) ≠ 0 := by
  obtain ⟨a, ha, he⟩ := exists_tri_solution n (fun j => prev b j - b (j+1))
  have hs := blockLift_stationary n a b he
  obtain ⟨i, hi, hr⟩ := exists_response_ne_zero n (blockLift a b) b
    (blockLift_zero a b) (by rw [blockLift_first, hb, ha, add_zero])
    (fun j _ => blockLift_average a b j) hs hne
  refine ⟨i, hi, ?_⟩
  rw [column_pairing n i a (c i) b hi ha (hc i hi) hb (heq i hi) he]
  simpa only [blockLift_response] using hr

/-- Fully explicit dictionary interface, with no choice-based matrix in its hypotheses. -/
theorem exists_coupling_of_source_columns (n : ℕ) (b coupling : ℕ → ℝ)
    (c : ℕ → ℕ → ℝ) (factor : ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j)
    (hdict : ∀ i < n, coupling i = factor *
      (∑ j ∈ range n, columnWeight (c i) i j * b j)) :
    ∃ i < n, coupling i ≠ 0 := by
  obtain ⟨i, hi, hr⟩ := source_columns_separate n b c hb hne hc heq
  refine ⟨i, hi, ?_⟩
  rw [hdict i hi]
  exact mul_ne_zero hf hr

#print axioms source_columns_separate
#print axioms exists_coupling_of_source_columns
#print axioms sum_prev_mul
#print axioms sum_next_mul
#print axioms tri_pairing_symm
#print axioms sum_delta
#print axioms sum_prev_delta
#print axioms sourceRhs
#print axioms sourceAmplitude
#print axioms sourceAmplitude_boundary
#print axioms sourceAmplitude_equation
#print axioms columnWeight
#print axioms sourceResponse
#print axioms columnWeight_first
#print axioms column_pairing
#print axioms sourceResponse_pos
#print axioms exists_sourceResponse_ne_zero
#print axioms exists_actual_coupling_of_source_dictionary

end AdalyFormal.Round10.Nonvanishing.FreeProfile

/-! Compact concrete glue. No cofinal coupling is asserted without a premise. -/
namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

/-- Symmetry of a derivative, including its totalized value at nonsmooth points.
This does not claim differentiability; round 9 proves that separately. -/
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

/-- The actual round-9 coefficient is symmetric at every instance, with no
regularity premise added to the compact source-to-coupling bridge. -/
theorem corrDeriv_symmetric (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (x y : TwistSpace q R) :
    ⟪corrDeriv q R f x, y⟫ = ⟪x, corrDeriv q R f y⟫ :=
  deriv_symmetric (fun ε => bulkD q R f ε)
    (fun ε => ((dataS selIn selIn (bulkP q R f ε)).Delta2_spec
      (dataS_laws selIn selIn _)).1) 0 x y

/-- Full-kernel geometry for any exterior path. There is no assertion that a
selected character exhausts the kernel unless the last clause is proved. -/
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

/-- A concrete, compiled substitute for the uncompiled r1 glue. It works for
any exterior path, and consumes no unproved soft-regularity assumption. -/
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

/-- Finite-source cancellation is discharged by the shared R1 estimate.
The source identification, jet hypotheses and full kernel still must be supplied. -/
theorem canonicalCoupling_of_dominatedSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R)
    (hline : KernelLine q R V u)
    (hsource : Nonvanishing.BlockSourceData ⟪u, corrDeriv q R f u⟫) :
    CanonicalCoupling q R V (corrDeriv q R f) :=
  canonicalCoupling_of_line V f u hline
    (Nonvanishing.coupling_ne_zero_of_blockSourceData _ hsource)

/-- Missing cofinal hand-off. The body uses the actual carrier and derivative. -/
def CofinalDominatedSource : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ (f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ) (u : TwistSpace (2^j) R),
      KernelLine (2^j) R (uthPath (2^j) R) u ∧
      Nonvanishing.BlockSourceData ⟪u, corrDeriv (2^j) R f u⟫

theorem cofinalAnyProfileCoupling_of_dominatedSource (h : CofinalDominatedSource) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, u, hline, hsource⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, f,
    canonicalCoupling_of_dominatedSource (uthPath _ _) f u hline hsource⟩

/-- Source error implies a signed lower bound. Unlike the charged-line route,
this is applicable simultaneously to every vector of a higher-dimensional kernel. -/
theorem signed_source_lower (n : ℕ) (a v : ℕ → ℝ)
    (ha : a (n+1) = 0)
    (heq : ∀ j < n+1, 6*a j + Nonvanishing.left a j + a (j+1) =
      if j = 0 then (3/2 : ℝ) else 0)
    (hv : ∀ j < n+1, |v j| ≤ |v 0|) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hpos : 0 ≤ σ * v 0) :
    (4/19 : ℝ) * (σ * v 0) ≤ σ * Nonvanishing.sourcePairing n a v := by
  have he := Nonvanishing.sourcePairing_error n a v ha heq hv
  obtain ⟨hl, hu⟩ := abs_le.mp he
  rcases hσ with rfl | rfl
  · have hz : 0 ≤ v 0 := by simpa using hpos
    rw [abs_of_nonneg hz] at hl
    linarith
  · have hz : v 0 ≤ 0 := by linarith
    rw [abs_of_nonpos hz] at hu
    linarith

/-- Whole-kernel source criterion. No spectral simplicity or character exclusion
is required; instead the first jet must have one coercive sign on the whole kernel.
All operator/source and jet hypotheses are explicit, not established here. -/
theorem canonicalCoupling_of_kernelSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (n : ℕ) (a : ℕ → ℝ) (v : TwistSpace q R → ℕ → ℝ)
    (factor δ σ : ℝ) (hf : 0 < factor) (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1)
    (ha : a (n+1) = 0)
    (heq : ∀ j < n+1, 6*a j + Nonvanishing.left a j + a (j+1) =
      if j = 0 then (3/2 : ℝ) else 0)
    (hjet : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ∀ j < n+1, |v u j| ≤ |v u 0|)
    (hfirst : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      δ * ‖u‖^2 ≤ σ * v u 0)
    (hform : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ⟪u, corrDeriv q R f u⟫ = factor * Nonvanishing.sourcePairing n a (v u)) :
    CanonicalCoupling q R V (corrDeriv q R f) := by
  have hbound (u : TwistSpace q R) (hu : vacA q R V 1 (vacEdge q R V) u = 0) :
      (factor * (4/19 : ℝ) * δ) * ‖u‖^2 ≤ σ * ⟪u, corrDeriv q R f u⟫ := by
    have hz : 0 ≤ σ * v u 0 :=
      (mul_nonneg hδ.le (sq_nonneg _)).trans (hfirst u hu)
    have hb := signed_source_lower n a (v u) ha heq (hjet u hu) σ hσ hz
    have h1 := mul_le_mul_of_nonneg_left (hfirst u hu) (by norm_num : (0 : ℝ) ≤ 4/19)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hb) hf.le
    rw [hform u hu]
    nlinarith only [h2]
  refine ⟨factor * (4/19 : ℝ) * δ, by positivity, ?_⟩
  rcases hσ with rfl | rfl
  · exact Or.inl (fun u hu => by simpa using hbound u hu)
  · exact Or.inr (fun u hu => by simpa using hbound u hu)

/-- The R2 source-family theorem removes every first-jet domination hypothesis.
It suffices to identify the actual coupling for a finite family of interior profiles
and prove that at least one component of the actual jet vector is nonzero. -/
theorem exists_profile_coupling_of_sourceFamily {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
      factor * Nonvanishing.FreeProfile.sourceResponse N i b) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i)) := by
  obtain ⟨i, hi, hn⟩ := Nonvanishing.FreeProfile.exists_actual_coupling_of_source_dictionary
    N b (fun i => ⟪u, corrDeriv q R (profiles i) u⟫) factor hb hne hf hdict
  exact ⟨i, hi, canonicalCoupling_of_line V (profiles i) u hline hn⟩

/-- Choice-independent version for a dictionary that supplies source amplitudes
satisfying the finite equations, rather than the chosen sourceResponse operator. -/
theorem exists_profile_coupling_of_sourceColumns {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < N, c i N = 0)
    (heq : ∀ i < N, ∀ j < N, 6*c i j + Nonvanishing.FreeProfile.prev (c i) j +
      c i (j+1) = Nonvanishing.FreeProfile.sourceRhs i j)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ = factor *
      (∑ j ∈ Finset.range N, Nonvanishing.FreeProfile.columnWeight (c i) i j * b j)) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i)) := by
  obtain ⟨i, hi, hn⟩ := Nonvanishing.FreeProfile.exists_coupling_of_source_columns
    N b (fun i => ⟪u, corrDeriv q R (profiles i) u⟫) c factor hb hne hf hc heq hdict
  exact ⟨i, hi, canonicalCoupling_of_line V (profiles i) u hline hn⟩

/-- Exact per-instance unproved hand-off, allowing the source site to vary. -/
def SourceFamilyData (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  ∃ (u : TwistSpace q R), KernelLine q R V u ∧
    ∃ (N : ℕ) (b : ℕ → ℝ)
      (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ),
      b N = 0 ∧ (∃ j < N, b j ≠ 0) ∧ factor ≠ 0 ∧
      (∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
        factor * Nonvanishing.FreeProfile.sourceResponse N i b)

def CofinalSourceFamily : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ SourceFamilyData (2^j) R (uthPath (2^j) R)

theorem cofinalAnyProfileCoupling_of_sourceFamily (h : CofinalSourceFamily) :
    CofinalAnyProfileCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, u, hline, N, b, profiles, factor, hb, hne, hf, hd⟩ := hRs R₀
  obtain ⟨i, -, hi⟩ := exists_profile_coupling_of_sourceFamily (uthPath _ _)
    u hline N b profiles factor hb hne hf hd
  exact ⟨R, hRR, hR, hR18, profiles i, hi⟩

#print axioms exists_profile_coupling_of_sourceColumns
#print axioms exists_profile_coupling_of_sourceFamily
#print axioms SourceFamilyData
#print axioms CofinalSourceFamily
#print axioms cofinalAnyProfileCoupling_of_sourceFamily
#print axioms deriv_symmetric
#print axioms corrDeriv_symmetric
#print axioms KernelLine
#print axioms canonicalCoupling_of_line
#print axioms canonicalCoupling_of_dominatedSource
#print axioms CofinalDominatedSource
#print axioms cofinalAnyProfileCoupling_of_dominatedSource
#print axioms signed_source_lower
#print axioms canonicalCoupling_of_kernelSource
end AdalyFormal.Round10.Assembly.R2

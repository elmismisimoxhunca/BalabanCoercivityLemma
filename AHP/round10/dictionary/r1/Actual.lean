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

theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega

theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega

def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1

noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)

end AdalyFormal.Round4.Guarded.RefuteR1


namespace AdalyFormal.Round5.Guarded.IVTR1
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

noncomputable def twistU (q R : ℕ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  dilU q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t)

end AdalyFormal.Round5.Guarded.IVTR1


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
open AdalyFormal.Round5.Guarded.IVTR1
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

noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

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
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

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

end AdalyFormal.Round9.Guarded.QualitativeR2


/-! Symmetry infrastructure on the actual frozen carriers. No spectral assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
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

section Linear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric quadratic form invariant under an orthogonal map determines a
commuting operator. In particular, the second jet itself need not be linear. -/
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

/-- Differentiation preserves equivariance, including the totalized derivative
at a nondifferentiable point. This does not assert differentiability. -/
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

/-- Every real eigenspace of a symmetry is invariant under a commuting map. -/
theorem real_sector_invariant (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) (c : ℝ) {x : E} (hx : J x = c • x) :
    J (T x) = c • T x := by rw [← h, hx, map_smul]

/-- Opposite charge blocks are orthogonal also for a commuting operator's
bilinear form. Symmetry of the operator is not needed. -/
theorem opposite_charge_cross_zero (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) {x y : E} (hx : J x = x) (hy : J y = -y) :
    ⟪x, T y⟫ = 0 := by
  have hi := J.inner_map_map x (T y)
  rw [hx, ← h, hy, map_neg, inner_neg_right] at hi
  linarith

/-- Full kernels, not only selected eigenvectors, are invariant. -/
theorem kernel_invariant (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (h : ∀ x, T (J x) = J (T x)) {x : E} (hx : T x = 0) : T (J x) = 0 := by
  rw [h, hx, map_zero]

/-- Exact orthogonal splitting for an involutive orthogonal symmetry. It makes
no unsupported claim that one summand of the crossing kernel vanishes. -/
theorem involution_split (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = x) (x : E) :
    ∃ xp xm : E, x = xp + xm ∧ J xp = xp ∧ J xm = -xm ∧ ⟪xp, xm⟫ = 0 := by
  let xp : E := (1 / 2 : ℝ) • (x + J x)
  let xm : E := (1 / 2 : ℝ) • (x - J x)
  have hp : J xp = xp := by simp only [xp, map_smul, map_add, hJ]; rw [add_comm]
  have hm : J xm = -xm := by
    simp only [xm, map_smul, map_sub, hJ]
    rw [← smul_neg, neg_sub]
  refine ⟨xp, xm, ?_, hp, hm, ?_⟩
  · dsimp [xp, xm]; module
  · have hi := J.inner_map_map xp xm
    rw [hp, hm, inner_neg_right] at hi
    linarith

theorem involution_kernel_split (T : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hJ : ∀ x, J (J x) = x) (h : ∀ x, T (J x) = J (T x))
    {x : E} (hx : T x = 0) :
    ∃ xp xm : E, x = xp + xm ∧ J xp = xp ∧ J xm = -xm ∧
      ⟪xp, xm⟫ = 0 ∧ T xp = 0 ∧ T xm = 0 := by
  let xp : E := (1 / 2 : ℝ) • (x + J x)
  let xm : E := (1 / 2 : ℝ) • (x - J x)
  have hp : J xp = xp := by simp only [xp, map_smul, map_add, hJ]; rw [add_comm]
  have hm : J xm = -xm := by
    simp only [xm, map_smul, map_sub, hJ]
    rw [← smul_neg, neg_sub]
  refine ⟨xp, xm, ?_, hp, hm, ?_, ?_, ?_⟩
  · dsimp [xp, xm]; module
  · have hi := J.inner_map_map xp xm
    rw [hp, hm, inner_neg_right] at hi
    linarith
  · simp [xp, h, hx]
  · simp [xm, h, hx]
end Linear

/-! The next theorem is the round-9 all-plaquette covariance proof, copied
verbatim. All definitions in its statement are frozen library definitions. -/
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

section FixedGauge
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (hU : periodicGaugeTransform γ U = U)
include hU

/-- A fixed gauge of the background commutes with the actual localized carrier. -/
theorem localized_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.Ginv (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.Ginv x) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).Ginv x
  rwa [hU] at h

theorem all_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have h := Ginv_all_gauge hell S U a Lam γ x
  rwa [hU] at h

theorem correction_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws
      (adEL γ (geomOf ell k S) x) = adEL γ (geomOf ell k S)
        ((gparams ell k Lu hell S U a Lam).data.Delta2
          (gparams ell k Lu hell S U a Lam).data_laws x) := by
  apply comm_of_quad _ (adEL γ (geomOf ell k S))
    ((gparams ell k Lu hell S U a Lam).data.Delta2_spec
      (gparams ell k Lu hell S U a Lam).data_laws).1
  intro y
  have hB := AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ
  rw [hU] at hB
  rw [((gparams ell k Lu hell S U a Lam).data.Delta2_spec
    (gparams ell k Lu hell S U a Lam).data_laws).2,
    ((gparams ell k Lu hell S U a Lam).data.Delta2_spec
    (gparams ell k Lu hell S U a Lam).data_laws).2, hB.C2, hB.H]
  calc
    _ = 2 * ⟪adEL γ (geomOf ell k S)
        ((gparams ell k Lu hell S U a Lam).data.H ((gparams ell k Lu hell S U a Lam).data.C2 y)),
        adEL γ (geomOf ell k S) (gparams ell k Lu hell S U a Lam).data.J⟫ := by rw [← hB.J]
    _ = _ := by rw [LinearIsometryEquiv.inner_map_map]

theorem H_comm (f : FSp (geomOf ell k S)) :
    (gparams ell k Lu hell S U a Lam).data.H (adFL γ (geomOf ell k S) f) =
      adEL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.H f) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).H f
  rwa [hU] at h

/-- Quadratic equivariance, deliberately NOT a linear-sector assertion. -/
theorem C2_equivariant (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S U a Lam).data.C2 (adEL γ (geomOf ell k S) x) =
      adFL γ (geomOf ell k S) ((gparams ell k Lu hell S U a Lam).data.C2 x) := by
  have h := (AdalyFormal.M1GaugeW4.baseEqv_gparams hell S a Lam U γ).C2 x
  rwa [hU] at h
end FixedGauge

def localCorrection {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ↥(bondSupp (geomOf ell k S)) →L[ℝ] ↥(bondSupp (geomOf ell k S)) :=
  (gparams ell k Lu hell S U a Lam).data.Delta2 (gparams ell k Lu hell S U a Lam).data_laws

/-- Pointwise fixed-gauge families have commuting first-order correction. -/
theorem correction_deriv_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (V : ℝ → LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (hV : ∀ t, periodicGaugeTransform γ (V t) = V t) (t : ℝ)
    (x : ↥(bondSupp (geomOf ell k S))) :
    deriv (fun s : ℝ => localCorrection hell S (V s) a Lam) t (adEL γ (geomOf ell k S) x) =
    adEL γ (geomOf ell k S) (deriv (fun s : ℝ => localCorrection hell S (V s) a Lam) t x) :=
  deriv_comm _ _ (fun s => correction_comm hell S (V s) a Lam γ (hV s)) t x

/-- A canonical q=1 radius cannot match BOTH longitudinal collar and core
lengths of the q-dilated geometry unless q=1. No matrix asymptotic is exactified. -/
theorem no_canonical_radius_dilation {q R R' : ℕ}
    (hc : 2 * R' = 2 * R * q) (hi : 8 * R' + 8 = (8 * R + 8) * q) : q = 1 := by
  have he : R' = R * q := by nlinarith
  rw [he, add_mul] at hi
  have hh : 8 * (R * q) = 8 * R * q := by ring
  rw [hh] at hi
  omega

#print axioms comm_of_quad
#print axioms deriv_comm
#print axioms real_sector_invariant
#print axioms opposite_charge_cross_zero
#print axioms kernel_invariant
#print axioms involution_split
#print axioms involution_kernel_split
#print axioms Ginv_all_gauge
#print axioms localized_comm
#print axioms all_comm
#print axioms correction_comm
#print axioms H_comm
#print axioms C2_equivariant
#print axioms localCorrection
#print axioms correction_deriv_comm
#print axioms no_canonical_radius_dilation
end AdalyFormal.Round10.Dictionary

/-! Requires Core.lean, concatenated to Gauge.lean by assemble.py. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_coe_apply BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- A phase background uses the frozen uθ, not a substitute operator. -/
def phaseCfg {L : PeriodicLatticeExtent} (f : Bond L → ℝ) : LinkCfg L := fun e => uθ (f e)

def diagonalGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L := fun _ => uθ α

/-- Verbatim matrix calculation from round 9. -/
theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem phaseCfg_fixed {L : PeriodicLatticeExtent} (f : Bond L → ℝ) (α : ℝ) :
    periodicGaugeTransform (diagonalGauge α) (phaseCfg f) = phaseCfg f := by
  funext e
  change uθ α * uθ (f e) * (uθ α)⁻¹ = uθ (f e)
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

section Diagonal
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (f : Bond (scaleUp ell k Lu) → ℝ) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (α : ℝ)

/-- No invertibility, admissibility, radius, or scale hypotheses. -/
theorem phase_all_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      ((dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv x) :=
  all_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x

theorem phase_localized_comm (x : ↥(bondSupp (geomOf ell k S))) :
    (gparams ell k Lu hell S (phaseCfg f) a Lam).data.Ginv
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      ((gparams ell k Lu hell S (phaseCfg f) a Lam).data.Ginv x) :=
  localized_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x

theorem phase_correction_comm (x : ↥(bondSupp (geomOf ell k S))) :
    localCorrection hell S (phaseCfg f) a Lam (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S) (localCorrection hell S (phaseCfg f) a Lam x) :=
  correction_comm hell S (phaseCfg f) a Lam (diagonalGauge α) (phaseCfg_fixed f α) x
end Diagonal

theorem phase_deriv_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (f : ℝ → Bond (scaleUp ell k Lu) → ℝ) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (α t : ℝ) (x : ↥(bondSupp (geomOf ell k S))) :
    deriv (fun s : ℝ => localCorrection hell S (phaseCfg (f s)) a Lam) t
      (adEL (diagonalGauge α) (geomOf ell k S) x) =
    adEL (diagonalGauge α) (geomOf ell k S)
      (deriv (fun s : ℝ => localCorrection hell S (phaseCfg (f s)) a Lam) t x) :=
  correction_deriv_comm hell S (fun s => phaseCfg (f s)) a Lam (diagonalGauge α)
    (fun s => phaseCfg_fixed (f s) α) t x

/-- The adjoint half turn fixes the diagonal and negates the off-diagonal
entries. This is the neutral/charged involution of the real carrier. -/
theorem half_rotation_matrix : (uθ (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I, 0; 0, -Complex.I] := by
  change uMat (Real.pi / 2) = _
  simp only [uMat, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [show -((Real.pi : ℂ) / 2 * Complex.I) = -Real.pi / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

theorem half_RMap_twice (X : SuTwo) : RMap (uθ (Real.pi / 2)) (RMap (uθ (Real.pi / 2)) X) = X := by
  apply Subtype.ext
  rw [RMap_coe_apply, RMap_coe_apply, half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

theorem half_carrier_twice {L : PeriodicLatticeExtent} (G : TowerGeom L) (x : ↥(bondSupp G)) :
    adEL (diagonalGauge (Real.pi / 2)) G (adEL (diagonalGauge (Real.pi / 2)) G x) = x := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  exact half_RMap_twice ((x : BondFnL2 L) e)

theorem carrier_neutral_charged_split {L : PeriodicLatticeExtent} (G : TowerGeom L)
    (x : ↥(bondSupp G)) :
    ∃ xp xm : ↥(bondSupp G), x = xp + xm ∧
      adEL (diagonalGauge (Real.pi / 2)) G xp = xp ∧
      adEL (diagonalGauge (Real.pi / 2)) G xm = -xm ∧ ⟪xp, xm⟫ = 0 :=
  involution_split _ (half_carrier_twice G) x

theorem phase_kernel_neutral_charged_split {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (f : Bond (scaleUp ell k Lu) → ℝ)
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (geomOf ell k S)))
    (hx : (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv x = 0) :
    ∃ xp xm : ↥(bondSupp (geomOf ell k S)), x = xp + xm ∧
      adEL (diagonalGauge (Real.pi / 2)) (geomOf ell k S) xp = xp ∧
      adEL (diagonalGauge (Real.pi / 2)) (geomOf ell k S) xm = -xm ∧ ⟪xp, xm⟫ = 0 ∧
      (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv xp = 0 ∧
      (dataS selAll selAll (gparams ell k Lu hell S (phaseCfg f) a Lam)).Ginv xm = 0 :=
  involution_kernel_split _ _ (half_carrier_twice _) (phase_all_comm hell S f a Lam _) hx

#print axioms phaseCfg
#print axioms diagonalGauge
#print axioms uθ_comm
#print axioms phaseCfg_fixed
#print axioms phase_all_comm
#print axioms phase_localized_comm
#print axioms phase_correction_comm
#print axioms phase_deriv_comm
#print axioms half_rotation_matrix
#print axioms half_RMap_twice
#print axioms half_carrier_twice
#print axioms carrier_neutral_charged_split
#print axioms phase_kernel_neutral_charged_split
end AdalyFormal.Round10.Dictionary


/-! Exact translation covariance of the frozen local differential operators.
The nonlinear blocking and gauge-fixing projection are not covered here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Translation
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.StatementLaneR6
open AdalyFormal.GaugeCov (adjoint_eqv ringInverse_intertwine)
variable {L : PeriodicLatticeExtent}

/-! These four definitions/lemmas are verbatim from round 6. -/
def siteTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    PeriodicLatticeSite L ≃ PeriodicLatticeSite L := Equiv.addRight a

def bondTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    Bond L ≃ Bond L := Equiv.prodCongr (siteTranslation a) (Equiv.refl _)

theorem translation_shift {L : PeriodicLatticeExtent}
    (a x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift (x + a) μ = periodicLatticeShift x μ + a := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp [periodicLatticeShift, add_assoc, add_comm]
  · simp [periodicLatticeShift, h]

noncomputable def bondPullback {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    BondFnL2 L ≃ₗᵢ[ℝ] BondFnL2 L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (bondTranslation a).symm

def sitePullback (a : PeriodicLatticeSite L) : SiteL2 L ≃ₗᵢ[ℝ] SiteL2 L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (siteTranslation a).symm

def plaqTranslation (a : PeriodicLatticeSite L) :
    PeriodicLatticePlaquette L ≃ PeriodicLatticePlaquette L :=
  Equiv.prodCongr (siteTranslation a) (Equiv.refl _)

def cfgPullback (a : PeriodicLatticeSite L) (U : LinkCfg L) : LinkCfg L :=
  fun e => U (bondTranslation a e)

@[simp] theorem bondPullback_apply (a : PeriodicLatticeSite L) (v : BondFnL2 L) (e : Bond L) :
    bondPullback a v e = v (e.1 + a, e.2) := rfl

@[simp] theorem sitePullback_apply (a : PeriodicLatticeSite L) (v : SiteL2 L)
    (x : PeriodicLatticeSite L) : sitePullback a v x = v (x + a) := rfl

@[simp] theorem plaqTranslation_apply (a : PeriodicLatticeSite L) (p : PeriodicLatticePlaquette L) :
    plaqTranslation a p = (p.1 + a, p.2) := rfl

/-- Covariance requires no hypothesis on U; the background is pulled back too. -/
theorem grad_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (f : SiteL2 L) :
    gradL2 (cfgPullback a U) (sitePullback a f) = bondPullback a (gradL2 U f) := by
  apply PiLp.ext
  rintro ⟨x, μ⟩
  simp only [gradL2_apply, bondPullback_apply]
  simp [gradValueCovariant, cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem div_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x : BondFnL2 L) :
    gradAdj (cfgPullback a U) (bondPullback a x) = sitePullback a (gradAdj U x) :=
  adjoint_eqv (sitePullback a) (bondPullback a) _ _ (grad_translate a U) x

theorem lap_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (f : SiteL2 L) :
    lapFull (cfgPullback a U) (sitePullback a f) = sitePullback a (lapFull U f) := by
  change gradAdj _ (gradL2 _ (sitePullback a f)) = sitePullback a (gradAdj U (gradL2 U f))
  rw [grad_translate, div_translate]

theorem siteMask_translate (a : PeriodicLatticeSite L) (S : Set (PeriodicLatticeSite L))
    (hS : ∀ x, x + a ∈ S ↔ x ∈ S) (f : SiteL2 L) :
    siteMask S (sitePullback a f) = sitePullback a (siteMask S f) := by
  classical
  apply PiLp.ext
  intro x
  simp only [siteMask_apply, sitePullback_apply, hS]

theorem curl_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    curlValueCovariant (cfgPullback a U) (WithLp.ofLp (bondPullback a x)) p =
      curlValueCovariant U (WithLp.ofLp x) (plaqTranslation a p) := by
  simp [curlValueCovariant, cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem holonomy_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (p : PeriodicLatticePlaquette L) :
    periodicPlaquetteHolonomy (cfgPullback a U) p = periodicPlaquetteHolonomy U (plaqTranslation a p) := by
  simp [periodicPlaquetteHolonomy, cfgPullback, bondTranslation, siteTranslation, translation_shift]

/-- The complete frozen plaquette bilinear form, including the curvature terms. -/
theorem bilPlaq_translate (a : PeriodicLatticeSite L) (U : LinkCfg L) (x y : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    bilPlaq (cfgPullback a U) p (WithLp.ofLp (bondPullback a x)) (WithLp.ofLp (bondPullback a y)) =
      bilPlaq U (plaqTranslation a p) (WithLp.ofLp x) (WithLp.ofLp y) := by
  rw [bilPlaq_atoms, bilPlaq_atoms]
  simp only [b1LM, b2LM, b3LM, b4LM, LinearMap.comp_apply, smulILM_apply,
    curlMatLM_apply, curl_translate]
  simp [a1LM, a2LM, a3LM, a4LM, bondMatRLM_apply, bondMatLM_apply,
    reHolonomy, imHolonomy, holonomyElemInv, holonomyElem, periodicPlaquetteHolonomy,
    cfgPullback, bondTranslation, siteTranslation, translation_shift]

theorem raw_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    deltaPrimeBilRawLoc (cfgPullback a U) P (WithLp.ofLp (bondPullback a x))
      (WithLp.ofLp (bondPullback a y)) = deltaPrimeBilRawLoc U P (WithLp.ofLp x) (WithLp.ofLp y) := by
  classical
  rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
  simp_rw [bilPlaq_translate]
  calc
    _ = ∑ p, (if plaqTranslation a p ∈ P then
      bilPlaq U (plaqTranslation a p) (WithLp.ofLp x) (WithLp.ofLp y) else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hP]
    _ = _ := Equiv.sum_comp (plaqTranslation a)
      (fun p => if p ∈ P then bilPlaq U p (WithLp.ofLp x) (WithLp.ofLp y) else 0)

theorem normalized_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    deltaPrimeBilL2NormLoc (cfgPullback a U) P (bondPullback a x) (bondPullback a y) =
      deltaPrimeBilL2NormLoc U P x y := by
  change deltaPrimeBilNormLoc (cfgPullback a U) P (WithLp.ofLp (bondPullback a x))
    (WithLp.ofLp (bondPullback a y)) = deltaPrimeBilNormLoc U P (WithLp.ofLp x) (WithLp.ofLp y)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [raw_translate a U P hP, raw_translate a U P hP]

theorem curl_form_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (x y : BondFnL2 L) :
    ⟪plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (cfgPullback a U) (bondPullback a x)),
      plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (cfgPullback a U) (bondPullback a y))⟫ =
    ⟪plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U x),
      plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U y)⟫ := by
  classical
  simp only [PiLp.inner_apply, plaqMask_apply, AdalyFormal.GaugeCov.curlL2_apply, curl_translate]
  calc
    _ = ∑ p, ⟪(if plaqTranslation a p ∈ P then
      curlValueCovariant U (WithLp.ofLp x) (plaqTranslation a p) else 0),
      (if plaqTranslation a p ∈ P then
      curlValueCovariant U (WithLp.ofLp y) (plaqTranslation a p) else 0)⟫ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hP]
    _ = _ := Equiv.sum_comp (plaqTranslation a)
      (fun p => ⟪(if p ∈ P then curlValueCovariant U (WithLp.ofLp x) p else 0),
        (if p ∈ P then curlValueCovariant U (WithLp.ofLp y) p else 0)⟫)

/-- True operator covariance of the frozen Hessian; no compression/inverse
interchange. This is NOT yet covariance of the dressed all-plaquette carrier. -/
theorem deltaK_translate (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (P : Set (PeriodicLatticePlaquette L)) (hP : ∀ p, plaqTranslation a p ∈ P ↔ p ∈ P)
    (y : BondFnL2 L) :
    deltaKLocCLM (cfgPullback a U) P (bondPullback a y) = bondPullback a (deltaKLocCLM U P y) := by
  apply AdalyFormal.GaugeCov.op_of_form (bondPullback a).toLinearEquiv.toLinearMap
    (bondPullback a).inner_map_map (bondPullback a).surjective
  intro x z
  change ⟪bondPullback a x, deltaKLocCLM (cfgPullback a U) P (bondPullback a z)⟫ = _
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM, curl_form_translate a U P hP,
    normalized_translate a U P hP]

/-- An invariant background has a commuting all-plaquette Hessian. -/
theorem deltaK_all_comm (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (hU : cfgPullback a U = U) (x : BondFnL2 L) :
    deltaKLocCLM U Set.univ (bondPullback a x) = bondPullback a (deltaKLocCLM U Set.univ x) := by
  have h := deltaK_translate a U Set.univ (fun _ => Iff.rfl) x
  rwa [hU] at h

#print axioms siteTranslation
#print axioms bondTranslation
#print axioms translation_shift
#print axioms bondPullback
#print axioms sitePullback
#print axioms plaqTranslation
#print axioms cfgPullback
#print axioms bondPullback_apply
#print axioms sitePullback_apply
#print axioms plaqTranslation_apply
#print axioms grad_translate
#print axioms div_translate
#print axioms lap_translate
#print axioms siteMask_translate
#print axioms curl_translate
#print axioms holonomy_translate
#print axioms bilPlaq_translate
#print axioms raw_translate
#print axioms normalized_translate
#print axioms curl_form_translate
#print axioms deltaK_translate
#print axioms deltaK_all_comm
end AdalyFormal.Round10.Dictionary.Translation


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
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Round10.Dictionary (Ginv_all_gauge)

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

theorem rot_uthPath (q R : ℕ) (α t : ℝ) :
    periodicGaugeTransform (rotGauge α) (uthPath q R t) = uthPath q R t := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, rotGauge]
  split_ifs
  · exact uθ_conj α t
  · rw [mul_one, mul_inv_cancel]

theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem rot_pathU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform (rotGauge α) (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f ε t := by
  unfold pathU
  rw [rot_maskedU, rot_uthPath]

theorem rot_bulkU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform (rotGauge α) (bulkU q R f ε) = bulkU q R f ε := by
  unfold bulkU
  rw [rot_maskedU, rot_trivial]

theorem vacA_rot (q R : ℕ) (α t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPath q R) 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) x) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) x
  rw [rot_pathU] at h
  exact h

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
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

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
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))

end AdalyFormal.Round9.Guarded.AnalyticR1

namespace AdalyFormal.Round6.Guarded.ClosedFormR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (PSD)

/-- Translation of the physical fine torus, not a smaller substitute torus. -/
def siteTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    PeriodicLatticeSite L ≃ PeriodicLatticeSite L := Equiv.addRight a

def bondTranslation {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    Bond L ≃ Bond L := Equiv.prodCongr (siteTranslation a) (Equiv.refl _)

theorem siteTranslation_apply {L : PeriodicLatticeExtent}
    (a x : PeriodicLatticeSite L) : siteTranslation a x = x + a := rfl

theorem bondTranslation_apply {L : PeriodicLatticeExtent}
    (a : PeriodicLatticeSite L) (e : Bond L) :
    bondTranslation a e = (e.1 + a, e.2) := rfl

/-- The site permutation commutes with every fine forward shift. -/
theorem translation_shift {L : PeriodicLatticeExtent}
    (a x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeShift (x + a) μ = periodicLatticeShift x μ + a := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp [periodicLatticeShift, add_assoc, add_comm]
  · simp [periodicLatticeShift, h]

/-- Every level of this tower is invariant under longitudinally zero shifts. -/
theorem translation_tower {q R : ℕ}
    (a x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0) (j : ℕ) :
    x + a ∈ (dilTower q R).Om j ↔ x ∈ (dilTower q R).Om j := by
  by_cases h0 : j = 0
  · simp [dilTower, h0, ha]
  · by_cases h1 : j = 1 <;> simp [dilTower, h0, h1, ha]

theorem translation_bondsOm0 {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0)
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    bondTranslation a e ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) ↔
      e ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  change ((e.1 + a) ∈ (dilTower q R).Om 0 ∨
      periodicLatticeShift (e.1 + a) e.2 ∈ (dilTower q R).Om 0) ↔ _
  rw [translation_shift, translation_tower a _ ha, translation_tower a _ ha]
  rfl

theorem translation_Zb {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0)
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    bondTranslation a e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) ↔
      e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := by
  change ((e.1 + a) ∉ (dilTower q R).Om 0 ∧
      periodicLatticeShift (e.1 + a) e.2 ∉ (dilTower q R).Om 0) ↔ _
  rw [translation_shift, translation_tower a _ ha, translation_tower a _ ha]
  rfl

/-- Pullback by translation on the full physical bond Hilbert space. -/
noncomputable def bondPullback {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L) :
    BondFnL2 L ≃ₗᵢ[ℝ] BondFnL2 L :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ SuTwo (bondTranslation a).symm

theorem bondPullback_apply {L : PeriodicLatticeExtent} (a : PeriodicLatticeSite L)
    (v : BondFnL2 L) (e : Bond L) : bondPullback a v e = v (bondTranslation a e) := rfl

/-- The support restriction is the pin's touching-bond support. -/
theorem bondPullback_mem {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    bondPullback a v ∈ bondSupp (geomOf 2 1 (dilTower q R)) := by
  intro e he
  rw [bondPullback_apply]
  exact v.property _ (fun h => he ((translation_bondsOm0 a ha e).mp h))

noncomputable def carrierTranslationIsometry {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗᵢ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))) where
  toFun v := ⟨bondPullback a v, bondPullback_mem a ha v⟩
  map_add' v w := by apply Subtype.ext; exact (bondPullback a).map_add _ _
  map_smul' c v := by apply Subtype.ext; exact (bondPullback a).map_smul c v
  norm_map' v := (bondPullback a).norm_map v

/-- A genuine orthogonal automorphism of the complete carrier, with no sector
compression and no assertion of operator equivariance built into its type. -/
noncomputable def carrierTranslation {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) ≃ₗᵢ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  LinearIsometryEquiv.ofSurjective (carrierTranslationIsometry a ha)
    ((LinearMap.injective_iff_surjective
      (f := (carrierTranslationIsometry a ha).toLinearMap)).mp
      (carrierTranslationIsometry a ha).injective)

theorem carrierTranslation_apply {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    (carrierTranslation a ha v : BondFnL2 _) e = (v : BondFnL2 _) (bondTranslation a e) := rfl

/-- The two fine-site generator; the stride is NOT 2q. -/
def twoSite (q R : ℕ) (μ : Fin 3) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun ν => if ν = μ then 2 else 0

theorem twoSite_zero (q R : ℕ) (μ : Fin 3) (hμ : μ ≠ 0) :
    twoSite q R μ 0 = 0 := by simp [twoSite, Ne.symm hμ]

theorem translation_parity {n : ℕ} (hn : 2 ∣ n + 1) (x a : Fin (n + 1))
    (ha : a.val % 2 = 0) : (x + a).val % 2 = x.val % 2 := by
  rw [Fin.val_add, Nat.mod_mod_of_dvd _ hn, Nat.add_mod, ha]
  simp

theorem twoSite_parity {q : ℕ} (hq : 0 < q) (R : ℕ) (μ ν : Fin 3) (hν : ν ≠ 0) :
    (twoSite q R μ ν).val % 2 = 0 := by
  have hn : 2 ∣ scaleUp 2 1 (dilLu q R) ν + 1 := by
    rw [dil_fine_size hq, if_neg hν]
    exact ⟨4*q, by omega⟩
  unfold twoSite
  split_ifs
  · change (2 % (scaleUp 2 1 (dilLu q R) ν + 1)) % 2 = 0
    rw [Nat.mod_mod_of_dvd _ hn]
  · rfl

theorem twoSite_dilPattern {q : ℕ} (hq : 0 < q) (R : ℕ)
    (μ : Fin 3) (hμ : μ ≠ 0) (e : Bond (scaleUp 2 1 (dilLu q R))) :
    dilPattern q R (bondTranslation (twoSite q R μ) e) ↔ dilPattern q R e := by
  have hn (ν : Fin 3) (hν : ν ≠ 0) : 2 ∣ scaleUp 2 1 (dilLu q R) ν + 1 := by
    rw [dil_fine_size hq, if_neg hν]
    exact ⟨4*q, by omega⟩
  have hp (ν : Fin 3) (hν : ν ≠ 0) :=
    translation_parity (hn ν hν) (e.1 ν) (twoSite q R μ ν) (twoSite_parity hq R μ ν hν)
  simp only [dilPattern, bondTranslation_apply, Pi.add_apply,
    twoSite_zero q R μ hμ, add_zero, hp 1 (by decide), hp 2 (by decide)]

/-- Exact invariance of the curved exterior-twist background, all parameters. -/
theorem twistU_twoSite {q : ℕ} (hq : 0 < q) (R : ℕ) (ε t : ℝ)
    (μ : Fin 3) (hμ : μ ≠ 0) (e : Bond (scaleUp 2 1 (dilLu q R))) :
    twistU q R ε t (bondTranslation (twoSite q R μ) e) = twistU q R ε t e := by
  classical
  simp only [twistU, dilU, AdalyFormal.D1Literal.Uth,
    translation_Zb _ (twoSite_zero q R μ hμ), twoSite_dilPattern hq R μ hμ]

/-- The actual four-link plaquette word is invariant too. This is not yet an
identity for the dressed Hessian or the nonlinear constrained second jet. -/
theorem twist_holonomy_twoSite {q : ℕ} (hq : 0 < q) (R : ℕ) (ε t : ℝ)
    (μ : Fin 3) (hμ : μ ≠ 0) (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R))) :
    periodicPlaquetteHolonomy (twistU q R ε t) (p.1 + twoSite q R μ, p.2) =
      periodicPlaquetteHolonomy (twistU q R ε t) p := by
  unfold periodicPlaquetteHolonomy
  simp only [translation_shift]
  have he (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ν : Fin 3) :
      twistU q R ε t (x + twoSite q R μ, ν) = twistU q R ε t (x, ν) :=
    twistU_twoSite hq R ε t μ hμ (x, ν)
  simp only [he]

#print axioms siteTranslation
#print axioms bondTranslation
#print axioms siteTranslation_apply
#print axioms bondTranslation_apply
#print axioms translation_shift
#print axioms translation_tower
#print axioms translation_bondsOm0
#print axioms translation_Zb
#print axioms bondPullback
#print axioms bondPullback_apply
#print axioms bondPullback_mem
#print axioms carrierTranslationIsometry
#print axioms carrierTranslation
#print axioms carrierTranslation_apply
#print axioms twoSite
#print axioms twoSite_zero
#print axioms translation_parity
#print axioms twoSite_parity
#print axioms twoSite_dilPattern
#print axioms twistU_twoSite
#print axioms twist_holonomy_twoSite

/-- Orthogonality uses the actual carrier inner product. -/
theorem carrierTranslation_inner {q R : ℕ}
    (a : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0)
    (v w : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪carrierTranslation a ha v, carrierTranslation a ha w⟫ = ⟪v, w⟫ :=
  (carrierTranslation a ha).inner_map_map v w

/-- The full carrier translations compose without a discarded complement. -/
theorem carrierTranslation_add {q R : ℕ}
    (a b : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0) (hb : b 0 = 0)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    carrierTranslation (a + b) (by simp [ha, hb]) v =
      carrierTranslation a ha (carrierTranslation b hb v) := by
  apply Subtype.ext
  apply PiLp.ext
  intro e
  simp only [carrierTranslation_apply, bondTranslation_apply, add_assoc]

/-- In particular, the two transverse generators commute on bondSupp. -/
theorem carrierTranslation_commute {q R : ℕ}
    (a b : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (ha : a 0 = 0) (hb : b 0 = 0)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    carrierTranslation a ha (carrierTranslation b hb v) =
      carrierTranslation b hb (carrierTranslation a ha v) := by
  rw [← carrierTranslation_add, ← carrierTranslation_add]
  simp only [add_comm a b]

#print axioms carrierTranslation_inner
#print axioms carrierTranslation_add
#print axioms carrierTranslation_commute

open scoped Fin.NatCast in
/-- The physical two-site generator has the expected 4q-period. -/
theorem twoSite_period {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) (hμ : μ ≠ 0) :
    (4*q) • twoSite q R μ = 0 := by
  funext ν
  simp only [Pi.smul_apply, Pi.zero_apply, twoSite]
  by_cases hν : ν = μ
  · subst ν
    rw [if_pos rfl]
    have htwo : (2 : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) = (2 : ℕ) • 1 := by
      rw [nsmul_one]; rfl
    rw [htwo, ← mul_smul, nsmul_one, Fin.natCast_eq_zero,
      dil_fine_size hq, if_neg hμ]
    have he : 4*q*2 = 8*q := by omega
    rw [he]
  · rw [if_neg hν, smul_zero]

/-- The part of the requested exact symmetry dictionary proved in this file:
an orthogonal physical-carrier action, the actual link invariance, and the
actual plaquette-word invariance. NO commutation with twistA or twistD is
asserted, and this theorem does not block-diagonalise those operators. -/
theorem twoSite_exact_symmetry {q : ℕ} (hq : 0 < q) (R : ℕ) (ε t : ℝ)
    (μ : Fin 3) (hμ : μ ≠ 0) :
    ∃ T : ↥(bondSupp (geomOf 2 1 (dilTower q R))) ≃ₗᵢ[ℝ]
        ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      (∀ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
        ∀ e : Bond (scaleUp 2 1 (dilLu q R)),
        (T v : BondFnL2 _) e = (v : BondFnL2 _) (bondTranslation (twoSite q R μ) e)) ∧
      (∀ e : Bond (scaleUp 2 1 (dilLu q R)),
        twistU q R ε t (bondTranslation (twoSite q R μ) e) = twistU q R ε t e) ∧
      (∀ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        periodicPlaquetteHolonomy (twistU q R ε t) (p.1 + twoSite q R μ, p.2) =
          periodicPlaquetteHolonomy (twistU q R ε t) p) := by
  exact ⟨carrierTranslation (twoSite q R μ) (twoSite_zero q R μ hμ),
    carrierTranslation_apply _ _, twistU_twoSite hq R ε t μ hμ,
    twist_holonomy_twoSite hq R ε t μ hμ⟩

#print axioms twoSite_period
#print axioms twoSite_exact_symmetry
end AdalyFormal.Round6.Guarded.ClosedFormR1

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

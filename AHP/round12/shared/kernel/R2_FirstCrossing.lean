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


set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
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

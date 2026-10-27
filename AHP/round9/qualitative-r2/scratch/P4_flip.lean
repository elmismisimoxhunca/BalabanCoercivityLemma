
/-! ## The global gauge flip: the forward and backward twists are equivalent

The frozen gauge-covariance lane (`GaugeCov`, `M1GaugeW4`) proves that the localized data are
covariant under every gauge transformation, and that the plaquette Hessian is covariant for
every plaquette set; so the all-plaquette carrier is covariant as well (`Ginv_all_gauge`).  The
constant gauge transformation by `w = [[0,1],[-1,0]]` conjugates `diag(a, ā)` into `diag(ā, a)`:
it maps the curved twist at curvature `ε` and angle `t` to the curved twist at `-ε` and `-t`.
Hence the backward vacuum twist is unitarily equivalent to the forward one, the canonical
crossings coincide, and the first-order coupling changes sign between the two kernels.  A
coupling of EITHER sign on the forward kernel is therefore a positive coupling on one of the two
kernels, which is what the pre-crossing argument needs. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL adBL adSL adBL_apply iE_adEL pE_adBL adjoint_intertwine
  bondEqv_gauge deltaKLocCLM_gauge)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-! ### The all-plaquette carrier is gauge covariant -/

/-- The all-plaquette carrier at `U^γ`, applied to `Ad_γ x`, is `Ad_γ` of the carrier at `U`. -/
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

/-! ### The flip -/

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

theorem flip_conj_uMat (t : ℝ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat t) :
    ((flipElt * g * flipElt⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat (-t) := by
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem flip_uθ (t : ℝ) :
    flipElt * AdalyFormal.D1Literal.uθ t * flipElt⁻¹ = AdalyFormal.D1Literal.uθ (-t) :=
  Subtype.ext (flip_conj_uMat t _ rfl)

theorem flip_Ug (s : ℝ) : flipElt * Ug s * flipElt⁻¹ = Ug (-s) := by
  apply Subtype.ext
  rw [flip_conj_uMat s (Ug s) (Ug_coe_uMat s), Ug_coe_uMat]

theorem flip_one : flipElt * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * flipElt⁻¹ = 1 := by
  rw [mul_one, mul_inv_cancel]

theorem flip_maskedU (q R : ℕ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform flipGauge (maskedU q R g V) =
      maskedU q R (fun e => -g e) (periodicGaugeTransform flipGauge V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, flipGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, flipGauge]
    exact flip_Ug (g e)

theorem flip_uthPath (q R : ℕ) (t : ℝ) :
    periodicGaugeTransform flipGauge (uthPath q R t) = uthPath q R (-t) := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, flipGauge]
  split_ifs
  · exact flip_uθ t
  · exact flip_one

theorem flip_trivial (L : PeriodicLatticeExtent) :
    periodicGaugeTransform (flipGauge (L := L))
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  exact flip_one

theorem flip_pathU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform flipGauge (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f (-ε) (-t) := by
  unfold pathU
  rw [flip_maskedU, flip_uthPath]
  congr 1
  funext e
  ring

theorem flip_bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform flipGauge (bulkU q R f ε) = bulkU q R f (-ε) := by
  unfold bulkU
  rw [flip_maskedU, flip_trivial]
  congr 1
  funext e
  ring

/-! ### Consequences for the twist -/

/-- The flip maps the carrier at `(ε, t)` to the carrier at `(-ε, -t)`. -/
theorem pathA_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    pathA q R (uthPath q R) f (-ε) 1 (-t) (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (pathA q R (uthPath q R) f ε 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) f ε t) 1 (dilLam q R) flipGauge x
  rw [flip_pathU] at h
  exact h

/-- **The backward vacuum twist is unitarily equivalent to the forward one.** -/
theorem vacA_flip (q R : ℕ) (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPathNeg q R) 1 t (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := pathA_flip q R (fun _ => 0) 0 t x
  rw [neg_zero] at h
  exact h

theorem vacA_flip_psd (q R : ℕ) (t : ℝ) :
    PSD (vacA q R (uthPathNeg q R) 1 t) ↔ PSD (vacA q R (uthPath q R) 1 t) := by
  constructor
  · intro h x
    have h1 := h (adEL flipGauge (geomOf 2 1 (dilTower q R)) x)
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map] at h1
    exact h1
  · intro h y
    obtain ⟨x, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective y
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map]
    exact h x

/-- The canonical crossings of the forward and backward twists coincide. -/
theorem vacEdge_flip (q R : ℕ) : vacEdge q R (uthPathNeg q R) = vacEdge q R (uthPath q R) := by
  have hS : {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPathNeg q R) 1 s)} =
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPath q R) 1 s)} := by
    ext t
    exact and_congr_right (fun _ => forall₂_congr (fun s _ => vacA_flip_psd q R s))
  exact congrArg sSup hS

/-- The flip maps the correction at `ε` to the correction at `-ε` (quadratic forms). -/
theorem bulkD_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f (-ε) (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ =
      ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) flipGauge u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f (-ε)) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [flip_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f (-ε) := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

/-- The derivative of a quadratic form of a differentiable operator family. -/
theorem hasDerivAt_quadForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v : E) :
    HasDerivAt (fun ε => ⟪v, D ε v⟫) ⟪v, De v⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- **The coupling is odd under the flip**: on the image of a vector under the flip the
first-order coefficient has the opposite quadratic form. -/
theorem De_flip {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫ := by
  have h1 := hasDerivAt_quadForm hD u
  have h2 := hasDerivAt_quadForm hD (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)
  have h2' : HasDerivAt (fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫)
      ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
        De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ (-0) := by
    rw [neg_zero]; exact h2
  have h3 := h2'.comp (0 : ℝ) (hasDerivAt_neg' (x := (0 : ℝ)))
  have e : ((fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫) ∘ fun x : ℝ => -x) =
      fun ε => ⟪u, bulkD q R f ε u⟫ := by
    funext ε
    exact bulkD_flip q R f ε u
  rw [e] at h3
  have h4 := h3.unique h1
  rw [mul_neg_one] at h4
  linarith

/-- A negative coupling on the forward canonical kernel is a positive coupling on the backward
one. -/
theorem couplingPos_back {q R : ℕ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hflip : ∀ u, ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫)
    {c : ℝ} (hneg : ∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫) :
    ∀ u', vacA q R (uthPathNeg q R) 1 (vacEdge q R (uthPathNeg q R)) u' = 0 →
      c * ‖u'‖ ^ 2 ≤ ⟪u', De u'⟫ := by
  intro u' hu'
  obtain ⟨u, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective u'
  rw [vacEdge_flip, vacA_flip] at hu'
  have hu : vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 :=
    (map_eq_zero_iff _ (adEL flipGauge (geomOf 2 1 (dilTower q R))).injective).mp hu'
  rw [LinearIsometryEquiv.norm_map, hflip]
  exact hneg u hu

/-! ### The literal target with one kernel -/

/-- **The reduced premise for the literal round-8 family at `(q,R)`, one kernel.**  Soft
regularity of the single-defect interior family at the flat interior, and a first-order
coefficient that is definite, of EITHER sign, on the kernel of the vacuum carrier at the
canonical crossing of the forward twist.  NOT proved here. -/
def TwistSoftCouplingFwd (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalCoupling q R (uthPath q R) De

theorem twistSoftCoupling_of_fwd {q R : ℕ} (h : TwistSoftCouplingFwd q R) :
    TwistSoftCoupling q R := by
  obtain ⟨De, hs, c, hc, hpos | hneg⟩ := h
  · exact ⟨De, hs, Or.inl ⟨c, hc, hpos⟩⟩
  · exact ⟨De, hs, Or.inr ⟨c, hc, couplingPos_back (De_flip hs.2.2) hneg⟩⟩

def CofinalTwistSoftCouplingFwd : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCouplingFwd (2^j) R

theorem cofinalTwistSoftCoupling_of_fwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCoupling_of_fwd hv⟩

/-- **Main reduction of this round (literal target, one kernel, either sign).** -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_cofinalTwistSoftCoupling (cofinalTwistSoftCoupling_of_fwd h)

theorem goalNeg2_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd h)

theorem not_cofinalTwistSoftCouplingFwd_of_goalPos1 (h : GoalPos1) :
    ¬ CofinalTwistSoftCouplingFwd :=
  fun h' => goalNeg2_of_cofinalTwistSoftCouplingFwd h' (goalPos2_iff_goalPos1.mpr h)

/-- **Per instance.**  At every large scale and every large even radius, the reduced premise at
that instance gives a separation of the literal family at every small positive curvature. -/
theorem twistSeparation_eventually_of_fwd :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      TwistSoftCouplingFwd (2^j) R →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation (2^j) R ε := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 h => ?_⟩
  exact twistSeparation_eventually (by positivity) hR2 hR18 (hR₁ R hR hR2 hR18)
    (twistSoftCoupling_of_fwd h)

/-- What the positive reading demands, stated directly: at every large scale and every large
even radius the reduced premise fails, i.e. the interior family is not softly regular or the
first-order coupling is not definite on the canonical forward vacuum kernel. -/
theorem goalPos1_forces_no_softCoupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ TwistSoftCouplingFwd (2^j) R := by
  have h' := not_cofinalTwistSoftCouplingFwd_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  exact ⟨R, hRR, hR2, hR18, not_not.mp hR4⟩

#print axioms Ginv_all_gauge
#print axioms flipMat_mem
#print axioms flipElt
#print axioms flipGauge
#print axioms flip_conj_uMat
#print axioms flip_uθ
#print axioms flip_Ug
#print axioms flip_one
#print axioms flip_maskedU
#print axioms flip_uthPath
#print axioms flip_trivial
#print axioms flip_pathU
#print axioms flip_bulkU
#print axioms pathA_flip
#print axioms vacA_flip
#print axioms vacA_flip_psd
#print axioms vacEdge_flip
#print axioms bulkD_flip
#print axioms hasDerivAt_quadForm
#print axioms De_flip
#print axioms couplingPos_back
#print axioms TwistSoftCouplingFwd
#print axioms twistSoftCoupling_of_fwd
#print axioms CofinalTwistSoftCouplingFwd
#print axioms cofinalTwistSoftCoupling_of_fwd
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd
#print axioms goalNeg2_of_cofinalTwistSoftCouplingFwd
#print axioms not_cofinalTwistSoftCouplingFwd_of_goalPos1
#print axioms twistSeparation_eventually_of_fwd
#print axioms goalPos1_forces_no_softCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2

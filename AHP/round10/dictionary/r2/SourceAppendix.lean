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

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

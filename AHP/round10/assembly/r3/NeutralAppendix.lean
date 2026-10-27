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

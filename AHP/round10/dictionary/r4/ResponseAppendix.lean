
/-! Application to the R3 physical source dictionary. All inverses are the frozen full inverses. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.ColorResponse
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.Color

variable {L : PeriodicLatticeExtent}

theorem halfE_twice (G : TowerGeom L) (u : ↥(bondSupp G)) : halfE G (halfE G u) = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro b
  exact half_twice ((u : BondFnL2 L) b)

def neutralPart (G : TowerGeom L) (u : ↥(bondSupp G)) : ↥(bondSupp G) :=
  (1 / 2 : ℝ) • (u + halfE G u)

def chargedPart (G : TowerGeom L) (u : ↥(bondSupp G)) : ↥(bondSupp G) :=
  (1 / 2 : ℝ) • (u - halfE G u)

theorem color_decomposition (G : TowerGeom L) (u : ↥(bondSupp G)) :
    neutralPart G u + chargedPart G u = u := by unfold neutralPart chargedPart; module

theorem neutralPart_fixed (G : TowerGeom L) (u : ↥(bondSupp G)) :
    halfE G (neutralPart G u) = neutralPart G u := by
  simp only [neutralPart, map_smul, map_add, halfE_twice]
  rw [add_comm]

theorem chargedPart_neg (G : TowerGeom L) (u : ↥(bondSupp G)) :
    halfE G (chargedPart G u) = -chargedPart G u := by
  simp only [chargedPart, map_smul, map_sub, halfE_twice]
  module

theorem color_orthogonal (G : TowerGeom L) (u : ↥(bondSupp G)) :
    ⟪neutralPart G u, chargedPart G u⟫ = 0 := by
  have h := (halfE G).inner_map_map (neutralPart G u) (chargedPart G u)
  rw [neutralPart_fixed, chargedPart_neg, inner_neg_right] at h
  linarith

theorem neutralPart_component (G : TowerGeom L) (u : ↥(bondSupp G)) (b : Bond L) :
    (neutralPart G u : BondFnL2 L) b = neutralCoord ((u : BondFnL2 L) b) • pauliE3 :=
  half_average ((u : BondFnL2 L) b)

theorem neutral_coordinate_flip (X : SuTwo) : neutralCoord (RMap flipElt X) = -neutralCoord X := by
  have h := inner_RMap flipElt pauliE3 X
  rw [flip_axis, inner_neg_left] at h
  unfold neutralCoord
  linarith

theorem neutral_coordinate_rot (α : ℝ) (X : SuTwo) :
    neutralCoord (RMap (AdalyFormal.D1Literal.uθ α) X) = neutralCoord X := by
  have h := inner_RMap (AdalyFormal.D1Literal.uθ α) pauliE3 X
  rw [phase_axis_fixed] at h
  exact h

/-- Scalar neutral coordinates of the full actual coarse jet. -/
def neutralJet (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) (p : BIdx G) : ℝ :=
  neutralCoord (flatJet G a u p)

theorem neutralJet_quad (G : TowerGeom L) (a : ℝ) : IsQuadMap (neutralJet G a) := by
  let M : FSp G →ₗ[ℝ] (BIdx G → ℝ) :=
    { toFun := fun z p => neutralCoord (z p)
      map_add' := by intros; funext p; simp [neutralCoord, inner_add_right]
      map_smul' := by intros; funext p; simp [neutralCoord, inner_smul_right] }
  exact (flatJet_quad G a).map_linear M

theorem neutralJet_half (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) :
    neutralJet G a (halfE G u) = neutralJet G a u := by
  funext p
  unfold neutralJet
  rw [show halfE G u = adEL (constGauge (AdalyFormal.D1Literal.uθ (Real.pi / 2))) G u from rfl,
    flatJet_gauge]
  exact neutral_coordinate_rot (Real.pi / 2) _

theorem neutralJet_chargedPart (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) :
    neutralJet G a (chargedPart G u) = neutralJet G a u := by
  have h := quad_add_of_invariant (neutralJet_quad G a) (halfE G).toLinearEquiv.toLinearMap
    (neutralJet_half G a) (neutralPart_fixed G u) (chargedPart_neg G u)
  have hn : neutralJet G a (neutralPart G u) = 0 := by
    funext p
    simp [neutralJet, flatJet_neutral_zero G a _ (neutralPart_fixed G u), neutralCoord]
  rw [color_decomposition, hn, zero_add] at h
  exact h.symm

/-- Neutral coarse jets (and therefore every physical transverse sum of them)
are unchanged by projecting the input to the charged carrier. -/
theorem vacJet_chargedPart_component (q R : ℕ) (u : TwistSpace q R)
    (p : BIdx (geomOf 2 1 (dilTower q R))) :
    vacJet q R (chargedPart (geomOf 2 1 (dilTower q R)) u) p =
      neutralCoord (vacJet q R u p) • pauliE3 := by
  have h := flatJet_charged_neutral (geomOf 2 1 (dilTower q R)) 1 _ (chargedPart_neg _ u) p
  have he := congrFun (neutralJet_chargedPart (geomOf 2 1 (dilTower q R)) 1 u) p
  change neutralCoord (vacJet q R (chargedPart _ u) p) = neutralCoord (vacJet q R u p) at he
  change vacJet q R (chargedPart _ u) p = neutralCoord (vacJet q R (chargedPart _ u) p) • pauliE3 at h
  rw [he] at h
  exact h

/-- Actual R9 jet, now equivariant under the full constant SU(2) group at the flat point. -/
theorem vacJet_constant (q R : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (u : TwistSpace q R) :
    vacJet q R (adEL (constGauge g) (geomOf 2 1 (dilTower q R)) u) =
      adFL (constGauge g) (geomOf 2 1 (dilTower q R)) (vacJet q R u) :=
  flatJet_gauge _ 1 g u

theorem flatH_constant (q R : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (z : FSp (geomOf 2 1 (dilTower q R))) :
    (flatData q R).H (adFL (constGauge g) (geomOf 2 1 (dilTower q R)) z) =
      adEL (constGauge g) (geomOf 2 1 (dilTower q R)) ((flatData q R).H z) := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (constGauge g)
  rw [const_trivial] at h
  exact h.H z

theorem responseProfile_quad (q R : ℕ) : IsQuadMap (responseProfile q R) := by
  let M : FSp (geomOf 2 1 (dilTower q R)) →ₗ[ℝ]
      (Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :=
    { toFun := fun z b => neutralCoord (iE (geomOf 2 1 (dilTower q R)) ((flatData q R).H z) b)
      map_add' := by intros; funext b; simp [neutralCoord, inner_add_right]
      map_smul' := by intros; funext b; simp [neutralCoord, inner_smul_right] }
  exact (flatJet_quad (geomOf 2 1 (dilTower q R)) 1).map_linear M

theorem responseProfile_rot (q R : ℕ) (α : ℝ) (u : TwistSpace q R) :
    responseProfile q R (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      responseProfile q R u := by
  funext b
  change neutralCoord (iE _ ((flatData q R).H
    (vacJet q R (adEL (constGauge (AdalyFormal.D1Literal.uθ α)) _ u))) b) = _
  rw [vacJet_constant, flatH_constant, iE_adEL]
  exact neutral_coordinate_rot α _

theorem responseProfile_flip (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R (flipE (geomOf 2 1 (dilTower q R)) u) = -responseProfile q R u := by
  funext b
  change neutralCoord (iE _ ((flatData q R).H
    (vacJet q R (adEL (constGauge flipElt) _ u))) b) = _
  rw [vacJet_constant, flatH_constant, iE_adEL]
  exact neutral_coordinate_flip _

theorem vacJet_neutralPart_zero (q R : ℕ) (u : TwistSpace q R) :
    vacJet q R (neutralPart (geomOf 2 1 (dilTower q R)) u) = 0 :=
  flatJet_neutral_zero _ 1 _ (neutralPart_fixed _ u)

theorem responseProfile_neutralPart_zero (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R (neutralPart (geomOf 2 1 (dilTower q R)) u) = 0 := by
  funext b
  simp [responseProfile, vacJet_neutralPart_zero, neutralCoordinate]

/-- All physical free-profile information depends only on the charged projection. -/
theorem responseProfile_chargedPart (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R (chargedPart (geomOf 2 1 (dilTower q R)) u) = responseProfile q R u := by
  have h := quad_add_of_invariant (responseProfile_quad q R)
    (halfE (geomOf 2 1 (dilTower q R))).toLinearEquiv.toLinearMap
    (responseProfile_rot q R (Real.pi / 2)) (neutralPart_fixed _ u) (chargedPart_neg _ u)
  rw [color_decomposition, responseProfile_neutralPart_zero, zero_add] at h
  exact h.symm

theorem curlDetected_chargedPart_iff (q R : ℕ) (u : TwistSpace q R) :
    CurlDetected q R (chargedPart (geomOf 2 1 (dilTower q R)) u) ↔ CurlDetected q R u := by
  unfold CurlDetected
  rw [responseProfile_chargedPart]

theorem profileCoupling_chargedPart (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (chargedPart (geomOf 2 1 (dilTower q R)) u) = profileCoupling q R f u := by
  rw [profileCoupling_curl, profileCoupling_curl, responseProfile_chargedPart]

/-- A single flip eigenspace is invisible to every diagonal source. This is a
necessary obstruction, not a statement about the actual crossing kernel. -/
theorem responseProfile_flip_eigen_zero (q R : ℕ) (u : TwistSpace q R)
    (hu : flipE (geomOf 2 1 (dilTower q R)) u = u ∨
      flipE (geomOf 2 1 (dilTower q R)) u = -u) : responseProfile q R u = 0 :=
  quad_zero_of_anti_fixed (responseProfile_quad q R)
    (flipE (geomOf 2 1 (dilTower q R))).toLinearEquiv.toLinearMap (responseProfile_flip q R) hu

theorem profileCoupling_zero_of_flip_eigen (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R)
    (hu : flipE (geomOf 2 1 (dilTower q R)) u = u ∨
      flipE (geomOf 2 1 (dilTower q R)) u = -u) : profileCoupling q R f u = 0 := by
  rw [profileCoupling_curl, responseProfile_flip_eigen_zero q R u hu]
  simp [PhaseSource.circulation]

/-- Actual mixed-color profile law, with exact normalization and no invertibility premise. -/
theorem responseProfile_mixed (q R : ℕ) (x y : TwistSpace q R)
    (hx : flipE (geomOf 2 1 (dilTower q R)) x = x)
    (hy : flipE (geomOf 2 1 (dilTower q R)) y = -y) (a b : ℝ) :
    responseProfile q R (a • x + b • y) = (a * b) • responseProfile q R (x + y) :=
  quad_mixed_scaling (responseProfile_quad q R)
    (responseProfile_flip_eigen_zero q R x (Or.inl hx))
    (responseProfile_flip_eigen_zero q R y (Or.inr hy)) a b

end AdalyFormal.Round10.Dictionary.ColorResponse

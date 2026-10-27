import DrEquiv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

theorem half_rotation_matrix : (uθ (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I, 0; 0, -Complex.I] := by
  change uMat (Real.pi / 2) = _
  simp only [uMat, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [show -((Real.pi : ℂ) / 2 * Complex.I) = -Real.pi / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]

end AdalyFormal.Round10.Dictionary

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

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

end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round10.Dictionary.Source
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)

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

end AdalyFormal.Round10.Dictionary.Source

/-! Exact global-color selection rules for the frozen flat dressed quadratic jet. -/
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Color
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt flipGauge)
open AdalyFormal.Round10.Dictionary.Source (neutralCoord neutral_of_half_fixed)
open AdalyFormal.D1Literal (uθ)

section Quadratic
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

theorem quad_even {Q : X → Y} (hQ : IsQuadMap Q) (x : X) : Q (-x) = Q x := by
  simpa only [neg_one_smul, neg_one_sq, one_smul] using hQ.smul_sq (-1 : ℝ) x

theorem quad_zero {Q : X → Y} (hQ : IsQuadMap Q) : Q 0 = 0 := by
  simpa using hQ.smul_sq (0 : ℝ) (0 : X)

theorem quad_parallelogram {Q : X → Y} (hQ : IsQuadMap Q) (x y : X) :
    Q (x + y) + Q (x - y) = (2 : ℝ) • Q x + (2 : ℝ) • Q y := by
  obtain ⟨B, hB⟩ := hQ
  simp only [hB, map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  module

theorem quad_add_of_invariant {Q : X → Y} (hQ : IsQuadMap Q) (J : X →ₗ[ℝ] X)
    (hJ : ∀ x, Q (J x) = Q x) {x y : X} (hx : J x = x) (hy : J y = -y) :
    Q (x + y) = Q x + Q y := by
  have he : Q (x - y) = Q (x + y) := by
    have h := hJ (x + y)
    simpa only [map_add, hx, hy, ← sub_eq_add_neg] using h
  have h := quad_parallelogram hQ x y
  rw [he] at h
  have hh : (2 : ℝ) • (Q (x + y) - (Q x + Q y)) = 0 := by
    calc
      _ = (Q (x + y) + Q (x + y)) - ((2 : ℝ) • Q x + (2 : ℝ) • Q y) := by module
      _ = 0 := sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (by norm_num))

theorem quad_zero_of_anti_fixed {Q : X → Y} (hQ : IsQuadMap Q) (J : X →ₗ[ℝ] X)
    (hJ : ∀ x, Q (J x) = -Q x) {x : X} (hx : J x = x ∨ J x = -x) : Q x = 0 := by
  have hh : Q x = -Q x := by
    rcases hx with hx | hx
    · simpa only [hx] using hJ x
    · simpa only [hx, quad_even hQ] using hJ x
  have h2 : (2 : ℝ) • Q x = 0 := by
    rw [two_smul]
    exact (congrArg (fun y => y + Q x) hh).trans (neg_add_cancel (Q x))
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- On two color lines with zero self-jets, the actual jet is purely mixed. -/
theorem quad_mixed_scaling {Q : X → Y} (hQ : IsQuadMap Q) {x y : X}
    (hx : Q x = 0) (hy : Q y = 0) (a b : ℝ) :
    Q (a • x + b • y) = (a * b) • Q (x + y) := by
  obtain ⟨B, hB⟩ := hQ
  rw [hB] at hx hy
  simp only [hB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hx, hy, smul_zero, zero_add, add_zero]
  module
end Quadratic

variable {L : PeriodicLatticeExtent}

def constGauge (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : GaugeFn L := fun _ => g

theorem const_trivial (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    periodicGaugeTransform (constGauge (L := L) g) (fun _ => 1) = fun _ => 1 := by
  funext b
  change g * 1 * g⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

def halfE (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) :=
  adEL (constGauge (uθ (Real.pi / 2))) G

def flipE (G : TowerGeom L) : ↥(bondSupp G) ≃ₗᵢ[ℝ] ↥(bondSupp G) := adEL flipGauge G

def flatJet (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) : FSp G :=
  C2fullOf G (fun _ => 1) (Wop G (fun _ => 1) a (iE G u))

theorem flatJet_quad (G : TowerGeom L) (a : ℝ) : IsQuadMap (flatJet G a) :=
  (C2fullOf_quad G (fun _ => 1)).comp_linear
    (((Wop G (fun _ => 1) a).comp (iE G)).toLinearMap)

theorem flatJet_gauge (G : TowerGeom L) (a : ℝ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (u : ↥(bondSupp G)) :
    flatJet G a (adEL (constGauge g) G u) = adFL (constGauge g) G (flatJet G a u) := by
  have hw := Wop_gauge G (constGauge g) (fun _ => 1) a (iE G u)
  have hc := C2fullOf_gauge G (fun _ => 1) (constGauge g)
    (Wop G (fun _ => 1) a (iE G u))
  rw [const_trivial] at hw hc
  unfold flatJet
  rw [iE_adEL, hw, hc]

theorem flip_matrix (X : SuTwo) :
    ((RMap flipElt X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(X : Matrix (Fin 2) (Fin 2) ℂ) 1 1, -(X : Matrix (Fin 2) (Fin 2) ℂ) 1 0;
      -(X : Matrix (Fin 2) (Fin 2) ℂ) 0 1, (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0] := by
  rw [RMap_coe_apply]
  change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * _ *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem flip_axis : RMap flipElt pauliE3 = -pauliE3 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliE3, AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
    AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal]

theorem half_axis : RMap (uθ (Real.pi / 2)) pauliE3 = pauliE3 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE3, AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_neutral (X : SuTwo) (hX : RMap (uθ (Real.pi / 2)) X = X) :
    RMap flipElt X = -X := by
  rw [neutral_of_half_fixed X hX, map_smul, flip_axis, smul_neg]

theorem two_fixed_zero (X : SuTwo) (hh : RMap (uθ (Real.pi / 2)) X = X)
    (hf : RMap flipElt X = X) : X = 0 := by
  have hn := flip_neutral X hh
  rw [hf] at hn
  have h2 : (2 : ℝ) • X = 0 := by
    rw [two_smul]
    exact (congrArg (fun y => y + X) hn).trans (neg_add_cancel X)
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem halfE_flip_on_fixed (G : TowerGeom L) (u : ↥(bondSupp G)) (hu : halfE G u = u) :
    flipE G u = -u := by
  apply Subtype.ext
  apply PiLp.ext
  intro b
  apply flip_neutral
  exact congrArg (fun v : ↥(bondSupp G) => (v : BondFnL2 L) b) hu

/-- A neutral carrier input has zero FULL quadratic jet, before any source pairing. -/
theorem flatJet_neutral_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = u) : flatJet G a u = 0 := by
  have hh := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hh
  rw [hu] at hh
  have hf := flatJet_gauge G a flipElt u
  change flatJet G a (flipE G u) = _ at hf
  rw [halfE_flip_on_fixed G u hu, quad_even (flatJet_quad G a)] at hf
  apply PiLp.ext
  intro p
  apply two_fixed_zero
  · exact (congrArg (fun v : FSp G => v p) hh).symm
  · exact (congrArg (fun v : FSp G => v p) hf).symm

/-- A charged carrier input has a neutral quadratic jet. -/
theorem flatJet_charged_neutral (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) (p : BIdx G) :
    flatJet G a u p = neutralCoord (flatJet G a u p) • pauliE3 := by
  apply neutral_of_half_fixed
  have hh := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hh
  rw [hu, quad_even (flatJet_quad G a)] at hh
  exact (congrArg (fun v : FSp G => v p) hh).symm

/-- Within the charged carrier, either single real color has zero full jet. -/
theorem flatJet_single_color_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hh : halfE G u = -u) (hf : flipE G u = u ∨ flipE G u = -u) :
    flatJet G a u = 0 := by
  have hhalf := flatJet_gauge G a (uθ (Real.pi / 2)) u
  change flatJet G a (halfE G u) = _ at hhalf
  rw [hh, quad_even (flatJet_quad G a)] at hhalf
  have hflip := flatJet_gauge G a flipElt u
  change flatJet G a (flipE G u) = _ at hflip
  rcases hf with hf | hf
  all_goals
    rw [hf] at hflip
    try rw [quad_even (flatJet_quad G a)] at hflip
    apply PiLp.ext
    intro p
    apply two_fixed_zero
    · exact (congrArg (fun v : FSp G => v p) hhalf).symm
    · exact (congrArg (fun v : FSp G => v p) hflip).symm

end AdalyFormal.Round10.Dictionary.Color
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_even
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_parallelogram
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_add_of_invariant
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_zero_of_anti_fixed
#print axioms AdalyFormal.Round10.Dictionary.Color.quad_mixed_scaling
#print axioms AdalyFormal.Round10.Dictionary.Color.constGauge
#print axioms AdalyFormal.Round10.Dictionary.Color.const_trivial
#print axioms AdalyFormal.Round10.Dictionary.Color.halfE
#print axioms AdalyFormal.Round10.Dictionary.Color.flipE
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_quad
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_gauge
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_matrix
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_axis
#print axioms AdalyFormal.Round10.Dictionary.Color.half_axis
#print axioms AdalyFormal.Round10.Dictionary.Color.flip_neutral
#print axioms AdalyFormal.Round10.Dictionary.Color.two_fixed_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.halfE_flip_on_fixed
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_neutral_zero
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_charged_neutral
#print axioms AdalyFormal.Round10.Dictionary.Color.flatJet_single_color_zero

namespace AdalyFormal.Round10.Dictionary.ColorObstruction
open AdalyFormal.Balaban.CovariantOperators (RMap RMap_coe_apply)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt)
open AdalyFormal.Round10.Dictionary.Color
theorem half_pauliE1 : RMap (AdalyFormal.D1Literal.uθ (Real.pi / 2)) pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE1, pauliE1Val, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem flip_pauliE1 : RMap flipElt pauliE1 = -pauliE1 := by
  apply Subtype.ext
  rw [flip_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliE1, pauliE1Val]


end AdalyFormal.Round10.Dictionary.ColorObstruction

namespace AdalyFormal.Round13.Detection.ColorTrace
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt)
open AdalyFormal.Round10.Dictionary.Color
open AdalyFormal.Round10.Dictionary.ColorObstruction

/-- Arbitrary spatial variation in a single charged color is killed by the actual
flat dressed jet. This includes fields with nonzero traces on many layers. -/
theorem flatJet_zero_of_pointwise_color {L : PeriodicLatticeExtent}
    (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) (f : Bond L → ℝ)
    (hf : ∀ b, (u : BondFnL2 L) b = f b • pauliE1) : flatJet G a u = 0 := by
  have hh : halfE G u = -u := by
    apply Subtype.ext
    apply PiLp.ext
    intro b
    change RMap (AdalyFormal.D1Literal.uθ (Real.pi/2)) ((u : BondFnL2 L) b) =
      -((u : BondFnL2 L) b)
    rw [hf b, map_smul, half_pauliE1, smul_neg]
  have hw : flipE G u = -u := by
    apply Subtype.ext
    apply PiLp.ext
    intro b
    change RMap flipElt ((u : BondFnL2 L) b) = -((u : BondFnL2 L) b)
    rw [hf b, map_smul, flip_pauliE1, smul_neg]
  exact flatJet_single_color_zero G a u hh (Or.inr hw)

/-- A nonzero trace does not repair that obstruction: the field is nonzero but
its full physical flat jet is zero, under the displayed pointwise-color condition.
No claim places such a field in the right-star crossing kernel. -/
theorem nonzero_trace_with_zero_jet {L : PeriodicLatticeExtent}
    (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) (f : Bond L → ℝ)
    (hf : ∀ b, (u : BondFnL2 L) b = f b • pauliE1)
    (b : Bond L) (hb : f b ≠ 0) : u ≠ 0 ∧ flatJet G a u = 0 := by
  refine ⟨?_, flatJet_zero_of_pointwise_color G a u f hf⟩
  intro hu
  have hz : f b • pauliE1 = 0 := by
    rw [← hf b, hu]
    rfl
  have he : pauliE1 = 0 := (smul_eq_zero.mp hz).resolve_left hb
  have hn := hsInner_e1_e1
  rw [he] at hn
  norm_num [hsInner] at hn

#print axioms flatJet_zero_of_pointwise_color
#print axioms nonzero_trace_with_zero_jet
end AdalyFormal.Round13.Detection.ColorTrace

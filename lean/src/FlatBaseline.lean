import PhysicalCovariance

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.G0Close
open HConstruction.Covariance HConstruction.DRepair
open AdalyFormal.Balaban.ConstantA (BaseConstant)

/-- The mass parameter in the requested physical precision is exactly one. -/
def unitConstant : BaseConstant := ⟨1, by norm_num⟩

/-- Flat VALUE precision on the entire 576-real-dimensional original carrier.
This is not the axial restriction, nor its zero extension to the full carrier. -/
def flatBaseline : H →L[ℝ] H := physicalPrecision unitConstant

theorem flatBaseline_density : flatBaseline = (8 : ℝ) • basePrecision 1 := by
  rw [flatBaseline, physicalPrecision_density, (nativeData_identified unitConstant).1]
  rfl

/-- Unconditional full-carrier hpos for the flat baseline in the sparse strategy. -/
theorem flatBaseline_positive (x : H) (hx : x ≠ 0) :
    (0 : ℝ) < inner ℝ x (flatBaseline x) := by
  exact physicalPrecision_strict unitConstant x hx

theorem flatBaseline_selfAdjoint (x y : H) :
    (inner ℝ (flatBaseline x) y : ℝ) = inner ℝ x (flatBaseline y) := by
  rw [flatBaseline_density]
  simp only [smul_apply, real_inner_smul_left, inner_smul_right,
    basePrecision_selfAdjoint]

def flatInverse : H →L[ℝ] H := physicalG0 unitConstant

theorem flatInverse_right (x : H) : flatBaseline (flatInverse x) = x :=
  physicalG0_rightInverse unitConstant x

theorem flatInverse_left (x : H) : flatInverse (flatBaseline x) = x :=
  physicalG0_leftInverse unitConstant x

theorem flatInverse_positive (x : H) (hx : x ≠ 0) :
    (0 : ℝ) < inner ℝ x (flatInverse x) :=
  physicalG0_strict unitConstant x hx

section Compression
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The true Gram matrix for the energy minimization, not V*V. -/
def flatGram (V : F →L[ℝ] H) : F →L[ℝ] F :=
  V.adjoint.comp (flatInverse.comp V)

theorem flatGram_positive (V : F →L[ℝ] H) (hV : Function.Injective V)
    (z : F) (hz : z ≠ 0) : (0 : ℝ) < inner ℝ z (flatGram V z) := by
  have hv : V z ≠ 0 := by
    intro hv
    exact hz (hV (by simpa only [map_zero] using hv))
  simpa only [flatGram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right] using flatInverse_positive (V z) hv

/-- Actual inverse, obtained only after proving strict positivity of the Gram. -/
def flatSchurC (V : F →L[ℝ] H) (hV : Function.Injective V) : F →L[ℝ] F :=
  Classical.choose (positive_inverse (flatGram V) (flatGram_positive V hV))

theorem flatSchurC_right (V : F →L[ℝ] H) (hV : Function.Injective V) (z : F) :
    flatGram V (flatSchurC V hV z) = z :=
  (Classical.choose_spec (positive_inverse (flatGram V) (flatGram_positive V hV))).1 z

theorem flatSchurC_left (V : F →L[ℝ] H) (hV : Function.Injective V) (z : F) :
    flatSchurC V hV (flatGram V z) = z :=
  (Classical.choose_spec (positive_inverse (flatGram V) (flatGram_positive V hV))).2.1 z

def flatLift (V : F →L[ℝ] H) (hV : Function.Injective V) : F →L[ℝ] H :=
  flatInverse.comp (V.comp (flatSchurC V hV))

/-- These are the actual hVK and hAK of CompressedSchur. -/
theorem flatLift_VK (V : F →L[ℝ] H) (hV : Function.Injective V) (z : F) :
    V.adjoint (flatLift V hV z) = z := flatSchurC_right V hV z

theorem flatLift_AK (V : F →L[ℝ] H) (hV : Function.Injective V) (z : F) :
    flatBaseline (flatLift V hV z) = V (flatSchurC V hV z) :=
  flatInverse_right _

end Compression

#print axioms flatBaseline_positive
#print axioms flatBaseline_selfAdjoint
#print axioms flatInverse_right
#print axioms flatInverse_left
#print axioms flatInverse_positive
#print axioms flatGram_positive
#print axioms flatSchurC_right
#print axioms flatSchurC_left
#print axioms flatLift_VK
#print axioms flatLift_AK
end HConstruction.G0Close

import DK3LocalLift

/-!
Objects 1--4 only. ROUTE 5B is the intended remaining variational construction;
it is NOT YET IDENTIFIED with the literal CMP99b (3.156) at k=3.
All gates below are proved on a positive closed interval, with no analytic
assumption on the background left as a theorem parameter.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3
open HConstruction.Predicate
open AdalyFormal.Target.ClayStatement

/-- The genuine source of the current unit background, with eta_unit=1.
This is not the fine source at eta=1/8 or a linear functional chosen for positivity. -/
def J (t : ℝ) : K := genuineSource (V t)

theorem J_exact (t : ℝ) : sourceCoordinates (J t) = HConstruction.Reproduced.Source.Jsource (V t) :=
  genuineSource_exact (V t)

theorem J_zero : J 0 = 0 := by
  unfold J
  rw [V_zero]
  exact genuineSource_trivial

/-- Joint gate for the genuine unit nonlinear map, native Q1, and b0 inverse. -/
theorem object_radius_exists : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
    IsUnit (Unit.crossingMatrix t) ∧ ContDiffAt ℝ 2 (Unit.raw t) 0 ∧
    Unit.rawQ t = nativeRawQ t := by
  have he := Unit.eventually_crossingMatrix_unit.and
    (Unit.eventually_raw_smooth.and Unit.eventually_rawQ_native)
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r,hr,fun t ht => hs (by simpa only [dist_zero_right,Real.norm_eq_abs] using ht)⟩

def objectRadius : ℝ := Classical.choose object_radius_exists

def interval : ℝ := min regularityRadius (objectRadius/2)

theorem interval_pos : 0 < interval :=
  lt_min regularityRadius_pos (half_pos (Classical.choose_spec object_radius_exists).1)

theorem interval_le_regularity : interval ≤ regularityRadius := min_le_left _ _

theorem object_gates (t : ℝ) (ht : |t| ≤ interval) :
    IsUnit (Unit.crossingMatrix t) ∧ ContDiffAt ℝ 2 (Unit.raw t) 0 ∧
    Unit.rawQ t = nativeRawQ t := by
  apply (Classical.choose_spec object_radius_exists).2 t
  have h := ht.trans (min_le_right regularityRadius (objectRadius/2))
  have hp : 0 < objectRadius := (Classical.choose_spec object_radius_exists).1
  change |t| < objectRadius
  linarith

/-- Three constraints at Lambda=the whole periodic T^(3), not a k=1 cube. -/
def domain (t : ℝ) : Submodule ℝ K where
  carrier := {B | (∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond unitL,
    b.1 ∉ (Finset.univ : Finset US) ∨ periodicLatticeShift b.1 b.2 ∉ (Finset.univ : Finset US) →
      unitCoordinates B b = 0) ∧ B ∈ axialSpace ∧ nativeRawQ t B = 0}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC
    refine ⟨?_, axialSpace.add_mem hB.2.1 hC.2.1, ?_⟩
    · intro b hb; simp [hB.1 b hb,hC.1 b hb]
    · rw [map_add,hB.2.2,hC.2.2,add_zero]
  smul_mem' := by
    intro r B hB
    refine ⟨?_,axialSpace.smul_mem r hB.2.1,?_⟩
    · intro b hb; simp [hB.1 b hb]
    · rw [map_smul,hB.2.2,smul_zero]

/-- A proved second jet of NONLINEAR averaging at V_t, not linear Q as Qext. -/
theorem second_jet_exact (t : ℝ) (ht : |t| ≤ interval) (B : K) :
    HConstruction.Reproduced.Dtilde2Shape (Unit.liftedRaw t) B = Unit.unitD2 t B :=
  Unit.liftedRaw_jet t (object_gates t ht).2.1 B

/-- The b0-supported solve for the second jet is genuine throughout the interval. -/
theorem second_jet_solve (t : ℝ) (ht : |t| ≤ interval) (B : K) :
    (∀ b, ¬ Crossing b → unitCoordinates (Unit.unitD2 t B) b = 0) ∧
    nativeRawQ t (Unit.unitD2 t B) = (1/2 : ℝ) • Unit.rawHessianAt t B B := by
  have h := Unit.unitD2_characterization t (object_gates t ht).1 B
  exact ⟨h.1, by rw [← (object_gates t ht).2.2]; exact h.2.1⟩

/-- Prop1 and the nonlinear jet/b0 gates hold on the SAME positive interval. -/
theorem interval_regularity (t : ℝ) (ht : |t| ≤ interval) (j : ℕ) (hj : j ≤ 3) :
    DepthUniformity.Fitted.SublatticePlaqBound (2^j) (tower t j) (2*alpha0) :=
  depth3_regularity t (ht.trans interval_le_regularity) j hj
end HConstruction.DK3

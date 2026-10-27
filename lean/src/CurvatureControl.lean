import MinimizerEquations
/-! The CMP122-II (1.8) axial-tree inequality cannot be applied to the
whole-torus R-gauge in GenK: constant modes survive it. This is a negative
control for pure-curvature coercivity, NOT a counterexample to the requested
mass bound with incoming-data norm. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace HConstruction.MassCMP122
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo_smul_fixed)
open HConstruction.GenK
open HConstruction.MassU1

variable (M : PeriodicLatticeExtent) {n : ℕ} (hn : 0 < n)

/-- A constant fine bond field on GenK's actual SU(2) carrier. -/
def constantFine (v : SuTwo) : Fine M (n := n) :=
  bfl2Equiv.symm (fun _ => v)

lemma constantFine_value (v : SuTwo) (b : Bond (fineExtent M n)) :
    bfl2Equiv (constantFine M (n := n) v) b = v := rfl

lemma constantFine_curl (v : SuTwo) : curl M (constantFine M (n := n) v) = 0 := by
  apply (WithLp.linearEquiv 2 ℝ _).injective
  funext p
  change curl M (constantFine M (n := n) v) p = 0
  rw [curl_apply]
  simp [AdalyFormal.Balaban.CovU1Reduction.flatCurlValue, constantFine_value]

lemma constantFine_incoming (v : SuTwo) (b : Bond M) :
    bfl2Equiv (incoming M hn (constantFine M (n := n) v)) b = v := by
  rw [incoming_apply]
  have hfield : bfl2Equiv (constantFine M (n := n) v) =
      (fun e : Bond (fineExtent M n) => (1 : ℝ) • v) := by
    funext e; rw [constantFine_value, one_smul]
  rw [hfield, lineCoarseRestrictSuTwo_smul_fixed]
  have h := AdalyFormal.Balaban.U1AnchorCoarse.lineCoarseRestrict_constBond
    (L := fineExtent M n) (ell := n) hn (fineTiling M hn)
    (fun _ : Fin 3 => (1 : ℝ)) (bonds M hn b)
  rw [h, one_smul]

/-- The actual gauge projection keeps the incoming datum and the zero curl,
so it cannot annihilate this nonzero harmonic mode. -/
theorem r_gauge_has_nonzero_harmonic_mode :
    ∃ Y : Fine M (n := n), gaugeConstraint M Y = 0 ∧
      curl M Y = 0 ∧ 0 < mass M Y ∧ incoming M hn Y ≠ 0 := by
  let A := constantFine M (n := n) suTwoWitness
  let Y := gaugePi M A
  have hB : incoming M hn A ≠ 0 := by
    intro hz
    have hb := constantFine_incoming M hn suTwoWitness (⟨fun _ => 0, 0⟩ : Bond M)
    rw [hz, map_zero] at hb
    exact suTwoWitness_ne_zero hb.symm
  have hQ : incoming M hn Y ≠ 0 := by
    rw [show Y = gaugePi M A from rfl, gaugePi_incoming]
    exact hB
  have hY : Y ≠ 0 := by
    intro hz; apply hQ; rw [hz, map_zero]
  refine ⟨Y, gaugePi_feasible M A, ?_, ?_, hQ⟩
  · rw [show Y = gaugePi M A from rfl, gaugePi_curl]
    exact constantFine_curl M suTwoWitness
  · unfold mass
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (one_div_pos.mpr (pow_pos hnR 3))
      (sq_pos_of_pos (norm_pos_iff.mpr hY))

/-- The counterexample applies to GenK's *actual physicalH* as well: the
constant field is a zero-curl competitor in the same Q fibre. It refutes
only a pure-curvature bound, not the S1 estimate with ||B||². -/
theorem actual_minimizer_constant_mode :
    ∃ B : Unit M, B ≠ 0 ∧
      fineEnergy M (physicalH M hn B) = 0 ∧
      0 < mass M (physicalH M hn B) := by
  let A := constantFine M (n := n) suTwoWitness
  let B := incoming M hn A
  have hB : B ≠ 0 := by
    intro hz
    have hb := constantFine_incoming M hn suTwoWitness (⟨fun _ => 0, 0⟩ : Bond M)
    rw [show incoming M hn A = B from rfl, hz, map_zero] at hb
    exact suTwoWitness_ne_zero hb.symm
  have hA : fineEnergy M A = 0 := by
    rw [fineEnergy, constantFine_curl M suTwoWitness, norm_zero]
    ring
  have hE : fineEnergy M (physicalH M hn B) = 0 := by
    have hmin := minimum M hn A B rfl
    have heq : fineEnergy M (physicalH M hn B) = fineEnergy M (H M hn B) := by
      unfold fineEnergy
      rw [physicalH_curl M hn B]
    have hnonneg : 0 ≤ fineEnergy M (physicalH M hn B) := by
      unfold fineEnergy
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      exact mul_nonneg (le_of_lt (one_div_pos.mpr hnR)) (sq_nonneg _)
    rw [←heq, hA] at hmin
    exact le_antisymm hmin hnonneg
  have hphys : physicalH M hn B ≠ 0 := by
    intro hz; apply hB
    rw [←physicalH_Q M hn B, hz, map_zero]
  refine ⟨B, hB, hE, ?_⟩
  unfold mass
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (one_div_pos.mpr (pow_pos hnR 3))
    (sq_pos_of_pos (norm_pos_iff.mpr hphys))

/-- An unconditional, actual-minimizer obstruction to replacing the datum
term in S1 by curl alone (even with a depth- or extent-dependent constant). -/
theorem no_pure_curvature_bound (K : ℝ) :
    ¬ ∀ B : Unit M,
      mass M (physicalH M hn B) ≤ K * fineEnergy M (physicalH M hn B) := by
  intro h
  obtain ⟨B, _, he, hm⟩ := actual_minimizer_constant_mode M hn
  have hB := h B
  rw [he, mul_zero] at hB
  exact (not_le_of_gt hm) hB
end HConstruction.MassCMP122

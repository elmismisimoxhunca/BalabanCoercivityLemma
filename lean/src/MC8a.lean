import MC2

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC8a -- abstract: an abelian field `U = exp(iη χ σ₃)` with `χ` obeying the three bounds is in `GlobalRegular2` (single gauge `g = 1`);
and the sine-profile arithmetic.
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

/-- the `ν`-sum inside `ddA` for a scalar field, as in `ddA_rsmul` -/
noncomputable def ddChi {L : PeriodicLatticeExtent} (η : ℝ) (χ : Bond L → ℝ) (x : PeriodicLatticeSite L) (μ : Fin 3) : ℝ :=
  η⁻¹ * ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        (η⁻¹ * (χ (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - χ (periodicLatticeShiftBack x ν, μ)
            - χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + χ (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (χ (periodicLatticeShift x ν, μ) - χ (x, μ)
            - χ (periodicLatticeShift x μ, ν) + χ (x, ν)))

/-- **abelian fields in the whole-torus class**: `χ` obeying the three scalar bounds gives `GlobalRegular2` with `g = 1`, `A = χ σ₃`. -/
theorem ufield_global {L : PeriodicLatticeExtent} {ell M f k : ℕ} {α₀ η : ℝ} (hη : 0 < η) (χ : Bond L → ℝ)
    (h1 : ∀ e, |χ e| * Real.sqrt 2 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 1))
    (h2 : ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
      |η⁻¹ * (χ (periodicLatticeShift x μ, ν) - χ (x, ν))| * Real.sqrt 2 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 2))
    (h3 : ∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
      |ddChi η χ x μ| * Real.sqrt 2 < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ k * η)⁻¹ ^ 3)) :
    GlobalRegular2 ell M f k α₀ η (Ufield η χ) := by
  refine ⟨fun _ => 1, fun e => χ e • sig, ?_, ?_, ?_⟩
  · intro e
    refine ⟨HT_rsmul_sig _, ?_, ?_⟩
    · rw [gauge_one]
      show NormedSpace.exp (Xm (η * χ e)) = _
      rw [smul_sig_eq]
    · rw [frobNorm_rsmul_sig]; exact h1 e
  · intro μ ν x
    have e1 : (η⁻¹ : ℝ) • (χ (periodicLatticeShift x μ, ν) • sig - χ (x, ν) • sig)
        = (η⁻¹ * (χ (periodicLatticeShift x μ, ν) - χ (x, ν))) • sig := by module
    show frobNorm ((η⁻¹ : ℝ) • ((fun e => χ e • sig) (periodicLatticeShift x μ, ν)
      - (fun e => χ e • sig) (x, ν))) < _
    simp only []
    rw [e1, frobNorm_rsmul_sig]
    exact h2 μ ν x
  · intro μ x
    show frobNorm (ddA η (fun e => χ e • sig) x μ) < _
    rw [ddA_rsmul, frobNorm_rsmul_sig]
    exact h3 μ x

/-! ## sine arithmetic -/

theorem sin_modEq (N v w : ℕ) (hN : 0 < N) (h : v % N = w % N) :
    Real.sin (2 * Real.pi * v / N) = Real.sin (2 * Real.pi * w / N) := by
  have hv := Nat.div_add_mod v N
  have hw := Nat.div_add_mod w N
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have e1 : 2 * Real.pi * (v : ℝ) / N = 2 * Real.pi * ((v % N : ℕ) : ℝ) / N + ((v / N : ℕ) : ℝ) * (2 * Real.pi) := by
    have : (v : ℝ) = (N : ℝ) * ((v / N : ℕ) : ℝ) + ((v % N : ℕ) : ℝ) := by exact_mod_cast hv.symm
    rw [this]; field_simp; ring
  have e2 : 2 * Real.pi * (w : ℝ) / N = 2 * Real.pi * ((w % N : ℕ) : ℝ) / N + ((w / N : ℕ) : ℝ) * (2 * Real.pi) := by
    have : (w : ℝ) = (N : ℝ) * ((w / N : ℕ) : ℝ) + ((w % N : ℕ) : ℝ) := by exact_mod_cast hw.symm
    rw [this]; field_simp; ring
  rw [e1, e2, Real.sin_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, h]

/-- first difference of the sine profile -/
theorem sin_diff1 (N v : ℕ) (hN : 0 < N) :
    |Real.sin (2 * Real.pi * ((v + 1 : ℕ) : ℝ) / N) - Real.sin (2 * Real.pi * (v : ℝ) / N)| ≤ 2 * Real.pi / N := by
  refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [show 2 * Real.pi * ((v : ℝ) + 1) / N - 2 * Real.pi * v / N = 2 * Real.pi / N by ring]
  exact abs_of_pos (by positivity)

/-- second difference of the sine profile -/
theorem sin_diff2 (N v : ℕ) (hN : 0 < N) :
    |2 * Real.sin (2 * Real.pi * ((v + 1 : ℕ) : ℝ) / N) - Real.sin (2 * Real.pi * (v : ℝ) / N)
        - Real.sin (2 * Real.pi * ((v + 2 : ℕ) : ℝ) / N)| ≤ (2 * Real.pi / N) ^ 2 := by
  set h : ℝ := 2 * Real.pi / N with hh
  set t : ℝ := 2 * Real.pi * ((v + 1 : ℕ) : ℝ) / N with ht
  have e1 : 2 * Real.pi * (v : ℝ) / N = t - h := by
    rw [ht, hh]; push_cast; ring
  have e2 : 2 * Real.pi * ((v + 2 : ℕ) : ℝ) / N = t + h := by
    rw [ht, hh]; push_cast; ring
  rw [e1, e2, Real.sin_sub, Real.sin_add]
  have : 2 * Real.sin t - (Real.sin t * Real.cos h - Real.cos t * Real.sin h)
      - (Real.sin t * Real.cos h + Real.cos t * Real.sin h) = 2 * Real.sin t * (1 - Real.cos h) := by ring
  rw [this, abs_mul, abs_mul]
  have hc0 : 0 ≤ 1 - Real.cos h := by linarith [Real.cos_le_one h]
  have hc1 : 1 - Real.cos h ≤ h ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
  rw [abs_of_nonneg hc0]
  have hs := Real.abs_sin_le_one t
  have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [this]
  nlinarith [abs_nonneg (Real.sin t)]

#print axioms ufield_global
#print axioms sin_modEq
#print axioms sin_diff1
#print axioms sin_diff2

end AdalyFormal.M0Corollary

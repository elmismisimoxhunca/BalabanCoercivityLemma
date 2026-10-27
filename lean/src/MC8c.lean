import MC8b

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

/-!
# MC8c -- the smooth sine field is in `GlobalRegular2` for EVERY `k` with a `k`-free amplitude (physical profile fixed in unit-lattice units).
-/
namespace AdalyFormal.M0Corollary

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLaneG AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

noncomputable def Aa (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) : ℝ :=
  if μ = 1 then (if ν = 0 then Dd L Ac y else 0) else 0

theorem tf_eq (L : PeriodicLatticeExtent) (Ac : ℝ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    chiP L Ac (periodicLatticeShift y ν, μ) - chiP L Ac (y, μ) - chiP L Ac (periodicLatticeShift y μ, ν)
      + chiP L Ac (y, ν) = Aa L Ac y ν μ - Aa L Ac y μ ν := by
  have h1 := chiP_diff L Ac y ν μ
  have h2 := chiP_diff L Ac y μ ν
  unfold Aa
  linarith

theorem Aa_diff (L : PeriodicLatticeExtent) (Ac : ℝ) (y x : PeriodicLatticeSite L) (ν μ : Fin 3) :
    |Aa L Ac y ν μ - Aa L Ac x ν μ| ≤ |Dd L Ac y - Dd L Ac x| := by
  unfold Aa
  split_ifs <;> simp

theorem ddChi_bound (L : PeriodicLatticeExtent) (Ac η : ℝ) (hη : 0 < η) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    |ddChi η (chiP L Ac) x μ| ≤ 6 * η⁻¹ * η⁻¹ * (|Ac| * (2 * Real.pi / ((L 0 + 1 : ℕ) : ℝ)) ^ 2) := by
  unfold ddChi
  set B : ℝ := |Ac| * (2 * Real.pi / ((L 0 + 1 : ℕ) : ℝ)) ^ 2 with hB
  have hi : (0 : ℝ) < η⁻¹ := inv_pos.mpr hη
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
      |η⁻¹ * (chiP L Ac (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - chiP L Ac (periodicLatticeShiftBack x ν, μ)
            - chiP L Ac (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + chiP L Ac (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (chiP L Ac (periodicLatticeShift x ν, μ) - chiP L Ac (x, μ)
            - chiP L Ac (periodicLatticeShift x μ, ν) + chiP L Ac (x, ν))| ≤ η⁻¹ * (2 * B) := by
    intro ν _
    rw [← mul_sub, abs_mul, abs_of_pos hi, tf_eq, tf_eq]
    apply mul_le_mul_of_nonneg_left _ hi.le
    have e : Aa L Ac (periodicLatticeShiftBack x ν) ν μ - Aa L Ac (periodicLatticeShiftBack x ν) μ ν
        - (Aa L Ac x ν μ - Aa L Ac x μ ν)
        = (Aa L Ac (periodicLatticeShiftBack x ν) ν μ - Aa L Ac x ν μ)
          - (Aa L Ac (periodicLatticeShiftBack x ν) μ ν - Aa L Ac x μ ν) := by ring
    rw [e]
    have a1 := Aa_diff L Ac (periodicLatticeShiftBack x ν) x ν μ
    have a2 := Aa_diff L Ac (periodicLatticeShiftBack x ν) x μ ν
    have d := Dd_shiftBack L Ac x ν
    have := abs_sub (Aa L Ac (periodicLatticeShiftBack x ν) ν μ - Aa L Ac x ν μ)
      (Aa L Ac (periodicLatticeShiftBack x ν) μ ν - Aa L Ac x μ ν)
    linarith
  have hsum : |∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
      (η⁻¹ * (chiP L Ac (periodicLatticeShift (periodicLatticeShiftBack x ν) ν, μ)
            - chiP L Ac (periodicLatticeShiftBack x ν, μ)
            - chiP L Ac (periodicLatticeShift (periodicLatticeShiftBack x ν) μ, ν)
            + chiP L Ac (periodicLatticeShiftBack x ν, ν))
          - η⁻¹ * (chiP L Ac (periodicLatticeShift x ν, μ) - chiP L Ac (x, μ)
            - chiP L Ac (periodicLatticeShift x μ, ν) + chiP L Ac (x, ν)))| ≤ 3 * (η⁻¹ * (2 * B)) := by
    calc _ ≤ ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), η⁻¹ * (2 * B) := Finset.sum_le_sum hterm
      _ = (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card • (η⁻¹ * (2 * B)) := by rw [Finset.sum_const]
      _ ≤ 3 * (η⁻¹ * (2 * B)) := by
          rw [nsmul_eq_mul]
          have hcard : (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card ≤ 3 := by
            calc _ ≤ Finset.univ.card := Finset.card_le_univ _
              _ = 3 := by simp
          have : ((Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card : ℝ) ≤ 3 := by exact_mod_cast hcard
          have hnn : 0 ≤ η⁻¹ * (2 * B) := by positivity
          nlinarith
  rw [abs_mul, abs_of_pos hi]
  calc η⁻¹ * _ ≤ η⁻¹ * (3 * (η⁻¹ * (2 * B))) := mul_le_mul_of_nonneg_left hsum hi.le
    _ = 6 * η⁻¹ * η⁻¹ * B := by ring

theorem chiP_abs (L : PeriodicLatticeExtent) (Ac : ℝ) (e : Bond L) : |chiP L Ac e| ≤ |Ac| := by
  unfold chiP sprof
  split_ifs
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · simp

/-- **the smooth curved witness is in the whole-torus class for every `k`**: amplitude `α/2` (k-free), unit-lattice wavelength `Lu 0 + 1 ≥ 16`. -/
theorem sine_globalRegular2 (ell M k : ℕ) (hell : 0 < ell) (Lu : PeriodicLatticeExtent) (h16 : 16 ≤ Lu 0 + 1)
    (α₀ : ℝ) (hα : 0 < (12 : ℝ) * M * α₀) :
    GlobalRegular2 ell M 12 k α₀ ((ell : ℝ) ^ k)⁻¹
      (Ufield ((ell : ℝ) ^ k)⁻¹ (chiP (scaleUp ell k Lu) ((12 : ℝ) * M * α₀ / 2))) := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hη : 0 < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hnη : (ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹ = 1 := mul_inv_cancel₀ hn.ne'
  set α : ℝ := (12 : ℝ) * M * α₀ with hαdef
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = α := by rw [hαdef]; norm_num
  set Ac : ℝ := α / 2 with hAc
  have hAc0 : 0 < Ac := by positivity
  have hN0 : (((scaleUp ell k Lu) 0 + 1 : ℕ) : ℝ) = ((Lu 0 + 1 : ℕ) : ℝ) * (ell : ℝ) ^ k := by
    rw [scaleUp_succ ell k Lu hell 0]; push_cast; ring
  set θ : ℝ := 2 * Real.pi / ((Lu 0 + 1 : ℕ) : ℝ) with hθ
  have h16r : (16 : ℝ) ≤ ((Lu 0 + 1 : ℕ) : ℝ) := by exact_mod_cast h16
  have hpi := Real.pi_lt_d2
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 0.4 := by
    rw [hθ, div_le_iff₀ (by linarith)]; nlinarith
  have hh : (2 * Real.pi / (((scaleUp ell k Lu) 0 + 1 : ℕ) : ℝ)) = ((ell : ℝ) ^ k)⁻¹ * θ := by
    rw [hN0, hθ]; field_simp
  have hs2 : Real.sqrt 2 < 1.5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hα' : α * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 1) = α := by rw [hnη]; simp
  have hα2 : α * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 2) = α := by rw [hnη]; simp
  have hα3 : α * (((ell : ℝ) ^ k * ((ell : ℝ) ^ k)⁻¹)⁻¹ ^ 3) = α := by rw [hnη]; simp
  apply ufield_global hη
  · intro e
    rw [hcast, hα']
    have := chiP_abs (scaleUp ell k Lu) Ac e
    rw [abs_of_pos hAc0] at this
    nlinarith
  · intro μ ν x
    rw [hcast, hα2]
    have h1 := chiP_diff (scaleUp ell k Lu) Ac x μ ν
    rw [h1]
    have hD := Dd_abs (scaleUp ell k Lu) Ac x
    rw [abs_of_pos hAc0, hh] at hD
    have key : |((ell : ℝ) ^ k)⁻¹⁻¹ * (if ν = 1 then (if μ = 0 then Dd (scaleUp ell k Lu) Ac x else 0) else 0)|
        ≤ Ac * θ := by
      rw [inv_inv]
      split_ifs
      · rw [abs_mul, abs_of_pos hn]
        calc _ ≤ (ell : ℝ) ^ k * (Ac * (((ell : ℝ) ^ k)⁻¹ * θ)) := mul_le_mul_of_nonneg_left hD hn.le
          _ = Ac * θ := by field_simp
      all_goals simp; positivity
    have : |((ell : ℝ) ^ k)⁻¹⁻¹ * (if ν = 1 then (if μ = 0 then Dd (scaleUp ell k Lu) Ac x else 0) else 0)| * Real.sqrt 2
        ≤ Ac * θ * 1.5 := by
      exact mul_le_mul key hs2.le hs0.le (by positivity)
    nlinarith
  · intro μ x
    rw [hcast, hα3]
    have hb := ddChi_bound (scaleUp ell k Lu) Ac _ hη x μ
    rw [abs_of_pos hAc0, hh] at hb
    have e : 6 * ((ell : ℝ) ^ k)⁻¹⁻¹ * ((ell : ℝ) ^ k)⁻¹⁻¹ * (Ac * (((ell : ℝ) ^ k)⁻¹ * θ) ^ 2) = 6 * Ac * θ ^ 2 := by
      rw [inv_inv]; field_simp
    rw [e] at hb
    have : |ddChi ((ell : ℝ) ^ k)⁻¹ (chiP (scaleUp ell k Lu) Ac) x μ| * Real.sqrt 2 ≤ 6 * Ac * θ ^ 2 * 1.5 :=
      mul_le_mul hb hs2.le hs0.le (by positivity)
    nlinarith [sq_nonneg θ, mul_pos hAc0 hθ0]

#print axioms ddChi_bound
#print axioms sine_globalRegular2

end AdalyFormal.M0Corollary

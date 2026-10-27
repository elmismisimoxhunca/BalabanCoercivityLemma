import M2B6c

/-!
# M2B6d -- `cutA_M1Bounds` : the cut-off cube field satisfies lane B's global `M1Bounds` (m2_bridge_20261014, Layer B1/B3)

Hypotheses: `Admissible`, a class cube `sites` of index `i` carrying `CubeData` (the printed clauses (3.35)+(3.36) for the cube gauge field `A`),
a cutoff `χ` with `CutSpec sites χ τ1 τ2`, and the smallness `64 τ1 ell^i ≤ 1`, `24 (τ2 + τ1²) ell^(2i) ≤ 1`.
Conclusion: `M1Bounds S ell M f k (ell^3 · 2 α₀) η (cutA χ A)`  -- on EVERY bond of the torus.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M1 (M1Bounds bstrat StratReads)

variable {L : PeriodicLatticeExtent}

section main

variable {ell M R f k i : ℕ} {S : Tower L} {α₀ η : ℝ} {sites : Set (PeriodicLatticeSite L)} {A : Bond L → M2m}
  {χ : PeriodicLatticeSite L → ℝ} {τ1 τ2 : ℝ}

theorem cubeBond_of_chi (hc : CutSpec sites χ τ1 τ2) {e : Bond L} (h : χ e.1 ≠ 0) : CubeBond sites e := by
  have hx := hc.supp e.1 h
  refine ⟨hx e.1 (by rw [pdist_self']; norm_num), hx _ ?_⟩
  have := pdist_shift_le e.1 e.2
  omega

theorem cutA_pos (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η) (j p : ℕ) :
    0 < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ p) := by
  have h1 : (0 : ℝ) < f := by exact_mod_cast hf
  have h2 : (0 : ℝ) < M := by exact_mod_cast hM
  have h3 : (0 : ℝ) < ell := by exact_mod_cast hell
  positivity

theorem lt_transfer (hell : 1 ≤ ell) (hη : 0 < η) (hα : 0 ≤ α₀) {j p : ℕ} (hj : j ≤ i + 1) (hp : p ≤ 3) {x : ℝ}
    (hx : x < (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ p)) :
    x < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ p) :=
  bound_transfer hell hη hj hp (by positivity) hx

theorem cut_c1 (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hq : IsClassCube ell M f k S sites i) (hd : CubeData ell M f k α₀ η sites i A) (hc : CutSpec sites χ τ1 τ2) :
    ∀ (e : Bond L) (j : ℕ), j ≤ bstrat S k e →
      frobNorm (cutA χ A e) < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ 1) := by
  intro e j hj
  by_cases h0 : χ e.1 = 0
  · have : cutA χ A e = 0 := by unfold cutA; rw [h0, zero_smul]
    rw [this, frob_zero']
    exact cutA_pos hell hf hM hα hη j 1
  · have hb := cubeBond_of_chi hc h0
    have hji : j ≤ i + 1 := le_trans hj (bstrat_le_succ_of_cubeBond hA hq hb)
    apply lt_transfer hell hη hα.le hji (by norm_num)
    have h1 := hd.c1 e hb
    have h2 : frobNorm (cutA χ A e) ≤ frobNorm (A e) := by
      unfold cutA
      rw [frob_smul, abs_of_nonneg (hc.nonneg _)]
      calc χ e.1 * frobNorm (A e) ≤ 1 * frobNorm (A e) :=
            mul_le_mul_of_nonneg_right (hc.le_one _) (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
        _ = frobNorm (A e) := one_mul _
    have hKX : (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) ≤ (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) := by
      have h3 : (0 : ℝ) < f := by exact_mod_cast hf
      have h4 : (0 : ℝ) < M := by exact_mod_cast hM
      have h5 : (0 : ℝ) < ell := by exact_mod_cast hell
      have : 0 ≤ (f : ℝ) * M * α₀ * (((ell : ℝ) ^ i * η)⁻¹ ^ 1) := by positivity
      nlinarith
    linarith

theorem cut_ht (hc : CutSpec sites χ τ1 τ2) (hd : CubeData ell M f k α₀ η sites i A) :
    ∀ e : Bond L, HT (cutA χ A e) := by
  intro e
  by_cases h0 : χ e.1 = 0
  · have : cutA χ A e = 0 := by unfold cutA; rw [h0, zero_smul]
    rw [this]
    simp [HT]
  · have hb := cubeBond_of_chi hc h0
    have hh := hd.ht e hb
    obtain ⟨h1, h2⟩ := hh
    unfold cutA HT
    constructor
    · rw [Matrix.conjTranspose_smul, h1]; simp
    · rw [Matrix.trace_smul, h2]; simp

theorem cut_c2 (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hq : IsClassCube ell M f k S sites i) (hd : CubeData ell M f k α₀ η sites i A) (hc : CutSpec sites χ τ1 τ2)
    (h1 : 64 * τ1 * (ell : ℝ) ^ i ≤ 1) :
    ∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      j ≤ bstrat S k (x, ν) → j ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      frobNorm ((η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν)))
        < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ 2) := by
  intro μ ν x j hj1 hj2
  by_cases hz : χ x = 0 ∧ χ (periodicLatticeShift x μ) = 0
  · have : (η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν)) = 0 := by
      unfold cutA; dsimp only; rw [hz.1, hz.2]; simp
    rw [this, frob_zero']
    exact cutA_pos hell hf hM hα hη j 2
  · have hex : ∃ p, χ p ≠ 0 ∧ pdist x p ≤ 1 := by
      by_cases hx0 : χ x = 0
      · refine ⟨periodicLatticeShift x μ, ?_, pdist_shift_le x μ⟩
        intro h; exact hz ⟨hx0, h⟩
      · exact ⟨x, hx0, by rw [pdist_self']; norm_num⟩
    obtain ⟨p, hp, hxp⟩ := hex
    have hx4 := cut_hx4 hc hp (by omega : pdist x p ≤ 2)
    have d0 : pdist x x ≤ 3 := by rw [pdist_self']; norm_num
    have b0 : CubeBond sites ((x, ν) : Bond L) := cubeBond_of_near hx4 (e := (x, ν)) d0
    have b1 : CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) :=
      cubeBond_of_near hx4 (e := (periodicLatticeShift x μ, ν)) (le_trans (pdist_shift_le x μ) (by norm_num))
    have hji : j ≤ i + 1 := le_trans hj1 (bstrat_le_succ_of_cubeBond hA hq b0)
    apply lt_transfer hell hη hα.le hji (by norm_num)
    set K : ℝ := (f : ℝ) * M * α₀ with hK
    set E : ℝ := (ell : ℝ) ^ i with hE
    set X : ℝ := (E * η)⁻¹ with hX
    have h3 : (0 : ℝ) < f := by exact_mod_cast hf
    have h4 : (0 : ℝ) < M := by exact_mod_cast hM
    have h5 : (0 : ℝ) < ell := by exact_mod_cast hell
    have hK0 : 0 < K := by positivity
    have hE1 : 1 ≤ E := one_le_pow₀ (by exact_mod_cast hell)
    have hX0 : 0 < X := by rw [hX]; have : 0 < E := by linarith
                           positivity
    have hηinv : η⁻¹ = E * X := by rw [hX]; field_simp
    have τ1nn : 0 ≤ τ1 := le_trans (abs_nonneg _) (hc.fwd x μ)
    have hdiff := hd.c2 μ ν x b0 b1
    have hc1 := hd.c1 (x, ν) b0
    have id : (η⁻¹ : ℝ) • (cutA χ A (periodicLatticeShift x μ, ν) - cutA χ A (x, ν))
        = χ (periodicLatticeShift x μ) • ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          + (η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)) • A (x, ν) := by
      unfold cutA; dsimp only; module
    rw [id]
    refine lt_of_le_of_lt (frob_add_le _ _) ?_
    rw [frob_smul (χ (periodicLatticeShift x μ)) _, frob_smul (η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)) (A (x, ν))]
    have e1 : |χ (periodicLatticeShift x μ)| * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
        ≤ K * X ^ 2 := by
      rw [abs_of_nonneg (hc.nonneg _)]
      calc χ (periodicLatticeShift x μ) * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          ≤ 1 * frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) :=
            mul_le_mul_of_nonneg_right (hc.le_one _) (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
        _ ≤ K * X ^ 2 := by rw [one_mul]; exact hdiff.le
    have e2 : |η⁻¹ * (χ (periodicLatticeShift x μ) - χ x)| * frobNorm (A (x, ν)) ≤ K * X ^ 2 / 64 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hη)]
      have : |χ (periodicLatticeShift x μ) - χ x| ≤ τ1 := hc.fwd x μ
      have hc1' : frobNorm (A (x, ν)) ≤ K * X := by simpa [hK, hX, hE] using hc1.le
      calc η⁻¹ * |χ (periodicLatticeShift x μ) - χ x| * frobNorm (A (x, ν)) ≤ η⁻¹ * τ1 * (K * X) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left this (inv_pos.mpr hη).le) hc1'
              (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (by positivity)
        _ = K * X ^ 2 * (τ1 * E) := by rw [hηinv]; ring
        _ ≤ K * X ^ 2 / 64 := by
            have : τ1 * E ≤ 1 / 64 := by linarith
            have hh : 0 ≤ K * X ^ 2 := by positivity
            calc K * X ^ 2 * (τ1 * E) ≤ K * X ^ 2 * (1 / 64) := mul_le_mul_of_nonneg_left this hh
              _ = K * X ^ 2 / 64 := by ring
    have hKX : 0 < K * X ^ 2 := by positivity
    calc _ ≤ K * X ^ 2 + K * X ^ 2 / 64 := add_le_add e1 e2
      _ < (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 2) := by
        have : (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 2) = 2 * (K * X ^ 2) := by
          rw [hK, hX, hE]; ring
        rw [this]; linarith

end main

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.cut_c1
#print axioms AdalyFormal.M2Bridge.cut_ht
#print axioms AdalyFormal.M2Bridge.cut_c2

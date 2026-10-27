import M2B6d

/-!
# M2B6e -- clause 3 (`ddA`) of the cut-off field and the assembly `cutA_M1Bounds` (m2_bridge_20261014, Layer B1/B3/B5)
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

theorem exists_ne (μ : Fin 3) : ∃ ν : Fin 3, ν ≠ μ := by
  fin_cases μ
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

theorem cut_c3 (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hq : IsClassCube ell M f k S sites i) (hd : CubeData ell M f k α₀ η sites i A) (hc : CutSpec sites χ τ1 τ2)
    (h1 : 64 * τ1 * (ell : ℝ) ^ i ≤ 1) (h2 : 24 * (τ2 + τ1 ^ 2) * ((ell : ℝ) ^ i) ^ 2 ≤ 1) :
    ∀ (μ : Fin 3) (x : PeriodicLatticeSite L) (j : ℕ),
      (∀ ν : Fin 3, ν ≠ μ → StratReads S k j (periodicLatticeShiftBack x ν) ν μ ∧ StratReads S k j x ν μ) →
      frobNorm (ddA η (cutA χ A) x μ)
        < (f : ℝ) * M * ((ell : ℝ) ^ 3 * (2 * α₀)) * (((ell : ℝ) ^ j * η)⁻¹ ^ 3) := by
  intro μ x j hs
  by_cases hg : ∃ p, χ p ≠ 0 ∧ pdist x p ≤ 2
  · obtain ⟨p, hp, hxp⟩ := hg
    have hx4 := cut_hx4 hc hp hxp
    obtain ⟨ν0, hν0⟩ := exists_ne μ
    have hb : CubeBond sites ((periodicLatticeShift x ν0, μ) : Bond L) :=
      cubeBond_of_near hx4 (e := (periodicLatticeShift x ν0, μ)) (le_trans (pdist_shift_le x ν0) (by norm_num))
    have hji : j ≤ i + 1 := le_trans (hs ν0 hν0).2.1 (bstrat_le_succ_of_cubeBond hA hq hb)
    apply lt_transfer hell hη hα.le hji (by norm_num)
    set K : ℝ := (f : ℝ) * M * α₀ with hK
    set E : ℝ := (ell : ℝ) ^ i with hE
    set X : ℝ := (E * η)⁻¹ with hX
    have h3 : (0 : ℝ) < f := by exact_mod_cast hf
    have h4 : (0 : ℝ) < M := by exact_mod_cast hM
    have h5 : (0 : ℝ) < ell := by exact_mod_cast hell
    have hK0 : 0 < K := by positivity
    have hE1 : 1 ≤ E := one_le_pow₀ (by exact_mod_cast hell)
    have hE0 : 0 < E := by linarith
    have hX0 : 0 < X := by rw [hX]; positivity
    have τ1nn : 0 ≤ τ1 := le_trans (abs_nonneg _) (hc.fwd x μ)
    have τ2nn : 0 ≤ τ2 := le_trans (abs_nonneg _) (hc.sec x μ)
    have hdd := hd.c3 μ x (fun ν _ => ⟨curlReads_of_near hx4 (pdist_shiftBack_le x ν) ν μ,
      curlReads_of_near hx4 (by rw [pdist_self']; norm_num) ν μ⟩)
    rw [ddA_cut_decomp]
    refine lt_of_le_of_lt (frob_add_le _ _) ?_
    rw [frob_smul (χ x) _]
    have e1 : |χ x| * frobNorm (ddA η A x μ) ≤ frobNorm (ddA η A x μ) := by
      rw [abs_of_nonneg (hc.nonneg _)]
      calc χ x * frobNorm (ddA η A x μ) ≤ 1 * frobNorm (ddA η A x μ) :=
            mul_le_mul_of_nonneg_right (hc.le_one _) (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _)
        _ = frobNorm (ddA η A x μ) := one_mul _
    have hBR : ∀ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
        frobNorm ((η⁻¹ : ℝ) • Rv χ A x μ ν) ≤ η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)) := by
      intro ν hν
      have hne : ν ≠ μ := (Finset.mem_filter.mp hν).2
      have := Rv_bound hd hc hη hx4 hne
      rw [frob_smul, abs_of_pos (inv_pos.mpr hη)]
      apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hη).le
      simpa [hK, hX, hE] using this
    have hcard : (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card ≤ 3 := by
      calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_filter_le _ _
        _ = 3 := by simp
    have e2 : frobNorm ((η⁻¹ : ℝ) • ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), (η⁻¹ : ℝ) • Rv χ A x μ ν)
        ≤ K * X ^ 3 / 2 := by
      rw [frob_smul, abs_of_pos (inv_pos.mpr hη)]
      have hs1 := frob_sum_le (Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)) (fun ν => (η⁻¹ : ℝ) • Rv χ A x μ ν)
      have hs2 : ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), frobNorm ((η⁻¹ : ℝ) • Rv χ A x μ ν)
          ≤ ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
            η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)) := Finset.sum_le_sum hBR
      rw [Finset.sum_const, nsmul_eq_mul] at hs2
      have hBRnn : 0 ≤ η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)) := by positivity
      have hs3 : ((Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ)).card : ℝ)
          * (η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)))
          ≤ 3 * (η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X))) := by
        apply mul_le_mul_of_nonneg_right _ hBRnn
        exact_mod_cast hcard
      have hfin := scal_final (K := K) (E := E) (η := η) (τ1 := τ1) (τ2 := τ2) (X := X) hK0 hE1 hη hX h1 h2 τ1nn τ2nn
      calc η⁻¹ * frobNorm (∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ), (η⁻¹ : ℝ) • Rv χ A x μ ν)
          ≤ η⁻¹ * (3 * (η⁻¹ * (8 * τ1 * (η * (K * X ^ 2)) + (τ2 + τ1 ^ 2) * (K * X)))) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_pos.mpr hη).le
        _ ≤ K * X ^ 3 / 2 := hfin
    have hdd' : frobNorm (ddA η A x μ) < K * X ^ 3 := by simpa [hK, hX, hE] using hdd
    have hKX : 0 < K * X ^ 3 := by positivity
    have : (f : ℝ) * M * (2 * α₀) * (((ell : ℝ) ^ i * η)⁻¹ ^ 3) = 2 * (K * X ^ 3) := by
      rw [hK, hX, hE]; ring
    rw [this]
    linarith
  · push_neg at hg
    have hz : ∀ p, pdist x p ≤ 2 → χ p = 0 := fun p hp => by
      by_contra h; exact absurd hp (not_le.mpr (hg p h))
    have z0 : χ x = 0 := hz x (by rw [pdist_self']; norm_num)
    have zq : χ (periodicLatticeShift x μ) = 0 := hz _ (le_trans (pdist_shift_le x μ) (by norm_num))
    have hzero : ddA η (cutA χ A) x μ = 0 := by
      rw [ddA_def]
      have : ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 => ν ≠ μ),
          (curlA η (cutA χ A) (periodicLatticeShiftBack x ν) ν μ - curlA η (cutA χ A) x ν μ) = 0 := by
        apply Finset.sum_eq_zero
        intro ν _
        have zp : χ (periodicLatticeShift x ν) = 0 := hz _ (le_trans (pdist_shift_le x ν) (by norm_num))
        have zm : χ (periodicLatticeShiftBack x ν) = 0 := hz _ (le_trans (pdist_shiftBack_le x ν) (by norm_num))
        have zr : χ (periodicLatticeShift (periodicLatticeShiftBack x ν) μ) = 0 := by
          apply hz
          have h1 := pdist_triangle x (periodicLatticeShiftBack x ν) (periodicLatticeShift (periodicLatticeShiftBack x ν) μ)
          have h2 := pdist_shift_le (periodicLatticeShiftBack x ν) μ
          have h3 := pdist_shiftBack_le x ν
          omega
        rw [ddTerm_eq]
        simp [cutA, z0, zq, zp, zm, zr]
      rw [this, smul_zero]
    rw [hzero, frob_zero']
    exact cutA_pos hell hf hM hα hη j 3

/-- **the cut-off cube field is in lane B's global M1 regime.** -/
theorem cutA_M1Bounds (hA : Admissible ell M R k S) (hell : 1 ≤ ell) (hf : 1 ≤ f) (hM : 1 ≤ M) (hα : 0 < α₀) (hη : 0 < η)
    (hq : IsClassCube ell M f k S sites i) (hd : CubeData ell M f k α₀ η sites i A) (hc : CutSpec sites χ τ1 τ2)
    (h1 : 64 * τ1 * (ell : ℝ) ^ i ≤ 1) (h2 : 24 * (τ2 + τ1 ^ 2) * ((ell : ℝ) ^ i) ^ 2 ≤ 1) :
    M1Bounds S ell M f k ((ell : ℝ) ^ 3 * (2 * α₀)) η (cutA χ A) :=
  ⟨cut_ht hc hd, cut_c1 hA hell hf hM hα hη hq hd hc, cut_c2 hA hell hf hM hα hη hq hd hc h1,
    cut_c3 hA hell hf hM hα hη hq hd hc h1 h2⟩

end main

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.cut_c3
#print axioms AdalyFormal.M2Bridge.cutA_M1Bounds

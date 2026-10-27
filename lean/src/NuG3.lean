import NuG2
import NuQ3
import NuE3

/-!
# NuG3 -- Z-fields of `E₀` with `Q = 0` are chain vectors of the constraint space (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

section
variable [CfData]
variable {ell M R : ℕ}

/-- the level of a chain row. -/
theorem row_level (hg : NGeo ell M R) {i : ℕ} (hi : i < RN hg) :
    ∃ j, j ≤ 2 ∧ isRowN ell M R j (neP0 ell M R + stN ell M R i) ∧ lnN ell M R i = ell ^ j := by
  have hs := RN_start hg i hi
  rcases hs with h | h | h
  · exact ⟨0, by norm_num, h, rowLen_of_isRowN hg h⟩
  · exact ⟨1, by norm_num, h, rowLen_of_isRowN hg h⟩
  · exact ⟨2, by norm_num, h, rowLen_of_isRowN hg h⟩

theorem rowsum_eq_fSum (hg : NGeo ell M R) {i : ℕ} (hi : i < RN hg) (e : Fin (nN ell M R) → ℝ) :
    ∃ j, j ≤ 2 ∧ isRowN ell M R j (neP0 ell M R + stN ell M R i) ∧
      ∑ x ∈ (univ.filter (fun x : Fin (nN ell M R) => rowOfN ell M R x.val = i)), e x =
        fSum ell j (fe (neP0 ell M R) e) (neP0 ell M R + stN ell M R i) := by
  obtain ⟨j, hj, hr, hl⟩ := row_level hg hi
  exact ⟨j, hj, hr, (fSum_eq_rowsum hg hj hi rfl hl e).symm⟩

/-- the chain vector of a profile. -/
def chainOf (P0 n : ℕ) (f : ℕ → ℝ) : Fin n → ℝ := fun x => f (P0 + x.val)

theorem fe_chainOf {P0 n L0 : ℕ} {f : ℕ → ℝ} (hf : ∀ v, v ≤ L0 → ¬ (P0 ≤ v ∧ v < P0 + n) → f v = 0) {v : ℕ}
    (hvL : v ≤ L0) : fe P0 (chainOf P0 n f) v = f v := by
  unfold fe
  by_cases h1 : P0 ≤ v
  · rw [if_pos h1]
    unfold ex chainOf
    by_cases h2 : v - P0 < n
    · rw [dif_pos h2]; simp only []; rw [show P0 + (v - P0) = v by omega]
    · rw [dif_neg h2]; exact (hf v hvL (by omega)).symm
  · rw [if_neg h1]; exact (hf v hvL (by omega)).symm

/-- a Z-field of `E₀` vanishes on the slices outside `Ω₀`. -/
theorem zfield_vanish_outside (hg : NGeo ell M R) (hM : 0 < M) (hR : 1 ≤ R) (f : ℕ → ℝ)
    (hf : (zfield f : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R))) (v : ℕ)
    (hv : v ≤ scaleUp ell 2 (neLu M R) 0) (hJ : ¬ (neP0 ell M R ≤ v ∧ v < neQ0 ell M R)) : f v = 0 := by
  have hell : 0 < ell := by have := hg.hell; omega
  have hdim : ∀ μ : Fin 3, scaleUp ell 2 (neLu M R) μ + 1 = neN ell M R := fun μ => ne_scaleUp hell hM μ
  let y : PeriodicLatticeSite (scaleUp ell 2 (neLu M R)) := fun μ => ⟨if μ = 0 then v else 0, by
    have := hdim μ
    have h0 := hdim 0
    split_ifs <;> omega⟩
  have hy0 : (y 0).val = v := by simp [y]
  have hb := hf (y, (1 : Fin 3)) (by
    intro hmem
    apply hJ
    rcases hmem with h1 | h1
    · have h1' : y ∈ (geomOf ell 2 (neS ell M R)).Om0 := h1
      have := (neS_om0 y).mp h1'
      rw [hy0] at this; exact this
    · have h1' : periodicLatticeShift y 1 ∈ (geomOf ell 2 (neS ell M R)).Om0 := h1
      have := (neS_om0 (periodicLatticeShift y 1)).mp h1'
      rw [shift_coord_ne y 1 0 (by decide), hy0] at this; exact this)
  have hb' : dgS (f v) = 0 := by
    have : (zfield f : BondFnL2 (scaleUp ell 2 (neLu M R))) (y, (1 : Fin 3)) = dgS (f (y 0).val) := by
      show zfun f (y, (1 : Fin 3)) = _
      unfold zfun; simp
    rw [this, hy0] at hb
    exact hb
  exact dgS_eq_zero hb'


/-- a Z-field of `E₀` annihilated by `Q` is the Z-field of a chain vector of the constraint space. -/
theorem wz_chain (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) {d : ↥(bondSupp (geomOf ell 2 (neS ell M R)))} (hd : d ∈ WZ (geomOf ell 2 (neS ell M R)))
    (hQ : (Pt ell M R (by omega) (neC0 ell M R) t a).data.Q d = 0) :
    ∃ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) ∧ d = xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  obtain ⟨f, hf⟩ := hd
  have hmem := d.2
  rw [hf] at hmem
  have hvan : ∀ v, v ≤ scaleUp ell 2 (neLu M R) 0 → ¬ (neP0 ell M R ≤ v ∧ v < neP0 ell M R + nN ell M R) → f v = 0 := by
    intro v hvL hv
    have hv' : ¬ (neP0 ell M R ≤ v ∧ v < neQ0 ell M R) := by unfold nN at hv; omega
    exact zfield_vanish_outside hg hM hR f hmem v hvL hv'
  set e : Fin (nN ell M R) → ℝ := chainOf (neP0 ell M R) (nN ell M R) f with he
  have hfe : ∀ v, v ≤ scaleUp ell 2 (neLu M R) 0 → fe (neP0 ell M R) e v = f v := fun v hv => fe_chainOf hvan hv
  have hzf : (zfield f : BondFnL2 (scaleUp ell 2 (neLu M R))) = zfield (fe (neP0 ell M R) e) :=
    zfield_congr (fun v hv => (hfe v hv).symm)
  refine ⟨e, ?_, Subtype.ext (by rw [hf, hzf]; rfl)⟩
  -- the row sums
  intro r
  by_cases hrR : r < RN hg
  · obtain ⟨j, hj, hjr, hsum⟩ := rowsum_eq_fSum hg hrR e
    rw [hsum]
    -- Q d = 0 gives zero row profile
    have hQz : (QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (neC0 ell M R) t)
        (zfield f) : FSp (geomOf ell 2 (neS ell M R))) = 0 := by
      have : (Pt ell M R (by omega) (neC0 ell M R) t a).data.Q d = QfullOf (geomOf ell 2 (neS ell M R))
          (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (neC0 ell M R) t) (d : BondFnL2 (scaleUp ell 2 (neLu M R))) := rfl
      rw [← hf, ← this]; exact hQ
    rw [Qfull_zfield_eq_zrow0 S f] at hQz
    have hrow0 := zrow_rows_zero hg hM hR _ hQz j hj _ hjr
    have hfS : fSum ell j (fe (neP0 ell M R) e) (neP0 ell M R + stN ell M R r) = fSum ell j f (neP0 ell M R + stN ell M R r) := by
      rw [fSum_eq_sum, fSum_eq_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      obtain ⟨j', hj', hjr', hl'⟩ := row_level hg hrR
      have hjj : j' = j := by
        have := rowLen_of_isRowN hg hjr'
        have h2 := rowLen_of_isRowN hg hjr
        have : ell ^ j' = ell ^ j := by rw [← this, ← h2]
        exact Nat.pow_right_injective (by have := hg.hell; omega) this
      subst hjj
      have hrow := row_lt_nD (nested_rowGeom hg) hrR
      have hend : stN ell M R r + lnN ell M R r ≤ nN ell M R := hrow
      have hQN : neQ0 ell M R + 1 ≤ neN ell M R := ne_Q0_lt_N_two hg.hell hM hR
      have hN1 : scaleUp ell 2 (neLu M R) 0 + 1 = neN ell M R := ne_scaleUp hell hM 0
      apply hfe
      unfold nN at hend
      omega
    rw [hfS]
    have hne : ((ell : ℝ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hell.ne')
    have : ((ell : ℝ) ^ j)⁻¹ * fSum ell j f (neP0 ell M R + stN ell M R r) = 0 := hrow0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (inv_ne_zero hne)
    · exact h
  · apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exfalso
    have := (rowOfN_spec hg x.2).1
    omega

end

end AdalyFormal.NcwdhTwo

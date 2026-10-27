import SoZ1
import SoE3
import NuG3
import NuG2
import NuQ3
import NuE3

/-!
# NuG3 -- Z-fields of `E₀` with `Q = 0` are chain vectors of the constraint space (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.NcwdhTwo

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
variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

/-- a Z-field of `E₀` annihilated by `Q` is the Z-field of a chain vector of the constraint space. -/
theorem wz_chain (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) {d : ↥(bondSupp (geomOf ell 2 (neS ell M R)))} (hd : d ∈ WZ (geomOf ell 2 (neS ell M R)))
    (hQ : (Pt ell M R (by omega) (C) t a).data.Q d = 0) :
    ∃ e : Fin (nN ell M R) → ℝ, e ∈ Vsub (rowOfN ell M R) ∧ d = xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have S := nested_z0Setup_S hCp hell2 hE hdvd hM hR t ht
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
    have hQz : (QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (C) t)
        (zfield f) : FSp (geomOf ell 2 (neS ell M R))) = 0 := by
      have : (Pt ell M R (by omega) (C) t a).data.Q d = QfullOf (geomOf ell 2 (neS ell M R))
          (stag0Cfg (L := scaleUp ell 2 (neLu M R)) (C) t) (d : BondFnL2 (scaleUp ell 2 (neLu M R))) := rfl
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

#print axioms wz_chain

end AdalyFormal.SitesOnly

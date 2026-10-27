import ZStatementP428

set_option autoImplicit false

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

namespace AdalyFormal.Fidelity.SheetVariants

-- The total map from the decision, including its modulo at zero scale.
def unitEmb {Lu : PeriodicLatticeExtent} (ell k : ℕ)
    (y : PeriodicLatticeSite Lu) : PeriodicLatticeSite (scaleUp ell k Lu) :=
  fun μ => ⟨(ell ^ k * (y μ).val) % (scaleUp ell k Lu μ + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem scaleUp_length {Lu : PeriodicLatticeExtent} (ell k : ℕ)
    (hs : 0 < ell ^ k) (μ : Fin 3) :
    scaleUp ell k Lu μ + 1 = (Lu μ + 1) * ell ^ k := by
  unfold scaleUp
  have hp : 0 < (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) hs
  omega

theorem unitEmb_val {Lu : PeriodicLatticeExtent} (ell k : ℕ) (hs : 0 < ell ^ k)
    (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    (unitEmb ell k y μ).val = ell ^ k * (y μ).val := by
  change (ell ^ k * (y μ).val) % (scaleUp ell k Lu μ + 1) = _
  apply Nat.mod_eq_of_lt
  rw [scaleUp_length ell k hs, Nat.mul_comm (Lu μ + 1)]
  exact Nat.mul_lt_mul_of_pos_left (y μ).isLt hs

-- Local arithmetic helper: no extra project imports are needed.
theorem pcd_scale (N s a b : ℕ) (hs : 0 < s) :
    pcd (N * s) (s * a) (s * b) = s * pcd N a b := by
  unfold pcd
  rcases le_total a b with h | h
  · have h' : s * a ≤ s * b := Nat.mul_le_mul_left s h
    rw [if_pos h, if_pos h', ← Nat.mul_sub, mul_comm N s,
      ← Nat.mul_sub, Nat.mul_min_mul_left]
  · by_cases hab : a = b
    · subst hab; simp
    · have hna : ¬ a ≤ b := by omega
      have hna' : ¬ s * a ≤ s * b := by
        intro hh
        exact hna (Nat.le_of_mul_le_mul_left hh hs)
      rw [if_neg hna, if_neg hna', ← Nat.mul_sub, mul_comm N s,
        ← Nat.mul_sub, Nat.mul_min_mul_left]

theorem pdist_emb_scales {Lu : PeriodicLatticeExtent} (ell k : ℕ) (hs : 0 < ell ^ k)
    (y z : PeriodicLatticeSite Lu) :
    pdist (unitEmb ell k y) (unitEmb ell k z) = ell ^ k * pdist y z := by
  unfold pdist
  simp_rw [unitEmb_val ell k hs, scaleUp_length ell k hs,
    pcd_scale _ _ _ _ hs]
  rw [Finset.mul_sum]

theorem lambda_collar_scale_iff {Lu : PeriodicLatticeExtent} (ell k M R : ℕ)
    (hs : 0 < ell ^ k) (y z : PeriodicLatticeSite Lu) :
    (R * M < pdist y z) ↔
      R * bigSide M ell k < pdist (unitEmb ell k y) (unitEmb ell k z) := by
  rw [pdist_emb_scales ell k hs]
  have he : R * bigSide M ell k = ell ^ k * (R * M) := by
    unfold bigSide
    ring
  rw [he]
  exact (Nat.mul_lt_mul_left hs).symm

theorem headline_fine_side_ge16 (ell M k : ℕ) (Lu : PeriodicLatticeExtent)
    (hell : 2 ≤ ell) (hk : 2 ≤ k) (hT : TorusOK ell M Lu) (μ : Fin 3) :
    16 ≤ scaleUp ell k Lu μ + 1 := by
  have hs : 0 < ell ^ k := pow_pos (by omega) _
  rw [scaleUp_length ell k hs]
  have hside : 4 ≤ Lu μ + 1 := by
    obtain ⟨t, ht⟩ := hT.1 μ
    have hstrict := hT.2.1 μ
    have ht2 : 2 ≤ t := by
      by_contra hn
      have : t = 0 ∨ t = 1 := by omega
      rcases this with h | h <;> simp [h] at ht <;> omega
    nlinarith
  have hp : 4 ≤ ell ^ k := by
    have hpow : ell ^ 2 ≤ ell ^ k := pow_le_pow_right' (by omega) hk
    nlinarith
  nlinarith

end AdalyFormal.Fidelity.SheetVariants

#print axioms AdalyFormal.Fidelity.SheetVariants.scaleUp_length
#print axioms AdalyFormal.Fidelity.SheetVariants.unitEmb_val
#print axioms AdalyFormal.Fidelity.SheetVariants.pcd_scale
#print axioms AdalyFormal.Fidelity.SheetVariants.pdist_emb_scales
#print axioms AdalyFormal.Fidelity.SheetVariants.lambda_collar_scale_iff
#print axioms AdalyFormal.Fidelity.SheetVariants.headline_fine_side_ge16

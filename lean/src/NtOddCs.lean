import NtCvOF14

/-!
# NsOddCs -- the first crossing of the Z-chain form satisfies `cs ≥ -1/14` for `ell ≥ 3` (lane ncwdh_strong_20261017)

The layer row has length `k + 3 = ell²`.  The vector `e1vec` supported on the layer row has `q_c(e1vec) = locEnergy (k+2) c`, which is NEGATIVE at
`c = cLoc (k+2) = -6/((k+1)(k+6))`.  `IsCrossingN` says `q_c` is positive definite on `Vsub` for every `c ∈ (cs, 1]`; hence `cs ≥ cLoc (k+2)`,
and `(k+1)(k+6) = (ell²-2)(ell²+3) ≥ 7·12 = 84` gives `cs ≥ -1/14`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi

theorem qF_zero_vec {n : ℕ} (C : ℕ) (c : ℝ) : qF C c (0 : Fin n → ℝ) = 0 := by
  simp [qF, AdalyFormal.CoverJacobi.aF, AdalyFormal.CoverJacobi.bF, dlt, ex]

theorem qF_e1vec' {n : ℕ} (K k r : ℕ) (hn : n = (K + 1) + (k + 3) + r) (c : ℝ) :
    qF (K + 1) c (e1vec (K + 1) (k + 3) n) = locEnergy (k + 2) c := by
  subst hn
  exact qF_e1vec K k r c

/-- **`cs ≥ -1/14`** for the first crossing of the nested instance's Z-chain form (`ell ≥ 3`). -/
theorem crossing_lower {ell M R : ℕ} (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hMe : ell + 1 ≤ M)
    {cs : ℝ} (h : IsCrossingN ell M R cs) : -(1 / 14 : ℝ) ≤ cs := by
  have hg := nGeo hell3 hdvd hM hR
  obtain ⟨i0, i1, K, k, r, hi0a, hi0b, hst, hln, hn, hC, -, -, -, -, hk⟩ := nested_chain_data hg hMe
  have G := nested_rowGeom hg
  have hRM : 1 ≤ R * M := Nat.mul_pos hR hM
  have hi0R : i0 < RN hg := by omega
  have hCK : neC ell M R - neP0 ell M R = K + 1 := by omega
  have hmem := e1vec_memD G hi0R hst hln hn
  obtain ⟨-, -, -, hpos⟩ := h
  rw [hCK] at hpos
  have hcl : cLoc (k + 2) ≤ cs := by
    by_contra hlt
    push Not at hlt
    have hneg := locEnergy_neg k
    have hq := qF_e1vec' (n := nN ell M R) K k r hn (cLoc (k + 2))
    have hne : e1vec (K + 1) (k + 3) (nN ell M R) ≠ 0 := by
      intro h0
      rw [h0, qF_zero_vec] at hq
      linarith
    have := hpos (cLoc (k + 2)) hlt (le_of_lt (lt_trans (cLoc_neg k) one_pos)) _ hmem hne
    rw [hq] at this
    linarith
  have hell9 : 9 ≤ ell ^ 2 := by nlinarith
  have hk22 : (6 : ℝ) ≤ (k : ℝ) := by
    have : 6 ≤ k := by omega
    exact_mod_cast this
  have hc : cLoc (k + 2) = -6 / (((k : ℝ) + 1) * ((k : ℝ) + 6)) := by
    unfold cLoc; push_cast
    rw [show ((k : ℝ) + 2 - 1) = (k : ℝ) + 1 by ring, show ((k : ℝ) + 2 + 4) = (k : ℝ) + 6 by ring]
  have hA : (84 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 6) := by nlinarith
  have hApos : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 6) := by linarith
  have hbd : -(1 / 14 : ℝ) ≤ -6 / (((k : ℝ) + 1) * ((k : ℝ) + 6)) := by
    rw [le_div_iff₀ hApos]
    nlinarith
  rw [hc] at hcl
  linarith

#print axioms crossing_lower

end AdalyFormal.CoverOmega

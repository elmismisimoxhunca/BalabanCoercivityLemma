import NsCvOI3
import NsCvOH5

/-!
# CvOI4 -- the slice Euler-Lagrange identity (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open Finset
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.StatementLane (scaleUp)

variable {ell M R : ℕ}

theorem ne_P0_pos (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : 1 ≤ neP0 ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  simp only [neP0, neP1, neA']; omega

theorem ne_Q0_lt_N (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neQ0 ell M R + 1 ≤ neN ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  simp only [neQ0, neQ1, neB, neN]; omega

theorem zprof_eq_BF (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ)
    (e : Fin (nN ell M R) → ℝ) (x : Fin (nN ell M R)) :
    zprof (scaleUp ell 2 (neLu M R) 0) (omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0) (neC ell M R) t)
        (fe (neP0 ell M R) e) (neP0 ell M R + x.val) =
      BF (neC ell M R - neP0 ell M R) (Real.cos t) e (Pi.single x 1) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  set N := scaleUp ell 2 (neLu M R) 0 with hNdef
  have hN1 : N + 1 = neN ell M R := ne_scaleUp hell hM 0
  have hQN : neQ0 ell M R ≤ N := by have := ne_Q0_lt_N hell3 hM hR; omega
  have hP0 := ne_P0_pos hell3 hM hR
  have hn' : nN ell M R = neQ0 ell M R - neP0 ell M R := rfl
  have hC1 : 1 ≤ neC ell M R - neP0 ell M R := by
    have := layer_lo hg; have := hg.hP0P1; have := hg.hP1A; omega
  have hC2 : neC ell M R - neP0 ell M R + 1 < (nN ell M R) := by
    have := layer_hi hg; have := hg.hB'A; have := hg.hAB; have := hg.hBQ1; have := hg.hQ1Q0
    have : 4 ≤ ell ^ 2 := by nlinarith
    omega
  rw [BF_single _ _ hC1 hC2 e x]
  set v := neP0 ell M R + x.val with hv
  have hxn : x.val < (nN ell M R) := x.2
  have hvQ : v < neQ0 ell M R := by omega
  have hv0 : v ≠ 0 := by omega
  have hvN : v ≠ N := by omega
  unfold zprof Wa
  have hprv : prv N v = v - 1 := by unfold prv; rw [if_neg hv0]
  have hnxt : nxt N v = v + 1 := by unfold nxt; rw [if_neg hvN]
  have hnxt' : nxt N (v - 1) = v := by unfold nxt; rw [if_neg (by omega)]; omega
  rw [hprv, hnxt', hnxt]
  -- the two terms
  have hnxe : ∀ k : ℕ, k < (nN ell M R) → nx e (k : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + k) := by
    intro k hk
    rw [nx_nat e k hk]
    exact (fe_at (neP0 ell M R) e ⟨k, hk⟩).symm
  -- right term
  have hR2 : omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t v *
      (fe (neP0 ell M R) e (v + 1) - fe (neP0 ell M R) e v) =
      AdalyFormal.CoverJacobi.Wt (neC ell M R - neP0 ell M R) (Real.cos t) (x.val : ℤ) * (nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ)) := by
    by_cases hx1 : x.val + 1 < (nN ell M R)
    · rw [hv, omegaW_edge hg t hQN x.val hx1]
      have h1 : nx e ((x.val : ℤ) + 1) = fe (neP0 ell M R) e (neP0 ell M R + x.val + 1) := by
        have := hnxe (x.val + 1) hx1
        push_cast at this; rw [this]; congr 1
      have h2 : nx e (x.val : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + x.val) := hnxe x.val hxn
      rw [h1, h2]
    · have hx2 : x.val + 1 = (nN ell M R) := by omega
      have hoff : omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t v = 0 :=
        omegaW_off hg t hQN (Or.inr (by omega)) hvN
      rw [hoff, zero_mul]
      have : nx e ((x.val : ℤ) + 1) - nx e (x.val : ℤ) = 0 := by
        have e1 : (x.val : ℤ) + 1 = ((nN ell M R) : ℤ) := by omega
        have e2 : (x.val : ℤ) = ((nN ell M R) : ℤ) - 1 := by omega
        rw [e1, nx_n e (by omega), ← e2]; ring
      rw [this, mul_zero]
  -- left term
  have hL2 : omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t (v - 1) *
      (fe (neP0 ell M R) e v - fe (neP0 ell M R) e (v - 1)) =
      AdalyFormal.CoverJacobi.Wt (neC ell M R - neP0 ell M R) (Real.cos t) ((x.val : ℤ) - 1) * (nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1)) := by
    by_cases hx0 : x.val = 0
    · have hoff : omegaW (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) N (neC ell M R) t (v - 1) = 0 :=
        omegaW_off hg t hQN (Or.inl (by omega)) (by omega)
      rw [hoff, zero_mul]
      have : nx e (x.val : ℤ) - nx e ((x.val : ℤ) - 1) = 0 := by
        rw [hx0]
        have := nx_neg_one e (by omega : 0 < (nN ell M R))
        simp only [Nat.cast_zero, zero_sub]
        rw [this]; ring
      rw [this, mul_zero]
    · have hy : x.val - 1 + 1 < (nN ell M R) := by omega
      have hvv : v - 1 = neP0 ell M R + (x.val - 1) := by omega
      rw [hvv, omegaW_edge hg t hQN (x.val - 1) hy]
      have e1 : (((x.val - 1 : ℕ)) : ℤ) = (x.val : ℤ) - 1 := by omega
      rw [e1]
      have h1 : nx e (x.val : ℤ) = fe (neP0 ell M R) e (neP0 ell M R + x.val) := hnxe x.val hxn
      have h2 : nx e ((x.val : ℤ) - 1) = fe (neP0 ell M R) e (neP0 ell M R + (x.val - 1)) := by
        have := hnxe (x.val - 1) (by omega)
        rw [← this]; congr 1; omega
      rw [h1, h2, ← hv]
  rw [hL2, hR2]

#print axioms zprof_eq_BF

end AdalyFormal.CoverOmega

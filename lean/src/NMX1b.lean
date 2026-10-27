import NMX1

/-!
# NMX1b -- widths and coverage on the mixed layout (lane nonvac_mixed_20261017)

`mx_widths`: the window-width inequalities that `slab3_coversp` needs, for a cube factor `f ≤ w = R + ell q` (and `f ≤ T`).
`mx_covers`: a cube factor `f` with `2 ≤ f ≤ w` covers `Ω₀` (sites and plaquettes) alone.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.NonVacMix

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.NonVacC

section cov
variable {ell M R T q : ℕ}

theorem mx_widths (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) {f : ℕ} (hfw : f ≤ R + ell * q) :
    mxP0 ell M R q + f * M ≤ mxP2 ell M R q ∧ nvcQ2 ell M T + f * M ≤ nvcQ0 ell M R T ∧
      mxP1 ell M R q + f * (M * ell) ≤ nvcQ1 ell M T ∧ mxP2 ell M R q + f * (M * ell ^ 2) ≤ nvcQ2 ell M T ∧
      nvcQ0 ell M R T < nvcN ell M T ∧ mxP1 ell M R q < mxP2 ell M R q ∧ nvcQ2 ell M T < nvcQ1 ell M T ∧
      nvcQ1 ell M T < nvcQ0 ell M R T := by
  have hRT : R ≤ T := by nlinarith
  have hfT : f ≤ T := le_trans hfw hwT
  obtain ⟨d, t, hd, hdd, ht, hdt, hw2, hRw⟩ := mx_left_facts hell hR hq
  obtain ⟨-, w2, w3, w4, w5, -, w7, w8⟩ := nvc_widths (c := f) hell hM hR hRT hT (by omega)
  have e2 : M * ell ^ 2 * (R + ell * q) = M * ((d + 1) * (R + ell * q)) := by rw [← hd]; ring
  have hee : 0 < ell ^ 2 := pow_pos (by omega) 2
  have hP12 : mxP1 ell M R q < mxP2 ell M R q := by
    simp only [mxP1, mxP2, hdd]; rw [e2]; exact Nat.mul_lt_mul_of_pos_left (by nlinarith) hM
  have hP2le : mxP2 ell M R q ≤ M * ell ^ 2 * (2 * T) := by
    simp only [mxP2]; exact Nat.mul_le_mul_left _ (by omega)
  have hP1le : mxP1 ell M R q ≤ M * ell ^ 2 * T := by
    have h1 : mxP1 ell M R q ≤ mxP2 ell M R q := hP12.le
    have h2 : mxP2 ell M R q ≤ M * ell ^ 2 * T := by
      simp only [mxP2]; exact Nat.mul_le_mul_left _ hwT
    omega
  refine ⟨?_, w2, ?_, ?_, w5, hP12, w7, w8⟩
  · simp only [mxP0, mxP2, hdd]; rw [e2]
    have := Nat.mul_le_mul_left M (Nat.mul_le_mul_right f hfw |>.trans (le_refl _))
    have h3 : M * (f) ≤ M * (R + ell * q) := Nat.mul_le_mul_left M hfw
    nlinarith
  · have : nvcP1 ell M T = M * ell ^ 2 * T := rfl
    omega
  · have : nvcP2 ell M T = M * ell ^ 2 * (2 * T) := rfl
    omega

theorem mx_covers (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (hq : R ≤ q) (hT : 1 ≤ T)
    (hwT : R + ell * q ≤ T) {f : ℕ} (hf2 : 2 ≤ f) (hfw : f ≤ R + ell * q)
    {L : PeriodicLatticeExtent} (hN : ∀ μ, L μ + 1 = nvcN ell M T) :
    CoversOm0p ell M f 2 (mxS L ell M R T q) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := mx_widths hell hM hR hq hT hwT hfw
  exact slab3_coversp hf2 (slabGeo_mix hell hdvd hM hR hq hT hwT) w1 w2 w3 w4 w5 w6 w7 w8 hN

end cov

end AdalyFormal.NonVacMix

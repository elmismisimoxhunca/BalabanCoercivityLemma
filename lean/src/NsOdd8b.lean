import NsOdd8a

/-!
# NsOdd8b -- aligned amplitudes: on the sublattice `ell ℤ³` the first blocked level `phi1o` has its INTERIOR values (lane ncwdh_strong_20261017)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix
open AdalyFormal.Target.ClayStatement

variable {L : PeriodicLatticeExtent}

/-- geometry hypotheses of the odd family. -/
structure OddGeo (L : PeriodicLatticeExtent) (ell c : ℕ) : Prop where
  hN : 2 ∣ L 1 + 1
  hO : ell % 2 = 1
  h5 : 5 ≤ ell
  hdiv : ∀ μ : Fin 3, ell * ell ∣ L μ + 1
  hbig : ell * ell + ell < L 1 + 1
  hc1 : ell ≤ c
  hc2 : c + ell ≤ L 0 + 1
  hc3 : c + ell * ell < L 0 + 1
  hcd : ell * ell ∣ c

/-- interior values -/
noncomputable def aInt (ell : ℕ) : ℝ := ((ell : ℝ) - 1) / (2 * ell)
noncomputable def pInt (ell : ℕ) : ℝ := 1 / (ell : ℝ) ^ 2

theorem dvd_mod_pos {N A k ell : ℕ} (hN : ell ∣ N) (hA : ell ∣ A) : ell ∣ (A + ell * k) % N :=
  (Nat.dvd_mod_iff hN).mpr (dvd_add hA (dvd_mul_right ell k))

theorem cnt_al {ell N z : ℕ} (hN : ell ∣ N) (hz : ell ∣ z) (hzN : z < N) : min ell (N - z) = ell := by
  obtain ⟨a, ha⟩ := hz
  obtain ⟨b, hb⟩ := hN
  have hab : a < b := by
    by_contra hc
    push Not at hc
    have : ell * b ≤ ell * a := Nat.mul_le_mul_left ell hc
    omega
  have : ell * (a + 1) ≤ ell * b := Nat.mul_le_mul_left ell hab
  rw [Nat.mul_add] at this
  omega

theorem aAmp_al {ell : ℕ} (hO : ell % 2 = 1) (hell : 0 < ell) (hd1 : ell ∣ L 1 + 1) (hd2 : ell ∣ L 2 + 1) {z1 z2 : ℕ}
    (h1 : ell ∣ z1) (h2 : ell ∣ z2) (hz1 : z1 < L 1 + 1) (hz2 : z2 < L 2 + 1) : aAmp L ell z1 z2 = aInt ell := by
  unfold aAmp aInt
  rw [cnt_al hd1 h1 hz1, cnt_al hd2 h2 hz2]
  have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have h4 : (2 : ℕ) * (ell / 2) = ell - 1 := by omega
  have h5 : ((ell / 2 : ℕ) : ℝ) = ((ell : ℝ) - 1) / 2 := by
    have : (2 : ℝ) * ((ell / 2 : ℕ) : ℝ) = (ell : ℝ) - 1 := by
      have h6 : ((2 * (ell / 2) : ℕ) : ℝ) = ((ell - 1 : ℕ) : ℝ) := by rw [h4]
      push_cast at h6
      rw [h6]; push_cast [Nat.cast_sub hell]; ring
    linarith
  push_cast
  rw [h5]
  field_simp

theorem pAmp_al {ell : ℕ} (hO : ell % 2 = 1) (hell : 0 < ell) (hd1 : ell ∣ L 1 + 1) (hd2 : ell ∣ L 2 + 1) {z1 z2 : ℕ}
    (h1 : ell ∣ z1) (h2 : ell ∣ z2) (hz1 : z1 < L 1 + 1) (hz2 : z2 < L 2 + 1) : pAmp L ell z1 z2 = pInt ell := by
  unfold pAmp pInt
  rw [cnt_al hd1 h1 hz1, cnt_al hd2 h2 hz2, hO]
  have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  push_cast
  field_simp

/-- `Efun` at an `ell`-aligned site (for an `ell`-aligned layer). -/
theorem Efun_al {c ell v : ℕ} (hell : 0 < ell) (hv : ell ∣ v) (hc : ell ∣ c) :
    Efun c ell v = if v = c then 1 - (ell : ℝ) else 0 := by
  unfold Efun
  by_cases h : v = c
  · subst h; simp [hell]
  · have : ¬ (c < v + ell ∧ v ≤ c) := by
      rintro ⟨h1, h2⟩
      obtain ⟨a, ha⟩ := hv
      obtain ⟨b, hb⟩ := hc
      have hab : a < b := by
        by_contra hh; push Not at hh
        have := Nat.mul_le_mul_left ell hh
        omega
      have : ell * (a + 1) ≤ ell * b := Nat.mul_le_mul_left ell hab
      rw [Nat.mul_add] at this
      omega
    simp [h, this]

#print axioms aAmp_al
#print axioms pAmp_al
#print axioms Efun_al

end AdalyFormal.CoverOmega

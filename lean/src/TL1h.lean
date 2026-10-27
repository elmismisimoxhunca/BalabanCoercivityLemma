import TL1g

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem off_lt (m z x : ℕ) (hm : 0 < m) : off m z x < m := Nat.mod_lt _ hm

theorem off_spec (m z x : ℕ) (hm : 0 < m) (hz : z < m) : (z + off m z x) % m = x % m := by
  unfold off
  have h1 : Nat.ModEq m (z + (x + m - z) % m) (z + (x + m - z)) :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
  have h2 : z + (x + m - z) = x + m := by omega
  have h3 : Nat.ModEq m (x + m) x := by
    have : Nat.ModEq m m 0 := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    simpa using (Nat.ModEq.add_left x this)
  rw [h2] at h1
  exact (h1.trans h3)

theorem off_unique (m z x t : ℕ) (hm : 0 < m) (hz : z < m) (ht : t < m) (h : (z + t) % m = x % m) :
    off m z x = t := by
  have h1 := off_spec m z x hm hz
  have h2 : Nat.ModEq m (z + off m z x) (z + t) := by
    unfold Nat.ModEq; rw [h1, h]
  have h3 := Nat.ModEq.add_left_cancel' z h2
  exact (Nat.ModEq.eq_of_lt_of_lt h3 (off_lt m z x hm) ht)

theorem corner_nat (b m N s x z : ℕ) (hb : 0 < b) (hbm : b ∣ m) (hmN : m ∣ N) (hbN : b < N) (hbs : b < s)
    (hm : 0 < m) (hz : z < m) (hzb : z % b = 0) (hx : x < N) (p : ℕ)
    (hin0 : off m z (x % m) < s) (hin1 : p = 1 → off m z ((x + 1) % m) < s) :
    ∃ w, w < N ∧ w % b = 0 ∧ (w % m = z ∨ m ≤ s) ∧ off N w x < s ∧
      (p = 1 → off N w ((x + 1) % N) < s) := by
  have hN : 0 < N := by omega
  obtain ⟨t, hmt⟩ := hmN
  by_cases hms : m ≤ s
  · -- full circle: take the grid base of `x`
    have hrb : x % b < b := Nat.mod_lt _ hb
    have hxd := Nat.div_add_mod x b
    refine ⟨x - x % b, by omega, ?_, Or.inr hms, ?_, fun hp => ?_⟩
    · have : x - x % b = b * (x / b) := by omega
      rw [this]; exact Nat.mul_mod_right _ _
    · rw [off_unique N (x - x % b) x (x % b) hN (by omega) (by omega) (by rw [show x - x % b + x % b = x by omega])]
      omega
    · rw [off_unique N (x - x % b) ((x + 1) % N) (x % b + 1) hN (by omega) (by omega)
        (by
          rw [Nat.mod_mod, show x - x % b + (x % b + 1) = x + 1 by omega])]
      omega
  · push Not at hms
    set d := off m z (x % m) with hd
    have hdm : d < m := off_lt m z _ hm
    have hmleN : m ≤ N := Nat.le_of_dvd hN ⟨t, hmt⟩
    have hdN : d < N := lt_of_lt_of_le hdm hmleN
    have hzd : (z + d) % m = x % m := by
      have := off_spec m z (x % m) hm hz
      rw [Nat.mod_mod] at this; exact this
    -- the lift
    have hex : ∃ w, w < N ∧ (w + d = x ∨ w + d = x + N) := by
      by_cases hdx : d ≤ x
      · exact ⟨x - d, by omega, Or.inl (by omega)⟩
      · exact ⟨x + N - d, by omega, Or.inr (by omega)⟩
    obtain ⟨w, hwN, hw⟩ := hex
    have hwm : (w + d) % m = x % m := by
      rcases hw with h | h
      · rw [h]
      · rw [h, hmt, Nat.add_mul_mod_self_left]
    have hwz : w % m = z := by
      have h1 : Nat.ModEq m (w + d) (z + d) := by unfold Nat.ModEq; rw [hwm, hzd]
      have h2 := Nat.ModEq.add_right_cancel' d h1
      unfold Nat.ModEq at h2
      rw [h2, Nat.mod_eq_of_lt hz]
    have hwN' : (w + d) % N = x % N := by
      rcases hw with h | h
      · rw [h]
      · rw [h, Nat.add_mod_right]
    refine ⟨w, hwN, ?_, Or.inl hwz, ?_, fun hp => ?_⟩
    · rw [← Nat.mod_mod_of_dvd w hbm, hwz, hzb]
    · rw [off_unique N w x d hN hwN hdN hwN']; exact hin0
    · have h1 := hin1 hp
      have hd1 : off m z ((x + 1) % m) = d + 1 := by
        apply off_unique m z _ (d + 1) hm hz (by omega)
        rw [Nat.mod_mod, ← Nat.add_assoc, ← Nat.mod_add_mod, hzd, Nat.mod_add_mod]
      rw [hd1] at h1
      rw [off_unique N w ((x + 1) % N) (d + 1) hN hwN (by omega : d + 1 < N)]
      · exact h1
      · rw [Nat.mod_mod, ← Nat.add_assoc, ← Nat.mod_add_mod, hwN', Nat.mod_add_mod]

end AdalyFormal.Thin

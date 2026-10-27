import TL1f

set_option autoImplicit false
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

/-- offset of `x` from `z` on `ℤ/m` -/
def off (m z x : ℕ) : ℕ := (x + m - z) % m

theorem off_proj (m N x z : ℕ) (hm : 0 < m) (hmN : m ∣ N) (hx : x < N) (hz : z < N) :
    off m (z % m) (x % m) = off N z x % m := by
  unfold off
  obtain ⟨t, rfl⟩ := hmN
  have h1 : (x + m * t - z) % (m * t) % m = (x + m * t - z) % m := Nat.mod_mod_of_dvd _ (Dvd.intro t rfl)
  rw [h1]
  have hxm := Nat.mod_lt x hm
  have hzm := Nat.mod_lt z hm
  have e1 : (x % m + m - z % m) + z % m = x % m + m := by omega
  have e2 : (x + m * t - z) + z = x + m * t := by omega
  have hmod : Nat.ModEq m ((x % m + m - z % m) + z % m) ((x + m * t - z) + z % m) := by
    calc (x % m + m - z % m) + z % m = x % m + m := e1
      _ ≡ x % m + 0 [MOD m] := by
          apply Nat.ModEq.add_left; exact (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)
      _ = x % m := by simp
      _ ≡ x [MOD m] := Nat.mod_modEq x m
      _ ≡ x + m * t [MOD m] := by
          have : Nat.ModEq m (m * t) 0 := Nat.modEq_zero_iff_dvd.mpr (Dvd.intro t rfl)
          simpa using (Nat.ModEq.add_left x this).symm
      _ = (x + m * t - z) + z := e2.symm
      _ ≡ (x + m * t - z) + z % m [MOD m] := Nat.ModEq.add_left _ (Nat.mod_modEq z m).symm
  have := Nat.ModEq.add_right_cancel' (z % m) hmod
  exact this

theorem lift_off (N m a y t : ℕ) (hmN : m ∣ N) (ha : a < N) (ht : t < N) (hmod : (a % m + t) % m = y) :
    ∃ b, b < N ∧ b % m = y ∧ (b + N - a) % N = t := by
  by_cases hlt : a + t < N
  · refine ⟨a + t, hlt, ?_, ?_⟩
    · rw [← hmod, Nat.mod_add_mod]
    · rw [show a + t + N - a = t + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · refine ⟨a + t - N, by omega, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hmN
      have : a + t - N = (a + t) - m * s := by rw [hs]
      rw [this, Nat.sub_mul_mod (by rw [← hs]; omega), ← hmod, Nat.mod_add_mod]
    · rw [show a + t - N + N - a = t by omega, Nat.mod_eq_of_lt ht]

theorem mem_siteBox_iff {L : PeriodicLatticeExtent} (z x : PeriodicLatticeSite L) (s : ℕ) :
    x ∈ siteBox z s ↔ ∀ μ : Fin 3, off (L μ + 1) (z μ).val (x μ).val < s := Iff.rfl

theorem box_proj_subset {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (z x : PeriodicLatticeSite Lt) (s : ℕ)
    (hx : x ∈ siteBox z s) : projS h x ∈ siteBox (projS h z) s := by
  intro μ
  have := off_proj (L μ + 1) (Lt μ + 1) (x μ).val (z μ).val (Nat.succ_pos _) (h μ) (x μ).isLt (z μ).isLt
  show off (L μ + 1) ((z μ).val % (L μ + 1)) ((x μ).val % (L μ + 1)) < s
  rw [this]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (hx μ)

theorem box_proj_surj {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (z : PeriodicLatticeSite Lt)
    (y : PeriodicLatticeSite L) (s : ℕ) (hy : y ∈ siteBox (projS h z) s) :
    ∃ x ∈ siteBox z s, projS h x = y := by
  have key : ∀ μ : Fin 3, ∃ b : Fin (Lt μ + 1), b.val % (L μ + 1) = (y μ).val ∧
      off (Lt μ + 1) (z μ).val b.val < s := by
    intro μ
    have hm : 0 < L μ + 1 := Nat.succ_pos _
    set m := L μ + 1 with hmdef
    set d := ((y μ).val + m - (z μ).val % m) % m with hd
    have hdlt : d < m := Nat.mod_lt _ hm
    have hmN : m ∣ Lt μ + 1 := h μ
    have hmle : m ≤ Lt μ + 1 := Nat.le_of_dvd (Nat.succ_pos _) hmN
    have hyd : ((z μ).val % m + d) % m = (y μ).val := by
      have hc := Nat.mod_lt (z μ).val hm
      rw [hd, Nat.add_mod_mod, show (z μ).val % m + ((y μ).val + m - (z μ).val % m) = (y μ).val + m by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (y μ).isLt]
    obtain ⟨b, hb1, hb2, hb3⟩ := lift_off (Lt μ + 1) m (z μ).val (y μ).val d hmN (z μ).isLt (by omega) hyd
    refine ⟨⟨b, hb1⟩, hb2, ?_⟩
    show (b + (Lt μ + 1) - (z μ).val) % (Lt μ + 1) < s
    rw [hb3]
    have := hy μ
    show d < s
    exact this
  choose w hw1 hw2 using key
  refine ⟨w, hw2, ?_⟩
  funext μ; exact Fin.ext (by simp only [projS_val]; exact hw1 μ)

end AdalyFormal.Thin

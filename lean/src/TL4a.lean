import TL3c

/-!
# TL4a -- deck translations on a coordinate: 1D arithmetic
-/
set_option autoImplicit false
namespace AdalyFormal.Thin

theorem tau_decomp (x m n d : ℕ) (hm : 0 < m) (hx : x < m * n) :
    (x + d * m) % (m * n) = x % m + m * (((x / m) + d) % n) := by
  have h1 : x + d * m = x % m + m * (x / m + d) := by
    have := Nat.mod_add_div x m
    nlinarith
  rw [h1, Nat.mod_mul]
  have h2 : (x % m + m * (x / m + d)) % m = x % m := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  have h3 : (x % m + m * (x / m + d)) / m % n = (x / m + d) % n := by
    rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (Nat.mod_lt _ hm), zero_add]
  rw [h2, h3]

theorem tau_lt (x m n d : ℕ) (hm : 0 < m) (hn : 0 < n) (hx : x < m * n) : (x + d * m) % (m * n) < m * n :=
  Nat.mod_lt _ (Nat.mul_pos hm hn)

theorem tau_free (x y m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hx : x < m * n) (hy : y < m * n) (hxy : x % m = y % m) :
    ∃ d, d < n ∧ (x + d * m) % (m * n) = y := by
  refine ⟨((y / m) + n - (x / m)) % n, Nat.mod_lt _ hn, ?_⟩
  rw [tau_decomp x m n _ hm hx]
  have hxq : x / m < n := (Nat.div_lt_iff_lt_mul hm).mpr (by linarith [Nat.mul_comm m n])
  have hyq : y / m < n := (Nat.div_lt_iff_lt_mul hm).mpr (by linarith [Nat.mul_comm m n])
  have : (x / m + (y / m + n - x / m) % n) % n = y / m := by
    generalize x / m = a at *
    generalize y / m = b at *
    rw [Nat.add_mod_mod, show a + (b + n - a) = b + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hyq]
  rw [this, hxy]
  have := Nat.mod_add_div y m
  linarith

theorem tau_unique (x m n d d' : ℕ) (hm : 0 < m) (hx : x < m * n) (hd : d < n) (hd' : d' < n)
    (h : (x + d * m) % (m * n) = (x + d' * m) % (m * n)) : d = d' := by
  rw [tau_decomp x m n d hm hx, tau_decomp x m n d' hm hx] at h
  have h1 : m * ((x / m + d) % n) = m * ((x / m + d') % n) := by omega
  have h2 := Nat.eq_of_mul_eq_mul_left hm h1
  have hxq : x / m < n := (Nat.div_lt_iff_lt_mul hm).mpr (by linarith [Nat.mul_comm m n])
  have h3 : Nat.ModEq n (x / m + d) (x / m + d') := h2
  have h4 := Nat.ModEq.add_left_cancel' (x / m) h3
  exact Nat.ModEq.eq_of_lt_of_lt h4 hd hd'

theorem tau_inv_left (x m n d : ℕ) (hm : 0 < m) (hn : 0 < n) (hx : x < m * n) (hd : d ≤ n) :
    ((x + d * m) % (m * n) + (n - d) * m) % (m * n) = x := by
  rw [Nat.mod_add_mod, show x + d * m + (n - d) * m = x + m * n by
    have : d * m + (n - d) * m = n * m := by rw [← Nat.add_mul, Nat.add_sub_cancel' hd]
    nlinarith [Nat.mul_comm n m], Nat.add_mod_right, Nat.mod_eq_of_lt hx]

theorem tau_inv_left' (x N m n d : ℕ) (hN : m * n = N) (hm : 0 < m) (hn : 0 < n) (hx : x < N) (hd : d ≤ n) :
    ((x + d * m) % N + (n - d) * m) % N = x := by
  subst hN; exact tau_inv_left x m n d hm hn hx hd

theorem tau_free' (x y N m n : ℕ) (hN : m * n = N) (hm : 0 < m) (hn : 0 < n) (hx : x < N) (hy : y < N)
    (hxy : x % m = y % m) : ∃ d, d < n ∧ (x + d * m) % N = y := by
  subst hN; exact tau_free x y m n hm hn hx hy hxy

theorem tau_unique' (x N m n d d' : ℕ) (hN : m * n = N) (hm : 0 < m) (hx : x < N) (hd : d < n) (hd' : d' < n)
    (h : (x + d * m) % N = (x + d' * m) % N) : d = d' := by
  subst hN; exact tau_unique x m n d d' hm hx hd hd' h

end AdalyFormal.Thin

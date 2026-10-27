import GV1
import M2B8

/-!
# GE1 -- block arithmetic for the class-cube cover geometry (m2_gluegeo, 2026-10-15)

* `iota_val_int`, `iota_val_div`: for a vertex `v` on the `s`-grid (`v_mu % s = 0`, `s | L_mu + 1`), the block coordinate
  `(iota v p mu).val / s` depends only on `p_mu / s` (floor division in `Z`).  No non-wrap hypothesis.
* `siteBox_blockClosed`: a periodic box `siteBox z side` with `s | z_mu`, `s | side`, `s | L_mu+1` is a union of `s`-blocks.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2GlueGeo

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open Fin.CommRing

variable {L : PeriodicLatticeExtent}


theorem iota_val_int (v : PeriodicLatticeSite L) (p : Z3) (μ : Fin 3) :
    ((iota v p μ).val : ℤ) = (((v μ).val : ℤ) + p μ) % ((L μ + 1 : ℕ) : ℤ) := by
  unfold iota
  rw [Fin.val_add, Fin.val_intCast]
  push_cast
  have hN : (0 : ℤ) < (L μ : ℤ) + 1 := by positivity
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')]
  exact Int.add_emod_emod _ _ _

theorem blk_formula (s n u p : ℤ) (hs : 0 < s) (hn : 0 < n) :
    (s * u + p) % (s * n) = s * ((u + p / s) % n) + p % s := by
  have hr0 : 0 ≤ p % s := Int.emod_nonneg _ hs.ne'
  have hr1 : p % s < s := Int.emod_lt_of_pos _ hs
  have h1 : s * u + p = s * (u + p / s) + p % s := by
    have := Int.mul_ediv_add_emod p s
    nlinarith
  have h2 : u + p / s = n * ((u + p / s) / n) + (u + p / s) % n := (Int.mul_ediv_add_emod _ _).symm
  have h3 : s * u + p = (s * ((u + p / s) % n) + p % s) + (s * n) * ((u + p / s) / n) := by
    rw [h1]; nth_rewrite 1 [h2]; ring
  rw [h3, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · exact add_nonneg (mul_nonneg hs.le (Int.emod_nonneg _ hn.ne')) hr0
  · have : (u + p / s) % n + 1 ≤ n := Int.emod_lt_of_pos _ hn
    nlinarith

theorem blk_div (s t r : ℤ) (hs : 0 < s) (hr0 : 0 ≤ r) (hr1 : r < s) : (s * t + r) / s = t := by
  rw [Int.mul_add_ediv_left _ _ hs.ne', Int.ediv_eq_zero_of_lt hr0 hr1]; ring

theorem nat_blk (s n A r : ℕ) (hs : 0 < s) (hn : 0 < n) (hr : r < s) :
    (s * A + r) % (s * n) = s * (A % n) + r := by
  have h2 : A = n * (A / n) + A % n := (Nat.div_add_mod A n).symm
  have h3 : s * A + r = (s * (A % n) + r) + (s * n) * (A / n) := by
    nth_rewrite 1 [h2]; ring
  rw [h3, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have : A % n + 1 ≤ n := Nat.mod_lt _ hn
  nlinarith

theorem iota_val_div (v : PeriodicLatticeSite L) (s : ℕ) (hs : 0 < s) (hv : ∀ μ, (v μ).val % s = 0)
    (hsN : ∀ μ, s ∣ L μ + 1) (p q : Z3) (h : ∀ μ, p μ / (s : ℤ) = q μ / (s : ℤ)) (μ : Fin 3) :
    (iota v p μ).val / s = (iota v q μ).val / s := by
  obtain ⟨n, hn⟩ := hsN μ
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hn; omega
    · exact h0
  obtain ⟨u, hu⟩ : ∃ u, (v μ).val = s * u := ⟨(v μ).val / s, by
    have := Nat.div_add_mod (v μ).val s; rw [hv μ] at this; omega⟩
  have key : ∀ r : Z3, (((iota v r μ).val / s : ℕ) : ℤ) = ((u : ℤ) + r μ / (s : ℤ)) % (n : ℤ) := by
    intro r
    have e := iota_val_int v r μ
    have hN : ((L μ + 1 : ℕ) : ℤ) = (s : ℤ) * (n : ℤ) := by exact_mod_cast hn
    rw [hu, hN] at e
    have hs' : (0 : ℤ) < s := by exact_mod_cast hs
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn0
    have e2 : (((iota v r μ).val : ℕ) : ℤ) = (s : ℤ) * (((u : ℤ) + r μ / (s : ℤ)) % (n : ℤ)) + r μ % (s : ℤ) := by
      rw [e]; push_cast
      exact blk_formula (s : ℤ) (n : ℤ) (u : ℤ) (r μ) hs' hn'
    have hr0 : 0 ≤ r μ % (s : ℤ) := Int.emod_nonneg _ hs'.ne'
    have hr1 : r μ % (s : ℤ) < s := Int.emod_lt_of_pos _ hs'
    rw [Int.natCast_div, e2]
    exact blk_div (s : ℤ) _ _ hs' hr0 hr1
  have a := key p
  have b := key q
  rw [h μ] at a
  exact_mod_cast a.trans b.symm

theorem box_coord (s n w t xv yv : ℕ) (hs : 0 < s) (hn : 0 < n) (hw : w < n) (hxy : xv / s = yv / s)
    (hx : (xv + s * n - s * w) % (s * n) < s * t) : (yv + s * n - s * w) % (s * n) < s * t := by
  obtain ⟨k, hk⟩ : ∃ k, n = w + k + 1 := ⟨n - w - 1, by omega⟩
  have hsn : s * n = s * w + s * (k + 1) := by rw [hk]; ring
  have hxe : xv = s * (xv / s) + xv % s := (Nat.div_add_mod xv s).symm
  have hye : yv = s * (yv / s) + yv % s := (Nat.div_add_mod yv s).symm
  have hxr : xv % s < s := Nat.mod_lt _ hs
  have hyr : yv % s < s := Nat.mod_lt _ hs
  set a := xv / s with ha
  have hya : yv / s = a := hxy.symm
  rw [hya] at hye
  have hm : s * (a + (k + 1)) = s * a + s * (k + 1) := mul_add _ _ _
  have e1 : xv + s * n - s * w = s * (a + (k + 1)) + xv % s := by
    rw [hsn, hm]; omega
  have e2 : yv + s * n - s * w = s * (a + (k + 1)) + yv % s := by
    rw [hsn, hm]; omega
  rw [e1, nat_blk s n _ _ hs hn hxr] at hx
  rw [e2, nat_blk s n _ _ hs hn hyr]
  have h1 : (a + (k + 1)) % n < t := by
    by_contra hc
    replace hc := not_lt.mp hc
    have : s * t ≤ s * ((a + (k + 1)) % n) := Nat.mul_le_mul_left s hc
    omega
  have : (a + (k + 1)) % n + 1 ≤ t := h1
  nlinarith

theorem box_coord' (s n w t N zv side xv yv : ℕ) (hs : 0 < s) (hn : 0 < n) (hw : w < n) (hN : N = s * n)
    (hz : zv = s * w) (hside : side = s * t) (hxy : xv / s = yv / s)
    (hx : (xv + N - zv) % N < side) : (yv + N - zv) % N < side := by
  subst hN hz hside
  exact box_coord s n w t xv yv hs hn hw hxy hx

/-- **a periodic box with grid-aligned corner and grid-multiple side is a union of `s`-blocks.** -/
theorem siteBox_blockClosed {s : ℕ} (hs : 0 < s) (hsN : ∀ μ, s ∣ L μ + 1) {z : PeriodicLatticeSite L}
    (hz : ∀ μ, (z μ).val % s = 0) {side : ℕ} (hside : s ∣ side) : BlockClosed s (siteBox z side) := by
  intro x hx y hxy μ
  have hxy' : (y μ).val / s = (x μ).val / s := hxy μ
  have hx' : ((x μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < side := hx μ
  show ((y μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) < side
  obtain ⟨n, hn⟩ := hsN μ
  obtain ⟨t, ht⟩ := hside
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hn; omega
    · exact h0
  obtain ⟨w, hw⟩ : ∃ w, (z μ).val = s * w := ⟨(z μ).val / s, by
    have := Nat.div_add_mod (z μ).val s; rw [hz μ] at this; omega⟩
  have hzl := (z μ).isLt
  have hwn : w < n := by
    have : s * w < s * n := by rw [← hw, ← hn]; exact hzl
    exact Nat.lt_of_mul_lt_mul_left this
  exact box_coord' s n w t _ _ _ _ _ hs hn0 hwn hn hw ht hxy'.symm hx'

end AdalyFormal.M2GlueGeo

import NuE4

/-!
# NuE5 -- positivity of the single-edge form at `c = 0`; hence the first crossing is negative (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega

section
variable {n R a b : ℕ} {st ln rowOf : ℕ → ℕ}

/-- at `c = 0` the form splits the chain at the layer edge, and the collar singletons kill both halves. -/
theorem qF1_zero_pos (g : RowGeomD n R a b st ln rowOf) (ha : 1 ≤ a) (hb : 1 ≤ b) (C : ℕ) (hC : C + 1 < n)
    {e : Fin n → ℝ} (he : e ∈ Vsub rowOf) (hne : e ≠ 0) : 0 < qF1 C 0 e := by
  by_contra hle
  push Not at hle
  have hn : 0 < n := by omega
  have hRpos : 0 < R := by
    by_contra hR0
    have hR0' : R = 0 := by omega
    have := g.stR
    rw [hR0', g.st0] at this
    omega
  -- all differences except at C vanish
  have hsum : ∑ y ∈ range (n - 1), (dlt e y) ^ 2 - (dlt e C) ^ 2 = ∑ y ∈ (range (n - 1)).erase C, (dlt e y) ^ 2 := by
    have hmem : C ∈ range (n - 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.sum_erase_add _ _ hmem]; ring
  have hq : qF1 C 0 e = ∑ y ∈ (range (n - 1)).erase C, (dlt e y) ^ 2 := by
    unfold qF1 aF bF1; rw [← hsum]; ring
  have hnn : 0 ≤ qF1 C 0 e := by rw [hq]; exact Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hz : qF1 C 0 e = 0 := le_antisymm hle hnn
  rw [hq] at hz
  have hd : ∀ y, y < n - 1 → y ≠ C → dlt e y = 0 := by
    intro y hy hyC
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (dlt e y))).mp hz y
      (Finset.mem_erase.mpr ⟨hyC, Finset.mem_range.mpr hy⟩)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  -- collars
  have h0 : ex e 0 = 0 := by
    have hl : ln 0 = 1 := g.lnL 0 (by omega)
    have hsum' := rowSum_of_memD g he hRpos
    unfold BlockSums at hsum'
    rw [hl] at hsum'
    simp only [Finset.sum_range_one, Nat.cast_zero, add_zero] at hsum'
    rw [g.st0] at hsum'
    simp only [Nat.cast_zero] at hsum'
    have hh := nx_nat e 0 hn
    simp only [Nat.cast_zero] at hh
    rw [hh] at hsum'
    unfold ex; rw [dif_pos hn]; exact hsum'
  have hlast : ex e (n - 1) = 0 := by
    have hiR : R - 1 < R := by omega
    have hl : ln (R - 1) = 1 := g.lnR (R - 1) (by omega) hiR
    have hs := g.stS (R - 1)
    rw [show R - 1 + 1 = R by omega, g.stR, hl] at hs
    have hsum' := rowSum_of_memD g he hiR
    unfold BlockSums at hsum'
    rw [hl] at hsum'
    simp only [Finset.sum_range_one, Nat.cast_zero, add_zero] at hsum'
    have : (st (R - 1) : ℤ) = ((n - 1 : ℕ) : ℤ) := by omega
    rw [this, nx_nat e (n - 1) (by omega)] at hsum'
    unfold ex; rw [dif_pos (by omega)]; exact hsum'
  -- constancy on both sides
  have hleft : ∀ k, k ≤ C → ex e k = ex e 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have := hd k (by omega) (by omega)
      unfold dlt at this
      have := ih (by omega)
      linarith [hd k (by omega) (by omega), show dlt e k = ex e (k + 1) - ex e k from rfl]
  have hright : ∀ d, C + 1 + d ≤ n - 1 → ex e (C + 1 + d) = ex e (C + 1) := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hk
      have h1 := hd (C + 1 + d) (by omega) (by omega)
      have h2 := ih (by omega)
      have h3 : dlt e (C + 1 + d) = ex e (C + 1 + d + 1) - ex e (C + 1 + d) := rfl
      rw [show C + 1 + (d + 1) = C + 1 + d + 1 by ring]
      linarith
  apply hne
  funext x
  have hx := x.2
  show e x = 0
  have hex : e x = ex e x.val := by unfold ex; rw [dif_pos hx]
  rw [hex]
  by_cases hxC : x.val ≤ C
  · rw [hleft x.val hxC, h0]
  · have := hright (x.val - (C + 1)) (by omega)
    rw [show C + 1 + (x.val - (C + 1)) = x.val by omega] at this
    have h2 := hright (n - 1 - (C + 1)) (by omega)
    rw [show C + 1 + (n - 1 - (C + 1)) = n - 1 by omega, hlast] at h2
    rw [this, ← h2]

/-- the first crossing of the single-edge form is negative. -/
theorem cs_neg (g : RowGeomD n R a b st ln rowOf) (ha : 1 ≤ a) (hb : 1 ≤ b) (C : ℕ) (hC : C + 1 < n)
    {cs : ℝ} {es : Fin n → ℝ} (hes : es ∈ Vsub rowOf) (hne : es ≠ 0) (h0 : qF1 C cs es = 0) : cs < 0 := by
  by_contra hcs
  push Not at hcs
  have hpos := qF1_zero_pos g ha hb C hC hes hne
  have hb' := bF1_nonneg C es
  have : qF1 C cs es = qF1 C 0 es + cs * bF1 C es := by
    have := qF1_affine C cs 0 es; linarith
  rw [h0] at this
  nlinarith

end

end AdalyFormal.NcwdhTwo

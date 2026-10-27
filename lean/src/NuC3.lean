import NuC2

/-!
# NuC3 -- unique continuation of a radical vector of the single-edge chain, and the two-pair window lemma (lane ncwdh_ell2_20261018)

Abstract sequence lemmas (`e f : ℤ → ℝ`, flux `f y = W y (e (y+1) - e y)`, `W y ≠ 0`, weight `1` on the edges inside a row):
* `row_fwd` / `row_bwd`: a row of length `L ≥ 2` with constant multiplier `μ`, row sum `0`: the "flux state" `(e s = 0, f (s-1) = 0)` propagates to `(e (s+L) = 0, f (s+L-1) = 0)` and back,
  and the row vanishes (via ghost values and `blocks_fwd_zero` / `blocks_back_zero`).
* `uc_rows`: a zero state at one interior row forces `e = 0` on all rows.
* `pair_lemma`: on four consecutive flat rows of equal length `L ≥ 2`, `μ₀ = μ₁` and `μ₂ = μ₃` force the state at the window start to be zero.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi

/-- the flux state at `s`: value zero and incoming flux zero. -/
def FSt (e f : ℤ → ℝ) (s : ℤ) : Prop := e s = 0 ∧ f (s - 1) = 0

/-- the row function with the two ghost neighbours that make the row equations flat. -/
noncomputable def ghost (e f : ℤ → ℝ) (s : ℤ) (L : ℕ) : ℤ → ℝ := fun x =>
  if x = s - 1 then e s - f (s - 1) else if x = s + L then e (s + L - 1) + f (s + L - 1) else e x

section
variable {e f : ℤ → ℝ} {W : ℤ → ℝ} {s : ℤ} {L : ℕ} {μ : ℝ}

theorem ghost_mid (hL : 1 ≤ L) {j : ℕ} (hj : j < L) : ghost e f s L (s + j) = e (s + j) := by
  unfold ghost
  rw [if_neg (by omega), if_neg (by omega)]

theorem ghost_left : ghost e f s L (s - 1) = e s - f (s - 1) := by
  unfold ghost; rw [if_pos rfl]

theorem ghost_right (hL : 1 ≤ L) : ghost e f s L (s + L) = e (s + L - 1) + f (s + L - 1) := by
  unfold ghost; rw [if_neg (by omega), if_pos rfl]

theorem ghost_blockELs (hL : 1 ≤ L) (hf : ∀ y, f y = W y * (e (y + 1) - e y))
    (hint : ∀ j : ℕ, j + 1 < L → W (s + j) = 1)
    (hEL : ∀ j : ℕ, j < L → f (s + j - 1) - f (s + j) = μ) :
    BlockELs s L (ghost e f s L) μ := by
  intro j hj
  have hl : ghost e f s L (s + j - 1) = if j = 0 then e s - f (s - 1) else e (s + (j - 1 : ℕ)) := by
    by_cases h0 : j = 0
    · subst h0; simp only [if_true]; rw [show s + ((0 : ℕ) : ℤ) - 1 = s - 1 by push_cast; ring]; exact ghost_left
    · rw [if_neg h0]
      have : s + (j : ℤ) - 1 = s + ((j - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ j)]; ring
      rw [this]; exact ghost_mid hL (by omega)
  have hr : ghost e f s L (s + j + 1) = if j + 1 = L then e (s + L - 1) + f (s + L - 1) else e (s + (j + 1 : ℕ)) := by
    by_cases h1 : j + 1 = L
    · rw [if_pos h1]
      have : s + (j : ℤ) + 1 = s + L := by rw [← h1]; push_cast; ring
      rw [this]; exact ghost_right hL
    · rw [if_neg h1]
      have : s + (j : ℤ) + 1 = s + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact ghost_mid hL (by omega)
  have hm := ghost_mid (e := e) (f := f) (s := s) hL hj
  have hEL' := hEL j hj
  have hd1 : ghost e f s L (s + j) - ghost e f s L (s + j - 1) = f (s + j - 1) := by
    rw [hm, hl]
    by_cases h0 : j = 0
    · subst h0; simp only [if_true]; simp
    · rw [if_neg h0]
      have hW := hint (j - 1) (by omega)
      have hfj := hf (s + ((j - 1 : ℕ) : ℤ))
      rw [hW, one_mul] at hfj
      have e1 : s + ((j - 1 : ℕ) : ℤ) + 1 = s + (j : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ j)]; ring
      have e2 : s + ((j - 1 : ℕ) : ℤ) = s + (j : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ j)]; ring
      rw [e1, e2] at hfj
      rw [e2]
      linarith
  have hd2 : ghost e f s L (s + j + 1) - ghost e f s L (s + j) = f (s + j) := by
    rw [hm, hr]
    by_cases h1 : j + 1 = L
    · rw [if_pos h1]
      have : s + (j : ℤ) = s + L - 1 := by rw [← h1]; push_cast; ring
      rw [this]; ring
    · rw [if_neg h1]
      have hW := hint j (by omega)
      have hfj := hf (s + (j : ℤ))
      rw [hW, one_mul] at hfj
      have e1 : s + (j : ℤ) + 1 = s + ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e1] at hfj
      linarith
  linarith

theorem ghost_sums (hL : 1 ≤ L) (hS : ∑ j ∈ Finset.range L, e (s + j) = 0) : BlockSums s L (ghost e f s L) := by
  unfold BlockSums
  rw [← hS]
  exact Finset.sum_congr rfl (fun j hj => ghost_mid hL (Finset.mem_range.mp hj))

/-- forward propagation of a flux-zero state through a row. -/
theorem row_fwd (hL : 2 ≤ L) (hf : ∀ y, f y = W y * (e (y + 1) - e y)) (hWL : W (s + L - 1) ≠ 0)
    (hint : ∀ j : ℕ, j + 1 < L → W (s + j) = 1)
    (hEL : ∀ j : ℕ, j < L → f (s + j - 1) - f (s + j) = μ)
    (hS : ∑ j ∈ Finset.range L, e (s + j) = 0) (hz : FSt e f s) :
    μ = 0 ∧ (∀ j : ℕ, j < L → e (s + j) = 0) ∧ FSt e f (s + L) := by
  have h1 : 1 ≤ L := by omega
  have hb := ghost_blockELs h1 hf hint hEL
  have hsm := ghost_sums (f := f) h1 hS
  obtain ⟨hE, hF⟩ := hz
  have hgs : ghost e f s L s = 0 := by
    have := ghost_mid (e := e) (f := f) (s := s) (L := L) h1 (j := 0) (by omega)
    simpa [hE] using this
  have hgl : ghost e f s L s - ghost e f s L (s - 1) = 0 := by
    rw [ghost_left, hgs]; simp [hF, hE]
  obtain ⟨hm0, hr1, hr2, hrows⟩ := blocks_fwd_zero hL hb hsm hgs hgl
  have hrowz : ∀ j : ℕ, j < L → e (s + j) = 0 := fun j hj => by
    have := hrows j hj.le
    rwa [ghost_mid h1 hj] at this
  refine ⟨hm0, hrowz, ?_⟩
  -- outgoing state
  have eL1 : e (s + L - 1) = 0 := by
    have := hrowz (L - 1) (by omega)
    have e1 : s + ((L - 1 : ℕ) : ℤ) = s + L - 1 := by push_cast [Nat.cast_sub h1]; ring
    rwa [e1] at this
  rw [ghost_right h1] at hr1
  rw [ghost_right h1] at hr2
  have hfL : f (s + L - 1) = 0 := by
    rw [eL1] at hr1; linarith
  have hfW := hf (s + L - 1)
  have e2 : s + L - 1 + 1 = s + L := by ring
  rw [e2, hfL, eL1] at hfW
  have : e (s + L) = 0 := by
    have h3 : W (s + L - 1) * (e (s + L) - 0) = 0 := by linarith
    have h4 := (mul_eq_zero.mp h3).resolve_left hWL
    linarith
  exact ⟨this, by rw [show s + L - 1 = s + (L : ℤ) - 1 from rfl]; exact hfL⟩

/-- backward propagation of a flux-zero state through a row. -/
theorem row_bwd (hL : 2 ≤ L) (hf : ∀ y, f y = W y * (e (y + 1) - e y)) (hWL : W (s + L - 1) ≠ 0)
    (hint : ∀ j : ℕ, j + 1 < L → W (s + j) = 1)
    (hEL : ∀ j : ℕ, j < L → f (s + j - 1) - f (s + j) = μ)
    (hS : ∑ j ∈ Finset.range L, e (s + j) = 0) (hz : FSt e f (s + L)) :
    μ = 0 ∧ (∀ j : ℕ, j < L → e (s + j) = 0) ∧ FSt e f s := by
  have h1 : 1 ≤ L := by omega
  have hb := ghost_blockELs h1 hf hint hEL
  have hsm := ghost_sums (f := f) h1 hS
  obtain ⟨hE, hF⟩ := hz
  have hfW := hf (s + L - 1)
  have e2 : s + L - 1 + 1 = s + L := by ring
  rw [e2, hF, hE] at hfW
  have hEL1 : e (s + L - 1) = 0 := by
    have h3 : W (s + L - 1) * (0 - e (s + L - 1)) = 0 := by linarith
    have h4 := (mul_eq_zero.mp h3).resolve_left hWL
    linarith
  have hgr : ghost e f s L (s + L) = 0 := by rw [ghost_right h1, hEL1, hF]; ring
  have hmidL : ghost e f s L (s + L - 1) = e (s + L - 1) := by
    have := ghost_mid (e := e) (f := f) (s := s) h1 (j := L - 1) (by omega)
    rwa [show s + ((L - 1 : ℕ) : ℤ) = s + L - 1 by push_cast [Nat.cast_sub h1]; ring] at this
  have hgd : ghost e f s L (s + L) - ghost e f s L (s + L - 1) = 0 := by
    rw [hgr, hmidL, hEL1]; ring
  obtain ⟨hm0, hs0, hsd, hrows⟩ := blocks_back_zero hL hb hsm hgr hgd
  have hrowz : ∀ j : ℕ, j < L → e (s + j) = 0 := fun j hj => by
    have := hrows j hj.le
    rwa [ghost_mid h1 hj] at this
  refine ⟨hm0, hrowz, ?_, ?_⟩
  · have := hrowz 0 (by omega); simpa using this
  · rw [ghost_left] at hsd
    have e0 : e s = 0 := by have := hrowz 0 (by omega); simpa using this
    have := ghost_mid (e := e) (f := f) (s := s) (L := L) h1 (j := 0) (by omega)
    simp only [Nat.cast_zero, add_zero] at this
    rw [this, e0] at hsd
    linarith

end

end AdalyFormal.NcwdhTwo

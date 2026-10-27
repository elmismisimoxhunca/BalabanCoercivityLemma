import NuC5

/-!
# NuC6 -- the row multipliers of the null vector differ on one of two aligned pairs (lane ncwdh_ell2_20261018)

`chain_overlap`: abstract chain with a single layer edge `(C, C+1)` between row `i0` (last slice `C`) and row `i0+1`; a radical nonzero vector `es` of the constrained form at weight
`c ≠ 0`; four consecutive rows `i1..i1+3` of length `4` to the right of the layer.  Then `rowMu1` differs on `(i1, i1+1)` or on `(i1+2, i1+3)`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega

section
variable {n a b R : ℕ} {st ln rowOf : ℕ → ℕ}

theorem st_lt_of_lt (g : RowGeomD n R a b st ln rowOf) {i j : ℕ} (hij : i < j) (hjR : j ≤ R) : st i < st j := by
  have h1 := g.stS i
  have h2 := g.ln1 i (by omega)
  have h3 := st_monoD g (show i + 1 ≤ j by omega)
  omega

theorem chain_overlap (g : RowGeomD n R a b st ln rowOf) (C : ℕ) (c : ℝ) (hc : c ≠ 0) (hC : C + 1 < n)
    {i0 : ℕ} (hi0 : i0 + 1 < R) (hC0 : st i0 + ln i0 = C + 1)
    {es : Fin n → ℝ} (hes : es ∈ Vsub rowOf) (hne : es ≠ 0)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF1 C c es d = 0)
    {i1 : ℕ} (hi1 : i0 + 1 < i1) (hai1 : a ≤ i1) (hbi1 : i1 + 3 + b < R) (hL4 : ∀ k, k ≤ 3 → ln (i1 + k) = 4) :
    rowMu1 C c es st i1 ≠ rowMu1 C c es st (i1 + 1) ∨ rowMu1 C c es st (i1 + 2) ≠ rowMu1 C c es st (i1 + 3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h01, h23⟩ := hcon
  set e : ℤ → ℝ := nx es with he
  set W : ℤ → ℝ := W1 C c with hW
  set f : ℤ → ℝ := fun y => W y * (e (y + 1) - e y) with hf
  have hWne : ∀ y, W y ≠ 0 := by
    intro y; simp only [hW, W1]; split_ifs
    · exact hc
    · exact one_ne_zero
  -- layer edge sits between rows
  have hCst : C + 1 = st (i0 + 1) := by rw [g.stS i0]; omega
  have hint : ∀ i, i < R → ∀ j : ℕ, j + 1 < ln i → W ((st i : ℤ) + (j : ℤ)) = 1 := by
    intro i hi j hj
    simp only [hW, W1]
    rw [if_neg]
    intro heq
    have hnat : st i + j = C := by exact_mod_cast heq
    have h1 : st i ≤ C := by omega
    have h2 : C + 1 < st (i + 1) := by rw [g.stS i]; omega
    have h3 : st i < st (i0 + 1) := by omega
    have h4 : st (i0 + 1) < st (i + 1) := by omega
    have hi1' : i < i0 + 1 := by
      by_contra hh
      have := st_monoD g (show i0 + 1 ≤ i by omega)
      omega
    have hi2' : i0 + 1 < i + 1 := by
      by_contra hh
      have := st_monoD g (show i + 1 ≤ i0 + 1 by omega)
      omega
    omega
  have hEL : ∀ i, i < R → ∀ j : ℕ, j < ln i → f ((st i : ℤ) + (j : ℤ) - 1) - f ((st i : ℤ) + (j : ℤ)) = rowMu1 C c es st i := by
    intro i hi j hj
    have h := rowEL_raw1 g C c hC hrad hi j hj
    simp only [hf]
    have e1 : (st i : ℤ) + (j : ℤ) - 1 + 1 = (st i : ℤ) + (j : ℤ) := by ring
    rw [e1]
    push_cast at h
    simpa [hW, he] using h
  have hS : ∀ i, i < R → ∑ j ∈ Finset.range (ln i), e ((st i : ℤ) + (j : ℤ)) = 0 := by
    intro i hi
    exact rowSum_of_memD g hes hi
  have hstS : ∀ i, ((st (i + 1) : ℕ) : ℤ) = ((st i : ℕ) : ℤ) + (ln i : ℤ) := by
    intro i; rw [g.stS i]; push_cast; ring
  -- the window
  set s0 : ℤ := (st i1 : ℤ) with hs0
  have hwin : ∀ k : ℕ, k ≤ 3 → (st (i1 + k) : ℤ) = s0 + (k : ℤ) * 4 := by
    intro k
    induction k with
    | zero => intro _; simp [hs0]
    | succ k ih =>
      intro hk
      have := hstS (i1 + k)
      rw [show i1 + (k + 1) = i1 + k + 1 by ring, this, ih (by omega), hL4 k (by omega)]
      push_cast; ring
  have hflat : ∀ k : ℕ, k ≤ 3 → BlockELs (s0 + (k : ℤ) * 4) 4 e (rowMu1 C c es st (i1 + k)) := by
    intro k hk
    have hiR : i1 + k < R := by omega
    have hC1 : C + 1 < st i1 := by
      have := st_lt_of_lt g (show i0 + 1 < i1 by omega) (by omega)
      omega
    intro j hj
    have h := hEL (i1 + k) hiR j (by rw [hL4 k hk]; exact hj)
    have hw1 : W ((st (i1 + k) : ℤ) + (j : ℤ) - 1) = 1 := by
      simp only [hW, W1]; rw [if_neg]
      intro heq
      have : st (i1 + k) + j = C + 1 := by
        have : ((st (i1 + k) + j : ℕ) : ℤ) = ((C + 1 : ℕ) : ℤ) := by push_cast; omega
        exact_mod_cast this
      have hm := st_monoD g (show i1 ≤ i1 + k by omega)
      omega
    have hw2 : W ((st (i1 + k) : ℤ) + (j : ℤ)) = 1 := by
      simp only [hW, W1]; rw [if_neg]
      intro heq
      have : st (i1 + k) + j = C := by exact_mod_cast heq
      have hm := st_monoD g (show i1 ≤ i1 + k by omega)
      omega
    simp only [hf, hw1, hw2] at h
    rw [hwin k hk] at h
    have e1 : s0 + (k : ℤ) * 4 + (j : ℤ) - 1 + 1 = s0 + (k : ℤ) * 4 + (j : ℤ) := by ring
    rw [e1] at h
    simp only [one_mul] at h
    linarith
  have hsum : ∀ k : ℕ, k ≤ 3 → BlockSums (s0 + (k : ℤ) * 4) 4 e := by
    intro k hk
    have := hS (i1 + k) (by omega)
    rw [hL4 k hk, hwin k hk] at this
    exact this
  have hstate := pair_lemma (L := 4) (by norm_num) (m := fun k => rowMu1 C c es st (i1 + k)) (s0 := s0)
    (fun k hk => by simpa using hflat k hk) hsum (by simpa using h01) (by simpa using h23)
  have hz : FSt e f s0 := by
    obtain ⟨h1, h2⟩ := hstate
    refine ⟨h1, ?_⟩
    simp only [hf]
    rw [show s0 - 1 + 1 = s0 by ring, h1]
    have : e s0 - e (s0 - 1) = 0 := h2
    rw [h1] at this
    rw [show (0:ℝ) - e (s0 - 1) = 0 from by linarith]; ring
  have hallz := uc_rows (R := R) (a := a) (b := b) (st := fun i => (st i : ℤ)) (ln := ln) (e := e) (f := f) (W := W) (μ := fun i => rowMu1 C c es st i)
    hWne (fun y => rfl) hstS (fun i hi => g.lnL i hi) (fun i h1 h2 => g.lnI i h1 h2) (fun i h1 h2 => g.lnR i h1 h2)
    hint hEL hS hai1 (by omega) hz
  apply hne
  funext x
  have hxn : x.val < n := x.2
  obtain ⟨i, hiR, hi1', hi2'⟩ := g.cover x.val hxn
  have := hallz i hiR (x.val - st i) (by omega)
  have e1 : (st i : ℤ) + ((x.val - st i : ℕ) : ℤ) = (x.val : ℤ) := by omega
  rw [e1] at this
  have h2 := nx_nat es x.val hxn
  simp only [he] at this
  rw [h2] at this
  simpa using this

end

end AdalyFormal.NcwdhTwo

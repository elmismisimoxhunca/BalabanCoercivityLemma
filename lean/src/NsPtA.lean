import Mathlib

/-!
# PtA -- cube sums and the abstract three-level chain (lane omega/near2/point)

`cube g n a b c = sum_{i,j,k<n} g (a+i) (b+j) (c+k)` (an `n`-cube sum of a function on `N^3` with values in a real vector space).
* `cube_tower`: `cube g (ell*n)` splits into `ell^3` sub-cubes of side `n`.
* `chain_main`: the x0-chain argument for the nested tower (abstract in `g`, pure arithmetic on the region boundaries).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega

open Finset

section cube
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- the `n`-cube sum based at `(a,b,c)`. -/
def cube (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) : E :=
  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, g (a + i) (b + j) (c + k)

theorem sum_range_mul_split (f : ℕ → E) (n ell : ℕ) :
    ∑ m ∈ range (ell * n), f m = ∑ i ∈ range ell, ∑ r ∈ range n, f (n * i + r) := by
  induction ell with
  | zero => simp
  | succ e ih =>
    rw [show (e + 1) * n = e * n + n by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1; ring

theorem cube_tower (g : ℕ → ℕ → ℕ → E) (n ell a b c : ℕ) :
    cube g (ell * n) a b c = ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ k ∈ range ell,
      cube g n (a + n * i) (b + n * j) (c + n * k) := by
  unfold cube
  simp_rw [sum_range_mul_split]
  simp only [add_assoc]
  -- goal: sum_i0 sum_r0 sum_i1 sum_r1 sum_i2 sum_r2 = sum_i0 sum_i1 sum_i2 sum_r0 sum_r1 sum_r2
  have e1 : ∀ (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E),
      ∑ i0 ∈ range ell, ∑ r0 ∈ range n, ∑ i1 ∈ range ell, ∑ r1 ∈ range n, ∑ i2 ∈ range ell, ∑ r2 ∈ range n, F i0 r0 i1 r1 i2 r2
      = ∑ i0 ∈ range ell, ∑ i1 ∈ range ell, ∑ i2 ∈ range ell, ∑ r0 ∈ range n, ∑ r1 ∈ range n, ∑ r2 ∈ range n, F i0 r0 i1 r1 i2 r2 := by
    intro F
    refine Finset.sum_congr rfl (fun i0 _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i1 _ => ?_)
    -- sum_r0 sum_r1 sum_i2 sum_r2  -> sum_i2 sum_r0 sum_r1 sum_r2
    have : ∀ r0 : ℕ, ∑ r1 ∈ range n, ∑ i2 ∈ range ell, ∑ r2 ∈ range n, F i0 r0 i1 r1 i2 r2
        = ∑ i2 ∈ range ell, ∑ r1 ∈ range n, ∑ r2 ∈ range n, F i0 r0 i1 r1 i2 r2 := by
      intro r0
      rw [Finset.sum_comm]
    simp_rw [this]
    rw [Finset.sum_comm]
  exact e1 (fun i0 r0 i1 r1 i2 r2 => g (a + (n * i0 + r0)) (b + (n * i1 + r1)) (c + (n * i2 + r2)))

theorem cube_one (g : ℕ → ℕ → ℕ → E) (a b c : ℕ) : cube g 1 a b c = g a b c := by
  simp [cube]

theorem cube_congr (g g' : ℕ → ℕ → ℕ → E) (n a b c : ℕ)
    (h : ∀ i j k, i < n → j < n → k < n → g (a + i) (b + j) (c + k) = g' (a + i) (b + j) (c + k)) :
    cube g n a b c = cube g' n a b c := by
  unfold cube
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => ?_)))
  exact h i j k (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)

theorem cube_const (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) (v : E)
    (h : ∀ i j k, i < n → j < n → k < n → g (a + i) (b + j) (c + k) = v) :
    cube g n a b c = ((n : ℝ) ^ 3) • v := by
  rw [show cube g n a b c = cube (fun _ _ _ => v) n a b c from cube_congr _ _ n a b c h]
  simp [cube, Finset.sum_const]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1; ring

theorem cube_zero_of (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ)
    (h : ∀ i j k, i < n → j < n → k < n → g (a + i) (b + j) (c + k) = 0) :
    cube g n a b c = 0 := by
  have := cube_const g n a b c 0 h
  simpa using this

theorem smul_pow_eq_zero {v : E} {n : ℕ} (hn : 0 < n) {m : ℕ} (h : ((n : ℝ) ^ m) • v = 0) : v = 0 := by
  have hn' : ((n : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  exact (smul_eq_zero.mp h).resolve_left hn'

/-- constancy along an arithmetic progression. -/
theorem const_chain (f : ℕ → E) (s n K : ℕ) (h : ∀ m, m < K → f (s + (m + 1) * n) = f (s + m * n)) :
    ∀ m, m ≤ K → f (s + m * n) = f s := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [h m (by omega), ih (by omega)]

end cube

end AdalyFormal.CoverOmega

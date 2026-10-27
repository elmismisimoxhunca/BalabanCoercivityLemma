import DrEquiv

/-! Exact charged/sesquilinear forms for mixed-colour areas, and the associated
complex current recurrence.  These are algebraic interfaces; no physical
nonvanishing statement is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AdalyFormal.Round14.Cancellation

open Finset
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

/-- The real oriented area of one complex charged coordinate against the real
coefficient matrix `K`.  If `z = g + i f`, the summand is exactly
`(f e * g d - g e * f d) * K e d`. -/
def chargedArea (K : ι → ι → ℝ) (z : ι → ℂ) : ℝ :=
  ∑ e : ι, ∑ d : ι, (z e * conj (z d)).im * K e d

/-- The same area as the real part of the sesquilinear form `i z* K z`.
No symmetry or definiteness of `K` is assumed. -/
def sesquilinearArea (K : ι → ι → ℝ) (z : ι → ℂ) : ℝ :=
  (Complex.I * ∑ e : ι, ∑ d : ι, conj (z e) * (K e d : ℂ) * z d).re

theorem chargedArea_eq_sesquilinear (K : ι → ι → ℝ) (z : ι → ℂ) :
    chargedArea K z = sesquilinearArea K z := by
  unfold chargedArea sesquilinearArea
  rw [Complex.I_mul_re]
  have hc : (∑ e : ι, ∑ d : ι, z e * conj (z d) * (K e d : ℂ)) =
      conj (∑ e : ι, ∑ d : ι, conj (z e) * (K e d : ℂ) * z d) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hi := congrArg Complex.im hc
  rw [Complex.conj_im] at hi
  rw [Complex.im_sum] at hi
  simp only [Complex.im_sum] at hi
  simp only [Complex.im_sum]
  rw [← hi]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  ring_nf

/-- Exact mixed-colour dictionary.  For `z = g + i f`, the charged-area
summand is the original ordered-pair determinant. -/
theorem chargedArea_real_imag (K : ι → ι → ℝ) (f g : ι → ℝ) :
    chargedArea K (fun e => (g e : ℂ) + (f e : ℂ) * Complex.I) =
      ∑ e : ι, ∑ d : ι, (f e * g d - g e * f d) * K e d := by
  unfold chargedArea
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro d _
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  ring_nf

/-- A complex phase/amplitude scales the charged area by its squared modulus. -/
theorem chargedArea_smul (K : ι → ι → ℝ) (z : ι → ℂ) (c : ℂ) :
    chargedArea K (fun e => c * z e) = Complex.normSq c * chargedArea K z := by
  have ht (e d : ι) : (c * z e * conj (c * z d)).im * K e d =
      Complex.normSq c * ((z e * conj (z d)).im * K e d) := by
    have h : c * z e * conj (c * z d) =
        (Complex.normSq c : ℂ) * (z e * conj (z d)) := by
      rw [map_mul]
      calc
        _ = (c * conj c) * (z e * conj (z d)) := by ring
        _ = _ := by rw [Complex.mul_conj]
    rw [h]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  unfold chargedArea
  simp_rw [ht]
  calc
    _ = ∑ e : ι, Complex.normSq c * ∑ d : ι, (z e * conj (z d)).im * K e d := by
      apply Finset.sum_congr rfl
      intro e _
      exact (Finset.mul_sum Finset.univ _ _).symm
    _ = _ := (Finset.mul_sum Finset.univ _ _).symm

/-- Real coefficients on one charged complex line give the exact factor `a²+b²`. -/
theorem chargedArea_affine (K : ι → ι → ℝ) (z : ι → ℂ) (a b : ℝ) :
    chargedArea K (fun e => ((a : ℂ) + (b : ℂ) * Complex.I) * z e) =
      (a ^ 2 + b ^ 2) * chargedArea K z := by
  rw [chargedArea_smul, Complex.normSq_add_mul_I]

/-- In particular, phase rotation and rescaling preserve a nonzero charged area. -/
theorem chargedArea_smul_ne_zero (K : ι → ι → ℝ) (z : ι → ℂ)
    (h : chargedArea K z ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    chargedArea K (fun e => c * z e) ≠ 0 := by
  rw [chargedArea_smul]
  exact mul_ne_zero (Complex.normSq_pos.mpr hc).ne' h

/-- A common complex phase times a real array has zero charged area.
Nonvanishing therefore requires a genuinely non-real ratio somewhere; chargedness
or a nonzero coordinate alone is not sufficient. -/
theorem chargedArea_common_phase_zero (K : ι → ι → ℝ) (w : ι → ℝ) (c : ℂ) :
    chargedArea K (fun e => c * (w e : ℂ)) = 0 := by
  have hz : chargedArea K (fun e => (w e : ℂ)) = 0 := by
    unfold chargedArea
    apply Finset.sum_eq_zero
    intro e _
    apply Finset.sum_eq_zero
    intro d _
    simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero, zero_mul]
  rw [chargedArea_smul, hz, mul_zero]

/-- Imaginary charge current between adjacent layers of one complex solution. -/
def chargeCurrent (z : ℕ → ℂ) (n : ℕ) : ℝ := (conj (z n) * z (n + 1)).im

/-- A real reversible second-order recurrence multiplies the complex current by
minus its last coefficient.  This is the one-solution charged form of the real
oriented-area recurrence. -/
theorem chargeCurrent_step (a b : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ)
    (hr : z (n + 2) = (a n : ℂ) * z (n + 1) + (b n : ℂ) * z n) :
    chargeCurrent z (n + 1) = -(b n) * chargeCurrent z n := by
  unfold chargeCurrent
  rw [hr]
  have hc : conj (z (n + 1)) * z n = conj (conj (z n) * z (n + 1)) := by
    simp only [map_mul, Complex.conj_conj]
    ring
  have hs : conj (z (n + 1)) * z (n + 1) =
      (Complex.normSq (z (n + 1)) : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hrw : conj (z (n + 1)) * ((a n : ℂ) * z (n + 1) + (b n : ℂ) * z n) =
      (a n : ℂ) * (Complex.normSq (z (n + 1)) : ℂ) +
        (b n : ℂ) * conj (conj (z n) * z (n + 1)) := by
    calc
      _ = (a n : ℂ) * (conj (z (n + 1)) * z (n + 1)) +
          (b n : ℂ) * (conj (z (n + 1)) * z n) := by ring
      _ = _ := by rw [hs, hc]
  rw [hrw]
  simp only [map_mul, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im,
    Complex.conj_re, Complex.conj_conj]
  ring

/-- The unit negative last coefficient gives exact current conservation, not merely
an inequality or an asymptotic statement. -/
theorem chargeCurrent_eq_seed (a : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ)
    (hr : ∀ n < N, z (n + 2) = (a n : ℂ) * z (n + 1) - z n) :
    chargeCurrent z N = chargeCurrent z 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [chargeCurrent_step a (fun _ => -1) z N (by
        convert hr N (Nat.lt_add_one N) using 1 ; norm_num [sub_eq_add_neg])]
      simp only [neg_neg, one_mul]
      exact ih (fun n hn => hr n (Nat.lt_succ_of_lt hn))

/-- A nonzero current seed propagates through every finite reversible segment. -/
theorem chargeCurrent_ne_zero (a b : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hr : ∀ n < N, z (n + 2) = (a n : ℂ) * z (n + 1) + (b n : ℂ) * z n)
    (hseed : chargeCurrent z 0 ≠ 0) : chargeCurrent z N ≠ 0 := by
  induction N with
  | zero => exact hseed
  | succ N ih =>
      have hprev : chargeCurrent z N ≠ 0 := ih (fun n hn => hb n (Nat.lt_succ_of_lt hn))
        (fun n hn => hr n (Nat.lt_succ_of_lt hn))
      rw [chargeCurrent_step a b z N (hr N (Nat.lt_add_one N))]
      exact mul_ne_zero (neg_ne_zero.mpr (hb N (Nat.lt_add_one N))) hprev

#print axioms chargedArea
#print axioms sesquilinearArea
#print axioms chargedArea_eq_sesquilinear
#print axioms chargedArea_real_imag
#print axioms chargedArea_smul
#print axioms chargedArea_affine
#print axioms chargedArea_smul_ne_zero
#print axioms chargedArea_common_phase_zero
#print axioms chargeCurrent
#print axioms chargeCurrent_step
#print axioms chargeCurrent_eq_seed
/-- An infinite reversible recurrence with one nonzero current seed has nonzero
current cofinally.  The physical recurrence and seed are deliberately left as
inputs; this theorem does not construct them. -/
theorem chargeCurrent_cofinal (a b : ℕ → ℝ) (z : ℕ → ℂ)
    (hb : ∀ n, b n ≠ 0)
    (hr : ∀ n, z (n + 2) = (a n : ℂ) * z (n + 1) + (b n : ℂ) * z n)
    (hseed : chargeCurrent z 0 ≠ 0) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ chargeCurrent z n ≠ 0 := by
  intro N
  exact ⟨N, le_rfl, chargeCurrent_ne_zero a b z N (fun n _ => hb n)
    (fun n _ => hr n) hseed⟩

#print axioms chargeCurrent_ne_zero
#print axioms chargeCurrent_cofinal

end AdalyFormal.Round14.Cancellation

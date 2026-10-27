import Mathlib

/-!
# GFC4 -- the quasi-periodic cell model on `ℤ³`: lattice, cell, periodic sums, shift invariance.
Pure combinatorics; no repo types.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexConjugate

namespace AdalyFormal.FlatCoercivity

abbrev Z3 := Fin 3 → ℤ

/-- unit vector -/
def ev (μ : Fin 3) : Z3 := Pi.single μ 1

/-- the cell of side `n` -/
abbrev Cell (n : ℕ) := Fin 3 → Fin n

/-- embedding of the cell into `ℤ³` -/
def cc {n : ℕ} (t : Cell n) : Z3 := fun μ => ((t μ : ℕ) : ℤ)

/-- reduction `ℤ³ → Cell n` -/
def modc (n : ℕ) (hn : 0 < n) (x : Z3) : Cell n := fun μ =>
  ⟨(x μ % (n : ℤ)).toNat, by
    have h1 : 0 ≤ x μ % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have h2 : x μ % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    omega⟩

variable {n : ℕ}

theorem cc_modc (hn : 0 < n) (x : Z3) (μ : Fin 3) :
    cc (modc n hn x) μ = x μ % (n : ℤ) := by
  have h1 : 0 ≤ x μ % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  show (((modc n hn x μ : Fin n) : ℕ) : ℤ) = _
  simp only [modc]
  omega

theorem modc_cc (hn : 0 < n) (t : Cell n) : modc n hn (cc t) = t := by
  funext μ
  apply Fin.ext
  have h := cc_modc hn (cc t) μ
  have h2 : cc t μ % (n : ℤ) = cc t μ := Int.emod_eq_of_lt (by simp [cc]) (by
    simp only [cc]; exact_mod_cast (t μ).isLt)
  have h3 : (((modc n hn (cc t) μ : Fin n) : ℕ) : ℤ) = ((t μ : ℕ) : ℤ) := by
    have := h; rw [h2] at this; simpa [cc] using this
  exact_mod_cast h3

theorem modc_add (hn : 0 < n) (x k : Z3) : modc n hn (x + (n : ℤ) • k) = modc n hn x := by
  funext μ
  apply Fin.ext
  simp only [modc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [Int.add_mul_emod_self_left]

theorem eq_cc_modc_add (hn : 0 < n) (x : Z3) :
    x = cc (modc n hn x) + (n : ℤ) • (fun μ => x μ / (n : ℤ)) := by
  funext μ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cc_modc hn]
  have := Int.emod_add_mul_ediv (x μ) (n : ℤ)
  linarith [this]

/-- periodic: invariant under all translations by multiples of `n` -/
def Per (n : ℕ) (f : Z3 → ℂ) : Prop := ∀ x (k : Z3), f (x + (n : ℤ) • k) = f x

theorem Per.eq_cell (hn : 0 < n) {f : Z3 → ℂ} (hf : Per n f) (x : Z3) : f x = f (cc (modc n hn x)) := by
  conv_lhs => rw [eq_cc_modc_add hn x]
  exact hf _ _

/-- the cell integral -/
def cint (n : ℕ) (h : Z3 → ℂ) : ℂ := ∑ t : Cell n, h (cc t)

/-- translation by `a` permutes the cell mod `n` -/
noncomputable def cellShift (hn : 0 < n) (a : Z3) : Equiv.Perm (Cell n) where
  toFun t := modc n hn (cc t + a)
  invFun t := modc n hn (cc t - a)
  left_inv t := by
    have h := eq_cc_modc_add hn (cc t + a)
    have : cc (modc n hn (cc t + a)) - a = cc t - (n : ℤ) • (fun μ => (cc t + a) μ / (n : ℤ)) := by
      funext μ
      have := congrFun h μ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
      linarith
    show modc n hn (cc (modc n hn (cc t + a)) - a) = t
    rw [this, sub_eq_add_neg, ← smul_neg, modc_add, modc_cc]
  right_inv t := by
    have h := eq_cc_modc_add hn (cc t - a)
    have : cc (modc n hn (cc t - a)) + a = cc t - (n : ℤ) • (fun μ => (cc t - a) μ / (n : ℤ)) := by
      funext μ
      have := congrFun h μ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
      linarith
    show modc n hn (cc (modc n hn (cc t - a)) + a) = t
    rw [this, sub_eq_add_neg, ← smul_neg, modc_add, modc_cc]

theorem cint_shift (hn : 0 < n) {h : Z3 → ℂ} (hh : Per n h) (a : Z3) :
    cint n (fun x => h (x + a)) = cint n h := by
  unfold cint
  have : ∀ t : Cell n, h (cc t + a) = h (cc (cellShift hn a t)) := by
    intro t
    rw [hh.eq_cell hn (cc t + a)]
    rfl
  simp only [this]
  exact Equiv.sum_comp (cellShift hn a) (fun t => h (cc t))

#print axioms cint_shift

end AdalyFormal.FlatCoercivity

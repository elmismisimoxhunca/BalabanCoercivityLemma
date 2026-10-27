import CvX1

/-!
# CvK1 -- the constrained chain form and its first crossing (lane cover_jacobi_20261016)

Model of the transverse-zero-mode, direction-1, sigma_3 sector (NOTES round 5/7): slices `0..n-1`, values `e : Fin n -> R`,
edge differences `dlt e y = e_{y+1} - e_y` (`y < n - 1`), constraint space `V = {e | every row sum vanishes}` (`rowOf : N -> N` assigns a row to a slice),
form `q C c e = sum_y w_y(c) (dlt e y)^2` with `w_y = c` on the two layer edges `y = C - 1`, `y = C` and `1` elsewhere.
`chain_crossing`: if `q C c1 e1 < 0` for some `c1 < 1`, `e1 in V`, there is `c* in (c1,1)` and `e* in V`, `e* != 0`, with `q c* e* = 0`, `q c* >= 0` on `V`, `q c` positive definite on `V`
for `c in (c*,1]`, and the radical identity `bil c* e* delta = 0` for all `delta in V`.  `chain_mult_const`: consequently `(L e*)_x` is constant on every row.
This is a statement about the abstract chain only; it is NOT connected to the genuine operators here.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

section chain
variable {n : ℕ}

/-- extension of `e : Fin n -> R` by zero to `N`. -/
def ex (e : Fin n → ℝ) (x : ℕ) : ℝ := if h : x < n then e ⟨x, h⟩ else 0

def dlt (e : Fin n → ℝ) (y : ℕ) : ℝ := ex e (y + 1) - ex e y

theorem ex_add (e f : Fin n → ℝ) (x : ℕ) : ex (e + f) x = ex e x + ex f x := by
  unfold ex; split_ifs <;> simp

theorem ex_smul (r : ℝ) (e : Fin n → ℝ) (x : ℕ) : ex (r • e) x = r * ex e x := by
  unfold ex; split_ifs <;> simp

theorem dlt_add (e f : Fin n → ℝ) (y : ℕ) : dlt (e + f) y = dlt e y + dlt f y := by
  unfold dlt; rw [ex_add, ex_add]; ring

theorem dlt_smul (r : ℝ) (e : Fin n → ℝ) (y : ℕ) : dlt (r • e) y = r * dlt e y := by
  unfold dlt; rw [ex_smul, ex_smul]; ring

theorem ex_cont (x : ℕ) : Continuous (fun e : Fin n → ℝ => ex e x) := by
  unfold ex
  by_cases h : x < n
  · simp only [dif_pos h]; exact continuous_apply _
  · simp only [dif_neg h]; exact continuous_const

theorem dlt_cont (y : ℕ) : Continuous (fun e : Fin n → ℝ => dlt e y) :=
  (ex_cont (y + 1)).sub (ex_cont y)

/-- the unit-weight form: sum of squares of all consecutive differences. -/
def aF (e : Fin n → ℝ) : ℝ := ∑ y ∈ range (n - 1), (dlt e y) ^ 2

/-- the layer part: the two layer edges `(C-1,C)` and `(C,C+1)`. -/
def bF (C : ℕ) (e : Fin n → ℝ) : ℝ := (dlt e (C - 1)) ^ 2 + (dlt e C) ^ 2

/-- the one-parameter family `q_c = a - (1 - c) b`. -/
def qF (C : ℕ) (c : ℝ) (e : Fin n → ℝ) : ℝ := aF e - (1 - c) * bF C e

theorem aF_cont : Continuous (fun e : Fin n → ℝ => aF e) := by
  unfold aF
  exact continuous_finsetSum _ (fun y _ => (dlt_cont y).pow 2)

theorem bF_cont (C : ℕ) : Continuous (fun e : Fin n → ℝ => bF C e) := by
  unfold bF
  exact ((dlt_cont _).pow 2).add ((dlt_cont _).pow 2)

theorem aF_smul (r : ℝ) (e : Fin n → ℝ) : aF (r • e) = r ^ 2 * aF e := by
  unfold aF
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _ => by rw [dlt_smul]; ring)

theorem bF_smul (C : ℕ) (r : ℝ) (e : Fin n → ℝ) : bF C (r • e) = r ^ 2 * bF C e := by
  unfold bF; rw [dlt_smul, dlt_smul]; ring

theorem bF_nonneg (C : ℕ) (e : Fin n → ℝ) : 0 ≤ bF C e := by
  unfold bF; positivity

/-- the constraint space: every row sum vanishes. -/
def Vsub (rowOf : ℕ → ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {e | ∀ r : ℕ, ∑ x ∈ (univ.filter (fun x : Fin n => rowOf x.val = r)), e x = 0}
  zero_mem' := by intro r; simp
  add_mem' := by
    intro e f he hf r
    simp only [Pi.add_apply, Finset.sum_add_distrib, he r, hf r, add_zero]
  smul_mem' := by
    intro c e he r
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, he r, mul_zero]

theorem mem_Vsub {rowOf : ℕ → ℕ} {e : Fin n → ℝ} : e ∈ Vsub rowOf ↔ ∀ r : ℕ, ∑ x ∈ (univ.filter (fun x : Fin n => rowOf x.val = r)), e x = 0 := Iff.rfl

theorem aF_nonneg (e : Fin n → ℝ) : 0 ≤ aF e := by
  unfold aF; exact Finset.sum_nonneg (fun y _ => sq_nonneg _)

theorem ex_zero_of_const (e : Fin n → ℝ) (h : aF e = 0) (k : ℕ) (hk : k < n) : ex e k = ex e 0 := by
  have hd : ∀ y ∈ range (n - 1), (dlt e y) ^ 2 = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (dlt e y))).mp h
    exact this
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < n := by omega
    have h1 := ih hk'
    have h2 : dlt e k = 0 := by
      have := hd k (by simp [Finset.mem_range]; omega)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    unfold dlt at h2
    linarith

/-- positive definiteness of the unit-weight form on the constraint space. -/
theorem aF_pos (rowOf : ℕ → ℕ) {e : Fin n → ℝ} (he : e ∈ Vsub rowOf) (hne : e ≠ 0) : 0 < aF e := by
  by_contra hle
  have h0 : aF e = 0 := le_antisymm (not_lt.mp hle) (aF_nonneg e)
  apply hne
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim e 0) hne
    · exact h
  have hconst : ∀ x : Fin n, e x = ex e 0 := by
    intro x
    have := ex_zero_of_const e h0 x.val x.2
    simpa [ex, x.2] using this
  have hsum := he (rowOf 0)
  have h00 : ex e 0 = 0 := by
    have hmem : (⟨0, hn⟩ : Fin n) ∈ (univ.filter (fun x : Fin n => rowOf x.val = rowOf 0)) := by simp
    have hcard : 0 < (univ.filter (fun x : Fin n => rowOf x.val = rowOf 0)).card := Finset.card_pos.mpr ⟨_, hmem⟩
    rw [Finset.sum_congr rfl (fun x _ => hconst x)] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have : (((univ.filter (fun x : Fin n => rowOf x.val = rowOf 0)).card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hcard.ne'
    exact (mul_eq_zero.mp hsum).resolve_left this
  funext x
  rw [hconst x, h00]; rfl

/-- the polarisation of `qF`. -/
def BF (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : ℝ :=
  (∑ y ∈ range (n - 1), dlt e y * dlt f y) - (1 - c) * (dlt e (C - 1) * dlt f (C - 1) + dlt e C * dlt f C)

theorem qF_add (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : qF C c (e + f) = qF C c e + 2 * BF C c e f + qF C c f := by
  unfold qF aF bF BF
  simp only [dlt_add]
  have : ∑ y ∈ range (n - 1), (dlt e y + dlt f y) ^ 2 =
      ∑ y ∈ range (n - 1), (dlt e y) ^ 2 + 2 * ∑ y ∈ range (n - 1), dlt e y * dlt f y + ∑ y ∈ range (n - 1), (dlt f y) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF_smul_right (C : ℕ) (c t : ℝ) (e f : Fin n → ℝ) : BF C c e (t • f) = t * BF C c e f := by
  unfold BF
  simp only [dlt_smul]
  have : ∑ y ∈ range (n - 1), dlt e y * (t * dlt f y) = t * ∑ y ∈ range (n - 1), dlt e y * dlt f y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF_add_right (C : ℕ) (c : ℝ) (e f g : Fin n → ℝ) : BF C c e (f + g) = BF C c e f + BF C c e g := by
  unfold BF
  simp only [dlt_add]
  have : ∑ y ∈ range (n - 1), dlt e y * (dlt f y + dlt g y) =
      ∑ y ∈ range (n - 1), dlt e y * dlt f y + ∑ y ∈ range (n - 1), dlt e y * dlt g y := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem qF_smul (C : ℕ) (c t : ℝ) (e : Fin n → ℝ) : qF C c (t • e) = t ^ 2 * qF C c e := by
  unfold qF; rw [aF_smul, bF_smul]; ring

theorem quad_neg_exists (B Q : ℝ) (hB : B ≠ 0) (hQ : 0 ≤ Q) : ∃ t : ℝ, 2 * t * B + t ^ 2 * Q < 0 := by
  refine ⟨-B / (Q + 1), ?_⟩
  have hQ1 : 0 < Q + 1 := by linarith
  have : 2 * (-B / (Q + 1)) * B + (-B / (Q + 1)) ^ 2 * Q = -(B ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by
    field_simp; ring
  rw [this]
  apply div_neg_of_neg_of_pos
  · have : 0 < B ^ 2 := by positivity
    nlinarith
  · positivity

/-- a null vector of a positive semidefinite form is in its radical. -/
theorem radical_of_psd (rowOf : ℕ → ℕ) (C : ℕ) (c : ℝ) (es : Fin n → ℝ) (hes : es ∈ Vsub rowOf)
    (hpsd : ∀ e : Fin n → ℝ, e ∈ Vsub rowOf → 0 ≤ qF C c e) (h0 : qF C c es = 0) :
    ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C c es d = 0 := by
  intro d hd
  by_contra hB
  obtain ⟨t, ht⟩ := quad_neg_exists (BF C c es d) (qF C c d) hB (hpsd d hd)
  have hmem : es + t • d ∈ Vsub rowOf := (Vsub rowOf).add_mem hes ((Vsub rowOf).smul_mem t hd)
  have := hpsd _ hmem
  rw [qF_add, BF_smul_right, qF_smul, h0] at this
  linarith

/-- the first crossing of the constrained chain form. -/
theorem chain_crossing (rowOf : ℕ → ℕ) (C : ℕ) (c1 : ℝ) (hc1 : c1 < 1) (e1 : Fin n → ℝ) (he1 : e1 ∈ Vsub rowOf)
    (hneg : qF C c1 e1 < 0) :
    ∃ cs : ℝ, c1 < cs ∧ cs < 1 ∧ (∃ es : Fin n → ℝ, es ∈ Vsub rowOf ∧ es ≠ 0 ∧ qF C cs es = 0) ∧
      (∀ e : Fin n → ℝ, e ∈ Vsub rowOf → 0 ≤ qF C cs e) ∧
      (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e : Fin n → ℝ, e ∈ Vsub rowOf → e ≠ 0 → 0 < qF C c e) ∧
      (∀ es : Fin n → ℝ, es ∈ Vsub rowOf → qF C cs es = 0 → ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C cs es d = 0) := by
  have hfc := first_crossing (E := Fin n → ℝ) (Vsub rowOf) aF (bF C) aF_cont (bF_cont C)
    aF_smul (bF_smul C) (bF_nonneg C) (fun e he hne => aF_pos rowOf he hne) c1 hc1 e1 he1 hneg
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos⟩ := hfc
  refine ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, ?_⟩
  intro es' hes' h0' d hd
  exact radical_of_psd rowOf C cs es' hes' hpsd h0' d hd

/-- the row multipliers: `(L e*)_x = B(e*, delta_x)` is constant along each row. -/
theorem chain_mult_const (rowOf : ℕ → ℕ) (C : ℕ) (cs : ℝ) (es : Fin n → ℝ)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF C cs es d = 0) (x x' : Fin n) (hxx : rowOf x.val = rowOf x'.val) :
    BF C cs es (Pi.single x 1) = BF C cs es (Pi.single x' 1) := by
  classical
  have hmem : (Pi.single x (1 : ℝ) - Pi.single x' (1 : ℝ) : Fin n → ℝ) ∈ Vsub rowOf := by
    intro r
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [Finset.sum_pi_single' , Finset.sum_pi_single']
    by_cases hr : rowOf x.val = r
    · have h2 : rowOf x'.val = r := by rw [← hxx]; exact hr
      simp [hr, h2]
    · have h2 : ¬ rowOf x'.val = r := by rw [← hxx]; exact hr
      simp [hr, h2]
  have h := hrad _ hmem
  have hsub : BF C cs es (Pi.single x 1 - Pi.single x' 1) = BF C cs es (Pi.single x 1) - BF C cs es (Pi.single x' 1) := by
    rw [sub_eq_add_neg, BF_add_right]
    have : (-(Pi.single x' (1 : ℝ)) : Fin n → ℝ) = (-1 : ℝ) • Pi.single x' (1 : ℝ) := by simp
    rw [this, BF_smul_right]; ring
  linarith

end chain



#print axioms ex
#print axioms dlt
#print axioms ex_add
#print axioms ex_smul
#print axioms dlt_add
#print axioms dlt_smul
#print axioms ex_cont
#print axioms dlt_cont
#print axioms aF
#print axioms bF
#print axioms qF
#print axioms aF_cont
#print axioms bF_cont
#print axioms aF_smul
#print axioms bF_smul
#print axioms bF_nonneg
#print axioms Vsub
#print axioms mem_Vsub
#print axioms aF_nonneg
#print axioms ex_zero_of_const
#print axioms aF_pos
#print axioms BF
#print axioms qF_add
#print axioms BF_smul_right
#print axioms BF_add_right
#print axioms qF_smul
#print axioms quad_neg_exists
#print axioms radical_of_psd
#print axioms chain_crossing
#print axioms chain_mult_const

end AdalyFormal.CoverJacobi

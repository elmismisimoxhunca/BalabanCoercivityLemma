import NsCvOK8

/-!
# NuC1 -- the single-negative-edge chain form and its first crossing (lane ncwdh_ell2_20261018)

`qF1 C c e = aF e - (1 - c) (e_{C+1} - e_C)^2`: unit weights on all edges except the single edge `(C, C+1)` of weight `c`.
Copy of `CvK1` (two layer edges) for ONE layer edge.  `chain_crossing1`: a negative value at `c1 < 1` on the constraint space `Vsub rowOf` gives the first crossing
`cs`, a null vector, positivity beyond, and the radical identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.CoverJacobi

section chain
variable {n : ℕ}

def bF1 (C : ℕ) (e : Fin n → ℝ) : ℝ := (dlt e C) ^ 2

def qF1 (C : ℕ) (c : ℝ) (e : Fin n → ℝ) : ℝ := aF e - (1 - c) * bF1 C e

def BF1 (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : ℝ :=
  (∑ y ∈ range (n - 1), dlt e y * dlt f y) - (1 - c) * (dlt e C * dlt f C)

theorem bF1_cont (C : ℕ) : Continuous (fun e : Fin n → ℝ => bF1 C e) := by
  unfold bF1; exact (dlt_cont _).pow 2

theorem bF1_smul (C : ℕ) (r : ℝ) (e : Fin n → ℝ) : bF1 C (r • e) = r ^ 2 * bF1 C e := by
  unfold bF1; rw [dlt_smul]; ring

theorem bF1_nonneg (C : ℕ) (e : Fin n → ℝ) : 0 ≤ bF1 C e := by
  unfold bF1; positivity

theorem qF1_add (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : qF1 C c (e + f) = qF1 C c e + 2 * BF1 C c e f + qF1 C c f := by
  unfold qF1 aF bF1 BF1
  simp only [dlt_add]
  have : ∑ y ∈ range (n - 1), (dlt e y + dlt f y) ^ 2 =
      ∑ y ∈ range (n - 1), (dlt e y) ^ 2 + 2 * ∑ y ∈ range (n - 1), dlt e y * dlt f y + ∑ y ∈ range (n - 1), (dlt f y) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF1_smul_right (C : ℕ) (c t : ℝ) (e f : Fin n → ℝ) : BF1 C c e (t • f) = t * BF1 C c e f := by
  unfold BF1
  simp only [dlt_smul]
  have : ∑ y ∈ range (n - 1), dlt e y * (t * dlt f y) = t * ∑ y ∈ range (n - 1), dlt e y * dlt f y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF1_add_right (C : ℕ) (c : ℝ) (e f g : Fin n → ℝ) : BF1 C c e (f + g) = BF1 C c e f + BF1 C c e g := by
  unfold BF1
  simp only [dlt_add]
  have : ∑ y ∈ range (n - 1), dlt e y * (dlt f y + dlt g y) =
      ∑ y ∈ range (n - 1), dlt e y * dlt f y + ∑ y ∈ range (n - 1), dlt e y * dlt g y := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF1_comm (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : BF1 C c e f = BF1 C c f e := by
  unfold BF1
  have : ∑ y ∈ range (n - 1), dlt e y * dlt f y = ∑ y ∈ range (n - 1), dlt f y * dlt e y :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF1_self (C : ℕ) (c : ℝ) (e : Fin n → ℝ) : BF1 C c e e = qF1 C c e := by
  unfold BF1 qF1 aF bF1
  have : ∑ y ∈ range (n - 1), dlt e y * dlt e y = ∑ y ∈ range (n - 1), (dlt e y) ^ 2 :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem BF1_smul_left (C : ℕ) (c t : ℝ) (e f : Fin n → ℝ) : BF1 C c (t • e) f = t * BF1 C c e f := by
  rw [BF1_comm, BF1_smul_right, BF1_comm]

theorem BF1_add_left (C : ℕ) (c : ℝ) (e f g : Fin n → ℝ) : BF1 C c (e + f) g = BF1 C c e g + BF1 C c f g := by
  rw [BF1_comm, BF1_add_right, BF1_comm C c g e, BF1_comm C c g f]

theorem qF1_smul (C : ℕ) (c t : ℝ) (e : Fin n → ℝ) : qF1 C c (t • e) = t ^ 2 * qF1 C c e := by
  unfold qF1; rw [aF_smul, bF1_smul]; ring

theorem qF1_affine (C : ℕ) (c cs : ℝ) (e : Fin n → ℝ) : qF1 C c e = qF1 C cs e + (c - cs) * bF1 C e := by
  unfold qF1; ring

/-- a null vector of a positive semidefinite form is in its radical. -/
theorem radical_of_psd1 (rowOf : ℕ → ℕ) (C : ℕ) (c : ℝ) (es : Fin n → ℝ) (hes : es ∈ Vsub rowOf)
    (hpsd : ∀ e : Fin n → ℝ, e ∈ Vsub rowOf → 0 ≤ qF1 C c e) (h0 : qF1 C c es = 0) :
    ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF1 C c es d = 0 := by
  intro d hd
  by_contra hB
  obtain ⟨t, ht⟩ := quad_neg_exists (BF1 C c es d) (qF1 C c d) hB (hpsd d hd)
  have hmem : es + t • d ∈ Vsub rowOf := (Vsub rowOf).add_mem hes ((Vsub rowOf).smul_mem t hd)
  have := hpsd _ hmem
  rw [qF1_add, BF1_smul_right, qF1_smul, h0] at this
  linarith

/-- the first crossing of the constrained single-edge chain form. -/
theorem chain_crossing1 (rowOf : ℕ → ℕ) (C : ℕ) (c1 : ℝ) (hc1 : c1 < 1) (e1 : Fin n → ℝ) (he1 : e1 ∈ Vsub rowOf)
    (hneg : qF1 C c1 e1 < 0) :
    ∃ cs : ℝ, c1 < cs ∧ cs < 1 ∧ (∃ es : Fin n → ℝ, es ∈ Vsub rowOf ∧ es ≠ 0 ∧ qF1 C cs es = 0) ∧
      (∀ e : Fin n → ℝ, e ∈ Vsub rowOf → 0 ≤ qF1 C cs e) ∧
      (∀ c : ℝ, cs < c → c ≤ 1 → ∀ e : Fin n → ℝ, e ∈ Vsub rowOf → e ≠ 0 → 0 < qF1 C c e) ∧
      (∀ es : Fin n → ℝ, es ∈ Vsub rowOf → qF1 C cs es = 0 → ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF1 C cs es d = 0) := by
  have hfc := first_crossing (E := Fin n → ℝ) (Vsub rowOf) aF (bF1 C) aF_cont (bF1_cont C)
    aF_smul (bF1_smul C) (bF1_nonneg C) (fun e he hne => aF_pos rowOf he hne) c1 hc1 e1 he1 hneg
  obtain ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos⟩ := hfc
  refine ⟨cs, h1, h2, ⟨es, hes, hne, h0⟩, hpsd, hpos, ?_⟩
  intro es' hes' h0' d hd
  exact radical_of_psd1 rowOf C cs es' hes' hpsd h0' d hd

/-- the row multipliers of a radical vector: `BF1 es δ_x` is constant along each row. -/
theorem chain_mult_const1 (rowOf : ℕ → ℕ) (C : ℕ) (cs : ℝ) (es : Fin n → ℝ)
    (hrad : ∀ d : Fin n → ℝ, d ∈ Vsub rowOf → BF1 C cs es d = 0) (x x' : Fin n) (hxx : rowOf x.val = rowOf x'.val) :
    BF1 C cs es (Pi.single x 1) = BF1 C cs es (Pi.single x' 1) := by
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
  have hsub : BF1 C cs es (Pi.single x 1 - Pi.single x' 1) = BF1 C cs es (Pi.single x 1) - BF1 C cs es (Pi.single x' 1) := by
    rw [sub_eq_add_neg, BF1_add_right]
    have : (-(Pi.single x' (1 : ℝ)) : Fin n → ℝ) = (-1 : ℝ) • Pi.single x' (1 : ℝ) := by simp
    rw [this, BF1_smul_right]; ring
  linarith

end chain

end AdalyFormal.NcwdhTwo

import NsCvOK6

/-!
# CvOK7 -- the blow-up bound of the constrained minimum at the first crossing (lane omega)

`blowup_bound`: let `es` be a null vector of the constrained form `qF cs` on a subspace `V` with `bF es > 0`, `qF c` nonnegative on `V` for `c in (cs, 1]`, and `f₀` with
`B_cs(f₀, es) ≠ 0`.  For every `M` there is `ε > 0` such that for `c in (cs, cs + ε)` every `f` in the affine space `f₀ + V` which is a saddle point for `qF c`
(`B_c(f, d) = 0` for all `d in V`) has `qF c f < M`.  (Since `qF c f ≤ qF c (f₀ + s es)` for all `s`, optimised in `s`.)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open Finset
open AdalyFormal.CoverJacobi

variable {n : ℕ}

theorem BF_comm (C : ℕ) (c : ℝ) (e f : Fin n → ℝ) : BF C c e f = BF C c f e := by
  unfold BF
  have : ∑ y ∈ range (n - 1), dlt e y * dlt f y = ∑ y ∈ range (n - 1), dlt f y * dlt e y :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

/-- `B_c` is affine in `c`. -/
theorem BF_affine (C : ℕ) (c cs : ℝ) (e f : Fin n → ℝ) :
    BF C c e f = BF C cs e f + (c - cs) * (dlt e (C - 1) * dlt f (C - 1) + dlt e C * dlt f C) := by
  unfold BF; ring

theorem qF_affine (C : ℕ) (c cs : ℝ) (e : Fin n → ℝ) :
    qF C c e = qF C cs e + (c - cs) * bF C e := by
  unfold qF; ring

theorem BF_self (C : ℕ) (c : ℝ) (e : Fin n → ℝ) : BF C c e e = qF C c e := by
  unfold BF qF aF bF
  have : ∑ y ∈ range (n - 1), dlt e y * dlt e y = ∑ y ∈ range (n - 1), (dlt e y) ^ 2 :=
    Finset.sum_congr rfl (fun y _ => by ring)
  rw [this]; ring

theorem blowup_bound (C : ℕ) (V : Submodule ℝ (Fin n → ℝ)) (cs : ℝ) (es f₀ : Fin n → ℝ) (hes : es ∈ V)
    (hcs1 : -1 ≤ cs) (h0 : qF C cs es = 0) (hbF : 0 < bF C es) (hP : BF C cs f₀ es ≠ 0)
    (hpos : ∀ c : ℝ, cs < c → c ≤ 1 → ∀ d ∈ V, 0 ≤ qF C c d) (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, cs < c → c < cs + ε → c ≤ 1 → ∀ f : Fin n → ℝ, f - f₀ ∈ V →
      (∀ d ∈ V, BF C c f d = 0) → qF C c f < M := by
  set P := BF C cs f₀ es with hPdef
  set Lc := dlt f₀ (C - 1) * dlt es (C - 1) + dlt f₀ C * dlt es C with hLc
  set Q0 := |aF f₀| + 2 * |bF C f₀| with hQ0
  set bb := bF C es with hbb
  have hP2 : 0 < P ^ 2 := by positivity
  -- smallness of the cross term
  set ε1 := |P| / (2 * |Lc| + 1) with hε1
  have hε1pos : 0 < ε1 := by positivity
  -- target: (c - cs) < P^2 / (4 bb (|Q0| + |M| + 1))
  set ε2 := P ^ 2 / (4 * bb * (|Q0| + |M| + 1)) with hε2
  have hε2pos : 0 < ε2 := by
    have : 0 < |Q0| + |M| + 1 := by positivity
    positivity
  refine ⟨min ε1 (min ε2 1), by positivity, ?_⟩
  intro c hcs hcε hc1 f hfV hsad
  have hm1 := min_le_left ε1 (min ε2 1)
  have hm2 : min ε1 (min ε2 1) ≤ min ε2 1 := min_le_right _ _
  have hm3 := min_le_left ε2 1
  have hm4 := min_le_right ε2 1
  have hε1' : c - cs < ε1 := by linarith
  have hε2' : c - cs < ε2 := by linarith
  have hε3' : c - cs < 1 := by linarith
  have hd : 0 < c - cs := by linarith
  -- B_c(f0, es)
  have hBc : BF C c f₀ es = P + (c - cs) * Lc := by rw [BF_affine C c cs]
  have hBlow : |P| / 2 ≤ |BF C c f₀ es| := by
    rw [hBc]
    have h1 : |(c - cs) * Lc| ≤ |P| / 2 := by
      rw [abs_mul, abs_of_pos hd]
      have : (c - cs) * |Lc| ≤ ε1 * |Lc| := mul_le_mul_of_nonneg_right hε1'.le (abs_nonneg _)
      have h2 : ε1 * |Lc| ≤ |P| / 2 := by
        rw [hε1]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg Lc, abs_nonneg P]
      linarith
    calc |P| / 2 = |P| - |P| / 2 := by ring
      _ ≤ |P| - |(c - cs) * Lc| := by linarith
      _ ≤ |P + (c - cs) * Lc| := by
        have := abs_sub_abs_le_abs_sub P (-((c - cs) * Lc))
        rw [abs_neg] at this
        simpa [sub_neg_eq_add] using this
  have hB2 : P ^ 2 / 4 ≤ (BF C c f₀ es) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg P, neg_abs_le P, abs_nonneg (BF C c f₀ es), neg_abs_le (BF C c f₀ es)] : -|BF C c f₀ es| ≤ |P| / 2) (by linarith : |P| / 2 ≤ |BF C c f₀ es|)
    nlinarith [sq_abs P, sq_abs (BF C c f₀ es), hBlow, abs_nonneg P]
  -- the comparison vector
  set s := -(BF C c f₀ es) / ((c - cs) * bb) with hs
  have hqes : qF C c es = (c - cs) * bb := by rw [qF_affine C c cs, h0]; ring
  have hmem : (f₀ + s • es) - f ∈ V := by
    have : (f₀ + s • es) - f = s • es - (f - f₀) := by abel
    rw [this]
    exact V.sub_mem (V.smul_mem s hes) hfV
  have hineq : qF C c f ≤ qF C c (f₀ + s • es) := by
    have e1 : f₀ + s • es = f + ((f₀ + s • es) - f) := by abel
    have hpd := hpos c hcs hc1 _ hmem
    rw [e1, qF_add, hsad _ hmem]
    nlinarith [hpd]
  have hval : qF C c (f₀ + s • es) = qF C c f₀ - (BF C c f₀ es) ^ 2 / ((c - cs) * bb) := by
    rw [qF_add, BF_smul_right, qF_smul, hqes, hs]
    field_simp
    ring
  have hqf0 : qF C c f₀ ≤ Q0 := by
    unfold qF
    have h1 : aF f₀ ≤ |aF f₀| := le_abs_self _
    have h2 : -((1 - c) * bF C f₀) ≤ 2 * |bF C f₀| := by
      have : |(1 - c) * bF C f₀| ≤ 2 * |bF C f₀| := by
        rw [abs_mul]
        have : |1 - c| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [hd, hε3', hcs, hcs1]
        nlinarith [abs_nonneg (bF C f₀)]
      have := neg_abs_le ((1 - c) * bF C f₀)
      linarith
    nlinarith [abs_nonneg (aF f₀), abs_nonneg (bF C f₀)]
  have hfrac : P ^ 2 / (4 * ((c - cs) * bb)) ≤ (BF C c f₀ es) ^ 2 / ((c - cs) * bb) := by
    have hpos' : 0 < (c - cs) * bb := by positivity
    rw [div_le_div_iff₀ (by positivity) hpos']
    nlinarith [hB2]
  have hbig : |Q0| + |M| + 1 ≤ P ^ 2 / (4 * ((c - cs) * bb)) := by
    have hpos' : 0 < (c - cs) * bb := by positivity
    rw [le_div_iff₀ (by positivity)]
    have : (c - cs) < P ^ 2 / (4 * bb * (|Q0| + |M| + 1)) := hε2'
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hQ0abs : Q0 ≤ |Q0| := le_abs_self _
  have hMabs : -|M| ≤ M := neg_abs_le M
  have hM1 : M ≤ |M| := le_abs_self M
  linarith

#print axioms blowup_bound

end AdalyFormal.CoverOmega

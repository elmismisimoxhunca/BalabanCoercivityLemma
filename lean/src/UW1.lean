import UZ5

/-!
# UW1 -- one-directional box averages of `M2`-valued fields on ℤ³ (lane unif_20261016)

`Av τ n f x = (2n+1)⁻¹ Σ_{k<2n+1} f (x + (k − n) e_τ)` (window of radius `n` along `τ`).  With `D1 τ f D` (every `τ`-difference
of `f` is `≤ D`, everywhere) and `SupB f B` (`|f| ≤ B` everywhere):
* `av_diff`        : `Av f (x+e_τ) − Av f x = (2n+1)⁻¹ (f(x+(n+1)e_τ) − f(x−n e_τ))`;
* `av_d1`          : `|Δ_τ Av f| ≤ D`;  `av_d1_sup` : `|Δ_τ Av h| ≤ 2B/(2n+1)`;
* `av_step`        : `Av (n+1) f − Av n f = (2n+3)⁻¹ (f(x+(n+1)e_τ) + f(x−(n+1)e_τ) − 2 Av n f)`;
* `av_step_d1`     : `|Av (n+1) f − Av n f| ≤ 2D`;  `av_step_sup` : `≤ 4B/(2n+3)`;
* `av_step_dd`     : `|Δ_τ (Av (n+1) f − Av n f)| ≤ 4D/(2n+3)`;
* `av_step2`       : `|Av (n+2) f − 2 Av (n+1) f + Av n f| ≤ 10 D/(2n+5)`;
* `av_sup`, `av_sub`, `av_shift` (linearity, contraction, shifts in any direction commute).
Reusable (no lattice-gauge content).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (frobNorm_sub_le' frobNorm_sub_comm)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

/-- the average along `τ`, radius `n`. -/
noncomputable def Av (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (x : Z3) : M2 :=
  ((2 * (n : ℝ) + 1)⁻¹) • ∑ k ∈ Finset.range (2 * n + 1), f (x + ((k : ℤ) - n) • ev τ)

/-- all `τ`-differences bounded by `D`. -/
def D1 (τ : Fin 3) (f : Z3 → M2) (D : ℝ) : Prop := ∀ y, frobNorm (f (y + ev τ) - f y) ≤ D

/-- `|f| ≤ B` everywhere. -/
def SupB (f : Z3 → M2) (B : ℝ) : Prop := ∀ y, frobNorm (f y) ≤ B

theorem frobNorm_sum_le {ι : Type*} (s : Finset ι) (g : ι → M2) :
    frobNorm (∑ i ∈ s, g i) ≤ ∑ i ∈ s, frobNorm (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (frobNorm_add_le _ _).trans (by linarith)

theorem pos2n1 (n : ℕ) : (0 : ℝ) < 2 * n + 1 := by positivity

theorem av_shift (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (x e : Z3) :
    Av τ n f (x + e) = Av τ n (fun y => f (y + e)) x := by
  unfold Av; congr 1; refine Finset.sum_congr rfl (fun k _ => ?_); congr 1; abel

theorem av_sub (τ : Fin 3) (n : ℕ) (f g : Z3 → M2) (x : Z3) :
    Av τ n f x - Av τ n g x = Av τ n (fun y => f y - g y) x := by
  unfold Av; rw [← smul_sub, ← Finset.sum_sub_distrib]

theorem av_sup {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {B : ℝ} (h : ∀ y, frobNorm (f y) ≤ B) (x : Z3) :
    frobNorm (Av τ n f x) ≤ B := by
  unfold Av
  rw [frobNorm_smul, abs_of_pos (inv_pos.mpr (pos2n1 n))]
  have h1 := frobNorm_sum_le (Finset.range (2 * n + 1)) (fun k => f (x + ((k : ℤ) - n) • ev τ))
  have h2 : ∑ k ∈ Finset.range (2 * n + 1), frobNorm (f (x + ((k : ℤ) - n) • ev τ))
      ≤ ∑ k ∈ Finset.range (2 * n + 1), B := Finset.sum_le_sum (fun k _ => h _)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  push_cast at h2
  rw [inv_mul_le_iff₀ (pos2n1 n)]
  linarith

/-- telescoping along `τ`. -/
theorem tele (τ : Fin 3) (f : Z3 → M2) (x : Z3) (m : ℕ) :
    ∑ k ∈ Finset.range m, (f (x + ((k : ℤ) + 1) • ev τ) - f (x + (k : ℤ) • ev τ)) = f (x + (m : ℤ) • ev τ) - f x := by
  have := Finset.sum_range_sub (fun k : ℕ => f (x + (k : ℤ) • ev τ)) m
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_smul, add_zero] at this
  exact this

theorem d1_far {τ : Fin 3} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (x : Z3) (m : ℕ) :
    frobNorm (f (x + (m : ℤ) • ev τ) - f x) ≤ m * D := by
  rw [← tele τ f x m]
  refine (frobNorm_sum_le _ _).trans ?_
  have := Finset.sum_le_sum (s := Finset.range m) (fun k _ => by
    have := h (x + (k : ℤ) • ev τ)
    rw [show x + (k : ℤ) • ev τ + ev τ = x + ((k : ℤ) + 1) • ev τ by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring] at this
    exact this)
  simpa using this

theorem av_diff (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (x : Z3) :
    Av τ n f (x + ev τ) - Av τ n f x
      = ((2 * (n : ℝ) + 1)⁻¹) • (f (x + ((n : ℤ) + 1) • ev τ) - f (x - (n : ℤ) • ev τ)) := by
  unfold Av
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  have := tele τ f (x - (n : ℤ) • ev τ) (2 * n + 1)
  have e1 : ∀ k : ℕ, x + ev τ + ((k : ℤ) - n) • ev τ = x - (n : ℤ) • ev τ + ((k : ℤ) + 1) • ev τ := by
    intro k; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e2 : ∀ k : ℕ, x + ((k : ℤ) - n) • ev τ = x - (n : ℤ) • ev τ + (k : ℤ) • ev τ := by
    intro k; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e1, e2]
  rw [this]
  congr 1
  push_cast
  rw [show x - (n : ℤ) • ev τ + (2 * (n : ℤ) + 1) • ev τ = x + ((n : ℤ) + 1) • ev τ by
    funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring]

theorem av_d1_sup {τ : Fin 3} {n : ℕ} {h : Z3 → M2} {B : ℝ} (hB : SupB h B) (x : Z3) :
    frobNorm (Av τ n h (x + ev τ) - Av τ n h x) ≤ 2 * B / (2 * n + 1) := by
  rw [av_diff, frobNorm_smul, abs_of_pos (inv_pos.mpr (pos2n1 n))]
  have h1 := frobNorm_sub_le' (h (x + ((n : ℤ) + 1) • ev τ)) 0 (h (x - (n : ℤ) • ev τ))
  rw [sub_zero, zero_sub, frobNorm_neg] at h1
  have h2 := hB (x + ((n : ℤ) + 1) • ev τ)
  have h3 := hB (x - (n : ℤ) • ev τ)
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (pos2n1 n).le)

theorem av_d1 {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (hD : D1 τ f D) (x : Z3) :
    frobNorm (Av τ n f (x + ev τ) - Av τ n f x) ≤ D := by
  rw [av_diff, frobNorm_smul, abs_of_pos (inv_pos.mpr (pos2n1 n))]
  have h := d1_far hD (x - (n : ℤ) • ev τ) (2 * n + 1)
  rw [show x - (n : ℤ) • ev τ + ((2 * n + 1 : ℕ) : ℤ) • ev τ = x + ((n : ℤ) + 1) • ev τ by
    funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring] at h
  push_cast at h
  rw [inv_mul_le_iff₀ (pos2n1 n)]
  linarith

/-- the radius step. -/
theorem av_step (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (x : Z3) :
    Av τ (n + 1) f x - Av τ n f x
      = ((2 * (n : ℝ) + 3)⁻¹) • (f (x + ((n : ℤ) + 1) • ev τ) + f (x - ((n : ℤ) + 1) • ev τ) - (2 : ℝ) • Av τ n f x) := by
  set S := ∑ k ∈ Finset.range (2 * n + 1), f (x + ((k : ℤ) - n) • ev τ) with hS
  have hS1 : ∑ k ∈ Finset.range (2 * (n + 1) + 1), f (x + ((k : ℤ) - (n + 1 : ℕ)) • ev τ)
      = f (x - ((n : ℤ) + 1) • ev τ) + S + f (x + ((n : ℤ) + 1) • ev τ) := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ']
    have e0 : f (x + (((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) • ev τ) = f (x - ((n : ℤ) + 1) • ev τ) := by
      congr 1; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    have eS : ∑ k ∈ Finset.range (2 * n + 1), f (x + (((k + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) • ev τ) = S := by
      rw [hS]; refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    have eL : f (x + (((2 * n + 1 + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) • ev τ) = f (x + ((n : ℤ) + 1) • ev τ) := by
      congr 1; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    rw [e0, eS, eL]; abel
  have hA : S = (2 * (n : ℝ) + 1) • Av τ n f x := by
    unfold Av; rw [← hS, smul_smul, mul_inv_cancel₀ (pos2n1 n).ne', one_smul]
  have hN : Av τ (n + 1) f x = ((2 * (n : ℝ) + 3)⁻¹) • (f (x - ((n : ℤ) + 1) • ev τ) + S + f (x + ((n : ℤ) + 1) • ev τ)) := by
    unfold Av; rw [hS1]; congr 1; push_cast; ring_nf
  rw [hN, hA]
  set A := Av τ n f x
  set fp := f (x + ((n : ℤ) + 1) • ev τ)
  set fm := f (x - ((n : ℤ) + 1) • ev τ)
  have hc : (2 * (n : ℝ) + 3)⁻¹ * (2 * (n : ℝ) + 1) - 1 = -(2 * (2 * (n : ℝ) + 3)⁻¹) := by
    have : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    field_simp; ring
  have k1 : (2 * (n : ℝ) + 3)⁻¹ • (fm + (2 * (n : ℝ) + 1) • A + fp) - A
      = (2 * (n : ℝ) + 3)⁻¹ • (fp + fm) + ((2 * (n : ℝ) + 3)⁻¹ * (2 * (n : ℝ) + 1) - 1) • A := by module
  have k2 : (2 * (n : ℝ) + 3)⁻¹ • (fp + fm - (2 : ℝ) • A)
      = (2 * (n : ℝ) + 3)⁻¹ • (fp + fm) + (-(2 * (2 * (n : ℝ) + 3)⁻¹)) • A := by module
  rw [k1, k2, hc]

theorem av_sup_win {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {B : ℝ} (x : Z3)
    (h : ∀ k : ℕ, k < 2 * n + 1 → frobNorm (f (x + ((k : ℤ) - n) • ev τ)) ≤ B) :
    frobNorm (Av τ n f x) ≤ B := by
  unfold Av
  rw [frobNorm_smul, abs_of_pos (inv_pos.mpr (pos2n1 n))]
  have h1 := frobNorm_sum_le (Finset.range (2 * n + 1)) (fun k => f (x + ((k : ℤ) - n) • ev τ))
  have h2 : ∑ k ∈ Finset.range (2 * n + 1), frobNorm (f (x + ((k : ℤ) - n) • ev τ))
      ≤ ∑ k ∈ Finset.range (2 * n + 1), B := Finset.sum_le_sum (fun k hk => h k (Finset.mem_range.mp hk))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  push_cast at h2
  rw [inv_mul_le_iff₀ (pos2n1 n)]
  linarith

theorem av_const (τ : Fin 3) (n : ℕ) (g : M2) (x : Z3) : Av τ n (fun _ => g) x = g := by
  unfold Av
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pos2n1 n).ne', one_smul]

theorem d1_far_int {τ : Fin 3} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (hD : 0 ≤ D) (x : Z3) (a b : ℤ) :
    frobNorm (f (x + a • ev τ) - f (x + b • ev τ)) ≤ ((|a - b| : ℤ) : ℝ) * D := by
  rcases le_total b a with hab | hab
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, a - b = m := ⟨(a - b).toNat, by omega⟩
    have := d1_far h (x + b • ev τ) m
    have ex : x + b • ev τ + (m : ℤ) • ev τ = x + a • ev τ := by
      rw [← hm]; funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [ex] at this
    rw [hm, abs_of_nonneg (by positivity)]; exact_mod_cast this
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, b - a = m := ⟨(b - a).toNat, by omega⟩
    have := d1_far h (x + a • ev τ) m
    have ex : x + a • ev τ + (m : ℤ) • ev τ = x + b • ev τ := by
      rw [← hm]; funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [ex] at this
    rw [frobNorm_sub_comm, abs_sub_comm, hm, abs_of_nonneg (by positivity)]; exact_mod_cast this

/-- distance of a far point to the window average. -/
theorem far_av {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (hD : 0 ≤ D) (x : Z3) (a : ℤ)
    (ha : |a| = n + 1) : frobNorm (f (x + a • ev τ) - Av τ n f x) ≤ (2 * n + 1) * D := by
  rw [← av_const τ n (f (x + a • ev τ)) x, av_sub]
  refine av_sup_win x (fun k hk => ?_)
  have := d1_far_int h hD x a ((k : ℤ) - n)
  refine this.trans (mul_le_mul_of_nonneg_right ?_ hD)
  have hk' : (k : ℤ) ≤ 2 * n := by omega
  have hb : |a - ((k : ℤ) - n)| ≤ 2 * n + 1 := by
    rcases abs_eq (by positivity : (0 : ℤ) ≤ n + 1) |>.mp ha with h1 | h1 <;>
    · rw [h1, abs_le]; constructor <;> omega
  exact_mod_cast hb

theorem av_step_d1 {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (hD : 0 ≤ D) (x : Z3) :
    frobNorm (Av τ (n + 1) f x - Av τ n f x) ≤ 2 * D := by
  rw [av_step, frobNorm_smul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * n + 3))]
  have hp := far_av h hD x ((n : ℤ) + 1) (by rw [abs_of_nonneg (by positivity)])
  have hm := far_av h hD x (-((n : ℤ) + 1)) (by rw [abs_neg, abs_of_nonneg (by positivity)])
  rw [show x + (-((n : ℤ) + 1)) • ev τ = x - ((n : ℤ) + 1) • ev τ by rw [neg_smul]; abel] at hm
  have e : f (x + ((n : ℤ) + 1) • ev τ) + f (x - ((n : ℤ) + 1) • ev τ) - (2 : ℝ) • Av τ n f x
      = (f (x + ((n : ℤ) + 1) • ev τ) - Av τ n f x) + (f (x - ((n : ℤ) + 1) • ev τ) - Av τ n f x) := by
    rw [two_smul]; abel
  rw [e]
  have h3 := frobNorm_add_le (f (x + ((n : ℤ) + 1) • ev τ) - Av τ n f x) (f (x - ((n : ℤ) + 1) • ev τ) - Av τ n f x)
  rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 * n + 3)]
  nlinarith

theorem av_step_sup {τ : Fin 3} {n : ℕ} {h : Z3 → M2} {B : ℝ} (hB : SupB h B) (x : Z3) :
    frobNorm (Av τ (n + 1) h x - Av τ n h x) ≤ 4 * B / (2 * n + 3) := by
  rw [av_step, frobNorm_smul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * n + 3))]
  have hA := av_sup (τ := τ) (n := n) hB x
  have e := frobNorm_add_le (h (x + ((n : ℤ) + 1) • ev τ) + h (x - ((n : ℤ) + 1) • ev τ)) (-((2 : ℝ) • Av τ n h x))
  rw [← sub_eq_add_neg, frobNorm_neg, frobNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at e
  have e2 := frobNorm_add_le (h (x + ((n : ℤ) + 1) • ev τ)) (h (x - ((n : ℤ) + 1) • ev τ))
  have := hB (x + ((n : ℤ) + 1) • ev τ); have := hB (x - ((n : ℤ) + 1) • ev τ)
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (by positivity))

theorem av_step_dd {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (x : Z3) :
    frobNorm ((Av τ (n + 1) f (x + ev τ) - Av τ n f (x + ev τ)) - (Av τ (n + 1) f x - Av τ n f x))
      ≤ 4 * D / (2 * n + 3) := by
  rw [av_step, av_step, ← smul_sub, frobNorm_smul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * n + 3))]
  have hd := av_d1 (n := n) h x
  have h1 := h (x + ((n : ℤ) + 1) • ev τ)
  have h2 := h (x - ((n : ℤ) + 1) • ev τ)
  rw [show x + ((n : ℤ) + 1) • ev τ + ev τ = x + ev τ + ((n : ℤ) + 1) • ev τ by abel] at h1
  rw [show x - ((n : ℤ) + 1) • ev τ + ev τ = x + ev τ - ((n : ℤ) + 1) • ev τ by abel] at h2
  have e : f (x + ev τ + ((n : ℤ) + 1) • ev τ) + f (x + ev τ - ((n : ℤ) + 1) • ev τ) - (2 : ℝ) • Av τ n f (x + ev τ)
      - (f (x + ((n : ℤ) + 1) • ev τ) + f (x - ((n : ℤ) + 1) • ev τ) - (2 : ℝ) • Av τ n f x)
      = (f (x + ev τ + ((n : ℤ) + 1) • ev τ) - f (x + ((n : ℤ) + 1) • ev τ))
        + (f (x + ev τ - ((n : ℤ) + 1) • ev τ) - f (x - ((n : ℤ) + 1) • ev τ))
        - (2 : ℝ) • (Av τ n f (x + ev τ) - Av τ n f x) := by module
  rw [e]
  have h3 := frobNorm_add_le ((f (x + ev τ + ((n : ℤ) + 1) • ev τ) - f (x + ((n : ℤ) + 1) • ev τ))
        + (f (x + ev τ - ((n : ℤ) + 1) • ev τ) - f (x - ((n : ℤ) + 1) • ev τ)))
        (-((2 : ℝ) • (Av τ n f (x + ev τ) - Av τ n f x)))
  rw [← sub_eq_add_neg, frobNorm_neg, frobNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
  have h4 := frobNorm_add_le (f (x + ev τ + ((n : ℤ) + 1) • ev τ) - f (x + ((n : ℤ) + 1) • ev τ))
        (f (x + ev τ - ((n : ℤ) + 1) • ev τ) - f (x - ((n : ℤ) + 1) • ev τ))
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (by positivity))

theorem av_step2 {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) (hD : 0 ≤ D) (x : Z3) :
    frobNorm ((Av τ (n + 2) f x - Av τ (n + 1) f x) - (Av τ (n + 1) f x - Av τ n f x)) ≤ 10 * D / (2 * n + 5) := by
  have s1 := av_step τ (n + 1) f x
  have s0 := av_step τ n f x
  rw [show n + 1 + 1 = n + 2 by ring] at s1
  rw [s1, s0]
  set fp0 := f (x + ((n : ℤ) + 1) • ev τ)
  set fm0 := f (x - ((n : ℤ) + 1) • ev τ)
  set fp1 := f (x + (((n + 1 : ℕ) : ℤ) + 1) • ev τ)
  set fm1 := f (x - (((n + 1 : ℕ) : ℤ) + 1) • ev τ)
  set A0 := Av τ n f x
  set A1 := Av τ (n + 1) f x
  set E0 := fp0 + fm0 - (2 : ℝ) • A0
  set E1 := fp1 + fm1 - (2 : ℝ) • A1
  have hc1 : (2 * ((n + 1 : ℕ) : ℝ) + 3) = 2 * n + 5 := by push_cast; ring
  rw [hc1]
  have hp3 : (0 : ℝ) < 2 * n + 3 := by positivity
  have hp5 : (0 : ℝ) < 2 * n + 5 := by positivity
  have e : (2 * (n : ℝ) + 5)⁻¹ • E1 - (2 * (n : ℝ) + 3)⁻¹ • E0
      = (2 * (n : ℝ) + 5)⁻¹ • (E1 - E0) + ((2 * (n : ℝ) + 5)⁻¹ - (2 * (n : ℝ) + 3)⁻¹) • E0 := by module
  rw [e]
  -- |E0| ≤ 2(2n+1)D
  have hfp := far_av h hD x ((n : ℤ) + 1) (by rw [abs_of_nonneg (by positivity)])
  have hfm := far_av h hD x (-((n : ℤ) + 1)) (by rw [abs_neg, abs_of_nonneg (by positivity)])
  rw [show x + (-((n : ℤ) + 1)) • ev τ = x - ((n : ℤ) + 1) • ev τ by rw [neg_smul]; abel] at hfm
  have hE0 : frobNorm E0 ≤ 2 * (2 * n + 1) * D := by
    have e0 : E0 = (fp0 - A0) + (fm0 - A0) := by simp only [E0]; rw [two_smul]; abel
    rw [e0]; have := frobNorm_add_le (fp0 - A0) (fm0 - A0); linarith
  -- |E1 - E0| ≤ 6D
  have d1 : frobNorm (fp1 - fp0) ≤ D := by
    have := h (x + ((n : ℤ) + 1) • ev τ)
    rw [show x + ((n : ℤ) + 1) • ev τ + ev τ = x + (((n + 1 : ℕ) : ℤ) + 1) • ev τ by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring] at this
    exact this
  have d2 : frobNorm (fm1 - fm0) ≤ D := by
    have := h (x - (((n + 1 : ℕ) : ℤ) + 1) • ev τ)
    rw [show x - (((n + 1 : ℕ) : ℤ) + 1) • ev τ + ev τ = x - ((n : ℤ) + 1) • ev τ by
      funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring] at this
    rw [frobNorm_sub_comm]; exact this
  have d3 := av_step_d1 (n := n) h hD x
  have hE10 : frobNorm (E1 - E0) ≤ 6 * D := by
    have e1 : E1 - E0 = (fp1 - fp0) + (fm1 - fm0) - (2 : ℝ) • (A1 - A0) := by simp only [E1, E0]; module
    rw [e1]
    have := frobNorm_add_le ((fp1 - fp0) + (fm1 - fm0)) (-((2 : ℝ) • (A1 - A0)))
    rw [← sub_eq_add_neg, frobNorm_neg, frobNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    have := frobNorm_add_le (fp1 - fp0) (fm1 - fm0)
    linarith
  have t1 := frobNorm_add_le ((2 * (n : ℝ) + 5)⁻¹ • (E1 - E0)) (((2 * (n : ℝ) + 5)⁻¹ - (2 * (n : ℝ) + 3)⁻¹) • E0)
  rw [frobNorm_smul, frobNorm_smul, abs_of_pos (inv_pos.mpr hp5)] at t1
  have hcd : |(2 * (n : ℝ) + 5)⁻¹ - (2 * (n : ℝ) + 3)⁻¹| = 2 / ((2 * n + 3) * (2 * n + 5)) := by
    rw [abs_sub_comm, abs_of_nonneg (by
      rw [sub_nonneg]; exact inv_anti₀ hp3 (by linarith))]
    field_simp; ring
  rw [hcd] at t1
  have hD0 := hD
  have k1 : (2 * (n : ℝ) + 5)⁻¹ * frobNorm (E1 - E0) ≤ 6 * D / (2 * n + 5) := by
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hE10 (inv_nonneg.mpr hp5.le)
  have k2 : 2 / ((2 * n + 3) * (2 * n + 5)) * frobNorm E0 ≤ 4 * D / (2 * n + 5) := by
    have : 2 / ((2 * (n : ℝ) + 3) * (2 * n + 5)) * frobNorm E0 ≤ 2 / ((2 * (n : ℝ) + 3) * (2 * n + 5)) * (2 * (2 * n + 1) * D) :=
      mul_le_mul_of_nonneg_left hE0 (by positivity)
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hp5]
    nlinarith
  have : 6 * D / (2 * n + 5) + 4 * D / (2 * n + 5) = 10 * D / (2 * n + 5) := by ring
  linarith

end AdalyFormal.UnifLane.Z

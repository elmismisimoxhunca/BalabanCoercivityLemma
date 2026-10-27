import UW1

/-!
# UW2 -- two-directional (plane) box averages (lane unif_20261016)

`P2 τ₁ τ₂ n f = Av τ₁ n (Av τ₂ n f)` (square window of radius `n` in the plane spanned by `e_{τ₁}, e_{τ₂}`).
For `f` with all `e_{τ₁}`- and `e_{τ₂}`-differences `≤ D`:
* `p2_d1`     : every first difference (any direction `e` with `D1 e f D`) of `P2 n f` is `≤ D`;
* `p2_dd`     : plane second differences `|P(x+e+e') − P(x+e) − P(x+e') + P(x)| ≤ 2D/(2n+1)` (`e ∈ {τ₁,τ₂}`, `e'` any with `D1 e' f D`);
* `p2_step`   : `|P2 (n+1) f − P2 n f| ≤ 4D`;
* `p2_step_d` : `|Δ_e (P2 (n+1) f − P2 n f)| ≤ 8D/(2n+1)` (`e ∈ {τ₁,τ₂}`);
* `p2_step2`  : `|P2 (n+2) f − 2 P2 (n+1) f + P2 n f| ≤ 36 D/(2n+3)`.
Reusable.
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

/-- first differences along an arbitrary vector `e`. -/
def D1v (e : Z3) (f : Z3 → M2) (D : ℝ) : Prop := ∀ y, frobNorm (f (y + e) - f y) ≤ D

theorem D1v_of_D1 {τ : Fin 3} {f : Z3 → M2} {D : ℝ} (h : D1 τ f D) : D1v (ev τ) f D := h

/-- differences commute with averages. -/
theorem av_diff_v (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (x e : Z3) :
    Av τ n f (x + e) - Av τ n f x = Av τ n (fun y => f (y + e) - f y) x := by
  rw [av_shift, av_sub]

theorem av_D1v {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {e : Z3} {D : ℝ} (h : D1v e f D) : D1v e (Av τ n f) D :=
  fun y => by rw [av_diff_v]; exact av_sup h y

theorem av_SupB {τ : Fin 3} {n : ℕ} {f : Z3 → M2} {B : ℝ} (h : SupB f B) : SupB (Av τ n f) B := fun y => av_sup h y

/-- the plane average. -/
noncomputable def P2 (τ₁ τ₂ : Fin 3) (n : ℕ) (f : Z3 → M2) : Z3 → M2 := Av τ₁ n (Av τ₂ n f)

theorem p2_d1 {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {e : Z3} {D : ℝ} (h : D1v e f D) : D1v e (P2 τ₁ τ₂ n f) D :=
  av_D1v (av_D1v h)

theorem p2_sup {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {B : ℝ} (h : SupB f B) : SupB (P2 τ₁ τ₂ n f) B :=
  av_SupB (av_SupB h)

/-- the difference function. -/
def dlt (e : Z3) (f : Z3 → M2) : Z3 → M2 := fun y => f (y + e) - f y

theorem dlt_sup {e : Z3} {f : Z3 → M2} {D : ℝ} (h : D1v e f D) : SupB (dlt e f) D := h

theorem dlt_av (τ : Fin 3) (n : ℕ) (f : Z3 → M2) (e : Z3) : dlt e (Av τ n f) = Av τ n (dlt e f) := by
  funext x; exact av_diff_v τ n f x e

theorem dlt_D1v {e e' : Z3} {f : Z3 → M2} {D : ℝ} (h : D1v e f D) : D1v e (dlt e' f) (2 * D) := by
  intro y
  have e1 : dlt e' f (y + e) - dlt e' f y = (f (y + e' + e) - f (y + e')) - (f (y + e) - f y) := by
    simp only [dlt]; rw [show y + e + e' = y + e' + e by abel]; abel
  rw [e1]
  refine (frobNorm_sub_le' _ 0 _).trans ?_
  rw [sub_zero, zero_sub, frobNorm_neg]
  have := h (y + e'); have := h y; linarith

theorem dlt_comm (e e' : Z3) (f : Z3 → M2) : dlt e' (dlt e f) = dlt e (dlt e' f) := by
  funext y; simp only [dlt]; rw [show y + e' + e = y + e + e' by abel]; abel

/-- the stencil second difference. -/
theorem stencil_eq (g : Z3 → M2) (x e e' : Z3) :
    g (x + e + e') - g (x + e) - g (x + e') + g x = dlt e' (dlt e g) x := by
  simp only [dlt]; rw [show x + e' + e = x + e + e' by abel]; abel

/-- **plane second differences.** -/
theorem p2_dd {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h1 : D1 τ₁ f D) (h2 : D1 τ₂ f D)
    {e' : Z3} (he' : D1v e' f D) (μ : Fin 3) (hμ : μ = τ₁ ∨ μ = τ₂) (x : Z3) :
    frobNorm (P2 τ₁ τ₂ n f (x + ev μ + e') - P2 τ₁ τ₂ n f (x + ev μ) - P2 τ₁ τ₂ n f (x + e') + P2 τ₁ τ₂ n f x)
      ≤ 2 * D / (2 * n + 1) := by
  rw [stencil_eq]
  rcases hμ with rfl | rfl
  · -- Δ_{e'} Δ_{τ₁} Av τ₁ g, g = Av τ₂ f
    have e1 : dlt e' (dlt (ev μ) (P2 μ τ₂ n f)) x = dlt (ev μ) (Av μ n (dlt e' (Av τ₂ n f))) x := by
      simp only [P2]; rw [← dlt_av]
      simp only [dlt]; rw [show x + e' + ev μ = x + ev μ + e' by abel]; abel
    rw [e1]
    exact av_d1_sup (dlt_sup (av_D1v he')) x
  · have e1 : dlt e' (dlt (ev μ) (P2 τ₁ μ n f)) x = Av τ₁ n (dlt (ev μ) (Av μ n (dlt e' f))) x := by
      simp only [P2]; rw [dlt_av, dlt_av, dlt_av, dlt_av, dlt_av, dlt_comm]
    rw [e1]
    exact av_sup (fun y => av_d1_sup (dlt_sup he') y) x

/-- mixed radii. -/
noncomputable def Pk (τ₁ τ₂ : Fin 3) (k j : ℕ) (f : Z3 → M2) : Z3 → M2 := Av τ₁ k (Av τ₂ j f)

theorem p2_step {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h1 : D1 τ₁ f D) (h2 : D1 τ₂ f D) (hD : 0 ≤ D)
    (x : Z3) : frobNorm (P2 τ₁ τ₂ (n + 1) f x - P2 τ₁ τ₂ n f x) ≤ 4 * D := by
  have e : P2 τ₁ τ₂ (n + 1) f x - P2 τ₁ τ₂ n f x
      = (Av τ₁ (n + 1) (Av τ₂ (n + 1) f) x - Av τ₁ n (Av τ₂ (n + 1) f) x)
        + Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) x := by
    simp only [P2]; rw [← av_sub]; abel
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  have a := av_step_d1 (n := n) (av_D1v (n := n + 1) (τ := τ₂) (D1v_of_D1 h1)) hD x
  have b := av_sup (τ := τ₁) (n := n) (f := fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) (fun y => av_step_d1 h2 hD y) x
  linarith

theorem p2_step_d {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h1 : D1 τ₁ f D) (h2 : D1 τ₂ f D) (hD : 0 ≤ D)
    (μ : Fin 3) (hμ : μ = τ₁ ∨ μ = τ₂) (x : Z3) :
    frobNorm ((P2 τ₁ τ₂ (n + 1) f (x + ev μ) - P2 τ₁ τ₂ n f (x + ev μ)) - (P2 τ₁ τ₂ (n + 1) f x - P2 τ₁ τ₂ n f x))
      ≤ 8 * D / (2 * n + 1) := by
  have hp1 := pos2n1 n
  have hp3 : (0 : ℝ) < 2 * n + 3 := by positivity
  have split : ∀ z, P2 τ₁ τ₂ (n + 1) f z - P2 τ₁ τ₂ n f z
      = (Av τ₁ (n + 1) (Av τ₂ (n + 1) f) z - Av τ₁ n (Av τ₂ (n + 1) f) z)
        + Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) z := by
    intro z; simp only [P2]; rw [← av_sub]; abel
  rw [split, split]
  have e : (Av τ₁ (n + 1) (Av τ₂ (n + 1) f) (x + ev μ) - Av τ₁ n (Av τ₂ (n + 1) f) (x + ev μ)
        + Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) (x + ev μ))
      - (Av τ₁ (n + 1) (Av τ₂ (n + 1) f) x - Av τ₁ n (Av τ₂ (n + 1) f) x
        + Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) x)
      = ((Av τ₁ (n + 1) (Av τ₂ (n + 1) f) (x + ev μ) - Av τ₁ n (Av τ₂ (n + 1) f) (x + ev μ))
          - (Av τ₁ (n + 1) (Av τ₂ (n + 1) f) x - Av τ₁ n (Av τ₂ (n + 1) f) x))
        + (Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) (x + ev μ)
          - Av τ₁ n (fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y) x) := by abel
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  rcases hμ with rfl | rfl
  · have a := av_step_dd (n := n) (av_D1v (n := n + 1) (τ := τ₂) (D1v_of_D1 h1)) x
    have b := av_d1_sup (τ := μ) (n := n) (h := fun y => Av τ₂ (n + 1) f y - Av τ₂ n f y)
      (fun y => av_step_d1 h2 hD y) x
    have : 4 * D / (2 * n + 3) ≤ 4 * D / (2 * n + 1) := div_le_div_of_nonneg_left (by positivity) hp1 (by linarith)
    have : 2 * (2 * D) / (2 * n + 1) = 4 * D / (2 * n + 1) := by ring
    have : 4 * D / (2 * n + 1) + 4 * D / (2 * n + 1) = 8 * D / (2 * n + 1) := by ring
    linarith
  · -- first term: Δ_{τ₂} commutes with the τ₁-operators
    have a : frobNorm ((Av τ₁ (n + 1) (Av μ (n + 1) f) (x + ev μ) - Av τ₁ n (Av μ (n + 1) f) (x + ev μ))
          - (Av τ₁ (n + 1) (Av μ (n + 1) f) x - Av τ₁ n (Av μ (n + 1) f) x)) ≤ 4 * D / (2 * n + 3) := by
      have e2 : (Av τ₁ (n + 1) (Av μ (n + 1) f) (x + ev μ) - Av τ₁ n (Av μ (n + 1) f) (x + ev μ))
          - (Av τ₁ (n + 1) (Av μ (n + 1) f) x - Av τ₁ n (Av μ (n + 1) f) x)
          = Av τ₁ (n + 1) (dlt (ev μ) (Av μ (n + 1) f)) x - Av τ₁ n (dlt (ev μ) (Av μ (n + 1) f)) x := by
        rw [← dlt_av, ← dlt_av]; simp only [dlt]; abel
      rw [e2]
      exact av_step_sup (dlt_sup (av_D1v (D1v_of_D1 h2))) x
    have b : frobNorm (Av τ₁ n (fun y => Av μ (n + 1) f y - Av μ n f y) (x + ev μ)
          - Av τ₁ n (fun y => Av μ (n + 1) f y - Av μ n f y) x) ≤ 4 * D / (2 * n + 3) := by
      rw [av_diff_v]
      exact av_sup (fun y => by
        exact av_step_dd (n := n) h2 y) x
    have : 4 * D / (2 * n + 3) ≤ 4 * D / (2 * n + 1) := div_le_div_of_nonneg_left (by positivity) hp1 (by linarith)
    have : 4 * D / (2 * n + 1) + 4 * D / (2 * n + 1) = 8 * D / (2 * n + 1) := by ring
    linarith

theorem p2_step2 {τ₁ τ₂ : Fin 3} {n : ℕ} {f : Z3 → M2} {D : ℝ} (h1 : D1 τ₁ f D) (h2 : D1 τ₂ f D) (hD : 0 ≤ D)
    (x : Z3) :
    frobNorm ((P2 τ₁ τ₂ (n + 2) f x - P2 τ₁ τ₂ (n + 1) f x) - (P2 τ₁ τ₂ (n + 1) f x - P2 τ₁ τ₂ n f x))
      ≤ 36 * D / (2 * n + 3) := by
  have hp3 : (0 : ℝ) < 2 * n + 3 := by positivity
  have hp5 : (0 : ℝ) < 2 * n + 5 := by positivity
  set a2 := Av τ₁ (n + 2) (Av τ₂ (n + 2) f) x
  set a1 := Av τ₁ (n + 1) (Av τ₂ (n + 2) f) x
  set a0 := Av τ₁ n (Av τ₂ (n + 2) f) x
  set b1 := Av τ₁ (n + 1) (Av τ₂ (n + 1) f) x
  set c1 := Av τ₁ n (Av τ₂ (n + 1) f) x
  set c0 := Av τ₁ n (Av τ₂ n f) x
  have e : (P2 τ₁ τ₂ (n + 2) f x - P2 τ₁ τ₂ (n + 1) f x) - (P2 τ₁ τ₂ (n + 1) f x - P2 τ₁ τ₂ n f x)
      = ((a2 - a1) - (a1 - a0)) + (2 : ℝ) • ((a1 - b1) - (a0 - c1)) + ((a0 - c1) - (c1 - c0)) := by
    simp only [P2]; module
  rw [e]
  have t := frobNorm_add_le (((a2 - a1) - (a1 - a0)) + (2 : ℝ) • ((a1 - b1) - (a0 - c1))) ((a0 - c1) - (c1 - c0))
  have t' := frobNorm_add_le ((a2 - a1) - (a1 - a0)) ((2 : ℝ) • ((a1 - b1) - (a0 - c1)))
  rw [frobNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at t'
  -- first: second radius difference in τ₁ of g = Av τ₂ (n+2) f
  have A1 : frobNorm ((a2 - a1) - (a1 - a0)) ≤ 10 * D / (2 * n + 5) :=
    av_step2 (av_D1v (n := n + 2) (τ := τ₂) (D1v_of_D1 h1)) hD x
  -- middle: (Av τ₁ (n+1) − Av τ₁ n) of h = Av τ₂ (n+2) f − Av τ₂ (n+1) f
  have A2 : frobNorm ((a1 - b1) - (a0 - c1)) ≤ 8 * D / (2 * n + 3) := by
    have e2 : (a1 - b1) - (a0 - c1)
        = Av τ₁ (n + 1) (fun y => Av τ₂ (n + 2) f y - Av τ₂ (n + 1) f y) x
          - Av τ₁ n (fun y => Av τ₂ (n + 2) f y - Av τ₂ (n + 1) f y) x := by
      simp only [a1, b1, a0, c1]; rw [← av_sub, ← av_sub]
    rw [e2]
    have hs : SupB (fun y => Av τ₂ (n + 2) f y - Av τ₂ (n + 1) f y) (2 * D) := fun y => av_step_d1 h2 hD y
    have := av_step_sup (τ := τ₁) (n := n) hs x
    rw [show 4 * (2 * D) / (2 * (n : ℝ) + 3) = 8 * D / (2 * n + 3) by ring] at this
    exact this
  -- last: Av τ₁ n of the second radius difference in τ₂
  have A3 : frobNorm ((a0 - c1) - (c1 - c0)) ≤ 10 * D / (2 * n + 5) := by
    have e3 : (a0 - c1) - (c1 - c0)
        = Av τ₁ n (fun y => (Av τ₂ (n + 2) f y - Av τ₂ (n + 1) f y) - (Av τ₂ (n + 1) f y - Av τ₂ n f y)) x := by
      simp only [a0, c1, c0]; rw [← av_sub, ← av_sub, ← av_sub]
    rw [e3]
    exact av_sup (fun y => av_step2 h2 hD y) x
  have k1 : 10 * D / (2 * n + 5) ≤ 10 * D / (2 * n + 3) := div_le_div_of_nonneg_left (by positivity) hp3 (by linarith)
  have k2 : 10 * D / (2 * (n : ℝ) + 3) + 2 * (8 * D / (2 * n + 3)) + 10 * D / (2 * n + 3) = 36 * D / (2 * n + 3) := by ring
  linarith

end AdalyFormal.UnifLane.Z

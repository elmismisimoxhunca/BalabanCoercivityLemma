import MI8

/-!
# MI23 -- the smooth block profile: a quadratic tent on a block and its sums (M1 lane E, 2026-10-13)

`tp n t = (t+1)(n−t)` on `t ∈ {0,…,n−1}`; `T_y(x) = Π_μ tp n (x_μ − y_μ)` on the block `B(y,n)`.
* `tp_pos`, `tp_le` (`≤ (n+1)²/4`), `tp_step` (`|Δ tp| ≤ n`), `tp_zero`, `tp_last` (`= n` at both ends);
* `tp_sum` : `Σ_{t<n} tp n t = n(n+1)(n+2)/6`;
* `blockSum_prod` : `Σ_{x ∈ B(y,n)} Π_μ f_μ(x_μ − y_μ) = Π_μ Σ_{t<n} f_μ(t)` (the block is a product, no wrap).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M1IMS

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf)
open Finset

/-- the 1D quadratic tent. -/
noncomputable def tp (n t : ℕ) : ℝ := ((t : ℝ) + 1) * ((n : ℝ) - t)

theorem tp_pos {n t : ℕ} (ht : t < n) : 0 < tp n t := by
  unfold tp
  have h1 : (t : ℝ) + 1 > 0 := by positivity
  have h2 : (t : ℝ) < n := by exact_mod_cast ht
  have : (0 : ℝ) < (n : ℝ) - t := by linarith
  positivity

theorem tp_le {n t : ℕ} : tp n t ≤ ((n : ℝ) + 1) ^ 2 / 4 := by
  unfold tp
  nlinarith [sq_nonneg ((t : ℝ) + 1 - ((n : ℝ) - t))]

theorem tp_step {n t : ℕ} (ht : t + 1 < n) : |tp n (t + 1) - tp n t| ≤ n := by
  unfold tp
  have h : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
  rw [h]
  have e : ((t : ℝ) + 1 + 1) * ((n : ℝ) - ((t : ℝ) + 1)) - ((t : ℝ) + 1) * ((n : ℝ) - t) = (n : ℝ) - 2 * t - 2 := by ring
  rw [e, abs_le]
  have h1 : (t : ℝ) + 1 < n := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  constructor <;> linarith

theorem tp_zero (n : ℕ) : tp n 0 = n := by unfold tp; simp

theorem tp_last {n : ℕ} (hn : 1 ≤ n) : tp n (n - 1) = n := by
  unfold tp
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [this]; ring

theorem sum_range_succ_cast (n : ℕ) : ∑ t ∈ range n, ((t : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

theorem tp_sum (n : ℕ) : ∑ t ∈ range n, tp n t = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have e : ∀ t ∈ range n, tp (n + 1) t = tp n t + ((t : ℝ) + 1) := by
      intro t _; unfold tp; push_cast; ring
    rw [sum_congr rfl e, sum_add_distrib, ih, sum_range_succ_cast]
    unfold tp; push_cast; ring

/-- the block is a product box: sums of separable functions factor. -/
theorem blockSum_prod {L : PeriodicLatticeExtent} (y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (y μ).val + n ≤ L μ + 1) (f : Fin 3 → ℕ → ℝ) :
    ∑ x ∈ blockOf y n, ∏ μ : Fin 3, f μ ((x μ).val - (y μ).val)
      = ∏ μ : Fin 3, ∑ t ∈ range n, f μ t := by
  classical
  -- the parametrisation `t ↦ y + t`
  let φ : (Fin 3 → Fin n) → PeriodicLatticeSite L :=
    fun t μ => ⟨(y μ).val + (t μ).val, by have := (t μ).isLt; have := hfit μ; omega⟩
  have hφinj : Function.Injective φ := by
    intro t t' h
    funext μ
    have := congrArg (fun z : PeriodicLatticeSite L => (z μ).val) h
    simp only [φ] at this
    exact Fin.ext (by omega)
  have himg : blockOf y n = univ.image φ := by
    ext x
    rw [mem_blockOf, mem_image]
    constructor
    · intro hx
      refine ⟨fun μ => ⟨(x μ).val - (y μ).val, by have := (hx μ).2; have := (hx μ).1; omega⟩, mem_univ _, ?_⟩
      funext μ
      apply Fin.ext
      simp only [φ]
      have := (hx μ).1; omega
    · rintro ⟨t, -, rfl⟩ μ
      simp only [φ]
      exact ⟨Nat.le_add_right _ _, by have := (t μ).isLt; omega⟩
  rw [himg, sum_image (fun t _ t' _ h => hφinj h)]
  have e : ∀ t : Fin 3 → Fin n, ∏ μ : Fin 3, f μ (((φ t) μ).val - (y μ).val) = ∏ μ : Fin 3, f μ (t μ).val := by
    intro t
    refine prod_congr rfl (fun μ _ => ?_)
    simp only [φ]
    congr 1; omega
  rw [sum_congr rfl (fun t _ => e t)]
  rw [← Fintype.prod_sum (fun μ (s : Fin n) => f μ s.val)]
  refine prod_congr rfl (fun μ _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun s => f μ s) n

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.tp_pos
#print axioms AdalyFormal.M1IMS.tp_le
#print axioms AdalyFormal.M1IMS.tp_step
#print axioms AdalyFormal.M1IMS.tp_zero
#print axioms AdalyFormal.M1IMS.tp_last
#print axioms AdalyFormal.M1IMS.sum_range_succ_cast
#print axioms AdalyFormal.M1IMS.tp_sum
#print axioms AdalyFormal.M1IMS.blockSum_prod
#print axioms AdalyFormal.M1IMS.tp

import OG14
import OL14

/-!
# RI1 -- quantitative inverse of a nilpotent perturbation; the `D`-norm on `𝔅` (lane m2_rightinv_20261015)

* `bound_of_perturbed` : `T = I + N + S`, `N ∘ N = 0`, `ν(N y) ≤ A ν(y)`, `ν(S y) ≤ s ν(y)`, `4 s (1 + A) ≤ 1/2`
  ⇒ `ν(y) ≤ 8 (1 + A) ν(T y)` (from `(I − N) T = I + S − N S`).
* `nD_neg`, `eq_zero_of_nD`, `nD_sglL`, `nD_sum_sparse` (the `D`-weight copy of W6 `nF_sum_sparse`).
* `nD_le_of_inter` : a vector supported on the rows interacting with `p` has `nD ≤ ℓ² ℓ^{-2 lev p} nF`
  (interacting rows have level `≥ lev p − 1`); `nD_src` : per-source `nF` bounds become `nD` bounds with a factor `ℓ²`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2RightInv

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.W6 (nD wD wD_pos nD_nonneg nD_add_le nD_sub_le nD_smul nF wF wF_pos nF_nonneg)
open AdalyFormal.M2W6 (Inter sglL sglL_apply)

/-- **quantitative inverse of `I + N + S`** with `N² = 0` -/
theorem bound_of_perturbed {H : Type*} [AddCommGroup H] [Module ℝ H] (ν : H → ℝ)
    (hν0 : ∀ x, 0 ≤ ν x) (hνadd : ∀ x y, ν (x + y) ≤ 2 * ν x + 2 * ν y) (hνneg : ∀ x, ν (-x) = ν x)
    (N S T : H →ₗ[ℝ] H) (hT : ∀ y, T y = y + N y + S y) (hNN : ∀ y, N (N y) = 0)
    (A s : ℝ) (hN : ∀ y, ν (N y) ≤ A * ν y) (hS : ∀ y, ν (S y) ≤ s * ν y) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hsmall : 4 * s * (1 + A) ≤ 1 / 2) (y : H) : ν y ≤ 8 * (1 + A) * ν (T y) := by
  have h1 : T y - N (T y) = y + S y - N (S y) := by
    rw [hT y, map_add, map_add, hNN]; abel
  have hy : y = (T y + -(N (T y))) + (N (S y) + -(S y)) := by
    have e : y = (T y - N (T y)) - S y + N (S y) := by rw [h1]; abel
    conv_lhs => rw [e]
    abel
  have e1 := hνadd (T y + -(N (T y))) (N (S y) + -(S y))
  rw [← hy] at e1
  have e2 := hνadd (T y) (-(N (T y)))
  have e3 := hνadd (N (S y)) (-(S y))
  rw [hνneg] at e2 e3
  have e4 := hN (T y)
  have e5 := hN (S y)
  have e6 := hS y
  have hT0 := hν0 (T y)
  have hy0 := hν0 y
  have hS0 := hν0 (S y)
  have k1 : ν y ≤ 4 * (1 + A) * ν (T y) + 4 * (1 + A) * ν (S y) := by nlinarith
  have k2 : 4 * (1 + A) * ν (S y) ≤ 4 * (1 + A) * (s * ν y) := mul_le_mul_of_nonneg_left e6 (by linarith)
  have k3 : 4 * (1 + A) * (s * ν y) ≤ 1 / 2 * ν y := by
    have := mul_le_mul_of_nonneg_right hsmall hy0
    nlinarith
  linarith

section nrm
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem nD_neg (y : FSp (geomOf ell k S)) : nD (-y) = nD y := by
  unfold nD; refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show (-y) p = -(y p) from rfl, norm_neg]

theorem eq_zero_of_nD (hell : 0 < ell) (y : FSp (geomOf ell k S)) (h : nD y ≤ 0) : y = 0 := by
  have h0 : nD y = 0 := le_antisymm h (nD_nonneg hell y)
  unfold nD at h0
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (wD_pos hell p).le (sq_nonneg _))] at h0
  refine PiLp.ext (fun p => ?_)
  have hp := h0 p (Finset.mem_univ p)
  have hw := (wD_pos hell p).ne'
  have h2 : ‖y p‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact absurd h1 hw
    · exact h1
  have h3 : ‖y p‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
  rw [PiLp.zero_apply]; exact norm_eq_zero.mp h3

theorem nD_sglL (w : SuTwo) (p : BIdx (geomOf ell k S)) : nD (sglL p w) = wD p * ‖w‖ ^ 2 := by
  classical
  unfold nD
  simp only [sglL_apply]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq; simp [hq]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- `‖Σ a_i‖² ≤ |F| Σ ‖a_i‖²` when `a` vanishes off `F` -/
theorem norm_sq_sum_le_card {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] (F : Finset ι) (a : ι → E)
    (h : ∀ i, i ∉ F → a i = 0) : ‖∑ i, a i‖ ^ 2 ≤ (F.card : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ∑ i, a i = ∑ i ∈ F, a i := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => h i hi)
  rw [h1]
  have h2 : ‖∑ i ∈ F, a i‖ ≤ ∑ i ∈ F, ‖a i‖ := norm_sum_le _ _
  have h3 : (∑ i ∈ F, ‖a i‖) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖a i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have h4 : ‖∑ i ∈ F, a i‖ ^ 2 ≤ (∑ i ∈ F, ‖a i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h6 : ∑ i ∈ F, ‖a i‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  calc _ ≤ _ := h4.trans h3
    _ ≤ (F.card : ℝ) * ∑ i, ‖a i‖ ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)

open Classical in
/-- the sparse sum in the `D` weight: each target row sees at most `m0` sources -/
theorem nD_sum_sparse (hell : 0 < ell) (m0 : ℕ) (v : BIdx (geomOf ell k S) → FSp (geomOf ell k S))
    (hsupp : ∀ p p' : BIdx (geomOf ell k S), ¬ Inter p' p → v p p' = 0)
    (hcard : ∀ p' : BIdx (geomOf ell k S), (Finset.univ.filter (fun p => Inter p' p)).card ≤ m0) :
    nD (∑ p, v p) ≤ (m0 : ℝ) * ∑ p, nD (v p) := by
  unfold nD
  have hrow : ∀ p' : BIdx (geomOf ell k S), ‖(∑ p, v p) p'‖ ^ 2 ≤ (m0 : ℝ) * ∑ p, ‖v p p'‖ ^ 2 := by
    intro p'
    have h1 : (∑ p, v p) p' = ∑ p, v p p' := by rw [WithLp.ofLp_sum, Finset.sum_apply]
    rw [h1]
    have h2 := norm_sq_sum_le_card (Finset.univ.filter (fun p => Inter p' p)) (fun p => v p p')
      (fun p hp => hsupp p p' (by simpa using hp))
    have h5 : ((Finset.univ.filter (fun p => Inter p' p)).card : ℝ) ≤ m0 := by exact_mod_cast hcard p'
    have h7 : 0 ≤ ∑ p, ‖v p p'‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact h2.trans (mul_le_mul_of_nonneg_right h5 h7)
  calc ∑ p', wD p' * ‖(∑ p, v p) p'‖ ^ 2 ≤ ∑ p', wD p' * ((m0 : ℝ) * ∑ p, ‖v p p'‖ ^ 2) :=
        Finset.sum_le_sum (fun p' _ => mul_le_mul_of_nonneg_left (hrow p') (wD_pos hell p').le)
    _ = ∑ p', ∑ p, (m0 : ℝ) * (wD p' * ‖v p p'‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun p' _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
    _ = ∑ p, ∑ p', (m0 : ℝ) * (wD p' * ‖v p p'‖ ^ 2) := Finset.sum_comm
    _ = (m0 : ℝ) * ∑ p, ∑ p', wD p' * ‖v p p'‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]

/-- **`nF` to `nD` on vectors supported on the rows interacting with `p`** -/
theorem nD_le_of_inter (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (v : FSp (geomOf ell k S))
    (hv : ∀ p' : BIdx (geomOf ell k S), ¬ Inter p' p → v p' = 0) :
    nD v ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * nF v := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  unfold nD nF
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun p' _ => ?_)
  by_cases hI : Inter p' p
  · have hj : (p.1 : ℕ) ≤ (p'.1 : ℕ) + 1 := hI.2.1
    set a : ℝ := (ell : ℝ) ^ (p.1 : ℕ) with ha
    set b : ℝ := (ell : ℝ) ^ (p'.1 : ℕ) with hb
    have ha0 : 0 < a := by rw [ha]; positivity
    have hb0 : 0 < b := by rw [hb]; positivity
    have hab : a ≤ (ell : ℝ) * b := by
      rw [ha, hb, ← pow_succ']
      exact pow_le_pow_right₀ hl1 hj
    have key : b ≤ (ell : ℝ) ^ 2 * (a⁻¹) ^ 2 * b ^ 3 := by
      calc b = (a⁻¹) ^ 2 * (a ^ 2 * b) := by field_simp
        _ ≤ (a⁻¹) ^ 2 * (((ell : ℝ) * b) ^ 2 * b) := by
            have : a ^ 2 ≤ ((ell : ℝ) * b) ^ 2 := pow_le_pow_left₀ ha0.le hab 2
            gcongr
        _ = (ell : ℝ) ^ 2 * (a⁻¹) ^ 2 * b ^ 3 := by ring
    have hwD : wD p' = b := rfl
    have hwF : wF p' = b ^ 3 := rfl
    rw [hwD, hwF]
    have := mul_le_mul_of_nonneg_right key (sq_nonneg ‖v p'‖)
    calc b * ‖v p'‖ ^ 2 ≤ (ell : ℝ) ^ 2 * (a⁻¹) ^ 2 * b ^ 3 * ‖v p'‖ ^ 2 := this
      _ = _ := by ring
  · rw [hv p' hI, norm_zero]; simp

/-- per-source `nF` bound ⇒ per-source `nD` bound (factor `ℓ²`) -/
theorem nD_src (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (v : FSp (geomOf ell k S))
    (hv : ∀ p' : BIdx (geomOf ell k S), ¬ Inter p' p → v p' = 0) (c : ℝ) (w : SuTwo)
    (hF : nF v ≤ c * (wF p * ‖w‖ ^ 2)) : nD v ≤ (ell : ℝ) ^ 2 * c * (wD p * ‖w‖ ^ 2) := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have h1 := nD_le_of_inter hell p v hv
  have hc : 0 ≤ (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left hF hc
  have ha0 : (0 : ℝ) < (ell : ℝ) ^ (p.1 : ℕ) := by positivity
  have e : (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * (c * (wF p * ‖w‖ ^ 2))
      = (ell : ℝ) ^ 2 * c * (wD p * ‖w‖ ^ 2) := by
    show (ell : ℝ) ^ 2 * (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) ^ 2 * (c * (((ell : ℝ) ^ (p.1 : ℕ)) ^ 3 * ‖w‖ ^ 2))
      = (ell : ℝ) ^ 2 * c * ((ell : ℝ) ^ (p.1 : ℕ) * ‖w‖ ^ 2)
    field_simp
  linarith

end nrm

end AdalyFormal.M2RightInv

#print axioms AdalyFormal.M2RightInv.bound_of_perturbed
#print axioms AdalyFormal.M2RightInv.nD_neg
#print axioms AdalyFormal.M2RightInv.eq_zero_of_nD
#print axioms AdalyFormal.M2RightInv.nD_sglL
#print axioms AdalyFormal.M2RightInv.norm_sq_sum_le_card
#print axioms AdalyFormal.M2RightInv.nD_sum_sparse
#print axioms AdalyFormal.M2RightInv.nD_le_of_inter
#print axioms AdalyFormal.M2RightInv.nD_src

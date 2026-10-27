import DLR42
import DLR45

/-!
# DL46 -- curl and divergence of a bond field from its shift-gradient, and the covariant corrections

`gradE A ν = Σ_b ‖A(b.1 + e_ν, b.2) − A b‖²` (shift-gradient energy in direction `ν`).
* **`curl_flat_le`** : `gradE A ν ≤ Γ ∀ν` ⟹ `‖curl₁ A‖² ≤ 36 Γ` (`curl₁ = curlC (trivialU)`).
* **`div_flat_le`**  : `gradE A ν ≤ Γ ∀ν` ⟹ `‖D₁* A‖ ≤ 3√Γ` (`D₁ = gradL2 (trivialU)`; summation by parts).
* **`curl_cov_diff`** : `dv(U b) ≤ e ∀b` ⟹ `‖curl_U A − curl₁ A‖ ≤ 12 e ‖A‖`.
* **`grad_cov_diff`** : `‖D_U f − D₁ f‖ ≤ 2√3 e ‖f‖`; `div_cov_diff` : the same for the adjoints.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2 trivialU)

variable {L : PeriodicLatticeExtent}

/-- the shift-gradient energy of a bond field in direction `ν` -/
noncomputable def gradE (A : BondFnL2 L) (ν : Fin 3) : ℝ :=
  ∑ b : Bond L, ‖A (periodicLatticeShift b.1 ν, b.2) - A b‖ ^ 2

theorem gradE_nonneg (A : BondFnL2 L) (ν : Fin 3) : 0 ≤ gradE A ν :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem slice_le_gradE (A : BondFnL2 L) (ν μ : Fin 3) :
    ∑ x : PeriodicLatticeSite L, ‖A (periodicLatticeShift x ν, μ) - A (x, μ)‖ ^ 2 ≤ gradE A ν := by
  unfold gradE
  rw [Fintype.sum_prod_type_right]
  exact Finset.single_le_sum (f := fun μ' => ∑ x : PeriodicLatticeSite L,
      ‖A (periodicLatticeShift (x, μ').1 ν, (x, μ').2) - A (x, μ')‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ μ)

theorem RMap_sub_id_le (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : SuTwo) :
    ‖RMap g v - v‖ ≤ 2 * AdalyFormal.CurvBlock.dv g * ‖v‖ := by
  have h := RMap_diff_le g 1 v
  rw [RMap_one, LinearMap.id_apply, inv_one, mul_one] at h
  exact h

theorem RMap_trivial (b : Bond L) (v : SuTwo) : RMap (trivialU L b) v = v := by
  show RMap 1 v = v
  rw [RMap_one, LinearMap.id_apply]

/-! ## flat curl -/

theorem curl_flat_pt (A : BondFnL2 L) (p : PeriodicLatticePlaquette L) :
    ‖curlC (trivialU L) A p‖ ^ 2
      ≤ 2 * ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.1)‖ ^ 2
        + 2 * ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - A (p.1, p.2.1.2)‖ ^ 2 := by
  rw [curlC_apply]
  unfold curlValueCovariant
  rw [RMap_trivial, RMap_trivial]
  have e : (WithLp.ofLp A) (p.1, p.2.1.1) + (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      - (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - (WithLp.ofLp A) (p.1, p.2.1.2)
      = -(A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.1))
        + (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - A (p.1, p.2.1.2)) := by
    show A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
      - A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2) = _
    abel
  rw [e]
  have h := norm_add_le (-(A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.1)))
    (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - A (p.1, p.2.1.2))
  rw [norm_neg] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.1)‖
    - ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - A (p.1, p.2.1.2)‖)]

theorem curl_flat_le (A : BondFnL2 L) (Γ : ℝ) (hΓ : ∀ ν, gradE A ν ≤ Γ) :
    ‖curlC (trivialU L) A‖ ^ 2 ≤ 36 * Γ := by
  have hΓ0 : 0 ≤ Γ := le_trans (gradE_nonneg A 0) (hΓ 0)
  rw [PiLp.norm_sq_eq_of_L2]
  have hd : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
      (2 * ‖A (periodicLatticeShift x d.1.2, d.1.1) - A (x, d.1.1)‖ ^ 2
        + 2 * ‖A (periodicLatticeShift x d.1.1, d.1.2) - A (x, d.1.2)‖ ^ 2) ≤ 4 * Γ := by
    intro d
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := (slice_le_gradE A d.1.2 d.1.1).trans (hΓ d.1.2)
    have h2 := (slice_le_gradE A d.1.1 d.1.2).trans (hΓ d.1.1)
    linarith
  calc ∑ p, ‖curlC (trivialU L) A p‖ ^ 2
      ≤ ∑ p : PeriodicLatticePlaquette L, (2 * ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.1)‖ ^ 2
          + 2 * ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) - A (p.1, p.2.1.2)‖ ^ 2) :=
        Finset.sum_le_sum (fun p _ => curl_flat_pt A p)
    _ = ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
          (2 * ‖A (periodicLatticeShift x d.1.2, d.1.1) - A (x, d.1.1)‖ ^ 2
            + 2 * ‖A (periodicLatticeShift x d.1.1, d.1.2) - A (x, d.1.2)‖ ^ 2) := by
        rw [Fintype.sum_prod_type_right]
    _ ≤ ∑ _d : PeriodicPlaquetteDirections, 4 * Γ := Finset.sum_le_sum (fun d _ => hd d)
    _ = (Fintype.card PeriodicPlaquetteDirections : ℝ) * (4 * Γ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 9 * (4 * Γ) := mul_le_mul_of_nonneg_right card_dirs_le (by positivity)
    _ = 36 * Γ := by ring

/-! ## flat divergence (summation by parts) -/

theorem grad_trivial_apply (f : SiteL2 L) (b : Bond L) :
    (gradL2 (trivialU L) f) b = f (periodicLatticeShift b.1 b.2) - f b.1 := by
  show gradValueCovariant (trivialU L) (WithLp.ofLp f) b = _
  unfold gradValueCovariant
  rw [RMap_trivial]

theorem div_flat_le (A : BondFnL2 L) (Γ : ℝ) (hΓ : ∀ ν, gradE A ν ≤ Γ) :
    ‖ContinuousLinearMap.adjoint (gradL2 (trivialU L)) A‖ ≤ 3 * Real.sqrt Γ := by
  have hΓ0 : 0 ≤ Γ := le_trans (gradE_nonneg A 0) (hΓ 0)
  set f := ContinuousLinearMap.adjoint (gradL2 (trivialU L)) A with hf
  have hff : ‖f‖ ^ 2 = ⟪A, gradL2 (trivialU L) f⟫ := by
    rw [← real_inner_self_eq_norm_sq, hf, ContinuousLinearMap.adjoint_inner_left]
  -- the bond sum, direction by direction
  have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ⟪A (x, μ), (gradL2 (trivialU L) f) (x, μ)⟫
      ≤ Real.sqrt Γ * ‖f‖ := by
    intro μ
    have e1 : ∑ x : PeriodicLatticeSite L, ⟪A (x, μ), (gradL2 (trivialU L) f) (x, μ)⟫
        = ∑ x : PeriodicLatticeSite L, ⟪A (x, μ) - A (periodicLatticeShift x μ, μ), f (periodicLatticeShift x μ)⟫ := by
      have e2 : ∑ x : PeriodicLatticeSite L, ⟪A (x, μ), f x⟫
          = ∑ x : PeriodicLatticeSite L, ⟪A (periodicLatticeShift x μ, μ), f (periodicLatticeShift x μ)⟫ :=
        (sum_shift_site μ (fun y => ⟪A (y, μ), f y⟫)).symm
      simp only [grad_trivial_apply, inner_sub_right, inner_sub_left, Finset.sum_sub_distrib]
      rw [e2]
    rw [e1]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun x : PeriodicLatticeSite L => ‖A (x, μ) - A (periodicLatticeShift x μ, μ)‖)
      (fun x : PeriodicLatticeSite L => ‖f (periodicLatticeShift x μ)‖)
    have hS1 : ∑ x : PeriodicLatticeSite L, ‖A (x, μ) - A (periodicLatticeShift x μ, μ)‖ ^ 2 ≤ Γ := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl (fun x _ => by rw [norm_sub_rev]))) ?_
      exact (slice_le_gradE A μ μ).trans (hΓ μ)
    have hS2 : ∑ x : PeriodicLatticeSite L, ‖f (periodicLatticeShift x μ)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, sum_shift_site μ (fun y => ‖f y‖ ^ 2)]
    have hsum : ∑ x : PeriodicLatticeSite L, ⟪A (x, μ) - A (periodicLatticeShift x μ, μ), f (periodicLatticeShift x μ)⟫
        ≤ ∑ x : PeriodicLatticeSite L, ‖A (x, μ) - A (periodicLatticeShift x μ, μ)‖ * ‖f (periodicLatticeShift x μ)‖ :=
      Finset.sum_le_sum (fun x _ => real_inner_le_norm _ _)
    have hP0 : 0 ≤ ∑ x : PeriodicLatticeSite L, ‖A (x, μ) - A (periodicLatticeShift x μ, μ)‖ * ‖f (periodicLatticeShift x μ)‖ :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hsq : (∑ x : PeriodicLatticeSite L, ‖A (x, μ) - A (periodicLatticeShift x μ, μ)‖ * ‖f (periodicLatticeShift x μ)‖) ^ 2
        ≤ (Real.sqrt Γ * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΓ0, ← hS2]
      exact hcs.trans (mul_le_mul_of_nonneg_right hS1 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    have := (pow_le_pow_iff_left₀ hP0 (by positivity) two_ne_zero).mp hsq
    linarith
  have hsplit : ⟪A, gradL2 (trivialU L) f⟫
      = ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ⟪A (x, μ), (gradL2 (trivialU L) f) (x, μ)⟫ := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type_right]
  have hle : ‖f‖ ^ 2 ≤ 3 * Real.sqrt Γ * ‖f‖ := by
    rw [hff, hsplit]
    calc ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ⟪A (x, μ), (gradL2 (trivialU L) f) (x, μ)⟫
        ≤ ∑ _μ : Fin 3, Real.sqrt Γ * ‖f‖ := Finset.sum_le_sum (fun μ _ => hμ μ)
      _ = 3 * Real.sqrt Γ * ‖f‖ := by simp; ring
  by_cases h0 : ‖f‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖f‖ * ‖f‖ ≤ (3 * Real.sqrt Γ) * ‖f‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-! ## covariant corrections -/

theorem curl_cov_diff (U : Cfg L) (e : ℝ) (he : ∀ b, AdalyFormal.CurvBlock.dv (U b) ≤ e) (A : BondFnL2 L) :
    ‖curlC U A - curlC (trivialU L) A‖ ≤ 12 * e * ‖A‖ := by
  have he0 : 0 ≤ e := le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (he (0, 0))
  have hpt : ∀ p : PeriodicLatticePlaquette L, ‖(curlC U A - curlC (trivialU L) A) p‖
      ≤ 2 * e * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖) := by
    intro p
    rw [PiLp.sub_apply, curlC_apply, curlC_apply]
    unfold curlValueCovariant
    rw [RMap_trivial, RMap_trivial]
    have e1 : ((WithLp.ofLp A) (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) ((WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (U (p.1, p.2.1.2)) ((WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - (WithLp.ofLp A) (p.1, p.2.1.2))
        - ((WithLp.ofLp A) (p.1, p.2.1.1) + (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
          - (WithLp.ofLp A) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - (WithLp.ofLp A) (p.1, p.2.1.2))
        = (RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)) - A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - (RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) := by
      show (A (p.1, p.2.1.1) + RMap (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
          - RMap (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)) - A (p.1, p.2.1.2))
        - (A (p.1, p.2.1.1) + A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
          - A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - A (p.1, p.2.1.2)) = _
      abel
    rw [e1]
    refine (norm_sub_le _ _).trans ?_
    have h1 := RMap_sub_id_le (U (p.1, p.2.1.1)) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
    have h2 := RMap_sub_id_le (U (p.1, p.2.1.2)) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
    have h3 : 2 * AdalyFormal.CurvBlock.dv (U (p.1, p.2.1.1)) * ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
        ≤ 2 * e * ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ :=
      mul_le_mul_of_nonneg_right (by linarith [he (p.1, p.2.1.1)]) (norm_nonneg _)
    have h4 : 2 * AdalyFormal.CurvBlock.dv (U (p.1, p.2.1.2)) * ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖
        ≤ 2 * e * ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ :=
      mul_le_mul_of_nonneg_right (by linarith [he (p.1, p.2.1.2)]) (norm_nonneg _)
    linarith
  have hsq : ‖curlC U A - curlC (trivialU L) A‖ ^ 2 ≤ (12 * e * ‖A‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hpt2 : ∀ p : PeriodicLatticePlaquette L, ‖(curlC U A - curlC (trivialU L) A) p‖ ^ 2
        ≤ 8 * e ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
      intro p
      have h := hpt p
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith [sq_nonneg (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
        - ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖)]
    have hs1 : ∀ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
        (‖A (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) ≤ 2 * ‖A‖ ^ 2 := by
      intro d
      rw [Finset.sum_add_distrib, sum_shift_site d.1.1 (fun y => ‖A (y, d.1.2)‖ ^ 2),
        sum_shift_site d.1.2 (fun y => ‖A (y, d.1.1)‖ ^ 2)]
      linarith [sum_dir_le A d.1.2, sum_dir_le A d.1.1]
    calc ∑ p, ‖(curlC U A - curlC (trivialU L) A) p‖ ^ 2
        ≤ ∑ p : PeriodicLatticePlaquette L, 8 * e ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
          + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := Finset.sum_le_sum (fun p _ => hpt2 p)
      _ = 8 * e ^ 2 * ∑ d : PeriodicPlaquetteDirections, ∑ x : PeriodicLatticeSite L,
          (‖A (periodicLatticeShift x d.1.1, d.1.2)‖ ^ 2 + ‖A (periodicLatticeShift x d.1.2, d.1.1)‖ ^ 2) := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ ≤ 8 * e ^ 2 * ∑ _d : PeriodicPlaquetteDirections, 2 * ‖A‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hs1 d)) (by positivity)
      _ = 8 * e ^ 2 * ((Fintype.card PeriodicPlaquetteDirections : ℝ) * (2 * ‖A‖ ^ 2)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 8 * e ^ 2 * (9 * (2 * ‖A‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right card_dirs_le (by positivity)) (by positivity)
      _ ≤ (12 * e * ‖A‖) ^ 2 := by nlinarith [sq_nonneg e, sq_nonneg ‖A‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem grad_cov_diff (U : Cfg L) (e : ℝ) (he : ∀ b, AdalyFormal.CurvBlock.dv (U b) ≤ e) (f : SiteL2 L) :
    ‖gradL2 U f - gradL2 (trivialU L) f‖ ≤ 2 * Real.sqrt 3 * e * ‖f‖ := by
  have he0 : 0 ≤ e := le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (he (0, 0))
  have hpt : ∀ b : Bond L, ‖(gradL2 U f - gradL2 (trivialU L) f) b‖ ≤ 2 * e * ‖f (periodicLatticeShift b.1 b.2)‖ := by
    intro b
    rw [PiLp.sub_apply]
    have e1 : (gradL2 U f) b - (gradL2 (trivialU L) f) b = RMap (U b) (f (periodicLatticeShift b.1 b.2))
        - f (periodicLatticeShift b.1 b.2) := by
      show gradValueCovariant U (WithLp.ofLp f) b - gradValueCovariant (trivialU L) (WithLp.ofLp f) b = _
      unfold gradValueCovariant
      rw [RMap_trivial]
      show RMap (U b) (f (periodicLatticeShift b.1 b.2)) - f b.1 - (f (periodicLatticeShift b.1 b.2) - f b.1) = _
      abel
    rw [e1]
    exact (RMap_sub_id_le _ _).trans (mul_le_mul_of_nonneg_right (by linarith [he b]) (norm_nonneg _))
  have hsq : ‖gradL2 U f - gradL2 (trivialU L) f‖ ^ 2 ≤ (2 * Real.sqrt 3 * e * ‖f‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ b, ‖(gradL2 U f - gradL2 (trivialU L) f) b‖ ^ 2
        ≤ ∑ b : Bond L, (2 * e) ^ 2 * ‖f (periodicLatticeShift b.1 b.2)‖ ^ 2 := by
          refine Finset.sum_le_sum (fun b _ => ?_)
          have h := pow_le_pow_left₀ (norm_nonneg _) (hpt b) 2
          rw [mul_pow] at h
          exact h
      _ = (2 * e) ^ 2 * ∑ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ‖f (periodicLatticeShift x μ)‖ ^ 2 := by
          rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
      _ = (2 * e) ^ 2 * (3 * ‖f‖ ^ 2) := by
          congr 1
          have hμ : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ‖f (periodicLatticeShift x μ)‖ ^ 2 = ‖f‖ ^ 2 := by
            intro μ; rw [PiLp.norm_sq_eq_of_L2, sum_shift_site μ (fun y => ‖f y‖ ^ 2)]
          rw [Finset.sum_congr rfl (fun μ _ => hμ μ), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
      _ = (2 * Real.sqrt 3 * e * ‖f‖) ^ 2 := by
          rw [show (2 * Real.sqrt 3 * e * ‖f‖) ^ 2 = 4 * Real.sqrt 3 ^ 2 * e ^ 2 * ‖f‖ ^ 2 by ring,
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem div_cov_diff (U : Cfg L) (e : ℝ) (he : ∀ b, AdalyFormal.CurvBlock.dv (U b) ≤ e) (A : BondFnL2 L) :
    ‖ContinuousLinearMap.adjoint (gradL2 U) A - ContinuousLinearMap.adjoint (gradL2 (trivialU L)) A‖
      ≤ 2 * Real.sqrt 3 * e * ‖A‖ := by
  have he0 : 0 ≤ e := le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (he (0, 0))
  have hop : ‖gradL2 U - gradL2 (trivialU L)‖ ≤ 2 * Real.sqrt 3 * e :=
    opnorm_le_of _ _ (by positivity) (fun f => by rw [ContinuousLinearMap.sub_apply]; exact grad_cov_diff U e he f)
  have e1 : ContinuousLinearMap.adjoint (gradL2 U) A - ContinuousLinearMap.adjoint (gradL2 (trivialU L)) A
      = ContinuousLinearMap.adjoint (gradL2 U - gradL2 (trivialU L)) A := by
    rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [e1]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)

#print axioms gradE_nonneg
#print axioms slice_le_gradE
#print axioms RMap_sub_id_le
#print axioms curl_flat_pt
#print axioms curl_flat_le
#print axioms grad_trivial_apply
#print axioms div_flat_le
#print axioms curl_cov_diff
#print axioms grad_cov_diff
#print axioms div_cov_diff

end AdalyFormal.DLayer

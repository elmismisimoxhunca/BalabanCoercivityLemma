import DE2

/-!
# DE3 -- the first-order interior estimate for `h = Δμ` (m1_w2_decay, 2026-10-13)

* `bond_ineq` : `((p²+q²)/4)‖b−a‖² ≤ ⟪b−a, q²b − p²a⟫ + ½(q−p)²‖a+b‖²` (any real inner product space);
* `inner_grad_grad` : `⟪D f, D g⟫ = ⟪Δ f, g⟫`;
* **`interior_bound`** : with `η = ramp w (s+1) B`, `Y = Ball w ρY` (`ρY ≥ s + 2 + B + 6ℓB`) and every class meeting
  `Ball w (s+1+B)` inside `K`:  `gradOn (Ball w s) h ≤ CB / B² · Σ_{x ∈ Y} ‖h x‖²`, `CB = 2 Kb + 12708`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1Decay

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (pdist)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.M1W2 (gradOn)

variable {L : PeriodicLatticeExtent}

/-- the constant of `interior_bound`. -/
noncomputable def CB : ℝ := 2 * Kb + 12708

theorem bond_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) (p q : ℝ) :
    (p ^ 2 + q ^ 2) / 4 * ‖b - a‖ ^ 2 ≤ ⟪b - a, q ^ 2 • b - p ^ 2 • a⟫ + 1 / 2 * (q - p) ^ 2 * ‖a + b‖ ^ 2 := by
  have e : q ^ 2 • b - p ^ 2 • a = ((p ^ 2 + q ^ 2) / 2) • (b - a) + ((q ^ 2 - p ^ 2) / 2) • (a + b) := by
    module
  rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  set X := ‖b - a‖
  set Y := ‖a + b‖
  set t := ⟪b - a, a + b⟫
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := norm_nonneg _
  have ht : |t| ≤ X * Y := abs_real_inner_le_norm _ _
  have h1 : |(q ^ 2 - p ^ 2) / 2 * t| ≤ |q + p| * X * (|q - p| * Y) / 2 := by
    rw [abs_mul, show q ^ 2 - p ^ 2 = (q + p) * (q - p) by ring, abs_div, abs_mul, abs_two]
    have : |q + p| * |q - p| / 2 * |t| ≤ |q + p| * |q - p| / 2 * (X * Y) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    linarith
  have h2 := neg_abs_le ((q ^ 2 - p ^ 2) / 2 * t)
  set u := |q + p| * X
  set v := |q - p| * Y
  have hu : u ^ 2 = (q + p) ^ 2 * X ^ 2 := by simp only [u]; rw [mul_pow, sq_abs]
  have hv : v ^ 2 = (q - p) ^ 2 * Y ^ 2 := by simp only [v]; rw [mul_pow, sq_abs]
  have hpq : (q + p) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by nlinarith [sq_nonneg (q - p)]
  have hX2 : (q + p) ^ 2 * X ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) * X ^ 2 := mul_le_mul_of_nonneg_right hpq (sq_nonneg _)
  nlinarith [sq_nonneg (u - 2 * v)]

theorem inner_grad_grad (f g : SiteL2 L) :
    ⟪gradL2 (U0 L) f, gradL2 (U0 L) g⟫ = ⟪lapFull (U0 L) f, g⟫ := by
  show _ = ⟪gradAdj (U0 L) (gradL2 (U0 L) f), g⟫
  rw [gradAdj, ContinuousLinearMap.adjoint_inner_left]

theorem inner_bond (A A' : BondFnL2 L) :
    ⟪A, A'⟫ = ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ⟪A (x, μ), A' (x, μ)⟫ := by
  rw [PiLp.inner_apply]
  exact Fintype.sum_prod_type _

/-- `Δ F` vanishes far from the support of `F`. -/
theorem lap_zero_far (F : SiteL2 L) (w : PeriodicLatticeSite L) (ρ : ℕ) (hF : ∀ z, ρ ≤ pdist w z → F z = 0)
    (x : PeriodicLatticeSite L) (hx : ρ + 1 ≤ pdist w x) : lapFull (U0 L) F x = 0 := by
  rw [lap_flat]
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h1 := pdist_triangle w (periodicLatticeShift x μ) x
  have h2 := pdist_shift_le x μ
  rw [pdist_comm] at h2
  have h3 := pdist_triangle w (periodicLatticeShiftBack x μ) x
  have h4 := pdist_back_le x μ
  rw [pdist_comm] at h4
  rw [hF x (by omega), hF _ (by omega), hF _ (by omega)]
  simp

namespace Classes
variable {B ell : ℕ} (Cl : Classes L B ell)

open Classical in
/-- **the interior estimate**. -/
theorem interior_bound (hell : 2 ≤ ell) (hB : 1 ≤ B) (μ : SiteL2 L) (K : Set (PeriodicLatticeSite L))
    (hconst : ∀ x, (∀ z ∈ Cl.cls x, z ∈ K) → ∀ z ∈ Cl.cls x,
      lapFull (U0 L) (lapFull (U0 L) μ) z = lapFull (U0 L) (lapFull (U0 L) μ) x)
    (w : PeriodicLatticeSite L) (s ρY : ℕ) (hρY : s + 2 + B + 6 * (ell * B) ≤ ρY)
    (hKY : ∀ x, pdist w x ≤ s + 1 + B → ∀ z ∈ Cl.cls x, z ∈ K) :
    gradOn (U0 L) (Ball w s) (lapFull (U0 L) μ)
      ≤ CB / (B : ℝ) ^ 2 * ∑ x, (if pdist w x ≤ ρY then ‖lapFull (U0 L) μ x‖ ^ 2 else 0) := by
  set h := lapFull (U0 L) μ with hh
  set k := lapFull (U0 L) h with hk
  set η := ramp w (s + 1) B with hη
  set hY : SiteL2 L := WithLp.toLp 2 (fun z => if pdist w z ≤ ρY then h z else 0) with hhY
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hYn : ‖hY‖ ^ 2 = ∑ x, (if pdist w x ≤ ρY then ‖h x‖ ^ 2 else 0) := by
    rw [normSq_site]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    show ‖(if pdist w x ≤ ρY then h x else 0)‖ ^ 2 = _
    split_ifs <;> simp
  rw [← hYn]
  have hηlip := ramp_lip w (s + 1) B hB
  have hη0 : ∀ x, 0 ≤ η x := ramp_nonneg w (s + 1) B
  have hη1 : ∀ x, η x ≤ 1 := ramp_le_one w (s + 1) B
  have hηone : ∀ x, pdist w x ≤ s + 1 → η x = 1 := fun x hx => ramp_one w (s + 1) B hB x hx
  have hηzero : ∀ x, s + 1 + B ≤ pdist w x → η x = 0 := fun x hx => ramp_zero w (s + 1) B hB x hx
  have hηY : ∀ x, η x ≠ 0 → pdist w x ≤ s + 1 + B := by
    intro x hx; by_contra hc; exact hx (hηzero x (by omega))
  have hYeq : ∀ x, pdist w x ≤ ρY → hY x = h x := fun x hx => by
    show (if pdist w x ≤ ρY then h x else 0) = h x; rw [if_pos hx]
  -- step 1: gradOn ≤ Σ ((p²+q²)/2)‖Dh‖²
  set W : PeriodicLatticeSite L → Fin 3 → ℝ := fun x μ =>
    (η x ^ 2 + η (periodicLatticeShift x μ) ^ 2) / 4 * ‖h (periodicLatticeShift x μ) - h x‖ ^ 2 with hW
  have step1 : gradOn (U0 L) (Ball w s) h ≤ 2 * ∑ x, ∑ μ : Fin 3, W x μ := by
    unfold gradOn
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun μ _ => ?_)
    have hWnn : 0 ≤ W x μ := by simp only [hW]; positivity
    split_ifs with hb
    · have hs1 := pdist_shift_le x μ
      have hx1 : pdist w x ≤ s + 1 := by
        rcases hb with hb | hb
        · exact le_trans hb (Nat.le_succ s)
        · have := pdist_triangle w (periodicLatticeShift x μ) x
          rw [pdist_comm (periodicLatticeShift x μ) x] at this
          have hb' : pdist w (periodicLatticeShift x μ) ≤ s := hb
          omega
      have hx2 : pdist w (periodicLatticeShift x μ) ≤ s + 1 := by
        rcases hb with hb | hb
        · have := pdist_triangle w x (periodicLatticeShift x μ)
          have hb' : pdist w x ≤ s := hb
          omega
        · exact le_trans hb (Nat.le_succ s)
      simp only [hW]
      rw [hηone x hx1, hηone _ hx2, grad_flat]
      dsimp only
      apply le_of_eq; ring
    · linarith
  -- step 2: bond inequality summed
  set Fη : SiteL2 L := mulR (fun z => η z ^ 2) h with hFη
  have step2 : ∑ x, ∑ μ : Fin 3, W x μ ≤ ⟪k, Fη⟫ + ∑ x, ∑ μ : Fin 3,
      1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 * ‖h x + h (periodicLatticeShift x μ)‖ ^ 2 := by
    have e : ⟪k, Fη⟫ = ∑ x, ∑ μ : Fin 3, ⟪h (periodicLatticeShift x μ) - h x,
        η (periodicLatticeShift x μ) ^ 2 • h (periodicLatticeShift x μ) - η x ^ 2 • h x⟫ := by
      rw [hk, ← inner_grad_grad, inner_bond]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun μ _ => ?_))
      rw [grad_flat, grad_flat]
      rfl
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun μ _ => ?_)
    exact bond_ineq (h x) (h (periodicLatticeShift x μ)) (η x) (η (periodicLatticeShift x μ))
  -- step 3: the gradient-of-cutoff terms
  have step3 : ∑ x, ∑ μ : Fin 3, 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 * ‖h x + h (periodicLatticeShift x μ)‖ ^ 2
      ≤ 6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
    have hpt : ∀ x (μ : Fin 3), 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 * ‖h x + h (periodicLatticeShift x μ)‖ ^ 2
        ≤ 1 / (B : ℝ) ^ 2 * (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) := by
      intro x μ
      by_cases heq : η (periodicLatticeShift x μ) = η x
      · rw [heq, sub_self]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul]
        positivity
      · have hs1 := pdist_shift_le x μ
        have hboth : pdist w x ≤ ρY ∧ pdist w (periodicLatticeShift x μ) ≤ ρY := by
          by_cases h0 : η x = 0
          · have h1 : η (periodicLatticeShift x μ) ≠ 0 := by rw [h0] at heq; exact heq
            have h2 := hηY _ h1
            have := pdist_triangle w (periodicLatticeShift x μ) x
            rw [pdist_comm (periodicLatticeShift x μ) x] at this
            constructor <;> omega
          · have h2 := hηY _ h0
            have := pdist_triangle w x (periodicLatticeShift x μ)
            constructor <;> omega
        rw [hYeq x hboth.1, hYeq _ hboth.2]
        have hl : |η (periodicLatticeShift x μ) - η x| ≤ 1 / B := by
          have := hηlip (periodicLatticeShift x μ) x
          rw [pdist_comm] at this
          have hp : (pdist x (periodicLatticeShift x μ) : ℝ) ≤ 1 := by exact_mod_cast hs1
          calc |η (periodicLatticeShift x μ) - η x| ≤ 1 / B * (pdist x (periodicLatticeShift x μ) : ℝ) := this
            _ ≤ 1 / B * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
            _ = 1 / B := by ring
        have hl2 : (η (periodicLatticeShift x μ) - η x) ^ 2 ≤ 1 / (B : ℝ) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hl 2
          rw [sq_abs, div_pow, one_pow] at this; exact this
        have hab : ‖h x + h (periodicLatticeShift x μ)‖ ^ 2 ≤ 2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2) := by
          have := norm_add_le (h x) (h (periodicLatticeShift x μ))
          nlinarith [norm_nonneg (h x + h (periodicLatticeShift x μ)), norm_nonneg (h x),
            norm_nonneg (h (periodicLatticeShift x μ)), sq_nonneg (‖h x‖ - ‖h (periodicLatticeShift x μ)‖)]
        calc 1 / 2 * (η (periodicLatticeShift x μ) - η x) ^ 2 * ‖h x + h (periodicLatticeShift x μ)‖ ^ 2
            ≤ 1 / 2 * (1 / (B : ℝ) ^ 2) * (2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hl2 (by norm_num)) hab (sq_nonneg _) (by positivity)
          _ = 1 / (B : ℝ) ^ 2 * (‖h x‖ ^ 2 + ‖h (periodicLatticeShift x μ)‖ ^ 2) := by ring
    calc _ ≤ ∑ x, ∑ μ : Fin 3, 1 / (B : ℝ) ^ 2 * (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) :=
          Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun μ _ => hpt x μ))
      _ = 1 / (B : ℝ) ^ 2 * ∑ x, ∑ μ : Fin 3, (‖hY x‖ ^ 2 + ‖hY (periodicLatticeShift x μ)‖ ^ 2) := by
          simp only [Finset.mul_sum]
      _ = 6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_add_distrib, sum_shift (fun y => ‖hY y‖ ^ 2), Fin.sum_univ_three]
          rw [normSq_site]; ring
  -- step 4: the Δh term
  have step4 : ⟪k, Fη⟫ ≤ (Kb + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
    have hFηY : Fη = mulR (fun z => η z ^ 2) hY := by
      ext1 z
      show η z ^ 2 • h z = η z ^ 2 • (if pdist w z ≤ ρY then h z else 0)
      by_cases hz : η z = 0
      · rw [hz]; simp
      · rw [if_pos (by have := hηY z hz; omega)]
    by_cases hB24 : 24 ≤ B
    · set A : PeriodicLatticeSite L → ℝ := fun x => if η x ≠ 0 then ‖k x‖ else 0 with hA
      have hterm : ∀ x, ⟪k x, Fη x⟫ ≤ A x * ‖hY x‖ := by
        intro x
        show ⟪k x, η x ^ 2 • h x⟫ ≤ _
        by_cases hx : η x = 0
        · rw [hx]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul, inner_zero_right]
          have : A x = 0 := if_neg (not_not.mpr hx); rw [this, zero_mul]
        · have hAx : A x = ‖k x‖ := if_pos hx
          rw [hAx, hYeq x (by have := hηY x hx; omega), real_inner_smul_right]
          have h4 : ⟪k x, h x⟫ ≤ ‖k x‖ * ‖h x‖ := real_inner_le_norm _ _
          have h0 : 0 ≤ η x ^ 2 := sq_nonneg _
          have h2 : η x ^ 2 ≤ 1 := by
            have a1 := hη1 x
            have a0 := hη0 x
            calc η x ^ 2 = η x * η x := sq _
              _ ≤ 1 * 1 := mul_le_mul a1 a1 a0 zero_le_one
              _ = 1 := one_mul 1
          have h3 : 0 ≤ ‖k x‖ * ‖h x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
          calc η x ^ 2 * ⟪k x, h x⟫ ≤ η x ^ 2 * (‖k x‖ * ‖h x‖) := mul_le_mul_of_nonneg_left h4 h0
            _ ≤ 1 * (‖k x‖ * ‖h x‖) := mul_le_mul_of_nonneg_right h2 h3
            _ = ‖k x‖ * ‖h x‖ := one_mul _
      have hA2 : ∀ x, A x ^ 2 ≤ Kb2 * ((Cl.nn x : ℝ) ^ 7)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := by
        intro x
        by_cases hx : η x = 0
        · have : A x = 0 := if_neg (not_not.mpr hx)
          rw [this]
          have : 0 ≤ Kb2 := by unfold Kb2; norm_num
          have h0 : 0 ≤ ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
          have hn : (0 : ℝ) ≤ ((Cl.nn x : ℝ) ^ 7)⁻¹ := by positivity
          have : (0 : ℝ) ^ 2 = 0 := by norm_num
          rw [this]; positivity
        · have hAx : A x = ‖k x‖ := if_pos hx
          rw [hAx]
          have hxs := hηY x hx
          have hin := hKY x hxs
          have hn24 : 24 ≤ Cl.nn x := le_trans hB24 (Cl.nn_ge x)
          have hbb := bump_bound (Cl.anc x) (Cl.nn x) hn24 (Cl.fit x) h (k x) (by
            intro z hz
            rw [← Cl.cls_eq_block] at hz
            exact hconst x hin z hz)
          rw [← Cl.cls_eq_block] at hbb
          have hsY : ∑ z ∈ Cl.cls x, ‖h z‖ ^ 2 = ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun z hz => ?_)
            have h1 := Cl.pdist_in_cls x z hz
            have h2 := pdist_triangle w x z
            have h3 := Cl.nn_le x
            rw [hYeq z (by
              have : 6 * Cl.nn x ≤ 6 * (ell * B) := by omega
              omega)]
          rw [hsY] at hbb
          have hnpos : (0 : ℝ) < Cl.nn x := by
            have : (B : ℝ) ≤ Cl.nn x := by exact_mod_cast Cl.nn_ge x
            linarith
          rw [show Kb2 * ((Cl.nn x : ℝ) ^ 7)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2
              = (Kb2 * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2) / (Cl.nn x : ℝ) ^ 7 by ring]
          rw [le_div_iff₀ (by positivity)]
          exact hbb
      have hsumA : ∑ x, A x ^ 2 ≤ Kb2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2 := by
        calc ∑ x, A x ^ 2 ≤ ∑ x, Kb2 * ((Cl.nn x : ℝ) ^ 7)⁻¹ * ∑ z ∈ Cl.cls x, ‖hY z‖ ^ 2 :=
              Finset.sum_le_sum (fun x _ => hA2 x)
          _ = ∑ z, ‖hY z‖ ^ 2 * (Kb2 * ((Cl.nn z : ℝ) ^ 7)⁻¹ * (Cl.nn z : ℝ) ^ 3) :=
              Cl.sum_cls_const (fun n => Kb2 * ((n : ℝ) ^ 7)⁻¹) (fun z => ‖hY z‖ ^ 2)
          _ ≤ ∑ z, ‖hY z‖ ^ 2 * (Kb2 * ((B : ℝ) ^ 4)⁻¹) := by
              refine Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
              have hn : (B : ℝ) ≤ Cl.nn z := by exact_mod_cast Cl.nn_ge z
              have hnpos : (0 : ℝ) < Cl.nn z := by linarith
              have e : Kb2 * ((Cl.nn z : ℝ) ^ 7)⁻¹ * (Cl.nn z : ℝ) ^ 3 = Kb2 * ((Cl.nn z : ℝ) ^ 4)⁻¹ := by
                field_simp
              rw [e]
              have hK0 : 0 ≤ Kb2 := by unfold Kb2; norm_num
              exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hn 4)) hK0
          _ = Kb2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2 := by
              rw [normSq_site, Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A (fun x => ‖hY x‖)
      have hA0 : 0 ≤ ∑ x, A x * ‖hY x‖ := by
        refine Finset.sum_nonneg (fun x _ => mul_nonneg ?_ (norm_nonneg _))
        simp only [hA]; split_ifs <;> simp
      have hsq : (∑ x, A x * ‖hY x‖) ^ 2 ≤ (Kb / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) ^ 2 := by
        calc (∑ x, A x * ‖hY x‖) ^ 2 ≤ (∑ x, A x ^ 2) * ∑ x, ‖hY x‖ ^ 2 := hCS
          _ ≤ (Kb2 * ((B : ℝ) ^ 4)⁻¹ * ‖hY‖ ^ 2) * ‖hY‖ ^ 2 := by
              rw [← normSq_site]
              exact mul_le_mul_of_nonneg_right hsumA (sq_nonneg _)
          _ = (Kb / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) ^ 2 := by rw [Kb2_eq]; field_simp
      have hRHS0 : 0 ≤ Kb / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
        have := Kb_pos
        exact mul_nonneg (div_nonneg this.le (by positivity)) (sq_nonneg _)
      have hle := (pow_le_pow_iff_left₀ hA0 hRHS0 (by norm_num)).mp hsq
      have hsplit : ⟪k, Fη⟫ ≤ ∑ x, A x * ‖hY x‖ := by
        rw [PiLp.inner_apply]; exact Finset.sum_le_sum (fun x _ => hterm x)
      have : Kb / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 ≤ (Kb + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    · have hB23 : (B : ℝ) ≤ 23 := by
        have : B ≤ 23 := by omega
        exact_mod_cast this
      have hsupp : ∀ z, s + 1 + B ≤ pdist w z → Fη z = 0 := by
        intro z hz
        show η z ^ 2 • h z = 0
        rw [hηzero z hz]; simp
      have hlapY : ⟪h, lapFull (U0 L) Fη⟫ = ⟪hY, lapFull (U0 L) Fη⟫ := by
        rw [PiLp.inner_apply, PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : pdist w x ≤ ρY
        · rw [hYeq x hx]
        · rw [lap_zero_far Fη w (s + 1 + B) hsupp x (by omega)]
          simp
      have h1 : ⟪k, Fη⟫ = ⟪hY, lapFull (U0 L) Fη⟫ := by rw [hk, lapFull_symm, hlapY]
      have h2 : ‖Fη‖ ≤ ‖hY‖ := by
        rw [hFηY]
        have := norm_mulR_le (fun z => η z ^ 2) hY 1 (by norm_num) (fun z => by
          rw [abs_of_nonneg (sq_nonneg _)]; have := hη1 z; have := hη0 z; nlinarith)
        linarith
      have h3 : ⟪k, Fη⟫ ≤ 12 * ‖hY‖ ^ 2 := by
        rw [h1]
        calc ⟪hY, lapFull (U0 L) Fη⟫ ≤ ‖hY‖ * ‖lapFull (U0 L) Fη‖ := real_inner_le_norm _ _
          _ ≤ ‖hY‖ * (12 * ‖Fη‖) := mul_le_mul_of_nonneg_left (lap_norm_le Fη) (norm_nonneg _)
          _ ≤ ‖hY‖ * (12 * ‖hY‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ = 12 * ‖hY‖ ^ 2 := by ring
      have h4 : 12 ≤ (Kb + 6348) / (B : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have := Kb_pos
        have hBB := mul_le_mul hB23 hB23 (by positivity) (by norm_num)
        nlinarith
      calc ⟪k, Fη⟫ ≤ 12 * ‖hY‖ ^ 2 := h3
        _ ≤ (Kb + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  -- assemble
  unfold CB
  have e : (2 * Kb + 12708) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2
      = 2 * ((Kb + 6348) / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) + 2 * (6 / (B : ℝ) ^ 2 * ‖hY‖ ^ 2) := by ring
  rw [e]
  linarith

end Classes

end AdalyFormal.M1Decay

#print axioms AdalyFormal.M1Decay.bond_ineq
#print axioms AdalyFormal.M1Decay.inner_grad_grad
#print axioms AdalyFormal.M1Decay.lap_zero_far
#print axioms AdalyFormal.M1Decay.Classes.interior_bound

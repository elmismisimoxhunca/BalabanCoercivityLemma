import DLR78

/-!
# DL79 -- the operator `M_ψ` of `Δ⁽²⁾` (`⟨u, M_ψ v⟩ = 2⟨β(u,v), ψ⟩`): norm and WEIGHTED COMMUTATOR bounds (full tower)

* `psiForm`, `Mpsi := symmOp psiForm`; `Mpsi_inner` : `⟨u, M_ψ v⟩ = 2⟨β(u,v), ψ⟩`; `Mpsi_symm`;
* **`Mpsi_norm`** : `‖ψ p‖ ≤ S` (all `p`) and `Σ_p‖C2fullOf z p‖ ≤ K‖z‖²` ⇒ `‖M_ψ‖ ≤ 2SK`;
* **`Mpsi_cjp`** : with `WtLip (θ/n) φ`, `n = ℓ^k`:  `‖e^φ M_ψ e^{−φ} − M_ψ‖ ≤ 2SK·648·(e^{5θ} − 1)(e^{5θ} + 1)`
  (footprint radius `≤ 5n` (`Rfoot_le`), the base-point factor `e^{φ(y_p)}` cancels in the bilinear `β`, multiplicity 648);
  `Mpsi_cjm` (the same for `e^{−φ} M_ψ e^{φ}`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (RegTower bgTower Cfg C2fullOf C2fullOf_quad BIdx FSp symmOp symmOp_symm
  inner_bilinOp bilinOp)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent) (U : Cfg (scaleUp ell k Lu))

/-- the bilinear form `(u,v) ↦ ⟨B u v + B v u, ψ⟩ = 2⟨β(u,v), ψ⟩` -/
noncomputable def psiForm (ψ : FSp (GF ell k Lu)) :
    BondFnL2 (scaleUp ell k Lu) →ₗ[ℝ] BondFnL2 (scaleUp ell k Lu) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => ⟪(C2fullOf_quad (GF ell k Lu) U).choose u v + (C2fullOf_quad (GF ell k Lu) U).choose v u, ψ⟫)
    (fun u1 u2 v => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c u v => by simp only [map_smul, LinearMap.smul_apply, inner_add_left, real_inner_smul_left]; ring)
    (fun u v1 v2 => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c u v => by simp only [map_smul, LinearMap.smul_apply, inner_add_left, real_inner_smul_left]; ring)

theorem psiForm_eq (ψ : FSp (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    psiForm ell k Lu U ψ u v = 2 * ⟪polar (GF ell k Lu) U u v, ψ⟫ := by
  rw [polar_eq, real_inner_smul_left]
  show ⟪(C2fullOf_quad (GF ell k Lu) U).choose u v + (C2fullOf_quad (GF ell k Lu) U).choose v u, ψ⟫ = _
  ring

theorem psiForm_symm (ψ : FSp (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    psiForm ell k Lu U ψ u v = psiForm ell k Lu U ψ v u := by
  show ⟪_ + _, ψ⟫ = ⟪_ + _, ψ⟫
  rw [add_comm]

/-- `M_ψ` -/
noncomputable def Mpsi (ψ : FSp (GF ell k Lu)) : BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  symmOp (psiForm ell k Lu U ψ)

theorem Mpsi_inner (ψ : FSp (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    ⟪u, Mpsi ell k Lu U ψ v⟫ = 2 * ⟪polar (GF ell k Lu) U u v, ψ⟫ := by
  unfold Mpsi symmOp
  rw [inner_bilinOp]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  rw [psiForm_symm ell k Lu U ψ v u, psiForm_eq]
  ring

theorem Mpsi_symm (ψ : FSp (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    ⟪Mpsi ell k Lu U ψ u, v⟫ = ⟪u, Mpsi ell k Lu U ψ v⟫ := symmOp_symm _ u v

/-- the pairing with a sup-bounded `ψ` -/
theorem pair_le (ψ : FSp (GF ell k Lu)) (S : ℝ) (hψ : ∀ p, ‖ψ p‖ ≤ S) (X : FSp (GF ell k Lu)) :
    |⟪X, ψ⟫| ≤ S * ∑ p, ‖X p‖ := by
  rw [PiLp.inner_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hψ p) (norm_nonneg _)

theorem Mpsi_bil (ψ : FSp (GF ell k Lu)) (S K : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (u v : BondFnL2 (scaleUp ell k Lu)) : |⟪u, Mpsi ell k Lu U ψ v⟫| ≤ 2 * S * K * ‖u‖ * ‖v‖ := by
  rw [Mpsi_inner, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1 := pair_le ell k Lu ψ S hψ (polar (GF ell k Lu) U u v)
  have h2 := polar_l1 (GF ell k Lu) U K hK hC u v
  have := mul_le_mul_of_nonneg_left h2 hS
  nlinarith

theorem opNorm_le_of_bil {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (M : E →L[ℝ] E) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ u v, |⟪u, M v⟫| ≤ C * ‖u‖ * ‖v‖) : ‖M‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun v => ?_)
  have h1 := h (M v) v
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
  by_cases hv : ‖M v‖ = 0
  · rw [hv]; positivity
  have hpos : 0 < ‖M v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  nlinarith

theorem Mpsi_norm (ψ : FSp (GF ell k Lu)) (S K : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2) :
    ‖Mpsi ell k Lu U ψ‖ ≤ 2 * S * K :=
  opNorm_le_of_bil _ _ (by positivity) (fun u v => Mpsi_bil ell k Lu U ψ S K hS hK hψ hC u v)

/-! ## the weighted commutator -/

open Classical in
/-- multiplication by `g` on the footprint of `p` -/
noncomputable def footMul (p : BIdx (GF ell k Lu)) (g : Bond (scaleUp ell k Lu) → ℝ)
    (u : BondFnL2 (scaleUp ell k Lu)) : BondFnL2 (scaleUp ell k Lu) :=
  WithLp.toLp 2 (fun e => if Foot ell (p.1 : ℕ) p.2.1 e then g e • u e else 0)

open Classical in
theorem footMul_le (p : BIdx (GF ell k Lu)) (g : Bond (scaleUp ell k Lu) → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hg : ∀ e, Foot ell (p.1 : ℕ) p.2.1 e → |g e| ≤ d) (u : BondFnL2 (scaleUp ell k Lu)) :
    ‖footMul ell k Lu p g u‖ ≤ d * ‖footRes ell k Lu p u‖ := by
  have h1 : ‖footMul ell k Lu p g u‖ ^ 2 ≤ (d * ‖footRes ell k Lu p u‖) ^ 2 := by
    rw [mul_pow, footRes_sq, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    show ‖(if Foot ell (p.1 : ℕ) p.2.1 e then g e • u e else 0)‖ ^ 2 ≤ d ^ 2 * (if Foot ell (p.1 : ℕ) p.2.1 e then ‖u e‖ ^ 2 else 0)
    split_ifs with he
    · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have := hg e he
      have h2 : g e ^ 2 ≤ d ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    · simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1

open Classical in
theorem footRes_footMul (p : BIdx (GF ell k Lu)) (g : Bond (scaleUp ell k Lu) → ℝ) (u : BondFnL2 (scaleUp ell k Lu)) :
    footRes ell k Lu p (footMul ell k Lu p g u) = footMul ell k Lu p g u := by
  refine PiLp.ext fun e => ?_
  show (if Foot ell (p.1 : ℕ) p.2.1 e then (footMul ell k Lu p g u) e else 0) = (footMul ell k Lu p g u) e
  split_ifs with he
  · rfl
  · show (0 : SuTwo) = (if Foot ell (p.1 : ℕ) p.2.1 e then g e • u e else 0)
    rw [if_neg he]

theorem polar_add_left (u u' v : BondFnL2 (scaleUp ell k Lu)) :
    polar (GF ell k Lu) U (u + u') v = polar (GF ell k Lu) U u v + polar (GF ell k Lu) U u' v := by
  rw [polar_eq, polar_eq, polar_eq]; simp only [map_add, LinearMap.add_apply, smul_add]; abel

theorem polar_add_right (u v v' : BondFnL2 (scaleUp ell k Lu)) :
    polar (GF ell k Lu) U u (v + v') = polar (GF ell k Lu) U u v + polar (GF ell k Lu) U u v' := by
  rw [polar_eq, polar_eq, polar_eq]; simp only [map_add, LinearMap.add_apply, smul_add]; abel

open Classical in
theorem Mpsi_cjp (hell2 : 2 ≤ ell) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (ψ : FSp (GF ell k Lu)) (S K : ℝ) (hS : 0 ≤ S) (hK : 0 ≤ K) (hψ : ∀ p, ‖ψ p‖ ≤ S)
    (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (hφ : WtLip (θ / (ell : ℝ) ^ k) φ) :
    ‖cjp (bondWP φ) (bondWP φ) (Mpsi ell k Lu U ψ) - Mpsi ell k Lu U ψ‖
      ≤ 2 * S * K * 648 * ((Real.exp (5 * θ) - 1) * (Real.exp (5 * θ) + 1)) := by
  have hell : 0 < ell := by omega
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := by positivity
  set d := Real.exp (5 * θ) - 1 with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith [Real.add_one_le_exp (5 * θ)]
  set M := Mpsi ell k Lu U ψ with hM
  -- the per-row difference
  have hrow : ∀ (p : BIdx (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)),
      ‖(polar (GF ell k Lu) U (bondWt φ u) (bondWt (-φ) v) - polar (GF ell k Lu) U u v) p‖
        ≤ K * (d * (Real.exp (5 * θ) + 1)) * (‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖) := by
    intro p u v
    set y : PeriodicLatticeSite (scaleUp ell k Lu) := p.2.1.1 with hy
    -- the footprint is within reach `5n` of `y`
    have hreach : ∀ e, Foot ell (p.1 : ℕ) p.2.1 e → |φ e.1 - φ y| ≤ 5 * θ := by
      intro e he
      have hf := Foot_reach ell hell (p.1 : ℕ) p.2.1 e he
      have hl := Reach_lip _ φ hφ hf
      have hR : (Rfoot ell (p.1 : ℕ) : ℝ) ≤ 5 * (ell : ℝ) ^ k := by
        have h1 := Rfoot_le ell hell2 (p.1 : ℕ)
        have h2 : (ell : ℝ) ^ (p.1 : ℕ) ≤ (ell : ℝ) ^ k :=
          pow_le_pow_right₀ (by exact_mod_cast hell) (Nat.lt_succ_iff.mp p.1.isLt)
        have h3 : (Rfoot ell (p.1 : ℕ) : ℝ) ≤ 5 * (ell : ℝ) ^ (p.1 : ℕ) := by exact_mod_cast h1
        linarith
      have : (Rfoot ell (p.1 : ℕ) : ℝ) * (θ / (ell : ℝ) ^ k) ≤ 5 * θ := by
        rw [mul_div_assoc', div_le_iff₀ hn]; nlinarith
      linarith
    set a : Bond (scaleUp ell k Lu) → ℝ := fun e => Real.exp (φ e.1 - φ y) with ha
    set ai : Bond (scaleUp ell k Lu) → ℝ := fun e => Real.exp (-(φ e.1 - φ y)) with hai
    have hX : footRes ell k Lu p (bondWt φ u) = Real.exp (φ y) • footMul ell k Lu p a u := by
      refine PiLp.ext fun e => ?_
      show (if Foot ell (p.1 : ℕ) p.2.1 e then (bondWt φ u) e else 0)
        = Real.exp (φ y) • (if Foot ell (p.1 : ℕ) p.2.1 e then a e • u e else 0)
      split_ifs
      · rw [bondWt_apply, smul_smul, ha]; congr 1; rw [← Real.exp_add]; ring_nf
      · simp
    have hY : footRes ell k Lu p (bondWt (-φ) v) = (Real.exp (φ y))⁻¹ • footMul ell k Lu p ai v := by
      refine PiLp.ext fun e => ?_
      show (if Foot ell (p.1 : ℕ) p.2.1 e then (bondWt (-φ) v) e else 0)
        = (Real.exp (φ y))⁻¹ • (if Foot ell (p.1 : ℕ) p.2.1 e then ai e • v e else 0)
      split_ifs
      · rw [bondWt_apply, smul_smul, hai, ← Real.exp_neg]; congr 1; rw [← Real.exp_add]; congr 1
        simp only [Pi.neg_apply]; ring
      · simp
    have hu1 : footRes ell k Lu p u = footMul ell k Lu p (fun _ => 1) u := by
      refine PiLp.ext fun e => ?_
      show (if Foot ell (p.1 : ℕ) p.2.1 e then u e else 0) = (if Foot ell (p.1 : ℕ) p.2.1 e then (1 : ℝ) • u e else 0)
      simp
    have hv1 : footRes ell k Lu p v = footMul ell k Lu p (fun _ => 1) v := by
      refine PiLp.ext fun e => ?_
      show (if Foot ell (p.1 : ℕ) p.2.1 e then v e else 0) = (if Foot ell (p.1 : ℕ) p.2.1 e then (1 : ℝ) • v e else 0)
      simp
    -- rewrite both polars on the footprint
    have e1 : polar (GF ell k Lu) U (bondWt φ u) (bondWt (-φ) v) p
        = polar (GF ell k Lu) U (footMul ell k Lu p a u) (footMul ell k Lu p ai v) p := by
      rw [polar_row_congr ell k Lu hell U hreg p, hX, hY, polar_scale _ _ _ _ _ (Real.exp_pos _).ne']
    have e2 : polar (GF ell k Lu) U u v p
        = polar (GF ell k Lu) U (footMul ell k Lu p (fun _ => 1) u) (footMul ell k Lu p (fun _ => 1) v) p := by
      rw [polar_row_congr ell k Lu hell U hreg p, hu1, hv1]
    have hsubm : ∀ (g g' : Bond (scaleUp ell k Lu) → ℝ) (w : BondFnL2 (scaleUp ell k Lu)),
        footMul ell k Lu p g w - footMul ell k Lu p g' w = footMul ell k Lu p (g - g') w := by
      intro g g' w
      refine PiLp.ext fun e => ?_
      show (if Foot ell (p.1 : ℕ) p.2.1 e then g e • w e else 0) - (if Foot ell (p.1 : ℕ) p.2.1 e then g' e • w e else 0)
        = (if Foot ell (p.1 : ℕ) p.2.1 e then (g - g') e • w e else 0)
      split_ifs <;> simp [sub_smul]
    -- bilinear split
    set X1 := footMul ell k Lu p a u
    set Y1 := footMul ell k Lu p ai v
    set X0 := footMul ell k Lu p (fun _ => 1) u
    set Y0 := footMul ell k Lu p (fun _ => 1) v
    have split : polar (GF ell k Lu) U X1 Y1 - polar (GF ell k Lu) U X0 Y0
        = polar (GF ell k Lu) U (X1 - X0) Y1 + polar (GF ell k Lu) U X0 (Y1 - Y0) := by
      simp only [polar_eq, map_sub, LinearMap.sub_apply, smul_sub, smul_add]
      abel
    rw [PiLp.sub_apply, e1, e2, ← PiLp.sub_apply, split, PiLp.add_apply]
    refine (norm_add_le _ _).trans ?_
    rw [hsubm, hsubm]
    have b1 := polar_row ell k Lu hell U hreg K hK hC p (X1 - X0) Y1
    have b2 := polar_row ell k Lu hell U hreg K hK hC p X0 (Y1 - Y0)
    rw [hsubm, footRes_footMul, footRes_footMul] at b1
    rw [hsubm, footRes_footMul, footRes_footMul] at b2
    have n1 : ‖footMul ell k Lu p (a - fun _ => 1) u‖ ≤ d * ‖footRes ell k Lu p u‖ :=
      footMul_le ell k Lu p _ d hd0 (fun e he => by
        have := hreach e he
        show |Real.exp (φ e.1 - φ y) - 1| ≤ d
        refine (abs_exp_sub_one_le _).trans ?_
        rw [hd]; linarith [Real.exp_le_exp.mpr this]) u
    have n2 : ‖Y1‖ ≤ Real.exp (5 * θ) * ‖footRes ell k Lu p v‖ :=
      footMul_le ell k Lu p _ _ (Real.exp_pos _).le (fun e he => by
        have := hreach e he
        show |Real.exp (-(φ e.1 - φ y))| ≤ Real.exp (5 * θ)
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by rw [abs_le] at this; linarith)) v
    have n3 : ‖X0‖ ≤ 1 * ‖footRes ell k Lu p u‖ :=
      footMul_le ell k Lu p _ 1 zero_le_one (fun e _ => by simp) u
    have n4 : ‖footMul ell k Lu p (ai - fun _ => 1) v‖ ≤ d * ‖footRes ell k Lu p v‖ :=
      footMul_le ell k Lu p _ d hd0 (fun e he => by
        have := hreach e he
        show |Real.exp (-(φ e.1 - φ y)) - 1| ≤ d
        refine (abs_exp_sub_one_le _).trans ?_
        rw [hd, abs_neg]; linarith [Real.exp_le_exp.mpr this]) v
    have hfu := norm_nonneg (footRes ell k Lu p u)
    have hfv := norm_nonneg (footRes ell k Lu p v)
    have t1 : K * ‖footMul ell k Lu p (a - fun _ => 1) u‖ * ‖Y1‖
        ≤ K * (d * ‖footRes ell k Lu p u‖) * (Real.exp (5 * θ) * ‖footRes ell k Lu p v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left n1 hK) n2 (norm_nonneg _) (by positivity)
    have t2 : K * ‖X0‖ * ‖footMul ell k Lu p (ai - fun _ => 1) v‖
        ≤ K * (1 * ‖footRes ell k Lu p u‖) * (d * ‖footRes ell k Lu p v‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left n3 hK) n4 (norm_nonneg _) (by positivity)
    have := add_le_add (b1.trans t1) (b2.trans t2)
    refine this.trans (le_of_eq ?_)
    ring
  -- the operator bound
  refine opNorm_le_of_bil _ _ (by positivity) (fun u v => ?_)
  have hcj : ⟪u, (cjp (bondWP φ) (bondWP φ) M - M) v⟫
      = 2 * ⟪polar (GF ell k Lu) U (bondWt φ u) (bondWt (-φ) v) - polar (GF ell k Lu) U u v, ψ⟫ := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, inner_sub_left]
    have : ⟪u, cjp (bondWP φ) (bondWP φ) M v⟫ = ⟪bondWt φ u, M (bondWt (-φ) v)⟫ := by
      show ⟪u, bondWt φ (M (bondWt (-φ) v))⟫ = _
      exact ((bondWP φ).w_sym u _).symm
    rw [this, Mpsi_inner, Mpsi_inner]; ring
  rw [hcj, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hp := pair_le ell k Lu ψ S hψ (polar (GF ell k Lu) U (bondWt φ u) (bondWt (-φ) v) - polar (GF ell k Lu) U u v)
  have hsum : ∑ p, ‖(polar (GF ell k Lu) U (bondWt φ u) (bondWt (-φ) v) - polar (GF ell k Lu) U u v) p‖
      ≤ K * (d * (Real.exp (5 * θ) + 1)) * ∑ p : BIdx (GF ell k Lu), ‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖ := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun p _ => hrow p u v
  have hcs : ∑ p : BIdx (GF ell k Lu), ‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖ ≤ 648 * ‖u‖ * ‖v‖ := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : BIdx (GF ell k Lu) => ‖footRes ell k Lu p u‖)
      (fun p => ‖footRes ell k Lu p v‖)
    have hu := foot_mult_full ell k Lu hell2 u
    have hv := foot_mult_full ell k Lu hell2 v
    have hsn : 0 ≤ ∑ p : BIdx (GF ell k Lu), ‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖ :=
      Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h2 : (∑ p : BIdx (GF ell k Lu), ‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖) ^ 2
        ≤ (648 * ‖u‖ * ‖v‖) ^ 2 := by
      refine h1.trans ?_
      have := mul_le_mul hu hv (Finset.sum_nonneg fun p _ => sq_nonneg _) (by positivity)
      nlinarith
    exact (pow_le_pow_iff_left₀ hsn (by positivity) two_ne_zero).mp h2
  have hK' : 0 ≤ K * (d * (Real.exp (5 * θ) + 1)) := by positivity
  have := mul_le_mul_of_nonneg_left hcs hK'
  have := mul_le_mul_of_nonneg_left (hsum.trans this) hS
  nlinarith

end

#print axioms Mpsi_inner
#print axioms Mpsi_norm
#print axioms Mpsi_cjp

end AdalyFormal.DLayer

import DLR30

/-!
# DL31 -- **the Combes–Thomas commutator of the genuine bond `Q`** (full tower)

`‖Q⁺ − Q‖, ‖Q⁻ − Q‖ ≤ qbM · (e^{Rfoot·θ'} − 1) · √(3 (Rfoot/n + 1)³)`, `Q⁺ = e^{φ} Q e^{−φ}` (`fspWP`, `bondWP`).
Proof: `(Q⁺x − Qx)(p) = Q(e^{φ(c₀)−φ}x − x)(p)` (`c = p₂₁`), = `Q(1_{Foot c}(e^{φ(c₀)−φ}x − x))(p)` by row locality (DL30),
`|φ(c₀) − φ(b₀)| ≤ Rfoot·θ'` on the footprint (DL29 `Foot_reach`, `Reach_lip`), `‖Q r (p)‖ ≤ ‖Q‖ ‖r‖`, and the overlap count
(DL30 `foot_mult`).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (TowerClass)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

theorem Qfull_conj_pt (U : Cfg (scaleUp ell k Lu)) (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ)
    (x : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (GF ell k Lu)) :
    (fspWt ell k Lu φ ((bondSectorOf (GF ell k Lu) U).Qfull (bondWt (-φ) x)) - (bondSectorOf (GF ell k Lu) U).Qfull x) p
      = (bondSectorOf (GF ell k Lu) U).Qfull (bondWt (fun z => φ p.2.1.1 - φ z) x - x) p := by
  have hf : Real.exp (φ p.2.1.1) • bondWt (-φ) x = bondWt (fun z => φ p.2.1.1 - φ z) x := by
    refine PiLp.ext (fun b => ?_)
    rw [PiLp.smul_apply, bondWt_apply, bondWt_apply, smul_smul, ← Real.exp_add]
    congr 2
  rw [PiLp.sub_apply, fspWt_apply, map_sub, PiLp.sub_apply, ← PiLp.smul_apply, ← map_smul, hf]

open Classical in
theorem Qfull_local_pt (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (y : BondFnL2 (scaleUp ell k Lu)) (p : BIdx (GF ell k Lu)) :
    (bondSectorOf (GF ell k Lu) U).Qfull y p
      = (bondSectorOf (GF ell k Lu) U).Qfull (bondRestr (Foot ell k p.2.1) y) p := by
  have h0 := Qfull_row_local ell k Lu U hreg (y - bondRestr (Foot ell k p.2.1) y) p (fun b hb => by
    show y b - (if Foot ell k p.2.1 b then y b else 0) = 0
    rw [if_pos hb, sub_self])
  rw [map_sub, PiLp.sub_apply, sub_eq_zero] at h0
  exact h0

open Classical in
theorem restr_resc_sq (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (hell : 0 < ell)
    (x : BondFnL2 (scaleUp ell k Lu)) (c : PeriodicLatticeEdge (scaleUp ell k Lu)) :
    ‖bondRestr (Foot ell k c) (bondWt (fun z => φ c.1 - φ z) x - x)‖ ^ 2
      ≤ (Real.exp (Rfoot ell k * θ') - 1) ^ 2
        * ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k c b then ‖x b‖ ^ 2 else 0) := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun b _ => ?_)
  show ‖(if Foot ell k c b then (bondWt (fun z => φ c.1 - φ z) x - x) b else 0)‖ ^ 2 ≤ _
  split_ifs with hb
  · rw [PiLp.sub_apply, bondWt_apply]
    have e : Real.exp (φ c.1 - φ b.1) • x b - x b = (Real.exp (φ c.1 - φ b.1) - 1) • x b := by
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hr := Reach_lip θ' φ hφ (Foot_reach ell hell k c b hb)
    have h1 : |φ c.1 - φ b.1| ≤ Rfoot ell k * θ' := by rw [abs_sub_comm]; exact hr
    have h2 := abs_exp_sub_one_le_of _ _ h1
    have h3 : (Real.exp (φ c.1 - φ b.1) - 1) ^ 2 ≤ (Real.exp (Rfoot ell k * θ') - 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  · simp

/-- **the weighted commutator of the genuine bond `Q`** -/
theorem Qfull_conj_le (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) (x : BondFnL2 (scaleUp ell k Lu)) :
    ‖fspWt ell k Lu φ ((bondSectorOf (GF ell k Lu) U).Qfull (bondWt (-φ) x)) - (bondSectorOf (GF ell k Lu) U).Qfull x‖
      ≤ qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * Real.sqrt ((3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ))
        * ‖x‖ := by
  classical
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (Rfoot ell k * θ') - 1 := by
    have : 0 ≤ (Rfoot ell k : ℝ) * θ' := by positivity
    linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * θ')]
  have hq0 := qbM_nonneg ell k ε
  set M : ℝ := ((3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ) : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ p : BIdx (GF ell k Lu),
      ‖(fspWt ell k Lu φ ((bondSectorOf (GF ell k Lu) U).Qfull (bondWt (-φ) x))
          - (bondSectorOf (GF ell k Lu) U).Qfull x) p‖ ^ 2
        ≤ (qbM ell k ε) ^ 2 * (Real.exp (Rfoot ell k * θ') - 1) ^ 2
          * ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0) := by
    intro p
    rw [Qfull_conj_pt, Qfull_local_pt ell k Lu U hreg]
    set r := bondRestr (Foot ell k p.2.1) (bondWt (fun z => φ p.2.1.1 - φ z) x - x) with hr
    have h1 : ‖(bondSectorOf (GF ell k Lu) U).Qfull r p‖ ≤ qbM ell k ε * ‖r‖ :=
      (PiLp.norm_apply_le _ p).trans (Qfull_norm_le ell k Lu hell U ε hreg hcl hε0 hsm r)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := restr_resc_sq ell k Lu φ θ' hφ hell x p.2.1
    rw [← hr] at h3
    calc _ ≤ (qbM ell k ε * ‖r‖) ^ 2 := h2
      _ = (qbM ell k ε) ^ 2 * ‖r‖ ^ 2 := by ring
      _ ≤ (qbM ell k ε) ^ 2 * ((Real.exp (Rfoot ell k * θ') - 1) ^ 2
          * ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = _ := by ring
  have hsq : ‖fspWt ell k Lu φ ((bondSectorOf (GF ell k Lu) U).Qfull (bondWt (-φ) x))
        - (bondSectorOf (GF ell k Lu) U).Qfull x‖ ^ 2
      ≤ (qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * Real.sqrt M * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc _ ≤ ∑ p : BIdx (GF ell k Lu), (qbM ell k ε) ^ 2 * (Real.exp (Rfoot ell k * θ') - 1) ^ 2
          * ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0) :=
          Finset.sum_le_sum (fun p _ => hpt p)
      _ = (qbM ell k ε) ^ 2 * (Real.exp (Rfoot ell k * θ') - 1) ^ 2
          * ∑ p : BIdx (GF ell k Lu), ∑ b : Bond (scaleUp ell k Lu), (if Foot ell k p.2.1 b then ‖x b‖ ^ 2 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (qbM ell k ε) ^ 2 * (Real.exp (Rfoot ell k * θ') - 1) ^ 2 * (M * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (foot_mult ell k Lu hell x) (by positivity)
      _ = (qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * Real.sqrt M * ‖x‖) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM0]; ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem Qfull_cjp_norm (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjp (bondWP φ) (fspWP ell k Lu φ) (bondSectorOf (GF ell k Lu) U).Qfull - (bondSectorOf (GF ell k Lu) U).Qfull‖
      ≤ qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * Real.sqrt ((3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ)) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (Rfoot ell k * θ') - 1 := by
    have : 0 ≤ (Rfoot ell k : ℝ) * θ' := by positivity
    linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * θ')]
  have hq0 := qbM_nonneg ell k ε
  refine opnorm_le_of _ _ (by positivity) (fun x => ?_)
  rw [ContinuousLinearMap.sub_apply, cjp_apply]
  exact Qfull_conj_le ell k Lu hell U ε hreg hcl hε0 hsm φ θ' hφ x

theorem Qfull_cjm_norm (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℝ)
    (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ) :
    ‖cjm (bondWP φ) (fspWP ell k Lu φ) (bondSectorOf (GF ell k Lu) U).Qfull - (bondSectorOf (GF ell k Lu) U).Qfull‖
      ≤ qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * Real.sqrt ((3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ)) := by
  have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ : 0 ≤ Real.exp (Rfoot ell k * θ') - 1 := by
    have : 0 ≤ (Rfoot ell k : ℝ) * θ' := by positivity
    linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * θ')]
  have hq0 := qbM_nonneg ell k ε
  refine opnorm_le_of _ _ (by positivity) (fun x => ?_)
  rw [ContinuousLinearMap.sub_apply]
  have e : cjm (bondWP φ) (fspWP ell k Lu φ) (bondSectorOf (GF ell k Lu) U).Qfull x
      = fspWt ell k Lu (-φ) ((bondSectorOf (GF ell k Lu) U).Qfull (bondWt (-(-φ)) x)) := by
    rw [neg_neg]; rfl
  rw [e]
  exact Qfull_conj_le ell k Lu hell U ε hreg hcl hε0 hsm (-φ) θ' (WtLip_neg θ' φ hφ) x

end

#print axioms Qfull_conj_pt
#print axioms Qfull_local_pt
#print axioms restr_resc_sq
#print axioms Qfull_conj_le
#print axioms Qfull_cjp_norm
#print axioms Qfull_cjm_norm

end AdalyFormal.DLayer

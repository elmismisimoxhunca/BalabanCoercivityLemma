import DS1
import DLR78

/-!
# DY1 -- weighted polarization of the composite second jet, and coarse points in a periodic ball
(M1 D-layer lane, clause 2, 2026-10-14)

* `wq S ℓ k` : the bond weight `z ↦ (ℓ^{-bstrat b} z_b)_b`; **`wq_normSq`** : `‖wq z‖² = wnormSq S ℓ k z`;
* **`polar_l1_T`** : for ANY linear `T`, `Σ_p ‖C2 z p‖ ≤ K ‖T z‖²` for all `z` ⟹ `Σ_p ‖β(u,v)(p)‖ ≤ K ‖T u‖ ‖T v‖`
  (`β = polar`, DLR78; the M0 proof with the norm replaced by `‖T ·‖`);
* `disp_le` : `pcd N a b ≤ r` ⟹ `((b + r) − a).val ≤ 2r` in `Fin N`;
* `card_disp_coarse_le` : coarse points `y` with `(z_ν − y_ν).val ≤ m` (all `ν`) number `≤ (m/n + 1)³` (DL29's count with the
  displacement as the hypothesis);
* **`card_ball_coarse_le`** : coarse points in the periodic ball `pdist y x ≤ r` number `≤ (2r/n + 1)³`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (C2fullOf TowerGeom Cfg FSp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (Tower pdist pcd)
open AdalyFormal.DLayer (polar polar_scale polar_zero_left polar_eq sub_val_mod)
open AdalyFormal.M1 (bstrat wnormSq)

/-! ## 1. the weight operator of `wnormSq` -/

section wq
variable {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ)

/-- `(wq z)_b = ℓ^{-bstrat b} z_b` -/
noncomputable def wq : BondFnL2 L →L[ℝ] BondFnL2 L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun b => (((ell : ℝ) ^ bstrat S k b)⁻¹) • z b)
      map_add' := fun z w => by
        refine PiLp.ext (fun b => ?_)
        simp only [PiLp.add_apply, smul_add]
      map_smul' := fun c z => by
        refine PiLp.ext (fun b => ?_)
        simp only [PiLp.smul_apply, RingHom.id_apply]
        rw [smul_comm] }

theorem wq_apply (z : BondFnL2 L) (b : Bond L) : wq S ell k z b = (((ell : ℝ) ^ bstrat S k b)⁻¹) • z b := rfl

theorem wq_normSq (z : BondFnL2 L) : ‖wq S ell k z‖ ^ 2 = wnormSq S ell k z := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [wq_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

end wq

/-! ## 2. polarization with a linear weight -/

section polarT
variable {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)

theorem polar_l1_T (T : BondFnL2 L →L[ℝ] BondFnL2 L) (K : ℝ) (hK : 0 ≤ K)
    (hC : ∀ z : BondFnL2 L, ∑ p, ‖C2fullOf G U z p‖ ≤ K * ‖T z‖ ^ 2)
    (u v : BondFnL2 L) : ∑ p, ‖polar G U u v p‖ ≤ K * ‖T u‖ * ‖T v‖ := by
  have gen : ∀ x y : BondFnL2 L, ∑ p, ‖polar G U x y p‖ ≤ K / 2 * (‖T x‖ ^ 2 + ‖T y‖ ^ 2) := by
    intro x y
    have hpt : ∀ p, ‖polar G U x y p‖ ≤ (1 / 4 : ℝ) * (‖C2fullOf G U (x + y) p‖ + ‖C2fullOf G U (x - y) p‖) := by
      intro p
      show ‖((1 / 4 : ℝ) • (C2fullOf G U (x + y) - C2fullOf G U (x - y))) p‖ ≤ _
      rw [PiLp.smul_apply, PiLp.sub_apply, norm_smul, Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    refine (Finset.sum_le_sum fun p _ => hpt p).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have h1 := hC (x + y)
    have h2 := hC (x - y)
    have hpar : ‖T (x + y)‖ ^ 2 + ‖T (x - y)‖ ^ 2 = 2 * (‖T x‖ ^ 2 + ‖T y‖ ^ 2) := by
      rw [map_add, map_sub]
      have := parallelogram_law_with_norm ℝ (T x) (T y)
      nlinarith [this]
    nlinarith
  have hnn : 0 ≤ ∑ p, ‖polar G U u v p‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  -- degenerate cases by scaling
  have hdeg : ∀ x y : BondFnL2 L, ‖T x‖ = 0 → ∑ p, ‖polar G U x y p‖ = 0 := by
    intro x y hx
    have hX : 0 ≤ ∑ p, ‖polar G U x y p‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    by_contra hne
    have hpos : 0 < ∑ p, ‖polar G U x y p‖ := lt_of_le_of_ne hX (Ne.symm hne)
    set X := ∑ p, ‖polar G U x y p‖ with hXd
    set c : ℝ := K / 2 * ‖T y‖ ^ 2 + 1 with hc
    have hc0 : 0 < c := by positivity
    set s : ℝ := Real.sqrt (c / X) + 1 with hs
    have hs1 : 1 ≤ s := by have := Real.sqrt_nonneg (c / X); linarith
    have hs0 : 0 < s := by linarith
    have h := gen (s • x) (s⁻¹ • y)
    rw [polar_scale G U x y s hs0.ne', map_smul, map_smul, norm_smul, norm_smul, hx, mul_zero,
      Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)] at h
    -- X ≤ K/2 ‖Ty‖² / s² < X
    have hs2 : c / X < s ^ 2 := by
      have h1 : Real.sqrt (c / X) < s := by linarith
      have h2 := Real.sq_sqrt (show 0 ≤ c / X by positivity)
      nlinarith [Real.sqrt_nonneg (c / X)]
    have h3 : c < X * s ^ 2 := by rwa [div_lt_iff₀ hpos, mul_comm] at hs2
    have h4 : X * s ^ 2 ≤ K / 2 * ‖T y‖ ^ 2 := by
      have e : (0 : ℝ) ^ 2 + (s⁻¹ * ‖T y‖) ^ 2 = ‖T y‖ ^ 2 / s ^ 2 := by
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, mul_pow, inv_pow, div_eq_inv_mul]
      rw [e] at h
      have := mul_le_mul_of_nonneg_right h (sq_nonneg s)
      have e2 : K / 2 * (‖T y‖ ^ 2 / s ^ 2) * s ^ 2 = K / 2 * ‖T y‖ ^ 2 := by field_simp
      linarith
    linarith
  by_cases hu : ‖T u‖ = 0
  · rw [hdeg u v hu, hu]; simp
  by_cases hv : ‖T v‖ = 0
  · have hsym : ∀ p, polar G U u v p = polar G U v u p := by
      intro p; rw [polar_eq, polar_eq, add_comm]
    rw [Finset.sum_congr rfl (fun p _ => by rw [hsym p]), hdeg v u hv, hv]; simp
  have hu' : 0 < ‖T u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hv' : 0 < ‖T v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  set s := Real.sqrt (‖T v‖ / ‖T u‖) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hv' hu')
  have hs2 : s ^ 2 = ‖T v‖ / ‖T u‖ := Real.sq_sqrt (div_pos hv' hu').le
  have h := gen (s • u) (s⁻¹ • v)
  rw [polar_scale G U u v s hs.ne'] at h
  refine h.trans (le_of_eq ?_)
  rw [map_smul, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (inv_nonneg.mpr hs.le),
    mul_pow, mul_pow, inv_pow, hs2]
  field_simp
  ring

end polarT

/-! ## 3. coarse points in a periodic ball -/

theorem disp_le (N : ℕ) [NeZero N] (a b : Fin N) (r : ℕ) (h : pcd N a.val b.val ≤ r) :
    ((b + (⟨r % N, Nat.mod_lt r (Nat.pos_of_ne_zero (NeZero.ne N))⟩ : Fin N)) - a).val ≤ 2 * r := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have ha := a.isLt
  have hb := b.isLt
  rw [Fin.val_sub, Fin.val_add]
  simp only [Fin.val_mk]
  unfold pcd at h
  set s := r % N with hs
  have hsr : s ≤ r := Nat.mod_le r N
  have hsN : s < N := Nat.mod_lt r hN
  -- u = (b + s) % N
  have hu : (b.val + s) % N = if b.val + s < N then b.val + s else b.val + s - N := by
    split_ifs with h1
    · exact Nat.mod_eq_of_lt h1
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hu]
  -- the final reduction
  have hred : ∀ w : ℕ, w < 2 * N → w % N = if w < N then w else w - N := by
    intro w hw
    split_ifs with h1
    · exact Nat.mod_eq_of_lt h1
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  by_cases hrN : N ≤ r
  · -- the value is `< N ≤ r`
    have : (N - a.val + if b.val + s < N then b.val + s else b.val + s - N) % N < N := Nat.mod_lt _ hN
    exact le_of_lt (lt_of_lt_of_le this (by omega))
  · have hs' : s = r := Nat.mod_eq_of_lt (by omega)
    split_ifs at h ⊢ <;> rw [hred _ (by omega)] <;> split_ifs <;> omega

open Classical in
theorem card_disp_coarse_le {L : PeriodicLatticeExtent} (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1) (m : ℕ)
    (z : PeriodicLatticeSite L) :
    (Finset.univ.filter (fun y : PeriodicLatticeSite L => (∀ ν, n ∣ (y ν).val) ∧ ∀ ν, (z ν - y ν).val ≤ m)).card
      ≤ (m / n + 1) ^ 3 := by
  have hcard : (Finset.univ : Finset (Fin 3 → Fin (m / n + 1))).card = (m / n + 1) ^ 3 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun y : PeriodicLatticeSite L => fun ν : Fin 3 =>
      (⟨min ((z ν - y ν).val / n) (m / n), Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (m / n + 1))) ?_ ?_
  · intro y _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
  · intro y hy y' hy' hyy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    funext ν
    have h1 := congrFun hyy ν
    simp only [Fin.mk.injEq] at h1
    have hm1 : (z ν - y ν).val / n ≤ m / n := Nat.div_le_div_right (hy.2 ν)
    have hm2 : (z ν - y' ν).val / n ≤ m / n := Nat.div_le_div_right (hy'.2 ν)
    rw [min_eq_left hm1, min_eq_left hm2] at h1
    have h2 : (z ν - y ν).val % n = (z ν - y' ν).val % n := by
      rw [sub_val_mod n (hdvd ν) _ _ (hy.1 ν), sub_val_mod n (hdvd ν) _ _ (hy'.1 ν)]
    have h3 : (z ν - y ν).val = (z ν - y' ν).val := by
      rw [← Nat.div_add_mod (z ν - y ν).val n, ← Nat.div_add_mod (z ν - y' ν).val n, h1, h2]
    have h4 : z ν - y ν = z ν - y' ν := Fin.ext h3
    exact sub_right_injective h4

open Classical in
/-- **coarse points in a periodic ball** -/
theorem card_ball_coarse_le {L : PeriodicLatticeExtent} (n : ℕ) (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1) (r : ℕ)
    (x : PeriodicLatticeSite L) :
    (Finset.univ.filter (fun y : PeriodicLatticeSite L => (∀ ν, n ∣ (y ν).val) ∧ pdist y x ≤ r)).card
      ≤ (2 * r / n + 1) ^ 3 := by
  let z : PeriodicLatticeSite L := fun ν => x ν + (⟨r % (L ν + 1), Nat.mod_lt r (Nat.succ_pos _)⟩ : Fin (L ν + 1))
  refine le_trans (Finset.card_le_card ?_) (card_disp_coarse_le n hn hdvd (2 * r) z)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  refine ⟨hy.1, fun ν => ?_⟩
  have hc : pcd (L ν + 1) (y ν).val (x ν).val ≤ r := by
    have h1 : pcd (L ν + 1) (y ν).val (x ν).val ≤ pdist y x := by
      unfold pdist
      exact Finset.single_le_sum (f := fun μ => pcd (L μ + 1) (y μ).val (x μ).val) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ ν)
    exact h1.trans hy.2
  exact disp_le (L ν + 1) (y ν) (x ν) r hc

#print axioms wq
#print axioms wq_apply
#print axioms wq_normSq
#print axioms polar_l1_T
#print axioms disp_le
#print axioms card_disp_coarse_le
#print axioms card_ball_coarse_le

end AdalyFormal.M1DStrat

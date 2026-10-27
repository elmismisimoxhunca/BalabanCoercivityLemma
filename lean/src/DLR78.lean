import DLR77
import DLR74

/-!
# DL78 -- the POLARIZED composite second jet: `ℓ¹` bound and the LOCALIZED row bound (full tower)

`β(u,v) = ¼ (C2fullOf(u+v) − C2fullOf(u−v))` (symmetric bilinear, `β(u,u) = C2fullOf u`).
* `polar_eq` : `β(u,v) = ½(B u v + B v u)` for the bilinear `B` of `C2fullOf_quad`;  `polar_scale` : `β(su, s⁻¹v) = β(u,v)`;
* **`polar_l1`** : `Σ_p ‖C2 z p‖ ≤ K‖z‖²` for all `z` ⇒ `Σ_p ‖β(u,v)(p)‖ ≤ K‖u‖‖v‖`;
* `C2full_row_congr` : the row `p` of `C2fullOf` reads only `Foot ℓ p.1 p.2.1` (DL77);
* **`polar_row`** : `‖β(u,v)(p)‖ ≤ K‖u|_{F(p)}‖‖v|_{F(p)}‖`;
* **`foot_mult`** : `Σ_p ‖u|_{F(p)}‖² ≤ 648‖u‖²` at the full tower (`Rfoot ≤ 5ℓ^k`, 3·6³).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (C2CompX RegTower XS bgTower Cfg C2fullOf C2fullOf_quad suCoord TowerGeom BIdx FSp)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (suOf)
open AdalyFormal.BondComposite (bidx_level bidxCB bidxCB_injective sum_le_of_injective bidx_aligned)

section polar
variable {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L)

/-- the symmetric polarization of the composite second jet -/
noncomputable def polar (u v : BondFnL2 L) : FSp G :=
  (1 / 4 : ℝ) • (C2fullOf G U (u + v) - C2fullOf G U (u - v))

theorem polar_eq (u v : BondFnL2 L) :
    polar G U u v = (1 / 2 : ℝ) • ((C2fullOf_quad G U).choose u v + (C2fullOf_quad G U).choose v u) := by
  have hβ := (C2fullOf_quad G U).choose_spec
  unfold polar
  rw [hβ, hβ]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [smul_add]
  have : (1 / 4 : ℝ) • ((C2fullOf_quad G U).choose u u + (C2fullOf_quad G U).choose v u
      + ((C2fullOf_quad G U).choose u v + (C2fullOf_quad G U).choose v v)
      - ((C2fullOf_quad G U).choose u u - (C2fullOf_quad G U).choose v u
        - ((C2fullOf_quad G U).choose u v - (C2fullOf_quad G U).choose v v)))
      = (1 / 2 : ℝ) • (C2fullOf_quad G U).choose u v + (1 / 2 : ℝ) • (C2fullOf_quad G U).choose v u := by
    rw [← sub_eq_zero]
    simp only [smul_sub, smul_add]
    module
  rw [this]

theorem polar_scale (u v : BondFnL2 L) (s : ℝ) (hs : s ≠ 0) : polar G U (s • u) (s⁻¹ • v) = polar G U u v := by
  rw [polar_eq, polar_eq]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hs, inv_mul_cancel₀ hs, one_smul]

theorem polar_zero_left (v : BondFnL2 L) : polar G U 0 v = 0 := by
  rw [polar_eq]; simp

theorem polar_l1 (K : ℝ) (hK : 0 ≤ K) (hC : ∀ z : BondFnL2 L, ∑ p, ‖C2fullOf G U z p‖ ≤ K * ‖z‖ ^ 2)
    (u v : BondFnL2 L) : ∑ p, ‖polar G U u v p‖ ≤ K * ‖u‖ * ‖v‖ := by
  -- generic bound for any pair
  have gen : ∀ x y : BondFnL2 L, ∑ p, ‖polar G U x y p‖ ≤ K / 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
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
    have hpar : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      have := parallelogram_law_with_norm ℝ x y
      nlinarith [this]
    nlinarith
  by_cases hu : ‖u‖ = 0
  · have hu0 : u = 0 := norm_eq_zero.mp hu
    rw [hu0, polar_zero_left]
    simp
  by_cases hv : ‖v‖ = 0
  · have hv0 : v = 0 := norm_eq_zero.mp hv
    have h0 : polar G U u 0 = 0 := by rw [polar_eq]; simp
    rw [hv0, h0]
    simp
  have hu' : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hv' : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  set s := Real.sqrt (‖v‖ / ‖u‖) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hv' hu')
  have hs2 : s ^ 2 = ‖v‖ / ‖u‖ := Real.sq_sqrt (div_pos hv' hu').le
  have h := gen (s • u) (s⁻¹ • v)
  rw [polar_scale G U u v s hs.ne'] at h
  refine h.trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), mul_pow, mul_pow,
    inv_pow, hs2]
  field_simp
  ring

end polar

section foot
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

open Classical in
/-- restriction of a bond field to the footprint of `p` -/
noncomputable def footRes (p : BIdx (GF ell k Lu)) (u : BondFnL2 (scaleUp ell k Lu)) : BondFnL2 (scaleUp ell k Lu) :=
  WithLp.toLp 2 (fun e => if Foot ell (p.1 : ℕ) p.2.1 e then u e else 0)

theorem C2full_row_congr (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (p : BIdx (GF ell k Lu)) (z z' : BondFnL2 (scaleUp ell k Lu))
    (h : ∀ e, Foot ell (p.1 : ℕ) p.2.1 e → z e = z' e) :
    C2fullOf (GF ell k Lu) U z p = C2fullOf (GF ell k Lu) U z' p := by
  rw [C2full_apply_level _ _ hreg, C2full_apply_level _ _ hreg]
  congr 2
  exact C2CompX_row_congr ell (bgTower (GF ell k Lu) U) k hreg (p.1 : ℕ) (Nat.lt_succ_iff.mp p.1.isLt) p.2.1
    (suCoord z) (suCoord z') (fun e he => by
      show AdalyFormal.IngredientFamilyR2.fromM2 ((z e : SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2)
        = AdalyFormal.IngredientFamilyR2.fromM2 ((z' e : SuTwo) : AdalyFormal.Balaban.SuTwoLogExp.M2)
      rw [h e he])

theorem polar_row_congr (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (p : BIdx (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    polar (GF ell k Lu) U u v p = polar (GF ell k Lu) U (footRes ell k Lu p u) (footRes ell k Lu p v) p := by
  classical
  unfold polar
  rw [PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply, PiLp.sub_apply]
  have h1 := C2full_row_congr ell k Lu hell U hreg p (u + v) (footRes ell k Lu p u + footRes ell k Lu p v)
    (fun e he => by simp [footRes, he])
  have h2 := C2full_row_congr ell k Lu hell U hreg p (u - v) (footRes ell k Lu p u - footRes ell k Lu p v)
    (fun e he => by simp [footRes, he])
  rw [h1, h2]

theorem polar_row (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k)
    (K : ℝ) (hK : 0 ≤ K) (hC : ∀ z : BondFnL2 (scaleUp ell k Lu), ∑ p, ‖C2fullOf (GF ell k Lu) U z p‖ ≤ K * ‖z‖ ^ 2)
    (p : BIdx (GF ell k Lu)) (u v : BondFnL2 (scaleUp ell k Lu)) :
    ‖polar (GF ell k Lu) U u v p‖ ≤ K * ‖footRes ell k Lu p u‖ * ‖footRes ell k Lu p v‖ := by
  rw [polar_row_congr ell k Lu hell U hreg p u v]
  refine le_trans ?_ (polar_l1 (GF ell k Lu) U K hK hC _ _)
  exact Finset.single_le_sum (f := fun p' => ‖polar (GF ell k Lu) U (footRes ell k Lu p u) (footRes ell k Lu p v) p'‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ p)

open Classical in
theorem footRes_sq (p : BIdx (GF ell k Lu)) (u : BondFnL2 (scaleUp ell k Lu)) :
    ‖footRes ell k Lu p u‖ ^ 2 = ∑ e, if Foot ell (p.1 : ℕ) p.2.1 e then ‖u e‖ ^ 2 else 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun e _ => ?_
  show ‖(if Foot ell (p.1 : ℕ) p.2.1 e then u e else 0)‖ ^ 2 = _
  split_ifs <;> simp

open Classical in
/-- the footprint multiplicity at the full tower -/
theorem card_foot_le (hell2 : 2 ≤ ell) (e : PeriodicLatticeEdge (scaleUp ell k Lu)) :
    (Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell (p.1 : ℕ) p.2.1 e)).card ≤ 648 := by
  have hell : 0 < ell := by omega
  set R := Rfoot ell k with hR
  set Y := Finset.univ.filter (fun y : PeriodicLatticeSite (scaleUp ell k Lu) =>
    (∀ ν, ell ^ k ∣ (y ν).val) ∧ Reach R y e.1) with hY
  have hn : ∀ ν, ell ^ k ∣ scaleUp ell k Lu ν + 1 :=
    fun ν => AdalyFormal.BondComposite.hdvd_scaleUp ell k Lu hell k le_rfl ν
  have hYc : Y.card ≤ 216 := by
    have h1 := card_reach_coarse_le (ell ^ k) (pow_pos hell k) hn R e.1
    have h2 : R ≤ 5 * ell ^ k := Rfoot_le ell hell2 k
    have h3 : R / ell ^ k ≤ 5 := by
      rw [Nat.div_le_iff_le_mul_add_pred (pow_pos hell k)]; nlinarith [pow_pos hell k]
    have h4 : (R / ell ^ k + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc Y.card ≤ (R / ell ^ k + 1) ^ 3 := h1
      _ ≤ 6 ^ 3 := h4
      _ = 216 := by norm_num
  have hinj : Set.InjOn (fun p : BIdx (GF ell k Lu) => (p.2.1.1, p.2.1.2))
      ↑(Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell (p.1 : ℕ) p.2.1 e)) := by
    intro p _ p' _ h
    have h' : bidxCB ell k Lu hell p = bidxCB ell k Lu hell p' := by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    exact bidxCB_injective ell k Lu hell h'
  have hmaps : ∀ p ∈ Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell (p.1 : ℕ) p.2.1 e),
      (fun p : BIdx (GF ell k Lu) => (p.2.1.1, p.2.1.2)) p ∈ Y ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, hY, Finset.mem_filter, true_and]
    refine ⟨fun ν => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp (bidx_aligned ell k Lu hell p) ν), ?_⟩
    have hk : (p.1 : ℕ) = k := bidx_level ell k Lu p
    have hf := Foot_reach ell hell (p.1 : ℕ) p.2.1 e hp
    have key : ∀ n : ℕ, n = k → Reach (Rfoot ell n) (p.2.1).1 e.1 → Reach R (p.2.1).1 e.1 := by
      intro n hn h; rw [hn] at h; exact h
    exact key _ hk hf
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
  omega

open Classical in
theorem foot_mult_full (hell2 : 2 ≤ ell) (u : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p : BIdx (GF ell k Lu), ‖footRes ell k Lu p u‖ ^ 2 ≤ 648 * ‖u‖ ^ 2 := by
  simp_rw [footRes_sq]
  rw [Finset.sum_comm, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.univ.filter (fun p : BIdx (GF ell k Lu) => Foot ell (p.1 : ℕ) p.2.1 e)).card : ℝ) ≤ 648 := by
    exact_mod_cast card_foot_le ell k Lu hell2 e
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end foot

#print axioms polar_eq
#print axioms polar_scale
#print axioms polar_l1
#print axioms C2full_row_congr
#print axioms polar_row
#print axioms card_foot_le
#print axioms foot_mult_full

end AdalyFormal.DLayer

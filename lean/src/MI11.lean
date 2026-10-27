import MI10

/-!
# MI11 -- the adjoint of a constraint row, and the `Q'*` commutator (M1 lane E, 2026-10-13)

`Kq = (Qlev_{j,y})* : SuTwo → SiteL2` for a constraint row `q = (j, y)`.
* `Kq_supp` : `Kq c` vanishes off the box of the row;  `Kq_norm_sq` : `‖Kq c‖² ≤ ℓ^{−3j} ‖c‖²`;
* `QpP_adj_on` : on the block of row `q`, `(Q'* v)(x) = √(a_jℓ^j) (Kq v_q)(x)`;  `QpP_adj_off` : off `Ω₀`, `(Q'* v)(x) = v_x`;
* **`cQs_sum`** (L4) : `Σ_p ‖ℓ^{2 strat}(h_p Q'* v − Q'*(h_p v))‖² ≤ 9 a KG ‖ℓ^{strat} v‖²`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the single-site field `e δ_x` -/
noncomputable def dsite (x : PeriodicLatticeSite L) (e : SuTwo) : SiteL2 L :=
  WithLp.toLp 2 (fun z => if z = x then e else 0)

theorem inner_dsite (F : SiteL2 L) (x : PeriodicLatticeSite L) (e : SuTwo) : ⟪F, dsite x e⟫ = ⟪F x, e⟫ := by
  classical
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single x]
  · show ⟪F x, (if x = x then e else 0)⟫ = _
    rw [if_pos rfl]
  · intro z _ hz
    show ⟪F z, (if z = x then e else 0)⟫ = 0
    rw [if_neg hz, inner_zero_right]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem eq_of_inner_all {u v : SuTwo} (h : ∀ e : SuTwo, ⟪u, e⟫ = ⟪v, e⟫) : u = v :=
  ext_inner_right ℝ h

section rows
variable {G : TowerGeom L} {ell k : ℕ} (hP : ProperTower G ell k)

/-- the adjoint of a row functional vanishes off the row's box. -/
theorem Kq_supp (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L) (c : SuTwo) {x : PeriodicLatticeSite L}
    (hx : x ∉ boxF y (G.ell ^ j)) : (ContinuousLinearMap.adjoint (Qlev G U j y) c) x = 0 := by
  classical
  refine eq_of_inner_all (fun e => ?_)
  rw [← inner_dsite, ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
  have h0 : Qlev G U j y (dsite x e) = Qlev G U j y 0 := by
    refine Qlev_congr_box G U j y _ _ (fun z hz => ?_)
    show (if z = x then e else 0) = (0 : SiteL2 L) z
    rw [if_neg (fun (h : z = x) => hx (by rw [← h]; exact hz))]; rfl
  rw [h0, map_zero, inner_zero_right]

theorem Qlev_norm_sq_le (U : Cfg L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L) (g : SiteL2 L) :
    ‖Qlev G U j y g‖ ^ 2 ≤ ((1 / (G.ell : ℝ) ^ 3) ^ j) * ‖g‖ ^ 2 := by
  rw [Qlev_apply]
  refine (Qcomposite_sq_le (bgTower G U) G.ell hell j (WithLp.ofLp g) y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)

/-- `‖Kq c‖² ≤ ℓ^{−3j} ‖c‖²`. -/
theorem Kq_norm_sq (U : Cfg L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L) (c : SuTwo) :
    ‖ContinuousLinearMap.adjoint (Qlev G U j y) c‖ ^ 2 ≤ ((1 / (G.ell : ℝ) ^ 3) ^ j) * ‖c‖ ^ 2 := by
  set K := ContinuousLinearMap.adjoint (Qlev G U j y) c
  set w : ℝ := (1 / (G.ell : ℝ) ^ 3) ^ j
  have hw : 0 ≤ w := by positivity
  have h1 : ‖K‖ ^ 2 = ⟪c, Qlev G U j y K⟫ := by
    rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_left]
  have h2 : ⟪c, Qlev G U j y K⟫ ≤ ‖c‖ * ‖Qlev G U j y K‖ := real_inner_le_norm _ _
  have h3 : ‖Qlev G U j y K‖ ≤ Real.sqrt w * ‖K‖ := by
    have := Qlev_norm_sq_le U hell j y K
    rw [← Real.sqrt_sq (norm_nonneg (Qlev G U j y K)), ← Real.sqrt_sq (norm_nonneg K), ← Real.sqrt_mul hw]
    exact Real.sqrt_le_sqrt this
  have hK : ‖K‖ ≤ Real.sqrt w * ‖c‖ := by
    by_cases hK0 : ‖K‖ = 0
    · rw [hK0]; positivity
    · have hKp : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hK0)
      have : ‖K‖ ^ 2 ≤ ‖c‖ * (Real.sqrt w * ‖K‖) := by
        rw [h1]; exact h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
      nlinarith [Real.sqrt_nonneg w]
  calc ‖K‖ ^ 2 ≤ (Real.sqrt w * ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hK 2
    _ = w * ‖c‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hw]

include hP

theorem QpP_adj_on (U : Cfg L) (a : ℝ) (v : YP G) (q : QIdx G) {x : PeriodicLatticeSite L}
    (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    (ContinuousLinearMap.adjoint (QpP G U a) v) x
      = Real.sqrt (wq G a (jq q)) • (ContinuousLinearMap.adjoint (Qlev G U (jq q) (yq q)) (v (Sum.inl q))) x := by
  classical
  have hx0 : x ∈ G.Om0 := block_Om0 hP q hx
  refine eq_of_inner_all (fun e => ?_)
  rw [← inner_dsite, ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left, ← inner_dsite,
    ContinuousLinearMap.adjoint_inner_left]
  rw [PiLp.inner_apply, Fintype.sum_sum_type]
  have hoff : ∑ z : OffIdx G, ⟪v (Sum.inr z), QpP G U a (dsite x e) (Sum.inr z)⟫ = 0 := by
    refine Finset.sum_eq_zero (fun z _ => ?_)
    rw [QpP_inr]
    show ⟪v (Sum.inr z), (if z.1 = x then e else 0)⟫ = 0
    rw [if_neg (fun (h : z.1 = x) => z.2 (by rw [h]; exact hx0)), inner_zero_right]
  rw [hoff, add_zero, Finset.sum_eq_single q]
  · rw [QpP_inl, real_inner_smul_right]
    congr 2
    refine congrArg _ ?_
    rw [siteMask_eq_self _ _ (fun z hz => by
      show (if z = x then e else 0) = 0
      rw [if_neg (fun (h : z = x) => hz (by rw [h]; exact hx0))])]
  · intro q' _ hq'
    rw [QpP_inl]
    have hdis := disj_q hP hq'
    have hx' : x ∉ blockOf (yq q') (ell ^ jq q') := fun h => Finset.disjoint_left.mp hdis h hx
    have h0 : Qlev G U q'.1.1.val q'.1.2 (siteMask G.Om0 (dsite x e)) = Qlev G U q'.1.1.val q'.1.2 0 := by
      refine Qlev_congr_box G U _ _ _ _ (fun z hz => ?_)
      rw [hP.ell_eq, boxF_eq_blockOf] at hz
      rw [siteMask_on _ _ _ (block_Om0 hP q' hz)]
      show (if z = x then e else 0) = (0 : SiteL2 L) z
      rw [if_neg (fun (h : z = x) => hx' (by rw [← h]; exact hz))]; rfl
    rw [h0, map_zero, smul_zero, inner_zero_right]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem QpP_adj_off (U : Cfg L) (a : ℝ) (v : YP G) {x : PeriodicLatticeSite L} (hx : x ∉ G.Om0) :
    (ContinuousLinearMap.adjoint (QpP G U a) v) x = v (Sum.inr ⟨x, hx⟩) := by
  classical
  refine eq_of_inner_all (fun e => ?_)
  rw [← inner_dsite, ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, Fintype.sum_sum_type]
  have hrows : ∑ q : QIdx G, ⟪v (Sum.inl q), QpP G U a (dsite x e) (Sum.inl q)⟫ = 0 := by
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [QpP_inl]
    have h0 : siteMask G.Om0 (dsite x e) = 0 := by
      refine PiLp.ext (fun z => ?_)
      by_cases hz : z ∈ G.Om0
      · rw [siteMask_on _ _ _ hz]
        show (if z = x then e else 0) = 0
        rw [if_neg (fun (h : z = x) => hx (by rw [← h]; exact hz))]
      · rw [siteMask_off _ _ _ hz]; rfl
    rw [h0, map_zero, smul_zero, inner_zero_right]
  rw [hrows, zero_add, Finset.sum_eq_single ⟨x, hx⟩]
  · rw [QpP_inr]; show ⟪_, (if x = x then e else 0)⟫ = _; rw [if_pos rfl]
  · intro z _ hz
    rw [QpP_inr]
    show ⟪_, (if z.1 = x then e else 0)⟫ = 0
    rw [if_neg (fun h => hz (Subtype.ext h)), inner_zero_right]
  · intro h; exact absurd (Finset.mem_univ _) h

end rows

section comm
variable {Lf : PeriodicLatticeExtent} {ell M R k κ c : ℕ} {S : Tower Lf}
  (hS : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M) (hell : 2 ≤ ell) (hR1 : 1 ≤ R)
  (hR : (c + 3) * κ * ell ≤ R) (hc : 5 ≤ c)
include hS hκ hM hell hR1 hR hc

/-- pointwise value of the `Q'*` commutator on a block. -/
theorem cQs_on (U : Cfg Lf) (a : ℝ) (h : PeriodicLatticeSite Lf → ℝ) (v : YP (geomOf ell k S))
    (q : QIdx (geomOf ell k S)) {x : PeriodicLatticeSite Lf} (hx : x ∈ blockOf (yq q) (ell ^ jq q)) :
    (siteMul h (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)
        - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) h v)) x
      = (Real.sqrt (wq (geomOf ell k S) a (jq q)) * (h x - h (yq q))) •
          (ContinuousLinearMap.adjoint (Qlev (geomOf ell k S) U (jq q) (yq q)) (v (Sum.inl q)) : SiteL2 Lf) x := by
  have hP := properTower_geomOf (show 0 < ell by omega) hS
  rw [PiLp.sub_apply, siteMul_apply, QpP_adj_on hP U a v q hx, QpP_adj_on hP U a _ q hx, ypMul_apply, map_smul,
    PiLp.smul_apply, smul_smul, smul_smul, ← sub_smul,
    show rowSite (Sum.inl q : PIdx (geomOf ell k S)) = yq q from rfl]
  congr 1; ring

theorem cQs_off (U : Cfg Lf) (a : ℝ) (h : PeriodicLatticeSite Lf → ℝ) (v : YP (geomOf ell k S))
    {x : PeriodicLatticeSite Lf} (hx : x ∉ (geomOf ell k S).Om0) :
    (siteMul h (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)
        - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) h v)) x = 0 := by
  have hP := properTower_geomOf (show 0 < ell by omega) hS
  rw [PiLp.sub_apply, siteMul_apply, QpP_adj_off hP U a v hx, QpP_adj_off hP U a _ hx, ypMul_apply]
  show h x • _ - h x • _ = 0
  rw [sub_self]

/-- **(L4) the `Q'*` commutator**: `Σ_p ‖ℓ^{2 strat}(h_p Q'* v − Q'*(h_p v))‖² ≤ 9 a KG ‖ℓ^{strat} v‖²`. -/
theorem cQs_sum (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (v : YP (geomOf ell k S)) :
    ∑ p, ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S))
        (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)
          - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a)
              (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) v))‖ ^ 2
      ≤ 9 * a * KG ell M κ c * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hellG : 0 < (geomOf ell k S).ell := hell0
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  -- the sum over sites splits into blocks (the field vanishes off Ω₀)
  set F : PeriodicLatticeSite Lf → ℝ := fun x => ∑ p, ‖(siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S))
        (siteMul (AdalyFormal.M1.hpart ell M k κ c S p) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)
          - ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) (ypMul (geomOf ell k S) (AdalyFormal.M1.hpart ell M k κ c S p) v))) x‖ ^ 2 with hF
  have hFoff : ∀ x, x ∉ (geomOf ell k S).Om0 → F x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero (fun p _ => ?_)
    rw [siteWt_apply, cQs_off hS hκ hM hell hR1 hR hc U a _ v hx, smul_zero, norm_zero]; simp
  have hsplit : ∑ x, F x = ∑ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x := by
    rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (QIdx (geomOf ell k S)))) (t := fun q => blockOf (yq q) (ell ^ jq q))
      (fun q _ q' _ hne => disj_q hP hne)]
    refine (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)).symm
    apply hFoff
    intro hx0
    obtain ⟨q, hq⟩ := Om0_block hP hx0
    exact hx (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hq⟩)
  rw [hsplit]
  -- per block
  have hblock : ∀ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x
      ≤ 9 * a * KG ell M κ c * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := by
    intro q
    have hj : (jq q) ≤ k := by have := jq_le q; exact this
    have hy : (yq q) ∈ (geomOf ell k S).Lam (jq q) := yq_mem q
    have hw0 : 0 ≤ wq (geomOf ell k S) a (jq q) := (wq_pos hell hP a (jq q) ha).le
    have hwq : wq (geomOf ell k S) a (jq q) ≤ a * (ell : ℝ) ^ (jq q) := by
      unfold wq
      have := ajSeq_le ell (jq q) hell ha
      have h0 : (0 : ℝ) ≤ (ell : ℝ) ^ (jq q) := by positivity
      show ajSeq a ell (jq q) * (ell : ℝ) ^ (jq q) ≤ _
      nlinarith
    set Kc := ContinuousLinearMap.adjoint (Qlev (geomOf ell k S) U (jq q) (yq q)) (v (Sum.inl q))
    have hFx : ∀ x ∈ blockOf (yq q) (ell ^ (jq q)), F x
        = ((ell : ℝ) ^ (jq q)) ^ 4 * wq (geomOf ell k S) a (jq q) *
          (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (yq q)) ^ 2) * ‖Kc x‖ ^ 2 := by
      intro x hx
      rw [hF]
      simp only
      have hsx : stratG (geomOf ell k S) x = (jq q) := stratG_eq hP hj hy hx
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [siteWt_apply, cQs_on hS hκ hM hell hR1 hR hc U a _ v q hx, norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, mul_pow, sq_abs, mul_pow, Real.sq_sqrt hw0]
      rw [Pi.add_apply, Real.exp_add, exp_sig (geomOf ell k S) hellG, hsx, show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]
      ring
    have hosc : ∀ x ∈ blockOf (yq q) (ell ^ (jq q)),
        ∑ p, (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (yq q)) ^ 2 ≤ 9 * KG ell M κ c := by
      intro x hx
      have := osc_block hS hκ hM hell hR1 hR hc q hx
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl (fun p _ => ?_); ring
    have hK0 := KG_nonneg ell M κ c
    have hKsum : ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), ‖Kc x‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ‖v (Sum.inl q)‖ ^ 2 := by
      have h1 := Kq_norm_sq U hellG (jq q) (yq q) (v (Sum.inl q))
      rw [PiLp.norm_sq_eq_of_L2] at h1
      refine le_trans ?_ h1
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
    have hpow : ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q)) = a * ((ell : ℝ) ^ (jq q)) ^ 2 := by
      have : (0 : ℝ) < (ell : ℝ) ^ (jq q) := by have : (0:ℝ) < ell := (by exact_mod_cast hell0); positivity
      rw [one_div, inv_pow, ← pow_mul]
      field_simp; ring
    calc ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), F x
        = ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), ((ell : ℝ) ^ (jq q)) ^ 4 * wq (geomOf ell k S) a (jq q) *
            (∑ p, (AdalyFormal.M1.hpart ell M k κ c S p x - AdalyFormal.M1.hpart ell M k κ c S p (yq q)) ^ 2) * ‖Kc x‖ ^ 2 :=
          Finset.sum_congr rfl hFx
      _ ≤ ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) * (9 * KG ell M κ c) * ‖Kc x‖ ^ 2 := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          refine mul_le_mul (mul_le_mul_of_nonneg_left hwq (by positivity)) (hosc x hx)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) * (9 * KG ell M κ c) * ∑ x ∈ blockOf (yq q) (ell ^ (jq q)), ‖Kc x‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) * (9 * KG ell M κ c) *
            (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ‖v (Sum.inl q)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hKsum (by positivity)
      _ = 9 * KG ell M κ c * (a * ((ell : ℝ) ^ (jq q)) ^ 2) * ‖v (Sum.inl q)‖ ^ 2 := by rw [← hpow]; ring
      _ = 9 * a * KG ell M κ c * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := by
          rw [ypWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
          show _ = 9 * a * KG ell M κ c * ((Real.exp (sigG (geomOf ell k S) (yq q))) ^ 2 * ‖v (Sum.inl q)‖ ^ 2)
          rw [exp_sig (geomOf ell k S) hellG]
          have hsy : stratG (geomOf ell k S) (yq q) = (jq q) := by
            refine stratG_eq hP hj hy ?_
            rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
          rw [hsy, show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]; ring
  calc ∑ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x
      ≤ ∑ q : QIdx (geomOf ell k S), 9 * a * KG ell M κ c * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 :=
        Finset.sum_le_sum (fun q _ => hblock q)
    _ = 9 * a * KG ell M κ c * ∑ q : QIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 9 * a * KG ell M κ c * ∑ p : PIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) p‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by have := KG_nonneg ell M κ c; positivity)
        rw [Fintype.sum_sum_type]
        have : 0 ≤ ∑ z : OffIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inr z)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        linarith

end comm

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.inner_dsite
#print axioms AdalyFormal.M1IMS.eq_of_inner_all
#print axioms AdalyFormal.M1IMS.Kq_supp
#print axioms AdalyFormal.M1IMS.Qlev_norm_sq_le
#print axioms AdalyFormal.M1IMS.Kq_norm_sq
#print axioms AdalyFormal.M1IMS.QpP_adj_on
#print axioms AdalyFormal.M1IMS.QpP_adj_off
#print axioms AdalyFormal.M1IMS.cQs_on
#print axioms AdalyFormal.M1IMS.cQs_off
#print axioms AdalyFormal.M1IMS.cQs_sum
#print axioms AdalyFormal.M1IMS.dsite

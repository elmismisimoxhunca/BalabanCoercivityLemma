import MI11
import MI4

/-!
# MI15 -- the projection `R` and the stratified row bounds of `Q'`, `Q'*` (M1 lane E, 2026-10-13)

On `G = geomOf ell k S` (admissible):
* `Rproj_norm_le` : `‖R s‖ ≤ ‖s‖`;
* `Q_row_bound`  : `‖ℓ^{strat} Q' f‖² ≤ max(a,1) ‖f‖²`;
* `Qs_row_bound` : `‖ℓ^{2 strat} Q'* v‖² ≤ max(a,1) ‖ℓ^{strat} v‖²`.
(The five-term commutator `cX_sum` and the gauge-fixing IMS `T_ims_concrete` are in MI16.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
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

/-! ## 0. the projection `R` -/

theorem Rproj_norm_le (G : TowerGeom L) (U : Cfg L) (s : SiteL2 L) : ‖Rproj G U s‖ ≤ ‖s‖ := by
  have h1 : ‖Rproj G U s‖ ^ 2 = ⟪Rproj G U s, s⟫ := by
    rw [← real_inner_self_eq_norm_sq, Rproj_symm, Rproj_idem, real_inner_comm]
  have h2 : ⟪Rproj G U s, s⟫ ≤ ‖Rproj G U s‖ * ‖s‖ := real_inner_le_norm _ _
  by_cases h0 : ‖Rproj G U s‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖Rproj G U s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith [norm_nonneg s]

section geo
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
include hS hell

/-- `‖ℓ^{strat} Q' f‖² ≤ max(a,1) ‖f‖²`. -/
theorem Q_row_bound (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (f : SiteL2 Lf) :
    ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (QpP (geomOf ell k S) U a f)‖ ^ 2 ≤ max a 1 * ‖f‖ ^ 2 := by
  classical
  set G := geomOf ell k S
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hellG : 0 < G.ell := hell0
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  have hrow : ∀ q : QIdx G, ‖(ypWt G (sigG G) (QpP G U a f)) (Sum.inl q)‖ ^ 2
      ≤ a * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
    intro q
    have hj : jq q ≤ k := by have := jq_le q; exact this
    have hy : yq q ∈ G.Lam (jq q) := yq_mem q
    have hw0 : 0 ≤ wq G a (jq q) := (wq_pos hell hP a (jq q) ha).le
    have hwq : wq G a (jq q) ≤ a * (ell : ℝ) ^ (jq q) := by
      unfold wq
      have := ajSeq_le ell (jq q) hell ha
      have h0 : (0 : ℝ) ≤ (ell : ℝ) ^ (jq q) := by positivity
      show ajSeq a ell (jq q) * (ell : ℝ) ^ (jq q) ≤ _
      nlinarith
    have hsy : stratG G (yq q) = jq q := by
      refine stratG_eq hP hj hy ?_
      rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
    rw [ypWt_apply, QpP_inl, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ wq G a q.1.1.val from hw0)]
    show (Real.exp (sigG G (yq q))) ^ 2 * (wq G a (jq q) * ‖Qlev G U (jq q) (yq q) (siteMask G.Om0 f)‖ ^ 2) ≤ _
    rw [exp_sig G hellG, hsy, show ((G.ell : ℕ) : ℝ) = (ell : ℝ) from rfl]
    have hQ := Qlev_norm_sq_le U hellG (jq q) (yq q) (siteMask G.Om0 f)
    have hQ' : ‖Qlev G U (jq q) (yq q) (siteMask G.Om0 f)‖ ^ 2
        ≤ ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by
      rw [Qlev_apply]
      refine (Qcomposite_sq_le (bgTower G U) G.ell hellG (jq q) (WithLp.ofLp (siteMask G.Om0 f)) (yq q)).trans (le_of_eq ?_)
      show ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ boxF (yq q) (ell ^ (jq q)), _ = _
      rw [boxF_eq_blockOf]
      congr 1
      refine Finset.sum_congr rfl (fun x hx => ?_)
      show ‖siteMask G.Om0 f x‖ ^ 2 = _
      rw [siteMask_on _ _ _ (block_Om0 hP q hx)]
    have hpow : ((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q)) = a := by
      have : (0 : ℝ) < (ell : ℝ) ^ (jq q) := by have : (0:ℝ) < ell := (by exact_mod_cast hell0); positivity
      rw [one_div, inv_pow, ← pow_mul]; field_simp; ring
    have hS0 : 0 ≤ ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc ((ell : ℝ) ^ (jq q)) ^ 2 * (wq G a (jq q) * ‖Qlev G U (jq q) (yq q) (siteMask G.Om0 f)‖ ^ 2)
        ≤ ((ell : ℝ) ^ (jq q)) ^ 2 * ((a * (ell : ℝ) ^ (jq q)) *
            (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hwq hQ' (sq_nonneg _) (by positivity)) (by positivity)
      _ = (((ell : ℝ) ^ (jq q)) ^ 2 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q)))
            * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by ring
      _ = a * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 := by rw [hpow]
  have hpad : ∀ x : OffIdx G, ‖(ypWt G (sigG G) (QpP G U a f)) (Sum.inr x)‖ ^ 2 = ‖f x.1‖ ^ 2 := by
    intro x
    have h0 : sigG G x.1 = 0 := by unfold sigG; rw [stratG_off hP x.2]; simp
    rw [ypWt_apply, QpP_inr, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    show (Real.exp (sigG G x.1) * _) ^ 2 = _
    rw [h0, Real.exp_zero, one_mul]
  simp only [hpad]
  -- disjointness of blocks and padding
  have hsplit : ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 + ∑ x : OffIdx G, ‖f x.1‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (QIdx G))) (t := fun q => blockOf (yq q) (ell ^ jq q))
      (fun q _ q' _ hne => disj_q hP hne)]
    have hoff : ∑ x : OffIdx G, ‖f x.1‖ ^ 2 = ∑ x ∈ (Finset.univ.filter (fun x => x ∉ G.Om0)), ‖f x‖ ^ 2 :=
      (Finset.sum_subtype (p := fun x => x ∉ G.Om0) _ (fun x => by simp) (fun x => ‖f x‖ ^ 2)).symm
    rw [hoff, ← Finset.sum_union]
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
    · rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hx').2 (block_Om0 hP q hq)
  have ha1 : a ≤ max a 1 := le_max_left _ _
  have h11 : (1 : ℝ) ≤ max a 1 := le_max_right _ _
  calc ∑ q : QIdx G, ‖(ypWt G (sigG G) (QpP G U a f)) (Sum.inl q)‖ ^ 2 + ∑ x : OffIdx G, ‖f x.1‖ ^ 2
      ≤ ∑ q : QIdx G, a * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 + ∑ x : OffIdx G, ‖f x.1‖ ^ 2 :=
        add_le_add (Finset.sum_le_sum (fun q _ => hrow q)) le_rfl
    _ ≤ max a 1 * (∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 + ∑ x : OffIdx G, ‖f x.1‖ ^ 2) := by
        rw [← Finset.mul_sum, mul_add]
        have h0 : 0 ≤ ∑ q : QIdx G, ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖f x‖ ^ 2 :=
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        have h0' : 0 ≤ ∑ x : OffIdx G, ‖f x.1‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        nlinarith
    _ ≤ max a 1 * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_left hsplit (by linarith)

/-- `‖ℓ^{2 strat} Q'* v‖² ≤ max(a,1) ‖ℓ^{strat} v‖²`. -/
theorem Qs_row_bound (U : Cfg Lf) (a : ℝ) (ha : 0 < a) (v : YP (geomOf ell k S)) :
    ‖siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)‖ ^ 2
      ≤ max a 1 * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖ ^ 2 := by
  classical
  have hell0 : 0 < ell := by omega
  have hP := properTower_geomOf hell0 hS
  have hellG : 0 < (geomOf ell k S).ell := hell0
  set F : PeriodicLatticeSite Lf → ℝ := fun x =>
    ‖(siteWt (sigG (geomOf ell k S) + sigG (geomOf ell k S)) (ContinuousLinearMap.adjoint (QpP (geomOf ell k S) U a) v)) x‖ ^ 2 with hF
  rw [PiLp.norm_sq_eq_of_L2]
  have hsplit : ∑ x, F x = ∑ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x + ∑ x : OffIdx (geomOf ell k S), F x.1 := by
    rw [← Finset.sum_biUnion (s := (Finset.univ : Finset (QIdx (geomOf ell k S)))) (t := fun q => blockOf (yq q) (ell ^ jq q))
      (fun q _ q' _ hne => disj_q hP hne)]
    have hoff : ∑ x : OffIdx (geomOf ell k S), F x.1 = ∑ x ∈ (Finset.univ.filter (fun x => x ∉ (geomOf ell k S).Om0)), F x :=
      (Finset.sum_subtype (p := fun x => x ∉ (geomOf ell k S).Om0) _ (fun x => by simp) F).symm
    rw [hoff, ← Finset.sum_union]
    · refine (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)).symm
      exfalso
      apply hx
      by_cases hx0 : x ∈ (geomOf ell k S).Om0
      · obtain ⟨q, hq⟩ := Om0_block hP hx0
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hq⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩)
    · rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hx').2 (block_Om0 hP q hq)
  show ∑ x, F x ≤ _
  rw [hsplit, PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  have hrow : ∀ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x
      ≤ a * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := by
    intro q
    have hj : jq q ≤ k := by have := jq_le q; exact this
    have hy : yq q ∈ (geomOf ell k S).Lam (jq q) := yq_mem q
    have hw0 : 0 ≤ wq (geomOf ell k S) a (jq q) := (wq_pos hell hP a (jq q) ha).le
    have hwq : wq (geomOf ell k S) a (jq q) ≤ a * (ell : ℝ) ^ (jq q) := by
      unfold wq
      have := ajSeq_le ell (jq q) hell ha
      have h0 : (0 : ℝ) ≤ (ell : ℝ) ^ (jq q) := by positivity
      show ajSeq a ell (jq q) * (ell : ℝ) ^ (jq q) ≤ _
      nlinarith
    have hsy : stratG (geomOf ell k S) (yq q) = jq q := by
      refine stratG_eq hP hj hy ?_
      rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by have := Nat.one_le_pow (jq q) ell hell0; omega⟩
    set Kc := ContinuousLinearMap.adjoint (Qlev (geomOf ell k S) U (jq q) (yq q)) (v (Sum.inl q))
    have hFx : ∀ x ∈ blockOf (yq q) (ell ^ jq q), F x = ((ell : ℝ) ^ (jq q)) ^ 4 * wq (geomOf ell k S) a (jq q) * ‖Kc x‖ ^ 2 := by
      intro x hx
      rw [hF]
      simp only
      rw [siteWt_apply, QpP_adj_on hP U a v q hx, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hw0]
      rw [Pi.add_apply, Real.exp_add, exp_sig (geomOf ell k S) hellG, stratG_eq hP hj hy hx,
        show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]
      ring
    have hK := Kq_norm_sq U hellG (jq q) (yq q) (v (Sum.inl q))
    rw [PiLp.norm_sq_eq_of_L2] at hK
    have hKB : ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖Kc x‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ‖v (Sum.inl q)‖ ^ 2 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)) hK
    have hpow : ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) * ((1 / (ell : ℝ) ^ 3) ^ (jq q))
        = a * ((ell : ℝ) ^ (jq q)) ^ 2 := by
      have : (0 : ℝ) < (ell : ℝ) ^ (jq q) := by have : (0:ℝ) < ell := (by exact_mod_cast hell0); positivity
      rw [one_div, inv_pow, ← pow_mul]; field_simp; ring
    calc ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x
        = ((ell : ℝ) ^ (jq q)) ^ 4 * wq (geomOf ell k S) a (jq q) * ∑ x ∈ blockOf (yq q) (ell ^ jq q), ‖Kc x‖ ^ 2 := by
          rw [Finset.sum_congr rfl hFx, Finset.mul_sum]
      _ ≤ ((ell : ℝ) ^ (jq q)) ^ 4 * (a * (ell : ℝ) ^ (jq q)) *
            (((1 / (ell : ℝ) ^ 3) ^ (jq q)) * ‖v (Sum.inl q)‖ ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hwq (by positivity)) hKB
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = a * (((ell : ℝ) ^ (jq q)) ^ 2 * ‖v (Sum.inl q)‖ ^ 2) := by rw [← mul_assoc, hpow]; ring
      _ = a * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := by
          rw [ypWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
          show _ = a * ((Real.exp (sigG (geomOf ell k S) (yq q))) ^ 2 * _)
          rw [exp_sig (geomOf ell k S) hellG, hsy, show (((geomOf ell k S).ell : ℕ) : ℝ) = (ell : ℝ) from rfl]
  have hpad : ∀ x : OffIdx (geomOf ell k S), F x.1 = ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inr x)‖ ^ 2 := by
    intro x
    have h0 : sigG (geomOf ell k S) x.1 = 0 := by unfold sigG; rw [stratG_off hP x.2]; simp
    rw [hF]; simp only
    rw [siteWt_apply, QpP_adj_off hP U a v x.2, ypWt_apply]
    show ‖Real.exp (sigG (geomOf ell k S) x.1 + sigG (geomOf ell k S) x.1) • v (Sum.inr ⟨x.1, x.2⟩)‖ ^ 2
      = ‖Real.exp (sigG (geomOf ell k S) x.1) • v (Sum.inr x)‖ ^ 2
    rw [h0, add_zero]
    rfl
  simp only [hpad]
  have ha1 : a ≤ max a 1 := le_max_left _ _
  have h11 : (1 : ℝ) ≤ max a 1 := le_max_right _ _
  have h0 : 0 ≤ ∑ q : QIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h0' : 0 ≤ ∑ x : OffIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inr x)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ∑ q : QIdx (geomOf ell k S), ∑ x ∈ blockOf (yq q) (ell ^ jq q), F x + ∑ x : OffIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inr x)‖ ^ 2
      ≤ ∑ q : QIdx (geomOf ell k S), a * ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inl q)‖ ^ 2 + ∑ x : OffIdx (geomOf ell k S), ‖(ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v) (Sum.inr x)‖ ^ 2 :=
        add_le_add (Finset.sum_le_sum (fun q _ => hrow q)) le_rfl
    _ ≤ _ := by rw [← Finset.mul_sum, mul_add]; nlinarith

end geo

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.Rproj_norm_le
#print axioms AdalyFormal.M1IMS.Q_row_bound
#print axioms AdalyFormal.M1IMS.Qs_row_bound

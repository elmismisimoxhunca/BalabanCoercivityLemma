import MS3

/-!
# MS4 -- S3 part 1 (PLAN.md §1.2 Layer S): the stratified `Γ = X*X` lower bound from a weighted (approximate) right inverse

Objects of MS1 (padded `QpP`, `LP = DelpA + (1 − Ω₀)`, `X = LinvP QpP*`).
* `sum_QIdx` : `Σ_{q : QIdx} F(j_q, y_q) = Σ_{j ≤ k} Σ_{y ∈ Λ_j} F(j, y)`.
* **`LP_form_le`** (ProperTower, `ℓ ≥ 2`, `a > 0`, ANY `U`): `⟪x, LP x⟫ ≤ (12 + a)‖x‖²`.
* `form_cs` : `⟪x, LP y⟫² ≤ ⟪x, LP x⟫⟪y, LP y⟫`.
* **`gamma_lower_approx`** (abstract in the row weights `β > 0`): if for `v ∈ YP` a site field `g` has energy
  `⟪g, LP g⟫ ≤ S := Σ_p ‖v_p‖²/β_p` and is an `η`-approximate preimage in the sense `|⟪v, QpP g⟫ − S| ≤ ηS`, then
  `(1 − η)² S ≤ K ‖X v‖²` (`K` any form bound, e.g. `12 + a`).  With `η = 0` and an exact right inverse this is the
  stratified DL10 `gamma_lower` (the DL10 statement has ONE `b` for all rows; here each row has its own `β_p`).
* **`exists_Gami_of_lower`** : `c S(v) ≤ ‖Xv‖²` (`c > 0`) for all `v` ⇒ `Γ = X*X` has a two-sided inverse (finite dimension) —
  the `Gi`/`hG1` hypothesis of `Rproj_eq_strat` (MS1) and the `Gami` of a DL13 `GamHyp`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)

variable {L : PeriodicLatticeExtent}

open Classical in
theorem sum_QIdx (G : TowerGeom L) (F : ℕ → PeriodicLatticeSite L → ℝ) :
    ∑ q : QIdx G, F q.1.1.val q.1.2 = ∑ j ∈ Finset.range (G.k + 1), ∑ y ∈ LamF G j, F j y := by
  have h1 : ∑ j ∈ Finset.range (G.k + 1), ∑ y ∈ LamF G j, F j y
      = ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L, if y ∈ G.Lam j then F j y else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext y; simp [LamF]) (fun _ _ => rfl)
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => ∑ y : PeriodicLatticeSite L, if y ∈ G.Lam j then F j y else 0)]
  rw [← Fintype.sum_prod_type' (fun (j : Fin (G.k + 1)) (y : PeriodicLatticeSite L) =>
      if y ∈ G.Lam j.val then F j.val y else 0)]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun p : Fin (G.k + 1) × PeriodicLatticeSite L => p.2 ∈ G.Lam p.1.val) _
    (fun p => by simp) (fun p => F p.1.val p.2)).symm

theorem norm_sq_split (G : TowerGeom L) (x : SiteL2 L) :
    ‖x‖ ^ 2 = ‖siteMask G.Om0 x‖ ^ 2 + ∑ z : OffIdx G, ‖x z.1‖ ^ 2 := by
  have h1 : ‖x‖ ^ 2 = ⟪x, siteMask G.Om0 x⟫ + ⟪x, (1 - siteMask G.Om0) x⟫ := by
    rw [← inner_add_right, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel,
      real_inner_self_eq_norm_sq]
  have h2 : ⟪x, siteMask G.Om0 x⟫ = ‖siteMask G.Om0 x‖ ^ 2 := by
    rw [← siteMask_idem G.Om0 x, ← siteMask_symm, siteMask_idem, real_inner_self_eq_norm_sq]
  rw [h1, h2, inner_one_sub_mask]
  congr 1
  refine Finset.sum_congr rfl (fun z _ => real_inner_self_eq_norm_sq _)

theorem grad_sq_le (U : Cfg L) (g : SiteL2 L) : ‖gradL2 U g‖ ^ 2 ≤ 12 * ‖g‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hpt : ∀ b : Bond L, ‖gradL2 U g b‖ ^ 2 ≤ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2 + 2 * ‖g b.1‖ ^ 2 := by
    intro b
    rw [gradL2_apply']
    have h1 := norm_sub_le (RMap (U b) (g (periodicLatticeShift b.1 b.2))) (g b.1)
    rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖g (periodicLatticeShift b.1 b.2)‖ - ‖g b.1‖)]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpt b)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hh := sum_head_eq (L := L) (fun x => ‖g x‖ ^ 2)
  have ht : ∑ b : Bond L, ‖g b.1‖ ^ 2 = 3 * ∑ x, ‖g x‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]; norm_num
  rw [hh, ht] at hs
  have hn : ‖g‖ ^ 2 = ∑ x, ‖g x‖ ^ 2 := norm_sq_site g
  rw [hn]; linarith

/-- **`⟪x, LP x⟫ ≤ (12 + a)‖x‖²`** at a proper tower, every background `U`. -/
theorem LP_form_le (ell k : ℕ) (hell : 2 ≤ ell) {G : TowerGeom L} (hP : ProperTower G ell k)
    (U : Cfg L) (a : ℝ) (ha : 0 < a) (x : SiteL2 L) :
    ⟪x, LP G U a x⟫ ≤ (12 + a) * ‖x‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  have hw : ∀ j, 0 ≤ wq G a j := fun j => by
    unfold wq; have := ajSeq_ge G.ell j (by rw [hP.ell_eq]; exact hell) ha
    have h0 : 0 ≤ ajSeq a G.ell j := by linarith
    exact mul_nonneg h0 (by positivity)
  rw [inner_LP G U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  set g := siteMask G.Om0 x with hg
  have hD : ‖Dm G U x‖ ^ 2 ≤ 12 * ‖g‖ ^ 2 := grad_sq_le U g
  have hQ : ‖QpP G U a x‖ ^ 2 = ∑ q : QIdx G, wq G a q.1.1.val * ‖Qlev G U q.1.1.val q.1.2 g‖ ^ 2
      + ∑ z : OffIdx G, ‖x z.1‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_QpP G U a hw]
    congr 1
    · refine Finset.sum_congr rfl (fun q _ => by rw [real_inner_self_eq_norm_sq])
    · refine Finset.sum_congr rfl (fun z _ => real_inner_self_eq_norm_sq _)
  -- the mass rows
  have hmass : ∑ q : QIdx G, wq G a q.1.1.val * ‖Qlev G U q.1.1.val q.1.2 g‖ ^ 2 ≤ a * ‖g‖ ^ 2 := by
    rw [sum_QIdx G (fun j y => wq G a j * ‖Qlev G U j y g‖ ^ 2)]
    have hpart : ‖g‖ ^ 2 = ∑ j ∈ Finset.range (k + 1), ∑ y ∈ LamF G j, ∑ z ∈ blockOf y (ell ^ j), ‖g z‖ ^ 2 := by
      rw [norm_sq_site]
      exact sum_partition hP (fun z => ‖g z‖ ^ 2) (fun z hz => by rw [hg, siteMask_off _ _ _ hz]; simp)
    rw [hpart, Finset.mul_sum, hP.k_eq]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun y hy => ?_)
    have hQ2 := Qcomposite_sq_le (bgTower G U) G.ell (by rw [hP.ell_eq]; exact hell0) j (WithLp.ofLp g) y
    rw [hP.ell_eq, boxF_eq_blockOf] at hQ2
    have hQ2' : ‖Qlev G U j y g‖ ^ 2 ≤ ((1 / (ell : ℝ) ^ 3) ^ j) * ∑ z ∈ blockOf y (ell ^ j), ‖g z‖ ^ 2 := by
      rw [Qlev_apply, hP.ell_eq]; exact hQ2
    have haj := ajSeq_le ell j hell ha
    have haj0 : 0 ≤ ajSeq a ell j := by linarith [ajSeq_ge ell j hell ha]
    set S := ∑ z ∈ blockOf y (ell ^ j), ‖g z‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun z _ => sq_nonneg _)
    have hnj : (1 : ℝ) ≤ (ell : ℝ) ^ j := one_le_pow₀ (by exact_mod_cast hell0)
    have hfac : (ell : ℝ) ^ j * (1 / (ell : ℝ) ^ 3) ^ j ≤ 1 := by
      have e3 : ((ell : ℝ) ^ 3) ^ j = ((ell : ℝ) ^ j) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [one_div_pow, e3, ← div_eq_mul_one_div, div_le_one (by positivity)]
      set n := (ell : ℝ) ^ j
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ n - 1))
        (by linarith : (0:ℝ) ≤ n + 1)]
    unfold wq
    rw [hP.ell_eq]
    have h1 : ajSeq a ell j * (ell : ℝ) ^ j * ‖Qlev G U j y g‖ ^ 2
        ≤ ajSeq a ell j * (ell : ℝ) ^ j * (((1 / (ell : ℝ) ^ 3) ^ j) * S) :=
      mul_le_mul_of_nonneg_left hQ2' (by positivity)
    have h2 : ajSeq a ell j * (ell : ℝ) ^ j * (((1 / (ell : ℝ) ^ 3) ^ j) * S)
        = ajSeq a ell j * (((ell : ℝ) ^ j * (1 / (ell : ℝ) ^ 3) ^ j) * S) := by ring
    have h3 : ajSeq a ell j * (((ell : ℝ) ^ j * (1 / (ell : ℝ) ^ 3) ^ j) * S) ≤ a * S := by
      have := mul_le_mul_of_nonneg_right hfac hS0
      rw [one_mul] at this
      exact mul_le_mul haj this (by positivity) ha.le
    linarith
  have hsplit := norm_sq_split G x
  rw [← hg] at hsplit
  have hoff0 : 0 ≤ ∑ z : OffIdx G, ‖x z.1‖ ^ 2 := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  rw [hQ, hsplit]
  nlinarith [hD, hmass, sq_nonneg ‖g‖]

/-- Cauchy–Schwarz for the form `⟪·, LP ·⟫`. -/
theorem form_cs (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j) (x y : SiteL2 L) :
    ⟪x, LP G U a y⟫ ^ 2 ≤ ⟪x, LP G U a x⟫ * ⟪y, LP G U a y⟫ := by
  rw [inner_LP G U a hw, inner_LP G U a hw, inner_LP G U a hw]
  set A := Dm G U x; set B := Dm G U y; set C := QpP G U a x; set D := QpP G U a y
  have h1 := abs_real_inner_le_norm A B
  have h2 := abs_real_inner_le_norm C D
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h3 : |⟪A, B⟫ + ⟪C, D⟫| ≤ ‖A‖ * ‖B‖ + ‖C‖ * ‖D‖ := (abs_add_le _ _).trans (add_le_add h1 h2)
  have h4 : (⟪A, B⟫ + ⟪C, D⟫) ^ 2 ≤ (‖A‖ * ‖B‖ + ‖C‖ * ‖D‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  nlinarith [sq_nonneg (‖A‖ * ‖D‖ - ‖C‖ * ‖B‖)]

/-- **stratified `gamma_lower`, approximate-preimage form**. -/
theorem gamma_lower_approx (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 ≤ wq G a j)
    (hu : IsUnit (LP G U a)) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ⟪x, LP G U a x⟫ ≤ K * ‖x‖ ^ 2)
    (β : PIdx G → ℝ) (η : ℝ) (hη : η ≤ 1) (v : YP G) (g : SiteL2 L)
    (hgE : ⟪g, LP G U a g⟫ ≤ ∑ p, ‖v p‖ ^ 2 / β p)
    (hr : |⟪v, QpP G U a g⟫ - ∑ p, ‖v p‖ ^ 2 / β p| ≤ η * ∑ p, ‖v p‖ ^ 2 / β p)
    (hS0 : 0 ≤ ∑ p, ‖v p‖ ^ 2 / β p) :
    (1 - η) ^ 2 * ∑ p, ‖v p‖ ^ 2 / β p ≤ K * ‖Xop G U a v‖ ^ 2 := by
  set S := ∑ p, ‖v p‖ ^ 2 / β p with hS
  have e1 : ⟪v, QpP G U a g⟫ = ⟪Xop G U a v, LP G U a g⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← LP_Xop G U a hu hw, LP_symm G U a hw]
  have hcs := form_cs G U a hw (Xop G U a v) g
  have hXK := hK (Xop G U a v)
  have hlow : (1 - η) * S ≤ ⟪v, QpP G U a g⟫ := by
    have := (abs_le.mp hr).1; linarith
  have hpos : 0 ≤ (1 - η) * S := mul_nonneg (by linarith) hS0
  rw [e1] at hlow
  have h2 : ((1 - η) * S) ^ 2 ≤ ⟪Xop G U a v, LP G U a g⟫ ^ 2 := pow_le_pow_left₀ hpos hlow 2
  have hgE0 : 0 ≤ ⟪g, LP G U a g⟫ := by
    rw [inner_LP G U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]; positivity
  have hXE0 : 0 ≤ ⟪Xop G U a v, LP G U a (Xop G U a v)⟫ := by
    rw [inner_LP G U a hw, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]; positivity
  have h3 : ((1 - η) * S) ^ 2 ≤ (K * ‖Xop G U a v‖ ^ 2) * S := by
    calc ((1 - η) * S) ^ 2 ≤ ⟪Xop G U a v, LP G U a g⟫ ^ 2 := h2
      _ ≤ ⟪Xop G U a v, LP G U a (Xop G U a v)⟫ * ⟪g, LP G U a g⟫ := hcs
      _ ≤ (K * ‖Xop G U a v‖ ^ 2) * S := mul_le_mul hXK hgE hgE0 (by positivity)
  rcases hS0.lt_or_eq with hSp | hSz
  · have h4 : ((1 - η) ^ 2 * S) * S ≤ (K * ‖Xop G U a v‖ ^ 2) * S := by nlinarith [h3]
    exact le_of_mul_le_mul_right h4 hSp
  · rw [← hSz, mul_zero]; positivity

/-- `Γ = X*X` is invertible once it is coercive in the row-weighted sense. -/
theorem exists_Gami_of_lower (G : TowerGeom L) (U : Cfg L) (a : ℝ) (β : PIdx G → ℝ) (hβ : ∀ p, 0 < β p)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ v : YP G, c * ∑ p, ‖v p‖ ^ 2 / β p ≤ ‖Xop G U a v‖ ^ 2) :
    ∃ Gi : YP G →L[ℝ] YP G,
      (∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) (Gi u) = u) ∧
      (∀ u, Gi ((ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a) u) = u) := by
  set Γ : YP G →L[ℝ] YP G := ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a with hΓ
  have hinj : Function.Injective (Γ : YP G →ₗ[ℝ] YP G) := by
    intro v w hvw
    have hd : Γ (v - w) = 0 := by
      have : (Γ : YP G →ₗ[ℝ] YP G) v - (Γ : YP G →ₗ[ℝ] YP G) w = 0 := by rw [hvw, sub_self]
      rw [map_sub]; exact this
    have hX : ‖Xop G U a (v - w)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right]
      have : ContinuousLinearMap.adjoint (Xop G U a) (Xop G U a (v - w)) = Γ (v - w) := rfl
      rw [this, hd, inner_zero_right]
    have hS := hlow (v - w)
    rw [hX] at hS
    have hS0 : ∑ p, ‖(v - w) p‖ ^ 2 / β p = 0 := by
      have h0 : 0 ≤ ∑ p, ‖(v - w) p‖ ^ 2 / β p :=
        Finset.sum_nonneg (fun p _ => div_nonneg (sq_nonneg _) (hβ p).le)
      nlinarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => div_nonneg (sq_nonneg _) (hβ p).le)).mp hS0
    rw [← sub_eq_zero]
    refine PiLp.ext (fun p => ?_)
    have := hall p (Finset.mem_univ p)
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · simpa using h
    · exact absurd h (hβ p).ne'
  set e := LinearEquiv.ofInjectiveEndo (Γ : YP G →ₗ[ℝ] YP G) hinj with he
  have h1 : ∀ x, e x = Γ x := fun x => by
    rw [he, LinearEquiv.coe_ofInjectiveEndo]; rfl
  refine ⟨LinearMap.toContinuousLinearMap (e.symm : YP G →ₗ[ℝ] YP G), fun u => ?_, fun u => ?_⟩
  · show Γ (e.symm u) = u
    rw [← h1]; exact e.apply_symm_apply u
  · show e.symm (Γ u) = u
    rw [← h1]; exact e.symm_apply_apply u

#print axioms sum_QIdx
#print axioms norm_sq_split
#print axioms grad_sq_le
#print axioms LP_form_le
#print axioms form_cs
#print axioms gamma_lower_approx
#print axioms exists_Gami_of_lower

end AdalyFormal.M1Site

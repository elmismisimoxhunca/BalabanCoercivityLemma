import DLR7

/-!
# DL8 -- Combes–Thomas for the genuine site operator `Δ'_a = Δ_U + Q'*aQ'` (full tower), k- and volume-uniform

Setting: `G : TowerGeom L` with `Ω₀ = ` torus and the full-tower stratification (`Λ_j = ∅` for `j < k`, `Λ_k` = points with all coordinates
divisible by `ℓ^k`); `φ` a weight with `WtLip θ' φ` (one fine step) and `|φ x − φ y| ≤ δ` on every level-`k` block `box(y, ℓ^k)`.
* `siteCT_form` : `⟪f, e^φ Δ'_a e^{−φ} f⟫ ≥ ½⟪f, Δ'_a f⟫ − E_s ‖f‖²`,
  `E_s = 9 (e^{θ'} − 1)² + 3 a_k ℓ^k ℓ^{−3k} (e^δ − 1)²`.  With `θ' = θ/ℓ^k`: `E_s ≤ (9θ²e^{2θ} + 3 a_k (e^δ−1)²)/n²`, the scale of the
  site coercivity constant `c_s/n²` (ASAl3 `site_coercive_GF_al`): k-uniform.
* `siteCT_inv` : if moreover `c ‖f‖² ≤ ½⟪f,Δ'_a f⟫ − E_s‖f‖²` (`c > 0`) and `Δ'_a` is a unit, then `c ‖e^φ G' e^{−φ} g‖ ≤ ‖g‖`
  (the weighted bound of the genuine `G' = Gp`), and `½‖D(e^φ G' e^{−φ} g)‖² ≤ ⟪·,g⟫ + E_s‖·‖²` (`siteCT_grad`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.QjComposite (Qcomposite)

variable {L : PeriodicLatticeExtent}

open scoped Classical

theorem siteMask_univ (f : SiteL2 L) : siteMask (Set.univ : Set (PeriodicLatticeSite L)) f = f := by
  refine PiLp.ext (fun x => ?_)
  rw [siteMask_apply]; simp

theorem DelpA_univ (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ) (f : SiteL2 L) :
    DelpA G U a f = lapFull U f + Qpa G U a f := by
  unfold DelpA
  simp only [ContinuousLinearMap.comp_apply, hOm, siteMask_univ, ContinuousLinearMap.add_apply]

/-- the conjugated mass form, term by term -/
theorem Qpa_conj_inner (G : TowerGeom L) (U : Cfg L) (a : ℝ) (φ : PeriodicLatticeSite L → ℝ) (f : SiteL2 L) :
    ⟪f, siteWt φ (Qpa G U a (siteWt (-φ) f))⟫
      = ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
          if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) *
            ⟪Qlev G U j y (siteWt φ f), Qlev G U j y (siteWt (-φ) f)⟫ else 0 := by
  classical
  rw [← siteWt_symm]
  simp only [Qpa, ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun y _ => ?_))
  split_ifs
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, real_inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right]
  · simp

/-- factoring the weight at the block base point -/
theorem Qlev_siteWt_shift (G : TowerGeom L) (U : Cfg L) (j : ℕ) (y : PeriodicLatticeSite L)
    (φ : PeriodicLatticeSite L → ℝ) (c : ℝ) (f : SiteL2 L) :
    Qlev G U j y (siteWt φ f) = Real.exp c • Qlev G U j y (siteWt (fun x => φ x - c) f) := by
  rw [← map_smul]
  congr 1
  refine PiLp.ext (fun x => ?_)
  rw [PiLp.smul_apply, siteWt_apply, siteWt_apply, smul_smul, ← Real.exp_add]
  congr 2; ring

/-- the box bound of a level-`j` row applied to `(e^{ψ} − 1) f` -/
theorem Qlev_err_sq (G : TowerGeom L) (U : Cfg L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (ψ : PeriodicLatticeSite L → ℝ) (δ : ℝ) (hψ : ∀ x ∈ boxF y (G.ell ^ j), |ψ x| ≤ δ) (f : SiteL2 L) :
    ‖Qlev G U j y (siteWt ψ f) - Qlev G U j y f‖ ^ 2
      ≤ ((1 / (G.ell : ℝ) ^ 3) ^ j) * (Real.exp δ - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖f x‖ ^ 2 := by
  rw [← map_sub, Qlev_apply]
  have h := AdalyFormal.DLayer.Qcomposite_sq_le (bgTower G U) G.ell hell j (WithLp.ofLp (siteWt ψ f - f)) y
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun x hx => ?_)
  have e : (WithLp.ofLp (siteWt ψ f - f)) x = (Real.exp (ψ x) - 1) • f x := by
    show (siteWt ψ f - f) x = _
    rw [PiLp.sub_apply, siteWt_apply, sub_smul, one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h1 := abs_exp_sub_one_le_of (ψ x) δ (hψ x hx)
  have h0 : 0 ≤ Real.exp δ - 1 := le_trans (abs_nonneg _) h1
  calc (Real.exp (ψ x) - 1) ^ 2 = |Real.exp (ψ x) - 1| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.exp δ - 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- `Σ_{y ∈ Λ_k} Σ_{box(y)} ‖f‖² ≤ ‖f‖²` (disjoint blocks) -/
theorem sum_boxes_le (G : TowerGeom L)
    (hLk : ∀ y ∈ G.Lam G.k, ∀ μ, G.ell ^ G.k ∣ (y μ).val) (f : SiteL2 L) :
    ∑ y : PeriodicLatticeSite L, (if y ∈ G.Lam G.k then ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2 else 0) ≤ ‖f‖ ^ 2 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_biUnion]
  · rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => sq_nonneg _)
  · intro y hy y' hy' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    exact boxF_disjoint (hLk y hy) (hLk y' hy') hne

/-- **site Combes–Thomas form**. -/
theorem siteCT_form (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (hell : 0 < G.ell)
    (hLlt : ∀ j, j < G.k → ∀ y, y ∉ G.Lam j)
    (hLk : ∀ y ∈ G.Lam G.k, ∀ μ, G.ell ^ G.k ∣ (y μ).val)
    (U : Cfg L) (a : ℝ) (ha : 0 ≤ ajSeq a G.ell G.k)
    (φ : PeriodicLatticeSite L → ℝ) (θ' δ : ℝ) (hφ : WtLip θ' φ)
    (hbox : ∀ y ∈ G.Lam G.k, ∀ x ∈ boxF y (G.ell ^ G.k), |φ x - φ y| ≤ δ) (f : SiteL2 L) :
    (1 / 2) * ⟪f, DelpA G U a f⟫
      - (9 * (Real.exp θ' - 1) ^ 2
          + 3 * (ajSeq a G.ell G.k * (G.ell : ℝ) ^ G.k) * (1 / (G.ell : ℝ) ^ 3) ^ G.k * (Real.exp δ - 1) ^ 2) * ‖f‖ ^ 2
      ≤ ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫ := by
  classical
  have hθ0 : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
  have hδ0 : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
  -- split into the gradient and mass parts
  have hsplit : ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫
      = ⟪f, siteWt φ (lapFull U (siteWt (-φ) f))⟫ + ⟪f, siteWt φ (Qpa G U a (siteWt (-φ) f))⟫ := by
    rw [DelpA_univ G hOm, map_add, inner_add_right]
  have hsplit0 : ⟪f, DelpA G U a f⟫ = ‖gradL2 U f‖ ^ 2 + ⟪f, Qpa G U a f⟫ := by
    rw [DelpA_univ G hOm, inner_add_right, inner_lapFull]
  rw [hsplit, hsplit0]
  -- gradient part
  set u := gradL2 U f with hu
  set up := bondWt φ (gradL2 U (siteWt (-φ) f)) with hup
  set um := bondWt (-φ) (gradL2 U (siteWt φ f)) with hum
  have hep : ‖up - u‖ ≤ Real.sqrt 3 * (Real.exp θ' - 1) * ‖f‖ := grad_conj_err U φ θ' hφ f
  have hφ' : WtLip θ' (-φ) := fun x μ => by
    have := hφ x μ; simp only [Pi.neg_apply]; rw [abs_sub_comm]; rwa [show -φ x - -φ (periodicLatticeShift x μ)
      = φ (periodicLatticeShift x μ) - φ x by ring] at *
  have hem : ‖um - u‖ ≤ Real.sqrt 3 * (Real.exp θ' - 1) * ‖f‖ := by
    have := grad_conj_err U (-φ) θ' hφ' f
    simpa using this
  have hgrad : ⟪f, siteWt φ (lapFull U (siteWt (-φ) f))⟫ = ⟪um, up⟫ := lap_conj_pair U φ f
  have hpl := pair_lower u up um
  set εD := Real.sqrt 3 * (Real.exp θ' - 1) * ‖f‖ with hεD
  have hεD0 : 0 ≤ εD := by positivity
  have hεD2 : εD ^ 2 = 3 * (Real.exp θ' - 1) ^ 2 * ‖f‖ ^ 2 := by
    rw [hεD, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  have hgrad_lb : (1 / 2) * ‖u‖ ^ 2 - 3 * εD ^ 2 ≤ ⟪um, up⟫ := by
    have h1 : ‖u‖ * (‖up - u‖ + ‖um - u‖) ≤ ‖u‖ * (2 * εD) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
    have h2 : ‖up - u‖ * ‖um - u‖ ≤ εD * εD :=
      mul_le_mul hep hem (norm_nonneg _) hεD0
    nlinarith [sq_nonneg (‖u‖ - 2 * εD), norm_nonneg u, hpl, h1, h2]
  -- mass part
  have hmass : ⟪f, siteWt φ (Qpa G U a (siteWt (-φ) f))⟫
      = ∑ y : PeriodicLatticeSite L, if y ∈ G.Lam G.k then (ajSeq a G.ell G.k * (G.ell : ℝ) ^ G.k) *
          ⟪Qlev G U G.k y (siteWt φ f), Qlev G U G.k y (siteWt (-φ) f)⟫ else 0 := by
    rw [Qpa_conj_inner, Finset.sum_range_succ]
    have hz : ∑ j ∈ Finset.range G.k, ∑ y : PeriodicLatticeSite L,
        (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) *
          ⟪Qlev G U j y (siteWt φ f), Qlev G U j y (siteWt (-φ) f)⟫ else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
      rw [if_neg (hLlt j (Finset.mem_range.mp hj) y)]
    rw [hz, zero_add]
  have hmass0 : ⟪f, Qpa G U a f⟫
      = ∑ y : PeriodicLatticeSite L, if y ∈ G.Lam G.k then (ajSeq a G.ell G.k * (G.ell : ℝ) ^ G.k) *
          ‖Qlev G U G.k y f‖ ^ 2 else 0 := by
    rw [inner_Qpa, Finset.sum_range_succ]
    have hz : ∑ j ∈ Finset.range G.k, ∑ y : PeriodicLatticeSite L,
        (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G U j y f‖ ^ 2 else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun y _ => ?_))
      rw [if_neg (hLlt j (Finset.mem_range.mp hj) y)]
    rw [hz, zero_add]
  rw [hmass, hmass0]
  set m := ajSeq a G.ell G.k * (G.ell : ℝ) ^ G.k with hm
  have hm0 : 0 ≤ m := mul_nonneg ha (by positivity)
  set w := (1 / (G.ell : ℝ) ^ 3) ^ G.k with hw
  have hw0 : 0 ≤ w := by positivity
  -- per block
  have hblock : ∀ y : PeriodicLatticeSite L, y ∈ G.Lam G.k →
      (1 / 2) * (m * ‖Qlev G U G.k y f‖ ^ 2) - 3 * m * w * (Real.exp δ - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2
        ≤ m * ⟪Qlev G U G.k y (siteWt φ f), Qlev G U G.k y (siteWt (-φ) f)⟫ := by
    intro y hy
    set ψ : PeriodicLatticeSite L → ℝ := fun x => φ x - φ y with hψ
    have e1 := Qlev_siteWt_shift G U G.k y φ (φ y) f
    rw [← hψ] at e1
    have e2 := Qlev_siteWt_shift G U G.k y (-φ) (-φ y) f
    have e3 : (fun x => (-φ) x - -φ y) = -ψ := by funext x; simp [hψ]; ring
    rw [e3] at e2
    have hinner : ⟪Qlev G U G.k y (siteWt φ f), Qlev G U G.k y (siteWt (-φ) f)⟫
        = ⟪Qlev G U G.k y (siteWt ψ f), Qlev G U G.k y (siteWt (-ψ) f)⟫ := by
      rw [e1, e2, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← Real.exp_add]
      simp
    rw [hinner]
    set v := Qlev G U G.k y f with hv
    set vp := Qlev G U G.k y (siteWt ψ f) with hvp
    set vm := Qlev G U G.k y (siteWt (-ψ) f) with hvm
    have hbψ : ∀ x ∈ boxF y (G.ell ^ G.k), |ψ x| ≤ δ := fun x hx => hbox y hy x hx
    have hbψ' : ∀ x ∈ boxF y (G.ell ^ G.k), |(-ψ) x| ≤ δ := fun x hx => by
      simpa [abs_neg] using hbψ x hx
    set S := ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have hdp := Qlev_err_sq G U hell G.k y ψ δ hbψ f
    have hdm := Qlev_err_sq G U hell G.k y (-ψ) δ hbψ' f
    set d := Real.sqrt (w * (Real.exp δ - 1) ^ 2 * S) with hd
    have hd2 : d ^ 2 = w * (Real.exp δ - 1) ^ 2 * S := Real.sq_sqrt (by positivity)
    have hdp' : ‖vp - v‖ ≤ d := by
      rw [hd]; apply Real.le_sqrt_of_sq_le; linarith
    have hdm' : ‖vm - v‖ ≤ d := by
      rw [hd]; apply Real.le_sqrt_of_sq_le; linarith
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hpl2 := pair_lower v vp vm
    have h1 : ‖v‖ * (‖vp - v‖ + ‖vm - v‖) ≤ ‖v‖ * (2 * d) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
    have h2 : ‖vp - v‖ * ‖vm - v‖ ≤ d * d := mul_le_mul hdp' hdm' (norm_nonneg _) hd0
    have hlow : (1 / 2) * ‖v‖ ^ 2 - 3 * d ^ 2 ≤ ⟪vm, vp⟫ := by
      nlinarith [sq_nonneg (‖v‖ - 2 * d), norm_nonneg v, hpl2, h1, h2]
    have hcomm : ⟪vp, vm⟫ = ⟪vm, vp⟫ := real_inner_comm _ _
    rw [hcomm]
    have := mul_le_mul_of_nonneg_left hlow hm0
    rw [hd2] at this
    nlinarith
  -- sum over blocks
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y (_ : y ∈ Finset.univ) =>
    (show (if y ∈ G.Lam G.k then (1 / 2) * (m * ‖Qlev G U G.k y f‖ ^ 2)
          - 3 * m * w * (Real.exp δ - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2 else 0)
        ≤ (if y ∈ G.Lam G.k then m * ⟪Qlev G U G.k y (siteWt φ f), Qlev G U G.k y (siteWt (-φ) f)⟫ else 0) by
      split_ifs with hy
      · exact hblock y hy
      · exact le_rfl))
  have hboxes := sum_boxes_le G hLk f
  have hsplitsum : ∑ y : PeriodicLatticeSite L, (if y ∈ G.Lam G.k then (1 / 2) * (m * ‖Qlev G U G.k y f‖ ^ 2)
          - 3 * m * w * (Real.exp δ - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2 else 0)
      = (1 / 2) * ∑ y : PeriodicLatticeSite L, (if y ∈ G.Lam G.k then m * ‖Qlev G U G.k y f‖ ^ 2 else 0)
        - 3 * m * w * (Real.exp δ - 1) ^ 2 *
          ∑ y : PeriodicLatticeSite L, (if y ∈ G.Lam G.k then ∑ x ∈ boxF y (G.ell ^ G.k), ‖f x‖ ^ 2 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs <;> ring
  rw [hsplitsum] at hsum
  have hmw : 0 ≤ 3 * m * w * (Real.exp δ - 1) ^ 2 := by positivity
  have hb2 := mul_le_mul_of_nonneg_left hboxes hmw
  rw [← hgrad] at hgrad_lb
  rw [hεD2] at hgrad_lb
  have hu2 : ‖u‖ ^ 2 = ‖gradL2 U f‖ ^ 2 := rfl
  linarith [hgrad_lb, hsum, hb2]

/-- **weighted bound of the genuine `G'`** (`Ω₀` = torus): if `Δ'_a` is a unit and `c‖f‖² ≤ ½⟪f,Δ'_a f⟫ − E_s‖f‖²`, then
`c ‖e^φ G' e^{−φ} g‖ ≤ ‖g‖`. -/
theorem siteCT_inv (G : TowerGeom L) (hOm : G.Om0 = Set.univ) (U : Cfg L) (a : ℝ)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (φ : PeriodicLatticeSite L → ℝ) (c Es : ℝ) (hc : 0 < c)
    (hform : ∀ f, (1 / 2) * ⟪f, DelpA G U a f⟫ - Es * ‖f‖ ^ 2 ≤ ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫)
    (hcoer : ∀ f, c * ‖f‖ ^ 2 ≤ (1 / 2) * ⟪f, DelpA G U a f⟫ - Es * ‖f‖ ^ 2) (g : SiteL2 L) :
    c * ‖siteWt φ (Gp G U a (siteWt (-φ) g))‖ ≤ ‖g‖ := by
  set h := siteWt φ (Gp G U a (siteWt (-φ) g)) with hh
  have hspec := Gp_spec G U a hu (siteWt (-φ) g)
  have hmask : ∀ v : SiteL2 L, siteMask G.Om0 v = v := fun v => by rw [hOm]; exact siteMask_univ v
  have hL : siteWt φ (DelpA G U a (siteWt (-φ) h)) = g := by
    rw [hh, siteWt_cancel_neg, hspec.2, hmask, siteWt_neg_cancel]
  have h1 := (hform h).trans' (hcoer h)
  rw [hL] at h1
  have h2 : ⟪h, g⟫ ≤ ‖h‖ * ‖g‖ := real_inner_le_norm h g
  by_cases h0 : ‖h‖ = 0
  · rw [h0]; simp
  have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have : c * ‖h‖ * ‖h‖ ≤ ‖g‖ * ‖h‖ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

#print axioms siteMask_univ
#print axioms DelpA_univ
#print axioms Qpa_conj_inner
#print axioms Qlev_siteWt_shift
#print axioms Qlev_err_sq
#print axioms sum_boxes_le
#print axioms siteCT_form
#print axioms siteCT_inv

end AdalyFormal.DLayer

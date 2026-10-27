import MS2

/-!
# MS3 -- S2 (PLAN.md §1.2 Layer S): stratum-adapted site Combes–Thomas for `Δ'_a` at a GENERAL tower

DL8 `siteCT_form` needs `Ω₀ = univ`, `Λ_j = ∅` for `j < k` and ONE Lipschitz constant `θ'`.  Here:
* `siteCT_gen` (any `TowerGeom`, Dirichlet mask, every level `j ≤ k`): for a weight `φ` with a PER-BOND bound
  `|φ(b₋) − φ(b₊)| ≤ Θ b` and PER-LEVEL block oscillation `|φ x − φ y| ≤ δ_j` on `box(y, ℓ^j)`, `y ∈ Λ_j`,
  `½⟪f,Δ'_a f⟫ − Err ≤ ⟪f, e^φ Δ'_a e^{−φ} f⟫` with
  `Err = 3 Σ_b (e^{Θ b} − 1)² ‖(Ω₀f)(b₊)‖² + Σ_{j,y∈Λ_j} 3 a_jℓ^j ℓ^{−3j}(e^{δ_j} − 1)² Σ_{box(y,ℓ^j)} ‖Ω₀f‖²`.
* **`siteCT_strat`** (ProperTower, the stratum weights): if `Θ b ≤ θ/ℓ^{stratG b₊}` for every bond with head in `Ω₀` and
  `δ_j ≤ δ`, then `Err ≤ (9(e^θ − 1)² + 3a(e^δ − 1)²) · wNormSq G f` — the error is in the S1 weighted norm, so S1 absorbs it.
* **`siteCT_inv_strat`**: with S1, `c·wNormSq(e^φ G' e^{−φ} g) ≤ ⟪e^φ G' e^{−φ} g, g⟫` for `c = c_s/2 − E`, and the weighted
  Cauchy–Schwarz form `c² · wNormSq h ≤ dualNormSq G g`, `dualNormSq G g = Σ_{x ∈ Ω₀} ℓ^{2 strat x}‖g x‖²`.
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
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.QjComposite (Qcomposite)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2)

variable {L : PeriodicLatticeExtent}

/-! ## 1. small facts -/

theorem siteWt_mask (φ : PeriodicLatticeSite L → ℝ) (S : Set (PeriodicLatticeSite L)) (f : SiteL2 L) :
    siteWt φ (siteMask S f) = siteMask S (siteWt φ f) := by
  classical
  refine PiLp.ext (fun x => ?_)
  rw [siteWt_apply, siteMask_apply, siteMask_apply, siteWt_apply]
  split_ifs <;> simp

theorem boxF_eq_blockOf (y : PeriodicLatticeSite L) (m : ℕ) : boxF y m = blockOf y m := by
  ext x; rw [mem_boxF, mem_blockOf]

theorem sum_head_eq (ψ : PeriodicLatticeSite L → ℝ) :
    ∑ b : Bond L, ψ (periodicLatticeShift b.1 b.2) = 3 * ∑ x, ψ x := by
  rw [Fintype.sum_prod_type_right]
  have hshift : ∀ μ : Fin 3, ∑ x : PeriodicLatticeSite L, ψ (periodicLatticeShift x μ) = ∑ x, ψ x := by
    intro μ
    exact Function.Bijective.sum_comp (Function.Injective.bijective_of_finite (shift_injective μ)) ψ
  simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- `n (e^{t/n} − 1) ≤ e^t − 1` (Bernoulli), `t ≥ 0`, `n ≥ 1` natural -/
theorem exp_div_sub_one_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (t / n) - 1 ≤ (Real.exp t - 1) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 ≤ Real.exp (t / n) - 1 := by
    have := Real.add_one_le_exp (t / n); have : 0 ≤ t / n := div_nonneg ht hn'.le; linarith
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ Real.exp (t / n) - 1 by linarith) n
  have e : (1 + (Real.exp (t / n) - 1)) ^ n = Real.exp t := by
    rw [add_sub_cancel, ← Real.exp_nat_mul]; congr 1; field_simp
  rw [e] at hb
  rw [le_div_iff₀ hn']
  linarith

theorem ajSeq_le (ell j : ℕ) (hell : 2 ≤ ell) {a : ℝ} (ha : 0 < a) : ajSeq a ell j ≤ a := by
  unfold ajSeq
  split_ifs
  · exact le_rfl
  · have hℓ : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ (by positivity)]
      have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
      nlinarith
    exact (AdalyFormal.Balaban.ConstantA.aSeqAux_invariant a _ ha hd hda (j - 1)).2

/-! ## 2. per-row mass commutator (DL8 `hblock`, any level `j`) -/

theorem row_conj_lower (G : TowerGeom L) (U : Cfg L) (hell : 0 < G.ell) (j : ℕ) (y : PeriodicLatticeSite L)
    (φ : PeriodicLatticeSite L → ℝ) (δ m : ℝ) (hm0 : 0 ≤ m)
    (hbox : ∀ x ∈ boxF y (G.ell ^ j), |φ x - φ y| ≤ δ) (f : SiteL2 L) :
    (1 / 2) * (m * ‖Qlev G U j y f‖ ^ 2)
        - 3 * m * ((1 / (G.ell : ℝ) ^ 3) ^ j) * (Real.exp δ - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖f x‖ ^ 2
      ≤ m * ⟪Qlev G U j y (siteWt φ f), Qlev G U j y (siteWt (-φ) f)⟫ := by
  set w := (1 / (G.ell : ℝ) ^ 3) ^ j with hw
  have hw0 : 0 ≤ w := by positivity
  set ψ : PeriodicLatticeSite L → ℝ := fun x => φ x - φ y with hψ
  have e1 := Qlev_siteWt_shift G U j y φ (φ y) f
  rw [← hψ] at e1
  have e2 := Qlev_siteWt_shift G U j y (-φ) (-φ y) f
  have e3 : (fun x => (-φ) x - -φ y) = -ψ := by funext x; simp [hψ]; ring
  rw [e3] at e2
  have hinner : ⟪Qlev G U j y (siteWt φ f), Qlev G U j y (siteWt (-φ) f)⟫
      = ⟪Qlev G U j y (siteWt ψ f), Qlev G U j y (siteWt (-ψ) f)⟫ := by
    rw [e1, e2, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← Real.exp_add]
    simp
  rw [hinner]
  set v := Qlev G U j y f with hv
  set vp := Qlev G U j y (siteWt ψ f) with hvp
  set vm := Qlev G U j y (siteWt (-ψ) f) with hvm
  have hbψ : ∀ x ∈ boxF y (G.ell ^ j), |ψ x| ≤ δ := fun x hx => hbox x hx
  have hbψ' : ∀ x ∈ boxF y (G.ell ^ j), |(-ψ) x| ≤ δ := fun x hx => by
    simpa [abs_neg] using hbψ x hx
  set S := ∑ x ∈ boxF y (G.ell ^ j), ‖f x‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hdp := Qlev_err_sq G U hell j y ψ δ hbψ f
  have hdm := Qlev_err_sq G U hell j y (-ψ) δ hbψ' f
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

/-! ## 3. the general stratified CT form -/

open Classical in
/-- the CT error of `siteCT_gen` -/
noncomputable def ctErr (G : TowerGeom L) (a : ℝ) (Θ : Bond L → ℝ) (δ : ℕ → ℝ) (f : SiteL2 L) : ℝ :=
  3 * ∑ b : Bond L, (Real.exp (Θ b) - 1) ^ 2 * ‖siteMask G.Om0 f (periodicLatticeShift b.1 b.2)‖ ^ 2
  + ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j)
        * (Real.exp (δ j) - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖siteMask G.Om0 f x‖ ^ 2 else 0

theorem siteCT_gen (G : TowerGeom L) (hell : 0 < G.ell) (U : Cfg L) (a : ℝ)
    (ha : ∀ j, 0 ≤ ajSeq a G.ell j)
    (φ : PeriodicLatticeSite L → ℝ) (Θ : Bond L → ℝ)
    (hφ : ∀ b : Bond L, |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ Θ b)
    (δ : ℕ → ℝ) (hbox : ∀ j, j ≤ G.k → ∀ y ∈ G.Lam j, ∀ x ∈ boxF y (G.ell ^ j), |φ x - φ y| ≤ δ j)
    (f : SiteL2 L) :
    (1 / 2) * ⟪f, DelpA G U a f⟫ - ctErr G a Θ δ f ≤ ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫ := by
  classical
  set g := siteMask G.Om0 f with hg
  -- reduce to `g` and `lapFull + Qpa`
  have hred : ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫
      = ⟪g, siteWt φ (lapFull U (siteWt (-φ) g))⟫ + ⟪g, siteWt φ (Qpa G U a (siteWt (-φ) g))⟫ := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply]
    rw [← siteWt_symm, ← siteMask_symm, ← siteWt_mask, siteWt_symm, siteWt_mask, ← hg,
      ContinuousLinearMap.add_apply, map_add, inner_add_right]
  have hred0 : ⟪f, DelpA G U a f⟫ = ‖gradL2 U g‖ ^ 2 + ⟪g, Qpa G U a g⟫ := by
    unfold DelpA
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← siteMask_symm,
      ContinuousLinearMap.add_apply, inner_add_right, inner_lapFull]
  rw [hred, hred0]
  -- gradient part
  set u := gradL2 U g with hu
  set up := bondWt φ (gradL2 U (siteWt (-φ) g)) with hup
  set um := bondWt (-φ) (gradL2 U (siteWt φ g)) with hum
  set εD := Real.sqrt (∑ b : Bond L, (Real.exp (Θ b) - 1) ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2) with hεD
  have hεD2 : εD ^ 2 = ∑ b : Bond L, (Real.exp (Θ b) - 1) ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun b _ => by positivity))
  have herr : ∀ ψ : PeriodicLatticeSite L → ℝ, (∀ b : Bond L, |ψ b.1 - ψ (periodicLatticeShift b.1 b.2)| ≤ Θ b) →
      ‖bondWt ψ (gradL2 U (siteWt (-ψ) g)) - gradL2 U g‖ ≤ εD := by
    intro ψ hψ
    rw [hεD]
    apply Real.le_sqrt_of_sq_le
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rw [grad_conj_sub, norm_smul, Real.norm_eq_abs, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 := abs_exp_sub_one_le_of _ _ (hψ b)
    calc |Real.exp (ψ b.1 - ψ (periodicLatticeShift b.1 b.2)) - 1| ^ 2
        ≤ (Real.exp (Θ b) - 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := rfl
  have hep : ‖up - u‖ ≤ εD := herr φ hφ
  have hem : ‖um - u‖ ≤ εD := by
    have := herr (-φ) (fun b => by
      have := hφ b; simp only [Pi.neg_apply]; rw [abs_sub_comm]
      rwa [show -φ (periodicLatticeShift b.1 b.2) - -φ b.1 = φ b.1 - φ (periodicLatticeShift b.1 b.2) by ring])
    simpa using this
  have hgrad : ⟪g, siteWt φ (lapFull U (siteWt (-φ) g))⟫ = ⟪um, up⟫ := lap_conj_pair U φ g
  have hpl := pair_lower u up um
  have hεD0 : 0 ≤ εD := Real.sqrt_nonneg _
  have hgrad_lb : (1 / 2) * ‖u‖ ^ 2 - 3 * εD ^ 2 ≤ ⟪um, up⟫ := by
    have h1 : ‖u‖ * (‖up - u‖ + ‖um - u‖) ≤ ‖u‖ * (2 * εD) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
    have h2 : ‖up - u‖ * ‖um - u‖ ≤ εD * εD :=
      mul_le_mul hep hem (norm_nonneg _) hεD0
    nlinarith [sq_nonneg (‖u‖ - 2 * εD), norm_nonneg u, hpl, h1, h2]
  -- mass part
  rw [Qpa_conj_inner, inner_Qpa]
  have hrow : ∀ j ∈ Finset.range (G.k + 1), ∀ y : PeriodicLatticeSite L,
      (if y ∈ G.Lam j then (1 / 2) * ((ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G U j y g‖ ^ 2)
          - 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j) * (Real.exp (δ j) - 1) ^ 2
            * ∑ x ∈ boxF y (G.ell ^ j), ‖g x‖ ^ 2 else 0)
        ≤ (if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) *
            ⟪Qlev G U j y (siteWt φ g), Qlev G U j y (siteWt (-φ) g)⟫ else 0) := by
    intro j hj y
    split_ifs with hy
    · have hjk : j ≤ G.k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact row_conj_lower G U hell j y φ (δ j) _ (mul_nonneg (ha j) (by positivity))
        (hbox j hjk y hy) g
    · exact le_rfl
  have hsum := Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hrow j hj y))
  have hsplit : ∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      (if y ∈ G.Lam j then (1 / 2) * ((ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G U j y g‖ ^ 2)
          - 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j) * (Real.exp (δ j) - 1) ^ 2
            * ∑ x ∈ boxF y (G.ell ^ j), ‖g x‖ ^ 2 else 0)
      = (1 / 2) * (∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
          if y ∈ G.Lam j then (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ‖Qlev G U j y g‖ ^ 2 else 0)
        - (∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
          if y ∈ G.Lam j then 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j)
            * (Real.exp (δ j) - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖g x‖ ^ 2 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs <;> ring
  rw [hsplit] at hsum
  rw [← hgrad] at hgrad_lb
  have hE : ctErr G a Θ δ f = 3 * εD ^ 2 + (∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
          if y ∈ G.Lam j then 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j)
            * (Real.exp (δ j) - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖g x‖ ^ 2 else 0) := by
    rw [hεD2]; rfl
  rw [hE]
  have hu2 : ‖u‖ ^ 2 = ‖gradL2 U g‖ ^ 2 := rfl
  linarith [hgrad_lb, hsum]

/-! ## 4. the stratum weights -/

theorem ctErr_le_wNorm (ell k : ℕ) (hell : 2 ≤ ell) {G : TowerGeom L} (hP : ProperTower G ell k)
    (a : ℝ) (ha : 0 < a) (θ δ0 : ℝ) (hθ : 0 ≤ θ) (hδ0 : 0 ≤ δ0)
    (Θ : Bond L → ℝ) (hΘ0 : ∀ b, 0 ≤ Θ b)
    (hΘ : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      Θ b ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2))
    (δ : ℕ → ℝ) (hδp : ∀ j, 0 ≤ δ j) (hδ : ∀ j, δ j ≤ δ0) (f : SiteL2 L) :
    ctErr G a Θ δ f ≤ (9 * (Real.exp θ - 1) ^ 2 + 3 * a * (Real.exp δ0 - 1) ^ 2) * wNormSq G f := by
  classical
  have hell0 : 0 < ell := by omega
  set g := siteMask G.Om0 f with hg
  have hw : ∀ x, ‖g x‖ ^ 2 / ((ell : ℝ) ^ stratG G x) ^ 2 = ‖siteMask G.Om0 f x‖ ^ 2 / ((G.ell : ℝ) ^ stratG G x) ^ 2 := by
    intro x; rw [hP.ell_eq]
  have hE1 : 0 ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
  -- gradient part
  have hgr : 3 * ∑ b : Bond L, (Real.exp (Θ b) - 1) ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2
      ≤ 9 * (Real.exp θ - 1) ^ 2 * wNormSq G f := by
    have hpt : ∀ b : Bond L, (Real.exp (Θ b) - 1) ^ 2 * ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2
        ≤ (Real.exp θ - 1) ^ 2 * (‖g (periodicLatticeShift b.1 b.2)‖ ^ 2
            / ((ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2)) ^ 2) := by
      intro b
      set x := periodicLatticeShift b.1 b.2
      by_cases hx : x ∈ G.Om0
      · set n : ℕ := ell ^ stratG G x with hn
        have hn1 : 1 ≤ n := Nat.one_le_pow _ _ hell0
        have hnR : ((n : ℕ) : ℝ) = (ell : ℝ) ^ stratG G x := by rw [hn]; push_cast; rfl
        have hnpos : (0 : ℝ) < (ell : ℝ) ^ stratG G x := by positivity
        have h1 : Real.exp (Θ b) - 1 ≤ (Real.exp θ - 1) / (ell : ℝ) ^ stratG G x := by
          have hb := hΘ b hx
          have h2 : Real.exp (Θ b) ≤ Real.exp (θ / (n : ℝ)) := by rw [hnR]; exact Real.exp_le_exp.mpr hb
          have h3 := exp_div_sub_one_le θ hθ n hn1
          rw [hnR] at h2 h3
          linarith
        have h0 : 0 ≤ Real.exp (Θ b) - 1 := by linarith [Real.add_one_le_exp (Θ b), hΘ0 b]
        have h4 : (Real.exp (Θ b) - 1) ^ 2 ≤ ((Real.exp θ - 1) / (ell : ℝ) ^ stratG G x) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
        rw [div_pow] at h4
        have := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖g x‖)
        calc _ ≤ (Real.exp θ - 1) ^ 2 / ((ell : ℝ) ^ stratG G x) ^ 2 * ‖g x‖ ^ 2 := this
          _ = _ := by ring
      · rw [hg, siteMask_off _ _ _ hx]; simp
    have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpt b)
    rw [← Finset.mul_sum, sum_head_eq (fun x => ‖g x‖ ^ 2 / ((ell : ℝ) ^ stratG G x) ^ 2)] at hs
    have hW : ∑ x, ‖g x‖ ^ 2 / ((ell : ℝ) ^ stratG G x) ^ 2 = wNormSq G f := by
      unfold wNormSq; exact Finset.sum_congr rfl (fun x _ => hw x)
    rw [hW] at hs
    nlinarith [hs]
  -- mass part
  have hms : (∑ j ∈ Finset.range (G.k + 1), ∑ y : PeriodicLatticeSite L,
      if y ∈ G.Lam j then 3 * (ajSeq a G.ell j * (G.ell : ℝ) ^ j) * ((1 / (G.ell : ℝ) ^ 3) ^ j)
        * (Real.exp (δ j) - 1) ^ 2 * ∑ x ∈ boxF y (G.ell ^ j), ‖g x‖ ^ 2 else 0)
      ≤ 3 * a * (Real.exp δ0 - 1) ^ 2 * wNormSq G f := by
    rw [wNormSq_blocks hP, Finset.mul_sum, hP.k_eq, hP.ell_eq]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mul_sum, ← Finset.sum_filter]
    have hLF : Finset.univ.filter (fun y => y ∈ G.Lam j) = LamF G j := by ext y; simp [LamF]
    rw [hLF]
    refine Finset.sum_le_sum (fun y hy => ?_)
    rw [boxF_eq_blockOf]
    set S := ∑ x ∈ blockOf y (ell ^ j), ‖g x‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have hSdiv : ∑ x ∈ blockOf y (ell ^ j), ‖siteMask G.Om0 f x‖ ^ 2 / ((ell : ℝ) ^ j) ^ 2 = S / ((ell : ℝ) ^ j) ^ 2 := by
      rw [hS, Finset.sum_div]
    rw [hSdiv]
    have hnj : 0 < (ell : ℝ) ^ j := by positivity
    have hcube : (ell : ℝ) ^ j * (1 / (ell : ℝ) ^ 3) ^ j = 1 / ((ell : ℝ) ^ j) ^ 2 := by
      have e3 : ((ell : ℝ) ^ 3) ^ j = ((ell : ℝ) ^ j) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [one_div_pow, e3]
      field_simp
    have hδe : (Real.exp (δ j) - 1) ^ 2 ≤ (Real.exp δ0 - 1) ^ 2 := by
      have hexp : Real.exp (δ j) ≤ Real.exp δ0 := Real.exp_le_exp.mpr (hδ j)
      have h0 : 0 ≤ Real.exp (δ j) - 1 := by linarith [Real.add_one_le_exp (δ j), hδp j]
      exact pow_le_pow_left₀ h0 (by linarith) 2
    have haj := ajSeq_le ell j hell ha
    have haj0 : 0 ≤ ajSeq a ell j := by linarith [ajSeq_ge ell j hell ha]
    have hSn : 0 ≤ S / ((ell : ℝ) ^ j) ^ 2 := div_nonneg hS0 (sq_nonneg _)
    have hprod : ajSeq a ell j * (Real.exp (δ j) - 1) ^ 2 ≤ a * (Real.exp δ0 - 1) ^ 2 :=
      mul_le_mul haj hδe (sq_nonneg _) ha.le
    have hL : 3 * (ajSeq a ell j * (ell : ℝ) ^ j) * ((1 / (ell : ℝ) ^ 3) ^ j) * (Real.exp (δ j) - 1) ^ 2 * S
        = 3 * (ajSeq a ell j * (Real.exp (δ j) - 1) ^ 2) * (S / ((ell : ℝ) ^ j) ^ 2) := by
      rw [div_eq_mul_one_div S, ← hcube]; ring
    rw [hL]
    have := mul_le_mul_of_nonneg_right hprod (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hSn)
    nlinarith [this]
  unfold ctErr
  rw [← hg]
  linarith [hgr, hms]

/-- **S2 `siteCT_strat`**: stratum-adapted site Combes–Thomas form, error in the S1 weighted norm. -/
theorem siteCT_strat (ell k : ℕ) (hell : 2 ≤ ell) {G : TowerGeom L} (hP : ProperTower G ell k)
    (U : Cfg L) (a : ℝ) (ha : 0 < a) (φ : PeriodicLatticeSite L → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hφ : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2))
    (δ0 : ℝ) (hδ0 : 0 ≤ δ0)
    (hbox : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ x ∈ blockOf y (ell ^ j), |φ x - φ y| ≤ δ0)
    (f : SiteL2 L) :
    (1 / 2) * ⟪f, DelpA G U a f⟫ - (9 * (Real.exp θ - 1) ^ 2 + 3 * a * (Real.exp δ0 - 1) ^ 2) * wNormSq G f
      ≤ ⟪f, siteWt φ (DelpA G U a (siteWt (-φ) f))⟫ := by
  classical
  have hell0 : 0 < ell := by omega
  set Θ : Bond L → ℝ := fun b => if periodicLatticeShift b.1 b.2 ∈ G.Om0 then
      θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2) else |φ b.1 - φ (periodicLatticeShift b.1 b.2)| with hΘd
  have hΘφ : ∀ b : Bond L, |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ Θ b := by
    intro b
    simp only [hΘd]
    split_ifs with h
    · exact hφ b h
    · exact le_rfl
  have hΘ0 : ∀ b, 0 ≤ Θ b := fun b => (abs_nonneg _).trans (hΘφ b)
  have hΘ : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      Θ b ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2) := by
    intro b hb; simp only [hΘd, if_pos hb]; exact le_rfl
  have hgen := siteCT_gen G (by rw [hP.ell_eq]; exact hell0) U a
    (fun j => by have := ajSeq_ge G.ell j (by rw [hP.ell_eq]; exact hell) ha; linarith)
    φ Θ hΘφ (fun _ => δ0)
    (by
      intro j hj y hy x hx
      rw [hP.ell_eq, boxF_eq_blockOf] at hx
      exact hbox j (by rw [← hP.k_eq]; exact hj) y hy x hx) f
  have herr := ctErr_le_wNorm ell k hell hP a ha θ δ0 hθ hδ0 Θ hΘ0 hΘ (fun _ => δ0) (fun _ => hδ0) (fun _ => le_rfl) f
  linarith [hgen, herr]

/-- the dual weighted norm `Σ_{x} ℓ^{2 strat x} ‖(Ω₀ g)(x)‖²` -/
noncomputable def dualNormSq (G : TowerGeom L) (g : SiteL2 L) : ℝ :=
  ∑ x, ‖siteMask G.Om0 g x‖ ^ 2 * ((G.ell : ℝ) ^ stratG G x) ^ 2

/-- weighted Cauchy–Schwarz: `⟪h, Ω₀ g⟫² ≤ wNormSq h · dualNormSq g` -/
theorem inner_mask_sq_le (G : TowerGeom L) (hell : 0 < G.ell) (h g : SiteL2 L) :
    ⟪h, siteMask G.Om0 g⟫ ^ 2 ≤ wNormSq G h * dualNormSq G g := by
  classical
  set n : PeriodicLatticeSite L → ℝ := fun x => (G.ell : ℝ) ^ stratG G x with hn
  have hnpos : ∀ x, 0 < n x := fun x => by simp only [hn]; positivity
  have hpt : ∀ x, ⟪h x, siteMask G.Om0 g x⟫
      ≤ (‖siteMask G.Om0 h x‖ / n x) * (‖siteMask G.Om0 g x‖ * n x) := by
    intro x
    by_cases hx : x ∈ G.Om0
    · rw [siteMask_on _ _ _ hx, siteMask_on _ _ _ hx]
      have e : ‖h x‖ / n x * (‖g x‖ * n x) = ‖h x‖ * ‖g x‖ := by field_simp [(hnpos x).ne']
      rw [e]; exact real_inner_le_norm _ _
    · rw [siteMask_off _ _ _ hx, siteMask_off _ _ _ hx]; simp
  have h1 : ⟪h, siteMask G.Om0 g⟫ ≤ ∑ x, (‖siteMask G.Om0 h x‖ / n x) * (‖siteMask G.Om0 g x‖ * n x) := by
    rw [PiLp.inner_apply]; exact Finset.sum_le_sum (fun x _ => hpt x)
  have h1' : -⟪h, siteMask G.Om0 g⟫ ≤ ∑ x, (‖siteMask G.Om0 h x‖ / n x) * (‖siteMask G.Om0 g x‖ * n x) := by
    have := (show ∀ x, -⟪h x, siteMask G.Om0 g x⟫
        ≤ (‖siteMask G.Om0 h x‖ / n x) * (‖siteMask G.Om0 g x‖ * n x) from fun x => by
      have := hpt x
      by_cases hx : x ∈ G.Om0
      · rw [siteMask_on _ _ _ hx, siteMask_on _ _ _ hx]
        have e : ‖h x‖ / n x * (‖g x‖ * n x) = ‖h x‖ * ‖g x‖ := by field_simp [(hnpos x).ne']
        rw [e]
        have := abs_real_inner_le_norm (h x) (g x)
        linarith [neg_abs_le (⟪h x, g x⟫)]
      · rw [siteMask_off _ _ _ hx, siteMask_off _ _ _ hx]; simp)
    rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]; exact Finset.sum_le_sum (fun x _ => this x)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun x => ‖siteMask G.Om0 h x‖ / n x)
    (fun x => ‖siteMask G.Om0 g x‖ * n x)
  have hW : ∑ x, (‖siteMask G.Om0 h x‖ / n x) ^ 2 = wNormSq G h := by
    unfold wNormSq; refine Finset.sum_congr rfl (fun x _ => ?_); rw [div_pow]
  have hD : ∑ x, (‖siteMask G.Om0 g x‖ * n x) ^ 2 = dualNormSq G g := by
    unfold dualNormSq; refine Finset.sum_congr rfl (fun x _ => ?_); rw [mul_pow]
  rw [hW, hD] at hcs
  set P := ∑ x, (‖siteMask G.Om0 h x‖ / n x) * (‖siteMask G.Om0 g x‖ * n x)
  have habs : |⟪h, siteMask G.Om0 g⟫| ≤ P := abs_le.mpr ⟨by linarith, h1⟩
  have hP0 : 0 ≤ P := (abs_nonneg _).trans habs
  calc ⟪h, siteMask G.Om0 g⟫ ^ 2 = |⟪h, siteMask G.Om0 g⟫| ^ 2 := (sq_abs _).symm
    _ ≤ P ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := hcs

/-- **S2 `siteCT_inv_strat`**: weighted bound for the conjugated `G'`, from S1 + `siteCT_strat`. -/
theorem siteCT_inv_strat (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (a : ℝ) (ha : 0 < a) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hU : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ b ∈ inBlockBonds y (ell ^ j),
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ ρ / (ell : ℝ) ^ j)
    (hT : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ i, i < j → ∀ z ∈ blockOf y (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ j) →
      AdalyFormal.Balaban.RMapLipschitz.frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ρ * (ell : ℝ) ^ i / (ell : ℝ) ^ j)
    (hu : IsUnit (DelpA G U a + (1 - siteMask G.Om0)))
    (φ : PeriodicLatticeSite L → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hφ : ∀ b : Bond L, periodicLatticeShift b.1 b.2 ∈ G.Om0 →
      |φ b.1 - φ (periodicLatticeShift b.1 b.2)| ≤ θ / (ell : ℝ) ^ stratG G (periodicLatticeShift b.1 b.2))
    (δ0 : ℝ) (hδ0 : 0 ≤ δ0)
    (hbox : ∀ j, j ≤ k → ∀ y ∈ G.Lam j, ∀ x ∈ blockOf y (ell ^ j), |φ x - φ y| ≤ δ0)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ (1 / 2) * ((1 - 216 * ρ ^ 2) / max 6 (16 / (3 * a)))
      - (9 * (Real.exp θ - 1) ^ 2 + 3 * a * (Real.exp δ0 - 1) ^ 2))
    (g : SiteL2 L) :
    c * wNormSq G (siteWt φ (Gp G U a (siteWt (-φ) g))) ≤ ⟪siteWt φ (Gp G U a (siteWt (-φ) g)), siteMask G.Om0 g⟫
    ∧ c ^ 2 * wNormSq G (siteWt φ (Gp G U a (siteWt (-φ) g))) ≤ dualNormSq G g := by
  set h := siteWt φ (Gp G U a (siteWt (-φ) g)) with hh
  have hm6 : 0 < max 6 (16 / (3 * a)) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hS1 := site_coercive_weighted ell k hell hdvd hP U a ha ρ hρ hU hT h
  have hS1' : ((1 - 216 * ρ ^ 2) / max 6 (16 / (3 * a))) * wNormSq G h ≤ ⟪h, DelpA G U a h⟫ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm6]; linarith
  have hCT := siteCT_strat ell k hell hP U a ha φ θ hθ hφ δ0 hδ0 hbox h
  have hspec := Gp_spec G U a hu (siteWt (-φ) g)
  have hL : siteWt φ (DelpA G U a (siteWt (-φ) h)) = siteMask G.Om0 g := by
    rw [hh, siteWt_cancel_neg, hspec.2, ← siteWt_mask, siteWt_neg_cancel]
  rw [hL] at hCT
  have hW0 := wNormSq_nonneg G h
  have h1 : c * wNormSq G h ≤ ⟪h, siteMask G.Om0 g⟫ := by
    have := mul_le_mul_of_nonneg_right hc hW0
    nlinarith [hS1', hCT, this]
  refine ⟨h1, ?_⟩
  have hcs := inner_mask_sq_le G (by rw [hP.ell_eq]; omega) h g
  have h2 : (c * wNormSq G h) ^ 2 ≤ wNormSq G h * dualNormSq G g := by
    have hcw : 0 ≤ c * wNormSq G h := mul_nonneg hc0 hW0
    exact (pow_le_pow_left₀ hcw h1 2).trans hcs
  rcases hW0.lt_or_eq with hpos | hzero
  · have : c ^ 2 * wNormSq G h * wNormSq G h ≤ dualNormSq G g * wNormSq G h := by nlinarith [h2]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero, mul_zero]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

#print axioms siteWt_mask
#print axioms boxF_eq_blockOf
#print axioms sum_head_eq
#print axioms exp_div_sub_one_le
#print axioms ajSeq_le
#print axioms row_conj_lower
#print axioms siteCT_gen
#print axioms ctErr_le_wNorm
#print axioms siteCT_strat
#print axioms inner_mask_sq_le
#print axioms siteCT_inv_strat

end AdalyFormal.M1Site

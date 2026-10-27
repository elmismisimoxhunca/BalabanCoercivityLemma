namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace ComplexConjugate
open Set Filter Topology
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)

/-! ### Entrywise real-analytic families of `2 × 2` complex matrices -/

/-- Every entry of the matrix family is real-analytic at every real parameter. -/
def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

theorem anM_const (M : Matrix (Fin 2) (Fin 2) ℂ) : AnM (fun _ => M) :=
  fun _ _ _ => analyticAt_const

/-- Real-analytic at every real parameter. -/
def AnR (g : ℝ → ℝ) : Prop := ∀ θ₀ : ℝ, AnalyticAt ℝ g θ₀

theorem anR_const (c : ℝ) : AnR (fun _ => c) := fun _ => analyticAt_const

theorem AnR.add {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ + g θ) :=
  fun θ₀ => (hf θ₀).fun_add (hg θ₀)

theorem AnR.sub {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ - g θ) :=
  fun θ₀ => (hf θ₀).fun_sub (hg θ₀)

theorem AnR.mul {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ * g θ) :=
  fun θ₀ => (hf θ₀).fun_mul (hg θ₀)

theorem AnR.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, AnR (f i)) :
    AnR (fun θ => ∑ i ∈ s, f i θ) :=
  fun θ₀ => Finset.analyticAt_fun_sum s (fun i hi => h i hi θ₀)

theorem AnM.add {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ + g θ) := by
  intro θ₀ i j
  simp only [Matrix.add_apply]
  exact (hf θ₀ i j).fun_add (hg θ₀ i j)

theorem AnM.sub {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ - g θ) := by
  intro θ₀ i j
  simp only [Matrix.sub_apply]
  exact (hf θ₀ i j).fun_sub (hg θ₀ i j)

theorem AnM.neg {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) : AnM (fun θ => -f θ) := by
  intro θ₀ i j
  simp only [Matrix.neg_apply]
  exact (hf θ₀ i j).fun_neg

theorem AnM.mul {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ * g θ) := by
  intro θ₀ i j
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun k _ => (hf θ₀ i k).fun_mul (hg θ₀ k j))

theorem AnM.smul {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (c : ℂ) :
    AnM (fun θ => c • f θ) := by
  intro θ₀ i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.fun_mul (hf θ₀ i j)

theorem AnM.star {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnM (fun θ => star (f θ)) := by
  intro θ₀ i j
  simp only [Matrix.star_apply]
  have h1 : AnalyticAt ℝ (fun θ => f θ j i) θ₀ := hf θ₀ j i
  have h2 : AnalyticAt ℝ (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((fun θ => f θ j i) θ₀) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => f θ j i) h2 h1
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]

/-- Real part of the trace of an analytic family is real-analytic. -/
theorem AnM.trace_re {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnR (fun θ => (Matrix.trace (f θ)).re) := by
  intro θ₀
  have htr : AnalyticAt ℝ (fun θ => Matrix.trace (f θ)) θ₀ := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.analyticAt_fun_sum _ (fun i _ => hf θ₀ i i)
  have h2 : AnalyticAt ℝ (Complex.reCLM : ℂ →L[ℝ] ℝ) ((fun θ => Matrix.trace (f θ)) θ₀) :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => Matrix.trace (f θ)) h2 htr
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]

theorem AnM.tr_re3 {f g h : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g)
    (hh : AnM h) : AnR (fun θ => (Matrix.trace (f θ * g θ * h θ)).re) :=
  ((hf.mul hg).mul hh).trace_re

/-- `θ ↦ exp(± i θ)` is real-analytic. -/
theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

/-! ### The Gram determinant: a polynomial certificate of invertibility -/

section Gram
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant of the matrix of `A` in the standard orthonormal basis. -/
noncomputable def gramDet (A : E →L[ℝ] E) : ℝ :=
  Matrix.det (Matrix.of fun i j =>
    ⟪stdOrthonormalBasis ℝ E i, A (stdOrthonormalBasis ℝ E j)⟫)

theorem gramDet_eq (A : E →L[ℝ] E) : gramDet A = LinearMap.det (A : E →ₗ[ℝ] E) := by
  rw [← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ E).toBasis]
  unfold gramDet
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  rfl

theorem isUnit_iff_gramDet (A : E →L[ℝ] E) : IsUnit A ↔ gramDet A ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    gramDet_eq, isUnit_iff_ne_zero]

/-- If every matrix coefficient of a path of operators is real-analytic, so is its
Gram determinant. -/
theorem analyticAt_gramDet {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ => gramDet (A θ)) θ₀ := by
  unfold gramDet
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.fun_mul ?_
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  simp only [Matrix.of_apply]
  exact h _ _ θ₀

/-- Isolated non-units: an analytic path of operators that is a unit at one parameter is a
unit on a punctured neighbourhood of EVERY parameter. -/
theorem isUnit_punctured {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀)
    {t₀ : ℝ} (hu : IsUnit (A t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s) := by
  set g : ℝ → ℝ := fun θ => gramDet (A θ) with hgdef
  have hg : AnalyticOnNhd ℝ g Set.univ := fun θ _ => analyticAt_gramDet h θ
  rcases (hg t (Set.mem_univ t)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ t) h0 (Set.mem_univ t₀)
    exact ((isUnit_iff_gramDet _).mp hu) hz
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨η, hη, hb⟩ := hne
    refine ⟨η, hη, fun s hs hst => (isUnit_iff_gramDet _).mpr (hb ?_ hs)⟩
    rw [Real.dist_eq]
    exact hst

end Gram

/-! ### The end of the initial positive semidefinite interval -/

section Edge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_le_opNorm (N : E →L[ℝ] E) (x : E) : |⟪x, N x⟫| ≤ ‖N‖ * ‖x‖ ^ 2 := by
  calc |⟪x, N x⟫| ≤ ‖x‖ * ‖N x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖N‖ * ‖x‖) := by gcongr; exact N.le_opNorm x
    _ = ‖N‖ * ‖x‖ ^ 2 := by ring

/-- A positive semidefinite unit is positive definite. -/
theorem pos_of_psd_unit (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (hu : IsUnit X) (x : E) (hx : x ≠ 0) : 0 < ⟪x, X x⟫ := by
  rcases (hp x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hk := psd_kernel X hs hp x h.symm
    have hinj : Function.Injective X := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    exact hx (hinj (by rw [hk, map_zero]))

/-- A positive definite operator is a unit. -/
theorem unit_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  have hi : Function.Injective X := (injective_iff_map_eq_zero X).mpr (by
    intro v hv
    by_contra hn
    have h := hpd v hn
    rw [hv, inner_zero_right] at h
    exact (lt_irrefl 0) h)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective (f := (show E →ₗ[ℝ] E from X))).mp hi⟩

omit [FiniteDimensional ℝ E] in
theorem psd_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro v
  by_cases hv : v = 0
  · rw [hv]; simp
  · exact (hpd v hv).le

/-- Positive definiteness is open along a continuous symmetric path. -/
theorem eventually_pd {A : ℝ → E →L[ℝ] E} (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ : ℝ)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t₀| < δ → ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A t₀) (hs t₀) (psd_of_pd _ hpd) (unit_of_pd _ hpd)
  have hct : ContinuousAt A t₀ := hc.continuousAt
  rw [Metric.continuousAt_iff] at hct
  obtain ⟨δ, hδ, hb⟩ := hct (m / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs' x hx => ?_⟩
  have hd : dist (A s) (A t₀) < m / 2 := hb (by rw [Real.dist_eq]; exact hs')
  rw [dist_eq_norm] at hd
  have h1 := hmc x
  have h2 := abs_inner_le_opNorm (A s - A t₀) x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have e : ⟪x, A s x⟫ = ⟪x, A t₀ x⟫ + ⟪x, (A s - A t₀) x⟫ := by
    rw [show (A s - A t₀) x = A s x - A t₀ x from rfl, inner_sub_right]; ring
  have h3 : ‖A s - A t₀‖ * ‖x‖ ^ 2 ≤ m / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hd.le hx2.le
  rw [e]
  have := (abs_le.mp h2).1
  nlinarith

/-- The end of the initial positive semidefinite interval of a path, in `[t₀, t₁]`. -/
noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

/-- **The canonical crossing.**  A continuous symmetric path, positive definite at `t₀`,
with a negative direction at `t₁ > t₀` and isolated non-units, has at the end `ts` of its
initial positive semidefinite interval a genuine sign change: `A ts` is positive
semidefinite and singular, `A` is positive definite at parameters arbitrarily close before
`ts` and has a negative direction at parameters arbitrarily close after `ts`. -/
theorem psdEdge_spec (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0)
    (hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s)) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ - η < s ∧ s < psdEdge A t₀ t₁ ∧
        ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)} with hS
  have hts' : psdEdge A t₀ t₁ = sSup S := rfl
  set ts := psdEdge A t₀ t₁ with hts
  have hpsd0 : PSD (A t₀) := psd_of_pd _ hpd
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01.le⟩, fun s hs' => by
    rw [le_antisymm hs'.2 hs'.1]; exact hpsd0⟩
  have hne : S.Nonempty := ⟨t₀, h0S⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hts0 : t₀ ≤ ts := by rw [hts']; exact le_csSup hbdd h0S
  have hts1 : ts ≤ t₁ := by rw [hts']; exact csSup_le hne (fun t ht => ht.1.2)
  obtain ⟨δ, hδ, hpdn⟩ := eventually_pd hc hs t₀ hpd
  have hδS : min (t₀ + δ / 2) t₁ ∈ S := by
    refine ⟨⟨le_min (by linarith) h01.le, min_le_right _ _⟩, fun s hs' => ?_⟩
    have hs1 : s ≤ t₀ + δ / 2 := le_trans hs'.2 (min_le_left _ _)
    exact psd_of_pd _ (hpdn s (by rw [abs_lt]; constructor <;> linarith [hs'.1]))
  have hts0' : t₀ < ts := by
    have h1 : t₀ < min (t₀ + δ / 2) t₁ := lt_min (by linarith) h01
    have h2 : min (t₀ + δ / 2) t₁ ≤ ts := by rw [hts']; exact le_csSup hbdd hδS
    linarith
  have hlt : ∀ s, t₀ ≤ s → s < ts → PSD (A s) := by
    intro s hs0 hs1
    rw [hts'] at hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hpsd_ts : PSD (A ts) := by
    intro v
    have hsub : Ico t₀ ts ⊆ {s : ℝ | 0 ≤ ⟪v, A s v⟫} := fun s hs' => hlt s hs'.1 hs'.2 v
    have hcl : IsClosed {s : ℝ | 0 ≤ ⟪v, A s v⟫} := isClosed_le continuous_const (by fun_prop)
    have hcs := hcl.closure_subset_iff.mpr hsub
    exact hcs (by rw [closure_Ico hts0'.ne]; exact ⟨hts0, le_rfl⟩)
  have hle : ∀ s, t₀ ≤ s → s ≤ ts → PSD (A s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have hts1' : ts < t₁ := by
    rcases hts1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts w
      rw [h] at this
      linarith
  have haft : ∀ η : ℝ, 0 < η → ∃ s, ts < s ∧ s < ts + η ∧ ∃ v, ⟪v, A s v⟫ < 0 := by
    intro η hη
    set t' := min (ts + η / 2) t₁ with ht'
    have ht'1 : ts < t' := lt_min (by linarith) hts1'
    have hnot : t' ∉ S := by
      intro h
      have : t' ≤ ts := by rw [hts']; exact le_csSup hbdd h
      linarith
    have hnall : ¬ ∀ s ∈ Icc t₀ t', PSD (A s) := fun hall =>
      hnot ⟨⟨by linarith, min_le_right _ _⟩, hall⟩
    push Not at hnall
    obtain ⟨s, hs', hns⟩ := hnall
    have hsts : ts < s := by
      by_contra hcon
      push Not at hcon
      exact hns (hle s hs'.1 hcon)
    have hst' : s < ts + η := lt_of_le_of_lt (le_trans hs'.2 (min_le_left _ _)) (by linarith)
    unfold PSD at hns
    push Not at hns
    exact ⟨s, hsts, hst', hns⟩
  have hnu : ¬ IsUnit (A ts) := by
    intro hu
    have hpdts : ∀ x, x ≠ 0 → 0 < ⟪x, A ts x⟫ := fun x hx =>
      pos_of_psd_unit _ (hs ts) hpsd_ts hu x hx
    obtain ⟨δ', hδ', hb⟩ := eventually_pd hc hs ts hpdts
    obtain ⟨s, h1, h2, v, hv⟩ := haft δ' hδ'
    have hsd := hb s (by rw [abs_lt]; constructor <;> linarith)
    by_cases hv0 : v = 0
    · rw [hv0] at hv; simp at hv
    · linarith [hsd v hv0]
  have hbef : ∀ η : ℝ, 0 < η → ∃ s, ts - η < s ∧ s < ts ∧ ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
    intro η hη
    obtain ⟨η', hη', hiso'⟩ := hiso ts
    set r := min (min η η') (ts - t₀) with hr
    have hr0 : 0 < r := lt_min (lt_min hη hη') (by linarith)
    have hr1 : r ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr2 : r ≤ η' := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr3 : r ≤ ts - t₀ := min_le_right _ _
    refine ⟨ts - r / 2, by linarith, by linarith, fun x hx => ?_⟩
    have hu := hiso' (ts - r / 2) (by intro h; linarith)
      (by rw [abs_lt]; constructor <;> linarith)
    exact pos_of_psd_unit _ (hs _) (hle _ (by linarith) (by linarith)) hu x hx
  exact ⟨hts0', hts1', hpsd_ts, hnu, hle, hbef, haft⟩

end Edge

#print axioms gramDet_eq
#print axioms isUnit_iff_gramDet
#print axioms analyticAt_gramDet
#print axioms isUnit_punctured
#print axioms psdEdge_spec
#print axioms AnM.trace_re
#print axioms analyticAt_exp_I

#print axioms AnM
#print axioms anM_const
#print axioms AnR
#print axioms anR_const
#print axioms AnR.add
#print axioms AnR.sub
#print axioms AnR.mul
#print axioms AnR.sum
#print axioms AnM.add
#print axioms AnM.sub
#print axioms AnM.neg
#print axioms AnM.mul
#print axioms AnM.smul
#print axioms AnM.star
#print axioms AnM.tr_re3
#print axioms gramDet
#print axioms abs_inner_le_opNorm
#print axioms pos_of_psd_unit
#print axioms unit_of_pd
#print axioms psd_of_pd
#print axioms eventually_pd
#print axioms psdEdge

end AdalyFormal.Round9.Guarded.QualitativeR2


/-!
Round 9.2, qualitative route: the vacuum crossing is a theorem, the two twist directions are
gauge equivalent, and the remaining premise is soft regularity plus one coupling.

* Abstract: a symmetric operator is a unit iff its Gram determinant is nonzero; along a path
  whose matrix coefficients are real-analytic the Gram determinant is analytic, so non-units
  are isolated once the path is a unit somewhere (identity theorem).  A continuous path that is
  positive definite at `t₀`, has a negative direction at `t₁` and isolated non-units, crosses
  at the end of its initial positive semidefinite interval: positive definite arbitrarily close
  before, a negative direction arbitrarily close after.
* Lattice: the frozen continuity chain for the plaquette Hessian (`D1Cont`), repeated with
  `Continuous` replaced by entrywise real-analyticity, and over a general parameter space.
* Concrete: the vacuum carrier of the actual exterior twist is positive definite at angle `0`
  for all large scales and radii (frozen `M2RightInv.p428Target8`), negative at `π` (round 5),
  analytic in the angle; hence it crosses canonically, forwards and backwards.  Joint
  continuity follows from interior continuity.  The literal family may use negative angles.
* Gauge flip: the constant gauge transformation by `[[0,1],[-1,0]]` maps the twist at
  `(ε, t)` to `(-ε, -t)` (frozen covariance lane, extended to the all-plaquette carrier), so
  the backward crossing is the forward one and the coupling changes sign between them.
* Diagonal `U(1)`: the constant rotations `diag(e^{iα}, e^{-iα})` fix every configuration of
  the family, so the vacuum carrier and the first-order coefficient commute with them; on a
  charged complex line the coupling is the single number `⟪u₀, De u₀⟫` (round 8's `c₁`).

Nothing here proves a pinned goal.  The premises `TwistSoftCouplingFwd`, `TwistSoftU1`,
`TwistSoftCoupling` and `PathSoftCoupling` are explicit, unproved hypotheses on the actual
operators.
-/
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

/-! ## The plaquette Hessian along an analytic family of links

The frozen `D1Cont` proves that `θ ↦ deltaKLocCLM (U θ) P` is continuous when every link
matrix is.  The same chain of elementary operations (matrix products, adjoints, traces,
real parts, finite sums) preserves real-analyticity; below is that chain, statement by
statement, with `Continuous` replaced by entrywise analyticity.  The second section repeats
the frozen continuity chain over an arbitrary topological parameter space (used for joint
continuity in curvature and angle). -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent}

/-- A family of link configurations whose link matrices are entrywise real-analytic. -/
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : AnFam U)
include hU

theorem an_inv_coe (e : PeriodicLatticeEdge L) :
    AnM fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star

theorem an_holonomyElem (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).mul (hU _)).mul (an_inv_coe hU _)).mul (an_inv_coe hU _)

theorem an_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (an_holonomyElem hU p).star

theorem an_reHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact ((an_holonomyElem hU p).add (an_holonomyElemInv hU p)).smul _

theorem an_imHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact ((an_holonomyElem hU p).sub (an_holonomyElemInv hU p)).smul _

theorem an_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    AnM fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).mul (anM_const _)).mul (hU e).star

theorem an_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((anM_const _).add (an_RMap hU _ _)).sub (an_RMap hU _ _)).sub (anM_const _)

theorem an_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a1LM (U θ) p A := by
  show AnM fun θ =>
    -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (an_RMap hU _ _).neg

theorem an_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a4LM (U θ) p A := by
  show AnM fun θ =>
    bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact an_RMap hU _ _

theorem an_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    AnR fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ}, AnM f → AnM fun θ => smulILM (f θ) := by
    intro f hf
    exact hf.smul Complex.I
  have b1A : AnM fun θ => b1LM (U θ) p A := hI (an_a1 hU p A)
  have b4B : AnM fun θ => b4LM (U θ) p B := hI (an_a4 hU p B)
  have hre := an_reHolonomy hU p
  have him := an_imHolonomy hU p
  have hcA : AnM fun θ => smulILM (curlMatLM (U θ) p A) := hI (an_curlMat hU p A)
  have hcB : AnM fun θ => smulILM (curlMatLM (U θ) p B) := hI (an_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), AnM fun _ : ℝ => M := fun M => anM_const M
  exact ((((((AnM.tr_re3 hcA hcB (hre.sub (k 1))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) b4B him).sub (AnM.tr_re3 (hI b4B) b1A him))).add
    ((AnM.tr_re3 (k _) (k _) him).sub (AnM.tr_re3 (k _) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))

open Classical in
theorem an_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    AnR fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, AnR fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact AnR.sum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact an_bilPlaq hU p A B
      · simp only [hp, if_false]; exact anR_const 0)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact (anR_const _).mul ((anR_const _).mul ((h A B).add (h B A)))

open Classical in
theorem an_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine AnR.sum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show AnR fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    exact (anR_const _).mul
      ((an_curlMat hU p (WithLp.ofLp x)).mul (an_curlMat hU p (WithLp.ofLp y))).trace_re
  · simp only [hp, if_false, inner_zero_left]
    exact anR_const 0

/-- Every matrix coefficient of the plaquette Hessian is real-analytic in the parameter. -/
theorem an_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (an_curlInner hU P x y).add (an_deltaPrimeBil hU P _ _)

end

/-- `diag(e^{iθ}, e^{-iθ})` is entrywise real-analytic. -/
theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

/-- The frozen exterior twist is an analytic family. -/
theorem anFam_Uth (Om : Set (PeriodicLatticeSite L)) : AnFam (AdalyFormal.D1Literal.Uth Om) := by
  intro e
  unfold AdalyFormal.D1Literal.Uth
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb Om
  · simp only [he, if_true]
    show AnM fun θ => AdalyFormal.D1Literal.uMat θ
    exact anM_uMat
  · simp only [he, if_false]
    exact anM_const _

/-! ### The frozen continuity chain over an arbitrary parameter space -/

section Param
variable {Y : Type*} [TopologicalSpace Y]

/-- A family of link configurations over a topological parameter space, continuous link by
link (the frozen `ContFam` with `ℝ` replaced by `Y`). -/
def ContFamY (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
include hU

theorem contY_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (hU e).star

theorem contY_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U y (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (contY_inv_coe hU _)).matrix_mul
    (contY_inv_coe hU _)

theorem contY_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y; rfl
  rw [this]
  exact (contY_holonomyElem hU p).star

theorem contY_reHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => reHolonomy (U y) p := by
  unfold reHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).add (contY_holonomyElemInv hU p))

theorem contY_imHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => imHolonomy (U y) p := by
  unfold imHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).sub (contY_holonomyElemInv hU p))

theorem contY_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U y e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star

theorem contY_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => curlMatLM (U y) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (contY_RMap hU _ _)).sub (contY_RMap hU _ _)).sub
    continuous_const)

theorem contY_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a1LM (U y) p A := by
  show Continuous fun y =>
    -(bondMatRLM (U y (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (contY_RMap hU _ _).neg

theorem contY_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a4LM (U y) p A := by
  show Continuous fun y =>
    bondMatRLM (U y (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact contY_RMap hU _ _

omit hU in
theorem contY_tr_re3 {f g h : Y → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun y => (Matrix.trace (f y * g y * h y)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)

theorem contY_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun y => bilPlaq (U y) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : Y → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f →
      Continuous fun y => smulILM (f y) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun y => b1LM (U y) p A := hI (contY_a1 hU p A)
  have b4B : Continuous fun y => b4LM (U y) p B := hI (contY_a4 hU p B)
  have hre := contY_reHolonomy hU p
  have him := contY_imHolonomy hU p
  have hcA : Continuous fun y => smulILM (curlMatLM (U y) p A) := hI (contY_curlMat hU p A)
  have hcB : Continuous fun y => smulILM (curlMatLM (U y) p B) := hI (contY_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : Y => M :=
    fun M => continuous_const
  refine ((((((contY_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) b4B him).sub (contY_tr_re3 (hI b4B) b1A him))).add
    ((contY_tr_re3 (k _) (k _) him).sub (contY_tr_re3 (k _) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))

open Classical in
theorem contY_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun y => deltaPrimeBilNormLoc (U y) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun y => deltaPrimeBilRawLoc (U y) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finsetSum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact contY_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))

open Classical in
theorem contY_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun w => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U w) (WithLp.ofLp x) p) (curlValueCovariant (U w) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((contY_curlMat hU p (WithLp.ofLp x)).matrix_mul
      (contY_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const

theorem contY_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w => (inner ℝ x (deltaKLocCLM (U w) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (contY_curlInner hU P x y).add (contY_deltaPrimeBil hU P _ _)

end

theorem contY_deltaKLocCLM {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun w => deltaKLocCLM (U w) P :=
  AdalyFormal.D1Literal.continuous_clm_of_inner (fun x y => contY_inner_delta hU P x y)

end Param

#print axioms AnFam
#print axioms an_inner_delta
#print axioms anM_uMat
#print axioms anFam_Uth
#print axioms ContFamY
#print axioms contY_deltaKLocCLM

#print axioms an_inv_coe
#print axioms an_holonomyElem
#print axioms an_holonomyElemInv
#print axioms an_reHolonomy
#print axioms an_imHolonomy
#print axioms an_RMap
#print axioms an_curlMat
#print axioms an_a1
#print axioms an_a4
#print axioms an_bilPlaq
#print axioms an_deltaPrimeBil
#print axioms an_curlInner
#print axioms contY_inv_coe
#print axioms contY_holonomyElem
#print axioms contY_holonomyElemInv
#print axioms contY_reHolonomy
#print axioms contY_imHolonomy
#print axioms contY_RMap
#print axioms contY_curlMat
#print axioms contY_a1
#print axioms contY_a4
#print axioms contY_tr_re3
#print axioms contY_bilPlaq
#print axioms contY_deltaPrimeBil
#print axioms contY_curlInner
#print axioms contY_inner_delta

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The actual operators: canonical vacuum crossings, and the reduced premise

Everything below concerns the actual pinned assemblies of the round-4/5 dilated family.
* Along an analytic exterior path every matrix coefficient of the actual carrier is
  real-analytic in the path parameter (frozen exterior path formula and the analytic
  plaquette chain above), so its non-units are isolated as soon as it is a unit somewhere.
* At the trivial configuration the all-plaquette carrier dominates the localized one, which is
  positive semidefinite, and a unit at every large scale and radius by the FROZEN localized
  theorem `M2RightInv.p428Target8`.  So the vacuum carrier of the exterior twist is positive
  definite at angle `0`; round 5 gives a negative direction at angle `π`.
* Hence at every large scale and radius the vacuum twist has a canonical crossing (the end of
  its initial positive semidefinite interval) with positive definite carriers arbitrarily close
  before it and negative directions arbitrarily close after it, for the twist run forwards
  (`Uth t`) and backwards (`Uth (-t)`).  Round 9.1 assumed this; here it is proved.
* Joint continuity in curvature and angle follows from continuity in the curvature, at the
  untwisted angle, of the carrier and of the dressing `W`.
* The literal round-8 family may use negative angles.  A positive coupling on the backward
  side gives a pre-crossing separation there, so no post-crossing analysis is needed.
What remains unproved is soft regularity of the interior family at the flat interior and a
definite first-order coupling on the canonical vacuum kernel. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-! ### Analyticity in the exterior angle -/

/-- An analytic exterior path, a fixed profile and a fixed curvature give an analytic family. -/
theorem pathU_anFam (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : AnFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact anM_const _

theorem uthPath_anFam (q R : ℕ) : AnFam (uthPath q R) := anFam_Uth _

/-- The frozen exterior twist run backwards. -/
noncomputable def uthPathNeg (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun s => uthPath q R (-s)

theorem uthPathNeg_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPathNeg q R) :=
  fun e => (uthPath_cont q R e).comp continuous_neg

theorem uthPathNeg_anFam (q R : ℕ) : AnFam (uthPathNeg q R) := by
  intro e θ₀ i j
  have hn : AnalyticAt ℝ (fun θ : ℝ => -θ) θ₀ := by fun_prop
  exact AnalyticAt.comp (g := fun θ => ((uthPath q R θ e : AdalyFormal.D1Literal.SU2m) :
    Matrix (Fin 2) (Fin 2) ℂ) i j) (uthPath_anFam q R e (-θ₀) i j) hn

theorem uthPath_zero (q R : ℕ) : uthPath q R 0 = fun _ => 1 :=
  AdalyFormal.D1Literal.Uth_zero _

theorem uthPathNeg_zero (q R : ℕ) : uthPathNeg q R 0 = fun _ => 1 := by
  show uthPath q R (-0) = _
  rw [neg_zero]
  exact uthPath_zero q R

/-- Along an analytic exterior path, every matrix coefficient of the actual all-plaquette
carrier is real-analytic in the path parameter. -/
theorem pathA_anR {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    AnR (fun t => ⟪x, pathA q R V f ε a t y⟫) := by
  have h : ∀ t, pathA q R V f ε a t = pathA q R V f ε a 0 +
      (pE (geomOf 2 1 (dilTower q R))).comp (((ContinuousLinearMap.adjoint
        (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ)).comp
          (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a))).comp
        (iE (geomOf 2 1 (dilTower q R)))) :=
    fun t => exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) (pathU q R V f ε) (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  have he : ∀ t, ⟪x, pathA q R V f ε a t y⟫ = ⟪x, pathA q R V f ε a 0 y⟫ +
      (⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫ -
        ⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫) := by
    intro t
    rw [h t]
    simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_right, pE_inner_right,
      ContinuousLinearMap.adjoint_inner_right, sub_apply, inner_sub_right]
  rw [funext he]
  exact (anR_const _).add
    ((an_inner_delta (pathU_anFam q R hV f ε) Set.univ _ _).sub (anR_const _))

/-- Isolated non-units along an analytic exterior path, at every curvature and profile. -/
theorem pathA_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (pathA q R V f ε a s) :=
  isUnit_punctured (fun x y θ₀ => pathA_anR hq hR hroom hV f ε a x y θ₀) hu t

/-- The corrected carrier along an analytic exterior path also has isolated non-units (the
correction does not depend on the exterior). -/
theorem pathC_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η →
      IsUnit (pathA q R V f ε a s - pathD q R V f ε a s) := by
  have hD : ∀ s, pathD q R V f ε a s = pathD q R V f ε a 0 :=
    fun s => pathD_constant hq hR hroom V f ε a s
  have hu' : IsUnit (pathA q R V f ε a t₀ - pathD q R V f ε a 0) := by rw [← hD t₀]; exact hu
  obtain ⟨η, hη, hb⟩ := isUnit_punctured (A := fun s => pathA q R V f ε a s - pathD q R V f ε a 0)
    (fun x y θ₀ => by
      have e : (fun θ => ⟪x, (pathA q R V f ε a θ - pathD q R V f ε a 0) y⟫) =
          fun θ => ⟪x, pathA q R V f ε a θ y⟫ - ⟪x, pathD q R V f ε a 0 y⟫ := by
        funext θ; rw [sub_apply, inner_sub_right]
      rw [e]
      exact (pathA_anR hq hR hroom hV f ε a x y θ₀).fun_sub analyticAt_const) hu' t
  exact ⟨η, hη, fun s hs hst => by rw [hD s]; exact hb s hs hst⟩

/-! ### The vacuum carrier at angle zero is positive definite -/

theorem inner_Ginv_dataS (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G)
        (Wop P.G P.U P.a (iE P.G x))⟫ + ‖(dataS sD sJ P).T x‖ ^ 2 +
      ⟪x, (dataS sD sJ P).Mass x⟫ := by
  have hD : ⟪x, (dataS sD sJ P).Dpi x⟫ = ⟪Wop P.G P.U P.a (iE P.G x),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x⟫ = _
    simp only [ContinuousLinearMap.comp_apply, DpiFullS, DeltaS]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [BaseDataS.inner_Ginv, hD]

/-- At the trivial background the plaquette Hessian is monotone in the plaquette set. -/
theorem flat_delta_le_univ {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (y : BondFnL2 L) :
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) P y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) Set.univ y⟫ := by
  have h1 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU P _ _
  have h2 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU Set.univ _ _
  change ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y⟫ ≤
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y⟫
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, h1, h2, add_zero, add_zero,
    AdalyFormal.StatementLaneR6.plaqMask_univ]
  simp only [PiLp.inner_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp only [hp, if_true, le_refl]
  · simp only [hp, if_false, inner_zero_left]
    exact real_inner_self_nonneg

theorem mass_nonneg_dataS (sD sJ : PlaqSel) (P : IngrBParams) (ha : 0 ≤ P.a)
    (x : ↥(bondSupp P.G)) : 0 ≤ ⟪x, (dataS sD sJ P).Mass x⟫ := by
  show 0 ≤ ⟪x, ((pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G))) x⟫
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pE_inner_right,
    inner_MassFull]
  refine Finset.sum_nonneg (fun p _ => ?_)
  have h1 : (0 : ℝ) ≤ (P.G.ell : ℝ) ^ (p.1 : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg (mul_nonneg ha h1) (sq_nonneg _)

/-- At the trivial background the localized carrier is positive semidefinite. -/
theorem Ginv_loc_psd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a) :
    PSD (dataS selIn selIn P).Ginv := by
  intro x
  rw [inner_Ginv_dataS]
  have h1 : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U
      (selIn _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    generalize Wop P.G P.U P.a (iE P.G x) = y
    rw [hU]
    exact AdalyFormal.StatementLaneR6.deltaKLocCLM_flat_nonneg _ y
  have h2 := mass_nonneg_dataS selIn selIn P ha x
  have h3 := sq_nonneg ‖(dataS selIn selIn P).T x‖
  linarith

/-- At the trivial background the all-plaquette carrier dominates the localized one. -/
theorem Ginv_loc_le_all_flat (P : IngrBParams) (hU : P.U = fun _ => 1)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [inner_Ginv_dataS, inner_Ginv_dataS]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have key : ∀ y, ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selIn _ P.G) y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selAll _ P.G) y⟫ := by
    intro y
    rw [hU]
    exact flat_delta_le_univ _ y
  linarith [key (Wop P.G P.U P.a (iE P.G x))]

/-- A unit localized carrier at the trivial background makes the all-plaquette carrier
positive definite. -/
theorem Ginv_all_pd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a)
    (hu : IsUnit (dataS selIn selIn P).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  intro x hx
  have h1 := pos_of_psd_unit _ ((dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P))
    (Ginv_loc_psd_flat P hU ha) hu x hx
  exact lt_of_lt_of_le h1 (Ginv_loc_le_all_flat P hU x)

/-- The trivial configuration of the dilated geometry, mass `1`. -/
noncomputable def flatP (q R : ℕ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)

theorem dilU_flat (q R : ℕ) : dilU q R 0 (fun _ => 1) = fun _ => 1 := by
  classical
  funext e
  simp only [dilU, ite_self, Ug_zero]

/-- **The frozen localized theorem at the trivial configuration.**  At every large scale and
every large even radius the localized carrier of the trivial configuration is a unit
(`M2RightInv.p428Target8`, through the instance inequality and `WellDefAt_loc_of_inst`). -/
theorem flat_loc_unit_eventually :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      IsUnit (dataS selIn selIn (flatP (2^j) R)).Ginv := by
  obtain ⟨m₂, -, hmm⟩ := (AdalyFormal.D1Literal.pin_target8_iff.mpr
    AdalyFormal.M2RightInv.p428Target8 : AdalyFormal.D1Literal.P428Target8S
      AdalyFormal.D1Literal.selIn AdalyFormal.D1Literal.selIn) 2 le_rfl 1 one_pos
  refine ⟨m₂, fun j hj => ?_⟩
  obtain ⟨R₂, hR₂⟩ := hmm (j+1) (by omega)
  refine ⟨R₂, fun R hR hR2 hR18 => ?_⟩
  obtain ⟨-, a₀, ha₀, γ₀, hγ, hcore⟩ := hR₂ R hR
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let α : ℝ := min (a₀/(24*q)) 1/2
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ) * ((2^(j+1) : ℕ) : ℝ) * α ≤ a₀ := by
    have hm : α ≤ a₀/(24*q) := by
      have hp : 0 < min (a₀/(24*q)) 1 := by positivity
      dsimp [α]; linarith [min_le_left (a₀/(24*q)) 1]
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 24*q)).mp hm
    rw [hpow]; push_cast; nlinarith
  have hT : TorusOK 2 (2^(j+1)) (dilLu q R) := by rw [hpow]; exact dil_torus hq R
  have hS : Admissible 2 (2^(j+1)) R 1 (dilTower q R) := by
    rw [hpow]; exact dil_admissible hq hR2
  have hL : LambdaOK2 2 (2^(j+1)) R 1 (dilTower q R) (dilLam q R) := by
    rw [hpow]; exact dil_lambda hq hR2
  have hreg := dil_regular hq hR2 hα (ε := 0) (by rw [abs_zero]; positivity) (fun _ => 1)
  rw [dilU_flat] at hreg
  have hcl : ClassCoupled 2 (2^(j+1)) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (fun _ => 1) := by
    rw [hpow]; exact ⟨dil_coverage hq hR2 (by omega), hreg⟩
  have hloc := hcore 1 le_rfl (dilLu q R) α hα hcap hT (dilTower q R) hS (dilLam q R) hL _ hcl
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR2
  exact (AdalyFormal.D1Guarded.WellDefAt_loc_of_inst 2 1 (by norm_num) 1 zero_le_one
    (dilLu q R) γ₀ hγ (dilTower q R) (dilLam q R) _ (dilBt hq R) hBt1 hBt2 hE hloc).1

theorem pathU_flat_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R V f 0 0 = fun _ => 1 := by
  classical
  funext e
  simp only [pathU, maskedU, hV0, zero_mul, Ug_zero, ite_self]

theorem vacA_zero_flat (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) : vacA q R V 1 0 = (dataS selAll selAll (flatP q R)).Ginv := by
  unfold vacA pathA pathP flatP
  rw [pathU_flat_base q R hV0 (fun _ => 0)]

/-- The vacuum carrier is positive definite at the base point of an exterior path that starts
at the trivial field, as soon as the localized carrier of the trivial configuration is a
unit. -/
theorem vacA_pd_zero {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫ := by
  rw [vacA_zero_flat q R hV0]
  exact Ginv_all_pd_flat (flatP q R) rfl zero_le_one hloc

/-! ### Negative endpoints and the canonical crossing -/

theorem vacA_uth_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) :
    ∃ w, ⟪w, vacA q R (uthPath q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := twistA_pi_negative hq hR hroom 0
  refine ⟨w, ?_⟩
  rw [twistA_eq_path, pathA_zero] at hw
  exact hw

theorem uθ_neg_pi : AdalyFormal.D1Literal.uθ (-Real.pi) = AdalyFormal.D1Literal.uθ Real.pi := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat (-Real.pi) = AdalyFormal.D1Literal.uMat Real.pi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Complex.exp_neg, Complex.exp_pi_mul_I]

theorem uthPath_neg_pi (q R : ℕ) : uthPath q R (-Real.pi) = uthPath q R Real.pi := by
  funext e
  simp only [uthPath, AdalyFormal.D1Literal.Uth, uθ_neg_pi]

theorem vacA_uthNeg_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) : ∃ w, ⟪w, vacA q R (uthPathNeg q R) 1 Real.pi w⟫ < 0 := by
  obtain ⟨w, hw⟩ := vacA_uth_pi_negative hq hR hroom
  refine ⟨w, ?_⟩
  have hU : pathU q R (uthPathNeg q R) (fun _ => 0) 0 Real.pi =
      pathU q R (uthPath q R) (fun _ => 0) 0 Real.pi := by
    show maskedU q R _ (uthPath q R (-Real.pi)) = maskedU q R _ (uthPath q R Real.pi)
    rw [uthPath_neg_pi]
  have h : vacA q R (uthPathNeg q R) 1 Real.pi = vacA q R (uthPath q R) 1 Real.pi := by
    unfold vacA pathA pathP
    rw [hU]
  rw [h]
  exact hw

/-- The canonical crossing angle of the vacuum carrier along an exterior path: the end of its
initial positive semidefinite interval in `[0, π]`. -/
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

/-- The vacuum carrier along `V` crosses at `ts`: it is positive semidefinite and singular
there, positive definite at angles arbitrarily close before `ts`, and has a negative
direction at angles arbitrarily close after `ts`. -/
def VacuumCrossesAt (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (ts : ℝ) : Prop :=
  0 < ts ∧ ts < Real.pi ∧ PSD (vacA q R V 1 ts) ∧ ¬ IsUnit (vacA q R V 1 ts) ∧
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)

/-- **The canonical vacuum crossing.**  Along a continuous, analytic exterior path whose vacuum
carrier is positive definite at `0` and has a negative direction at `π`, the vacuum carrier
crosses at `vacEdge`. -/
theorem vacuum_crossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hpd0 : ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0) :
    VacuumCrossesAt q R V (vacEdge q R V) := by
  obtain ⟨w, hw⟩ := hneg
  have hc : Continuous (vacA q R V 1) := pathA_continuous hq hR hroom hVc (fun _ => 0) 0 1
  have hs : ∀ t x y, ⟪vacA q R V 1 t x, y⟫ = ⟪x, vacA q R V 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (dataS_laws selAll selAll _) x y
  have hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (vacA q R V 1 s) :=
    fun t => pathA_isolated hq hR hroom hVa (fun _ => 0) 0 1 (t₀ := 0) (unit_of_pd _ hpd0) t
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ :=
    psdEdge_spec (vacA q R V 1) hc hs Real.pi_pos hpd0 w hw hiso
  exact ⟨h1, h2, h3, h4, h6, h7⟩

/-- **Unconditional.**  At every large scale and every large even radius the vacuum carrier of
the actual exterior twist crosses at its canonical angle, forwards and backwards. -/
theorem twist_vacuum_crossing :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      VacuumCrossesAt (2^j) R (uthPath (2^j) R) (vacEdge (2^j) R (uthPath (2^j) R)) ∧
      VacuumCrossesAt (2^j) R (uthPathNeg (2^j) R) (vacEdge (2^j) R (uthPathNeg (2^j) R)) := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R hR hR2 hR18
  exact ⟨vacuum_crossing hq hR2 hroom (uthPath_cont _ _) (uthPath_anFam _ _)
      (vacA_pd_zero (uthPath_zero _ _) hloc) (vacA_uth_pi_negative hq hR2 hroom),
    vacuum_crossing hq hR2 hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
      (vacA_pd_zero (uthPathNeg_zero _ _) hloc) (vacA_uthNeg_pi_negative hq hR2 hroom)⟩

/-- **Unconditional.**  At every curvature the non-units of the actual curved twist, and of its
corrected carrier, are isolated in the angle once the respective carrier is a unit somewhere. -/
theorem twist_isolated_nonunits {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (ε : ℝ) :
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s)) ∧
    ((∃ t₀, IsUnit (twistA q R ε 1 t₀ - twistD q R ε 1 t₀)) → ∀ t, ∃ η : ℝ, 0 < η ∧
      ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (twistA q R ε 1 s - twistD q R ε 1 s)) := by
  constructor
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathA_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path]; exact hb s hs hst⟩
  · rintro ⟨t₀, hu⟩ t
    rw [twistA_eq_path, twistD_eq_path] at hu
    obtain ⟨η, hη, hb⟩ := pathC_isolated hq hR hroom (uthPath_anFam q R) (dilMask q R) ε 1 hu t
    exact ⟨η, hη, fun s hs hst => by rw [twistA_eq_path, twistD_eq_path]; exact hb s hs hst⟩

/-! ### Joint continuity from interior continuity -/

theorem uMat_continuous' : Continuous fun θ : ℝ => AdalyFormal.D1Literal.uMat θ := by
  unfold AdalyFormal.D1Literal.uMat
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The abelian link `Ug t = exp(i t σ₃)` is `diag(e^{it}, e^{-it})`. -/
theorem Ug_coe_uMat (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]

/-- Path families are jointly continuous in (curvature, path parameter), link by link. -/
theorem pathU_contFamY (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFamY (fun p : ℝ × ℝ => pathU q R V f p.1 p.2) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact (hV e).comp continuous_snd
  · simp only [pathU, maskedU, if_neg he, Ug_coe_uMat]
    exact uMat_continuous'.comp (continuous_fst.mul continuous_const)

/-- Joint continuity of the carrier in (curvature, angle) at zero curvature, from continuity in
the curvature of the carrier at the path's base point and of the dressing `W` there. -/
theorem pathA_jointly_continuousAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hA0 : ContinuousAt (fun ε : ℝ => pathA q R V f ε 1 0) 0)
    (hW0 : ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) 0)
    (t : ℝ) : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  let G := geomOf 2 1 (dilTower q R)
  let Wf : ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun ε => Wop G (pathU q R V f ε 0) 1
  let Δf : ℝ × ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun p => AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f p.1 p.2) Set.univ
  have hpath : ∀ p : ℝ × ℝ, pathA q R V f p.1 1 p.2 = pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) := fun p =>
    exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) (pathU q R V f p.1) (fun s e he => path_agrees q R V f p.1 s 0 e he)
      selAll p.2
  rw [show (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) = fun p => pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) from funext hpath]
  have hΔ : Continuous Δf := contY_deltaKLocCLM (pathU_contFamY q R hV f) _
  have hA : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 0) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hA0 continuousAt_fst
  have hW : ContinuousAt (fun p : ℝ × ℝ => Wf p.1) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hW0 continuousAt_fst
  have hadj : Continuous (fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => ContinuousLinearMap.adjoint M) :=
    (ContinuousLinearMap.adjoint : (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R))) ≃ₗᵢ⋆[ℝ] (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)))).continuous
  have hWa : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Wf p.1)) (0, t) :=
    hadj.continuousAt.comp hW
  have hD : ContinuousAt (fun p : ℝ × ℝ => Δf p - Δf (p.1, 0)) (0, t) :=
    hΔ.continuousAt.sub ((hΔ.comp (continuous_fst.prodMk continuous_const)).continuousAt)
  have hmid : ContinuousAt (fun p : ℝ × ℝ => (ContinuousLinearMap.adjoint (Wf p.1)).comp
      ((Δf p - Δf (p.1, 0)).comp (Wf p.1))) (0, t) := hWa.clm_comp (hD.clm_comp hW)
  have hout : Continuous fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => (pE G).comp (M.comp (iE G)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact hA.add (hout.continuousAt.comp hmid)

/-! ### The reduced premise: soft regularity of the interior family and the coupling -/

/-- The curved interior with the trivial exterior field. -/
noncomputable def bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (fun _ => 1)

noncomputable def bulkP (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)

/-- The actual all-plaquette carrier of the interior family. -/
noncomputable def bulkA (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (bulkP q R f ε)).Ginv

/-- The actual localized correction of the interior family. -/
noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)

/-- **Soft regularity of the interior family** `ε ↦ maskedU (ε f) 1` (curved interior, trivial
exterior) at the flat interior: the carrier and the dressing `W` are continuous at `ε = 0`
and the correction has derivative `De` there.  No exterior angle appears.  NOT proved here. -/
def InteriorSoft (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ContinuousAt (fun ε : ℝ => bulkA q R f ε) 0 ∧
  ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1) 0 ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0

theorem pathU_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathU q R V f ε 0 = bulkU q R f ε := by
  unfold pathU bulkU
  rw [hV0]

theorem pathP_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathP q R V f ε 1 0 = bulkP q R f ε := by
  unfold pathP bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathA_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathA q R V f ε 1 0 = bulkA q R f ε := by
  unfold pathA pathP bulkA bulkP
  rw [pathU_base q R hV0 f ε]

theorem pathD_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathD q R V f ε 1 0 = bulkD q R f ε := by
  have hd : dataS selIn selIn (pathP q R V f ε 1 0) = dataS selIn selIn (bulkP q R f ε) := by
    unfold pathP bulkP
    rw [pathU_base q R hV0 f ε]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

theorem joint_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  obtain ⟨hA, hW, -⟩ := hs
  refine pathA_jointly_continuousAt hq hR hroom hVc f ?_ ?_ t
  · rw [show (fun ε : ℝ => pathA q R V f ε 1 0) = fun ε => bulkA q R f ε
      from funext (pathA_base q R hV0 f)]
    exact hA
  · rw [show (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) =
        fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1
      from funext (fun ε => by rw [pathU_base q R hV0 f ε])]
    exact hW

theorem deriv_of_soft {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) : HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 := by
  rw [show (fun ε : ℝ => pathD q R V f ε 1 0) = fun ε => bulkD q R f ε
    from funext (pathD_base q R hV0 f)]
  exact hs.2.2

/-- The first-order coefficient is definite, of either sign, on the kernel of the vacuum carrier
at the canonical crossing of `V`.  NOT proved here. -/
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The first-order coefficient is positive definite on the kernel of the vacuum carrier at the
canonical crossing of `V`.  NOT proved here. -/
def CanonicalCouplingPos (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫

/-- Soft regularity and a definite coupling give round 9.1's `VacuumCoupling`; the vacuum
crossing clauses are now theorems. -/
theorem vacuumCoupling_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCoupling q R V De) : VacuumCoupling q R V f := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hsign⟩ := hc
  exact ⟨vacEdge q R V, c, De, hbef, haft,
    ⟨1, one_pos, fun t _ => joint_of_soft hq hR hroom hVc hV0 hs t⟩,
    deriv_of_soft hV0 hs, hc0, hsign⟩

/-- Pre-crossing separation at every small curvature from soft regularity and a positive
coupling at the canonical crossing (the profile itself, no reflection). -/
theorem pathSeparation_eventually_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hVc : AdalyFormal.D1Literal.ContFam V) (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCouplingPos q R V De) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hpos⟩ := hc
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - vacEdge q R V| < η₀ → ∀ δ : ℝ, 0 < δ →
      ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨1, one_pos, fun t _ => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t
      (joint_of_soft hq hR hroom hVc hV0 hs t)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) (deriv_of_soft hV0 hs)
  refine eventually_pathSeparation_pos hq hR hroom hVc f (vacEdge q R V) c De hbef haft hj ?_
    hc0 hpos
  intro μ hμ
  obtain ⟨r, hr, hb⟩ := hDx μ hμ
  refine ⟨r, hr, fun ε hε hεr => ?_⟩
  have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
  rw [abs_of_pos hε] at h1
  exact h1

theorem twistSeparation_of_uth {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPath q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨t, hu, hnu⟩ := h
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- A separation of the backward twist is a separation of the literal family at a negative
angle. -/
theorem twistSeparation_of_uthNeg {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPathNeg q R) (dilMask q R) ε) : TwistSeparation q R ε := by
  obtain ⟨s, hu, hnu⟩ := h
  refine ⟨-s, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-! ### The literal round-8 target -/

/-- **The remaining premise for the literal round-8 family at `(q,R)`.**  Soft regularity of
the single-defect interior family at the flat interior, and a positive first-order coupling on
the kernel of the vacuum carrier at the canonical crossing of the twist run forwards OR run
backwards.  NOT proved here. -/
def TwistSoftCoupling (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧
      (CanonicalCouplingPos q R (uthPath q R) De ∨ CanonicalCouplingPos q R (uthPathNeg q R) De)

theorem twistSeparation_eventually {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) (h : TwistSoftCoupling q R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε := by
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom (uthPath_cont q R)
      (uthPath_anFam q R) (uthPath_zero q R) hloc (vacA_uth_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uth (hall ε h1 h2)⟩
  · obtain ⟨ε₀, hε₀, hall⟩ := pathSeparation_eventually_of_soft hq hR hroom
      (uthPathNeg_cont q R) (uthPathNeg_anFam q R) (uthPathNeg_zero q R) hloc
      (vacA_uthNeg_pi_negative hq hR hroom) hs hc
    exact ⟨ε₀, hε₀, fun ε h1 h2 => twistSeparation_of_uthNeg (hall ε h1 h2)⟩

/-- The cofinal form of the reduced premise, with the pinned quantifiers. -/
def CofinalTwistSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCoupling (2^j) R

/-- **Main reduction (literal target).**  The reduced premise implies round 8's
`CofinalTwistSeparation`.  The vacuum crossing, the joint continuity in curvature and angle
and the sign of the separation side are theorems; the premise keeps only interior soft
regularity and a positive coupling on one of the two canonical vacuum kernels. -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) :
    CofinalTwistSeparation := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hsc⟩ := hRs (max R₀ R₁)
  refine ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  obtain ⟨ε₀, hε₀, hall⟩ := twistSeparation_eventually hq hR hR18
    (hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18) hsc
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

theorem goalNeg2_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCoupling h)

theorem not_cofinalTwistSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSoftCoupling :=
  fun h' => goalNeg2_of_cofinalTwistSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-! ### Free profile, either sign -/

/-- **The weakest premise of this round at `(q,R)`.**  Some bounded interior profile whose
interior family is softly regular, with a definite first-order coupling (of either sign) on
the canonical vacuum kernel of the twist run forwards or backwards.  NOT proved here. -/
def PathSoftCoupling (q R : ℕ) : Prop :=
  ∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      InteriorSoft q R f De ∧
        (CanonicalCoupling q R (uthPath q R) De ∨ CanonicalCoupling q R (uthPathNeg q R) De)

def CofinalPathSoftCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    PathSoftCoupling (2^j) R

theorem pathSoftCoupling_of_twist {q R : ℕ} (h : TwistSoftCoupling q R) : PathSoftCoupling q R := by
  obtain ⟨De, hs, hc | hc⟩ := h
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inl ⟨c, hc0, Or.inl hpos⟩⟩
  · obtain ⟨c, hc0, hpos⟩ := hc
    exact ⟨dilMask q R, dilMask_bound q R, De, hs, Or.inr ⟨c, hc0, Or.inl hpos⟩⟩

theorem cofinalPathSoftCoupling_of_twist (h : CofinalTwistSoftCoupling) :
    CofinalPathSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, pathSoftCoupling_of_twist hv⟩

theorem cofinalVacuumCoupling_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) :
    CofinalVacuumCoupling := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h (max j₀ j₁)
  obtain ⟨R₁, hR₁⟩ := hj₁ j (le_trans (le_max_right _ _) hj)
  refine ⟨j, le_trans (le_max_left _ _) hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, f, hf, De, hs, hc⟩ := hRs (max R₀ R₁)
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  have hloc := hR₁ R (le_trans (le_max_right _ _) hRR) hR hR18
  rcases hc with hc | hc
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPath (2^j) R, uthPath_cont _ _, f, hf,
      vacuumCoupling_of_soft hq hR hroom (uthPath_cont _ _) (uthPath_anFam _ _)
        (uthPath_zero _ _) hloc (vacA_uth_pi_negative hq hR hroom) hs hc⟩
  · exact ⟨R, le_trans (le_max_left _ _) hRR, hR, hR18, uthPathNeg (2^j) R, uthPathNeg_cont _ _,
      f, hf, vacuumCoupling_of_soft hq hR hroom (uthPathNeg_cont _ _) (uthPathNeg_anFam _ _)
        (uthPathNeg_zero _ _) hloc (vacA_uthNeg_pi_negative hq hR hroom) hs hc⟩

/-- **Main reduction (weakest premise).** -/
theorem goalNeg2_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_cofinalPathSoftCoupling h)

theorem not_cofinalPathSoftCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathSoftCoupling :=
  fun h' => goalNeg2_of_cofinalPathSoftCoupling h' (goalPos2_iff_goalPos1.mpr h)

#print axioms pathU_anFam
#print axioms uthPath_anFam
#print axioms uthPathNeg
#print axioms uthPathNeg_cont
#print axioms uthPathNeg_anFam
#print axioms uthPath_zero
#print axioms uthPathNeg_zero
#print axioms pathA_anR
#print axioms pathA_isolated
#print axioms pathC_isolated
#print axioms inner_Ginv_dataS
#print axioms flat_delta_le_univ
#print axioms mass_nonneg_dataS
#print axioms Ginv_loc_psd_flat
#print axioms Ginv_loc_le_all_flat
#print axioms Ginv_all_pd_flat
#print axioms flatP
#print axioms dilU_flat
#print axioms flat_loc_unit_eventually
#print axioms pathU_flat_base
#print axioms vacA_zero_flat
#print axioms vacA_pd_zero
#print axioms vacA_uth_pi_negative
#print axioms uθ_neg_pi
#print axioms uthPath_neg_pi
#print axioms vacA_uthNeg_pi_negative
#print axioms vacEdge
#print axioms VacuumCrossesAt
#print axioms vacuum_crossing
#print axioms twist_vacuum_crossing
#print axioms twist_isolated_nonunits
#print axioms uMat_continuous'
#print axioms Ug_coe_uMat
#print axioms pathU_contFamY
#print axioms pathA_jointly_continuousAt
#print axioms bulkU
#print axioms bulkP
#print axioms bulkA
#print axioms bulkD
#print axioms InteriorSoft
#print axioms pathU_base
#print axioms pathP_base
#print axioms pathA_base
#print axioms pathD_base
#print axioms joint_of_soft
#print axioms deriv_of_soft
#print axioms CanonicalCoupling
#print axioms CanonicalCouplingPos
#print axioms vacuumCoupling_of_soft
#print axioms pathSeparation_eventually_of_soft
#print axioms twistSeparation_of_uth
#print axioms twistSeparation_of_uthNeg
#print axioms TwistSoftCoupling
#print axioms twistSeparation_eventually
#print axioms CofinalTwistSoftCoupling
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCoupling
#print axioms goalNeg2_of_cofinalTwistSoftCoupling
#print axioms not_cofinalTwistSoftCoupling_of_goalPos1
#print axioms PathSoftCoupling
#print axioms CofinalPathSoftCoupling
#print axioms pathSoftCoupling_of_twist
#print axioms cofinalPathSoftCoupling_of_twist
#print axioms cofinalVacuumCoupling_of_cofinalPathSoftCoupling
#print axioms goalNeg2_of_cofinalPathSoftCoupling
#print axioms not_cofinalPathSoftCoupling_of_goalPos1

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The global gauge flip: the forward and backward twists are equivalent

The frozen gauge-covariance lane (`GaugeCov`, `M1GaugeW4`) proves that the localized data are
covariant under every gauge transformation, and that the plaquette Hessian is covariant for
every plaquette set; so the all-plaquette carrier is covariant as well (`Ginv_all_gauge`).  The
constant gauge transformation by `w = [[0,1],[-1,0]]` conjugates `diag(a, ā)` into `diag(ā, a)`:
it maps the curved twist at curvature `ε` and angle `t` to the curved twist at `-ε` and `-t`.
Hence the backward vacuum twist is unitarily equivalent to the forward one, the canonical
crossings coincide, and the first-order coupling changes sign between the two kernels.  A
coupling of EITHER sign on the forward kernel is therefore a positive coupling on one of the two
kernels, which is what the pre-crossing argument needs. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL adBL adSL adBL_apply iE_adEL pE_adBL adjoint_intertwine
  bondEqv_gauge deltaKLocCLM_gauge)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-! ### The all-plaquette carrier is gauge covariant -/

/-- The all-plaquette carrier at `U^γ`, applied to `Ad_γ x`, is `Ad_γ` of the carrier at `U`. -/
theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]

/-! ### The flip -/

theorem flipMat_mem :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Matrix.det_fin_two]

/-- `w = [[0,1],[-1,0]] ∈ SU(2)`. -/
noncomputable def flipElt : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨!![0, 1; -1, 0], flipMat_mem⟩

/-- The constant gauge transformation by `w`. -/
noncomputable def flipGauge {L : PeriodicLatticeExtent} : GaugeFn L := fun _ => flipElt

theorem flip_conj_uMat (t : ℝ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat t) :
    ((flipElt * g * flipElt⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = AdalyFormal.D1Literal.uMat (-t) := by
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) *
    star (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem flip_uθ (t : ℝ) :
    flipElt * AdalyFormal.D1Literal.uθ t * flipElt⁻¹ = AdalyFormal.D1Literal.uθ (-t) :=
  Subtype.ext (flip_conj_uMat t _ rfl)

theorem flip_Ug (s : ℝ) : flipElt * Ug s * flipElt⁻¹ = Ug (-s) := by
  apply Subtype.ext
  rw [flip_conj_uMat s (Ug s) (Ug_coe_uMat s), Ug_coe_uMat]

theorem flip_one : flipElt * (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) * flipElt⁻¹ = 1 := by
  rw [mul_one, mul_inv_cancel]

theorem flip_maskedU (q R : ℕ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform flipGauge (maskedU q R g V) =
      maskedU q R (fun e => -g e) (periodicGaugeTransform flipGauge V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, flipGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, flipGauge]
    exact flip_Ug (g e)

theorem flip_uthPath (q R : ℕ) (t : ℝ) :
    periodicGaugeTransform flipGauge (uthPath q R t) = uthPath q R (-t) := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, flipGauge]
  split_ifs
  · exact flip_uθ t
  · exact flip_one

theorem flip_trivial (L : PeriodicLatticeExtent) :
    periodicGaugeTransform (flipGauge (L := L))
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  exact flip_one

theorem flip_pathU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform flipGauge (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f (-ε) (-t) := by
  unfold pathU
  rw [flip_maskedU, flip_uthPath]
  congr 1
  funext e
  ring

theorem flip_bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform flipGauge (bulkU q R f ε) = bulkU q R f (-ε) := by
  unfold bulkU
  rw [flip_maskedU, flip_trivial]
  congr 1
  funext e
  ring

/-! ### Consequences for the twist -/

/-- The flip maps the carrier at `(ε, t)` to the carrier at `(-ε, -t)`. -/
theorem pathA_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    pathA q R (uthPath q R) f (-ε) 1 (-t) (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (pathA q R (uthPath q R) f ε 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) f ε t) 1 (dilLam q R) flipGauge x
  rw [flip_pathU] at h
  exact h

/-- **The backward vacuum twist is unitarily equivalent to the forward one.** -/
theorem vacA_flip (q R : ℕ) (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPathNeg q R) 1 t (adEL flipGauge (geomOf 2 1 (dilTower q R)) x) =
      adEL flipGauge (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := pathA_flip q R (fun _ => 0) 0 t x
  rw [neg_zero] at h
  exact h

theorem vacA_flip_psd (q R : ℕ) (t : ℝ) :
    PSD (vacA q R (uthPathNeg q R) 1 t) ↔ PSD (vacA q R (uthPath q R) 1 t) := by
  constructor
  · intro h x
    have h1 := h (adEL flipGauge (geomOf 2 1 (dilTower q R)) x)
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map] at h1
    exact h1
  · intro h y
    obtain ⟨x, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective y
    rw [vacA_flip, LinearIsometryEquiv.inner_map_map]
    exact h x

/-- The canonical crossings of the forward and backward twists coincide. -/
theorem vacEdge_flip (q R : ℕ) : vacEdge q R (uthPathNeg q R) = vacEdge q R (uthPath q R) := by
  have hS : {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPathNeg q R) 1 s)} =
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) Real.pi ∧
        ∀ s ∈ Set.Icc (0 : ℝ) t, PSD (vacA q R (uthPath q R) 1 s)} := by
    ext t
    exact and_congr_right (fun _ => forall₂_congr (fun s _ => vacA_flip_psd q R s))
  exact congrArg sSup hS

/-- The flip maps the correction at `ε` to the correction at `-ε` (quadratic forms). -/
theorem bulkD_flip (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f (-ε) (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ =
      ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) flipGauge u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f (-ε)) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [flip_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform flipGauge (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f (-ε) := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

/-- The derivative of a quadratic form of a differentiable operator family. -/
theorem hasDerivAt_quadForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v : E) :
    HasDerivAt (fun ε => ⟪v, D ε v⟫) ⟪v, De v⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- **The coupling is odd under the flip**: on the image of a vector under the flip the
first-order coefficient has the opposite quadratic form. -/
theorem De_flip {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫ := by
  have h1 := hasDerivAt_quadForm hD u
  have h2 := hasDerivAt_quadForm hD (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)
  have h2' : HasDerivAt (fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫)
      ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
        De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ (-0) := by
    rw [neg_zero]; exact h2
  have h3 := h2'.comp (0 : ℝ) (hasDerivAt_neg' (x := (0 : ℝ)))
  have e : ((fun ε : ℝ => ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫) ∘ fun x : ℝ => -x) =
      fun ε => ⟪u, bulkD q R f ε u⟫ := by
    funext ε
    exact bulkD_flip q R f ε u
  rw [e] at h3
  have h4 := h3.unique h1
  rw [mul_neg_one] at h4
  linarith

/-- A negative coupling on the forward canonical kernel is a positive coupling on the backward
one. -/
theorem couplingPos_back {q R : ℕ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hflip : ∀ u, ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫)
    {c : ℝ} (hneg : ∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫) :
    ∀ u', vacA q R (uthPathNeg q R) 1 (vacEdge q R (uthPathNeg q R)) u' = 0 →
      c * ‖u'‖ ^ 2 ≤ ⟪u', De u'⟫ := by
  intro u' hu'
  obtain ⟨u, rfl⟩ := (adEL flipGauge (geomOf 2 1 (dilTower q R))).surjective u'
  rw [vacEdge_flip, vacA_flip] at hu'
  have hu : vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 :=
    (map_eq_zero_iff _ (adEL flipGauge (geomOf 2 1 (dilTower q R))).injective).mp hu'
  rw [LinearIsometryEquiv.norm_map, hflip]
  exact hneg u hu

/-! ### The literal target with one kernel -/

/-- **The reduced premise for the literal round-8 family at `(q,R)`, one kernel.**  Soft
regularity of the single-defect interior family at the flat interior, and a first-order
coefficient that is definite, of EITHER sign, on the kernel of the vacuum carrier at the
canonical crossing of the forward twist.  NOT proved here. -/
def TwistSoftCouplingFwd (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalCoupling q R (uthPath q R) De

theorem twistSoftCoupling_of_fwd {q R : ℕ} (h : TwistSoftCouplingFwd q R) :
    TwistSoftCoupling q R := by
  obtain ⟨De, hs, c, hc, hpos | hneg⟩ := h
  · exact ⟨De, hs, Or.inl ⟨c, hc, hpos⟩⟩
  · exact ⟨De, hs, Or.inr ⟨c, hc, couplingPos_back (De_flip hs.2.2) hneg⟩⟩

def CofinalTwistSoftCouplingFwd : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCouplingFwd (2^j) R

theorem cofinalTwistSoftCoupling_of_fwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSoftCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCoupling_of_fwd hv⟩

/-- **Main reduction of this round (literal target, one kernel, either sign).** -/
theorem cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSeparation :=
  cofinalTwistSeparation_of_cofinalTwistSoftCoupling (cofinalTwistSoftCoupling_of_fwd h)

theorem goalNeg2_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd h)

theorem not_cofinalTwistSoftCouplingFwd_of_goalPos1 (h : GoalPos1) :
    ¬ CofinalTwistSoftCouplingFwd :=
  fun h' => goalNeg2_of_cofinalTwistSoftCouplingFwd h' (goalPos2_iff_goalPos1.mpr h)

/-- **Per instance.**  At every large scale and every large even radius, the reduced premise at
that instance gives a separation of the literal family at every small positive curvature. -/
theorem twistSeparation_eventually_of_fwd :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      TwistSoftCouplingFwd (2^j) R →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation (2^j) R ε := by
  obtain ⟨j₁, hj₁⟩ := flat_loc_unit_eventually
  refine ⟨j₁, fun j hj => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hj₁ j hj
  refine ⟨R₁, fun R hR hR2 hR18 h => ?_⟩
  exact twistSeparation_eventually (by positivity) hR2 hR18 (hR₁ R hR hR2 hR18)
    (twistSoftCoupling_of_fwd h)

/-- What the positive reading demands, stated directly: at every large scale and every large
even radius the reduced premise fails, i.e. the interior family is not softly regular or the
first-order coupling is not definite on the canonical forward vacuum kernel. -/
theorem goalPos1_forces_no_softCoupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ TwistSoftCouplingFwd (2^j) R := by
  have h' := not_cofinalTwistSoftCouplingFwd_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  exact ⟨R, hRR, hR2, hR18, not_not.mp hR4⟩

#print axioms Ginv_all_gauge
#print axioms flipMat_mem
#print axioms flipElt
#print axioms flipGauge
#print axioms flip_conj_uMat
#print axioms flip_uθ
#print axioms flip_Ug
#print axioms flip_one
#print axioms flip_maskedU
#print axioms flip_uthPath
#print axioms flip_trivial
#print axioms flip_pathU
#print axioms flip_bulkU
#print axioms pathA_flip
#print axioms vacA_flip
#print axioms vacA_flip_psd
#print axioms vacEdge_flip
#print axioms bulkD_flip
#print axioms hasDerivAt_quadForm
#print axioms De_flip
#print axioms couplingPos_back
#print axioms TwistSoftCouplingFwd
#print axioms twistSoftCoupling_of_fwd
#print axioms CofinalTwistSoftCouplingFwd
#print axioms cofinalTwistSoftCoupling_of_fwd
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd
#print axioms goalNeg2_of_cofinalTwistSoftCouplingFwd
#print axioms not_cofinalTwistSoftCouplingFwd_of_goalPos1
#print axioms twistSeparation_eventually_of_fwd
#print axioms goalPos1_forces_no_softCoupling

end AdalyFormal.Round9.Guarded.QualitativeR2

/-! ## The diagonal `U(1)`: the coupling is a single number on a charged complex line

Every link of the curved twist family is diagonal, so the constant gauge rotations
`diag(e^{iα}, e^{-iα})` leave the configuration unchanged.  By the frozen covariance lane the
vacuum carrier and the correction commute with the induced orthogonal maps `J_α`.  Hence, if the
canonical vacuum kernel is the complex line spanned by a charged vector `u₀` and `J u₀`
(`J = J_{π/4}`, `J (J u₀) = -u₀`), the first-order coefficient acts on it as the scalar
`⟪u₀, De u₀⟫ / ‖u₀‖²`, and the coupling premise is exactly `⟪u₀, De u₀⟫ ≠ 0`: round 8's
`c₁(q,R) ≠ 0`.  Round 9.1 assumed the commutation; here it is proved. -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The constant diagonal gauge rotation by `diag(e^{iα}, e^{-iα})`. -/
noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α

theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem uθ_conj (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s * (AdalyFormal.D1Literal.uθ α)⁻¹ =
      AdalyFormal.D1Literal.uθ s := by
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem Ug_eq_uθ (s : ℝ) : Ug s = AdalyFormal.D1Literal.uθ s :=
  Subtype.ext (Ug_coe_uMat s)

theorem rot_maskedU (q R : ℕ) (α : ℝ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform (rotGauge α) (maskedU q R g V) =
      maskedU q R g (periodicGaugeTransform (rotGauge α) V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, rotGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, rotGauge, Ug_eq_uθ]
    exact uθ_conj α (g e)

theorem rot_uthPath (q R : ℕ) (α t : ℝ) :
    periodicGaugeTransform (rotGauge α) (uthPath q R t) = uthPath q R t := by
  classical
  funext e
  simp only [periodicGaugeTransform, uthPath, AdalyFormal.D1Literal.Uth, rotGauge]
  split_ifs
  · exact uθ_conj α t
  · rw [mul_one, mul_inv_cancel]

theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]

theorem rot_pathU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    periodicGaugeTransform (rotGauge α) (pathU q R (uthPath q R) f ε t) =
      pathU q R (uthPath q R) f ε t := by
  unfold pathU
  rw [rot_maskedU, rot_uthPath]

theorem rot_bulkU (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    periodicGaugeTransform (rotGauge α) (bulkU q R f ε) = bulkU q R f ε := by
  unfold bulkU
  rw [rot_maskedU, rot_trivial]

/-- The vacuum carrier of the twist commutes with every diagonal rotation. -/
theorem vacA_rot (q R : ℕ) (α t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    vacA q R (uthPath q R) 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) x) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R (uthPath q R) 1 t x) := by
  have h := Ginv_all_gauge (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R (uthPath q R) (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) x
  rw [rot_pathU] at h
  exact h

/-- The correction has rotation-invariant quadratic form. -/
theorem bulkD_rot (q R : ℕ) (α : ℝ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u,
      bulkD q R f ε (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)⟫ = ⟪u, bulkD q R f ε u⟫ := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  have h := AdalyFormal.M1GaugeW4.delta2_gauge (ell := 2) (k := 1) (Lu := dilLu q R) h2
    (dilTower q R) 1 (dilLam q R) (bulkU q R f ε) (rotGauge α) u
  have heq : ∀ (d d' : BaseDataS ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  have hd1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := by
    show dataS selIn selIn (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)) = _
    unfold bulkP
    rw [rot_bulkU]
  have hd2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data =
      dataS selIn selIn (bulkP q R f ε) := rfl
  have e1 : (gparams 2 1 (dilLu q R) h2 (dilTower q R)
      (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R)
        (periodicGaugeTransform (rotGauge α) (bulkU q R f ε)) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd1 _ _
  have e2 : (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data.Delta2
      (gparams 2 1 (dilLu q R) h2 (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)).data_laws =
      bulkD q R f ε := heq _ _ hd2 _ _
  rw [e1, e2] at h
  exact h

/-- The derivative of a matrix coefficient of a differentiable operator family. -/
theorem hasDerivAt_bilin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : ℝ → E →L[ℝ] E} {De : E →L[ℝ] E} {x₀ : ℝ} (hD : HasDerivAt D De x₀) (v w : E) :
    HasDerivAt (fun ε => ⟪v, D ε w⟫) ⟪v, De w⟫ x₀ := by
  have hL : HasFDerivAt ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w))
      ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)) (D x₀) :=
    ((innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E w)).hasFDerivAt
  exact hL.comp_hasDerivAt x₀ hD

/-- The first-order coefficient of the correction is symmetric. -/
theorem De_symm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : ⟪De x, y⟫ = ⟪x, De y⟫ := by
  have h1 := hasDerivAt_bilin hD y x
  have h2 := hasDerivAt_bilin hD x y
  have e : (fun ε : ℝ => ⟪y, bulkD q R f ε x⟫) = fun ε => ⟪x, bulkD q R f ε y⟫ := by
    funext ε
    exact (real_inner_comm (bulkD q R f ε x) y).trans
      (((dataS selIn selIn (bulkP q R f ε)).Delta2_spec (dataS_laws selIn selIn _)).1 x y)
  rw [e] at h1
  rw [real_inner_comm]
  exact h1.unique h2

/-- The first-order coefficient commutes with every diagonal rotation. -/
theorem De_rot_comm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (α : ℝ)
    (y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    De (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) y) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (De y) := by
  set J := adEL (rotGauge α) (geomOf 2 1 (dilTower q R))
  have hq : ∀ u, ⟪J u, De (J u)⟫ = ⟪u, De u⟫ := by
    intro u
    have h1 := hasDerivAt_quadForm hD (J u)
    have h2 := hasDerivAt_quadForm hD u
    have e : (fun ε : ℝ => ⟪J u, bulkD q R f ε (J u)⟫) = fun ε => ⟪u, bulkD q R f ε u⟫ :=
      funext (fun ε => bulkD_rot q R α f ε u)
    rw [e] at h1
    exact h1.unique h2
  have hb : ∀ x, ⟪J x, De (J y)⟫ = ⟪x, De y⟫ := by
    intro x
    have h := hq (x + y)
    have hx := hq x
    have hy := hq y
    have hs1 : ⟪J y, De (J x)⟫ = ⟪J x, De (J y)⟫ := by
      rw [← De_symm hD, real_inner_comm]
    have hs2 : ⟪y, De x⟫ = ⟪x, De y⟫ := by
      rw [← De_symm hD, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right] at h
    linarith
  refine ext_inner_left ℝ (fun v => ?_)
  obtain ⟨x, rfl⟩ := J.surjective v
  rw [hb x, LinearIsometryEquiv.inner_map_map]

/-- **Complex-line form of the coupling premise.**  The canonical forward vacuum kernel lies in
the plane spanned by a nonzero vector `u₀` and `J u₀`, where `J` is the quarter rotation and
`J (J u₀) = -u₀` (`u₀` is charged), and `⟪u₀, De u₀⟫ ≠ 0`.  NOT proved here. -/
def CanonicalU1Line (q R : ℕ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))), u₀ ≠ 0 ∧
    vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u₀ = 0 ∧
    adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
    (∀ u, vacA q R (uthPath q R) 1 (vacEdge q R (uthPath q R)) u = 0 →
      u ∈ Submodule.span ℝ {u₀, adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀}) ∧
    ⟪u₀, De u₀⟫ ≠ 0

/-- On a charged complex line the coupling is the single number `⟪u₀, De u₀⟫`; its
nonvanishing is the definite coupling of the reduced premise. -/
theorem canonicalCoupling_of_U1 {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (h : CanonicalU1Line q R De) :
    CanonicalCoupling q R (uthPath q R) De := by
  obtain ⟨u₀, hu₀, -, hJJ, hK, hc⟩ := h
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  let Jop : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    J.toLinearIsometry.toContinuousLinearMap
  obtain ⟨l, hl⟩ := scalar_on_complex_line De Jop (De_symm hD)
    (fun x y => LinearIsometryEquiv.inner_map_map J x y)
    (fun x => De_rot_comm hD (Real.pi / 4) x) u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, Jop u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hl0 : l ≠ 0 := by
    intro h0
    apply hc
    rw [hl u₀ hmem, h0, zero_mul]
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · refine ⟨-l, by linarith, Or.inr (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith
  · refine ⟨l, hpos, Or.inl (fun u hu => ?_)⟩
    have h1 := hl u (hK u hu)
    linarith

/-- The literal reduced premise in complex-line form. -/
def TwistSoftU1 (q R : ℕ) : Prop :=
  ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
    InteriorSoft q R (dilMask q R) De ∧ CanonicalU1Line q R De

theorem twistSoftCouplingFwd_of_U1 {q R : ℕ} (h : TwistSoftU1 q R) : TwistSoftCouplingFwd q R := by
  obtain ⟨De, hs, hc⟩ := h
  exact ⟨De, hs, canonicalCoupling_of_U1 hs.2.2 hc⟩

def CofinalTwistSoftU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ TwistSoftU1 (2^j) R

theorem cofinalTwistSeparation_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) :
    CofinalTwistSeparation := by
  refine cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (fun j₀ => ?_)
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, twistSoftCouplingFwd_of_U1 hv⟩

theorem goalNeg2_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) : GoalNeg2 :=
  goalNeg2_of_cofinalTwistSeparation (cofinalTwistSeparation_of_cofinalTwistSoftU1 h)

#print axioms rotGauge
#print axioms uθ_comm
#print axioms uθ_conj
#print axioms Ug_eq_uθ
#print axioms rot_maskedU
#print axioms rot_uthPath
#print axioms rot_trivial
#print axioms rot_pathU
#print axioms rot_bulkU
#print axioms vacA_rot
#print axioms bulkD_rot
#print axioms hasDerivAt_bilin
#print axioms De_symm
#print axioms De_rot_comm
#print axioms CanonicalU1Line
#print axioms canonicalCoupling_of_U1
#print axioms TwistSoftU1
#print axioms twistSoftCouplingFwd_of_U1
#print axioms CofinalTwistSoftU1
#print axioms cofinalTwistSeparation_of_cofinalTwistSoftU1
#print axioms goalNeg2_of_cofinalTwistSoftU1

end AdalyFormal.Round9.Guarded.QualitativeR2

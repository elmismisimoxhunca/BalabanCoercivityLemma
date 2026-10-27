import Mathlib

/-!
# DL63 -- the second derivative from the EVEN PART, at value level (Mathlib only)

**`second_deriv_le_of_even`** : if `f` is `C²` at `0`, `π` is a continuous linear map, and for all `0 < t ≤ t0`
  `‖π (f(tb) + f(−tb) − 2 f(0))‖ ≤ M t²`,
then `‖π (D²f(0)(b,b))‖ ≤ M`.

Proof: `g(s) = π(f(sb) + f(−sb) − 2f(0)) − s²·π(D²f(0)(b,b))` has `g(0) = 0` and
`g'(s) = π([Df(sb) − Df(0) − D²f(0)(sb)]b − [Df(−sb) − Df(0) − D²f(0)(−sb)]b)`, which is `o(s)` by the Fréchet
differentiability of `Df` at `0`; the mean value inequality gives `‖g(t)‖ <= 2‖π‖ε t²‖b‖²`, and `ε → 0`.
No derivative is evaluated at a point where differentiability is not proved: `f` is differentiable on a
ball around `0` (from `ContDiffAt`), and only that ball is used.
-/
set_option autoImplicit false

namespace AdalyFormal.DLayer.EvenLimit

open Set Filter Topology Asymptotics

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- the two facts used from `C²`: differentiability on a ball, and the little-o of `Df` at `0`. -/
theorem c2_facts (f : E → F) (hf : ContDiffAt ℝ 2 f 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : E, ‖y‖ < δ → DifferentiableAt ℝ f y ∧
      ‖fderiv ℝ f y - fderiv ℝ f 0 - fderiv ℝ (fderiv ℝ f) 0 y‖ ≤ ε * ‖y‖ := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) 0 :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.mp hD
  have ho' := ho.def hε
  simp only [zero_add] at ho'
  have hboth := hev.and ho'
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hboth
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hy' : dist y 0 < δ := by rwa [dist_zero_right]
  obtain ⟨hc, hb⟩ := hball hy'
  exact ⟨hc.differentiableAt (by norm_num), hb⟩

/-- **the second derivative from the even part.** -/
theorem second_deriv_le_of_even (f : E → F) (hf : ContDiffAt ℝ 2 f 0) (π : F →L[ℝ] G) (b : E) (M t0 : ℝ)
    (ht0 : 0 < t0)
    (h : ∀ t : ℝ, 0 < t → t ≤ t0 → ‖π (f (t • b) + f (-(t • b)) - (2 : ℝ) • f 0)‖ ≤ M * t ^ 2) :
    ‖π (fderiv ℝ (fderiv ℝ f) 0 b b)‖ ≤ M := by
  set L2 := fderiv ℝ (fderiv ℝ f) 0 with hL2
  set v : G := π (L2 b b) with hv
  -- it suffices: ∀ ε > 0, ‖v‖ ≤ M + 2‖π‖ε‖b‖²
  have key : ∀ ε : ℝ, 0 < ε → ‖v‖ ≤ M + 2 * ‖π‖ * ε * ‖b‖ ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := c2_facts f hf ε hε
    -- choose t
    set t : ℝ := min t0 (δ / (2 * (‖b‖ + 1))) with htdef
    have hb1 : 0 < ‖b‖ + 1 := by positivity
    have htpos : 0 < t := lt_min ht0 (by positivity)
    have htt0 : t ≤ t0 := min_le_left _ _
    have htb : t * ‖b‖ < δ := by
      have h1 : t ≤ δ / (2 * (‖b‖ + 1)) := min_le_right _ _
      have h2 : t * ‖b‖ ≤ δ / (2 * (‖b‖ + 1)) * (‖b‖ + 1) :=
        mul_le_mul h1 (by linarith) (norm_nonneg _) (by positivity)
      have h3 : δ / (2 * (‖b‖ + 1)) * (‖b‖ + 1) = δ / 2 := by field_simp
      linarith
    -- the auxiliary function
    set g : ℝ → G := fun s => π (f (s • b) + f (-(s • b)) - (2 : ℝ) • f 0) - (s ^ 2) • v with hg
    set g' : ℝ → G := fun s => π (fderiv ℝ f (s • b) b - fderiv ℝ f (-(s • b)) b) - (2 * s) • v with hg'
    have hsmall : ∀ s ∈ Icc (0 : ℝ) t, ‖s • b‖ < δ ∧ ‖-(s • b)‖ < δ := by
      intro s hs
      have e1 : ‖s • b‖ = s * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
      have e2 : s * ‖b‖ ≤ t * ‖b‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      rw [norm_neg, e1]; exact ⟨by linarith, by linarith⟩
    have hderiv : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt g (g' s) (Icc 0 t) s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hsmall s hs
      have hd1 := (hball _ hs1).1
      have hd2 := (hball _ hs2).1
      have hl1 : HasDerivAt (fun s : ℝ => s • b) b s := by
        simpa using (hasDerivAt_id s).smul_const b
      have hl2 : HasDerivAt (fun s : ℝ => -(s • b)) (-b) s := hl1.neg
      have hf1 : HasDerivAt (fun s : ℝ => f (s • b)) (fderiv ℝ f (s • b) b) s :=
        hd1.hasFDerivAt.comp_hasDerivAt s hl1
      have hf2 : HasDerivAt (fun s : ℝ => f (-(s • b))) (fderiv ℝ f (-(s • b)) (-b)) s :=
        hd2.hasFDerivAt.comp_hasDerivAt s hl2
      have hsum : HasDerivAt (fun s : ℝ => f (s • b) + f (-(s • b)) - (2 : ℝ) • f 0)
          (fderiv ℝ f (s • b) b + fderiv ℝ f (-(s • b)) (-b)) s := by
        simpa using (hf1.add hf2).sub_const ((2 : ℝ) • f 0)
      have hpi : HasDerivAt (fun s : ℝ => π (f (s • b) + f (-(s • b)) - (2 : ℝ) • f 0))
          (π (fderiv ℝ f (s • b) b + fderiv ℝ f (-(s • b)) (-b))) s :=
        π.hasFDerivAt.comp_hasDerivAt s hsum
      have hsq : HasDerivAt (fun s : ℝ => (s ^ 2) • v) ((2 * s) • v) s := by
        have := (hasDerivAt_pow 2 s).smul_const v
        simpa using this
      have hall := hpi.sub hsq
      have e : π (fderiv ℝ f (s • b) b + fderiv ℝ f (-(s • b)) (-b)) - (2 * s) • v = g' s := by
        simp only [hg', map_neg, sub_eq_add_neg]
      rw [e] at hall
      exact hall.hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖g' s‖ ≤ 2 * ‖π‖ * ε * t * ‖b‖ ^ 2 := by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
      obtain ⟨hs1, hs2⟩ := hsmall s hs'
      have hb1 := (hball _ hs1).2
      have hb2 := (hball _ hs2).2
      set D1 := fderiv ℝ f (s • b) - fderiv ℝ f 0 - L2 (s • b) with hD1
      set D2 := fderiv ℝ f (-(s • b)) - fderiv ℝ f 0 - L2 (-(s • b)) with hD2
      have e : g' s = π (D1 b - D2 b) := by
        simp only [hg', hD1, hD2, hv, ContinuousLinearMap.sub_apply, map_neg, map_smul,
          ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, map_sub]
        rw [two_mul, add_smul]
        abel
      rw [e]
      have hn1 : ‖D1 b‖ ≤ ε * (s * ‖b‖) * ‖b‖ := by
        have := (D1.le_opNorm b)
        have h' : ‖s • b‖ = s * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
        rw [h'] at hb1
        exact this.trans (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))
      have hn2 : ‖D2 b‖ ≤ ε * (s * ‖b‖) * ‖b‖ := by
        have := (D2.le_opNorm b)
        have h' : ‖-(s • b)‖ = s * ‖b‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hs.1]
        rw [h'] at hb2
        exact this.trans (mul_le_mul_of_nonneg_right hb2 (norm_nonneg _))
      have hst : s ≤ t := hs.2.le
      calc ‖π (D1 b - D2 b)‖ ≤ ‖π‖ * ‖D1 b - D2 b‖ := π.le_opNorm _
        _ ≤ ‖π‖ * (ε * (s * ‖b‖) * ‖b‖ + ε * (s * ‖b‖) * ‖b‖) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hn1 hn2)) (norm_nonneg _)
        _ = 2 * ‖π‖ * ε * s * ‖b‖ ^ 2 := by ring
        _ ≤ 2 * ‖π‖ * ε * t * ‖b‖ ^ 2 := by
          have : 0 ≤ 2 * ‖π‖ * ε := by positivity
          have h2 : 0 ≤ ‖b‖ ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hst this]
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨htpos.le, le_rfl⟩
    have hg0 : g 0 = 0 := by
      simp only [hg, zero_smul, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [two_smul, sub_self, map_zero, sub_zero]
    rw [hg0, sub_zero, sub_zero] at hmv
    -- ‖t² v‖ ≤ ‖π(...)‖ + ‖g t‖
    have hgt : (t ^ 2) • v = π (f (t • b) + f (-(t • b)) - (2 : ℝ) • f 0) - g t := by
      simp only [hg]; abel
    have ht2 : t ^ 2 * ‖v‖ ≤ M * t ^ 2 + 2 * ‖π‖ * ε * t * ‖b‖ ^ 2 * t := by
      have e1 : ‖(t ^ 2) • v‖ = t ^ 2 * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [← e1, hgt]
      exact (norm_sub_le _ _).trans (add_le_add (h t htpos htt0) hmv)
    have htsq : 0 < t ^ 2 := by positivity
    have : ‖v‖ ≤ M + 2 * ‖π‖ * ε * ‖b‖ ^ 2 := by
      have e : M * t ^ 2 + 2 * ‖π‖ * ε * t * ‖b‖ ^ 2 * t = t ^ 2 * (M + 2 * ‖π‖ * ε * ‖b‖ ^ 2) := by ring
      rw [e] at ht2
      exact le_of_mul_le_mul_left ht2 htsq
    exact this
  -- conclude
  refine le_of_forall_pos_lt_add (fun ε' hε' => ?_)
  set c : ℝ := 2 * ‖π‖ * ‖b‖ ^ 2 + 1 with hc
  have hcpos : 0 < c := by positivity
  have h1 := key (ε' / (2 * c)) (by positivity)
  have h2 : 2 * ‖π‖ * (ε' / (2 * c)) * ‖b‖ ^ 2 < ε' := by
    have e : 2 * ‖π‖ * (ε' / (2 * c)) * ‖b‖ ^ 2 = ε' * ((2 * ‖π‖ * ‖b‖ ^ 2) / (2 * c)) := by
      field_simp
    rw [e]
    have h3 : (2 * ‖π‖ * ‖b‖ ^ 2) / (2 * c) < 1 := by
      rw [div_lt_one (by positivity)]
      have : 0 ≤ 2 * ‖π‖ * ‖b‖ ^ 2 := by positivity
      nlinarith
    nlinarith
  linarith

#print axioms c2_facts
#print axioms second_deriv_le_of_even

end AdalyFormal.DLayer.EvenLimit

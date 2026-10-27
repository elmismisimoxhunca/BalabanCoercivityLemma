import DLR67
import DLR72

/-!
# DL77 -- the second derivative is DETERMINED by the even part; locality of the composite second jet on the footprints

* `even_approx` (Mathlib-level): for `f` `C²` at `0`: `‖π(f(tb)+f(−tb)−2f(0)) − t² π(D²f(0)(b,b))‖ ≤ ε t²` for small `t > 0`;
* **`second_deriv_eq_of_even`** : equal even parts along `b`, `b'` (for small `t`) ⇒ `π(D²f(0)(b,b)) = π(D²f(0)(b',b'))`;
* **`C2StepX_row_congr`** : the row `c` of the one-step second jet reads only `VisStep s ℓ c` (from `qStepX_congr`, DL27);
* **`C2CompX_row_congr`** : the row `c` of the level-`j` composite second jet reads only the footprint `Foot ℓ j c`
  (induction through `C2CompX_succ` with DL28 `QlinCompX_row_local`).
Differentiability is stated where derivatives are used (`RegBg`/`RegTower` ⇒ `ContDiffAt`), no junk value is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer.EvenLimit

open Set Filter Topology Asymptotics

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem even_approx (f : E → F) (hf : ContDiffAt ℝ 2 f 0) (π : F →L[ℝ] G) (b : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      ‖π (f (t • b) + f (-(t • b)) - (2 : ℝ) • f 0) - (t ^ 2) • π (fderiv ℝ (fderiv ℝ f) 0 b b)‖ ≤ ε * t ^ 2 := by
  set L2 := fderiv ℝ (fderiv ℝ f) 0 with hL2
  set v : G := π (L2 b b) with hv
  set c : ℝ := 2 * ‖π‖ * ‖b‖ ^ 2 + 1 with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨δ0, hδ0, hball⟩ := c2_facts f hf (ε / c) (by positivity)
  refine ⟨δ0 / (‖b‖ + 1), by positivity, fun t htpos htδ => ?_⟩
  have htb : t * ‖b‖ < δ0 := by
    have h1 : t * (‖b‖ + 1) < δ0 := by rwa [lt_div_iff₀ (by positivity)] at htδ
    nlinarith
  set g : ℝ → G := fun s => π (f (s • b) + f (-(s • b)) - (2 : ℝ) • f 0) - (s ^ 2) • v with hg
  set g' : ℝ → G := fun s => π (fderiv ℝ f (s • b) b - fderiv ℝ f (-(s • b)) b) - (2 * s) • v with hg'
  have hsmall : ∀ s ∈ Icc (0 : ℝ) t, ‖s • b‖ < δ0 ∧ ‖-(s • b)‖ < δ0 := by
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
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖g' s‖ ≤ 2 * ‖π‖ * (ε / c) * t * ‖b‖ ^ 2 := by
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
    have hn1 : ‖D1 b‖ ≤ (ε / c) * (s * ‖b‖) * ‖b‖ := by
      have := (D1.le_opNorm b)
      have h' : ‖s • b‖ = s * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
      rw [h'] at hb1
      exact this.trans (mul_le_mul_of_nonneg_right hb1 (norm_nonneg _))
    have hn2 : ‖D2 b‖ ≤ (ε / c) * (s * ‖b‖) * ‖b‖ := by
      have := (D2.le_opNorm b)
      have h' : ‖-(s • b)‖ = s * ‖b‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg hs.1]
      rw [h'] at hb2
      exact this.trans (mul_le_mul_of_nonneg_right hb2 (norm_nonneg _))
    have hst : s ≤ t := hs.2.le
    calc ‖π (D1 b - D2 b)‖ ≤ ‖π‖ * ‖D1 b - D2 b‖ := π.le_opNorm _
      _ ≤ ‖π‖ * ((ε / c) * (s * ‖b‖) * ‖b‖ + (ε / c) * (s * ‖b‖) * ‖b‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hn1 hn2)) (norm_nonneg _)
      _ = 2 * ‖π‖ * (ε / c) * s * ‖b‖ ^ 2 := by ring
      _ ≤ 2 * ‖π‖ * (ε / c) * t * ‖b‖ ^ 2 := by
        have : 0 ≤ 2 * ‖π‖ * (ε / c) := by positivity
        have h2 : 0 ≤ ‖b‖ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hst this]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t ⟨htpos.le, le_rfl⟩
  have hg0 : g 0 = 0 := by
    simp only [hg, zero_smul, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [two_smul, sub_self, map_zero, sub_zero]
  rw [hg0, sub_zero, sub_zero] at hmv
  have hfin : 2 * ‖π‖ * (ε / c) * t * ‖b‖ ^ 2 * t ≤ ε * t ^ 2 := by
    have h1 : 2 * ‖π‖ * ‖b‖ ^ 2 ≤ c := by rw [hc]; linarith
    have h2 : 2 * ‖π‖ * (ε / c) * t * ‖b‖ ^ 2 * t = (2 * ‖π‖ * ‖b‖ ^ 2) * (ε / c) * t ^ 2 := by ring
    rw [h2]
    have h3 : (2 * ‖π‖ * ‖b‖ ^ 2) * (ε / c) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hcpos]; nlinarith
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith
  exact hmv.trans hfin

/-- **the second derivative is determined by the even part** -/
theorem second_deriv_eq_of_even (f : E → F) (hf : ContDiffAt ℝ 2 f 0) (π : F →L[ℝ] G) (b b' : E)
    (h : ∃ t0 > 0, ∀ t : ℝ, 0 < t → t < t0 → π (f (t • b) + f (-(t • b))) = π (f (t • b') + f (-(t • b')))) :
    π (fderiv ℝ (fderiv ℝ f) 0 b b) = π (fderiv ℝ (fderiv ℝ f) 0 b' b') := by
  obtain ⟨t0, ht0, heq⟩ := h
  set X := π (fderiv ℝ (fderiv ℝ f) 0 b b)
  set X' := π (fderiv ℝ (fderiv ℝ f) 0 b' b')
  have key : ∀ ε : ℝ, 0 < ε → ‖X - X'‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨δ, hδ, h1⟩ := even_approx f hf π b ε hε
    obtain ⟨δ', hδ', h2⟩ := even_approx f hf π b' ε hε
    set t := min t0 (min δ δ') / 2 with ht
    have hm : 0 < min t0 (min δ δ') := lt_min ht0 (lt_min hδ hδ')
    have htpos : 0 < t := by positivity
    have htm : t < min t0 (min δ δ') := by rw [ht]; linarith
    have ht0' : t < t0 := lt_of_lt_of_le htm (min_le_left _ _)
    have htδ : t < δ := lt_of_lt_of_le htm ((min_le_right _ _).trans (min_le_left _ _))
    have htδ' : t < δ' := lt_of_lt_of_le htm ((min_le_right _ _).trans (min_le_right _ _))
    have a1 := h1 t htpos htδ
    have a2 := h2 t htpos htδ'
    have hE : π (f (t • b) + f (-(t • b)) - (2 : ℝ) • f 0) = π (f (t • b') + f (-(t • b')) - (2 : ℝ) • f 0) := by
      rw [map_sub, map_sub, heq t htpos ht0']
    rw [hE] at a1
    have e : (t ^ 2) • (X - X')
        = (π (f (t • b') + f (-(t • b')) - (2 : ℝ) • f 0) - (t ^ 2) • X')
          - (π (f (t • b') + f (-(t • b')) - (2 : ℝ) • f 0) - (t ^ 2) • X) := by
      rw [smul_sub]; abel
    have hn : t ^ 2 * ‖X - X'‖ ≤ ε * t ^ 2 + ε * t ^ 2 := by
      have := norm_sub_le (π (f (t • b') + f (-(t • b')) - (2 : ℝ) • f 0) - (t ^ 2) • X')
        (π (f (t • b') + f (-(t • b')) - (2 : ℝ) • f 0) - (t ^ 2) • X)
      rw [← e, norm_smul, Real.norm_of_nonneg (sq_nonneg t)] at this
      linarith
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith
  have h0 : ‖X - X'‖ = 0 := by
    refine le_antisymm (le_of_forall_pos_lt_add (fun ε hε => ?_)) (norm_nonneg _)
    have := key (ε / 4) (by positivity)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

#print axioms even_approx
#print axioms second_deriv_eq_of_even

end AdalyFormal.DLayer.EvenLimit

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.IngredientFamilyR2 (QlinStepX C2StepX QlinCompX C2CompX C2CompX_succ QlinCompX_succ qStepX
  qStepX_contDiffAt RegBg RegTower XS)

variable {L : PeriodicLatticeExtent}

theorem C2StepX_row_congr (s ell : ℕ) (V0 : PeriodicLinkConfiguration SU2 L) (hreg : RegBg s ell V0)
    (c : PeriodicLatticeEdge L) (b b' : XS L) (h : ∀ e, VisStep s ell c e → b e = b' e) :
    C2StepX s ell V0 b c = C2StepX s ell V0 b' c := by
  have hC2 : ContDiffAt ℝ 2 (qStepX s ell V0) 0 := (qStepX_contDiffAt s ell V0 hreg).of_le (by simp)
  have key := AdalyFormal.DLayer.EvenLimit.second_deriv_eq_of_even (qStepX s ell V0) hC2
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : PeriodicLatticeEdge L => (Fin 3 → ℝ)) c) b b'
    ⟨1, one_pos, fun t _ _ => by
      show qStepX s ell V0 (t • b) c + qStepX s ell V0 (-(t • b)) c
        = qStepX s ell V0 (t • b') c + qStepX s ell V0 (-(t • b')) c
      rw [qStepX_congr s ell V0 (t • b) (t • b') c (fun e he => by simp [h e he]),
        qStepX_congr s ell V0 (-(t • b)) (-(t • b')) c (fun e he => by simp [h e he])]⟩
  show ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 b b) c
    = ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 b' b') c
  rw [Pi.smul_apply, Pi.smul_apply]
  exact congrArg _ key

/-- **footprint locality of the composite second jet** -/
theorem C2CompX_row_congr (ell : ℕ) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (J : ℕ)
    (hreg : RegTower ell bg J) : ∀ j, j ≤ J → ∀ (c : PeriodicLatticeEdge L) (a a' : XS L),
      (∀ e, Foot ell j c e → a e = a' e) → C2CompX ell bg j a c = C2CompX ell bg j a' c := by
  intro j
  induction j with
  | zero =>
      intro _ c a a' _
      rw [C2CompX_zero, C2CompX_zero]
  | succ j ih =>
      intro hj c a a' ha
      rw [C2CompX_succ ell bg J hreg j (by omega) a, C2CompX_succ ell bg J hreg j (by omega) a',
        Pi.add_apply, Pi.add_apply]
      have hreg_j : RegBg (ell ^ j) ell (bg j) := hreg j (by omega)
      -- the linear part: rows agree on VisStep
      have h1 : QlinStepX (ell ^ j) ell (bg j) (C2CompX ell bg j a) c
          = QlinStepX (ell ^ j) ell (bg j) (C2CompX ell bg j a') c := by
        have h0 := QlinStepX_row_local (ell ^ j) ell (bg j) hreg_j c (C2CompX ell bg j a - C2CompX ell bg j a')
          (fun e' he' => by
            rw [Pi.sub_apply, sub_eq_zero]
            exact ih (by omega) e' a a' (fun e he => ha e ⟨e', he', he⟩))
        rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
        exact h0
      have h2 : C2StepX (ell ^ j) ell (bg j) (QlinCompX ell bg j a) c
          = C2StepX (ell ^ j) ell (bg j) (QlinCompX ell bg j a') c := by
        refine C2StepX_row_congr (ell ^ j) ell (bg j) hreg_j c _ _ (fun e' he' => ?_)
        have h0 := QlinCompX_row_local ell bg J hreg j (by omega) e' (a - a')
          (fun e he => by rw [Pi.sub_apply, sub_eq_zero]; exact ha e ⟨e', he', he⟩)
        rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
        exact h0
      rw [h1, h2]

#print axioms C2StepX_row_congr
#print axioms C2CompX_row_congr

end AdalyFormal.DLayer

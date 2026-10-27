import D1IVT

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.Round9.Guarded.AnalyticR1

open scoped RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.D1Literal (PSD psd_coercive psd_kernel)

section PathLemma
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The frozen `D1IVT.exists_nonunit_path`, with its proof copied verbatim, now also
returning that the non-unit found is PSD (the proof already establishes this: the
point is the supremum of the PSD initial segment). -/
theorem exists_psd_nonunit_path (F : ℝ → (E →L[ℝ] E)) (hc : Continuous F)
    (hs : ∀ t x y, ⟪F t x, y⟫ = ⟪x, F t y⟫) (h0 : PSD (F 0)) (T : ℝ) (hT : 0 < T) (v : E)
    (hv : ⟪v, F T v⟫ < 0) : ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ PSD (F t) ∧ ¬ IsUnit (F t) := by
  set S : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ ∀ s ∈ Icc (0 : ℝ) t, PSD (F s)} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT.le⟩, fun s hs' => by
    have : s = 0 := le_antisymm hs'.2 hs'.1
    rw [this]; exact h0⟩
  have hbdd : BddAbove S := ⟨T, fun t ht => ht.1.2⟩
  set ts := sSup S with hts
  have hts0 : 0 ≤ ts := le_csSup hbdd h0S
  have htsT : ts ≤ T := csSup_le ⟨0, h0S⟩ (fun t ht => ht.1.2)
  have hlt : ∀ s, 0 ≤ s → s < ts → PSD (F s) := by
    intro s hs0 hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hclosed : ∀ w : E, IsClosed {s : ℝ | 0 ≤ ⟪w, F s w⟫} := fun w =>
    isClosed_le continuous_const (by fun_prop)
  have hpsd_ts : PSD (F ts) := by
    intro w
    rcases hts0.lt_or_eq with h | h
    · have hsub : Ico (0 : ℝ) ts ⊆ {s : ℝ | 0 ≤ ⟪w, F s w⟫} := fun s hs' => hlt s hs'.1 hs'.2 w
      have := (hclosed w).closure_subset_iff.mpr hsub
      refine this ?_
      rw [closure_Ico h.ne]
      exact ⟨hts0, le_rfl⟩
    · rw [← h]; exact h0 w
  have hle : ∀ s, 0 ≤ s → s ≤ ts → PSD (F s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have htsT' : ts < T := by
    rcases htsT.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts v
      rw [h] at this
      linarith
  refine ⟨ts, hts0, htsT', hpsd_ts, fun hu => ?_⟩
  obtain ⟨m, hm, hmc⟩ := psd_coercive (F ts) (hs ts) hpsd_ts hu
  have hcts : ContinuousAt F ts := hc.continuousAt
  rw [Metric.continuousAt_iff] at hcts
  obtain ⟨δ, hδ, hF⟩ := hcts (m / 2) (by positivity)
  set t' := min (ts + δ / 2) T with ht'
  have ht'T : t' ≤ T := min_le_right _ _
  have ht'ts : ts < t' := lt_min (by linarith) htsT'
  have ht'S : t' ∈ S := by
    refine ⟨⟨by linarith, ht'T⟩, fun s hs' => ?_⟩
    rcases le_or_gt s ts with h | h
    · exact hle s hs'.1 h
    · intro w
      have hd : dist s ts < δ := by
        rw [Real.dist_eq, abs_lt]
        have : s ≤ ts + δ / 2 := le_trans hs'.2 (min_le_left _ _)
        constructor <;> linarith
      have hn := hF hd
      rw [dist_eq_norm] at hn
      have h1 : ⟪w, F s w⟫ = ⟪w, F ts w⟫ + ⟪w, (F s - F ts) w⟫ := by
        simp only [sub_apply, inner_sub_right]; ring
      have h2 : |⟪w, (F s - F ts) w⟫| ≤ ‖w‖ * (‖F s - F ts‖ * ‖w‖) := by
        calc |⟪w, (F s - F ts) w⟫| ≤ ‖w‖ * ‖(F s - F ts) w‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖w‖ * (‖F s - F ts‖ * ‖w‖) := by gcongr; exact (F s - F ts).le_opNorm w
      have h3 := hmc w
      have h4 : ‖w‖ * (‖F s - F ts‖ * ‖w‖) ≤ (m / 2) * ‖w‖ ^ 2 := by
        have : ‖F s - F ts‖ ≤ m / 2 := hn.le
        calc ‖w‖ * (‖F s - F ts‖ * ‖w‖) = ‖F s - F ts‖ * ‖w‖ ^ 2 := by ring
          _ ≤ (m / 2) * ‖w‖ ^ 2 := by gcongr
      have h5 := (abs_le.mp h2).1
      nlinarith [sq_nonneg ‖w‖]
  have := le_csSup hbdd ht'S
  linarith

/-- Strict positivity of a quadratic form on the range of an idempotent is uniform. -/
theorem exists_coercive_on_range (P M : E →L[ℝ] E)
    (h : ∀ x, P x = x → x ≠ 0 → 0 < ⟪x, M x⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, P x = x → c * ‖x‖ ^ 2 ≤ ⟪x, M x⟫ := by
  set S1 : Set E := {x | P x = x} ∩ Metric.sphere (0 : E) 1 with hS1
  have hcpt : IsCompact S1 :=
    (isCompact_sphere (0 : E) 1).inter_left (isClosed_eq P.continuous continuous_id)
  have hcont : Continuous (fun v : E => ⟪v, M v⟫) := by fun_prop
  have hscale : ∀ x : E, x ≠ 0 → P x = x → (‖x‖⁻¹ • x) ∈ S1 ∧
      ⟪x, M x⟫ = ‖x‖ ^ 2 * ⟪‖x‖⁻¹ • x, M (‖x‖⁻¹ • x)⟫ := by
    intro x hx hPx
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxn' : ‖x‖ ≠ 0 := hxn.ne'
    refine ⟨⟨by simp [map_smul, hPx], ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn']
    · simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      field_simp
      try ring
  rcases S1.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x hPx => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      have := (hscale x hx hPx).1
      rw [he] at this
      exact this
  · obtain ⟨x0, hx0, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
    have hx0n : x0 ≠ 0 := by
      intro h0
      have := hx0.2
      rw [h0] at this
      simp at this
    refine ⟨⟪x0, M x0⟫, h x0 hx0.1 hx0n, fun x hPx => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · obtain ⟨hmem, heq⟩ := hscale x hx hPx
      have hm : ⟪x0, M x0⟫ ≤ ⟪‖x‖⁻¹ • x, M (‖x‖⁻¹ • x)⟫ := hmin hmem
      rw [heq]
      nlinarith [sq_nonneg ‖x‖]

end PathLemma

section Schur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The complementary block `(1-P) Z (1-P)`, padded by `P` so that it is a unit of
the full operator ring exactly when the block is invertible on `ker P`. -/
noncomputable def schurC (P Z : E →L[ℝ] E) : E →L[ℝ] E := (1 - P) * Z * (1 - P) + P

/-- The Schur complement of `Z` onto the range of the idempotent `P`. -/
noncomputable def schurS (P Z : E →L[ℝ] E) : E →L[ℝ] E :=
  P * Z * P - P * Z * (1 - P) * Ring.inverse (schurC P Z) * ((1 - P) * Z * P)

theorem inverse_symm (C : E →L[ℝ] E) (hC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫) (x y : E) :
    ⟪Ring.inverse C x, y⟫ = ⟪x, Ring.inverse C y⟫ := by
  by_cases hu : IsUnit C
  · have h1 : ∀ v, C (Ring.inverse C v) = v := fun v => by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel C hu, one_apply_eq_self]
    calc ⟪Ring.inverse C x, y⟫ = ⟪Ring.inverse C x, C (Ring.inverse C y)⟫ := by rw [h1]
      _ = ⟪C (Ring.inverse C x), Ring.inverse C y⟫ := (hC _ _).symm
      _ = ⟪x, Ring.inverse C y⟫ := by rw [h1]
  · rw [Ring.inverse_non_unit C hu]
    simp

theorem schurS_symm (P Z : E →L[ℝ] E) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hZs : ∀ x y, ⟪Z x, y⟫ = ⟪x, Z y⟫) (x y : E) :
    ⟪schurS P Z x, y⟫ = ⟪x, schurS P Z y⟫ := by
  set Q : E →L[ℝ] E := 1 - P with hQ
  have hQs : ∀ x y, ⟪Q x, y⟫ = ⟪x, Q y⟫ := by
    intro x y
    simp only [hQ, sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right, hPs]
  have hCs : ∀ x y, ⟪schurC P Z x, y⟫ = ⟪x, schurC P Z y⟫ := by
    intro x y
    simp only [schurC, ← hQ, add_apply, mul_apply_eq_comp, inner_add_left, inner_add_right]
    rw [hQs, hZs, hQs, hPs]
  have hCis := inverse_symm (schurC P Z) hCs
  simp only [schurS, ← hQ]
  rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right]
  simp only [mul_apply_eq_comp]
  congr 1
  · rw [hPs, hZs, hPs]
  · rw [hPs, hZs, hQs, hCis, hQs, hZs, hPs]

theorem schurS_left (P Z : E →L[ℝ] E) (hP : P * P = P) (v : E) :
    P (schurS P Z v) = schurS P Z v := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  simp only [schurS, sub_apply, mul_apply_eq_comp, map_sub, hPv]

theorem schurS_right (P Z : E →L[ℝ] E) (hP : P * P = P) (v : E) :
    schurS P Z (P v) = schurS P Z v := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  simp only [schurS, sub_apply, mul_apply_eq_comp, hPv]

/-- Schur reduction: if the complementary block is invertible, `Z` is a unit iff its
Schur complement is injective on the range of `P`. -/
theorem schur_unit_iff {P Z : E →L[ℝ] E} (hP : P * P = P) (hC : IsUnit (schurC P Z)) :
    IsUnit Z ↔ ∀ x, P x = x → schurS P Z x = 0 → x = 0 := by
  set C := schurC P Z with hCdef
  set Ci := Ring.inverse C with hCi
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  have hCv : ∀ u, C u = (Z (u - P u) - P (Z (u - P u))) + P u := by
    intro u
    simp only [hCdef, schurC, add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  have hCCi : ∀ u, C (Ci u) = u := fun u => by
    rw [← mul_apply_eq_comp, hCi, Ring.mul_inverse_cancel C hC, one_apply_eq_self]
  have hCiC : ∀ u, Ci (C u) = u := fun u => by
    rw [← mul_apply_eq_comp, hCi, Ring.inverse_mul_cancel C hC, one_apply_eq_self]
  have hPC : ∀ u, P (C u) = P u := by
    intro u; rw [hCv]; simp [map_add, map_sub, hPv]
  have hPCi : ∀ u, P (Ci u) = P u := by
    intro u
    have := hPC (Ci u)
    rw [hCCi] at this
    exact this.symm
  have hkey : ∀ u, Z (Ci u - P u) - P (Z (Ci u - P u)) = u - P u := by
    intro u
    have h := hCCi u
    rw [hCv, hPCi] at h
    exact eq_sub_of_add_eq h
  have hSv : ∀ x, schurS P Z x =
      P (Z (P x)) - P (Z (Ci (Z (P x) - P (Z (P x))) - P (Ci (Z (P x) - P (Z (P x)))))) := by
    intro x
    simp only [schurS, ← hCdef, ← hCi, sub_apply, mul_apply_eq_comp, one_apply_eq_self]
  constructor
  · intro hu x hPx hS
    have hinj : Function.Injective Z := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    have hPr : P (Z x - P (Z x)) = 0 := by rw [map_sub, hPv, sub_self]
    have hPCir : P (Ci (Z x - P (Z x))) = 0 := by rw [hPCi, hPr]
    have hS' : P (Z x) - P (Z (Ci (Z x - P (Z x)))) = 0 := by
      have := hS
      rw [hSv, hPx, hPCir, sub_zero] at this
      exact this
    have hk := hkey (Z x - P (Z x))
    simp only [hPr, sub_zero] at hk
    have h2 : P (Z (Ci (Z x - P (Z x)))) = P (Z x) := (sub_eq_zero.mp hS').symm
    have hZy : Z (x - Ci (Z x - P (Z x))) = 0 := by
      rw [map_sub]
      have e : Z (Ci (Z x - P (Z x))) = Z x - P (Z x) + P (Z (Ci (Z x - P (Z x)))) :=
        eq_add_of_sub_eq hk
      rw [e, h2]; abel
    have hy0 : x - Ci (Z x - P (Z x)) = 0 := hinj (by rw [hZy, map_zero])
    have : P (x - Ci (Z x - P (Z x))) = x := by rw [map_sub, hPCir, hPx, sub_zero]
    rw [← this, hy0, map_zero]
  · intro h
    have hinj : Function.Injective Z := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have hPm : P (y - P y) = 0 := by rw [map_sub, hPv, sub_self]
      have hsplit : P y + (y - P y) = y := by abel
      have hZy : Z (P y) + Z (y - P y) = 0 := by rw [← map_add, hsplit, hy]
      have hCm : C (y - P y) = -(Z (P y) - P (Z (P y))) := by
        rw [hCv, hPm, sub_zero, add_zero]
        have e : Z (y - P y) = -Z (P y) := eq_neg_of_add_eq_zero_right hZy
        rw [e, map_neg]; abel
      have hneg : Ci (-(Z (P y) - P (Z (P y)))) = -(Ci (Z (P y) - P (Z (P y)))) := map_neg Ci _
      have hm' : y - P y = -(Ci (Z (P y) - P (Z (P y)))) := by
        rw [← hneg, ← hCm, hCiC]
      have hPCr : P (Ci (Z (P y) - P (Z (P y)))) = 0 := by
        rw [hPCi, map_sub, hPv, sub_self]
      have hS0 : schurS P Z (P y) = 0 := by
        rw [hSv, hPv, hPCr, sub_zero]
        have e : Ci (Z (P y) - P (Z (P y))) = -(y - P y) := by rw [hm', neg_neg]
        rw [e, map_neg, map_neg, sub_neg_eq_add, ← map_add, hZy, map_zero]
      have hPy : P y = 0 := h (P y) (hPv y) hS0
      have hm0 : y - P y = 0 := by
        rw [hm']
        simp only [hPy, map_zero, sub_zero, neg_zero]
      rw [hPy, sub_zero] at hm0
      exact hm0
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (Z : E →ₗ[ℝ] E))).mp hinj⟩

end Schur

section Perturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem tendsto_inverse_of_unit {α : Type*} {l : Filter α} {f : α → E →L[ℝ] E} {C : E →L[ℝ] E}
    (hC : IsUnit C) (hf : Tendsto f l (𝓝 C)) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 (Ring.inverse C)) := by
  have h := NormedRing.inverse_continuousAt hC.unit
  rw [hC.unit_spec] at h
  exact h.tendsto.comp hf

theorem schurC_continuous (P : E →L[ℝ] E) : Continuous (schurC P) := by
  unfold schurC
  exact ((continuous_const.mul continuous_id).mul continuous_const).add continuous_const

theorem tendsto_schurS {α : Type*} {l : Filter α} (P : E →L[ℝ] E) {f : α → E →L[ℝ] E}
    {Z : E →L[ℝ] E} (hC : IsUnit (schurC P Z)) (hf : Tendsto f l (𝓝 Z)) :
    Tendsto (fun a => schurS P (f a)) l (𝓝 (schurS P Z)) := by
  have hCi := tendsto_inverse_of_unit hC (((schurC_continuous P).tendsto Z).comp hf)
  unfold schurS
  exact ((tendsto_const_nhds.mul hf).mul tendsto_const_nhds).sub
    ((((tendsto_const_nhds.mul hf).mul tendsto_const_nhds).mul hCi).mul
      ((tendsto_const_nhds.mul hf).mul tendsto_const_nhds))

theorem quad_le_norm (A : E →L[ℝ] E) (x : E) : |⟪x, A x⟫| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  calc |⟪x, A x⟫| ≤ ‖x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

/-- First-order behaviour of the Schur complement at a kernel crossing. -/
theorem vacuum_schur_slope (P X' : E →L[ℝ] E) (Xv : ℝ → E →L[ℝ] E) (t₀ : ℝ)
    (hder : HasDerivAt Xv X' t₀)
    (hXP : Xv t₀ * P = 0) (hPX : P * Xv t₀ = 0) (hC0 : IsUnit (schurC P (Xv t₀))) :
    Tendsto (fun t => (t - t₀)⁻¹ • schurS P (Xv t)) (𝓝[≠] t₀) (𝓝 (P * X' * P)) := by
  have hslope : Tendsto (fun t => (t - t₀)⁻¹ • (Xv t - Xv t₀)) (𝓝[≠] t₀) (𝓝 X') := by
    have h := hasDerivAt_iff_tendsto_slope.mp hder
    have he : slope Xv t₀ = fun t => (t - t₀)⁻¹ • (Xv t - Xv t₀) := by
      funext t; exact slope_def_module Xv t₀ t
    rwa [he] at h
  have hcont : Tendsto Xv (𝓝[≠] t₀) (𝓝 (Xv t₀)) :=
    hder.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t => Xv t - Xv t₀) (𝓝[≠] t₀) (𝓝 0) := by
    have := hcont.sub_const (Xv t₀)
    rwa [sub_self] at this
  have hCi := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto _).comp hcont)
  have hid : ∀ t, (t - t₀)⁻¹ • schurS P (Xv t) =
      P * ((t - t₀)⁻¹ • (Xv t - Xv t₀)) * P - P * ((t - t₀)⁻¹ • (Xv t - Xv t₀)) * (1 - P) *
        Ring.inverse (schurC P (Xv t)) * ((1 - P) * (Xv t - Xv t₀) * P) := by
    intro t
    have e1 : P * Xv t * P = P * (Xv t - Xv t₀) * P := by
      rw [mul_sub P (Xv t) (Xv t₀), sub_mul (P * Xv t) (P * Xv t₀) P, hPX, zero_mul, sub_zero]
    have e2 : P * Xv t * (1 - P) = P * (Xv t - Xv t₀) * (1 - P) := by
      rw [mul_sub P (Xv t) (Xv t₀), hPX, sub_zero]
    have e3 : (1 - P) * Xv t * P = (1 - P) * (Xv t - Xv t₀) * P := by
      rw [mul_sub (1 - P) (Xv t) (Xv t₀), sub_mul ((1 - P) * Xv t) ((1 - P) * Xv t₀) P,
        mul_assoc (1 - P) (Xv t₀) P, hXP, mul_zero, sub_zero]
    unfold schurS
    rw [e1, e2, e3]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  simp_rw [hid]
  have hlim := ((tendsto_const_nhds (x := P)).mul hslope |>.mul (tendsto_const_nhds (x := P))).sub
    (((((tendsto_const_nhds (x := P)).mul hslope).mul (tendsto_const_nhds (x := 1 - P))).mul hCi).mul
      (((tendsto_const_nhds (x := 1 - P)).mul hh).mul (tendsto_const_nhds (x := P))))
  have hval : P * X' * P - P * X' * (1 - P) * Ring.inverse (schurC P (Xv t₀)) *
      ((1 - P) * 0 * P) = P * X' * P := by simp
  rwa [hval] at hlim

/-- The exact algebra of the corrected Schur complement. -/
theorem schur_difference_identity (P X D : E →L[ℝ] E) (c : ℝ)
    (hX : IsUnit (schurC P X)) (hY : IsUnit (schurC P (X - D))) :
    c • (schurS P X - schurS P (X - D)) =
      P * (c • D) * P
      + (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * (1 - P)) *
          Ring.inverse (schurC P X) * ((1 - P) * X * P)
      - (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * P)
      - (P * (c • D) * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * X * P)
      + (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * (c • D) * P) := by
  have hres : Ring.inverse (schurC P (X - D)) - Ring.inverse (schurC P X) =
      Ring.inverse (schurC P (X - D)) * ((1 - P) * D * (1 - P)) * Ring.inverse (schurC P X) := by
    have hd : schurC P X - schurC P (X - D) = (1 - P) * D * (1 - P) := by
      unfold schurC; noncomm_ring
    have e1 : Ring.inverse (schurC P (X - D)) * schurC P X * Ring.inverse (schurC P X) =
        Ring.inverse (schurC P (X - D)) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ hX, mul_one]
    have e2 : Ring.inverse (schurC P (X - D)) * schurC P (X - D) * Ring.inverse (schurC P X) =
        Ring.inverse (schurC P X) := by
      rw [Ring.inverse_mul_cancel _ hY, one_mul]
    rw [← hd, mul_sub, sub_mul, e1, e2]
  have key : schurS P X - schurS P (X - D) = P * D * P
      + (P * X * (1 - P)) * (Ring.inverse (schurC P (X - D)) - Ring.inverse (schurC P X)) *
          ((1 - P) * X * P)
      - (P * X * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * D * P)
      - (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * X * P)
      + (P * D * (1 - P)) * Ring.inverse (schurC P (X - D)) * ((1 - P) * D * P) := by
    unfold schurS
    generalize Ring.inverse (schurC P (X - D)) = CiY
    generalize Ring.inverse (schurC P X) = CiX
    noncomm_ring
  rw [key, hres]
  simp only [smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
  try abel

/-- The corrected Schur complement differs from the carrier one by `ε P D₁ P + o(ε)`. -/
theorem schur_difference_tendsto {α : Type*} {l : Filter α} (P : E →L[ℝ] E)
    {Xf Df : α → E →L[ℝ] E} {c : α → ℝ} {X0 D1 : E →L[ℝ] E}
    (hXP : X0 * P = 0) (hPX : P * X0 = 0) (hC0 : IsUnit (schurC P X0))
    (hX : Tendsto Xf l (𝓝 X0)) (hD : Tendsto Df l (𝓝 0))
    (hcD : Tendsto (fun a => c a • Df a) l (𝓝 D1)) :
    Tendsto (fun a => c a • (schurS P (Xf a) - schurS P (Xf a - Df a)) - P * D1 * P) l (𝓝 0) := by
  have hY : Tendsto (fun a => Xf a - Df a) l (𝓝 X0) := by
    have := hX.sub hD
    rwa [sub_zero] at this
  have hCX := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto X0).comp hX)
  have hCY := tendsto_inverse_of_unit hC0 (((schurC_continuous P).tendsto X0).comp hY)
  have hunitX : ∀ᶠ a in l, IsUnit (schurC P (Xf a)) :=
    (((schurC_continuous P).tendsto X0).comp hX).eventually (Units.isOpen.mem_nhds hC0)
  have hunitY : ∀ᶠ a in l, IsUnit (schurC P (Xf a - Df a)) :=
    (((schurC_continuous P).tendsto X0).comp hY).eventually (Units.isOpen.mem_nhds hC0)
  have hid : ∀ᶠ a in l,
      (P * (c a • Df a) * P - P * D1 * P)
      + (P * Xf a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) *
          ((1 - P) * (c a • Df a) * (1 - P)) * Ring.inverse (schurC P (Xf a)) * ((1 - P) * Xf a * P)
      - (P * Xf a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * (c a • Df a) * P)
      - (P * (c a • Df a) * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * Xf a * P)
      + (P * Df a * (1 - P)) * Ring.inverse (schurC P (Xf a - Df a)) * ((1 - P) * (c a • Df a) * P)
      = c a • (schurS P (Xf a) - schurS P (Xf a - Df a)) - P * D1 * P := by
    filter_upwards [hunitX, hunitY] with a hxu hyu
    rw [schur_difference_identity P (Xf a) (Df a) (c a) hxu hyu]
    abel
  refine Tendsto.congr' hid ?_
  have hb : Tendsto (fun a => P * Xf a * (1 - P)) l (𝓝 0) := by
    have := ((tendsto_const_nhds (x := P)).mul hX).mul (tendsto_const_nhds (x := 1 - P))
    rwa [hPX, zero_mul] at this
  have hb' : Tendsto (fun a => (1 - P) * Xf a * P) l (𝓝 0) := by
    have := ((tendsto_const_nhds (x := 1 - P)).mul hX).mul (tendsto_const_nhds (x := P))
    rwa [mul_assoc (1 - P) X0 P, hXP, mul_zero] at this
  have t0 : Tendsto (fun a => P * (c a • Df a) * P - P * D1 * P) l (𝓝 0) := by
    have := (((tendsto_const_nhds (x := P)).mul hcD).mul (tendsto_const_nhds (x := P))).sub_const
      (P * D1 * P)
    rwa [sub_self] at this
  have t1 := (((hb.mul hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul
    (tendsto_const_nhds (x := 1 - P)))).mul hCX).mul hb'
  have t2 := (hb.mul hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul
    (tendsto_const_nhds (x := P)))
  have t3 := ((((tendsto_const_nhds (x := P)).mul hcD).mul (tendsto_const_nhds (x := 1 - P))).mul
    hCY).mul hb'
  have t4 := ((((tendsto_const_nhds (x := P)).mul hD).mul (tendsto_const_nhds (x := 1 - P))).mul
    hCY).mul (((tendsto_const_nhds (x := 1 - P)).mul hcD).mul (tendsto_const_nhds (x := P)))
  have := (((t0.add t1).sub t2).sub t3).add t4
  simpa using this

end Perturbation

section Main
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Separation along a path from a positivity gap: the core sign-change step on the
range of `P`.  `B` is the corrected Schur complement, `A` the carrier one. -/
theorem core_separation (P : E →L[ℝ] E) (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (A B : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 < T)
    (hBc : ContinuousOn B (Icc 0 T))
    (hBs : ∀ s x y, ⟪B s x, y⟫ = ⟪x, B s y⟫)
    (hBl : ∀ s v, P (B s v) = B s v) (hBr : ∀ s v, B s (P v) = B s v)
    (hB0 : ∀ x, P x = x → 0 ≤ ⟪x, B 0 x⟫)
    (w : E) (hw : P w = w) (hBT : ⟪w, B T w⟫ < 0)
    (hAB : ∀ s ∈ Icc 0 T, ∀ x, P x = x → x ≠ 0 → ⟪x, B s x⟫ < ⟪x, A s x⟫) :
    ∃ s, 0 ≤ s ∧ s < T ∧ (∀ x, P x = x → A s x = 0 → x = 0) ∧
      ∃ x, P x = x ∧ x ≠ 0 ∧ B s x = 0 := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  set pr : ℝ → ℝ := fun s => (projIcc 0 T hT.le s : ℝ) with hpr
  have hprc : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hprmem : ∀ s, pr s ∈ Icc 0 T := fun s => (projIcc 0 T hT.le s).2
  have hprid : ∀ s ∈ Icc 0 T, pr s = s := fun s hs => by
    simp only [hpr, projIcc_of_mem hT.le hs]
  set G : ℝ → E →L[ℝ] E := fun s => B (pr s) + (1 - P) with hG
  have hGc : Continuous G := (hBc.comp_continuous hprc hprmem).add continuous_const
  have hQq : ∀ v, ⟪v, (1 - P) v⟫ = ‖v - P v‖ ^ 2 := by
    intro v
    rw [sub_apply, one_apply_eq_self, ← real_inner_self_eq_norm_sq]
    have h0 : ⟪P v, v - P v⟫ = 0 := by
      rw [hPs, map_sub, hPv, sub_self, inner_zero_right]
    calc ⟪v, v - P v⟫ = ⟪(v - P v) + P v, v - P v⟫ := by rw [sub_add_cancel]
      _ = ⟪v - P v, v - P v⟫ := by rw [inner_add_left, h0, add_zero]
  have hBq : ∀ s v, ⟪v, B s v⟫ = ⟪P v, B s (P v)⟫ := by
    intro s v
    rw [hBr, hPs, hBl]
  have hGs : ∀ s x y, ⟪G s x, y⟫ = ⟪x, G s y⟫ := by
    intro s x y
    simp only [hG, add_apply, sub_apply, one_apply_eq_self, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, hBs, hPs]
  have hG0 : PSD (G 0) := by
    intro v
    simp only [hG, add_apply, inner_add_right]
    rw [hprid 0 ⟨le_rfl, hT.le⟩, hQq, hBq]
    have h1 := hB0 (P v) (hPv v)
    have h2 := sq_nonneg ‖v - P v‖
    linarith
  have hGT : ⟪w, G T w⟫ < 0 := by
    simp only [hG, add_apply, inner_add_right]
    rw [hprid T ⟨hT.le, le_rfl⟩, hQq, hw, sub_self, norm_zero]
    simpa using hBT
  obtain ⟨s, hs0, hsT, hpsd, hnu⟩ := exists_psd_nonunit_path G hGc hGs hG0 T hT w hGT
  have hsI : s ∈ Icc 0 T := ⟨hs0, hsT.le⟩
  have hGs' : G s = B s + (1 - P) := by simp only [hG, hprid s hsI]
  -- a kernel vector of `G s`
  have hker : ∃ y, y ≠ 0 ∧ G s y = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hnu
    have hinj : Function.Injective (G s) := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      by_contra hy0
      exact hcon y hy0 hy
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := ((G s) : E →ₗ[ℝ] E))).mp hinj⟩
  obtain ⟨y, hy0, hGy⟩ := hker
  rw [hGs', add_apply, sub_apply, one_apply_eq_self] at hGy
  have hBy : B s y = 0 := by
    have := congrArg P hGy
    rw [map_add, map_sub, hBl, hPv, sub_self, add_zero, map_zero] at this
    exact this
  have hPy : P y = y := by
    rw [hBy, zero_add, sub_eq_zero] at hGy
    exact hGy.symm
  refine ⟨s, hs0, hsT, fun x hx hAx => ?_, y, hPy, hy0, hBy⟩
  by_contra hx0
  have h1 := hAB s hsI x hx hx0
  rw [hAx, inner_zero_right] at h1
  have h2 := hpsd x
  rw [hGs', add_apply, inner_add_right, hQq, hx, sub_self, norm_zero] at h2
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  linarith

end Main

section MainTheorem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Perturbative separation, positive sign.  At zero curvature the carrier `X 0 ·`
has a crossing at `t₀` whose kernel is the range of the symmetric idempotent `P`,
with negative slope there; the correction is `ε D₁ + o(ε)` with `D₁` positive on
the kernel.  Then every small `ε > 0` has an angle where `X ε t` is a unit and
`X ε t - D ε` is not.  No positivity of the carrier is assumed (other directions
may have crossed earlier), and no symmetry of the kernel. -/
theorem separation_of_vacuum_data_pos
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hpos : ∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  have hPv : ∀ u, P (P u) = P u := fun u => by rw [← mul_apply_eq_comp, hP]
  -- `P X₀ = 0` by symmetry
  have hPX : P * X 0 t₀ = 0 := by
    ext x
    rw [mul_apply_eq_comp, zero_apply]
    apply ext_inner_right ℝ
    intro y
    rw [hPs, hXs, ← mul_apply_eq_comp (X 0 t₀) P y, hXP, zero_apply, inner_zero_right,
      inner_zero_left]
  -- the complementary block is invertible at the crossing
  have hC0 : IsUnit (schurC P (X 0 t₀)) := by
    have hinj : Function.Injective (schurC P (X 0 t₀)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hCv : schurC P (X 0 t₀) x = (X 0 t₀ (x - P x) - P (X 0 t₀ (x - P x))) + P x := by
        simp only [schurC, add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
      have hPX0 : ∀ u, P (X 0 t₀ u) = 0 := fun u => by
        rw [← mul_apply_eq_comp, hPX, zero_apply]
      have hPx : P x = 0 := by
        have := congrArg P hx
        rw [hCv, map_add, map_sub, hPv, sub_self, zero_add, hPv, map_zero] at this
        exact this
      rw [hCv, hPx, sub_zero, add_zero, hPX0, sub_zero] at hx
      have := hker x hx
      rw [hPx] at this
      exact this.symm
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,
      (LinearMap.injective_iff_surjective (f := ((schurC P (X 0 t₀)) : E →ₗ[ℝ] E))).mp hinj⟩
  -- uniform constants on the kernel
  obtain ⟨ν, hν, hνc⟩ := exists_coercive_on_range P D₁ hpos
  obtain ⟨σ₀, hσ₀, hσc⟩ := exists_coercive_on_range P (-X') (fun v hv hv0 => by
    rw [neg_apply, inner_neg_right]; linarith [hslope v hv hv0])
  -- (1) the vacuum Schur complement has slope `P X' P`
  have hvac := vacuum_schur_slope P X' (X 0) t₀ hder hXP hPX hC0
  have hΨ : ∀ᶠ t in 𝓝[≠] t₀, ‖(t - t₀)⁻¹ • schurS P (X 0 t) - P * X' * P‖ < σ₀ / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hvac).eventually (gt_mem_nhds (by positivity))
  obtain ⟨η₂, hη₂, hη₂'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hΨ)
  -- (2) vacuum units near the crossing
  have hCvac : ∀ᶠ t in 𝓝 t₀, IsUnit (schurC P (X 0 t)) :=
    (((schurC_continuous P).tendsto _).comp hder.continuousAt.tendsto).eventually
      (Units.isOpen.mem_nhds hC0)
  obtain ⟨η₃, hη₃, hη₃'⟩ := Metric.eventually_nhds_iff.mp hCvac
  -- (3) off the vacuum: units and the first-order corrected difference
  have hXF : Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 (X 0 t₀)) := by
    have h := (hjoint t₀ (by simpa using hη₀)).tendsto
    refine h.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hD0 : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε • (ε⁻¹ • D ε)) (𝓝[>] 0) (𝓝 ((0 : ℝ) • D₁)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hD
    rw [zero_smul] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    rw [smul_smul, mul_inv_cancel₀ hε'.ne', one_smul]
  have hDF : Tendsto (fun p : ℝ × ℝ => D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 0) :=
    hD0.comp tendsto_fst
  have hcDF : Tendsto (fun p : ℝ × ℝ => p.1⁻¹ • D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀) (𝓝 D₁) :=
    hD.comp tendsto_fst
  have hYF : Tendsto (fun p : ℝ × ℝ => X p.1 p.2 - D p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀)
      (𝓝 (X 0 t₀)) := by
    have := hXF.sub hDF
    rwa [sub_zero] at this
  have hdiff := schur_difference_tendsto P hXP hPX hC0 hXF hDF hcDF
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 t₀,
      IsUnit (schurC P (X p.1 p.2)) ∧ IsUnit (schurC P (X p.1 p.2 - D p.1)) ∧
      ‖p.1⁻¹ • (schurS P (X p.1 p.2) - schurS P (X p.1 p.2 - D p.1)) - P * D₁ * P‖ < ν / 2 := by
    refine ((((schurC_continuous P).tendsto _).comp hXF).eventually
      (Units.isOpen.mem_nhds hC0)).and
      (((((schurC_continuous P).tendsto _).comp hYF).eventually
        (Units.isOpen.mem_nhds hC0)).and ?_)
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hdiff).eventually (gt_mem_nhds (by positivity))
      |>.mono (fun p hp => by simpa using hp)
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpa)
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.eventually_nhds_iff.mp hpb
  have hoff : ∀ ε t, 0 < ε → ε < δ₁ → |t - t₀| < η₁ →
      IsUnit (schurC P (X ε t)) ∧ IsUnit (schurC P (X ε t - D ε)) ∧
      ‖ε⁻¹ • (schurS P (X ε t) - schurS P (X ε t - D ε)) - P * D₁ * P‖ < ν / 2 := by
    intro ε t hε hεδ ht
    have h1 : pa ε := hδ₁' (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ) hε
    have h2 : pb t := hη₁' (by rw [Real.dist_eq]; exact ht)
    exact hpab h1 h2
  -- (4) fix the half-width `η`
  set η : ℝ := min (min η₀ η₁) (min η₂ η₃) / 2 with hη
  have hηpos : 0 < η := by positivity
  have hη0 : η < η₀ := by
    have := min_le_left (min η₀ η₁) (min η₂ η₃); have := min_le_left η₀ η₁; linarith
  have hη1 : η < η₁ := by
    have := min_le_left (min η₀ η₁) (min η₂ η₃); have := min_le_right η₀ η₁; linarith
  have hη2 : η < η₂ := by
    have := min_le_right (min η₀ η₁) (min η₂ η₃); have := min_le_left η₂ η₃; linarith
  have hη3 : η < η₃ := by
    have := min_le_right (min η₀ η₁) (min η₂ η₃); have := min_le_right η₂ η₃; linarith
  -- (5) the vacuum Schur form at `t₀ ∓ η`
  have hvacform : ∀ τ : ℝ, τ ≠ 0 → |τ| < η₂ → ∀ x, P x = x →
      |⟪x, schurS P (X 0 (t₀ + τ)) x⟫ - τ * ⟪x, X' x⟫| ≤ |τ| * (σ₀ / 2) * ‖x‖ ^ 2 := by
    intro τ hτ hτη x hx
    have hne : t₀ + τ ≠ t₀ := by intro h; apply hτ; linarith
    have hΨt := hη₂' (show dist (t₀ + τ) t₀ < η₂ by
      rw [Real.dist_eq, add_sub_cancel_left]; exact hτη) hne
    rw [add_sub_cancel_left] at hΨt
    set Ψ := τ⁻¹ • schurS P (X 0 (t₀ + τ)) - P * X' * P with hΨdef
    have hS : schurS P (X 0 (t₀ + τ)) = τ • (P * X' * P + Ψ) := by
      rw [hΨdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ hτ, one_smul]
    have hPXP : ⟪x, (P * X' * P) x⟫ = ⟪x, X' x⟫ := by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, hx, ← hPs, hx]
    rw [hS, smul_apply, inner_smul_right, add_apply, inner_add_right, hPXP]
    have hq := quad_le_norm Ψ x
    have : τ * (⟪x, X' x⟫ + ⟪x, Ψ x⟫) - τ * ⟪x, X' x⟫ = τ * ⟪x, Ψ x⟫ := by ring
    rw [this, abs_mul]
    have h3 : ‖Ψ‖ * ‖x‖ ^ 2 ≤ σ₀ / 2 * ‖x‖ ^ 2 := by gcongr
    calc |τ| * |⟪x, Ψ x⟫| ≤ |τ| * (‖Ψ‖ * ‖x‖ ^ 2) := by gcongr
      _ ≤ |τ| * (σ₀ / 2 * ‖x‖ ^ 2) := by gcongr
      _ = |τ| * (σ₀ / 2) * ‖x‖ ^ 2 := by ring
  have hleft : ∀ x, P x = x → η * (σ₀ / 2) * ‖x‖ ^ 2 ≤ ⟪x, schurS P (X 0 (t₀ - η)) x⟫ := by
    intro x hx
    have h := hvacform (-η) (neg_ne_zero.mpr hηpos.ne')
      (by rw [abs_neg, abs_of_pos hηpos]; exact hη2) x hx
    rw [← sub_eq_add_neg, abs_neg, abs_of_pos hηpos] at h
    have hs := hσc x hx
    rw [neg_apply, inner_neg_right] at hs
    have h1 := (abs_le.mp h).1
    have h2 := mul_le_mul_of_nonneg_left hs hηpos.le
    nlinarith
  have hright : ∀ x, P x = x → ⟪x, schurS P (X 0 (t₀ + η)) x⟫ ≤ -(η * (σ₀ / 2) * ‖x‖ ^ 2) := by
    intro x hx
    have h := hvacform η hηpos.ne' (by rw [abs_of_pos hηpos]; exact hη2) x hx
    rw [abs_of_pos hηpos] at h
    have hs := hσc x hx
    rw [neg_apply, inner_neg_right] at hs
    have h1 := (abs_le.mp h).2
    have h2 := mul_le_mul_of_nonneg_left hs hηpos.le
    nlinarith
  -- (6) the corrected Schur form at the two ends, for small `ε`
  have hend : ∀ τ : ℝ, |τ| = η → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖schurS P (X ε (t₀ + τ) - D ε) - schurS P (X 0 (t₀ + τ))‖ < η * (σ₀ / 4) := by
    intro τ hτ
    have hcl : |t₀ + τ - t₀| < η₀ := by rw [add_sub_cancel_left, hτ]; exact hη0
    have hX1 : Tendsto (fun ε : ℝ => X ε (t₀ + τ)) (𝓝[>] 0) (𝓝 (X 0 (t₀ + τ))) := by
      have h := (hjoint (t₀ + τ) hcl).tendsto
      exact h.comp (Tendsto.prodMk_nhds (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
        tendsto_const_nhds)
    have hY1 : Tendsto (fun ε : ℝ => X ε (t₀ + τ) - D ε) (𝓝[>] 0) (𝓝 (X 0 (t₀ + τ))) := by
      have := hX1.sub hD0
      rwa [sub_zero] at this
    have hu : IsUnit (schurC P (X 0 (t₀ + τ))) := hη₃' (by
      rw [Real.dist_eq, add_sub_cancel_left, hτ]; exact hη3)
    have hS1 := tendsto_schurS P hu hY1
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hS1).eventually (gt_mem_nhds (by positivity))
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp ((hend (-η) (by rw [abs_neg, abs_of_pos hηpos])).and
      (hend η (abs_of_pos hηpos))))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεδ => ?_⟩
  have hεδ₁ : ε < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεδ₂ : ε < δ₂ := lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨hendL, hendR⟩ := hδ₂' (show dist ε 0 < δ₂ by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ₂) hε
  rw [← sub_eq_add_neg] at hendL
  -- (7) the path argument on `[t₀ - η, t₀ + η]`
  have hin : ∀ u ∈ Icc (0 : ℝ) (2 * η), |t₀ - η + u - t₀| < η₁ := by
    intro u hu
    have : |t₀ - η + u - t₀| ≤ η := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    linarith
  have hBc : ContinuousOn (fun u => schurS P (X ε (t₀ - η + u) - D ε)) (Icc 0 (2 * η)) := by
    intro u hu
    have hun := (hoff ε (t₀ - η + u) hε hεδ₁ (hin u hu)).2.1
    have hc : Tendsto (fun u' => X ε (t₀ - η + u') - D ε) (𝓝 u)
        (𝓝 (X ε (t₀ - η + u) - D ε)) := by
      have : Continuous (fun u' => X ε (t₀ - η + u') - D ε) :=
        ((hXc ε).comp (continuous_const.add continuous_id)).sub continuous_const
      exact this.tendsto u
    exact ContinuousAt.continuousWithinAt (tendsto_schurS P hun hc)
  have hYs : ∀ u x y, ⟪(X ε (t₀ - η + u) - D ε) x, y⟫ = ⟪x, (X ε (t₀ - η + u) - D ε) y⟫ := by
    intro u x y
    rw [sub_apply, sub_apply, inner_sub_left, inner_sub_right, hXs, hDs]
  have hB0 : ∀ x, P x = x → 0 ≤ ⟪x, schurS P (X ε (t₀ - η + 0) - D ε) x⟫ := by
    intro x hx
    have e : t₀ - η + 0 = t₀ - η := by ring
    rw [e]
    have h1 := hleft x hx
    have h2 := quad_le_norm (schurS P (X ε (t₀ - η) - D ε) - schurS P (X 0 (t₀ - η))) x
    rw [sub_apply, inner_sub_right] at h2
    have h3 := mul_le_mul_of_nonneg_right hendL.le (sq_nonneg ‖x‖)
    have h4 : 0 ≤ η * σ₀ * ‖x‖ ^ 2 := by positivity
    have := (abs_le.mp h2).1
    nlinarith
  have hBT : ⟪w, schurS P (X ε (t₀ - η + 2 * η) - D ε) w⟫ < 0 := by
    have e : t₀ - η + 2 * η = t₀ + η := by ring
    rw [e]
    have h1 := hright w hwP
    have h2 := quad_le_norm (schurS P (X ε (t₀ + η) - D ε) - schurS P (X 0 (t₀ + η))) w
    rw [sub_apply, inner_sub_right] at h2
    have h3 := mul_le_mul_of_nonneg_right hendR.le (sq_nonneg ‖w‖)
    have h4 : 0 < η * σ₀ * ‖w‖ ^ 2 := by
      have := norm_pos_iff.mpr hw0; positivity
    have := (abs_le.mp h2).2
    nlinarith
  have hAB : ∀ u ∈ Icc 0 (2 * η), ∀ x, P x = x → x ≠ 0 →
      ⟪x, schurS P (X ε (t₀ - η + u) - D ε) x⟫ < ⟪x, schurS P (X ε (t₀ - η + u)) x⟫ := by
    intro u hu x hx hx0
    obtain ⟨-, -, hΦ⟩ := hoff ε (t₀ - η + u) hε hεδ₁ (hin u hu)
    set Φ := ε⁻¹ • (schurS P (X ε (t₀ - η + u)) - schurS P (X ε (t₀ - η + u) - D ε)) -
      P * D₁ * P with hΦdef
    have hdiff : schurS P (X ε (t₀ - η + u)) - schurS P (X ε (t₀ - η + u) - D ε) =
        ε • (P * D₁ * P + Φ) := by
      rw [hΦdef, add_sub_cancel, smul_smul, mul_inv_cancel₀ (ne_of_gt hε), one_smul]
    have hPDP : ⟪x, (P * D₁ * P) x⟫ = ⟪x, D₁ x⟫ := by
      rw [mul_apply_eq_comp, mul_apply_eq_comp, hx, ← hPs, hx]
    have hform : ⟪x, schurS P (X ε (t₀ - η + u)) x⟫ - ⟪x, schurS P (X ε (t₀ - η + u) - D ε) x⟫ =
        ε * (⟪x, D₁ x⟫ + ⟪x, Φ x⟫) := by
      rw [← inner_sub_right, ← sub_apply, hdiff, smul_apply, inner_smul_right, add_apply,
        inner_add_right, hPDP]
    have hq := quad_le_norm Φ x
    have hn := hνc x hx
    have hx2 : 0 < ν * ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx0; positivity
    have h3 := mul_le_mul_of_nonneg_right hΦ.le (sq_nonneg ‖x‖)
    have h4 := (abs_le.mp hq).1
    have h5 : 0 < ⟪x, D₁ x⟫ + ⟪x, Φ x⟫ := by nlinarith
    have h6 : 0 < ε * (⟪x, D₁ x⟫ + ⟪x, Φ x⟫) := mul_pos hε h5
    linarith
  obtain ⟨u, hu0, huT, hAinj, y, hyP, hy0, hBy⟩ :=
    core_separation P hP hPs (fun u => schurS P (X ε (t₀ - η + u)))
      (fun u => schurS P (X ε (t₀ - η + u) - D ε)) (2 * η) (by positivity) hBc
      (fun u x y => schurS_symm P _ hPs (hYs u) x y)
      (fun u v => schurS_left P _ hP v) (fun u v => schurS_right P _ hP v)
      hB0 w hwP hBT hAB
  have huI : u ∈ Icc (0 : ℝ) (2 * η) := ⟨hu0, huT.le⟩
  obtain ⟨hCX, hCY, -⟩ := hoff ε (t₀ - η + u) hε hεδ₁ (hin u huI)
  refine ⟨t₀ - η + u, (schur_unit_iff hP hCX).mpr hAinj, fun hY => ?_⟩
  exact hy0 ((schur_unit_iff hP hCY).mp hY y hyP hBy)

/-- Perturbative separation, either sign of the first-order correction on the kernel. -/
theorem separation_of_vacuum_data
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, P v = v → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  rcases hsign with hneg | hpos
  · -- reflect the angle about `t₀` and change the overall sign
    set Xr : ℝ → ℝ → E →L[ℝ] E := fun ε t => -X ε (2 * t₀ - t) with hXr
    set Dr : ℝ → E →L[ℝ] E := fun ε => -D ε with hDr
    have h2t : 2 * t₀ - t₀ = t₀ := by ring
    have hXr0 : Xr 0 t₀ = -X 0 t₀ := by simp only [hXr, h2t]
    have hXrs : ∀ ε t x y, ⟪Xr ε t x, y⟫ = ⟪x, Xr ε t y⟫ := by
      intro ε t x y
      simp only [hXr, neg_apply, inner_neg_left, inner_neg_right, hXs]
    have hDrs : ∀ ε x y, ⟪Dr ε x, y⟫ = ⟪x, Dr ε y⟫ := by
      intro ε x y
      simp only [hDr, neg_apply, inner_neg_left, inner_neg_right, hDs]
    have hXrc : ∀ ε, Continuous (Xr ε) := fun ε =>
      ((hXc ε).comp (continuous_const.sub continuous_id)).neg
    have hjr : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => Xr p.1 p.2) (0, t) := by
      intro t ht
      have h1 : |2 * t₀ - t - t₀| < η₀ := by
        rw [show 2 * t₀ - t - t₀ = -(t - t₀) by ring, abs_neg]; exact ht
      have h2 := hjoint (2 * t₀ - t) h1
      have hmap : ContinuousAt (fun p : ℝ × ℝ => (p.1, 2 * t₀ - p.2)) (0, t) :=
        (continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousAt
      have h3 := ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1, 2 * t₀ - p.2))
        (g := fun p : ℝ × ℝ => X p.1 p.2) h2 hmap
      exact h3.neg
    have hderr : HasDerivAt (Xr 0) X' t₀ := by
      have h1 : HasDerivAt (fun t : ℝ => 2 * t₀ - t) (-1) t₀ := by
        simpa using (hasDerivAt_id t₀).const_sub (2 * t₀)
      have h2 : HasDerivAt (X 0) X' (2 * t₀ - t₀) := by rw [h2t]; exact hder
      have h3 := h2.scomp t₀ h1
      have h4 := h3.neg
      simp only [neg_smul, one_smul, neg_neg] at h4
      exact h4
    have hDr1 : Tendsto (fun ε : ℝ => ε⁻¹ • Dr ε) (𝓝[>] 0) (𝓝 (-D₁)) := by
      simp only [hDr, smul_neg]
      exact hD.neg
    have hXrP : Xr 0 t₀ * P = 0 := by rw [hXr0, neg_mul, hXP, neg_zero]
    have hkerr : ∀ x, Xr 0 t₀ x = 0 → P x = x := by
      intro x hx
      rw [hXr0, neg_apply, neg_eq_zero] at hx
      exact hker x hx
    have hposr : ∀ v, P v = v → v ≠ 0 → 0 < ⟪v, (-D₁) v⟫ := by
      intro v hv hv0
      rw [neg_apply, inner_neg_right]
      linarith [hneg v hv hv0]
    obtain ⟨δ, hδ, hsep⟩ := separation_of_vacuum_data_pos Xr Dr P hP hPs hXrs hDrs hXrc t₀ η₀ hη₀
      hjr X' hderr (-D₁) hDr1 hXrP hkerr w hwP hw0 hslope hposr
    refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
    obtain ⟨t, hu, hnu⟩ := hsep ε hε hεδ
    refine ⟨2 * t₀ - t, ?_, ?_⟩
    · have := hu.neg
      simpa [hXr] using this
    · intro hcon
      apply hnu
      have : Xr ε t - Dr ε = -(X ε (2 * t₀ - t) - D ε) := by
        simp only [hXr, hDr]; abel
      rw [this]
      exact hcon.neg
  · exact separation_of_vacuum_data_pos X D P hP hPs hXs hDs hXc t₀ η₀ hη₀ hjoint X' hder D₁ hD
      hXP hker w hwP hw0 hslope hpos

/-- The same with the kernel of the vacuum carrier itself as the crossing space. -/
theorem separation_of_vacuum_kernel
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ → ContinuousAt (fun p : ℝ × ℝ => X p.1 p.2) (0, t))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hne : ∃ v, X 0 t₀ v = 0 ∧ v ≠ 0)
    (hslope : ∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, X 0 t₀ v = 0 → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε) := by
  set K : Submodule ℝ E := LinearMap.ker (X 0 t₀ : E →ₗ[ℝ] E) with hK
  set P : E →L[ℝ] E := K.starProjection with hPdef
  have hP : P * P = P := K.isIdempotentElem_starProjection
  have hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫ := fun x y => K.inner_starProjection_left_eq_right x y
  have hmem : ∀ x, P x = x ↔ X 0 t₀ x = 0 := by
    intro x
    rw [hPdef, Submodule.starProjection_eq_self_iff, hK, LinearMap.mem_ker]
    try rfl
  have hXP : X 0 t₀ * P = 0 := by
    ext x
    rw [mul_apply_eq_comp, zero_apply]
    have : P x ∈ K := K.starProjection_apply_mem x
    rw [hK, LinearMap.mem_ker] at this
    exact this
  obtain ⟨w, hw, hw0⟩ := hne
  refine separation_of_vacuum_data X D P hP hPs hXs hDs hXc t₀ η₀ hη₀ hjoint X' hder D₁ hD hXP
    (fun x hx => (hmem x).mpr hx) w ((hmem w).mpr hw) hw0
    (fun v hv hv0 => hslope v ((hmem v).mp hv) hv0) ?_
  rcases hsign with h | h
  · exact Or.inl (fun v hv hv0 => h v ((hmem v).mp hv) hv0)
  · exact Or.inr (fun v hv hv0 => h v ((hmem v).mp hv) hv0)

end MainTheorem

end AdalyFormal.Round9.Guarded.AnalyticR1

import Mathlib

/-!
# D1IVT -- a continuous path of symmetric operators on a finite-dimensional Hilbert space that starts positive semidefinite and ends with a negative direction passes through a NON-UNIT.
Pure Mathlib; no project imports.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open Set

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def PSD (F : E →L[ℝ] E) : Prop := ∀ v, 0 ≤ ⟪v, F v⟫

theorem psd_kernel (F : E →L[ℝ] E) (hs : ∀ x y, ⟪F x, y⟫ = ⟪x, F y⟫) (hp : PSD F) (v : E)
    (h : ⟪v, F v⟫ = 0) : F v = 0 := by
  have key : ∀ w : E, ⟪w, F v⟫ = 0 := by
    intro w
    by_contra hc
    set c := ⟪w, F v⟫ with hcdef
    set d := ⟪w, F w⟫ with hddef
    have hd : 0 ≤ d := hp w
    set ε : ℝ := -c / (d + 1) with hε
    have h1 := hp (v + ε • w)
    have e1 : ⟪v + ε • w, F (v + ε • w)⟫ = ⟪v, F v⟫ + ε * ⟪v, F w⟫ + ε * ⟪w, F v⟫ + ε * ε * ⟪w, F w⟫ := by
      simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      ring
    have e2 : ⟪v, F w⟫ = ⟪w, F v⟫ := by rw [← hs v w, real_inner_comm]
    rw [e1, e2, h] at h1
    have hd1 : 0 < d + 1 := by linarith
    have : ε * c + ε * c + ε * ε * d = c ^ 2 * (-(d + 2)) / (d + 1) ^ 2 := by
      rw [hε]; field_simp; ring
    have hc2 : 0 < c ^ 2 := by positivity
    have hneg : c ^ 2 * (-(d + 2)) / (d + 1) ^ 2 < 0 := by
      apply div_neg_of_neg_of_pos
      · nlinarith
      · positivity
    nlinarith
  exact inner_self_eq_zero.mp (key _)

theorem psd_coercive (F : E →L[ℝ] E) (hs : ∀ x y, ⟪F x, y⟫ = ⟪x, F y⟫) (hp : PSD F) (hu : IsUnit F) :
    ∃ m : ℝ, 0 < m ∧ ∀ v, m * ‖v‖ ^ 2 ≤ ⟪v, F v⟫ := by
  by_cases hE : Subsingleton E
  · exact ⟨1, one_pos, fun v => by
      have : v = 0 := Subsingleton.elim _ _
      subst this; simp⟩
  · rw [not_subsingleton_iff_nontrivial] at hE
    have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    have hcont : Continuous (fun v : E => ⟪v, F v⟫) := by fun_prop
    obtain ⟨v0, hv0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont.continuousOn
    refine ⟨⟪v0, F v0⟫, ?_, fun v => ?_⟩
    · have hn : ‖v0‖ = 1 := by simpa using hv0
      rcases (hp v0).lt_or_eq with h | h
      · exact h
      · exfalso
        have := psd_kernel F hs hp v0 h.symm
        have hinj : Function.Injective F := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
        have : v0 = 0 := hinj (by rw [this, map_zero])
        rw [this] at hn; simp at hn
    · by_cases hv : v = 0
      · subst hv; simp
      · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
        set u := (‖v‖⁻¹) • v with hu_def
        have hun : ‖u‖ = 1 := by
          rw [hu_def, norm_smul, norm_inv, norm_norm]; field_simp
        have hmu := hmin (show u ∈ Metric.sphere (0 : E) 1 by simpa using hun)
        have hmu' : ⟪v0, F v0⟫ ≤ ⟪u, F u⟫ := hmu
        have : ⟪v, F v⟫ = ‖v‖ ^ 2 * ⟪u, F u⟫ := by
          have hv_eq : v = ‖v‖ • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
          conv_lhs => rw [hv_eq]
          simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
          ring
        rw [this]
        nlinarith [sq_nonneg ‖v‖]
end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_nonunit_path (F : ℝ → (E →L[ℝ] E)) (hc : Continuous F)
    (hs : ∀ t x y, ⟪F t x, y⟫ = ⟪x, F t y⟫) (h0 : PSD (F 0)) (T : ℝ) (hT : 0 < T) (v : E)
    (hv : ⟪v, F T v⟫ < 0) : ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ ¬ IsUnit (F t) := by
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
  refine ⟨ts, hts0, htsT', fun hu => ?_⟩
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

#print axioms exists_nonunit_path
end
end AdalyFormal.D1Literal

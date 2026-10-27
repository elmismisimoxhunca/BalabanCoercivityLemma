import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# CvN1 -- abstract finite-dimensional facts used by the coverage-necessity refutation (lane cover_necessary_20261016)

* `continuous_of_inner`, `continuous_clm_of_inner`: in a finite-dimensional real inner product space continuity can be tested on the
  real numbers `⟪w, f t⟫` (orthonormal-basis expansion); for operator families, on `⟪w, A t x⟫`.
* `apply_eq_zero_of_psd`: a positive semidefinite symmetric operator kills every vector of zero energy.
* `exists_coercive`: a positive semidefinite symmetric operator that is a unit is coercive.
* **`exists_not_isUnit`** (the intermediate-value step): a continuous family `A : ℝ → E →L[ℝ] E` of symmetric operators that is
  positive semidefinite at `a` and has a negative direction at `b ≥ a` is NOT invertible at some `t ∈ [a, b]`.
-/
set_option autoImplicit false

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open Filter Topology Set

section cont
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {X : Type*} [TopologicalSpace X]

theorem continuous_of_inner (f : X → F) (h : ∀ w : F, Continuous fun t => ⟪w, f t⟫) : Continuous f := by
  let b := stdOrthonormalBasis ℝ F
  have e : f = fun t => ∑ i, ⟪b i, f t⟫ • b i := funext fun t => (b.sum_repr' (f t)).symm
  rw [e]
  exact continuous_finsetSum _ fun i _ => (h (b i)).smul continuous_const

theorem continuous_clm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : X → E →L[ℝ] F) (h : ∀ x w, Continuous fun t => ⟪w, A t x⟫) : Continuous A :=
  continuous_clm_apply.2 fun x => continuous_of_inner _ (h x)

end cont

section psd
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem apply_eq_zero_of_psd {B : E →L[ℝ] E} (hs : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    {x : E} (hx : ⟪x, B x⟫ = 0) : B x = 0 := by
  have key : ∀ y, ⟪y, B x⟫ = 0 := by
    intro y
    have h : ∀ s : ℝ, 0 ≤ 2 * s * ⟪y, B x⟫ + s ^ 2 * ⟪y, B y⟫ := by
      intro s
      have h1 := hp (x + s • y)
      have hxy : ⟪x, B y⟫ = ⟪y, B x⟫ := by rw [← hs, real_inner_comm]
      have e : ⟪x + s • y, B (x + s • y)⟫ = ⟪x, B x⟫ + 2 * s * ⟪y, B x⟫ + s ^ 2 * ⟪y, B y⟫ := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hxy]
        ring
      rw [e, hx] at h1
      linarith
    set c := ⟪y, B x⟫
    set q := ⟪y, B y⟫
    have hq : 0 ≤ q := hp y
    have hq1 : 0 < q + 1 := by linarith
    have h1 := h (-(c / (q + 1)))
    have e2 : (2 * -(c / (q + 1)) * c + (-(c / (q + 1))) ^ 2 * q) * (q + 1) ^ 2 = -(c ^ 2 * (q + 2)) := by
      field_simp
      ring
    have h2 : 0 ≤ (2 * -(c / (q + 1)) * c + (-(c / (q + 1))) ^ 2 * q) * (q + 1) ^ 2 :=
      mul_nonneg h1 (sq_nonneg _)
    rw [e2] at h2
    have h3 : c ^ 2 * (q + 2) ≤ 0 := by linarith
    have h4 : c ^ 2 ≤ 0 := by nlinarith [sq_nonneg c]
    nlinarith [sq_nonneg c]
  have := key (B x)
  exact inner_self_eq_zero.mp this

theorem exists_coercive [FiniteDimensional ℝ E] {B : E →L[ℝ] E} (hs : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫)
    (hp : ∀ x, 0 ≤ ⟪x, B x⟫) (hu : IsUnit B) : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, B x⟫ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hinj : Function.Injective B := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  by_cases hE : Nontrivial E
  · have hK : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
    have hc : ContinuousOn (fun x => ⟪x, B x⟫) (Metric.sphere (0 : E) 1) :=
      (continuous_id.inner B.continuous).continuousOn
    obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hc
    have hx0n : ‖x0‖ = 1 := by simpa using hx0
    refine ⟨⟪x0, B x0⟫, ?_, ?_⟩
    · rcases (hp x0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hB := apply_eq_zero_of_psd hs hp h.symm
        have : x0 = 0 := hinj (by rw [hB, map_zero])
        rw [this, norm_zero] at hx0n
        exact zero_ne_one hx0n
    · intro x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
        have hu1 : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : E) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
        have hm := hmin hu1
        simp only [Set.mem_setOf_eq] at hm
        have e : ⟪‖x‖⁻¹ • x, B (‖x‖⁻¹ • x)⟫ = ‖x‖⁻¹ ^ 2 * ⟪x, B x⟫ := by
          rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
        rw [e] at hm
        calc ⟪x0, B x0⟫ * ‖x‖ ^ 2 ≤ (‖x‖⁻¹ ^ 2 * ⟪x, B x⟫) * ‖x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hm (by positivity)
          _ = ⟪x, B x⟫ := by field_simp
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp

/-- **The intermediate-value step.** -/
theorem exists_not_isUnit [FiniteDimensional ℝ E] (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {a b : ℝ} (hab : a ≤ b)
    (h0 : ∀ x, 0 ≤ ⟪x, A a x⟫) {y : E} (hy : ⟪y, A b y⟫ < 0) :
    ∃ t ∈ Icc a b, ¬ IsUnit (A t) := by
  by_contra hcon
  push_neg at hcon
  set S : Set ℝ := {t | ∀ x, 0 ≤ ⟪x, A t x⟫} with hS
  have hform : ∀ x, Continuous fun t => ⟪x, A t x⟫ := fun x =>
    continuous_const.inner ((continuous_clm_apply.1 hA) x)
  have hSc : IsClosed S := by
    have : S = ⋂ x, {t | 0 ≤ ⟪x, A t x⟫} := by ext t; simp [hS]
    rw [this]
    exact isClosed_iInter fun x => isClosed_le continuous_const (hform x)
  have hsub : Icc a b ⊆ S := by
    refine (hSc.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin h0 ?_
    rintro t ⟨htS, htI⟩
    obtain ⟨c, hc, hcoer⟩ := exists_coercive (hs t) htS (hcon t (Ico_subset_Icc_self htI))
    have hev : ∀ᶠ s in 𝓝 t, ‖A s - A t‖ < c :=
      (tendsto_iff_norm_sub_tendsto_zero.1 (hA.continuousAt (x := t)).tendsto).eventually (gt_mem_nhds hc)
    apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [hev] with s hs'
    intro x
    have h1 := hcoer x
    have h2 : |⟪x, (A s - A t) x⟫| ≤ ‖A s - A t‖ * ‖x‖ ^ 2 := by
      calc |⟪x, (A s - A t) x⟫| ≤ ‖x‖ * ‖(A s - A t) x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖A s - A t‖ * ‖x‖) := by gcongr; exact (A s - A t).le_opNorm x
        _ = ‖A s - A t‖ * ‖x‖ ^ 2 := by ring
    have e : ⟪x, A s x⟫ = ⟪x, A t x⟫ + ⟪x, (A s - A t) x⟫ := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right]; ring
    have h3 := neg_abs_le ⟪x, (A s - A t) x⟫
    have h4 : ‖A s - A t‖ * ‖x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hs'.le (sq_nonneg _)
    rw [e]
    linarith
  exact absurd (hsub ⟨hab, le_rfl⟩ y) (not_le.2 hy)

end psd

#print axioms continuous_of_inner
#print axioms continuous_clm_of_inner
#print axioms apply_eq_zero_of_psd
#print axioms exists_coercive
#print axioms exists_not_isUnit

end AdalyFormal.CoverNec

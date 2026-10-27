import D1IVT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Scratch copies of two prefix declarations (same statements and proofs), for testing only:
`unit_of_definite_complements` (round 8) and `first_carrier_crossing` (round 5). -/
namespace Scratch
open scoped RealInnerProductSpace
open Set
open AdalyFormal.D1Literal (PSD)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem unit_of_definite_complements (X : E →L[ℝ] E)
    (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, X x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, X x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    IsUnit X := by
  have hinj : Function.Injective X := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hxU : x ∉ U := by
      intro hm
      have h := hU x hm hx0
      rw [hx, inner_zero_right] at h
      exact lt_irrefl 0 h
    let U' : Submodule ℝ E := U ⊔ Submodule.span ℝ {x}
    have hneg : ∀ y ∈ U', ⟪y, X y⟫ ≤ 0 := by
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hcross : ⟪c • x, X u⟫ = 0 := by
        rw [real_inner_smul_left, ← hs x u, hx, inner_zero_left, mul_zero]
      have heq : ⟪u + c • x, X (u + c • x)⟫ = ⟪u, X u⟫ := by
        rw [map_add, map_smul, hx, smul_zero, add_zero, inner_add_left, hcross, add_zero]
      rw [heq]
      by_cases hu0 : u = 0
      · rw [hu0, map_zero, inner_zero_right]
      · exact (hU u hu hu0).le
    have hlt : U < U' := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), hxU⟩
    have hrk : Module.finrank ℝ U < Module.finrank ℝ U' := Submodule.finrank_lt_finrank_of_lt hlt
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U' V
    have hle : Module.finrank ℝ ↥(U' ⊔ V) ≤ Module.finrank ℝ E := Submodule.finrank_le _
    have hpos : Module.finrank ℝ ↥(U' ⊓ V) ≠ 0 := by omega
    have hne : U' ⊓ V ≠ ⊥ := fun h => hpos (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hneg y (Submodule.mem_inf.mp hy).1
    have h2 := hV y (Submodule.mem_inf.mp hy).2 hy0
    linarith
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : E →ₗ[ℝ] E))).mp hinj⟩

theorem first_carrier_crossing
    (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hp0 : PSD (A 0)) (hu0 : IsUnit (A 0))
    (T : ℝ) (hT : 0 < T) (z : E) (hz : ⟪z, A T z⟫ < 0) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ PSD (A t) ∧ ¬ IsUnit (A t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t → PSD (A s) ∧ IsUnit (A s)) ∧
      ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
  obtain ⟨r, hr0, hrT, hrnu⟩ :=
    AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 T hT z hz
  let K : Set ℝ := Icc 0 r ∩ {t | ¬ IsUnit (A t)}
  have hcl : IsClosed {t : ℝ | ¬ IsUnit (A t)} := by
    exact (Units.isOpen.preimage hc).isClosed_compl
  have hK : IsCompact K := isCompact_Icc.inter_right hcl
  have hrK : r ∈ K := ⟨⟨hr0, le_rfl⟩, hrnu⟩
  obtain ⟨t, htK, htmin⟩ := hK.exists_isLeast ⟨r, hrK⟩
  have htpos : 0 < t := by
    refine lt_of_le_of_ne htK.1.1 ?_
    intro ht
    exact htK.2 (ht ▸ hu0)
  have htT : t < T := lt_of_le_of_lt htK.1.2 hrT
  have hguard : ∀ s : ℝ, 0 ≤ s → s < t → IsUnit (A s) := by
    intro s hs0 hst
    by_contra hnu
    have hsK : s ∈ K := ⟨⟨hs0, le_trans hst.le htK.1.2⟩, hnu⟩
    exact (not_lt_of_ge (htmin hsK)) hst
  have hpsd : ∀ s : ℝ, 0 ≤ s → s ≤ t → PSD (A s) := by
    intro s hs0 hst w
    by_contra hneg
    have hw : ⟪w, A s w⟫ < 0 := lt_of_not_ge hneg
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · subst s
        exact False.elim ((not_lt_of_ge (hp0 w)) hw)
    obtain ⟨u, hu0, hus, hnu⟩ :=
      AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 s hspos w hw
    exact hnu (hguard u hu0 (lt_of_lt_of_le hus hst))
  have hni : ¬ Function.Injective (A t) := by
    intro hi
    apply htK.2
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := (A t).toLinearMap)).mp hi⟩
  have hk : ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
    by_contra h
    apply hni
    apply (injective_iff_map_eq_zero (A t)).mpr
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  exact ⟨t, htpos, htT, hpsd t htpos.le le_rfl, htK.2,
    fun s hs0 hst => ⟨hpsd s hs0 hst.le, hguard s hs0 hst⟩, hk⟩

end Scratch

namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)
open Scratch (unit_of_definite_complements first_carrier_crossing)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_op_le (N : E →L[ℝ] E) (u y : E) : |⟪u, N y⟫| ≤ ‖N‖ * ‖u‖ * ‖y‖ := by
  calc |⟪u, N y⟫| ≤ ‖u‖ * ‖N y‖ := abs_real_inner_le_norm u (N y)
    _ ≤ ‖u‖ * (‖N‖ * ‖y‖) := mul_le_mul_of_nonneg_left (N.le_opNorm y) (norm_nonneg u)
    _ = ‖N‖ * ‖u‖ * ‖y‖ := by ring

/-- Two-block positivity with respect to `E = K ⊕ Kᗮ`: a definite `K`-block, a
definite `Kᗮ`-block and a small off-diagonal block give a positive definite form. -/
theorem block_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (K : Submodule ℝ E)
    {a g b : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g)
    (hK : ∀ u ∈ K, a * ‖u‖ ^ 2 ≤ ⟪u, X u⟫)
    (hKp : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫)
    (hX : ∀ u ∈ K, ∀ y ∈ Kᗮ, |⟪u, X y⟫| ≤ b * ‖u‖ * ‖y‖) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hsym : ⟪y, X u⟫ = ⟪u, X y⟫ := by rw [← hs y u, real_inner_comm]
  have hexp : ⟪u + y, X (u + y)⟫ = ⟪u, X u⟫ + 2 * ⟪u, X y⟫ + ⟪y, X y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]; ring
  rw [hexp]
  have h1 := hK u hu
  have h2 := hKp y hy
  have h3 : -(b * ‖u‖ * ‖y‖) ≤ ⟪u, X y⟫ := (abs_le.mp (hX u hu y hy)).1
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have key : 0 < a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2 := by
    have hQ : a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) =
        (a * ‖u‖ - b * ‖y‖) ^ 2 + (a * g - b ^ 2) * ‖y‖ ^ 2 := by ring
    rcases hr0.lt_or_eq with hr | hr
    · have hpos : 0 < (a * g - b ^ 2) * ‖y‖ ^ 2 := mul_pos (by linarith) (pow_pos hr 2)
      have hm : 0 < a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) := by
        rw [hQ]; linarith [sq_nonneg (a * ‖u‖ - b * ‖y‖)]
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' ha.le
      linarith
    · have hy0 : y = 0 := norm_eq_zero.mp hr.symm
      have hu0 : u ≠ 0 := by
        intro hu0
        apply hx
        rw [hu0, hy0, add_zero]
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      rw [← hr]
      have : 0 < a * ‖u‖ ^ 2 := mul_pos ha (pow_pos hun 2)
      linarith
  linarith

omit [FiniteDimensional ℝ E] in
/-- The quadratic form of `A0 + τ At + ε B + R` on a kernel vector of `A0` on which
`At` and `B` act as scalars. -/
theorem kernel_form (A0 At B R : E →L[ℝ] E) (τ ε σ β : ℝ) (u : E) (h0 : A0 u = 0)
    (ht : ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ⟪u, B u⟫ = β * ‖u‖ ^ 2) :
    ⟪u, (A0 + τ • At + ε • B + R) u⟫ = (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ := by
  simp only [add_apply, smul_apply, inner_add_right,
    real_inner_smul_right, h0, inner_zero_right, ht, hb]
  ring

omit [FiniteDimensional ℝ E] in
theorem expansion_dist (A0 At B R : E →L[ℝ] E) (τ ε : ℝ) :
    ‖(A0 + τ • At + ε • B + R) - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
  have h : (A0 + τ • At + ε • B + R) - A0 = τ • At + ε • B + R := by abel
  rw [h]
  calc ‖τ • At + ε • B + R‖ ≤ ‖τ • At + ε • B‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖τ • At‖ + ‖ε • B‖ + ‖R‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

omit [FiniteDimensional ℝ E] in
theorem perp_lower (A0 X : E →L[ℝ] E) (K : Submodule ℝ E) {g δ : ℝ}
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A0 y⟫) (hδ : ‖X - A0‖ ≤ δ) :
    ∀ y ∈ Kᗮ, (g - δ) * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  intro y hy
  have h1 := hgap y hy
  have h2 := (abs_le.mp (abs_inner_op_le (X - A0) y y)).1
  have h3 : ⟪y, X y⟫ = ⟪y, A0 y⟫ + ⟪y, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right]; ring
  have h4 : ‖X - A0‖ * ‖y‖ * ‖y‖ ≤ δ * ‖y‖ ^ 2 := by
    have hy0 : 0 ≤ ‖y‖ * ‖y‖ := mul_nonneg (norm_nonneg y) (norm_nonneg y)
    calc ‖X - A0‖ * ‖y‖ * ‖y‖ = ‖X - A0‖ * (‖y‖ * ‖y‖) := by ring
      _ ≤ δ * (‖y‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ hy0
      _ = δ * ‖y‖ ^ 2 := by ring
  rw [h3]
  linarith

omit [FiniteDimensional ℝ E] in
theorem cross_upper (A0 X : E →L[ℝ] E) (hs0 : ∀ x y, ⟪A0 x, y⟫ = ⟪x, A0 y⟫)
    (K : Submodule ℝ E) (hker : ∀ u ∈ K, A0 u = 0) {δ : ℝ} (hδ : ‖X - A0‖ ≤ δ) :
    ∀ u ∈ K, ∀ y : E, |⟪u, X y⟫| ≤ δ * ‖u‖ * ‖y‖ := by
  intro u hu y
  have h0 : ⟪u, A0 y⟫ = 0 := by rw [← hs0, hker u hu, inner_zero_left]
  have h3 : ⟪u, X y⟫ = ⟪u, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right, h0, sub_zero]
  rw [h3]
  have huy : 0 ≤ ‖u‖ * ‖y‖ := mul_nonneg (norm_nonneg u) (norm_nonneg y)
  calc |⟪u, (X - A0) y⟫| ≤ ‖X - A0‖ * ‖u‖ * ‖y‖ := abs_inner_op_le _ _ _
    _ = ‖X - A0‖ * (‖u‖ * ‖y‖) := by ring
    _ ≤ δ * (‖u‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ huy
    _ = δ * ‖u‖ * ‖y‖ := by ring

omit [FiniteDimensional ℝ E] in
/-- First-order bookkeeping: if `X = A0 + τ At + ε B + R` with `‖R‖ ≤ ρ`, then on the
kernel `K` of `A0` (where `At`, `B` act as scalars) the form of `X` is its first-order
value up to `ρ`, and `X` is within `|τ|‖At‖ + |ε|‖B‖ + ρ` of `A0`. -/
theorem kernel_form_bounds (A0 At B X : E →L[ℝ] E) (K : Submodule ℝ E)
    (hker : ∀ u ∈ K, A0 u = 0) {σ β τ ε ρ : ℝ}
    (ht : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ∀ u ∈ K, ⟪u, B u⟫ = β * ‖u‖ ^ 2)
    (hR : ‖X - A0 - τ • At - ε • B‖ ≤ ρ) :
    (∀ u ∈ K, |⟪u, X u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2| ≤ ρ * ‖u‖ ^ 2) ∧
      ‖X - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ρ := by
  obtain ⟨R, hR_def⟩ : ∃ R : E →L[ℝ] E, R = X - A0 - τ • At - ε • B := ⟨_, rfl⟩
  have hRn : ‖R‖ ≤ ρ := by rw [hR_def]; exact hR
  have hX : X = A0 + τ • At + ε • B + R := by rw [hR_def]; abel
  constructor
  · intro u hu
    rw [hX, kernel_form A0 At B R τ ε σ β u (hker u hu) (ht u hu) (hb u hu)]
    have h1 := abs_inner_op_le R u u
    have h2 : ‖R‖ * ‖u‖ * ‖u‖ ≤ ρ * ‖u‖ ^ 2 := by
      have hu0 : 0 ≤ ‖u‖ * ‖u‖ := mul_nonneg (norm_nonneg u) (norm_nonneg u)
      calc ‖R‖ * ‖u‖ * ‖u‖ = ‖R‖ * (‖u‖ * ‖u‖) := by ring
        _ ≤ ρ * (‖u‖ * ‖u‖) := mul_le_mul_of_nonneg_right hRn hu0
        _ = ρ * ‖u‖ ^ 2 := by ring
    have h3 : (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2 = ⟪u, R u⟫ := by
      ring
    rw [h3]
    exact le_trans h1 h2
  · rw [hX]
    exact le_trans (expansion_dist A0 At B R τ ε) (by linarith)

/-- **Perturbative sign-free separation.**  `A ε t` is a symmetric two-parameter
family, `D ε` a symmetric correction.  At `ε = 0` and `t = ts` the carrier `A 0 ts`
vanishes on a nonzero subspace `K` and is bounded below by `g > 0` on `Kᗮ` (so `A 0 ts`
is positive semidefinite and `ts` is a first crossing).  Suppose `(ε,t) ↦ A ε t` and
`ε ↦ D ε` are differentiable at `(0,ts)` and `0` in the first-order sense of `hAexp` and
`hDexp` (in particular `D 0 = 0`), with derivatives `At`, `Ae`, `De` acting on `K` as the
scalars `σ < 0`, `α`, `c`.  If `c ≠ 0` then for every sufficiently small `ε > 0` there is
an interval `[t₀,t₁]` of carrier units on which `A ε · - D ε` passes from positive
semidefinite to a negative direction.  For `c > 0` the carrier is positive definite on
the interval (pre-crossing), for `c < 0` it is an indefinite unit (post-crossing).
Only `c ≠ 0` enters, never its value. -/
theorem perturbative_sign_change
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (ts : ℝ) (K : Submodule ℝ E) (g σ α c : ℝ) (At Ae De : E →L[ℝ] E)
    (hker : ∀ u ∈ K, A 0 ts u = 0)
    (hg : 0 < g) (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A 0 ts y⟫)
    (hne : ∃ u ∈ K, u ≠ 0)
    (hσ : σ < 0) (hc : c ≠ 0)
    (hAt : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2)
    (hAe : ∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2)
    (hDe : ∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2)
    (hAexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖A ε (ts + τ) - A 0 ts - τ • At - ε • Ae‖ ≤ η * (|ε| + |τ|))
    (hDexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r →
      ‖D ε - ε • De‖ ≤ η * |ε|) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧ (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A ε t)) ∧
        PSD (A ε t₀ - D ε) ∧ ∃ w : E, ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
  have hs0 : ∀ x y, ⟪A 0 ts x, y⟫ = ⟪x, A 0 ts y⟫ := hsA 0 ts
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = -σ := ⟨_, rfl⟩
  have hs : 0 < s := by linarith
  have hσs : |σ| = s := by rw [abs_of_neg hσ, hs_def]
  have hcabs : 0 < |c| := abs_pos.mpr hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = |c| / (3 * s) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ_def]; exact div_pos hcabs (by linarith)
  have hsκ : s * κ = |c| / 3 := by
    rw [hκ_def, mul_div_assoc', div_eq_div_iff (mul_pos (by norm_num) hs).ne' (by norm_num)]
    ring
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = |α - c| / s + κ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ_def]; exact add_nonneg (div_nonneg (abs_nonneg _) hs.le) hκ0.le
  obtain ⟨η₁, hη₁_def⟩ : ∃ η : ℝ, η = |c| / (24 * (1 + Λ)) := ⟨_, rfl⟩
  have hη₁0 : 0 < η₁ := by rw [hη₁_def]; exact div_pos hcabs (by linarith)
  have hη₁Λ : η₁ * (1 + Λ) = |c| / 24 := by
    rw [hη₁_def, div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos (by norm_num) (by linarith : (0 : ℝ) < 1 + Λ)).ne' (by norm_num)]
    ring
  have hη₂0 : (0 : ℝ) < |c| / 24 := div_pos hcabs (by norm_num)
  obtain ⟨r₁, hr₁, hA1⟩ := hAexp η₁ hη₁0
  obtain ⟨r₂, hr₂, hD1⟩ := hDexp (|c| / 24) hη₂0
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = Λ * ‖At‖ + ‖Ae‖ + ‖De‖ + |c| / 12 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    have h1 := mul_nonneg hΛ0 (norm_nonneg At)
    have h2 := norm_nonneg Ae
    have h3 := norm_nonneg De
    have h4 : 0 < |c| / 12 := div_pos hcabs (by norm_num)
    rw [hC_def]; linarith
  have h1Λ : (0 : ℝ) < 1 + Λ := by linarith
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have h16C : (0 : ℝ) < 16 * C ^ 2 := mul_pos (by norm_num) (pow_pos hC0 2)
  have hr₁' : 0 < r₁ / (1 + Λ) := div_pos hr₁ h1Λ
  have hgC : 0 < g / (2 * C) := div_pos hg h2C
  have hcgC : 0 < |c| * g / (16 * C ^ 2) := div_pos (mul_pos hcabs hg) h16C
  refine ⟨min (min (r₁ / (1 + Λ)) r₂) (min (g / (2 * C)) (|c| * g / (16 * C ^ 2))),
    lt_min (lt_min hr₁' hr₂) (lt_min hgC hcgC), ?_⟩
  intro ε hε hε₀
  have hε1 : ε < r₁ / (1 + Λ) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : ε < r₂ := lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : ε < g / (2 * C) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε4 : ε < |c| * g / (16 * C ^ 2) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεr₁ : ε * (1 + Λ) < r₁ := (lt_div_iff₀ h1Λ).mp hε1
  have hεC : ε * C < g / 2 := by
    have h := (lt_div_iff₀ h2C).mp hε3
    linarith
  have hεC2 : ε * C ^ 2 * 16 < |c| * g := by
    have h := (lt_div_iff₀ h16C).mp hε4
    linarith
  have hεabs : |ε| = ε := abs_of_pos hε
  obtain ⟨τC, hτC_def⟩ : ∃ τ : ℝ, τ = ε * (α - c) / s := ⟨_, rfl⟩
  have hστC : σ * τC = -(ε * (α - c)) := by
    rw [hτC_def, mul_div_assoc', div_eq_iff hs.ne', hs_def]; ring
  have hτCabs : |τC| = ε * (|α - c| / s) := by
    rw [hτC_def, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hs]; ring
  have hDn : ‖D ε - ε • De‖ ≤ ε * |c| / 24 := by
    have h := hD1 ε (by rw [hεabs]; exact hε2)
    rw [hεabs] at h
    linarith
  -- every angle in the window `|t - ts - τC| ≤ ε κ`
  have window : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ →
      ‖A ε t - A 0 ts‖ ≤ ε * C ∧ ‖(A ε t - D ε) - A 0 ts‖ ≤ ε * C ∧
      (∀ u ∈ K, |⟪u, A ε t u⟫ - (ε * c + σ * (t - ts - τC)) * ‖u‖ ^ 2| ≤
        ε * |c| / 24 * ‖u‖ ^ 2) ∧
      (∀ u ∈ K, |⟪u, (A ε t - D ε) u⟫ - σ * (t - ts - τC) * ‖u‖ ^ 2| ≤
        ε * |c| / 12 * ‖u‖ ^ 2) := by
    intro t ht
    obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = t - ts := ⟨_, rfl⟩
    have hτ : |τ| ≤ ε * Λ := by
      have h1 : τ = τC + (t - ts - τC) := by rw [hτ_def]; ring
      calc |τ| = |τC + (t - ts - τC)| := by rw [h1]
        _ ≤ |τC| + |t - ts - τC| := abs_add_le _ _
        _ ≤ ε * (|α - c| / s) + ε * κ := by rw [hτCabs]; linarith
        _ = ε * Λ := by rw [hΛ_def]; ring
    have hεΛ : 0 ≤ ε * Λ := mul_nonneg hε.le hΛ0
    have hτr : |τ| < r₁ := by linarith
    have hεr : |ε| < r₁ := by rw [hεabs]; linarith
    have hA := hA1 ε τ hεr hτr
    have hts : ts + τ = t := by rw [hτ_def]; ring
    rw [hts] at hA
    have hAn : ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ ε * |c| / 24 := by
      calc ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ η₁ * (|ε| + |τ|) := hA
        _ ≤ η₁ * (ε + ε * Λ) :=
          mul_le_mul_of_nonneg_left (by rw [hεabs]; linarith) hη₁0.le
        _ = ε * (η₁ * (1 + Λ)) := by ring
        _ = ε * |c| / 24 := by rw [hη₁Λ]; ring
    have hRD : ‖(A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De)‖ ≤ ε * |c| / 12 := by
      have h : (A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De) =
          (A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De) := by
        rw [smul_sub]; abel
      rw [h]
      calc ‖(A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De)‖
          ≤ ‖A ε t - A 0 ts - τ • At - ε • Ae‖ + ‖D ε - ε • De‖ := norm_sub_le _ _
        _ ≤ ε * |c| / 24 + ε * |c| / 24 := add_le_add hAn hDn
        _ = ε * |c| / 12 := by ring
    have hADe : ∀ u ∈ K, ⟪u, (Ae - De) u⟫ = (α - c) * ‖u‖ ^ 2 := by
      intro u hu
      simp only [sub_apply, inner_sub_right, hAe u hu, hDe u hu]
      ring
    obtain ⟨hKA, hdA⟩ := kernel_form_bounds (A 0 ts) At Ae (A ε t) K hker hAt hAe hAn
    obtain ⟨hKD, hdD⟩ :=
      kernel_form_bounds (A 0 ts) At (Ae - De) (A ε t - D ε) K hker hAt hADe hRD
    have hτAt : |τ| * ‖At‖ ≤ ε * Λ * ‖At‖ := mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
    have hεDe : 0 ≤ ε * ‖De‖ := mul_nonneg hε.le (norm_nonneg _)
    have hεc : 0 ≤ ε * |c| := mul_nonneg hε.le (abs_nonneg _)
    have hsub : ‖Ae - De‖ ≤ ‖Ae‖ + ‖De‖ := norm_sub_le _ _
    have hεsub : ε * ‖Ae - De‖ ≤ ε * (‖Ae‖ + ‖De‖) := mul_le_mul_of_nonneg_left hsub hε.le
    have hστ1 : σ * τ + ε * α = ε * c + σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    have hστ2 : σ * τ + ε * (α - c) = σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc ‖A ε t - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae‖ + ε * |c| / 24 := hdA
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · calc ‖(A ε t - D ε) - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae - De‖ + ε * |c| / 12 := hdD
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · intro u hu
      have h := hKA u hu
      rw [hστ1] at h
      exact h
    · intro u hu
      have h := hKD u hu
      rw [hστ2] at h
      exact h
  have hσw : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ → |σ * (t - ts - τC)| ≤ ε * |c| / 3 := by
    intro t ht
    rw [abs_mul, hσs]
    calc s * |t - ts - τC| ≤ s * (ε * κ) := mul_le_mul_of_nonneg_left ht hs.le
      _ = ε * (s * κ) := by ring
      _ = ε * |c| / 3 := by rw [hsκ]; ring
  obtain ⟨u₀, hu₀K, hu₀⟩ := hne
  have hεκ : 0 < ε * κ := mul_pos hε hκ0
  refine ⟨ts + τC - ε * κ, ts + τC + ε * κ, by linarith, ?_, ?_, ?_⟩
  · -- the interval guard
    intro t ht0 ht1
    have hw : |t - ts - τC| ≤ ε * κ := abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨hdA, -, hKA, -⟩ := window t hw
    have hδ := abs_le.mp (hσw t hw)
    have hperp := perp_lower (A 0 ts) (A ε t) K hgap hdA
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · -- post-crossing: negative definite on `K`, positive definite on `Kᗮ`
      have hca : |c| = -c := abs_of_neg hcneg
      apply unit_of_definite_complements (A ε t) (hsA ε t) K Kᗮ
      · intro u hu hu0
        have h := (abs_le.mp (hKA u hu)).2
        have hun : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
        rw [hca] at h hδ
        have hm := mul_le_mul_of_nonneg_right hδ.2 hun.le
        have hp : 0 < ε * (-c) * ‖u‖ ^ 2 := mul_pos (mul_pos hε (by linarith)) hun
        linarith
      · intro y hy hy0
        have h := hperp y hy
        have hyn : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
        have hg2 : 0 < g - ε * C := by linarith
        have := mul_pos hg2 hyn
        linarith
      · exact (Submodule.finrank_add_finrank_orthogonal K).ge
    · -- pre-crossing: positive definite
      have hca : |c| = c := abs_of_pos hcpos
      have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, A ε t x⟫ := by
        refine block_pos (A ε t) (hsA ε t) K (a := ε * c / 2) (g := g / 2) (b := ε * C)
          (by have := mul_pos hε hcpos; linarith) ?_ ?_ ?_ ?_
        · rw [hca] at hεC2
          have h3 : ε * (ε * C ^ 2 * 16) < ε * (c * g) := mul_lt_mul_of_pos_left hεC2 hε
          have hpos : 0 < ε * (c * g) := mul_pos hε (mul_pos hcpos hg)
          linarith
        · intro u hu
          have h := (abs_le.mp (hKA u hu)).1
          rw [hca] at h hδ
          have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
          have hm := mul_le_mul_of_nonneg_right hδ.1 hun
          have hp : 0 ≤ ε * c * ‖u‖ ^ 2 := mul_nonneg (mul_nonneg hε.le hcpos.le) hun
          linarith
        · intro y hy
          have h := hperp y hy
          have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
          have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hyn
          linarith
        · intro u hu y _
          exact cross_upper (A 0 ts) (A ε t) hs0 K hker hdA u hu y
      refine unit_of_definite_complements (A ε t) (hsA ε t) ⊥ ⊤ ?_
        (fun x _ hx0 => hpd x hx0) ?_
      · intro x hx hx0
        exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
      · simp
  · -- the corrected carrier is positive semidefinite at `t₀`
    have hw : |ts + τC - ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC - ε * κ - ts - τC = -(ε * κ) by ring, abs_neg, abs_of_pos hεκ])
    obtain ⟨-, hdD, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC - ε * κ - ts - τC) = ε * |c| / 3 := by
      have h : σ * (ts + τC - ε * κ - ts - τC) = ε * (s * κ) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    have hperp := perp_lower (A 0 ts) (A ε (ts + τC - ε * κ) - D ε) K hgap hdD
    have hsM : ∀ x y, ⟪(A ε (ts + τC - ε * κ) - D ε) x, y⟫ =
        ⟪x, (A ε (ts + τC - ε * κ) - D ε) y⟫ := by
      intro x y
      simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
    have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε (ts + τC - ε * κ) - D ε) x⟫ := by
      refine block_pos _ hsM K (a := ε * |c| / 4) (g := g / 2) (b := ε * C)
        (by have := mul_pos hε hcabs; linarith) ?_ ?_ ?_ ?_
      · have h3 : ε * (ε * C ^ 2 * 16) < ε * (|c| * g) := mul_lt_mul_of_pos_left hεC2 hε
        have hpos : 0 < ε * (|c| * g) := mul_pos hε (mul_pos hcabs hg)
        linarith
      · intro u hu
        have h := (abs_le.mp (hKD u hu)).1
        rw [hval] at h
        have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
        linarith
      · intro y hy
        have h := hperp y hy
        have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
        have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hyn
        linarith
      · intro u hu y _
        exact cross_upper (A 0 ts) _ hs0 K hker hdD u hu y
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpd v hv).le
  · -- a negative direction of the corrected carrier at `t₁`
    have hw : |ts + τC + ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC + ε * κ - ts - τC = ε * κ by ring, abs_of_pos hεκ])
    obtain ⟨-, -, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC + ε * κ - ts - τC) = -(ε * |c| / 3) := by
      have h : σ * (ts + τC + ε * κ - ts - τC) = -(ε * (s * κ)) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    refine ⟨u₀, ?_⟩
    have h := (abs_le.mp (hKD u₀ hu₀K)).2
    rw [hval] at h
    have hun : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
    have hp : 0 < ε * |c| * ‖u₀‖ ^ 2 := mul_pos (mul_pos hε hcabs) hun
    linarith

omit [FiniteDimensional ℝ E] in
/-- A symmetric operator commuting with an orthogonal map `J` acts as a scalar on the
plane spanned by `u₀` and `J u₀` whenever `J (J u₀) = -u₀` (a complex line of a `U(1)`
symmetry).  This is how the scalar hypotheses of `perturbative_sign_change` arise from
the diagonal `U(1)` symmetry of the curved twist family. -/
theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2 := by
  have h01' : ⟪u₀, J u₀⟫ = -⟪u₀, J u₀⟫ := by
    calc ⟪u₀, J u₀⟫ = ⟪J u₀, J (J u₀)⟫ := (hJ _ _).symm
      _ = ⟪J u₀, -u₀⟫ := by rw [hJJ]
      _ = -⟪J u₀, u₀⟫ := inner_neg_right _ _
      _ = -⟪u₀, J u₀⟫ := by rw [real_inner_comm u₀ (J u₀)]
  have h01 : ⟪u₀, J u₀⟫ = 0 := by linarith
  have h10 : ⟪J u₀, u₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hJn : ⟪J u₀, J u₀⟫ = ⟪u₀, u₀⟫ := hJ u₀ u₀
  have e1 : ⟪J u₀, M u₀⟫ = ⟪u₀, M (J u₀)⟫ :=
    (hM (J u₀) u₀).symm.trans (real_inner_comm u₀ (M (J u₀)))
  have h1 : ⟪u₀, M (J u₀)⟫ = -⟪u₀, M (J u₀)⟫ := by
    calc ⟪u₀, M (J u₀)⟫ = ⟪J u₀, J (M (J u₀))⟫ := (hJ _ _).symm
      _ = ⟪J u₀, M (J (J u₀))⟫ := by rw [hMJ (J u₀)]
      _ = ⟪J u₀, M (-u₀)⟫ := by rw [hJJ]
      _ = -⟪J u₀, M u₀⟫ := by rw [map_neg, inner_neg_right]
      _ = -⟪u₀, M (J u₀)⟫ := by rw [e1]
  have hc1 : ⟪u₀, M (J u₀)⟫ = 0 := by linarith
  have hc2 : ⟪J u₀, M u₀⟫ = 0 := by rw [e1]; exact hc1
  have hd : ⟪J u₀, M (J u₀)⟫ = ⟪u₀, M u₀⟫ := by rw [hMJ u₀]; exact hJ _ _
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  refine ⟨⟪u₀, M u₀⟫ / ‖u₀‖ ^ 2, fun u hu => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hform : ⟪a • u₀ + b • J u₀, M (a • u₀ + b • J u₀)⟫ =
      (a ^ 2 + b ^ 2) * ⟪u₀, M u₀⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hc1, hc2, hd]
    ring
  have hnorm : ‖a • u₀ + b • J u₀‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hJn, h01, h10]
    ring
  rw [hform, hnorm, div_mul_eq_mul_div, eq_div_iff hn.ne']
  ring

/-- First-order expansion from joint Fréchet differentiability at `(0, ts)`. -/
theorem expansion_of_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ → F) (ts : ℝ) (Fe Ft : F)
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) ((0 : ℝ), ts)) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe‖ ≤ η * (|ε| + |τ|) := by
  intro η hη
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε τ hε hτ => ?_⟩
  have hd : dist ((ε, τ) : ℝ × ℝ) 0 < r := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    exact max_lt hε hτ
  have heq : f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe =
      (fun p : ℝ × ℝ => f p.1 p.2) (((0 : ℝ), ts) + (ε, τ)) -
      (fun p : ℝ × ℝ => f p.1 p.2) ((0 : ℝ), ts) -
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) (ε, τ) := by
    simp only [Prod.mk_add_mk, zero_add, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    abel
  have hn : ‖((ε, τ) : ℝ × ℝ)‖ ≤ |ε| + |τ| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg τ]) (by linarith [abs_nonneg ε])
  rw [heq]
  calc _ ≤ η * ‖((ε, τ) : ℝ × ℝ)‖ := hball hd
    _ ≤ η * (|ε| + |τ|) := mul_le_mul_of_nonneg_left hn hη.le

/-- First-order expansion from differentiability at `0`, for a map vanishing at `0`. -/
theorem expansion_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (Fe : F) (h0 : f 0 = 0) (h : HasDerivAt f Fe 0) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r → ‖f ε - ε • Fe‖ ≤ η * |ε| := by
  intro η hη
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε hε => ?_⟩
  have hd : dist ε 0 < r := by rw [Real.dist_eq, sub_zero]; exact hε
  have hb := hball hd
  simp only [zero_add, h0, sub_zero, Real.norm_eq_abs] at hb
  exact hb

/-! ### Pre-crossing separation from first-order data, without derivatives in the angle

The theorem `first_order_separation` below needs, at zero curvature, only that the
carrier is positive definite at angles arbitrarily close before a crossing angle `ts`
and has a negative direction at angles arbitrarily close after it.  For the curvature
it needs joint continuity at zero curvature, and a first-order expansion of the
correction whose coefficient is positive definite on the kernel of the vacuum carrier
at `ts`.  No derivative in the angle, no spectral-gap constant and no scalar action
on the kernel are assumed; the gap is produced by compactness.  The sign is the
pre-crossing one; for the families below the opposite sign is reached by reflecting
the interior profile. -/

/-- A positive definite symmetric operator is a unit. -/
theorem unit_of_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  refine unit_of_definite_complements X hs ⊥ ⊤ ?_ (fun x _ hx0 => hpos x hx0) ?_
  · intro x hx hx0
    exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
  · simp

omit [FiniteDimensional ℝ E] in
theorem psd_of_pos (X : E →L[ℝ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro x
  by_cases hx : x = 0
  · rw [hx, inner_zero_left]
  · exact (hpos x hx).le

omit [FiniteDimensional ℝ E] in
/-- Positive semidefiniteness at an angle that is a limit of positive definite angles. -/
theorem psd_of_pd_before (F : ℝ → E →L[ℝ] E) (hc : Continuous F) (ts : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, F t₀ x⟫) : PSD (F ts) := by
  intro x
  by_contra hneg
  have hx : ⟪x, F ts x⟫ < 0 := lt_of_not_ge hneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hcont : Continuous fun t => ⟪x, F t x⟫ :=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hev : ∀ᶠ t in nhds ts, ⟪x, F t x⟫ < 0 :=
    Filter.Tendsto.eventually (hcont.tendsto ts) (gt_mem_nhds hx)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨t₀, h1, h2, h3⟩ := h η hη
  have hd : dist t₀ ts < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h4 := hball hd
  have h5 := h3 x hx0
  linarith

/-- A positive semidefinite symmetric operator is bounded below by some `g > 0` on the
orthogonal complement of any subspace containing its kernel (compactness of the unit
sphere). -/
theorem exists_gap_of_psd (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (K : Submodule ℝ E) (hK : ∀ v, X v = 0 → v ∈ K) :
    ∃ g : ℝ, 0 < g ∧ ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ y ∈ Kᗮ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E) := by
    intro y hy hy0
    refine ⟨?_, Submodule.smul_mem _ _ hy⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hy0).ne']
  by_cases hne : (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)).Nonempty
  · have hS : IsCompact (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (isCompact_sphere (0 : E) 1).inter_right (Submodule.isClosed_orthogonal K)
    have hcont : ContinuousOn (fun y => ⟪y, X y⟫) (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (continuous_id.inner X.continuous).continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hcont
    have hy₀n : ‖y₀‖ = 1 := mem_sphere_zero_iff_norm.mp hy₀.1
    have hy₀K : y₀ ∈ Kᗮ := hy₀.2
    refine ⟨⟪y₀, X y₀⟫, ?_, ?_⟩
    · rcases (hp y₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have hX0 : X y₀ = 0 := psd_kernel X hs hp y₀ h.symm
        have h0 : ⟪y₀, y₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (hK y₀ hX0) hy₀K
        have hy0 : y₀ = 0 := inner_self_eq_zero.mp h0
        rw [hy0, norm_zero] at hy₀n
        exact zero_ne_one hy₀n
    · intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        simp
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have h1 : ⟪y₀, X y₀⟫ ≤ ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ :=
          isMinOn_iff.mp hmin _ (hunit y hy hy0)
        have h2 : ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ = (‖y‖ ^ 2)⁻¹ * ⟪y, X y⟫ := by
          rw [map_smul, real_inner_smul_left, real_inner_smul_right]
          ring
        rw [h2, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hyn 2)] at h1
        exact h1
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      simp
    · exact absurd ⟨_, hunit y hy hy0⟩ hne

/-- Positivity of a two-variable quadratic form. -/
theorem quad_pos {a b g U Y : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g) (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hne : U ≠ 0 ∨ Y ≠ 0) : 0 < a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2 := by
  have hQ : a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) =
      (a * U - b * Y) ^ 2 + (a * g - b ^ 2) * Y ^ 2 := by ring
  have hm : 0 < a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) := by
    rw [hQ]
    by_cases hY0 : Y = 0
    · have hU0 : U ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd hY0 h
      have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
      subst hY0
      have h1 : 0 < (a * U) ^ 2 := pow_pos (mul_pos ha hUp) 2
      have e : (a * U - b * 0) ^ 2 + (a * g - b ^ 2) * 0 ^ 2 = (a * U) ^ 2 := by ring
      rw [e]
      exact h1
    · have hYp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
      have h1 : 0 < (a * g - b ^ 2) * Y ^ 2 := mul_pos (by linarith) (pow_pos hYp 2)
      linarith [sq_nonneg (a * U - b * Y)]
  by_contra hcon
  have h2 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  rw [mul_zero] at h2
  linarith

/-- **The pre-crossing comparison.**  Let `A₀` vanish on `K` and be `≥ g` on `Kᗮ`, and let
`De ≥ c` on `K`.  If `C` is positive semidefinite (it may be singular) and `δ`-close to
`A₀`, then `C + ε De + R` is positive definite once `δ`, `ε` and `‖R‖/ε` are below
thresholds depending only on `g`, `c` and `‖De‖` (`κ` below).  The cross terms between
`K` and `Kᗮ` are absorbed by a fraction `κ ε` of the positive semidefinite form of `C`. -/
theorem pos_of_psd_add (A₀ C De R : E →L[ℝ] E) (K : Submodule ℝ E)
    (hs0 : ∀ x y, ⟪A₀ x, y⟫ = ⟪x, A₀ y⟫) (hsC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫)
    (hker : ∀ u ∈ K, A₀ u = 0) {g c δ ε μ κ : ℝ} (hg : 0 < g) (hc : 0 < c)
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A₀ y⟫)
    (hDe : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c)
    (hC : PSD C) (hδ : ‖C - A₀‖ ≤ δ) (hδg : δ ≤ g / 2) (hκδ : κ * δ ≤ 1)
    (hε : 0 < ε) (hκε : κ * ε ≤ 1) (hμ : μ ≤ c / 4) (hR : ‖R‖ ≤ μ * ε) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, (C + ε • De + R) x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hd0 : 0 ≤ ‖De‖ := norm_nonneg _
  have hU0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hμε0 : 0 ≤ μ * ε := le_trans (norm_nonneg _) hR
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  have hκpos : 0 < κ := by
    by_contra hk
    have h1 := mul_le_mul_of_nonneg_right (not_lt.mp hk) (le_of_lt (half_pos hg))
    rw [zero_mul] at h1
    linarith
  have hκε0 : 0 ≤ κ * ε := (mul_pos hκpos hε).le
  -- expansions
  have hC1 : ⟪u + y, C (u + y)⟫ = ⟪u, C u⟫ + 2 * ⟪u, C y⟫ + ⟪y, C y⟫ := by
    have hsym : ⟪y, C u⟫ = ⟪u, C y⟫ := by rw [← hsC y u, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]
    ring
  have hD1 : ⟪u + y, De (u + y)⟫ = ⟪u, De u⟫ + ⟪u, De y⟫ + ⟪y, De u⟫ + ⟪y, De y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have hQ : ⟪u + y, (C + ε • De + R) (u + y)⟫ =
      ⟪u + y, C (u + y)⟫ + ε * ⟪u + y, De (u + y)⟫ + ⟪u + y, R (u + y)⟫ := by
    simp only [add_apply, smul_apply, inner_add_right, real_inner_smul_right]
  -- the bounds
  have hCnn : 0 ≤ ⟪u + y, C (u + y)⟫ := hC _
  have hCu : 0 ≤ ⟪u, C u⟫ := hC u
  have hCuy := (abs_le.mp (cross_upper A₀ C hs0 K hker hδ u hu y)).1
  have hCy := perp_lower A₀ C K hgap hδ y hy
  have hDu := hDe u hu
  have hDuy := (abs_le.mp (abs_inner_op_le De u y)).1
  have hDyu := (abs_le.mp (abs_inner_op_le De y u)).1
  have hDy := (abs_le.mp (abs_inner_op_le De y y)).1
  have hRx : -(μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2))) ≤ ⟪u + y, R (u + y)⟫ := by
    have h1 := (abs_le.mp (abs_inner_op_le R (u + y) (u + y))).1
    have hx0 : 0 ≤ ‖u + y‖ := norm_nonneg _
    have hxn : ‖u + y‖ ≤ ‖u‖ + ‖y‖ := norm_add_le u y
    have h3a : ‖u + y‖ * ‖u + y‖ ≤ (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) :=
      mul_le_mul hxn hxn hx0 (by linarith)
    have e3 : 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) - (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) = (‖u‖ - ‖y‖) ^ 2 := by
      ring
    have h3 : ‖u + y‖ * ‖u + y‖ ≤ 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) := by
      linarith [sq_nonneg (‖u‖ - ‖y‖)]
    have h4 : ‖R‖ * ‖u + y‖ * ‖u + y‖ ≤ μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by
      calc ‖R‖ * ‖u + y‖ * ‖u + y‖ = ‖R‖ * (‖u + y‖ * ‖u + y‖) := by ring
        _ ≤ (μ * ε) * (‖u + y‖ * ‖u + y‖) :=
          mul_le_mul_of_nonneg_right hR (mul_nonneg hx0 hx0)
        _ ≤ (μ * ε) * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 hμε0
        _ = μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by ring
    linarith
  -- a fraction `κ ε` of the form of `C` absorbs the cross terms
  have hw1 : κ * ε * ⟪u + y, C (u + y)⟫ ≤ ⟪u + y, C (u + y)⟫ := by
    have h1 := mul_nonneg (sub_nonneg.mpr hκε) hCnn
    have e : (1 - κ * ε) * ⟪u + y, C (u + y)⟫ =
        ⟪u + y, C (u + y)⟫ - κ * ε * ⟪u + y, C (u + y)⟫ := by ring
    linarith
  have e5 : κ * ε * ⟪u + y, C (u + y)⟫ =
      κ * ε * ⟪u, C u⟫ + 2 * (κ * ε * ⟪u, C y⟫) + κ * ε * ⟪y, C y⟫ := by
    rw [hC1]
    ring
  have e6 : ε * ⟪u + y, De (u + y)⟫ =
      ε * ⟪u, De u⟫ + ε * ⟪u, De y⟫ + ε * ⟪y, De u⟫ + ε * ⟪y, De y⟫ := by
    rw [hD1]
    ring
  have h5a := mul_le_mul_of_nonneg_left hCuy hκε0
  have h5b := mul_le_mul_of_nonneg_left hCy hκε0
  have h5c := mul_nonneg hκε0 hCu
  have h6a := mul_le_mul_of_nonneg_left hDu hε.le
  have h6b := mul_le_mul_of_nonneg_left hDuy hε.le
  have h6c := mul_le_mul_of_nonneg_left hDyu hε.le
  have h6d := mul_le_mul_of_nonneg_left hDy hε.le
  -- the reduced two-variable form is positive
  have hbr : 0 < (c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2 := by
    have ha' : c / 2 ≤ c - 2 * μ := by linarith
    have hgd : κ * (g / 2) ≤ κ * (g - δ) := mul_le_mul_of_nonneg_left (by linarith) hκpos.le
    have hg' : c / 2 + 4 * (‖De‖ + 1) ^ 2 / c ≤ κ * (g - δ) - ‖De‖ - 2 * μ := by linarith
    have hprod : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) ≤
        (c - 2 * μ) * (κ * (g - δ) - ‖De‖ - 2 * μ) :=
      mul_le_mul ha' hg' (by linarith) (by linarith)
    have hcc : c / 2 * (4 * (‖De‖ + 1) ^ 2 / c) = 2 * (‖De‖ + 1) ^ 2 := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero two_ne_zero hc.ne')]
      ring
    have hval : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) =
        c ^ 2 / 4 + 2 * (‖De‖ + 1) ^ 2 := by
      rw [mul_add, hcc]
      ring
    have hb0 : 0 ≤ κ * δ + ‖De‖ := by
      have := mul_nonneg hκpos.le hδ0
      linarith
    have hb1 : κ * δ + ‖De‖ ≤ 1 + ‖De‖ := by linarith
    have hbsq : (κ * δ + ‖De‖) * (κ * δ + ‖De‖) ≤ (1 + ‖De‖) * (1 + ‖De‖) :=
      mul_le_mul hb1 hb1 hb0 (by linarith)
    have hd1 : 0 < (1 + ‖De‖) * (1 + ‖De‖) := by positivity
    have hc2 : 0 ≤ c ^ 2 / 4 := by positivity
    have e7 : (‖De‖ + 1) ^ 2 = (1 + ‖De‖) * (1 + ‖De‖) := by ring
    have e8 : (κ * δ + ‖De‖) ^ 2 = (κ * δ + ‖De‖) * (κ * δ + ‖De‖) := by ring
    refine quad_pos (by linarith) ?_ hU0 hY0 ?_
    · rw [e8]
      linarith [hbsq, hprod, hval, hd1, hc2, e7]
    · by_contra hcon
      apply hx
      have h1 : ‖u‖ = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h2 : ‖y‖ = 0 := by
        by_contra h
        exact hcon (Or.inr h)
      rw [norm_eq_zero.mp h1, norm_eq_zero.mp h2, add_zero]
  have hfin : ε * ((c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2) ≤ ⟪u + y, (C + ε • De + R) (u + y)⟫ := by
    rw [hQ]
    linarith
  have := mul_pos hε hbr
  linarith

omit [FiniteDimensional ℝ E] in
/-- The metric form of joint continuity at a point of zero curvature. -/
theorem metric_of_continuousAt {F : Type*} [SeminormedAddCommGroup F] (f : ℝ → ℝ → F) (t : ℝ)
    (h : ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (0, t)) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
      ‖f ε s - f 0 t‖ < δ := by
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp h δ hδ
  refine ⟨r, hr, fun ε s hε hs => ?_⟩
  have hd : dist ((ε, s) : ℝ × ℝ) (0, t) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hε hs
  have h1 := hball hd
  simp only [dist_eq_norm] at h1
  exact h1

/-- **First-order guarded separation (pre-crossing).**  `A ε t` is the carrier at curvature
`ε` and angle `t`, `D ε` the correction.  Hypotheses: symmetry; continuity in the angle at
every curvature; joint continuity at zero curvature near `ts` (metric form); at zero
curvature the carrier is positive definite at angles arbitrarily close before `ts` and has a negative
direction at angles arbitrarily close after `ts`; the correction is `ε De + o(ε)` with
`De ≥ c > 0` on the kernel of `A 0 ts`.  Then at every small positive curvature some
angle has a positive definite (hence unit) carrier and a singular corrected carrier. -/
theorem first_order_separation
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hcA : ∀ ε, Continuous (A ε)) (ts : ℝ)
    (hjoint : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖A ε s - A 0 t‖ < δ)
    (hbefore : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, A 0 t₀ x⟫)
    (hafter : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w : E, ⟪w, A 0 t₁ w⟫ < 0)
    (c : ℝ) (De : E →L[ℝ] E) (hc : 0 < c)
    (hDe : ∀ u : E, A 0 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hDexp : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖D ε - ε • De‖ ≤ μ * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t : ℝ, IsUnit (A ε t) ∧ ¬ IsUnit (A ε t - D ε) := by
  have hsC : ∀ ε t x y, ⟪(A ε t - D ε) x, y⟫ = ⟪x, (A ε t - D ε) y⟫ := by
    intro ε t x y
    simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  -- the vacuum carrier at `ts`: positive semidefinite, with a gap off its kernel
  have hpsd : PSD (A 0 ts) := psd_of_pd_before (A 0) (hcA 0) ts hbefore
  obtain ⟨K, hK_def⟩ : ∃ K : Submodule ℝ E, K = LinearMap.ker (A 0 ts : E →ₗ[ℝ] E) := ⟨_, rfl⟩
  have hmemK : ∀ v, v ∈ K ↔ A 0 ts v = 0 := by
    intro v
    rw [hK_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have hker : ∀ u ∈ K, A 0 ts u = 0 := fun u hu => (hmemK u).mp hu
  obtain ⟨g, hg, hgap⟩ := exists_gap_of_psd (A 0 ts) (hsA 0 ts) hpsd K
    (fun v hv => (hmemK v).mpr hv)
  have hDeK : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ :=
    fun u hu => hDe u (hker u hu)
  -- constants
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    rw [hκ_def]
    exact mul_pos (div_pos two_pos hg) (by linarith [norm_nonneg De])
  have hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by
    have h2g : 2 / g * (g / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 g, div_self (mul_ne_zero hg.ne' two_ne_zero)]
    rw [hκ_def]
    calc 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) * (g / 2)
        = (2 / g * (g / 2)) * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := by ring
      _ = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by rw [h2g, one_mul]
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ δ₀ : ℝ, δ₀ = min (g / 2) (1 / κ) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀_def]; exact lt_min (half_pos hg) (one_div_pos.mpr hκpos)
  have hδ₀g : δ₀ ≤ g / 2 := by rw [hδ₀_def]; exact min_le_left _ _
  have hκδ₀ : κ * δ₀ ≤ 1 := by
    have h := min_le_right (g / 2) (1 / κ)
    rw [← hδ₀_def] at h
    calc κ * δ₀ ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left h hκpos.le
      _ = 1 := mul_one_div_cancel hκpos.ne'
  -- the window, the correction size and the endpoints
  obtain ⟨η₀, hη₀, hjoint⟩ := hjoint
  obtain ⟨r₁, hr₁, hA1⟩ := hjoint ts (by simp [hη₀]) (δ₀ / 2) (half_pos hδ₀)
  obtain ⟨r₂, hr₂, hD2⟩ := hDexp (c / 4) (by linarith)
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min r₁ η₀ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact lt_min hr₁ hη₀
  have hρ1 : ρ ≤ r₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρ2 : ρ ≤ η₀ := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨t₀, ht₀a, ht₀b, hpd₀⟩ := hbefore ρ hρ
  obtain ⟨t₁, ht₁a, ht₁b, w, hw⟩ := hafter ρ hρ
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A 0 t₀) (hsA 0 t₀) (psd_of_pos _ hpd₀)
    (unit_of_pos _ (hsA 0 t₀) hpd₀)
  obtain ⟨r₃, hr₃, hA3⟩ := hjoint t₀ (by rw [abs_lt]; constructor <;> linarith) (m / 2)
    (half_pos hm)
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = -⟪w, A 0 t₁ w⟫ := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; linarith
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = ‖w‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hW_def]; positivity
  have hwW : ‖w‖ * ‖w‖ ≤ W := by
    rw [hW_def]
    have e : ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
    rw [e]
    linarith
  obtain ⟨r₄, hr₄, hA4⟩ := hjoint t₁ (by rw [abs_lt]; constructor <;> linarith) (ν / (2 * W))
    (div_pos hν (by linarith))
  obtain ⟨Dc, hDc_def⟩ : ∃ Dc : ℝ, Dc = ‖De‖ + c / 4 + 1 := ⟨_, rfl⟩
  have hDc : 0 < Dc := by rw [hDc_def]; linarith [norm_nonneg De]
  have hDsmall : ∀ ε : ℝ, 0 < ε → ε < r₂ → ‖D ε‖ ≤ Dc * ε := by
    intro ε hε hεr
    have h1 := hD2 ε hε hεr
    have h2 : ‖D ε‖ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := by
      calc ‖D ε‖ = ‖(D ε - ε • De) + ε • De‖ := by rw [sub_add_cancel]
        _ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
    rw [hDc_def]
    linarith
  have h2Dc : 0 < 2 * Dc := by linarith
  have h2WDc : 0 < 2 * W * Dc := mul_pos (mul_pos two_pos hW) hDc
  refine ⟨min (min (min r₁ r₂) (min r₃ r₄))
      (min (min (1 / κ) (δ₀ / (2 * Dc))) (min (m / (2 * Dc)) (ν / (2 * W * Dc)))), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄))
      (lt_min (lt_min (one_div_pos.mpr hκpos) (div_pos hδ₀ h2Dc))
        (lt_min (div_pos hm h2Dc) (div_pos hν h2WDc)))
  intro ε hε hε₀
  have e1 : ε < r₁ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e2 : ε < r₂ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e3 : ε < r₃ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e4 : ε < r₄ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have e5 : ε < 1 / κ := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e6 : ε < δ₀ / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e7 : ε < m / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e8 : ε < ν / (2 * W * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεabs : |ε| = ε := abs_of_pos hε
  have hDε := hDsmall ε hε e2
  have hDε1 : ‖D ε‖ < δ₀ / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e6
    linarith
  have hDε2 : ‖D ε‖ < m / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e7
    linarith
  have hDε3 : ‖D ε‖ * (2 * W) < ν := by
    have h := (lt_div_iff₀ h2WDc).mp e8
    have h' := mul_le_mul_of_nonneg_right hDε (by linarith : (0 : ℝ) ≤ 2 * W)
    linarith
  have hκε : κ * ε ≤ 1 := by
    have h := (lt_div_iff₀ hκpos).mp e5
    linarith
  -- the corrected carrier is positive definite at `t₀`
  have hC0 : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε t₀ - D ε) x⟫ := by
    intro x hx
    have h1 := hmc x
    have h2 : ‖A ε t₀ - A 0 t₀‖ < m / 2 := hA3 ε t₀ (by rw [hεabs]; exact e3) (by simp [hr₃])
    have hxx : 0 < ‖x‖ * ‖x‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hx)
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₀ - A 0 t₀) x x)).1
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) x x)).2
    have e : ⟪x, (A ε t₀ - D ε) x⟫ = ⟪x, A 0 t₀ x⟫ + ⟪x, (A ε t₀ - A 0 t₀) x⟫ - ⟪x, D ε x⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    have h5 := mul_lt_mul_of_pos_right h2 hxx
    have h6 := mul_lt_mul_of_pos_right hDε2 hxx
    have e' : ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    rw [e]
    rw [e'] at h1
    linarith
  -- and has a negative direction at `t₁`
  have hC1 : ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
    have h2 : ‖A ε t₁ - A 0 t₁‖ < ν / (2 * W) := hA4 ε t₁ (by rw [hεabs]; exact e4) (by simp [hr₄])
    have h2' : ‖A ε t₁ - A 0 t₁‖ * (2 * W) < ν := (lt_div_iff₀ (by linarith)).mp h2
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₁ - A 0 t₁) w w)).2
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) w w)).1
    have h5 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (A ε t₁ - A 0 t₁))
    have h6 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (D ε))
    have e : ⟪w, (A ε t₁ - D ε) w⟫ = ⟪w, A 0 t₁ w⟫ + ⟪w, (A ε t₁ - A 0 t₁) w⟫ - ⟪w, D ε w⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    rw [e]
    linarith
  -- the first singular corrected carrier on the window
  have hF : Continuous fun s : ℝ => A ε (t₀ + s) - D ε :=
    ((hcA ε).comp (continuous_const.add continuous_id)).sub continuous_const
  have hT : t₀ + (t₁ - t₀) = t₁ := by ring
  obtain ⟨s, hs0, hsT, hpsdF, hnuF, -, -⟩ := first_carrier_crossing
    (fun s : ℝ => A ε (t₀ + s) - D ε) hF (fun s x y => hsC ε (t₀ + s) x y)
    (by simpa only [add_zero] using psd_of_pos _ hC0)
    (by simpa only [add_zero] using unit_of_pos _ (hsC ε t₀) hC0)
    (t₁ - t₀) (by linarith) w (by simpa only [hT] using hC1)
  have hwin : ‖A ε (t₀ + s) - A 0 ts‖ < δ₀ / 2 := hA1 ε (t₀ + s) (by rw [hεabs]; exact e1)
    (by rw [abs_lt]; constructor <;> linarith)
  have hCδ : ‖(A ε (t₀ + s) - D ε) - A 0 ts‖ ≤ δ₀ := by
    have e : (A ε (t₀ + s) - D ε) - A 0 ts = (A ε (t₀ + s) - A 0 ts) - D ε := by abel
    rw [e]
    calc ‖(A ε (t₀ + s) - A 0 ts) - D ε‖ ≤ ‖A ε (t₀ + s) - A 0 ts‖ + ‖D ε‖ := norm_sub_le _ _
      _ ≤ δ₀ := by linarith
  have hpd := pos_of_psd_add (A 0 ts) (A ε (t₀ + s) - D ε) De (D ε - ε • De)
    K (hsA 0 ts) (hsC ε (t₀ + s)) hker hg hc hgap hDeK hκ hpsdF hCδ
    hδ₀g hκδ₀ hε hκε le_rfl (hD2 ε hε e2)
  have hAeq : (A ε (t₀ + s) - D ε) + ε • De + (D ε - ε • De) = A ε (t₀ + s) := by abel
  refine ⟨t₀ + s, unit_of_pos _ (hsA ε (t₀ + s)) (fun x hx => ?_), hnuF⟩
  have h := hpd x hx
  rwa [hAeq] at h

end Abstract
end AdalyFormal.Round9.Guarded.Qualitative

import D1IVT

/-! An exact common-profile criterion. This abstract result does not assert that
any physical crossing response satisfies its convex noncancellation condition. -/
noncomputable section
open scoped RealInnerProductSpace Topology
open Set
namespace AdalyFormal.Round10.Assembly.R4

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Unit-kernel response hull. Closed convex hull is intentional: a uniform
positive margin, not merely pointwise separation, is required. -/
def responseHull (K : Submodule ℝ E) (Q : E → F) : Set F :=
  closedConvexHull ℝ (Q '' {u | u ∈ K ∧ ‖u‖ = 1})

theorem separator_of_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (h : (0 : F) ∉ responseHull K Q) :
    ∃ (f : F →L[ℝ] ℝ) (c : ℝ), 0 < c ∧
      ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u) := by
  obtain ⟨f, c, hc, hf⟩ := geometric_hahn_banach_point_closed
    (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull h
  refine ⟨f, c, by simpa using hc, ?_⟩
  intro u hu hn
  exact le_of_lt (hf _ (subset_closedConvexHull (𝕜 := ℝ) ⟨u, ⟨hu, hn⟩, rfl⟩))

theorem notMem_responseHull_of_separator (K : Submodule ℝ E) (Q : E → F)
    (f : F →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u)) :
    (0 : F) ∉ responseHull K Q := by
  have hsub : responseHull K Q ⊆ {x : F | c ≤ f x} := by
    apply closedConvexHull_min
    · rintro _ ⟨u, ⟨hu, hn⟩, rfl⟩
      exact hf u hu hn
    · exact (convex_Ici c).linear_preimage f.toLinearMap
    · exact isClosed_le continuous_const f.continuous
  intro h
  have := hsub h
  simp only [mem_setOf_eq, map_zero] at this
  linarith

theorem norm_square_lower_of_unit_lower (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u)
    (f : F →L[ℝ] ℝ) (c : ℝ)
    (hf : ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u)) :
    ∀ u, u ∈ K → c * ‖u‖ ^ 2 ≤ f (Q u) := by
  intro u hu
  by_cases hz : u = 0
  · subst u
    have hzero : Q 0 = 0 := by simpa using hQ 0 0
    simp [hzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hz
  let v : E := ‖u‖⁻¹ • u
  have hvK : v ∈ K := K.smul_mem _ hu
  have hvn : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h := mul_le_mul_of_nonneg_right (hf v hvK hvn) (sq_nonneg ‖u‖)
  calc
    c * ‖u‖ ^ 2 ≤ f (Q v) * ‖u‖ ^ 2 := h
    _ = f (Q (‖u‖ • v)) := by simp only [hQ, map_smul, smul_eq_mul]; ring
    _ = f (Q u) := by rw [huv]

theorem common_coercive_iff_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u) :
    (∃ (f : F →L[ℝ] ℝ) (c : ℝ), 0 < c ∧
      ∀ u, u ∈ K → c * ‖u‖ ^ 2 ≤ f (Q u)) ↔
    (0 : F) ∉ responseHull K Q := by
  constructor
  · rintro ⟨f, c, hc, hf⟩
    apply notMem_responseHull_of_separator K Q f c hc
    intro u hu hn
    simpa only [hn, one_pow, mul_one] using hf u hu
  · intro h
    obtain ⟨f, c, hc, hf⟩ := separator_of_notMem_responseHull K Q h
    exact ⟨f, c, hc, norm_square_lower_of_unit_lower K Q hQ f c hf⟩

/-- Every common coercive profile excludes every convex cancellation, not just
individual zero responses. This is the missing quantifier strength. -/
theorem response_ne_zero_of_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u)
    (h : (0 : F) ∉ responseHull K Q) (u : E) (hu : u ∈ K) (hne : u ≠ 0) : Q u ≠ 0 := by
  obtain ⟨f, c, hc, hf⟩ := (common_coercive_iff_notMem_responseHull K Q hQ).mpr h
  intro hz
  have hg := hf u hu
  rw [hz, map_zero] at hg
  exact (not_le_of_gt (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hne)))) hg

#print axioms responseHull
#print axioms separator_of_notMem_responseHull
#print axioms notMem_responseHull_of_separator
#print axioms norm_square_lower_of_unit_lower
#print axioms common_coercive_iff_notMem_responseHull
#print axioms response_ne_zero_of_notMem_responseHull
end AdalyFormal.Round10.Assembly.R4

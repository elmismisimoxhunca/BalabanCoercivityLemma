import Mathlib

/-!
# W2A -- abstract projection facts for the W2 bridge (M1 lane W2, 2026-10-13)

For subspaces `V ≤ W` of a finite-dimensional real inner product space:
* `proj_proj_of_le` : `P_V (P_W f) = P_V f`;
* `proj_split` : `‖P_W f‖² = ‖P_V f‖² + ‖P_W f − P_V f‖²` (Pythagoras for nested projections);
* `proj_sq_mono` : `‖P_V f‖² ≤ ‖P_W f‖²`;
* `proj_defect_anti` : `V ≤ V' ≤ W` ⇒ `‖P_W f − P_{V'} f‖² ≤ ‖P_W f − P_V f‖²`;
* **`proj_cmp`** : if `V ≤ W₁` and `V ≤ W₂` then `‖P_{W₂} f‖² − ‖P_{W₂} f − P_V f‖² ≤ ‖P_{W₁} f‖²`.
No sorry / axiom.
-/
set_option autoImplicit false

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem proj_proj_of_le (V W : Submodule ℝ E) (h : V ≤ W) (f : E) :
    V.starProjection (W.starProjection f) = V.starProjection f := by
  have h1 : f - W.starProjection f ∈ Vᗮ := Submodule.orthogonal_le h (Submodule.sub_starProjection_mem_orthogonal f)
  have h2 : V.starProjection (f - W.starProjection f) = 0 := (Submodule.starProjection_apply_eq_zero_iff V).mpr h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2.symm

theorem proj_split (V W : Submodule ℝ E) (h : V ≤ W) (f : E) :
    ‖W.starProjection f‖ ^ 2 = ‖V.starProjection f‖ ^ 2 + ‖W.starProjection f - V.starProjection f‖ ^ 2 := by
  set g := W.starProjection f with hg
  have hPV : V.starProjection g = V.starProjection f := proj_proj_of_le V W h f
  have horth : g - V.starProjection g ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal g
  have hmem : V.starProjection g ∈ V := Submodule.starProjection_apply_mem V g
  have h0 : ⟪V.starProjection g, g - V.starProjection g⟫ = 0 :=
    (Submodule.mem_orthogonal V _).mp horth _ hmem
  have hsplit : g = V.starProjection g + (g - V.starProjection g) := by abel
  have hn : ‖g‖ ^ 2 = ‖V.starProjection g‖ ^ 2 + ‖g - V.starProjection g‖ ^ 2 := by
    conv_lhs => rw [hsplit]
    rw [@norm_add_sq_real, h0]; ring
  rw [hn, hPV]

theorem proj_sq_mono (V W : Submodule ℝ E) (h : V ≤ W) (f : E) :
    ‖V.starProjection f‖ ^ 2 ≤ ‖W.starProjection f‖ ^ 2 := by
  rw [proj_split V W h f]
  have := sq_nonneg ‖W.starProjection f - V.starProjection f‖
  linarith

theorem proj_defect_anti (V V' W : Submodule ℝ E) (hV : V ≤ V') (hV' : V' ≤ W) (f : E) :
    ‖W.starProjection f - V'.starProjection f‖ ^ 2 ≤ ‖W.starProjection f - V.starProjection f‖ ^ 2 := by
  have h1 := proj_split V W (le_trans hV hV') f
  have h2 := proj_split V' W hV' f
  have h3 := proj_sq_mono V V' hV f
  linarith

/-- **the one-sided comparison of two projections through a common subspace**. -/
theorem proj_cmp (V W₁ W₂ : Submodule ℝ E) (h₁ : V ≤ W₁) (h₂ : V ≤ W₂) (f : E) :
    ‖W₂.starProjection f‖ ^ 2 - ‖W₂.starProjection f - V.starProjection f‖ ^ 2 ≤ ‖W₁.starProjection f‖ ^ 2 := by
  have hs := proj_split V W₂ h₂ f
  have hm := proj_sq_mono V W₁ h₁ f
  linarith

end

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.proj_proj_of_le
#print axioms AdalyFormal.M1W2.proj_split
#print axioms AdalyFormal.M1W2.proj_sq_mono
#print axioms AdalyFormal.M1W2.proj_defect_anti
#print axioms AdalyFormal.M1W2.proj_cmp

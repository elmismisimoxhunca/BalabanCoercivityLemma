import CvK7

/-!
# CvK8 -- transversality of the crossing (lane cover_jacobi_20261016)

At the first crossing `cs` with kernel vector `es` (`es in V`, `es != 0`, `qF C cs es = 0`) the layer form is strictly positive, `bF C es > 0`, and
`qF C c es = (c - cs) * bF C es` for every `c`: the null direction crosses zero with nonzero slope `bF C es` as the layer weight passes `cs`
(so `qF C c es < 0` for `c < cs` and `> 0` for `c > cs`).  This is the simple sign change needed for `d(t)` in `LayerPoleAt`
(modulo the identification of the genuine determinant with the chain's).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open Finset

variable {n : ℕ}

theorem crossing_transversal {rowOf : ℕ → ℕ} (C : ℕ) (cs : ℝ) {es : Fin n → ℝ} (hes : es ∈ Vsub rowOf) (hne : es ≠ 0)
    (h0 : qF C cs es = 0) :
    0 < bF C es ∧ ∀ c : ℝ, qF C c es = (c - cs) * bF C es := by
  have hlin : ∀ c : ℝ, qF C c es = (c - cs) * bF C es := by
    intro c
    unfold qF at h0 ⊢
    linarith [h0]
  refine ⟨?_, hlin⟩
  by_contra hle
  have hb0 : bF C es = 0 := le_antisymm (not_lt.mp hle) (bF_nonneg C es)
  have h1 := hlin 1
  rw [hb0] at h1
  have : qF C 1 es = aF es := by unfold qF; ring
  have hpos := aF_pos rowOf hes hne
  rw [this] at h1
  linarith

#print axioms crossing_transversal

end AdalyFormal.CoverJacobi

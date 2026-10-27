import Mathlib

/-!
# LF2 -- the abstract scalar argument (Mathlib only)

Spaces `S` (sites), `B` (bonds), `D : S → B`, a "mass" functional `mass : B → ℝ`, the coarse subspace `K ⊂ S`
(block-constant functions), a cell-edge energy `ε : S → ℝ`, an extension `E : S → S`.  If
* `E w - w ⟂ K` for `w ∈ K`                      (exact block averages),
* `‖D E w‖² ≤ C1 n ε(w)` for `w ∈ K`               (extension energy),
* `ε(w) ≤ C2 (n/a) mass(D w)` for `w ∈ K`          (cell edges controlled by the mass),
* `ε(w) ≤ (12/n³) ‖w‖²` for `w ∈ K`                (trivial bound),
then for every `φ` with `G = D*Dφ ∈ K`, and `ψ ∈ K` with the same `K`-pairings as `φ` and the same mass,
`‖D*Dφ‖² ≤ 12 C1² C2 / a · mass(Dφ)`  (`n` cancels).
Proof: `‖Dφ‖² = ⟨G,φ⟩ = ⟨G,ψ⟩ = ⟨Dφ, DEψ⟩` gives `‖Dφ‖ ≤ ‖DEψ‖`; `‖G‖² = ⟨G,EG⟩ = ⟨Dφ,DEG⟩`.
No sorry / axiom.
-/
set_option autoImplicit false
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace

section
variable {S B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [CompleteSpace S] [CompleteSpace B]

theorem scalar_core (D : S →L[ℝ] B) (mass : B → ℝ) (K : Submodule ℝ S) (ε : S → ℝ) (E : S → S)
    (C1 C2 n a : ℝ) (hn : 0 < n) (ha : 0 < a) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hE_avg : ∀ w ∈ K, ∀ v ∈ K, ⟪v, E w⟫ = ⟪v, w⟫)
    (hE_grad : ∀ w ∈ K, ‖D (E w)‖ ^ 2 ≤ C1 * n * ε w)
    (hM1 : ∀ w ∈ K, ε w ≤ C2 * (n / a) * mass (D w))
    (hεG : ∀ w ∈ K, ε w ≤ 12 / n ^ 3 * ‖w‖ ^ 2)
    (φ ψ : S) (hψ : ψ ∈ K) (hφψ : ∀ v ∈ K, ⟪v, φ⟫ = ⟪v, ψ⟫) (hmass : mass (D ψ) = mass (D φ))
    (hm0 : 0 ≤ mass (D φ))
    (hG : ContinuousLinearMap.adjoint D (D φ) ∈ K) :
    ‖ContinuousLinearMap.adjoint D (D φ)‖ ^ 2 ≤ 12 * C1 ^ 2 * C2 / a * mass (D φ) := by
  set G := ContinuousLinearMap.adjoint D (D φ) with hGdef
  have hpair : ∀ w ∈ K, ⟪G, w⟫ = ⟪D φ, D (E w)⟫ := by
    intro w hw
    rw [← hE_avg w hw G hG, hGdef, ContinuousLinearMap.adjoint_inner_left]
  -- step 1: ‖Dφ‖ ≤ ‖D E ψ‖
  have hDφ : ‖D φ‖ ^ 2 = ⟪G, ψ⟫ := by
    rw [← hφψ G hG, hGdef, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have h1 : ‖D φ‖ ^ 2 ≤ ‖D φ‖ * ‖D (E ψ)‖ := by
    rw [hDφ, hpair ψ hψ]; exact real_inner_le_norm _ _
  have h1' : ‖D φ‖ ≤ ‖D (E ψ)‖ := by
    rcases (norm_nonneg (D φ)).eq_or_lt with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · have : ‖D φ‖ * ‖D φ‖ ≤ ‖D (E ψ)‖ * ‖D φ‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  set m := mass (D φ) with hm
  have hA : ‖D φ‖ ^ 2 ≤ C1 * C2 * n ^ 2 / a * m := by
    have e1 := hE_grad ψ hψ
    have e2 := hM1 ψ hψ
    rw [hmass] at e2
    have e3 : ‖D φ‖ ^ 2 ≤ ‖D (E ψ)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1' 2
    have e4 : C1 * n * ε ψ ≤ C1 * n * (C2 * (n / a) * m) := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e5 : C1 * n * (C2 * (n / a) * m) = C1 * C2 * n ^ 2 / a * m := by field_simp
    linarith
  -- step 2: ‖G‖² ≤ ‖Dφ‖ ‖D E G‖,  ‖D E G‖² ≤ 12 C1 / n² ‖G‖²
  have h2 : ‖G‖ ^ 2 ≤ ‖D φ‖ * ‖D (E G)‖ := by
    rw [← real_inner_self_eq_norm_sq, hpair G hG]; exact real_inner_le_norm _ _
  have hB : ‖D (E G)‖ ^ 2 ≤ 12 * C1 / n ^ 2 * ‖G‖ ^ 2 := by
    have e1 := hE_grad G hG
    have e2 := hεG G hG
    have e3 : C1 * n * ε G ≤ C1 * n * (12 / n ^ 3 * ‖G‖ ^ 2) := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e4 : C1 * n * (12 / n ^ 3 * ‖G‖ ^ 2) = 12 * C1 / n ^ 2 * ‖G‖ ^ 2 := by field_simp
    linarith
  -- combine: ‖G‖⁴ ≤ ‖Dφ‖² ‖DEG‖²
  have h4 : (‖G‖ ^ 2) ^ 2 ≤ (C1 * C2 * n ^ 2 / a * m) * (12 * C1 / n ^ 2 * ‖G‖ ^ 2) := by
    have e1 : (‖G‖ ^ 2) ^ 2 ≤ (‖D φ‖ * ‖D (E G)‖) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    have e2 : (‖D φ‖ * ‖D (E G)‖) ^ 2 = ‖D φ‖ ^ 2 * ‖D (E G)‖ ^ 2 := by ring
    have e3 : ‖D φ‖ ^ 2 * ‖D (E G)‖ ^ 2 ≤ (C1 * C2 * n ^ 2 / a * m) * (12 * C1 / n ^ 2 * ‖G‖ ^ 2) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    linarith
  have hprod : (C1 * C2 * n ^ 2 / a * m) * (12 * C1 / n ^ 2 * ‖G‖ ^ 2)
      = (12 * C1 ^ 2 * C2 / a * m) * ‖G‖ ^ 2 := by field_simp
  rw [hprod] at h4
  rcases (sq_nonneg ‖G‖).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : ‖G‖ ^ 2 * ‖G‖ ^ 2 ≤ (12 * C1 ^ 2 * C2 / a * m) * ‖G‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end

#print axioms scalar_core

end AdalyFormal.LemIFlat

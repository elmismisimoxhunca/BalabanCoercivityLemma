import RationalAnchor

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.G0Final

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace E] [CompleteSpace F]

/-- Completion of the flat energy along a finite-rank perturbation. The lift K
is A⁻¹ V (V* A⁻¹ V)⁻¹ when that Gram matrix is nonsingular. No positivity of J
is assumed, and no non-Hermitian I+JG is tested for positivity. -/
theorem compressed_schur_energy
    (A : E →L[ℝ] E) (V K : F →L[ℝ] E) (C J : F →L[ℝ] F)
    (hA : ∀ x y, (inner ℝ (A x) y : ℝ) = inner ℝ x (A y))
    (hVK : ∀ z, V.adjoint (K z) = z)
    (hAK : ∀ z, A (K z) = V (C z)) (x : E) :
    (inner ℝ x ((A + V.comp (J.comp V.adjoint)) x) : ℝ) =
      inner ℝ (x - K (V.adjoint x)) (A (x - K (V.adjoint x))) +
        inner ℝ (V.adjoint x) ((C + J) (V.adjoint x)) := by
  have hk : (inner ℝ (K (V.adjoint x)) (A (K (V.adjoint x))) : ℝ) =
      inner ℝ (V.adjoint x) (C (V.adjoint x)) := by
    rw [hAK, ← ContinuousLinearMap.adjoint_inner_left, hVK]
  have hx : (inner ℝ x (A (K (V.adjoint x))) : ℝ) =
      inner ℝ (V.adjoint x) (C (V.adjoint x)) := by
    rw [hAK, ← ContinuousLinearMap.adjoint_inner_left]
  have hy : (inner ℝ (K (V.adjoint x)) (A x) : ℝ) =
      inner ℝ (V.adjoint x) (C (V.adjoint x)) := by
    rw [← hA, real_inner_comm]
    exact hx
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    map_sub, inner_add_right, inner_sub_left, inner_sub_right]
  rw [hk, hx, hy, ← ContinuousLinearMap.adjoint_inner_left V (J (V.adjoint x)) x]
  ring

/-- Positive flat precision plus positive compressed Schur form is positive on
the ORIGINAL carrier, including the orthogonal complement of the update. -/
theorem strict_of_compressed_schur
    (A : E →L[ℝ] E) (V K : F →L[ℝ] E) (C J : F →L[ℝ] F)
    (hA : ∀ x y, (inner ℝ (A x) y : ℝ) = inner ℝ x (A y))
    (hVK : ∀ z, V.adjoint (K z) = z)
    (hAK : ∀ z, A (K z) = V (C z))
    (hpos : ∀ x : E, x ≠ 0 → (0 : ℝ) < inner ℝ x (A x))
    (hschur : ∀ z : F, z ≠ 0 → (0 : ℝ) < inner ℝ z ((C + J) z)) :
    ∀ x : E, x ≠ 0 →
      (0 : ℝ) < inner ℝ x ((A + V.comp (J.comp V.adjoint)) x) := by
  intro x hx
  rw [compressed_schur_energy A V K C J hA hVK hAK]
  have ha0 (y : E) : (0 : ℝ) ≤ inner ℝ y (A y) := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (hpos y hy).le
  by_cases hz : V.adjoint x = 0
  · simpa only [hz, map_zero, sub_zero, inner_zero_left, add_zero] using hpos x hx
  · exact add_pos_of_nonneg_of_pos (ha0 _) (hschur _ hz)

/-- Build the Schur lift from two checked left inverses. Right-inverse identities
are not silently supplied by Ring.inverse. -/
theorem schur_lift_identities
    (A G : E →L[ℝ] E) (V : F →L[ℝ] E) (C : F →L[ℝ] F)
    (hAG : ∀ x, A (G x) = x)
    (hGC : ∀ z, V.adjoint (G (V (C z))) = z) :
    (∀ z, V.adjoint ((G.comp (V.comp C)) z) = z) ∧
      (∀ z, A ((G.comp (V.comp C)) z) = V (C z)) := by
  constructor
  · exact hGC
  · intro z
    exact hAG _

/-- Source-specific assembly endpoint, with the source identity and compressed
certificate as EXPLICIT obligations. This does not assert they are discharged. -/
theorem chosen_G0_of_compressed_schur
    (A : HConstruction.Covariance.H →L[ℝ] HConstruction.Covariance.H)
    (V K : F →L[ℝ] HConstruction.Covariance.H) (C J : F →L[ℝ] F)
    (hsource : HConstruction.SmallNF.chosenPrecision = A + V.comp (J.comp V.adjoint))
    (hA : ∀ x y, (inner ℝ (A x) y : ℝ) = inner ℝ x (A y))
    (hVK : ∀ z, V.adjoint (K z) = z)
    (hAK : ∀ z, A (K z) = V (C z))
    (hpos : ∀ x, x ≠ 0 → (0 : ℝ) < inner ℝ x (A x))
    (hschur : ∀ z, z ≠ 0 → (0 : ℝ) < inner ℝ z ((C + J) z)) :
    HConstruction.SmallNF.HasPhysicalG0 HConstruction.SmallNF.chosenU 1 := by
  have hp := strict_of_compressed_schur A V K C J hA hVK hAK hpos hschur
  rw [← hsource] at hp
  apply HConstruction.SNFRepair.twoSidedInverse_iff_injective _ |>.mpr
  intro x y hxy
  change HConstruction.SmallNF.chosenPrecision x = HConstruction.SmallNF.chosenPrecision y at hxy
  have hz : HConstruction.SmallNF.chosenPrecision (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  by_contra hn
  have hp' := hp (x - y) (fun h => hn (sub_eq_zero.mp h))
  rw [hz, inner_zero_right] at hp'
  exact lt_irrefl _ hp'

#print axioms compressed_schur_energy
#print axioms strict_of_compressed_schur
#print axioms schur_lift_identities
#print axioms chosen_G0_of_compressed_schur
end HConstruction.G0Final

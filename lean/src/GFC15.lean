import GFC14

/-!
# GFC15 -- **TORUS COERCIVITY, VOLUME-INDEPENDENT** (complex scalar model).  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

theorem nsmul_eU_zero (μ : Fin 3) : (L μ + 1) • eU L μ = 0 := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp only [eU, Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply]
    apply Fin.ext
    rw [fin_val_nsmul, Fin.val_one']
    simp [Nat.mul_mod_right]
  · simp [eU, Pi.single_eq_of_ne h]

theorem twist_pow_one (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (hA0 : A ≠ 0) (μ : Fin 3) : ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ = 1 := by
  obtain ⟨⟨x, ν⟩, hxν⟩ : ∃ p : Site L × Fin 3, A p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hA0
    ext p
    simpa using h p
  have h1 : n • (Mc L n μ • eU L μ) = 0 := by
    rw [smul_smul, Mc_mul hdvd μ, nsmul_eU_zero]
  have h2 := hA (Mc L n μ • eU L μ) x ν
  rw [h1, add_zero] at h2
  have h3 : χ (Mc L n μ • eU L μ) = ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ := by
    rw [AddChar.map_nsmul_eq_pow]; rfl
  rw [h3] at h2
  have : (((zOf χ μ : Circle) : ℂ) ^ Mc L n μ - 1) * A (x, ν) = 0 := by
    rw [sub_mul, one_mul]; exact sub_eq_zero.mpr h2.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hxν)

/-- **eigen-field coercivity**, with the constant of the cell theorem -/
theorem eigen_coercive (hn : 0 < n) {c : ℝ}
    (hc : ∀ (z : Fin 3 → Circle) (w : Fin 3 → CV n) (S : ℝ), 0 ≤ S →
      (∀ u : CV n, ⟪epsV n, u⟫ = 0 →
        ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) →
      c * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + g2 hn (z, w) + S)
    (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L) (hA : IsEig n χ A) :
    c * ‖A‖ ^ 2 ≤ ‖L1 L A‖ ^ 2 + ‖L2 hdvd A‖ ^ 2 + ‖L3 hdvd A‖ ^ 2 := by
  by_cases hA0 : A = 0
  · subst hA0; simp
  have hzM := twist_pow_one hn hdvd χ A hA hA0
  have hM := Mnum_pos hn hdvd
  have hnormA : ‖A‖ ^ 2 = Mnum L n * ∑ μ, ‖vOf hdvd A μ‖ ^ 2 := by
    rw [normB_eig hn hdvd χ A hA]
    congr 1
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hS : 0 ≤ ‖L3 hdvd A‖ ^ 2 / Mnum L n := by positivity
  have key := hc (zOf χ) (fun μ => vOf hdvd A μ) (‖L3 hdvd A‖ ^ 2 / Mnum L n) hS
    (fun u hu => L3_ratio hn hdvd χ A hA hzM u hu)
  have h1 := L1_cell hn hdvd χ A hA
  have h2 := L2_cell hn hdvd χ A hA
  rw [h1, h2, hnormA]
  have := mul_le_mul_of_nonneg_left key hM.le
  calc c * (Mnum L n * ∑ μ, ‖vOf hdvd A μ‖ ^ 2) = Mnum L n * (c * ∑ μ, ‖vOf hdvd A μ‖ ^ 2) := by ring
    _ ≤ Mnum L n * (g1 hn (zOf χ, fun μ => vOf hdvd A μ) + g2 hn (zOf χ, fun μ => vOf hdvd A μ)
          + ‖L3 hdvd A‖ ^ 2 / Mnum L n) := this
    _ = _ := by field_simp

#print axioms eigen_coercive

end AdalyFormal.FlatCoercivity

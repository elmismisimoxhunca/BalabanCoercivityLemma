import SC4b

/-!
# SC4c -- normalised plane waves, the orthonormal basis, eigenvalues of the lattice Laplacian, spectral gap.
Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

section Basis
variable {n : ℕ}

noncomputable def cn (n : ℕ) : ℝ := (Real.sqrt ((n : ℝ) ^ 3))⁻¹

theorem cn_sq (hn : 0 < n) : cn n ^ 2 * (n : ℝ) ^ 3 = 1 := by
  have hp : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  unfold cn
  rw [inv_pow, Real.sq_sqrt hp.le]
  field_simp

noncomputable def pk (n : ℕ) (z : Fin 3 → Circle) (k : Cell n) : CV n :=
  ((cn n : ℝ) : ℂ) • pwv n z k

theorem inner_pk (hn : 0 < n) (z : Fin 3 → Circle) (k k' : Cell n) :
    ⟪pk n z k, pk n z k'⟫ = if k = k' then 1 else 0 := by
  unfold pk
  rw [inner_smul_left, inner_smul_right, inner_pwv hn, Complex.conj_ofReal]
  have h : ((cn n : ℝ) : ℂ) * (((cn n : ℝ) : ℂ) * (n : ℂ) ^ 3) = 1 := by
    have := cn_sq hn
    have h2 : ((cn n ^ 2 * (n : ℝ) ^ 3 : ℝ) : ℂ) = 1 := by rw [this]; simp
    push_cast at h2
    linear_combination h2
  split_ifs
  · exact h
  · simp

theorem orth_pk (hn : 0 < n) (z : Fin 3 → Circle) : Orthonormal ℂ (pk n z) :=
  orthonormal_iff_ite.mpr (inner_pk hn z)

noncomputable def onb (hn : 0 < n) (z : Fin 3 → Circle) : OrthonormalBasis (Cell n) ℂ (CV n) :=
  haveI : Nonempty (Cell n) := ⟨fun _ => ⟨0, hn⟩⟩
  (basisOfOrthonormalOfCardEqFinrank (orth_pk hn z)
    (by rw [finrank_euclideanSpace])).toOrthonormalBasis
    (by simpa using orth_pk hn z)

theorem onb_apply (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) : onb hn z k = pk n z k := by
  unfold onb
  simp

/-- the Laplace eigenvalue of the plane wave `k` -/
noncomputable def lam (n : ℕ) (z : Fin 3 → Circle) (k : Cell n) : ℝ := ∑ μ, ‖sg n z k μ - 1‖ ^ 2

theorem lam_nonneg (z : Fin 3 → Circle) (k : Cell n) : 0 ≤ lam n z k :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem D_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) :
    (cellSym hn z).D μ (pwv n z k) = (sg n z k μ - 1) • pwv n z k := by
  show Su hn z μ (pwv n z k) - pwv n z k = _
  rw [Su_pwv hn, sub_smul, one_smul]

theorem Ds_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) (μ : Fin 3) :
    (cellSym hn z).Ds μ (pwv n z k) = ((sg n z k μ)⁻¹ - 1) • pwv n z k := by
  show (Su hn z μ).symm (pwv n z k) - pwv n z k = _
  have : (Su hn z μ).symm (pwv n z k) = (sg n z k μ)⁻¹ • pwv n z k := by
    apply (Su hn z μ).injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, Su_pwv hn, smul_smul, inv_mul_cancel₀ (sg_ne z k μ),
      one_smul]
  rw [this, sub_smul, one_smul]

theorem Lap_pwv (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) :
    (cellSym hn z).Lap (pwv n z k) = ((lam n z k : ℝ) : ℂ) • pwv n z k := by
  unfold SymData.Lap lam
  have : ∀ μ, (cellSym hn z).Ds μ ((cellSym hn z).D μ (pwv n z k))
      = (((‖sg n z k μ - 1‖ ^ 2 : ℝ)) : ℂ) • pwv n z k := by
    intro μ
    rw [D_pwv hn, SymData.Ds_smul, Ds_pwv hn, smul_smul]
    congr 1
    have h1 : (sg n z k μ)⁻¹ = (starRingEnd ℂ) (sg n z k μ) := Complex.inv_eq_conj (norm_sg z k μ)
    have h2 : ((sg n z k μ)⁻¹ - 1) = (starRingEnd ℂ) (sg n z k μ - 1) := by
      rw [map_sub, map_one, h1]
    rw [h2, mul_comm, Complex.conj_mul']
    push_cast; ring
  simp only [this, ← Finset.sum_smul]
  push_cast
  rfl

theorem Lap_pk (hn : 0 < n) (z : Fin 3 → Circle) (k : Cell n) :
    (cellSym hn z).Lap (pk n z k) = ((lam n z k : ℝ) : ℂ) • pk n z k := by
  unfold pk
  rw [SymData.Lap_smul, Lap_pwv hn, smul_comm]

/-- Parseval for the energy: `Ef f = Σ_k λ_k |⟨e_k, f⟩|²` -/
theorem Ef_parseval (hn : 0 < n) (z : Fin 3 → Circle) (f : CV n) :
    Ef (cellSym hn z) f = ∑ k : Cell n, lam n z k * ‖⟪pk n z k, f⟫‖ ^ 2 := by
  have h1 := (onb hn z).sum_inner_mul_inner f ((cellSym hn z).Lap f)
  have h2 : ∀ k : Cell n, ⟪f, onb hn z k⟫ * ⟪onb hn z k, (cellSym hn z).Lap f⟫
      = ((lam n z k * ‖⟪pk n z k, f⟫‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have e1 : ⟪f, onb hn z k⟫ = (starRingEnd ℂ) ⟪pk n z k, f⟫ := by
      rw [onb_apply]; exact (inner_conj_symm f (pk n z k)).symm
    have e2 : ⟪onb hn z k, (cellSym hn z).Lap f⟫ = (lam n z k : ℂ) * ⟪pk n z k, f⟫ := by
      rw [onb_apply, ← (cellSym hn z).Lap_selfadj, Lap_pk hn, inner_smul_left, Complex.conj_ofReal]
    rw [e1, e2]
    have : (starRingEnd ℂ) ⟪pk n z k, f⟫ * ⟪pk n z k, f⟫ = ((‖⟪pk n z k, f⟫‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    push_cast at this ⊢
    linear_combination (lam n z k : ℂ) * this
  simp only [h2] at h1
  have h3 : ((Ef (cellSym hn z) f : ℝ) : ℂ) = ⟪f, (cellSym hn z).Lap f⟫ := Ef_eq _ f
  rw [← h1] at h3
  have h4 : ((∑ k : Cell n, lam n z k * ‖⟪pk n z k, f⟫‖ ^ 2 : ℝ) : ℂ)
      = ∑ k : Cell n, ((lam n z k * ‖⟪pk n z k, f⟫‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [← h4] at h3
  exact_mod_cast h3

theorem parseval_pk (hn : 0 < n) (z : Fin 3 → Circle) (f : CV n) :
    ∑ k : Cell n, ‖⟪pk n z k, f⟫‖ ^ 2 = ‖f‖ ^ 2 := by
  have := (onb hn z).sum_sq_norm_inner_right f
  simpa [onb_apply] using this

end Basis

#print axioms Ef_parseval
#print axioms parseval_pk

end AdalyFormal.ScaledCoercivity

import GFC13

/-!
# GFC14 -- the projected-divergence term on eigen fields, and the eigen-field coercivity.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace
open AdalyFormal.Target.ClayStatement

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

theorem eigS_of_equiv {β : Type*} [Fintype β] (χ : AddChar (Site L) ℂ) (A : EuclideanSpace ℂ (Site L × β))
    (hA : IsEig n χ A) (Lm : EuclideanSpace ℂ (Site L × β) →ₗ[ℂ] TS L)
    (hL : ∀ (g : Site L) (A : EuclideanSpace ℂ (Site L × β)), Lm (shiftE n g β A) = shiftS n g (Lm A)) :
    IsEigS n χ (Lm A) := by
  intro g x
  have h1 : shiftE n g β A = χ g • A := by
    ext ⟨y, c⟩
    rw [shiftE_apply]
    exact hA g y c
  have h2 := hL g A
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun F => F x) h2
  simp only [shiftS_apply] at h3
  simpa using h3.symm

theorem eigS_lap (χ : AddChar (Site L) ℂ) (φ : TS L) (hφ : IsEigS n χ φ) : IsEigS n χ (lapC L φ) := by
  intro g x
  have h1 : shiftS n g φ = χ g • φ := by
    ext y
    rw [shiftS_apply]
    exact hφ g y
  have h2 := lapC_equiv (n := n) g φ
  rw [h1, map_smul] at h2
  have h3 := congrArg (fun F => F x) h2
  simp only [shiftS_apply] at h3
  simpa using h3.symm

theorem Dst_cell (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (t : Cell n) :
    Dst L A (ιc hdvd t) = (cellSym hn (zOf χ)).Dstar (fun μ => vOf hdvd A μ) t := by
  rw [Dst_apply]
  unfold SymData.Dstar
  rw [show (∑ μ, (cellSym hn (zOf χ)).Ds μ (vOf hdvd A μ)) t
      = ∑ μ, ((cellSym hn (zOf χ)).Ds μ (vOf hdvd A μ)) t from by
    simp [WithLp.ofLp_sum, Finset.sum_apply]]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [eig_shift_neg hn hdvd χ A hA]
  show _ = ((Su hn (zOf χ) μ).symm (vOf hdvd A μ)) t - vOf hdvd A μ t
  rfl

/-- **the projected-divergence hypothesis of the cell theorem, for eigen fields** -/
theorem L3_ratio (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (χ : AddChar (Site L) ℂ) (A : TB L)
    (hA : IsEig n χ A) (hzM : ∀ μ, ((zOf χ μ : Circle) : ℂ) ^ Mc L n μ = 1) (u : CV n)
    (hu : ⟪epsV n, u⟫ = 0) :
    ‖⟪(cellSym hn (zOf χ)).Dstar (fun μ => vOf hdvd A μ), (cellSym hn (zOf χ)).Lap u⟫‖ ^ 2
      ≤ (‖L3 hdvd A‖ ^ 2 / Mnum L n) * ‖(cellSym hn (zOf χ)).Lap u‖ ^ 2 := by
  set f : TS L := Dst L A with hf
  set y : TS L := lapC L (wu hn (fun μ => ((zOf χ μ : Circle) : ℂ)) u) with hy
  have hfE : IsEigS n χ f := eigS_of_equiv χ A hA (Dst L) (fun g A => Dst_equiv g A)
  have hwE := wu_eig hn hdvd χ hzM u
  have hyE : IsEigS n χ y := eigS_lap χ _ hwE
  have hyDW : y ∈ DW (n := n) hdvd :=
    Submodule.mem_map.mpr ⟨_, wu_mem_Wc hn hdvd χ hzM u hu, rfl⟩
  have hM := Mnum_pos hn hdvd
  have hinner : ⟪f, y⟫ = (Mnum L n : ℂ) * ⟪(cellSym hn (zOf χ)).Dstar (fun μ => vOf hdvd A μ), (cellSym hn (zOf χ)).Lap u⟫ := by
    rw [innerS_eig hn hdvd χ f y hfE hyE, PiLp.inner_apply]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hf, hy, Dst_cell hn hdvd χ A hA, lapC_wu_cell hn hdvd χ hzM u]
    simp [mul_comm]
  have hnorm : ‖y‖ ^ 2 = Mnum L n * ‖(cellSym hn (zOf χ)).Lap u‖ ^ 2 := by
    rw [normS_eig hn hdvd χ y hyE, EuclideanSpace.norm_sq_eq]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hy, lapC_wu_cell hn hdvd χ hzM u]
  have hproj : ⟪f, y⟫ = ⟪Pw hdvd f, y⟫ := by
    have h0 := Submodule.starProjection_inner_eq_zero f y hyDW
    have : ⟪f, y⟫ - ⟪Pw hdvd f, y⟫ = 0 := by
      rw [← inner_sub_left]; exact h0
    exact sub_eq_zero.mp this
  have hCS : ‖⟪f, y⟫‖ ≤ ‖Pw hdvd f‖ * ‖y‖ := by
    rw [hproj]; exact norm_inner_le_norm _ _
  have hL3 : L3 hdvd A = Pw hdvd f := rfl
  rw [hL3]
  have h1 : ‖⟪f, y⟫‖ = Mnum L n * ‖⟪(cellSym hn (zOf χ)).Dstar (fun μ => vOf hdvd A μ), (cellSym hn (zOf χ)).Lap u⟫‖ := by
    rw [hinner, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  rw [h1] at hCS
  have h2 : (Mnum L n * ‖⟪(cellSym hn (zOf χ)).Dstar (fun μ => vOf hdvd A μ), (cellSym hn (zOf χ)).Lap u⟫‖) ^ 2
      ≤ (‖Pw hdvd f‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (by positivity) hCS 2
  rw [mul_pow, mul_pow, hnorm] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hM]
  nlinarith [h2, hM]

#print axioms L3_ratio

end AdalyFormal.FlatCoercivity

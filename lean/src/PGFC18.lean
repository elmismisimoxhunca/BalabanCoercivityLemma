import PGFC17

/-!
# GFC18 -- repo bridge, part 2: blocks, line paths and the line-block average.  Standard axioms only.
-/
set_option autoImplicit false
open scoped BigOperators ComplexInnerProductSpace RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice mem_blockOf)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

namespace AdalyFormal.FlatCoercivity

variable {L : PeriodicLatticeExtent} {n : ℕ}

theorem pathSite_eq (x : Site L) (μ : Fin 3) (i : ℕ) : pathSite x μ i = x + i • eU L μ := by
  induction i with
  | zero => simp [AdalyFormal.Balaban.QOne.pathSite_zero]
  | succ i ih => rw [AdalyFormal.Balaban.QOne.pathSite_succ, ih, shift_eq, succ_nsmul, add_assoc]

theorem coarse_iff (y : Site L) : Coarse n y ↔ ∀ μ : Fin 3, (y μ).val % n = 0 := by
  unfold Coarse
  exact forall_congr' (fun μ => Nat.dvd_iff_mod_eq_zero)

theorem coarse_val_add (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (y : Site L) (hy : Coarse n y) (t : Cell n) (μ : Fin 3) :
    ((y + ιc hdvd t) μ : ℕ) = (y μ : ℕ) + (t μ : ℕ) := by
  have h1 : ((y + ιc hdvd t) μ : ℕ) = ((y μ : ℕ) + (t μ : ℕ)) % (L μ + 1) := by
    simp [Fin.val_add, ιc]
  obtain ⟨k, hk⟩ := hy μ
  obtain ⟨M, hM⟩ := hdvd μ
  have h2 := (y μ).isLt
  have h3 := (t μ).isLt
  rw [h1]
  apply Nat.mod_eq_of_lt
  rw [hk] at h2 ⊢
  rw [hM] at h2 ⊢
  have : k < M := by
    by_contra hh; push_neg at hh; nlinarith
  nlinarith

theorem block_sum_eq (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) {M : Type*} [AddCommMonoid M] (f : Site L → M)
    (y : Site L) (hy : Coarse n y) :
    ∑ x ∈ blockOf y n, f x = ∑ t : Cell n, f (y + ιc hdvd t) := by
  symm
  refine Finset.sum_bij (fun t _ => y + ιc hdvd t) ?_ ?_ ?_ ?_
  · intro t _
    rw [mem_blockOf]
    intro μ
    rw [coarse_val_add hn hdvd y hy t μ]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (t μ).isLt _⟩
  · intro t _ t' _ h
    have h' : ιc hdvd t = ιc hdvd t' := add_left_cancel h
    funext μ
    apply Fin.ext
    have := congrFun h' μ
    exact Fin.mk.inj_iff.mp this
  · intro x hx
    rw [mem_blockOf] at hx
    refine ⟨fun μ => ⟨(x μ : ℕ) - (y μ : ℕ), by have := (hx μ).2; have := (hx μ).1; omega⟩, Finset.mem_univ _, ?_⟩
    funext μ
    apply Fin.ext
    rw [coarse_val_add hn hdvd y hy]
    have := (hx μ).1
    simp only [ιc]
    omega
  · intro t _; rfl

#print axioms block_sum_eq

theorem crd_sum {ι : Type*} (s : Finset ι) (f : ι → SuTwo) (j : JJ) : crd (∑ i ∈ s, f i) j = ∑ i ∈ s, crd (f i) j := by
  unfold crd
  rw [map_sum]
  simp

theorem LCR_crd (hn : 0 < n) (A : Bond L → SuTwo) (b : CoarseBond L n) (j : JJ) :
    crd (lineCoarseRestrictSuTwo n A b) j
      = (1 / (n : ℝ) ^ 4) * ∑ x ∈ blockOf b.1.1 n, ∑ i ∈ Finset.range n, crd (A (pathSite x b.2 i, b.2)) j := by
  unfold lineCoarseRestrictSuTwo
  rw [crd_smul, crd_sum]
  simp only [crd_sum]

theorem L2_coord_coarse (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (A : Bond L → SuTwo) (j : JJ) (y : Site L)
    (hy : y ∈ CoarseLattice L n) (μ : Fin 3) :
    ‖L2 hdvd (coordB A j) (y, μ)‖ ^ 2
      = ((n : ℝ) ^ 4 * crd (lineCoarseRestrictSuTwo n A (⟨y, hy⟩, μ)) j) ^ 2 := by
  have hc : Coarse n y := (coarse_iff y).mpr (mem_CoarseLattice.mp hy)
  rw [L2_apply, if_pos hc, LCR_crd hn]
  have h1 : ((n : ℝ) ^ 4 * ((1 / (n : ℝ) ^ 4) * ∑ x ∈ blockOf y n, ∑ i ∈ Finset.range n, crd (A (pathSite x μ i, μ)) j))
      = ∑ t : Cell n, ∑ i ∈ Finset.range n, crd (A (y + ιc hdvd t + i • eU L μ, μ)) j := by
    have hn' : (n : ℝ) ^ 4 ≠ 0 := by positivity
    rw [← mul_assoc, mul_one_div_cancel hn', one_mul]
    rw [block_sum_eq hn hdvd (fun x => ∑ i ∈ Finset.range n, crd (A (pathSite x μ i, μ)) j) y hc]
    refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [pathSite_eq, add_assoc]
  show ‖∑ t : Cell n, ∑ i ∈ Finset.range n, coordB A j (y + ιc hdvd t + i • eU L μ, μ)‖ ^ 2 = _
  simp only [coordB_apply]
  rw [h1]
  have e : (∑ t : Cell n, ∑ i ∈ Finset.range n, (((crd (A (y + ιc hdvd t + i • eU L μ, μ)) j : ℝ)) : ℂ))
      = ((∑ t : Cell n, ∑ i ∈ Finset.range n, crd (A (y + ιc hdvd t + i • eU L μ, μ)) j : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem L2_coord_not (hdvd : ∀ μ, n ∣ L μ + 1) (A : Bond L → SuTwo) (j : JJ) (y : Site L)
    (hy : ¬ y ∈ CoarseLattice L n) (μ : Fin 3) : L2 hdvd (coordB A j) (y, μ) = 0 := by
  have hc : ¬ Coarse n y := fun h => hy (mem_CoarseLattice.mpr ((coarse_iff y).mp h))
  rw [L2_apply, if_neg hc]


theorem Qsum (hn : 0 < n) (hdvd : ∀ μ, n ∣ L μ + 1) (A : Bond L → SuTwo) :
    ∑ b : CoarseBond L n, ‖lineCoarseRestrictSuTwo n A b‖ ^ 2
      = (1 / (n : ℝ) ^ 8) * ∑ j, ‖L2 hdvd (coordB A j)‖ ^ 2 := by
  classical
  set Gf : Site L → Fin 3 → JJ → ℝ := fun y μ j =>
    if hy : y ∈ CoarseLattice L n then (crd (lineCoarseRestrictSuTwo n A (⟨y, hy⟩, μ)) j) ^ 2 else 0 with hGf
  have hR : ∀ j, ‖L2 hdvd (coordB A j)‖ ^ 2 = ∑ y : Site L, ∑ μ : Fin 3, (n : ℝ) ^ 8 * Gf y μ j := by
    intro j
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun μ _ => ?_))
    by_cases hy : y ∈ CoarseLattice L n
    · rw [L2_coord_coarse hn hdvd A j y hy μ]
      simp only [hGf, dif_pos hy]
      ring
    · rw [L2_coord_not hdvd A j y hy μ]
      simp [hGf, hy]
  have hL : ∑ b : CoarseBond L n, ‖lineCoarseRestrictSuTwo n A b‖ ^ 2
      = ∑ y : Site L, ∑ μ : Fin 3, ∑ j, Gf y μ j := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ (y : {y : Site L // y ∈ CoarseLattice L n}) (μ : Fin 3),
        ‖lineCoarseRestrictSuTwo n A (y, μ)‖ ^ 2 = ∑ j, Gf y.1 μ j := by
      intro y μ
      rw [norm_sq_crd]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hGf, dif_pos y.2]
    simp only [h1]
    have h2 : ∀ μ : Fin 3, ∑ y : {y : Site L // y ∈ CoarseLattice L n}, ∑ j, Gf y.1 μ j
        = ∑ y : Site L, ∑ j, Gf y μ j := by
      intro μ
      rw [← Finset.sum_subtype (CoarseLattice L n) (fun y => Iff.rfl) (fun y => ∑ j, Gf y μ j)]
      refine Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => ?_)
      refine Finset.sum_eq_zero (fun j _ => ?_)
      simp [hGf, hy]
    rw [Finset.sum_comm]
    simp only [h2]
    rw [Finset.sum_comm]
  rw [hL]
  simp only [hR]
  have hn8 : (n : ℝ) ^ 8 ≠ 0 := by positivity
  have : ∑ j, ∑ y : Site L, ∑ μ : Fin 3, (n : ℝ) ^ 8 * Gf y μ j = (n : ℝ) ^ 8 * ∑ y : Site L, ∑ μ : Fin 3, ∑ j, Gf y μ j := by
    simp only [← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_comm]
  rw [this]
  field_simp

end AdalyFormal.FlatCoercivity

import R7Fork.DM13c

/-!
# DM13d -- the block relation for the tilted potential across a coarse bond:
`sum_{block q} Theta - sum_{block p} Theta = - n^3 [wrap] N_mu c_mu`  given the row relation for `phi`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp Tower Admissible bigSide BlockClosed)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice card_blockOf_of_coarse)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.CoarseShiftCovariance (coarseShift_blockOf_eq_image coarseShift_injective)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

section rel
variable {L : PeriodicLatticeExtent}

/-- coordinate behaviour of `coarseShift` on a block: uniform wrap -/
theorem coarseShift_coord {n : ℕ} (hn : 0 < n) (μ : Fin 3) (hdvdA : ∀ ν, n ∣ L ν + 1) {p : PeriodicLatticeSite L}
    (hp : p ∈ CoarseLattice L n) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf p n) :
    ((coarseShift x n μ) μ).val + (if (p μ).val + n = L μ + 1 then L μ + 1 else 0) = (x μ).val + n := by
  rw [coarseShift_val_eq]
  have hxb := (mem_blockOf.mp hx) μ
  obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hp) μ)
  obtain ⟨b, hb⟩ := hdvdA μ
  have hlt := (p μ).isLt
  have hfit : (p μ).val + n ≤ L μ + 1 :=
    AdalyFormal.Balaban.ReparamCDisjoint.coarse_coord_add_ell_le hdvdA μ (p μ).val ((mem_CoarseLattice.mp hp) μ) hlt
  by_cases hw : (p μ).val + n = L μ + 1
  · rw [if_pos hw]
    have h1 : (L μ + 1) ≤ (x μ).val + n := by omega
    have h2 : (x μ).val + n < 2 * (L μ + 1) := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg hw]
    have hlt2 : (p μ).val + n < L μ + 1 := by omega
    have hab : a + 1 < b := by
      by_contra hcon
      have : b ≤ a + 1 := by omega
      have : n * b ≤ n * (a + 1) := Nat.mul_le_mul_left n this
      rw [mul_add, mul_one] at this
      omega
    have h3 : n * (a + 2) ≤ n * b := Nat.mul_le_mul_left n (by omega)
    rw [mul_add] at h3
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem Theta_block_rel {n : ℕ} (hn : 0 < n) (hN : ∀ ν, 1 ≤ L ν) (φ : PeriodicLatticeSite L → SuTwo) (c : Fin 3 → SuTwo)
    (hdvd : ∀ ν, n ∣ L ν + 1) {p : PeriodicLatticeSite L} (hp : p ∈ CoarseLattice L n) (μ : Fin 3)
    (hrel : (1 / (n : ℝ) ^ 4) • (∑ x ∈ blockOf (coarseShift p n μ) n, φ x - ∑ x ∈ blockOf p n, φ x) + c μ = 0) :
    ∑ x ∈ blockOf (coarseShift p n μ) n, Theta φ c x - ∑ x ∈ blockOf p n, Theta φ c x
      = -(((n : ℝ) ^ 3) * (if (p μ).val + n = L μ + 1 then ((L μ + 1 : ℕ) : ℝ) else 0)) • c μ := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have himg := coarseShift_blockOf_eq_image hn (hdvd μ) hp
  have hq : ∑ x ∈ blockOf (coarseShift p n μ) n, Theta φ c x
      = ∑ x ∈ blockOf p n, Theta φ c (coarseShift x n μ) := by
    rw [himg, Finset.sum_image (fun a _ b _ h => coarseShift_injective n μ h)]
  have hq2 : ∑ x ∈ blockOf (coarseShift p n μ) n, φ x = ∑ x ∈ blockOf p n, φ (coarseShift x n μ) := by
    rw [himg, Finset.sum_image (fun a _ b _ h => coarseShift_injective n μ h)]
  have hcard : (blockOf p n).card = n ^ 3 := card_blockOf_of_coarse hdvd hp
  -- pointwise difference
  have hpt : ∀ x ∈ blockOf p n, Theta φ c (coarseShift x n μ) - Theta φ c x
      = (φ (coarseShift x n μ) - φ x) + ((n : ℝ) - (if (p μ).val + n = L μ + 1 then ((L μ + 1 : ℕ) : ℝ) else 0)) • c μ := by
    intro x hx
    have hco := coarseShift_coord hn μ hdvd hp hx
    have hcoR : (((coarseShift x n μ) μ).val : ℝ) = ((x μ).val : ℝ) + n -
        (if (p μ).val + n = L μ + 1 then ((L μ + 1 : ℕ) : ℝ) else 0) := by
      have h := congrArg (fun t : ℕ => (t : ℝ)) hco
      simp only [Nat.cast_add] at h
      split_ifs at h ⊢ <;> push_cast at h ⊢ <;> linarith
    have hsumdiff : ∑ ν : Fin 3, (((coarseShift x n μ) ν).val : ℝ) • c ν - ∑ ν : Fin 3, ((x ν).val : ℝ) • c ν
        = ((((coarseShift x n μ) μ).val : ℝ) - ((x μ).val : ℝ)) • c μ := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single μ]
      · rw [sub_smul]
      · intro ν _ hνμ
        simp [coarseShift_apply_ne x n μ ν hνμ]
      · intro h; exact absurd (Finset.mem_univ μ) h
    unfold Theta
    rw [hcoR] at hsumdiff
    calc φ (coarseShift x n μ) + ∑ ν : Fin 3, (((coarseShift x n μ) ν).val : ℝ) • c ν - (φ x + ∑ ν : Fin 3, ((x ν).val : ℝ) • c ν)
        = (φ (coarseShift x n μ) - φ x) + (∑ ν : Fin 3, (((coarseShift x n μ) ν).val : ℝ) • c ν - ∑ ν : Fin 3, ((x ν).val : ℝ) • c ν) := by abel
      _ = _ := by rw [hsumdiff]; congr 2; ring
  have hsum : ∑ x ∈ blockOf p n, Theta φ c (coarseShift x n μ) - ∑ x ∈ blockOf p n, Theta φ c x
      = (∑ x ∈ blockOf p n, φ (coarseShift x n μ) - ∑ x ∈ blockOf p n, φ x) +
        ((n ^ 3 : ℕ) : ℝ) • (((n : ℝ) - (if (p μ).val + n = L μ + 1 then ((L μ + 1 : ℕ) : ℝ) else 0)) • c μ) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, hcard, Nat.cast_smul_eq_nsmul]
  rw [← hq, ← hq2] at hsum
  rw [hsum]
  have h4 : ∑ x ∈ blockOf (coarseShift p n μ) n, φ x - ∑ x ∈ blockOf p n, φ x = -((n : ℝ) ^ 4) • c μ := by
    have := hrel
    have h5 := congrArg (fun v => ((n : ℝ) ^ 4) • v) (eq_neg_of_add_eq_zero_left this)
    simp only [smul_smul, smul_neg] at h5
    have e : (n : ℝ) ^ 4 * (1 / (n : ℝ) ^ 4) = 1 := by field_simp
    rw [e, one_smul] at h5
    rw [h5, neg_smul]
  rw [h4, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

end rel

#print axioms Theta_block_rel

end AdalyFormal.DirichletMono

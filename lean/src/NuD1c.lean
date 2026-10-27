import NuD1b

/-!
# NuD1c -- `bg1_stag0_all`: the first blocked level of the direction-0 staggered family at every base (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge loopVar coarseBondVar gammaVarStrided cPlusS cPlusS_eq)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)

section
variable [CfData]
variable {L : PeriodicLatticeExtent}

theorem hD0_stride_one {ell : ℕ} (hN0 : ell ≤ L 0 + 1) (xs : ℕ) :
    ∀ (a m : ℕ), m ≤ ell → |∑ j ∈ Finset.range m, D0 xs ((a + 1 * j) % (L 0 + 1))| ≤ 1 := by
  intro a m hm
  have := sum_D0_le_one xs a (L 0 + 1) m (by omega)
  simp only [one_mul]
  rw [abs_of_nonneg this.1]; exact this.2

theorem uSt_abs_le (t : ℝ) : ∀ a b, |uSt t a b| ≤ |t| := by
  intro a b
  unfold uSt
  rw [abs_mul]
  calc |sgnNat a| * |t| ≤ 1 * |t| := by gcongr; exact sgnNat_abs_le a
    _ = |t| := one_mul _

/-- level 0: every loop of the direction-0 staggered family has `|angle| < π` when `|t| < π/2`. -/
theorem regBg2_level0_stag0 {ell : ℕ} (hN0 : ell ≤ L 0 + 1) (xs : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) :
    RegBg2 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) :=
  regBg2_of_uTemp one_pos (stag0_isUTemp xs t) (uSt_abs_le t) (by linarith) (hD0_stride_one hN0 xs)

/-- **the first blocked level of the direction-0 staggered family, at every base `z`.** -/
theorem bg1_stag0_all {ell : ℕ} (hell : 0 < ell) (hN0 : ell ≤ L 0 + 1) (hN : 2 ∣ L 1 + 1) (hE : 2 ∣ ell)
    (xs : ℕ) (t : ℝ) (ht : |t| < Real.pi / 2) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    stridedBlockedGauge su2LogExp 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) (z, μ) =
      cartan (if μ = 0 then Sw0 xs ell (L 0 + 1) (z 0).val * Ubg0 ell t z else 0) := by
  have hV := stag0_isUTemp (L := L) xs t
  have hcb : coarseBondVar 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) (z, μ) =
      cartan (if μ = 0 then (∑ j ∈ Finset.range ell, D0 xs (((z 0).val + 1 * j) % (L 0 + 1))) * uSt t (z 1).val (z 2).val else 0) := by
    unfold coarseBondVar
    rw [hol_uTemp hV]
    congr 1
    by_cases hμ : μ = 0
    · subst hμ; simp only [if_true]; rw [uAng_rep_zero, ← Finset.sum_mul]
    · simp only [hμ, if_false]; exact uAng_rep_ne 1 _ _ μ hμ ell z
  have hloop : ∀ x ∈ stepBlockOf (z, μ).1 1 ell,
      loopVar 1 ell (stag0Cfg (L := L) xs t : PeriodicLinkConfiguration SU2 L) (z, μ) x = cartan (uPhi 1 ell (D0 xs) (uSt t) z μ x) ∧
        |uPhi 1 ell (D0 xs) (uSt t) z μ x| < Real.pi :=
    fun x hx => ⟨loopVar_uPhi hV z μ hx, uPhi_abs_lt one_pos (uSt_abs_le t) (by linarith) (hD0_stride_one hN0 xs) z μ hx⟩
  rw [blocked_cartan 1 ell _ (z, μ) (fun x => uPhi 1 ell (D0 xs) (uSt t) z μ x) _ hloop hcb]
  congr 1
  have hS : (∑ j ∈ Finset.range ell, D0 xs (((z 0).val + 1 * j) % (L 0 + 1))) = Sw0 xs ell (L 0 + 1) (z 0).val := by
    unfold Sw0; simp only [one_mul]
  rcases (show μ = 0 ∨ μ = 1 ∨ μ = 2 by fin_cases μ <;> simp) with rfl | rfl | rfl
  · simp only [uPhi, if_true]
    rw [hS]
    -- the block sum
    have hn1 : ∀ x ∈ stepBlockOf z 1 ell, uSt t (x 1).val (x 2).val - uSt t (z 1).val (z 2).val =
        (fun n : ℕ => (sgnNat ((z 1).val + n) - sgnNat (z 1).val) * t) (((x 1).val) - (z 1).val) := by
      intro x hx
      have h := mem_stepBlockOf.mp hx 1
      have hle : (z 1).val ≤ (x 1).val := h.1
      simp only [uSt]
      rw [show (z 1).val + ((x 1).val - (z 1).val) = (x 1).val by omega]
      ring
    have h1 : ∀ x ∈ stepBlockOf z 1 ell,
        Sw0 xs ell (L 0 + 1) (z 0).val * (uSt t (x 1).val (x 2).val - uSt t (z 1).val (z 2).val) =
        Sw0 xs ell (L 0 + 1) (z 0).val *
          (fun n : ℕ => (sgnNat ((z 1).val + n) - sgnNat (z 1).val) * t) (((x 1).val) - (z 1).val) := by
      intro x hx; rw [hn1 x hx]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      sum_block_one z ell (fun n : ℕ => (sgnNat ((z 1).val + n) - sgnNat (z 1).val) * t)]
    have hsum : ∑ n ∈ Finset.range (min ell (L 1 + 1 - (z 1).val)), (sgnNat ((z 1).val + n) - sgnNat (z 1).val) * t =
        -(2 * (((min ell (L 1 + 1 - (z 1).val)) / 2 : ℕ) : ℝ)) * (sgnNat (z 1).val * t) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, altsum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      generalize min ell (L 1 + 1 - (z 1).val) = m
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · have e1 : m % 2 = 0 := by omega
        have e2 : m / 2 = k := by omega
        rw [if_pos e1, e2, hk]; push_cast; ring
      · have e1 : ¬ m % 2 = 0 := by omega
        have e2 : m / 2 = k := by omega
        rw [if_neg e1, e2, hk]; push_cast; ring
    rw [hsum]
    unfold Ubg0
    simp only [uSt, hS, eq_self_iff_true, if_true]
    have hl : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
    field_simp
    ring
  · simp only [uPhi, if_neg (show ¬ ((1 : Fin 3) = 0) by decide), if_true]
    have h1 : ∀ x ∈ stepBlockOf z 1 ell,
        (∑ j ∈ Finset.range ((x 0 - z 0).val / 1), D0 xs (((z 0).val + 1 * j) % (L 0 + 1))) *
          (uSt t (x 1).val (x 2).val - uSt t (((x 1).val + 1 * ell) % (L 1 + 1)) (x 2).val) = 0 := by
      intro x _
      simp only [uSt, one_mul, sgnNat_mod_even hN hE]
      ring
    rw [Finset.sum_eq_zero h1]
    simp
  · have h20 : ¬ ((2 : Fin 3) = 0) := by decide
    have h21 : ¬ ((2 : Fin 3) = 1) := by decide
    simp only [uPhi, h20, h21, if_false]
    have h1 : ∀ x ∈ stepBlockOf z 1 ell,
        (∑ j ∈ Finset.range ((x 0 - z 0).val / 1), D0 xs (((z 0).val + 1 * j) % (L 0 + 1))) *
          (uSt t (x 1).val (x 2).val - uSt t (x 1).val (((x 2).val + 1 * ell) % (L 2 + 1))) = 0 := by
      intro x _
      simp only [uSt]
      ring
    rw [Finset.sum_eq_zero h1]
    simp

end

end AdalyFormal.NcwdhTwo

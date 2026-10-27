import D2Geo4

/-!
# D2Geo5 -- mass term for a bond field supported within `2` of the complement of `Ω₀`: `⟨A, Q*aQ A⟩ ≤ a ‖A‖²` (levels `j ≥ 1` do not see `A`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.NonVac
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.SuTwoLogExp (M2)

variable {L : PeriodicLatticeExtent}

theorem QlinB_supp_zero {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (h9 : 9 * ell ≤ R * M) (U : Cfg L) (A : BondFnL2 L)
    (hsupp : ∀ e : Bond L, A e ≠ 0 → ∃ w : PeriodicLatticeSite L, w ∉ S.Om 0 ∧ pdist e.1 w ≤ 2)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond L} (hb : b ∈ bondsLam (geomOf ell k S) j) :
    (QlinB (geomOf ell k S) U j A) b = 0 := by
  obtain ⟨hb1, -⟩ := hb
  obtain ⟨y, hyOm, hyd⟩ : ∃ y : PeriodicLatticeSite L, y ∈ S.Om j ∧ pdist b.1 y ≤ ell ^ j := by
    rcases hb1 with h | h
    · exact ⟨b.1, h.2.1, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨_, h.2.1, ?_⟩
      exact pdist_coarseShift_le b.1 (ell ^ j) b.2
  have hball := admissible_ball_Om0 hS hj1 (by omega) hyOm
  have hpow : ell ^ j = ell * ell ^ (j - 1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have hRM : 9 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
    calc 9 * ell ^ j = (9 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
      _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ h9
      _ = R * (M * ell ^ (j - 1)) := by ring
  have hrho := rhoT_le ell hell j
  have hz : QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j (suCoord A) b
      = QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j 0 b := by
    refine QlinCompL_congr_in (geomOf ell k S).ell (by show 0 < ell; omega) _ j b (fun e he => ?_)
    have hAe : A e = 0 := by
      by_contra hne
      obtain ⟨w, hw, hwd⟩ := hsupp e hne
      have hwball : w ∉ Ball y (R * (M * ell ^ (j - 1))) := fun hm => hw (hball hm)
      have hfar : R * (M * ell ^ (j - 1)) < pdist y w := by
        by_contra hnot
        exact hwball (by simpa [Ball] using (not_lt.mp hnot))
      have t1 := pdist_triangle y b.1 w
      have t2 := pdist_triangle b.1 e.1 w
      have h2 : pdist y b.1 ≤ ell ^ j := by rw [pdist_comm]; exact hyd
      have he' : pdist b.1 e.1 ≤ rhoT ell j := he
      omega
    show suCoord A e = (0 : XS L) e
    show fromM2 (((WithLp.ofLp A) e : SuTwo) : M2) = (0 : XS L) e
    rw [show (WithLp.ofLp A) e = 0 from hAe]
    simp
  rw [QlinB_apply]
  rw [suCoordInv_apply_congr' hz]
  simp

theorem Mass_supp_le {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (h9 : 9 * ell ≤ R * M) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a) (A : BondFnL2 L)
    (hsupp : ∀ e : Bond L, A e ≠ 0 → ∃ w : PeriodicLatticeSite L, w ∉ S.Om 0 ∧ pdist e.1 w ≤ 2) :
    (inner ℝ A (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) A) : ℝ) ≤ a * ‖A‖ ^ 2 := by
  classical
  rw [inner_MassFull]
  have hterm : ∀ p : BIdx (geomOf ell k S),
      a * ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) * ‖(bondSectorOf (geomOf ell k S) U).Qfull A p‖ ^ 2
        = if (p.1 : ℕ) = 0 then a * ‖A p.2.1‖ ^ 2 else 0 := by
    rintro ⟨j, b, hb⟩
    show a * ((ell : ℝ)) ^ (j : ℕ) * ‖(((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell k S) U j A)) b‖ ^ 2 = _
    by_cases hj : (j : ℕ) = 0
    · have hq : QlinB (geomOf ell k S) U (j : ℕ) A = A := by rw [hj]; exact QlinB_zero _ _ _
      have hp : ((ell : ℝ) ^ (j : ℕ)) = 1 := by rw [hj]; simp
      rw [hq, hp]
      simp only [inv_one, one_smul, mul_one]
      simp only [hj, if_true]
    · have hz := QlinB_supp_zero hS hell h9 U A hsupp (j := j) (by omega) (Nat.lt_succ_iff.mp j.2) hb
      rw [show (WithLp.ofLp (QlinB (geomOf ell k S) U j A)) b = 0 from hz]
      simp [hj]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun p : BIdx (geomOf ell k S) => p.2.1)
      ↑(Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = 0)) := by
    rintro ⟨j, b, hb⟩ hp ⟨j', b', hb'⟩ hq hbb
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hq
    have e1 : j = j' := Fin.ext (by rw [hp, hq])
    subst e1
    have : b = b' := hbb
    subst this
    rfl
  rw [← Finset.sum_image (f := fun b : Bond L => a * ‖A b‖ ^ 2) hinj]
  have hle : ∑ b ∈ (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = 0)).image (fun p => p.2.1),
      a * ‖A b‖ ^ 2 ≤ ∑ b : Bond L, a * ‖A b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => by positivity)
  refine le_trans hle ?_
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]

#print axioms QlinB_supp_zero
#print axioms Mass_supp_le

end AdalyFormal.D1Literal

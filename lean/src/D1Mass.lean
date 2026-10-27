import D1Geo2

/-!
# D1Mass -- the mass term on the single-bond field at the boundary bond: `⟨A, Q*aQ A⟩ ≤ a ⟨X,X⟩`.
Only the level-0 row of the bond itself sees `A` (level-`j ≥ 1` rows read `A` only within `rhoT j` of a site of `Λ_j ⊂ Ω_j`, and `Ω_j` is `R M`-far from `∂Ω₀`).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.SuTwoLogExp (M2)

variable {L : PeriodicLatticeExtent}

theorem suCoordInv_apply_congr' {x x' : XS L} {b : Bond L} (h : x b = x' b) :
    (suCoordInv x : BondFnL2 L) b = (suCoordInv x' : BondFnL2 L) b := by
  apply Subtype.ext
  show toM2 (x b) = toM2 (x' b)
  rw [h]

/-- rows of level `j ≥ 1` on bonds of `𝔅_j` do not see the single bond at `(x,0)`. -/
theorem QlinB_sing_zero {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (h9 : 9 * ell ≤ R * M) {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x) (U : Cfg L) (X : SuTwo)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {b : Bond L} (hb : b ∈ bondsLam (geomOf ell k S) j) :
    (QlinB (geomOf ell k S) U j (sing (x, (0 : Fin 3)) X)) b = 0 := by
  obtain ⟨hb1, -⟩ := hb
  -- a site `y ∈ Ω_j` within `ell^j` of `b.1`
  obtain ⟨y, hyOm, hyd⟩ : ∃ y : PeriodicLatticeSite L, y ∈ S.Om j ∧ pdist b.1 y ≤ ell ^ j := by
    rcases hb1 with h | h
    · exact ⟨b.1, h.2.1, by rw [AdalyFormal.StatementLaneR8.pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨_, h.2.1, ?_⟩
      exact pdist_coarseShift_le b.1 (ell ^ j) b.2
  have hball := admissible_ball_Om0 hS hj1 (by omega) hyOm
  have hx'ball : periodicLatticeShift x 0 ∉ Ball y (R * (M * ell ^ (j - 1))) := fun hm => hbd.hx' (hball hm)
  have hfar : R * (M * ell ^ (j - 1)) < pdist y (periodicLatticeShift x 0) := by
    by_contra hnot
    exact hx'ball (by simpa [Ball] using (not_lt.mp hnot))
  have h1 : pdist y (periodicLatticeShift x 0) ≤ pdist y b.1 + pdist b.1 x + pdist x (periodicLatticeShift x 0) := by
    have t1 := pdist_triangle y b.1 (periodicLatticeShift x 0)
    have t2 := pdist_triangle b.1 x (periodicLatticeShift x 0)
    omega
  have h2 : pdist y b.1 ≤ ell ^ j := by rw [pdist_comm]; exact hyd
  have h3 : pdist x (periodicLatticeShift x 0) ≤ 1 := pdist_shift_le _ _
  have hpow : ell ^ j = ell * ell ^ (j - 1) := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have hRM : 9 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
    calc 9 * ell ^ j = (9 * ell) * ell ^ (j - 1) := by rw [hpow]; ring
      _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ h9
      _ = R * (M * ell ^ (j - 1)) := by ring
  have hrho := rhoT_le ell hell j
  have hfarx : rhoT ell j < pdist b.1 x := by omega
  -- locality of the jet in the input
  have hz : QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j (suCoord (sing (x, (0 : Fin 3)) X)) b
      = QlinCompL (geomOf ell k S).ell (bgTower (geomOf ell k S) U) j 0 b := by
    refine QlinCompL_congr_in (geomOf ell k S).ell (by show 0 < ell; omega) _ j b (fun e he => ?_)
    have hne : e ≠ (x, (0 : Fin 3)) := by
      intro heq
      have : pdist b.1 x ≤ rhoT ell j := by rw [heq] at he; exact he
      omega
    show suCoord (sing (x, (0 : Fin 3)) X) e = (0 : XS L) e
    have : (sing (x, (0 : Fin 3)) X) e = 0 := sing_apply_ne _ _ hne
    show fromM2 (((WithLp.ofLp (sing (x, (0 : Fin 3)) X)) e : SuTwo) : M2) = (0 : XS L) e
    rw [show (WithLp.ofLp (sing (x, (0 : Fin 3)) X)) e = 0 from this]
    simp
  rw [QlinB_apply]
  rw [suCoordInv_apply_congr' hz]
  simp

theorem Mass_sing_le {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (hell : 2 ≤ ell)
    (h9 : 9 * ell ≤ R * M) {x : PeriodicLatticeSite L} (hbd : BdPt (S.Om 0) x) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (X : SuTwo) :
    (inner ℝ (sing (x, (0 : Fin 3)) X) (MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) U) (sing (x, (0 : Fin 3)) X)) : ℝ)
      ≤ a * hsInner X X := by
  classical
  rw [inner_MassFull]
  have hn : 0 ≤ hsInner X X := by
    have := real_inner_self_nonneg (x := X)
    exact this
  set b0 : Bond L := (x, (0 : Fin 3)) with hb0
  have hterm : ∀ p : BIdx (geomOf ell k S),
      a * ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) * ‖(bondSectorOf (geomOf ell k S) U).Qfull (sing b0 X) p‖ ^ 2
        = if ((p.1 : ℕ) = 0 ∧ p.2.1 = b0) then a * hsInner X X else 0 := by
    rintro ⟨j, b, hb⟩
    show a * ((ell : ℝ)) ^ (j : ℕ) * ‖(((ell : ℝ) ^ (j : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell k S) U j (sing b0 X))) b‖ ^ 2 = _
    by_cases hj : (j : ℕ) = 0
    · have hq : QlinB (geomOf ell k S) U (j : ℕ) (sing b0 X) = sing b0 X := by rw [hj]; exact QlinB_zero _ _ _
      have hp : ((ell : ℝ) ^ (j : ℕ)) = 1 := by rw [hj]; simp
      rw [hq, hp]
      simp only [inv_one, one_smul, mul_one]
      by_cases hbb : b = b0
      · simp only [hj, hbb, and_self, if_true]
        rw [hbb, sing_apply_self]
        have : ‖X‖ ^ 2 = hsInner X X := by
          rw [← real_inner_self_eq_norm_sq]; rfl
        rw [this]
      · simp only [hj, hbb, and_false, if_false]
        have : (WithLp.ofLp (sing b0 X)) b = 0 := sing_apply_ne _ _ hbb
        rw [this]; simp
    · have hz := QlinB_sing_zero hS hell h9 hbd U X (j := j) (by omega) (Nat.lt_succ_iff.mp j.2) hb
      rw [show (WithLp.ofLp (QlinB (geomOf ell k S) U j (sing b0 X))) b = 0 from hz]
      simp [hj]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  have hcard : (Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = 0 ∧ p.2.1 = b0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨j, b, hb⟩ hp ⟨j', b', hb'⟩ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have e1 : j = j' := Fin.ext (by rw [hp.1, hq.1])
    subst e1
    have e2 : b = b' := by rw [hp.2, hq.2]
    subst e2
    rfl
  have hpos : 0 ≤ a * hsInner X X := mul_nonneg ha hn
  calc _ = ((Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = 0 ∧ p.2.1 = b0)).card : ℝ) * (a * hsInner X X) := by
        rw [nsmul_eq_mul]
    _ ≤ 1 * (a * hsInner X X) := by
        gcongr
        exact_mod_cast hcard
    _ = a * hsInner X X := one_mul _

#print axioms QlinB_sing_zero
#print axioms Mass_sing_le

end AdalyFormal.D1Literal

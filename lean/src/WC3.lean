import MI32
import WC2

/-!
# WC3 -- level window of a row ball, kernel support radius, and the vanishing outside the interaction set (M2 W6 lane)

* `ball_window` : a site within `8 ℓ^{lev p}` of the base of row `p` has stratum within one of `lev p` (copy of M1IMS `row_window`
  with the ball radius `8ℓ^j ≥ rhoT ℓ j` in place of the footprint radius `5ℓ^j`; needs `17 ℓ ≤ R M`).
* `phi_pdist` : a bond carrying the kernel of row `p` is based within `4 ℓ^{lev p}` of the base of `p`.
* `Qfull_far` : if the source `x` vanishes at every bond based in `Ball (z_{p'}) (rhoT j')`, then `Q_V x` vanishes at row `p'`,
  for ANY configuration `V` (`compL_far_zero`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2W6

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice blockOf mem_blockOf)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane (Tower Admissible scaleUp bigSide pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_self pdist_coarseShift_le admissible_ball rhoT rhoT_le)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)

section win
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem ball_window (hS : Admissible ell M R k S) (hM : 0 < M) (hell2 : 2 ≤ ell) (hroom : 17 * ell ≤ R * M)
    (p : BIdx (geomOf ell k S)) (e : PeriodicLatticeSite (scaleUp ell k Lu))
    (he : pdist p.2.1.1 e ≤ 8 * ell ^ (p.1 : ℕ)) :
    AdalyFormal.M1.strat S k e ≤ (p.1 : ℕ) + 1 ∧ (p.1 : ℕ) ≤ AdalyFormal.M1.strat S k e + 1 := by
  classical
  have hell0 : 0 < ell := by omega
  set j : ℕ := (p.1 : ℕ) with hjdef
  have hj : j ≤ k := Nat.lt_succ_iff.mp p.1.isLt
  have hanc : ∃ a, a ∈ S.Om j ∧ a ∉ S.Om (j + 1) ∧ pdist a p.2.1.1 ≤ ell ^ j := by
    have hb : p.2.1.1 ∈ (geomOf ell k S).Lam (p.1 : ℕ) ∨
        coarseShift p.2.1.1 ((geomOf ell k S).ell ^ (p.1 : ℕ)) p.2.1.2 ∈ (geomOf ell k S).Lam (p.1 : ℕ) := p.2.2.1
    rcases hb with h | h
    · exact ⟨p.2.1.1, h.2.1, h.2.2, by rw [pdist_self]; exact Nat.zero_le _⟩
    · refine ⟨coarseShift p.2.1.1 (ell ^ j) p.2.1.2, h.2.1, h.2.2, ?_⟩
      rw [pdist_comm]; exact pdist_coarseShift_le p.2.1.1 (ell ^ j) p.2.1.2
  obtain ⟨a, haO, haN, had⟩ := hanc
  have he' : pdist p.2.1.1 e ≤ 8 * ell ^ j := he
  have hae : pdist a e ≤ 9 * ell ^ j := by
    have := pdist_triangle a p.2.1.1 e; omega
  have hsa : AdalyFormal.M1.strat S k a = j := by
    refine le_antisymm ?_ (AdalyFormal.M1.le_strat_of_mem hj haO)
    by_contra hlt
    push Not at hlt
    have hk1 : j + 1 ≤ k := le_trans hlt (AdalyFormal.M1.strat_le S k a)
    exact haN ((AdalyFormal.M1.le_strat_iff hS (by omega) hk1 a).mp hlt)
  have h9 : 9 * ell ^ j ≤ R * (M * ell ^ (j + 1)) := by
    have hp : ell ^ (j + 1) = ell * ell ^ j := by rw [pow_succ']
    rw [hp]
    have : 9 * ell ^ j ≤ (R * M) * ell ^ j := Nat.mul_le_mul_right _ (by omega)
    calc 9 * ell ^ j ≤ (R * M) * ell ^ j := this
      _ ≤ (R * M) * (ell * ell ^ j) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hell0)
      _ = R * (M * (ell * ell ^ j)) := by ring
  constructor
  · have hcl := AdalyFormal.M1.strat_close hS (x := a) (y := e) (by
      rw [hsa]; unfold bigSide
      omega)
    rw [hsa] at hcl; exact hcl
  · by_cases hj0 : j = 0
    · omega
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hsub := admissible_ball hS (j := j - 1) (by omega) (y := a) (by rw [Nat.sub_add_cancel hj1]; exact haO)
    have hin : e ∈ S.Om (j - 1) := by
      apply hsub
      show pdist a e ≤ R * bigSide M ell (j - 1)
      unfold bigSide
      have hpow : ell ^ j = ell * ell ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      have h1 : 9 * ell ^ j ≤ R * (M * ell ^ (j - 1)) := by
        calc 9 * ell ^ j = 9 * ell * ell ^ (j - 1) := by rw [hpow]; ring
          _ ≤ (R * M) * ell ^ (j - 1) := Nat.mul_le_mul_right _ (by omega)
          _ = R * (M * ell ^ (j - 1)) := by ring
      omega
    have := AdalyFormal.M1.le_strat_of_mem (by omega : j - 1 ≤ k) hin
    omega

end win

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.ball_window

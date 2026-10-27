import UA4
import FE4b

/-!
# UA5 -- properties of `C B̃ = Cop Λ Q B̃` for a GENERAL unit-level `Q` (lane m2_unit_20261014)

FE4b `Cop_props_gen` is stated for the flat `q1SU2`; its proof uses the flat `Q` only in the non-touching rows.
`Cop_props_Q`, for any linear `Q` with `H₀(Q)` bijective:
 (i) `C B̃` vanishes on every staircase; (ii) on every coarse bond `c`: `Q (C B̃) c = 0` (rows touching `Λ'`, `Cop_ker`) OR
 `C B̃` vanishes on every bond the FLAT row `q₁(c)` reads (rows not touching `Λ'`); (iii) `‖B̃‖² ≤ ‖C B̃‖²`;
 (iv) `C B̃` is supported on bonds touching `Λ`.
This is exactly the input shape of UA4 `cov_floor_ims` with `Q = Q1jet ℓ W`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.M2Unit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_mem_staircase
  droppedBondLast_not_reads)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.QOne (pathSite)

theorem Cop_props_Q {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell : 0 < ell) (hd : ∀ μ, ell ∣ Lu μ + 1) (hu : ∀ μ, 1 ≤ Lu μ)
    {Lam : Set (PeriodicLatticeSite Lu)} (hLB : LamBlockSum ell Lam)
    (Q : (Bond Lu → SuTwo) →ₗ[ℝ] (CoarseBond Lu ell → SuTwo))
    (hb : Function.Bijective (H0 Lam Q)) (Bt : Bond Lu → SuTwo)
    (hBt : OnLambdaTildeIn Lam ell Bt) (hBT : OnLambdaT Lam Bt) :
    (∀ y ∈ CoarseLattice Lu ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, Cop Lam Q Bt b = 0) ∧
    (∀ c : CoarseBond Lu ell, Q (Cop Lam Q Bt) c = 0 ∨
      ∀ x ∈ blockOf c.1.1 ell, ∀ j ∈ Finset.range ell, Cop Lam Q Bt (pathSite x c.2 j, c.2) = 0) ∧
    bondEnergy Bt ≤ ∑ b : Bond Lu, ‖Cop Lam Q Bt b‖ ^ 2 ∧
    (∀ e : Bond Lu, Cop Lam Q Bt e ≠ 0 → e.1 ∈ Lam ∨ periodicLatticeShift e.1 e.2 ∈ Lam) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy x hx b hbst
    have hnd : ¬ IsDroppedIn Lam ell b := by
      rintro ⟨c, -, rfl⟩
      exact droppedBondLast_not_mem_staircase hell hd c y hy x hx hbst
    rw [Cop_id _ _ Bt b hnd]
    by_cases hLP : y ∈ LamPrime ell Lam
    · exact hBt.1 y hLP x hx b hbst
    · apply hBT b
      rintro (h | h)
      · exact hLP (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hy
          (AdalyFormal.FlatEllGeneral.stair_in_block hell hu hd hy hx hbst).1 h)
      · exact hLP (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hy
          (AdalyFormal.FlatEllGeneral.stair_in_block hell hu hd hy hx hbst).2 h)
  · intro c
    by_cases hc : CRowIn ell Lam c
    · exact Or.inl (Cop_ker Lam Q hb Bt c hc)
    · right
      have hread : ∀ b : Bond Lu, ReadsBond ell c b → Cop Lam Q Bt b = 0 := by
        intro b hbr
        have hnd : ¬ IsDroppedIn Lam ell b := by
          rintro ⟨c', hc', rfl⟩
          by_cases hcc : c = c'
          · subst hcc; exact hc hc'
          · exact droppedBondLast_not_reads hell hd c c' hcc hbr
        rw [Cop_id _ _ Bt b hnd]
        apply hBT b
        have hrb := AdalyFormal.FlatEllGeneral.reads_in_blocks hell hd c b hbr
        have hcm : c.1.1 ∈ CoarseLattice Lu ell := c.1.2
        have hcp : coarseShift c.1.1 ell c.2 ∈ CoarseLattice Lu ell := coarseShift_mem_coarseLattice hd c.1.2 c.2
        rintro (h | h)
        · rcases hrb.1 with h1 | h1
          · exact hc (Or.inl (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hcm h1 h))
          · exact hc (Or.inr (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hcp h1 h))
        · rcases hrb.2 with h1 | h1
          · exact hc (Or.inl (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hcm h1 h))
          · exact hc (Or.inr (AdalyFormal.FlatEllGeneral.lamPrime_of_mem hLB hcp h1 h))
      intro x hx j hj
      exact hread _ ⟨x, hx, j, hj, rfl⟩
  · unfold bondEnergy
    refine Finset.sum_le_sum (fun b _ => ?_)
    by_cases hd' : IsDroppedIn Lam ell b
    · rw [hBt.2 b hd']; simp
    · rw [Cop_id _ _ Bt b hd']
  · intro e he
    by_cases hdr : IsDroppedIn Lam ell e
    · exact dropped_touches_lam hell hd hdr
    · rw [Cop_id Lam Q Bt e hdr] at he
      by_contra hnt
      exact he (hBT e hnt)

end AdalyFormal.M2Unit

#print axioms AdalyFormal.M2Unit.Cop_props_Q

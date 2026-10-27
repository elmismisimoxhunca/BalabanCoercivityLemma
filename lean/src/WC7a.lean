import WC5

/-!
# WC7a -- `source_bounds`: the F- and G-bounds for the flat kernel of ONE row in a regional chart (M2 W6 lane)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2W6

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6
open AdalyFormal.TowerLoc

section sb
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

open Classical in
/-- the sum of per-level bounds over at most three levels -/
theorem levels_sum (k s : ℕ) (f : Fin (k + 1) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ j : Fin (k + 1), f j ≤ if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then c else 0) :
    ∑ j, f j ≤ 3 * c := by
  calc ∑ j, f j ≤ ∑ j : Fin (k + 1), (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then c else 0) :=
        Finset.sum_le_sum (fun j _ => hf j)
    _ = c * ∑ j : Fin (k + 1), (if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ s + 1 then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs <;> simp
    _ ≤ c * 3 := mul_le_mul_of_nonneg_left (AdalyFormal.M1IMS.levels_le_three k s) hc
    _ = 3 * c := by ring

open Classical in
/-- **F- and G-bounds for the kernel of one row `p`**, with the background near the identity only on the ball
`Ball z_p (20 ℓ^{lev p + 1})` (regional class `ε j' l` for the rows of the three interacting levels `j'`). -/
theorem source_bounds (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hroom : 17 * ell ≤ R * M)
    (V : Cfg (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (ε : ℕ → ℕ → ℝ)
    (hcl : ∀ j' : ℕ, (p.1 : ℕ) ≤ j' + 1 → j' ≤ (p.1 : ℕ) + 1 → ∀ l, l < k → l < j' →
      ∀ z ∈ Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)), z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
        frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε j' l)
    (hε0 : ∀ j' l, l < k → 0 ≤ ε j' l) (hsm : ∀ j' l, l < k → rhoOf ell (ε j' l) < Real.pi / 2)
    (hr : ∀ j' l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j' l) < r0)
    (Sstar : ℝ) (hSstar : ∀ j' : ℕ, j' ≤ k → ∑ l ∈ range j', thetaOf ell (ε j' l) ≤ Sstar) (w : SuTwo) :
    W6.nF ((bondSectorOf (geomOf ell k S) V).Qfull (psiL (by omega : 0 < ell) p w)
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull (psiL (by omega : 0 < ell) p w))
      ≤ 3 * delStar ell Sstar ^ 2 * ‖psiL (by omega : 0 < ell) p w‖ ^ 2 ∧
    W6.nF ((bondSectorOf (geomOf ell k S) V).Qfull (psiL (by omega : 0 < ell) p w))
      ≤ 3 * (Real.exp (Sstar / rr ell)) ^ 2 * ‖psiL (by omega : 0 < ell) p w‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hr0 := rr_pos hell
  set ψ := psiL hell p w with hψ
  -- Sstar is nonnegative when there is a level with θ-sum (use j'=0: the empty sum)
  have hS0 : 0 ≤ Sstar := by
    have := hSstar 0 (Nat.zero_le _)
    simpa using this
  have hwin : ∀ j : Fin (k + 1), ¬ ((p.1 : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ (p.1 : ℕ) + 1) →
      ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ¬ Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p := by
    intro j hj r hI
    exact hj ⟨hI.2.1, hI.1⟩
  -- per-level, rows in `Inter`
  have hlev : ∀ j : Fin (k + 1), ((p.1 : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ (p.1 : ℕ) + 1) →
      (∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p then wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull ψ ⟨j, r⟩‖ ^ 2 else 0)
        ≤ (Real.exp (Sstar / rr ell)) ^ 2 * ‖ψ‖ ^ 2) ∧
      (∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p then wF (⟨j, r⟩ : BIdx (geomOf ell k S))
          * ‖(bondSectorOf (geomOf ell k S) V).Qfull ψ ⟨j, r⟩
              - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull ψ ⟨j, r⟩‖ ^ 2 else 0)
        ≤ delStar ell Sstar ^ 2 * ‖ψ‖ ^ 2) := by
    intro j hj
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    have h := level_FG_src hell V (fun p' => Inter p' p) (ε j)
      (fun l => if l < (j : ℕ) then Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)) else ∅)
      (fun l hl z hz hza μ => by
        by_cases hlj : l < (j : ℕ)
        · rw [if_pos hlj] at hz; exact hcl (j : ℕ) hj.1 hj.2 l hl hlj z hz hza μ
        · rw [if_neg hlj] at hz; exact absurd hz (Set.notMem_empty _))
      (fun l hl => hε0 _ l hl) (fun l hl => hsm _ l hl) (fun l hl => hr _ l hl) j
      (by
        intro r hI l hl z hz
        -- `z` is within `rhoT j - rhoT l ≤ 8 ℓ^j` of the row base, which is within `8ℓ^j + 4ℓ^{lev p}` of `z_p`
        have h1 : pdist r.1.1 z ≤ rhoT ell (j : ℕ) - rhoT ell l := hz
        have h2 : rhoT ell (j : ℕ) + 8 ≤ 8 * ell ^ (j : ℕ) := rhoT_le ell hell2 _
        have h3 := hI.2.2
        have h4 := pdist_triangle p.2.1.1 r.1.1 z
        rw [pdist_comm p.2.1.1 r.1.1] at h4
        have h5 : ell ^ (j : ℕ) ≤ ell * ell ^ (p.1 : ℕ) := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right hell (by have := hj.2; omega)
        have h6 : ell ^ (p.1 : ℕ) ≤ ell ^ ((p.1 : ℕ) + 1) := Nat.pow_le_pow_right hell (by omega)
        have h7 : ell ^ ((p.1 : ℕ) + 1) = ell * ell ^ (p.1 : ℕ) := by rw [pow_succ']
        show z ∈ (if l < (j : ℕ) then Ball p.2.1.1 (20 * ell ^ ((p.1 : ℕ) + 1)) else ∅)
        rw [if_pos hl]
        show pdist p.2.1.1 z ≤ 20 * ell ^ ((p.1 : ℕ) + 1)
        have : (pdist r.1.1 z : ℕ) ≤ 8 * ell ^ (j : ℕ) := by omega
        nlinarith [h4, h3, this, h5, h6, h7])
      ψ
    have hjS : ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) ≤ Sstar := hSstar (j : ℕ) hjk
    have hdel : delLoc ell (ε j) j ≤ delStar ell Sstar := by
      have h0 : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
        Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
      have h1 : (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell ≤ Sstar / rr ell :=
        div_le_div_of_nonneg_right hjS hr0.le
      have h2 : 0 ≤ (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell := div_nonneg h0 hr0.le
      unfold delLoc delStar
      exact mul_le_mul h1 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (le_trans h2 h1)
    have hdel0 : 0 ≤ delLoc ell (ε j) j := by
      have h0 : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
        Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
      unfold delLoc
      exact mul_nonneg (div_nonneg h0 hr0.le) (Real.exp_pos _).le
    have hexp : Real.exp ((∑ i ∈ Finset.range (j : ℕ), thetaOf ell (ε j i)) / rr ell) ≤ Real.exp (Sstar / rr ell) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hjS hr0.le)
    refine ⟨h.1.trans ?_, h.2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hexp 2) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdel0 hdel 2) (sq_nonneg _)
  -- assemble: `nF z = Σ_j Σ_r`, rows outside `Inter` vanish
  have hnF : ∀ z : FSp (geomOf ell k S), (∀ p' : BIdx (geomOf ell k S), ¬ Inter p' p → z p' = 0) →
      W6.nF z = ∑ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p then wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖z ⟨j, r⟩‖ ^ 2 else 0) := by
    intro z hz
    unfold W6.nF
    rw [Fintype.sum_sigma (fun p' : BIdx (geomOf ell k S) => wF p' * ‖z p'‖ ^ 2)]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r _ => ?_))
    split_ifs with hI
    · rfl
    · rw [hz _ hI, norm_zero]; simp
  constructor
  · have hz : ∀ p' : BIdx (geomOf ell k S), ¬ Inter p' p →
        ((bondSectorOf (geomOf ell k S) V).Qfull ψ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull ψ) p' = 0 := by
      intro p' hI
      rw [PiLp.sub_apply, Qfull_zero_of_not_inter hell2 hS hM hroom V p p' hI w,
        Qfull_zero_of_not_inter hell2 hS hM hroom (trivialU _) p p' hI w, sub_zero]
    rw [hnF _ hz]
    have hc : 0 ≤ delStar ell Sstar ^ 2 * ‖ψ‖ ^ 2 := by positivity
    have := levels_sum k (p.1 : ℕ) (fun j => ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p then wF (⟨j, r⟩ : BIdx (geomOf ell k S)) *
          ‖((bondSectorOf (geomOf ell k S) V).Qfull ψ - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull ψ) ⟨j, r⟩‖ ^ 2
          else 0)) (delStar ell Sstar ^ 2 * ‖ψ‖ ^ 2) hc (fun j => by
        by_cases hj : (p.1 : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ (p.1 : ℕ) + 1
        · rw [if_pos hj]
          have := (hlev j hj).2
          simpa only [PiLp.sub_apply] using this
        · rw [if_neg hj]
          refine le_of_eq (Finset.sum_eq_zero (fun r _ => ?_))
          rw [if_neg (hwin j hj r)])
    calc _ ≤ 3 * (delStar ell Sstar ^ 2 * ‖ψ‖ ^ 2) := this
      _ = _ := by ring
  · have hz : ∀ p' : BIdx (geomOf ell k S), ¬ Inter p' p → ((bondSectorOf (geomOf ell k S) V).Qfull ψ) p' = 0 := by
      intro p' hI
      exact Qfull_zero_of_not_inter hell2 hS hM hroom V p p' hI w
    rw [hnF _ hz]
    have hc : 0 ≤ (Real.exp (Sstar / rr ell)) ^ 2 * ‖ψ‖ ^ 2 := by positivity
    have := levels_sum k (p.1 : ℕ) (fun j => ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        (if Inter (⟨j, r⟩ : BIdx (geomOf ell k S)) p then wF (⟨j, r⟩ : BIdx (geomOf ell k S)) *
          ‖((bondSectorOf (geomOf ell k S) V).Qfull ψ) ⟨j, r⟩‖ ^ 2 else 0))
        ((Real.exp (Sstar / rr ell)) ^ 2 * ‖ψ‖ ^ 2) hc (fun j => by
        by_cases hj : (p.1 : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ (p.1 : ℕ) + 1
        · rw [if_pos hj]
          exact (hlev j hj).1
        · rw [if_neg hj]
          refine le_of_eq (Finset.sum_eq_zero (fun r _ => ?_))
          rw [if_neg (hwin j hj r)])
    calc _ ≤ 3 * ((Real.exp (Sstar / rr ell)) ^ 2 * ‖ψ‖ ^ 2) := this
      _ = _ := by ring

end sb

end AdalyFormal.M2W6

#print axioms AdalyFormal.M2W6.level_FG_src
#print axioms AdalyFormal.M2W6.source_bounds

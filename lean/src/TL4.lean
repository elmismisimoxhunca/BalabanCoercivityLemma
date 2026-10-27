import TL3
import W6I

/-!
# TL4 -- `drift_F_loc` (the `hD` form of W6I `qs_injective_of_drift`, `D = 3 δ*²`) and `qs_injective_loc`

Level `j` has its OWN regional data `(ε j l, W j l)`; the only global input is a bound `S*` on the level sums
`S_j = Σ_{l<j} θ(ε j l)` (the `k`-free quantity).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.TowerLoc

open Finset
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.NonflatJet
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp)
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.SliceCoerc (GF)
open AdalyFormal.DLayer (Foot bondRestr)
open AdalyFormal.BondComposite
open SmallnessBridge.Assemble (loopFactorBound)
open AdalyFormal.W6

/-- the `k`-free drift constant `δ* = (S*/r) e^{S*/r}` -/
def delStar (ell : ℕ) (Sstar : ℝ) : ℝ := (Sstar / rr ell) * Real.exp (Sstar / rr ell)

section drift
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

/-- **drift in the row-normalised norm, region-restricted classes, `D = 3 δ*²` independent of `k`** -/
theorem drift_F_loc (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M) (hR : 8 * ell ≤ R)
    (V : Cfg (scaleUp ell k Lu)) (ε : ℕ → ℕ → ℝ) (W : ℕ → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ j : Fin (k + 1), ∀ l, l < k → ∀ z ∈ W j l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) V l (z, μ) : SU2) : M2) - 1) ≤ ε j l)
    (hε0 : ∀ j : Fin (k + 1), ∀ l, l < k → 0 ≤ ε j l)
    (hsm : ∀ j : Fin (k + 1), ∀ l, l < k → rhoOf ell (ε j l) < Real.pi / 2)
    (hr : ∀ j : Fin (k + 1), ∀ l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j l) < r0)
    (hW : ∀ j : Fin (k + 1),
      ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ∀ l, l < (j : ℕ) →
        Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W j l)
    (Sstar : ℝ) (hSstar : ∀ j : Fin (k + 1), ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) ≤ Sstar)
    (x : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, wF p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
        - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2
      ≤ 3 * delStar ell Sstar ^ 2 * ‖x‖ ^ 2 := by
  have hell : 0 < ell := by omega
  have hr0 := rr_pos hell
  rw [Fintype.sum_sigma (fun p : BIdx (geomOf ell k S) => wF p * ‖(bondSectorOf (geomOf ell k S) V).Qfull x p
      - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x p‖ ^ 2)]
  have hdel : ∀ j : Fin (k + 1), delLoc ell (ε j) j ≤ delStar ell Sstar := by
    intro j
    have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
    have h0 : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
      Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
    have h1 : (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell ≤ Sstar / rr ell :=
      div_le_div_of_nonneg_right (hSstar j) hr0.le
    have h2 : 0 ≤ (∑ l ∈ range (j : ℕ), thetaOf ell (ε j l)) / rr ell := div_nonneg h0 hr0.le
    unfold delLoc delStar
    exact mul_le_mul h1 (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (le_trans h2 h1)
  calc ∑ j : Fin (k + 1), ∑ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j},
        wF (⟨j, r⟩ : BIdx (geomOf ell k S)) * ‖(bondSectorOf (geomOf ell k S) V).Qfull x ⟨j, r⟩
          - (bondSectorOf (geomOf ell k S) (trivialU _)).Qfull x ⟨j, r⟩‖ ^ 2
      ≤ ∑ j : Fin (k + 1), delStar ell Sstar ^ 2 * ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hd := level_drift_loc (S := S) hell V (ε j) (W j) (hcl j) (hε0 j) (hsm j) (hr j) j (hW j) x
        refine hd.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        have h0 : 0 ≤ delLoc ell (ε j) j := by
          have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
          have : 0 ≤ ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) :=
            Finset.sum_nonneg (fun l hl => thetaOf_nonneg ell _ (hε0 j l (lt_of_lt_of_le (Finset.mem_range.mp hl) hjk)))
          unfold delLoc
          exact mul_nonneg (div_nonneg this hr0.le) (Real.exp_pos _).le
        exact pow_le_pow_left₀ h0 (hdel j) 2
    _ = delStar ell Sstar ^ 2 * ∑ j : Fin (k + 1), ‖bondRestr (FootL (S := S) j) x‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ delStar ell Sstar ^ 2 * (3 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (foot_levels hell2 hS hM hR x) (sq_nonneg _)
    _ = 3 * delStar ell Sstar ^ 2 * ‖x‖ ^ 2 := by ring

/-- **W6 injectivity from region-restricted classes**: `qs_injective_of_drift` with `D = 3 δ*²`. -/
theorem qs_injective_loc (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 0 < M)
    (hR : 8 * ell ≤ R) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (ε : ℕ → ℕ → ℝ) (W : ℕ → ℕ → Set (PeriodicLatticeSite (scaleUp ell k Lu)))
    (hcl : ∀ j : Fin (k + 1), ∀ l, l < k → ∀ z ∈ W j l, z ∈ CoarseLattice (scaleUp ell k Lu) (ell ^ l) → ∀ μ : Fin 3,
      frobNorm (((bgTower (GF ell k Lu) U l (z, μ) : SU2) : M2) - 1) ≤ ε j l)
    (hε0 : ∀ j : Fin (k + 1), ∀ l, l < k → 0 ≤ ε j l)
    (hsm : ∀ j : Fin (k + 1), ∀ l, l < k → rhoOf ell (ε j l) < Real.pi / 2)
    (hr : ∀ j : Fin (k + 1), ∀ l, l < k → Real.pi / 2 * ((loopFactorBound ell : ℝ) * ε j l) < r0)
    (hW : ∀ j : Fin (k + 1),
      ∀ r : {b : Bond (scaleUp ell k Lu) // b ∈ bondsLam (geomOf ell k S) j}, ∀ l, l < (j : ℕ) →
        Ball r.1.1 (rhoT ell j - rhoT ell l) ⊆ W j l)
    (Sstar : ℝ) (hSstar : ∀ j : Fin (k + 1), ∑ l ∈ range (j : ℕ), thetaOf ell (ε j l) ≤ Sstar)
    (hsmall : 3 * delStar ell Sstar ^ 2 * CEp < 1) :
    Function.Injective (gparams ell k Lu hell S U a Lam).data.Qs :=
  qs_injective_of_drift hell hell2 hS hM hR U a Lam (3 * delStar ell Sstar ^ 2)
    (fun x => drift_F_loc hell2 hS hM hR U ε W hcl hε0 hsm hr hW Sstar hSstar x) hsmall

end drift

end AdalyFormal.TowerLoc

#print axioms AdalyFormal.TowerLoc.drift_F_loc
#print axioms AdalyFormal.TowerLoc.qs_injective_loc

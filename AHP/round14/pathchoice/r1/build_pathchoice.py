#!/usr/bin/env python3
"""Assemble the compact weighted-star path file from the frozen round-13 prefix."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
source=ROOT/'AHP/round13/shared/trial/R1_Trial.lean'
prefix=source.read_text().splitlines()[:693]
assert len(prefix)==693
assert 'def rightStar' in '\n'.join(prefix)
append=r'''

/-! Round 14 path-choice infrastructure.  The arm weights are arbitrary real
numbers.  Only the pi-endpoint P1 input is asserted for signed arms; the
half-pi P1 input, P2, kernel line and detection are deliberately not claimed. -/
namespace AdalyFormal.Round14.PathChoice
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
open AdalyFormal.Round12.Noncancel.Path
variable {L : PeriodicLatticeExtent}

open Classical in
/-- Same exterior support as `starPath`, with an independent real angle
coefficient on every arm.  The numerical screen uses this common family. -/
def weightedStarPath (x : PeriodicLatticeSite L) (c : Bond L → ℝ) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ (c e * t) else 1

theorem weightedStarPath_zero (x : PeriodicLatticeSite L) (c : Bond L → ℝ) :
    weightedStarPath x c 0 = fun _ => 1 := by
  funext e
  simp [weightedStarPath, uθ_zero]

theorem weightedStarPath_cont (x : PeriodicLatticeSite L) (c : Bond L → ℝ) :
    ContFam (weightedStarPath x c) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [weightedStarPath, h, if_true]
    change Continuous fun t => uMat (c e * t)
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [weightedStarPath, h, if_false]
    exact continuous_const

theorem weightedStarPath_an (x : PeriodicLatticeSite L) (c : Bond L → ℝ) :
    AnFam (weightedStarPath x c) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [weightedStarPath, h, if_true]
    show AnM fun t => uMat (c e * t)
    intro t₀ i j
    have hlin : AnalyticAt ℝ (fun t : ℝ => c e * t) t₀ := by fun_prop
    exact (anM_uMat (c e * t₀) i j).comp hlin
  · intro t i j
    simp only [weightedStarPath, h, if_false]
    exact analyticAt_const

theorem weightedStarPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (c : Bond L → ℝ) (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) :
    weightedStarPath x c t e = 1 := by
  have hh : e ∉ starLinks x := fun h => he (starLinks_exterior Om x hx htrans h)
  simp [weightedStarPath, hh]

/-- A signed arm has the same pi-endpoint configuration as the original star. -/
theorem uθ_neg_pi : uθ (-Real.pi) = uθ Real.pi := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uθ, uMat, Complex.exp_pi_mul_I, Complex.exp_neg]

theorem weightedStarPath_pi_of_sign (x : PeriodicLatticeSite L) (c : Bond L → ℝ)
    (hc : ∀ e ∈ starLinks x, c e = 1 ∨ c e = -1) :
    weightedStarPath x c Real.pi = starPath x Real.pi := by
  funext e
  by_cases he : e ∈ starLinks x
  · simp only [weightedStarPath, starPath, he, if_true]
    rcases hc e he with h | h
    · rw [h, one_mul]
    · rw [h, neg_one_mul, uθ_neg_pi]
  · simp [weightedStarPath, starPath, he]

/-- The right-placed weighted family used in the path-choice screen. -/
def weightedRightStar {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  weightedStarPath (periodicLatticeShift (rightSite hq R) 0) c

theorem weightedRightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    weightedRightStar hq R c 0 = fun _ => 1 := weightedStarPath_zero _ _

theorem weightedRightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFam (weightedRightStar hq R c) := weightedStarPath_cont _ _

theorem weightedRightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnFam (weightedRightStar hq R c) := weightedStarPath_an _ _

theorem weightedRightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ Zb ((dilTower q R).Om 0)) : weightedRightStar hq R c t e = 1 :=
  weightedStarPath_off_exterior _ _ (rightSite_bd hq R).hx'
    (rightSite_bd hq R).trans c t e he

theorem pathU_weightedRightStar {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (weightedRightStar hq R c) f 0 t = weightedRightStar hq R c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [pathU, maskedU, he]
  · rw [weightedRightStar_off_exterior hq R c t e he]
    simp [pathU, maskedU, he, Ug_zero]

theorem dilU_weightedRightStar {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    dilU q R 0 (weightedRightStar hq R c t) = weightedRightStar hq R c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [dilU, he]
  · rw [weightedRightStar_off_exterior hq R c t e he]
    simp [dilU, he, Ug_zero]

theorem vacA_weightedRightStar {q : ℕ} (hq : 0 < q) (R : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    vacA q R (weightedRightStar hq R c) a t =
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (weightedRightStar hq R c t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_weightedRightStar]
  rfl

/-- Only the old pi-endpoint input, not the stronger half-pi P1 used by the
round-13 first-crossing proof. -/
theorem weightedRightStar_negative_pi {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hc : ∀ e ∈ starLinks (periodicLatticeShift (rightSite hq R) 0),
      c e = 1 ∨ c e = -1) :
    ∃ w, ⟪w, vacA q R (weightedRightStar hq R c) 1 Real.pi w⟫ < 0 := by
  rw [vacA_weightedRightStar]
  unfold weightedRightStar
  rw [weightedStarPath_pi_of_sign _ c hc]
  exact star_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero

#print axioms weightedStarPath
#print axioms weightedStarPath_zero
#print axioms weightedStarPath_cont
#print axioms weightedStarPath_an
#print axioms weightedStarPath_off_exterior
#print axioms uθ_neg_pi
#print axioms weightedStarPath_pi_of_sign
#print axioms weightedRightStar
#print axioms weightedRightStar_zero
#print axioms weightedRightStar_cont
#print axioms weightedRightStar_an
#print axioms weightedRightStar_off_exterior
#print axioms pathU_weightedRightStar
#print axioms dilU_weightedRightStar
#print axioms vacA_weightedRightStar
#print axioms weightedRightStar_negative_pi
#check @weightedRightStar_negative_pi
end AdalyFormal.Round14.PathChoice
'''
text='\n'.join(prefix)+append
local=ROOT/'AHP/round14/pathchoice/r1/PathChoice.lean'
shared=ROOT/'AHP/round14/shared/pathchoice/R1_WeightedStar.lean'
local.parent.mkdir(parents=True,exist_ok=True);shared.parent.mkdir(parents=True,exist_ok=True)
local.write_text(text);shared.write_text(text)
print(local);print(shared);print('lines',len(text.splitlines()))

#!/usr/bin/env python3
"""Build the finite-arm path and conditional detection interface."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
base=ROOT/'AHP/round14/transfer/r1/Generator.lean'
text=base.read_text()
assert 'theorem cofinalP3_of_laurentAreaSeed' in text
append=r'''

/-! Round 14, path choice R2: finite alternating arms and their area interface. -/
namespace AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2

/-- Coordinate formula needed to place every finite arm on the right boundary. -/
theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]

#print axioms dil_shift_zero
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega

#print axioms rightSite_bd
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀

def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin

theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

#print axioms AnM
#print axioms AnFam
#print axioms analyticAt_exp_I
#print axioms anM_uMat
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round14.PathChoice
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round13.Detection.PhysicalArea
open AdalyFormal.Round12.Kernel.ResponseActual
variable {L : PeriodicLatticeExtent}

/-- Forward iteration of a transverse lattice shift. -/
def shiftN (x : PeriodicLatticeSite L) (μ : Fin 3) : ℕ → PeriodicLatticeSite L
  | 0 => x
  | n+1 => periodicLatticeShift (shiftN x μ n) μ

/-- Backward iteration of a transverse lattice shift. -/
def backN (x : PeriodicLatticeSite L) (μ : Fin 3) : ℕ → PeriodicLatticeSite L
  | 0 => x
  | n+1 => periodicLatticeShiftBack (backN x μ n) μ

theorem shiftN_mem_iff (Om : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : shiftN x μ n ∈ Om ↔ x ∈ Om := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change periodicLatticeShift (shiftN x μ n) μ ∈ Om ↔ x ∈ Om
      rw [htrans _ _ hμ, ih]

theorem backN_mem_iff (Om : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : backN x μ n ∈ Om ↔ x ∈ Om := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change periodicLatticeShiftBack (backN x μ n) μ ∈ Om ↔ x ∈ Om
      have h := htrans (periodicLatticeShiftBack (backN x μ n) μ) μ hμ
      rw [periodicLatticeShift_shiftBack] at h
      exact h.symm.trans ih

/-- The forward bond at level `n`, and the backward bond at level `n+1`. -/
def forwardBond (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Bond L :=
  (shiftN x μ n, μ)

def backwardBond (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Bond L :=
  (backN x μ n, μ)

/-- The two transverse bonds added at one arm level. -/
def armLevel (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Set (Bond L) :=
  {forwardBond x μ n, backwardBond x μ (n+1)}

/-- All transverse bonds on both arms through level `N-1`.  Level zero is the
original four-bond star; each further level adds four bonds. -/
def longStarLinks (x : PeriodicLatticeSite L) (N : ℕ) : Set (Bond L) :=
  {e | ∃ μ : Fin 3, μ ≠ 0 ∧ ∃ n : ℕ, n < N ∧ e ∈ armLevel x μ n}

theorem forwardBond_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : forwardBond x μ n ∈ Zb Om := by
  constructor
  · exact fun h => hx ((shiftN_mem_iff Om x htrans μ hμ n).mp h)
  · change periodicLatticeShift (shiftN x μ n) μ ∉ Om
    exact fun h => hx ((shiftN_mem_iff Om x htrans μ hμ (n+1)).mp h)

theorem backwardBond_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : backwardBond x μ (n+1) ∈ Zb Om := by
  constructor
  · exact fun h => hx ((backN_mem_iff Om x htrans μ hμ (n+1)).mp h)
  · change periodicLatticeShift (periodicLatticeShiftBack (backN x μ n) μ) μ ∉ Om
    rw [periodicLatticeShift_shiftBack]
    exact fun h => hx ((backN_mem_iff Om x htrans μ hμ n).mp h)

theorem longStarLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (N : ℕ) : longStarLinks x N ⊆ Zb Om := by
  rintro e ⟨μ,hμ,n,hn,he⟩
  change e = forwardBond x μ n ∨ e = backwardBond x μ (n+1) at he
  rcases he with rfl | rfl
  · exact forwardBond_exterior Om x hx htrans μ hμ n
  · exact backwardBond_exterior Om x hx htrans μ hμ n

open Classical in
/-- Independent real angle coefficients on a finite two-sided transverse star. -/
def longStarPath (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) (t : ℝ) : Cfg L :=
  fun e => if e ∈ longStarLinks x N then uθ (c e * t) else 1

theorem longStarPath_zero (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    longStarPath x N c 0 = fun _ => 1 := by
  funext e
  simp [longStarPath, uθ_zero]

theorem longStarPath_cont (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    ContFam (longStarPath x N c) := by
  intro e
  by_cases h : e ∈ longStarLinks x N
  · simp only [longStarPath, h, if_true]
    change Continuous fun t => uMat (c e * t)
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [longStarPath, h, if_false]
    exact continuous_const

theorem longStarPath_an (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    AnFam (longStarPath x N c) := by
  intro e
  by_cases h : e ∈ longStarLinks x N
  · simp only [longStarPath, h, if_true]
    show AnM fun t => uMat (c e * t)
    intro t₀ i j
    have hlin : AnalyticAt ℝ (fun t : ℝ => c e * t) t₀ := by fun_prop
    exact (anM_uMat (c e * t₀) i j).comp hlin
  · intro t i j
    simp only [longStarPath, h, if_false]
    exact analyticAt_const

theorem longStarPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (N : ℕ) (c : Bond L → ℝ) (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) :
    longStarPath x N c t e = 1 := by
  have hh : e ∉ longStarLinks x N := fun h => he (longStarLinks_exterior Om x hx htrans N h)
  simp [longStarPath, hh]

theorem longStarPath_fixed (x : PeriodicLatticeSite L) (N : ℕ)
    (c : Bond L → ℝ) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (longStarPath x N c t) = longStarPath x N c t := by
  funext e
  change uθ α * longStarPath x N c t e * (uθ α)⁻¹ = longStarPath x N c t e
  by_cases he : e ∈ longStarLinks x N
  · simp only [longStarPath, he, if_true]
    rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
  · simp [longStarPath, he]

/-- The right-placed finite-arm family. -/
def longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  longStarPath (periodicLatticeShift (rightSite hq R) 0) N c

theorem longRightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    longRightStar hq R N c 0 = fun _ => 1 := longStarPath_zero _ _ _

theorem longRightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFam (longRightStar hq R N c) := longStarPath_cont _ _ _

theorem longRightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnFam (longRightStar hq R N c) := longStarPath_an _ _ _

theorem longRightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ Zb ((dilTower q R).Om 0)) : longRightStar hq R N c t e = 1 :=
  longStarPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans N c t e he

theorem longRightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (longRightStar hq R N c t) = longRightStar hq R N c t :=
  longStarPath_fixed _ _ _ _ _

theorem pathU_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (longRightStar hq R N c) f 0 t = longRightStar hq R N c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [pathU, maskedU, he]
  · rw [longRightStar_off_exterior hq R N c t e he]
    simp [pathU, maskedU, he, Ug_zero]

theorem dilU_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    dilU q R 0 (longRightStar hq R N c t) = longRightStar hq R N c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [dilU, he]
  · rw [longRightStar_off_exterior hq R N c t e he]
    simp [dilU, he, Ug_zero]

theorem vacA_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    vacA q R (longRightStar hq R N c) a t =
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (longRightStar hq R N c t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_longRightStar]
  rfl

open Classical in
/-- Exact coefficients used by the low-cancellation three-level path. -/
def tailCoeff (x : PeriodicLatticeSite L) (e : Bond L) : ℝ :=
  if e ∈ longStarLinks x 1 then 1
  else if e ∈ longStarLinks x 2 then -(1/4 : ℝ)
  else if e ∈ longStarLinks x 3 then -(9/4 : ℝ)
  else 0

/-- Three levels with coefficients 1, -1/4 and -9/4. -/
def tailPath (x : PeriodicLatticeSite L) : ℝ → Cfg L :=
  longStarPath x 3 (tailCoeff x)

def tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  tailPath (periodicLatticeShift (rightSite hq R) 0)

theorem tailCoeff_zero_level (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 1) : tailCoeff x e = 1 := by simp [tailCoeff, he]

theorem tailCoeff_first_extension (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 2) (hn : e ∉ longStarLinks x 1) :
    tailCoeff x e = -(1/4 : ℝ) := by simp [tailCoeff, he, hn]

theorem tailCoeff_second_extension (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 3) (hn : e ∉ longStarLinks x 2)
    (hn0 : e ∉ longStarLinks x 1) :
    tailCoeff x e = -(9/4 : ℝ) := by simp [tailCoeff, he, hn, hn0]

theorem tailPath_zero (x : PeriodicLatticeSite L) : tailPath x 0 = fun _ => 1 :=
  longStarPath_zero _ _ _

theorem tailPath_cont (x : PeriodicLatticeSite L) : ContFam (tailPath x) :=
  longStarPath_cont _ _ _

theorem tailPath_an (x : PeriodicLatticeSite L) : AnFam (tailPath x) :=
  longStarPath_an _ _ _

theorem tailPath_fixed (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (tailPath x t) = tailPath x t :=
  longStarPath_fixed _ _ _ _ _

theorem tailRightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    tailRightStar hq R 0 = fun _ => 1 := tailPath_zero _

theorem tailRightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ContFam (tailRightStar hq R) := tailPath_cont _

theorem tailRightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AnFam (tailRightStar hq R) := tailPath_an _

theorem tailRightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (tailRightStar hq R t) = tailRightStar hq R t :=
  tailPath_fixed _ _ _

theorem tailRightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ Zb ((dilTower q R).Om 0)) : tailRightStar hq R t e = 1 :=
  longRightStar_off_exterior hq R 3 (tailCoeff _) t e he

theorem pathU_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (tailRightStar hq R) f 0 t = tailRightStar hq R t :=
  pathU_longRightStar hq R 3 (tailCoeff _) t f

theorem dilU_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) :
    dilU q R 0 (tailRightStar hq R t) = tailRightStar hq R t :=
  dilU_longRightStar hq R 3 (tailCoeff _) t

theorem vacA_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (tailRightStar hq R) a t =
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (tailRightStar hq R t) a (dilLam q R))).Ginv :=
  vacA_longRightStar hq R 3 (tailCoeff _) a t

end AdalyFormal.Round14.PathChoice

namespace AdalyFormal.Round12.Kernel.Actual
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

/-- The physical charged entry, used only to state the remaining crossing input. -/
def chargedCoordinate (q R : ℕ) (b : Bond (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →ₗ[ℝ] ℂ where
  toFun u := ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  map_add' u v := rfl
  map_smul' c u := by
    change ((c : ℂ) * _) = _
    rfl

#print axioms chargedCoordinate
end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round14.PathChoice
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Round13.Detection.PhysicalArea
open AdalyFormal.Round12.Kernel.ResponseActual

/-- Negative-direction input at the original pi endpoint. -/
def TailEndpointNegative : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0

/-- Zero-coordinate positivity only at the canonical crossing, not on a whole
prefix.  This is the weaker input needed by the generalized crossing argument. -/
def TailCrossingPositive : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (x : TwistSpace q R), x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (tailRightStar hq R) 1 (vacEdge q R (tailRightStar hq R)) x⟫

/-- One area-detected whole-line generator at every admissible instance. -/
def TailAreaSeed : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
      ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0

/-- Modified-path detection; this is not the original right-star P3 predicate. -/
def TailP3 : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (u : TwistSpace q R), KernelLine q R (tailRightStar hq R) u → CurlDetected q R u

/-- One area-detected generator detects every vector on the same charged line. -/
theorem tailP3_of_areaSeed (h : TailAreaSeed) : TailP3 := by
  intro q R hq hR hR18 v hv
  obtain ⟨u,hline,j,hj,harea⟩ := h hq hR hR18
  have hu := crossing_curlDetected_of_area hq hR hR18 _ u hline ⟨j,hj,harea⟩
  exact all_kernel_detected_of_generator q R _ u hline hu v hv.2.1 hv.1

/-- Cofinal form of the same modified-path area input. -/
def CofinalTailAreaSeed : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (tailRightStar (by positivity) R) u ∧
      ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
        areaSum (by positivity : 0 < 2^j) hk u ≠ 0

/-- Cofinal modified-path detection, with the original nested quantifier order. -/
def CofinalTailP3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (tailRightStar (by positivity) R) u → CurlDetected (2^j) R u

theorem cofinalTailP3_of_areaSeed (h : CofinalTailAreaSeed) : CofinalTailP3 := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,u,hline,k,hk,harea⟩ := hRs R₀
  refine ⟨R,hR0,hR,hR18,?_⟩
  have hu := crossing_curlDetected_of_area (by positivity) hR hR18 _ u hline ⟨k,hk,harea⟩
  intro v hv
  exact all_kernel_detected_of_generator (2^j) R _ u hline hu v hv.2.1 hv.1

#print axioms shiftN
#print axioms backN
#print axioms shiftN_mem_iff
#print axioms backN_mem_iff
#print axioms forwardBond
#print axioms backwardBond
#print axioms armLevel
#print axioms longStarLinks
#print axioms forwardBond_exterior
#print axioms backwardBond_exterior
#print axioms longStarLinks_exterior
#print axioms longStarPath
#print axioms longStarPath_zero
#print axioms longStarPath_cont
#print axioms longStarPath_an
#print axioms longStarPath_off_exterior
#print axioms longStarPath_fixed
#print axioms longRightStar
#print axioms longRightStar_zero
#print axioms longRightStar_cont
#print axioms longRightStar_an
#print axioms longRightStar_off_exterior
#print axioms longRightStar_fixed
#print axioms pathU_longRightStar
#print axioms dilU_longRightStar
#print axioms vacA_longRightStar
#print axioms tailCoeff
#print axioms tailPath
#print axioms tailRightStar
#print axioms tailCoeff_zero_level
#print axioms tailCoeff_first_extension
#print axioms tailCoeff_second_extension
#print axioms tailPath_zero
#print axioms tailPath_cont
#print axioms tailPath_an
#print axioms tailPath_fixed
#print axioms tailRightStar_zero
#print axioms tailRightStar_cont
#print axioms tailRightStar_an
#print axioms tailRightStar_fixed
#print axioms tailRightStar_off_exterior
#print axioms pathU_tailRightStar
#print axioms dilU_tailRightStar
#print axioms vacA_tailRightStar
#print axioms TailEndpointNegative
#print axioms TailCrossingPositive
#print axioms TailAreaSeed
#print axioms TailP3
#print axioms tailP3_of_areaSeed
#print axioms CofinalTailAreaSeed
#print axioms CofinalTailP3
#print axioms cofinalTailP3_of_areaSeed
#check @tailP3_of_areaSeed
#check @cofinalTailP3_of_areaSeed
end AdalyFormal.Round14.PathChoice
'''
local=ROOT/'AHP/round14/pathchoice/r2/LongArm.lean'
shared=ROOT/'AHP/round14/shared/pathchoice/R2_LongArm.lean'
local.parent.mkdir(parents=True,exist_ok=True); shared.parent.mkdir(parents=True,exist_ok=True)
local.write_text(text+append); shared.write_text(text+append)
print(local); print(shared); print('lines',len((text+append).splitlines()))

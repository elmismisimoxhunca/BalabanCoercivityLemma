import NoncentralLog
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 10000
noncomputable section
namespace HConstruction.SmallNF
open HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.UbarTowerCov
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.SuTwoLogExp

def wordCount : PeriodicLatticeSite witnessL → List (Fin 3) → ℕ
  | _, [] => 0
  | y, mu::p => (if (y,mu)=(witnessY,0) then 1 else 0) +
      wordCount (AdalyFormal.Balaban.CoarseCurl.coarseShift y 1 mu) p

theorem path_word (t : ℝ) (y : PeriodicLatticeSite witnessL) (p : List (Fin 3)) :
    coarsePathHolonomy 1 (nonflatU t) y p = (rotElem t) ^ wordCount y p := by
  induction p generalizing y with
  | nil => simp [coarsePathHolonomy,wordCount]
  | cons mu p ih =>
    simp only [coarsePathHolonomy,wordCount,pow_add]
    rw [ih]
    by_cases h : (y,mu)=(witnessY,0)
    · rw [if_pos h,h,nonflatU_at_x_mu]; simp
    · rw [if_neg h,nonflatU_elsewhere _ h]; simp

def loopWord (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL) : ℤ :=
  (wordCount c.1.1 (coarseGammaPath 1 c.1.1 x) : ℤ) + wordCount x [c.2,c.2] -
    wordCount (cPlusS 1 2 (c.1.1,c.2)) (coarseGammaPath 1 c.1.1 x) -
    wordCount c.1.1 [c.2,c.2]

theorem loop_word (t : ℝ) (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL) :
    loopVar 1 2 (nonflatU t) (c.1.1,c.2) x = (rotElem t) ^ loopWord c x := by
  simp only [loopVar,gammaVarStrided,coarseBondVar,path_word,loopWord,
    zpow_sub,zpow_add,zpow_natCast]
  rfl

def coarseOutput (a b c : Fin 2) (mu : Fin 3) : CoarseBond witnessL (1*2) :=
  (⟨![2*a.castLE (by decide : 2 ≤ 4),2*b.castLE (by decide : 2 ≤ 4),2*c.castLE (by decide : 2 ≤ 4)], by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide⟩,mu)

theorem loopWord_row_000_0 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 0 0).1.1 1 2,
  loopWord (coarseOutput 0 0 0 0) x = -1 ∨ loopWord (coarseOutput 0 0 0 0) x = 0 ∨ loopWord (coarseOutput 0 0 0 0) x = 1 := by decide
theorem loopWord_row_000_1 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 0 1).1.1 1 2,
  loopWord (coarseOutput 0 0 0 1) x = -1 ∨ loopWord (coarseOutput 0 0 0 1) x = 0 ∨ loopWord (coarseOutput 0 0 0 1) x = 1 := by decide
theorem loopWord_row_000_2 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 0 2).1.1 1 2,
  loopWord (coarseOutput 0 0 0 2) x = -1 ∨ loopWord (coarseOutput 0 0 0 2) x = 0 ∨ loopWord (coarseOutput 0 0 0 2) x = 1 := by decide
theorem loopWord_row_001_0 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 1 0).1.1 1 2,
  loopWord (coarseOutput 0 0 1 0) x = -1 ∨ loopWord (coarseOutput 0 0 1 0) x = 0 ∨ loopWord (coarseOutput 0 0 1 0) x = 1 := by decide
theorem loopWord_row_001_1 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 1 1).1.1 1 2,
  loopWord (coarseOutput 0 0 1 1) x = -1 ∨ loopWord (coarseOutput 0 0 1 1) x = 0 ∨ loopWord (coarseOutput 0 0 1 1) x = 1 := by decide
theorem loopWord_row_001_2 : ∀ x ∈ stepBlockOf (coarseOutput 0 0 1 2).1.1 1 2,
  loopWord (coarseOutput 0 0 1 2) x = -1 ∨ loopWord (coarseOutput 0 0 1 2) x = 0 ∨ loopWord (coarseOutput 0 0 1 2) x = 1 := by decide
theorem loopWord_row_010_0 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 0 0).1.1 1 2,
  loopWord (coarseOutput 0 1 0 0) x = -1 ∨ loopWord (coarseOutput 0 1 0 0) x = 0 ∨ loopWord (coarseOutput 0 1 0 0) x = 1 := by decide
theorem loopWord_row_010_1 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 0 1).1.1 1 2,
  loopWord (coarseOutput 0 1 0 1) x = -1 ∨ loopWord (coarseOutput 0 1 0 1) x = 0 ∨ loopWord (coarseOutput 0 1 0 1) x = 1 := by decide
theorem loopWord_row_010_2 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 0 2).1.1 1 2,
  loopWord (coarseOutput 0 1 0 2) x = -1 ∨ loopWord (coarseOutput 0 1 0 2) x = 0 ∨ loopWord (coarseOutput 0 1 0 2) x = 1 := by decide
theorem loopWord_row_011_0 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 1 0).1.1 1 2,
  loopWord (coarseOutput 0 1 1 0) x = -1 ∨ loopWord (coarseOutput 0 1 1 0) x = 0 ∨ loopWord (coarseOutput 0 1 1 0) x = 1 := by decide
theorem loopWord_row_011_1 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 1 1).1.1 1 2,
  loopWord (coarseOutput 0 1 1 1) x = -1 ∨ loopWord (coarseOutput 0 1 1 1) x = 0 ∨ loopWord (coarseOutput 0 1 1 1) x = 1 := by decide
theorem loopWord_row_011_2 : ∀ x ∈ stepBlockOf (coarseOutput 0 1 1 2).1.1 1 2,
  loopWord (coarseOutput 0 1 1 2) x = -1 ∨ loopWord (coarseOutput 0 1 1 2) x = 0 ∨ loopWord (coarseOutput 0 1 1 2) x = 1 := by decide
theorem loopWord_row_100_0 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 0 0).1.1 1 2,
  loopWord (coarseOutput 1 0 0 0) x = -1 ∨ loopWord (coarseOutput 1 0 0 0) x = 0 ∨ loopWord (coarseOutput 1 0 0 0) x = 1 := by decide
theorem loopWord_row_100_1 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 0 1).1.1 1 2,
  loopWord (coarseOutput 1 0 0 1) x = -1 ∨ loopWord (coarseOutput 1 0 0 1) x = 0 ∨ loopWord (coarseOutput 1 0 0 1) x = 1 := by decide
theorem loopWord_row_100_2 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 0 2).1.1 1 2,
  loopWord (coarseOutput 1 0 0 2) x = -1 ∨ loopWord (coarseOutput 1 0 0 2) x = 0 ∨ loopWord (coarseOutput 1 0 0 2) x = 1 := by decide
theorem loopWord_row_101_0 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 1 0).1.1 1 2,
  loopWord (coarseOutput 1 0 1 0) x = -1 ∨ loopWord (coarseOutput 1 0 1 0) x = 0 ∨ loopWord (coarseOutput 1 0 1 0) x = 1 := by decide
theorem loopWord_row_101_1 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 1 1).1.1 1 2,
  loopWord (coarseOutput 1 0 1 1) x = -1 ∨ loopWord (coarseOutput 1 0 1 1) x = 0 ∨ loopWord (coarseOutput 1 0 1 1) x = 1 := by decide
theorem loopWord_row_101_2 : ∀ x ∈ stepBlockOf (coarseOutput 1 0 1 2).1.1 1 2,
  loopWord (coarseOutput 1 0 1 2) x = -1 ∨ loopWord (coarseOutput 1 0 1 2) x = 0 ∨ loopWord (coarseOutput 1 0 1 2) x = 1 := by decide
theorem loopWord_row_110_0 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 0 0).1.1 1 2,
  loopWord (coarseOutput 1 1 0 0) x = -1 ∨ loopWord (coarseOutput 1 1 0 0) x = 0 ∨ loopWord (coarseOutput 1 1 0 0) x = 1 := by decide
theorem loopWord_row_110_1 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 0 1).1.1 1 2,
  loopWord (coarseOutput 1 1 0 1) x = -1 ∨ loopWord (coarseOutput 1 1 0 1) x = 0 ∨ loopWord (coarseOutput 1 1 0 1) x = 1 := by decide
theorem loopWord_row_110_2 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 0 2).1.1 1 2,
  loopWord (coarseOutput 1 1 0 2) x = -1 ∨ loopWord (coarseOutput 1 1 0 2) x = 0 ∨ loopWord (coarseOutput 1 1 0 2) x = 1 := by decide
theorem loopWord_row_111_0 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 1 0).1.1 1 2,
  loopWord (coarseOutput 1 1 1 0) x = -1 ∨ loopWord (coarseOutput 1 1 1 0) x = 0 ∨ loopWord (coarseOutput 1 1 1 0) x = 1 := by decide
theorem loopWord_row_111_1 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 1 1).1.1 1 2,
  loopWord (coarseOutput 1 1 1 1) x = -1 ∨ loopWord (coarseOutput 1 1 1 1) x = 0 ∨ loopWord (coarseOutput 1 1 1 1) x = 1 := by decide
theorem loopWord_row_111_2 : ∀ x ∈ stepBlockOf (coarseOutput 1 1 1 2).1.1 1 2,
  loopWord (coarseOutput 1 1 1 2) x = -1 ∨ loopWord (coarseOutput 1 1 1 2) x = 0 ∨ loopWord (coarseOutput 1 1 1 2) x = 1 := by decide

theorem coarseOutput_cover : ∀ c : CoarseBond witnessL (1*2),
  c = coarseOutput 0 0 0 0 ∨
  c = coarseOutput 0 0 0 1 ∨
  c = coarseOutput 0 0 0 2 ∨
  c = coarseOutput 0 0 1 0 ∨
  c = coarseOutput 0 0 1 1 ∨
  c = coarseOutput 0 0 1 2 ∨
  c = coarseOutput 0 1 0 0 ∨
  c = coarseOutput 0 1 0 1 ∨
  c = coarseOutput 0 1 0 2 ∨
  c = coarseOutput 0 1 1 0 ∨
  c = coarseOutput 0 1 1 1 ∨
  c = coarseOutput 0 1 1 2 ∨
  c = coarseOutput 1 0 0 0 ∨
  c = coarseOutput 1 0 0 1 ∨
  c = coarseOutput 1 0 0 2 ∨
  c = coarseOutput 1 0 1 0 ∨
  c = coarseOutput 1 0 1 1 ∨
  c = coarseOutput 1 0 1 2 ∨
  c = coarseOutput 1 1 0 0 ∨
  c = coarseOutput 1 1 0 1 ∨
  c = coarseOutput 1 1 0 2 ∨
  c = coarseOutput 1 1 1 0 ∨
  c = coarseOutput 1 1 1 1 ∨
  c = coarseOutput 1 1 1 2 := by decide

theorem loopWord_values (c : CoarseBond witnessL (1*2)) :
    ∀ x ∈ stepBlockOf c.1.1 1 2, loopWord c x = -1 ∨ loopWord c x = 0 ∨ loopWord c x = 1 := by
  rcases coarseOutput_cover c with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
  · rw [h0]; exact loopWord_row_000_0
  · rw [h1]; exact loopWord_row_000_1
  · rw [h2]; exact loopWord_row_000_2
  · rw [h3]; exact loopWord_row_001_0
  · rw [h4]; exact loopWord_row_001_1
  · rw [h5]; exact loopWord_row_001_2
  · rw [h6]; exact loopWord_row_010_0
  · rw [h7]; exact loopWord_row_010_1
  · rw [h8]; exact loopWord_row_010_2
  · rw [h9]; exact loopWord_row_011_0
  · rw [h10]; exact loopWord_row_011_1
  · rw [h11]; exact loopWord_row_011_2
  · rw [h12]; exact loopWord_row_100_0
  · rw [h13]; exact loopWord_row_100_1
  · rw [h14]; exact loopWord_row_100_2
  · rw [h15]; exact loopWord_row_101_0
  · rw [h16]; exact loopWord_row_101_1
  · rw [h17]; exact loopWord_row_101_2
  · rw [h18]; exact loopWord_row_110_0
  · rw [h19]; exact loopWord_row_110_1
  · rw [h20]; exact loopWord_row_110_2
  · rw [h21]; exact loopWord_row_111_0
  · rw [h22]; exact loopWord_row_111_1
  · rw [h23]; exact loopWord_row_111_2

theorem chosen_rot_guard : LogGuard (rotElem (1/16)) := by
  right
  rw [rotElem_coe,trace_rotM_re]
  norm_num [rotA]

theorem chosen_rot_inv_guard : LogGuard ((rotElem (1/16))⁻¹) := by
  right
  rw [coe_inv,Matrix.trace_conjTranspose]
  simp only [Complex.star_def,Complex.conj_re]
  rw [rotElem_coe,trace_rotM_re]
  norm_num [rotA]

theorem chosen_loop_guard (c : CoarseBond witnessL (1*2)) (x : PeriodicLatticeSite witnessL)
    (hx : x ∈ stepBlockOf c.1.1 1 2) : LogGuard (loopVar 1 2 chosenU (c.1.1,c.2) x) := by
  rw [chosenU,loop_word]
  rcases loopWord_values c x hx with h | h | h
  · rw [h,zpow_neg_one]; exact chosen_rot_inv_guard
  · rw [h,zpow_zero]; exact Or.inl rfl
  · rw [h,zpow_one]; exact chosen_rot_guard

theorem chosen_firstJet : HConstruction.Predicate.FirstJet chosenU 2
    (HConstruction.Predicate.actualQ chosenU 2) :=
  HConstruction.Predicate.actualQ_firstJet chosenU 2 (by decide) (by decide)
    (fun c x hx => logGuard_ne_cut _ (chosen_loop_guard c x hx))
end HConstruction.SmallNF

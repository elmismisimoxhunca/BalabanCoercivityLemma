import TL7b

/-!
# TL7c -- strided staircase paths and the strided block average are natural
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarsePathEndpoint coarseGammaPath coarseCoordSteps coarseStraightSegment)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)

theorem fin_sub_val_of_le {n : ℕ} (a b : Fin (n + 1)) (h : a.val ≤ b.val) : (b - a).val = b.val - a.val := by
  rw [Fin.sub_def]
  simp only
  have : n + 1 - a.val + b.val = (n + 1) + (b.val - a.val) := by omega
  rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem phiS_update {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ) (y x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    phiS h o (Function.update y μ (x μ)) = Function.update (phiS h o y) μ (phiS h o x μ) := by
  funext ν
  by_cases hν : ν = μ
  · subst hν; simp [phiS]
  · simp [phiS, Function.update_of_ne hν]

theorem coarseCoordSteps_nat {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {b : ℕ} (hp : PhiOK h o b) (hb : 0 < b)
    (s : ℕ) {y a x : PeriodicLatticeSite Lt} (hy : Aligned b y) (ν : Fin 3) (hay : a ν = y ν)
    (h1 : (y ν).val ≤ (x ν).val) (h2 : (x ν).val < (y ν).val + b) :
    coarseCoordSteps s (phiS h o a) (phiS h o x) ν = coarseCoordSteps s a x ν := by
  unfold coarseCoordSteps
  have A : (x ν - a ν).val = (x ν).val - (y ν).val := by
    rw [fin_sub_val_of_le _ _ (by rw [hay]; exact h1), hay]
  have hay' : phiS h o a ν = phiS h o y ν := by simp only [phiS, hay]
  have hv := phiS_val_in_block hp hb hy ν h1 h2
  have B : (phiS h o x ν - phiS h o a ν).val = (x ν).val - (y ν).val := by
    rw [hay', fin_sub_val_of_le _ _ (by omega)]
    omega
  rw [A, B]

theorem coarseGammaPath_nat {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}
    (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell) {y x : PeriodicLatticeSite Lt}
    (hy : Aligned (s * ell) y) (hx : x ∈ stepBlockOf y s ell) :
    coarseGammaPath s (phiS h o y) (phiS h o x) = coarseGammaPath s y x := by
  have hb : 0 < s * ell := Nat.mul_pos hs hell
  rw [mem_stepBlockOf] at hx
  unfold coarseGammaPath coarseStraightSegment
  have e2 := coarseCoordSteps_nat hp hb s hy (a := y) (x := x) 2 rfl (hx 2).1 (hx 2).2.1
  have e1 := coarseCoordSteps_nat hp hb s hy (a := Function.update y 2 (x 2)) (x := x) 1
    (by simp [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]) (hx 1).1 (hx 1).2.1
  have e0 := coarseCoordSteps_nat hp hb s hy (a := Function.update (Function.update y 2 (x 2)) 1 (x 1)) (x := x) 0
    (by simp [Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1), Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2)])
    (hx 0).1 (hx 0).2.1
  rw [phiS_update, phiS_update] at e0
  rw [phiS_update] at e1
  rw [e2, e1, e0]

theorem aligned_of_mul {L : PeriodicLatticeExtent} {s ell : ℕ} {y : PeriodicLatticeSite L} (hy : Aligned (s * ell) y) :
    Aligned s y := fun μ => (Dvd.intro ell rfl).trans (hy μ)

theorem stepAverage_nat {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {s ell : ℕ}
    (hp : PhiOK h o (s * ell)) (hs : 0 < s) (hell : 0 < ell)
    {Vt : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lt}
    {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : AgreeAligned h o s Vt V)
    (lamt : PeriodicLatticeSite Lt → AdalyFormal.Balaban.CovariantOperators.SuTwo)
    (lam : PeriodicLatticeSite L → AdalyFormal.Balaban.CovariantOperators.SuTwo)
    {y : PeriodicLatticeSite Lt} (hy : Aligned (s * ell) y)
    (hlam : ∀ x ∈ stepBlockOf y s ell, lamt x = lam (phiS h o x)) :
    AdalyFormal.Balaban.QjComposite.stepAverage s Vt ell lamt y =
      AdalyFormal.Balaban.QjComposite.stepAverage s V ell lam (phiS h o y) := by
  unfold AdalyFormal.Balaban.QjComposite.stepAverage
  congr 1
  rw [← stepBlock_sum hp hs hell hy (fun w => AdalyFormal.Balaban.CovariantOperators.RMap
    (coarsePathHolonomy s V (phiS h o y) (coarseGammaPath s (phiS h o y) w)) (lam w))]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [coarseGammaPath_nat hp hs hell hy hx,
    coarsePathHolonomy_nat (hp.mono (Dvd.intro ell rfl)) hV _ _ (aligned_of_mul hy), hlam x hx]

theorem aligned_of_block {L : PeriodicLatticeExtent} {s ell : ℕ} {y x : PeriodicLatticeSite L}
    (hy : Aligned s y) (hx : x ∈ stepBlockOf y s ell) : Aligned s x := by
  rw [mem_stepBlockOf] at hx
  intro μ
  obtain ⟨h1, -, h3⟩ := hx μ
  have : (x μ).val = (y μ).val + ((x μ).val - (y μ).val) := by omega
  rw [this]; exact dvd_add (hy μ) h3

open AdalyFormal.Balaban.QjComposite (Qcomposite) in
theorem Qcomposite_nat {Lt L : PeriodicLatticeExtent} {h : Covers Lt L} {o : Fin 3 → ℕ} {ell : ℕ} (hell : 0 < ell)
    (bgt : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) Lt)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (lam : PeriodicLatticeSite L → AdalyFormal.Balaban.CovariantOperators.SuTwo) :
    ∀ j : ℕ, PhiOK h o (ell ^ j) → (∀ l, l < j → AgreeAligned h o (ell ^ l) (bgt l) (bg l)) →
      ∀ y : PeriodicLatticeSite Lt, Aligned (ell ^ j) y →
        Qcomposite bgt ell j (fun x => lam (phiS h o x)) y = Qcomposite bg ell j lam (phiS h o y) := by
  intro j
  induction j with
  | zero => intro _ _ y _; rfl
  | succ j ih =>
    intro hp hbg y hy
    have hpos : 0 < ell ^ j := pow_pos hell j
    have hp' : PhiOK h o (ell ^ j * ell) := by rw [← pow_succ]; exact hp
    have hy' : Aligned (ell ^ j * ell) y := by rw [← pow_succ]; exact hy
    show AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ j) (bgt j) ell (Qcomposite bgt ell j (fun x => lam (phiS h o x))) y =
      AdalyFormal.Balaban.QjComposite.stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) (phiS h o y)
    refine stepAverage_nat hp' hpos hell (hbg j (Nat.lt_succ_self j)) _ _ hy' (fun x hx => ?_)
    exact ih (hp.mono (pow_dvd_pow ell (Nat.le_succ j))) (fun l hl => hbg l (Nat.lt_succ_of_lt hl)) x
      (aligned_of_block (aligned_of_mul hy') hx)

end AdalyFormal.Thin

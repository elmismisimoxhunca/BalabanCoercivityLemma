import TL17b

/-!
# TL17c -- `OnLambdaTildeIn`, `OnLambdaT` and `bondEnergy` under pull-back
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice blockOf mem_blockOf staircasePath)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.IngredientFamilyR2

section onl
variable {Lut Lu : PeriodicLatticeExtent} {hu : Covers Lut Lu} {o : Fin 3 → ℕ} {ell : ℕ}

theorem onLambdaTildeIn_pull (hp : PhiOK hu o ell) (hell : 0 < ell) (Lam : Set (PeriodicLatticeSite Lu)) (Bt : Bond Lu → SuTwo)
    (h : OnLambdaTildeIn Lam ell Bt) : OnLambdaTildeIn (phiS hu o ⁻¹' Lam) ell (fun e => Bt (phiE hu o e)) := by
  refine ⟨fun y hy x hx b hb => ?_, fun b hb => ?_⟩
  · have hal : Aligned ell y := fun μ => Nat.dvd_of_mod_eq_zero (mem_CoarseLattice.mp hy.1 μ)
    exact h.1 (phiS hu o y) ((LamPrime_pull hp hell Lam y).mp hy) (phiS hu o x) (phiS_mem_blockOf hp hell hal hx) _
      (staircase_pull hp hell hal hx hb)
  · exact h.2 _ ((isDropped_pull hp hell Lam b).mp hb)

theorem onLambdaT_pull (Lam : Set (PeriodicLatticeSite Lu)) (Bt : Bond Lu → SuTwo) (h : OnLambdaT Lam Bt) :
    OnLambdaT (phiS hu o ⁻¹' Lam) (fun e => Bt (phiE hu o e)) := by
  intro b hb
  apply h
  intro hmem
  apply hb
  rw [phiE] at hmem
  simp only [Set.mem_preimage, phiS_shift]
  exact hmem

theorem bondEnergy_pull (Bt : Bond Lu → SuTwo) :
    bondEnergy (fun e => Bt (phiE hu (fun _ => 0) e)) = (Fintype.card (DeckIdx Lut Lu) : ℝ) * bondEnergy Bt := by
  have hπ : FibreCount (phiE hu (fun _ => 0)) (Fintype.card (DeckIdx Lut Lu)) := by
    rw [← covE_pi]; exact (covE hu).fibreCount
  unfold bondEnergy
  exact sum_comp_fibre hπ (fun b => ‖Bt b‖ ^ 2)

end onl

end AdalyFormal.Thin

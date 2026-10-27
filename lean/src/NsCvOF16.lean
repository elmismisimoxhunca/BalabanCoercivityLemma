import NsCvOF15

/-!
# CvOF16 -- admissibility of `zfun (gU p)`: `OnLambdaT` and `OnLambdaTildeIn` for `neLam` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (droppedBondLast)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem gU_aligned_zero (hE : StagOK ell) (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) {p : ℕ} (hp : p ≤ 1) {u : ℕ} (hu : u % ell = 0) :
    gU M R p u = 0 := by
  by_contra hne
  have hell4 : 4 ≤ ell := hE.four hell3
  rcases gU_ne_zero hne with h | h
  · have e1 : u0N M R + p = M * (2 * R + (CfData.cf + 2)) + (1 + p) := by unfold u0N; ring
    rw [h, e1, mod_aux hdvd _ (by omega)] at hu; omega
  · have e2 : u0N M R + p + 1 = M * (2 * R + (CfData.cf + 2)) + (2 + p) := by unfold u0N; ring
    rw [h, e2, mod_aux hdvd _ (by omega)] at hu; omega

theorem zfun_gU_eq_zero_of_dir {L : PeriodicLatticeExtent} (hE : StagOK ell) (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) {p : ℕ} (hp : p ≤ 1)
    (b : Bond L) (hb : b.2 ≠ 1 ∨ (b.1 0).val % ell = 0) : (zfun (gU M R p) : Bond L → SuTwo) b = 0 := by
  unfold zfun
  rcases hb with h | h
  · rw [if_neg h]
  · split_ifs
    · rw [gU_aligned_zero hE hell3 hdvd hp h, dgS_zero]
    · rfl

theorem onLambdaT_gU (hE : StagOK ell) (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hMe : ell ≤ M) {p : ℕ} (hp : p ≤ 1) :
    OnLambdaT (neLam M R) (zfun (gU M R p) : Bond (neLu M R) → SuTwo) := by
  intro b hb
  unfold zfun
  split_ifs with h1
  · by_contra hne
    apply hb
    left
    have : gU M R p (b.1 0).val ≠ 0 := by
      intro h0; apply hne; rw [h0, dgS_zero]
    unfold neLam
    have hell4 : 4 ≤ ell := hE.four hell3
    have hlo : neLo M R = M * (2 * R + (CfData.cf + 2)) := rfl
    rcases gU_ne_zero this with h | h
    · refine ⟨?_, ?_⟩ <;> simp only [h] <;> unfold u0N <;> omega
    · refine ⟨?_, ?_⟩ <;> simp only [h] <;> unfold u0N <;> omega
  · rfl

theorem onLambdaTildeIn_gU (hE : StagOK ell) (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) {p : ℕ} (hp : p ≤ 1) :
    OnLambdaTildeIn (neLam M R) ell (zfun (gU M R p) : Bond (neLu M R) → SuTwo) := by
  refine ⟨?_, ?_⟩
  · intro y hy x hx b hb
    have hyc : ∀ μ : Fin 3, (y μ).val % ell = 0 := mem_CoarseLattice.mp hy.1
    unfold staircasePath at hb
    simp only [Finset.mem_union] at hb
    rcases hb with (hb | hb) | hb
    · refine zfun_gU_eq_zero_of_dir hE hell3 hdvd hp b (Or.inl ?_)
      rw [mem_axisSegment] at hb; rw [hb.1]; decide
    · refine zfun_gU_eq_zero_of_dir hE hell3 hdvd hp b (Or.inr ?_)
      rw [mem_axisSegment] at hb
      have := hb.2.1 0 (by decide)
      rw [this]
      simp only [corner1, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide)]
      exact hyc 0
    · refine zfun_gU_eq_zero_of_dir hE hell3 hdvd hp b (Or.inl ?_)
      rw [mem_axisSegment] at hb; rw [hb.1]; decide
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := hb
    have hcc : ∀ μ : Fin 3, (c.1.1 μ).val % ell = 0 := mem_CoarseLattice.mp c.1.2
    refine zfun_gU_eq_zero_of_dir hE hell3 hdvd hp _ ?_
    by_cases hc1 : c.2 = 1
    · right
      have hps : ∀ i : ℕ, (pathSite c.1.1 c.2 i) 0 = c.1.1 0 := by
        intro i
        induction i with
        | zero => rfl
        | succ i ih =>
          rw [AdalyFormal.Balaban.QOne.pathSite_succ]
          have : (periodicLatticeShift (pathSite c.1.1 c.2 i) c.2) 0 = (pathSite c.1.1 c.2 i) 0 := by
            simp only [periodicLatticeShift, Function.update_of_ne (show (0 : Fin 3) ≠ c.2 by rw [hc1]; decide)]
          rw [this, ih]
      show ((pathSite c.1.1 c.2 (ell - 1)) 0).val % ell = 0
      rw [hps]; exact hcc 0
    · left; exact hc1

#print axioms gU_aligned_zero
#print axioms onLambdaT_gU
#print axioms onLambdaTildeIn_gU

end AdalyFormal.CoverOmega

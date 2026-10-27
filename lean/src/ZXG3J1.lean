import ZXG3I
import AdalyFormal.Balaban.SuTwoGeomU1

/-!
# G3J1 -- the tree's CMP96 Lemma 2.4 at `U = 1`, `ell = 2` in the form used at the closed point:
for axial `B` with `Q₁B = 0`:  `(1/1728) Σ_b ‖B b‖² ≤ Σ_p ‖(curl B)(p)‖²`.
(Same derivation as `HConstruction.GenK.lemma24_kernel`, redone here from the tree theorem
`SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible` so that this file imports only tree modules.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice staircasePath)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo lineCoarseRestrictCovLM)
open AdalyFormal.Balaban.CoercivityTargetsCorrected (SuTwoGeomAdditiveInequality)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem lemma24_flat {L : PeriodicLatticeExtent} (hL : ∀ μ : Fin 3, 4 ≤ L μ)
    (hdvd : ∀ μ : Fin 3, 2 ∣ (L μ + 1)) (B : Bond L → SuTwo)
    (hB : ∀ y ∈ CoarseLattice L 2, ∀ x ∈ blockOf y 2, ∀ b ∈ staircasePath y x, B b = 0)
    (hQ : ∀ c, lineCoarseRestrictSuTwo 2 B c = 0) :
    (1 / 1728 : ℝ) * ∑ b : Bond L, ‖B b‖ ^ 2 ≤
      ∑ p : PeriodicLatticePlaquette L, ‖curlCovariantLM (trivialU L) B p‖ ^ 2 := by
  have h := AdalyFormal.Balaban.SuTwoGeomU1.suTwoGeomAdditive_trivialU_of_admissible hL hdvd B hB
  unfold SuTwoGeomAdditiveInequality at h
  have hq : lineCoarseRestrictCovLM (trivialU L) 2 B = (fun c => lineCoarseRestrictSuTwo 2 B c) := by
    funext c
    exact AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU 2 B c
  rw [hq] at h
  simp only [AdalyFormal.Balaban.CovariantHj.covBondInner, AdalyFormal.Balaban.CovariantHj.covPlaqInner,
    AdalyFormal.Balaban.CovariantHjFaithful.covCoarseBondInner,
    ← AdalyFormal.Balaban.SuTwoInner.inner_eq_hsInner, real_inner_self_eq_norm_sq, hQ,
    norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero, zero_add] at h
  norm_num only [Nat.cast_ofNat] at h
  norm_num at h ⊢
  linarith [h]

#print axioms lemma24_flat

end AdalyFormal.StatementLaneG

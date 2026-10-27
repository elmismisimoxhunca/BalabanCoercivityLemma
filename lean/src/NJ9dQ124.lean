import NJ9cBase

/-!
# NJ9dQ124 -- the pure `q124Principal` versions (no `Q1jet`, no regularity predicate), on an ARBITRARY torus:
  (i)  `‖q124Principal 1 ell V A c - unitToCoarseCov 1 ell V A c‖ ≤ 8 κ M`   (printed (124) vs main term (125))
  (ii) `‖q124Principal 1 ell V A c - q124Principal 1 ell 1 A c‖ ≤ (8 ell ε₀ + 8 κ) M`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.NonflatJet

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (unitToCoarseCov)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.DeltaKR85 (q124Principal q124Principal_eq_unitToCoarseCov_add_delta)
open EstimatesLayer.E1E3
open OneStep124
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem q124_sub_T1_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (A : CoarseBond L 1 → SuTwo) (M : ℝ) (hM : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M)
    (c : CoarseBond L (1 * ell)) :
    ‖q124Principal 1 ell V A c - unitToCoarseCov 1 ell V A c‖
      ≤ 8 * e2Majorant (rhoOf ell ε0) * M := by
  rw [q124Principal_eq_unitToCoarseCov_add_delta, add_sub_cancel_left]
  obtain ⟨hE1, hE2, hE3⟩ := E_bounds hell hdvd V ε0 hε0 hV hsmall c
  exact norm_delta124_le_sup hell V _ c _ M (e2Majorant_nonneg (by unfold rhoOf; positivity)) hM
    hE1 hE2 hE3 A hA

theorem q124_sub_flat_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (A : CoarseBond L 1 → SuTwo) (M : ℝ) (hM : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M)
    (c : CoarseBond L (1 * ell)) :
    ‖q124Principal 1 ell V A c - q124Principal 1 ell (trivialU L) A c‖
      ≤ (8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0)) * M := by
  rw [q124Principal_eq_unitToCoarseCov_add_delta, q124Principal_eq_unitToCoarseCov_add_delta]
  have h1 := norm_T1_drift_le hell V ε0 hε0 hV A M hM hA c
  have hflatV : ∀ e, frobNorm ((((trivialU L) e : SU2) : M2) - 1) ≤ 0 := by
    intro e
    show frobNorm (((1 : SU2) : M2) - 1) ≤ 0
    simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero]
  obtain ⟨hE1, hE2, hE3⟩ := E_bounds hell hdvd V ε0 hε0 hV hsmall c
  obtain ⟨hF1, hF2, hF3⟩ := E_bounds hell hdvd (trivialU L) 0 le_rfl hflatV
    (by rw [rhoOf_zero]; positivity) c
  rw [rhoOf_zero, e2Majorant_zero] at hF1 hF2 hF3
  have hκ : 0 ≤ e2Majorant (rhoOf ell ε0) := e2Majorant_nonneg (by unfold rhoOf; positivity)
  have h2 := norm_delta124_le_sup hell V _ c _ M hκ hM hE1 hE2 hE3 A hA
  have h3 := norm_delta124_le_sup hell (trivialU L) _ c 0 M le_rfl hM hF1 hF2 hF3 A hA
  have key : ∀ (a b c' d : SuTwo), ‖(a + b) - (c' + d)‖ ≤ ‖a - c'‖ + ‖b‖ + ‖d‖ := by
    intro a b c' d
    have : (a + b) - (c' + d) = (a - c') + b - d := by abel
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  refine (key _ _ _ _).trans ?_
  nlinarith [h1, h2, h3]

#print axioms q124_sub_T1_le
#print axioms q124_sub_flat_le

end AdalyFormal.NonflatJet

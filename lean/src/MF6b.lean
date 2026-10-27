import MF6a
import NJ9cBase
import NJ9dQ124

/-!
# MF6b (TEXT COPY of nonflat_jet R5Drift, recompiled against the r7 fork) -- sup-norm drift of the genuine unit-level `Q₁` (r5 carrier) from the flat one.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace AdalyFormal.M0Finish.R7

open Matrix
open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLinkConfiguration)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.IngredientFamilyR2 (Q1jet flatCfg RegBg)
open AdalyFormal.NonflatJet (bondToUnit rhoOf guard_of_small regBg_flat flat_guard flatCfg_eq_trivialU
  q124_sub_flat_le)
open EstimatesLayer.E1E3
local instance : NormedSpace ℝ SuTwo := instInnerProductSpaceSuTwo.toNormedSpace

variable {L : PeriodicLatticeExtent}

theorem Q1jet_sub_flat_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (V : PeriodicLinkConfiguration SU2 L) (ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (hV : ∀ e, frobNorm ((V e : M2) - 1) ≤ ε0) (hsmall : rhoOf ell ε0 < Real.pi / 2)
    (hreg : RegBg 1 ell V) (B : Bond L → SuTwo) (M : ℝ) (hM : 0 ≤ M) (hB : ∀ b, ‖B b‖ ≤ M)
    (c : CoarseBond L ell) :
    ‖Q1jet ell V B c - Q1jet ell flatCfg B c‖
      ≤ (8 * ell * ε0 + 8 * e2Majorant (rhoOf ell ε0)) * M := by
  rw [Q1jet_eq_q124 V ell hell hdvd hreg (guard_of_small V ε0 hε0 hV hsmall) B c,
    Q1jet_eq_q124 (flatCfg : PeriodicLinkConfiguration SU2 L) ell hell hdvd (regBg_flat ell)
      (fun c x hx => flat_guard hell (c.1.1, c.2) x hx) B c, flatCfg_eq_trivialU]
  exact q124_sub_flat_le hell hdvd V ε0 hε0 hV hsmall (bondToUnit B) M hM (fun b => hB _) _

#print axioms Q1jet_sub_flat_le

end AdalyFormal.M0Finish.R7

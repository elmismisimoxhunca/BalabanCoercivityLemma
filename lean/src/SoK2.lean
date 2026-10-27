import SoK1
import NuK2

/-!
# SoK2 -- `Bperp` and the orthogonality of the transverse-sum-zero part, for general `ell` (lane sites_only_20261019)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}
variable {L : PeriodicLatticeExtent}

/-- the transverse-sum-zero part of the pattern. -/
noncomputable def Bperp (ell uE : ℕ) : BondFnL2 L := Bpat ell uE - zfield (gbar ell uE)

theorem inner_Bperp_zfield (hell : 0 < ell) (uE : ℕ) (huE : uE + 1 < L 0 + 1) (h1 : ell ∣ L 1 + 1) (h2 : ell ∣ L 2 + 1) (g : ℕ → ℝ) :
    (inner ℝ (Bperp ell uE : BondFnL2 L) (zfield g) : ℝ) = 0 := by
  unfold Bperp
  rw [inner_sub_left, inner_sig_zfield _ (Bpat_sig ell uE) g, inner_zfield_zfield]
  simp only [thetaOf_Bpat]
  rw [sum_betaPat ell hell uE huE h1 h2 g]
  ring

theorem perp_orth (hg : NGeo ell M R) (hM : 0 < M) (uE : ℕ) (huE : uE + 1 < neLu M R 0 + 1)
    (h1 : ell ∣ neLu M R 1 + 1) (h2 : ell ∣ neLu M R 2 + 1) (ρ : ℕ → ℕ → ℝ) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by have := hg.hell; omega) (neS ell M R)) (Bperp ell uE))
      (zrow (geomOf ell 2 (neS ell M R)) ρ) : ℝ) = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_left, tau_zrow hg hM]
  exact inner_Bperp_zfield (by have := hg.hell; omega) uE huE h1 h2 _

end

#print axioms perp_orth

end AdalyFormal.SitesOnly

import SoM1

/-!
# SoM2 -- `genForm` of the pattern competitor, for general `ell` (lane sites_only_20261019)

`genForm_pat_eq`: `genForm (genC B) = eta * <τ*B, N⁻¹ τ*B> - a <B, B>` for `B = Bpatf ell uE` (`genC B = B` and `D2in B = 0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.CoverJacobi
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLane (scaleUp Tower)
open AdalyFormal.StatementLaneG
open scoped RealInnerProductSpace
open AdalyFormal.NcwdhTwo

section
variable [CfData]
variable {ell M R : ℕ}

theorem Bperp_sig {L : PeriodicLatticeExtent} (ell uE : ℕ) : SigB (WithLp.ofLp (Bperp ell uE : BondFnL2 L)) := by
  intro b
  have h1 := Bpat_sig (L := L) ell uE b
  have h2 := zfield_sig (L := L) (gbar ell uE) b
  show diagP ((Bpat ell uE : BondFnL2 L).ofLp b - (zfield (gbar ell uE) : BondFnL2 L).ofLp b) = _
  rw [map_sub, h1, h2]; rfl

variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

theorem genForm_pat_eq (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (a t : ℝ) (ht : |t| < Real.pi / 2)
    (uE : ℕ) (huE : uE % ell + 2 ≤ ell) :
    GenP.genForm (Pt ell M R (by omega) C t a)
        (WithLp.toLp 2 (GenP.genC (Pt ell M R (by omega) C t a) (Bpatf ell uE))) =
      (Pt ell M R (by omega) C t a).eta *
        (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat ell uE))
          (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C t a))
            (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat ell uE))) : ℝ) -
      a * (inner ℝ (Bpat ell uE : BondFnL2 (neLu M R)) (Bpat ell uE) : ℝ) := by
  rw [Pt_genC_pat hCp hell2 hE hdvd hM hR a t ht uE huE]
  have hD := Pt_D2in_pat hCp hell2 hE hdvd hM hR a t ht uE
  unfold GenP.genForm GenP.firstTerm
  have : (WithLp.toLp 2 (Bpatf ell uE) : BondFnL2 (neLu M R)) = Bpat ell uE := rfl
  rw [this, hD, map_zero, inner_zero_left, mul_zero, sub_zero]
  rfl

end

#print axioms genForm_pat_eq

end AdalyFormal.SitesOnly

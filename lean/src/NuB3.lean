import NuB2
import NuSig5
import NuG4
import NsCvOX1

/-!
# NuB3 -- on `Ad_h`-fixed vectors of `E₀`, `Q` is `t`-independent and `G1inv` is affine in `cos 2t` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

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

section
variable [CfData]
variable {ell M R : ℕ}

theorem sigB'_iff {L : PeriodicLatticeExtent} (x : BondFnL2 L) : SigB' x ↔ SigB (WithLp.ofLp x) := by
  constructor
  · intro h b
    have := congrArg (fun g : BondFnL2 L => g b) h
    simpa [pwDiag_apply] using this
  · intro h
    refine PiLp.ext (fun b => ?_)
    rw [pwDiag_apply]
    exact h b

/-- `Q` of the direction-0 staggered tower on sigma_3 fields does not depend on `t`. -/
theorem Qfull_sig_indep (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) {t s : ℝ}
    (ht : |t| < Real.pi / 2) (hs : |s| < Real.pi / 2) {A : BondFnL2 (scaleUp ell 2 (neLu M R))} (hA : SigB (WithLp.ofLp A)) :
    QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t) A =
      QfullOf (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) s) A := by
  have St := nested_z0Setup hell2 hE hdvd hM hR t ht
  have Ss := nested_z0Setup hell2 hE hdvd hM hR s hs
  refine PiLp.ext (fun p => ?_)
  have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
  show (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) t) p.1 A)) p.2.1 =
    (((ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB (geomOf ell 2 (neS ell M R)) (stag0Cfg (neC0 ell M R) s) p.1 A)) p.2.1
  rw [QlinB_sig0 St.z _ rfl p.1 hj A hA, QlinB_sig0 Ss.z _ rfl p.1 hj A hA]

/-- abstract: on sigma_3 elements of `E₀`, `G1inv = Ginv` (given `C2 = 0` on sigma_3 fields). -/
theorem G1inv_eq_Ginv_of (P : IngrBParams) (hcart : CartanCfg P.U)
    (hC : ∀ A : BondFnL2 P.Lf, SigB (WithLp.ofLp A) → P.sector.C2full A = 0)
    (x : ↥(bondSupp P.G)) (hx : SigB (WithLp.ofLp (x : BondFnL2 P.Lf))) : P.G1inv x = P.data.Ginv x := by
  have hD2 := Delta2_sig P hcart hC x hx
  have hG1 : P.G1inv = P.data.Ginv - P.data.Delta2 P.data_laws :=
    P.data.G1inv_unique P.G1inv_spec (P.data.isG1inv_sub P.data_laws)
  rw [hG1]; simp [hD2]

/-- on sigma_3 elements of `E₀`, `G1inv = Ginv` (nested instance). -/
theorem G1inv_eq_Ginv (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (x : ↥(bondSupp (geomOf ell 2 (neS ell M R)))) (hx : SigB (WithLp.ofLp (x : BondFnL2 (scaleUp ell 2 (neLu M R))))) :
    (Pt ell M R (by omega) (neC0 ell M R) t a).G1inv x = (Pt ell M R (by omega) (neC0 ell M R) t a).data.Ginv x := by
  have S := nested_z0Setup hell2 hE hdvd hM hR t ht
  exact G1inv_eq_Ginv_of (Pt ell M R (by omega) (neC0 ell M R) t a) (stag0Cfg_cartan _ t)
    (fun A hA => C2fullOf_sig0 S.z _ S.hG S.hk A hA) x hx

end

end AdalyFormal.NcwdhTwo

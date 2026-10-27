import SoK6
import SoK3
import SoB7
import SoPtZ8
import SoU2
import SoE8
import NuM1

/-!
# SoM1 -- splitting `<y, N⁻¹ y>` for the pattern competitor into the Z-row part and the orthogonal part, for general `ell` (lane sites_only_20261019)

`val_split`  : `<τ*B, N⁻¹ τ*B> = <τ* z, N⁻¹ τ* z> + <τ* B⊥, N⁻¹ τ* B⊥>` with `z = zfield (gbar ell uE)`, `B⊥ = B - z`.
`val0_bound` : the Z-row part is bounded by the single-edge chain form at any chain vector with `Q x_e = τ* z`.
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
variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

local notation "GG" => geomOf ell 2 (neS ell M R)

theorem val_split (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2)
    (hG1 : IsUnit (Pt ell M R (by omega) C t a).G1inv)
    (hN : IsUnit (GenP.Nmat (Pt ell M R (by omega) C t a)))
    (uE : ℕ) (huE : uE + 1 < neLu M R 0 + 1) (h1 : ell ∣ neLu M R 1 + 1) (h2 : ell ∣ neLu M R 2 + 1) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat ell uE))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat ell uE))) : ℝ) =
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))) : ℝ) +
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp ell uE))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp ell uE))) : ℝ) := by
  have hg := nGeo_two hell2 hdvd hM hR
  set P := Pt ell M R (by omega) C t a with hP
  have hNeq : GenP.Nmat P = P.data.Q.comp ((Ring.inverse P.G1inv).comp P.data.Qs) := by
    unfold GenP.Nmat
    exact ContinuousLinearMap.ext (fun _ => rfl)
  have hBsplit : (Bpat ell uE : BondFnL2 (neLu M R)) = zfield (gbar ell uE) + Bperp ell uE := by
    unfold Bperp; abel
  rw [hBsplit, map_add]
  have hsp := AdalyNcwdhTwo.Min.split_inner (A := P.G1inv) P.G1inv_spec.symm hG1 (Q := P.data.Q) (Qs := P.data.Qs)
    P.data.Q_adj (by rw [← hNeq]; exact hN) (WZ GG) (ZF GG)
    (fun x hx => G1inv_mem_WZ hCp hell2 hE hdvd hM hR t a ht hx) (fun z hz => Qs_mem_WZ hCp hell2 hE hdvd hM hR t a ht hz)
    (fun x hx => Q_mem_ZF hCp hell2 hE hdvd hM hR t a ht hx)
    (y0 := ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))
    (y1 := ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp ell uE))
    (by rw [tauAdj_zfield_eq hell2 hdvd hM hR]; exact ⟨_, rfl⟩)
    (by
      rintro z ⟨ρ, rfl⟩
      exact perp_orth hg hM uE huE h1 h2 ρ)
  rw [← hNeq] at hsp
  exact hsp

theorem val0_bound (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2)
    (hG1 : IsUnit (Pt ell M R (by omega) C t a).G1inv)
    (hN : IsUnit (GenP.Nmat (Pt ell M R (by omega) C t a)))
    (hpsd : ∀ e' : Fin (nN ell M R) → ℝ, e' ∈ Vsub (rowOfN ell M R) → 0 ≤ qF1 (C - neP0 ell M R) (Real.cos (2 * t)) e')
    {i1 p uE : ℕ} (hp : i1 + p + 1 < RN (nGeo_two hell2 hdvd hM hR))
    (hlnE : lnN ell M R (i1 + p) = ell ^ 2) (hlnO : lnN ell M R (i1 + p + 1) = ell ^ 2)
    (hsE : neP0 ell M R + stN ell M R (i1 + p) = ell ^ 2 * uE) (hsO : neP0 ell M R + stN ell M R (i1 + p + 1) = ell ^ 2 * (uE + 1))
    {es : Fin (nN ell M R) → ℝ} (hes : es ∈ Vsub (rowOfN ell M R)) (τ : ℝ) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) C t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))) : ℝ) ≤
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (C - neP0 ell M R) (Real.cos (2 * t)) (f0pair (nGeo_two hell2 hdvd hM hR) i1 p hp + τ • es) +
      (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))
        (diagW (geomOf ell 2 (neS ell M R)) (massW (geomOf ell 2 (neS ell M R)) a)
          (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar ell uE)))) : ℝ) := by
  have hz := zblock_ineq hCp hell2 hE hdvd hM hR t a ht hG1 hN hpsd (f0pair (nGeo_two hell2 hdvd hM hR) i1 p hp + τ • es)
  rw [Qx_pair hCp hell2 hE hdvd hM hR t a ht hp hlnE hlnO hsE hsO hes τ] at hz
  rw [tauAdj_zfield_eq hell2 hdvd hM hR]
  exact hz

end

#print axioms val_split
#print axioms val0_bound

end AdalyFormal.SitesOnly

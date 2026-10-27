import NuB7
import NuK6
import NuK3
import NuF1
import NuPtZ8

/-!
# NuM1 -- splitting `<y, N⁻¹ y>` for the pattern competitor into the Z-row part and the orthogonal part (lane ncwdh_ell2_20261018)

`val_split`  : `<τ*B, N⁻¹ τ*B> = <τ* z, N⁻¹ τ* z> + <τ* B⊥, N⁻¹ τ* B⊥>` with `z = zfield (gbar uE)`, `B⊥ = B - z`.
`val0_bound` : the Z-row part is bounded by the single-edge chain form at any chain vector with `Q x_e = τ* z`.
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

local notation "GG" => geomOf ell 2 (neS ell M R)

theorem tauAdj_zfield_eq (hell2 : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (g : ℕ → ℝ) :
    ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield g) =
      zrow GG (AdalyFormal.CoverOmega.rhoY ell g) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have := tau_adjoint_zfield ell 2 (neLu M R) (by omega) (neS ell M R)
    (fun b hb => crs_of_bondsLam hg hM le_rfl b hb) g
  rw [this]; rfl

theorem val_split (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2)
    (hG1 : IsUnit (Pt ell M R (by omega) (neC0 ell M R) t a).G1inv)
    (hN : IsUnit (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a)))
    (uE : ℕ) (huE : uE + 1 < neLu M R 0 + 1) (h1 : 2 ∣ neLu M R 1 + 1) (h2 : 2 ∣ neLu M R 2 + 1) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat uE))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bpat uE))) : ℝ) =
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar uE)))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar uE)))) : ℝ) +
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp uE))
      (Ring.inverse (GenP.Nmat (Pt ell M R (by omega) (neC0 ell M R) t a))
        (ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp uE))) : ℝ) := by
  have hg := nGeo_two hell2 hdvd hM hR
  set P := Pt ell M R (by omega) (neC0 ell M R) t a with hP
  have hNeq : GenP.Nmat P = P.data.Q.comp ((Ring.inverse P.G1inv).comp P.data.Qs) := by
    unfold GenP.Nmat
    exact ContinuousLinearMap.ext (fun _ => rfl)
  have hBsplit : (Bpat uE : BondFnL2 (neLu M R)) = zfield (gbar uE) + Bperp uE := by
    unfold Bperp; abel
  rw [hBsplit, map_add]
  have hsp := AdalyNcwdhTwo.Min.split_inner (A := P.G1inv) P.G1inv_spec.symm hG1 (Q := P.data.Q) (Qs := P.data.Qs)
    P.data.Q_adj (by rw [← hNeq]; exact hN) (WZ GG) (ZF GG)
    (fun x hx => G1inv_mem_WZ hell2 hE hdvd hM hR t a ht hx) (fun z hz => Qs_mem_WZ hell2 hE hdvd hM hR t a ht hz)
    (fun x hx => Q_mem_ZF hell2 hE hdvd hM hR t a ht hx)
    (y0 := ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (zfield (gbar uE)))
    (y1 := ContinuousLinearMap.adjoint (tauExt ell 2 (neLu M R) (by omega) (neS ell M R)) (Bperp uE))
    (by rw [tauAdj_zfield_eq hell2 hdvd hM hR]; exact ⟨_, rfl⟩)
    (by
      rintro z ⟨ρ, rfl⟩
      exact perp_orth hg hM uE huE h1 h2 ρ)
  rw [← hNeq] at hsp
  exact hsp

theorem val0_bound (hdvd : 2 ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ) (ht : |t| < Real.pi / 2)
    (hG1 : IsUnit (Pt 2 M R (by norm_num) (neC0 2 M R) t a).G1inv)
    (hN : IsUnit (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) t a)))
    (hpsd : ∀ e' : Fin (nN 2 M R) → ℝ, e' ∈ Vsub (rowOfN 2 M R) → 0 ≤ qF1 (neC0 2 M R - neP0 2 M R) (Real.cos (2 * t)) e')
    {i1 p uE : ℕ} (hp : i1 + p + 1 < RN (nGeo_two (le_refl 2) hdvd hM hR))
    (hlnE : lnN 2 M R (i1 + p) = 4) (hlnO : lnN 2 M R (i1 + p + 1) = 4)
    (hsE : neP0 2 M R + stN 2 M R (i1 + p) = 4 * uE) (hsO : neP0 2 M R + stN 2 M R (i1 + p + 1) = 4 * (uE + 1))
    {es : Fin (nN 2 M R) → ℝ} (hes : es ∈ Vsub (rowOfN 2 M R)) (τ : ℝ) :
    (inner ℝ (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by omega) (neS 2 M R)) (zfield (gbar uE)))
      (Ring.inverse (GenP.Nmat (Pt 2 M R (by norm_num) (neC0 2 M R) t a))
        (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by omega) (neS 2 M R)) (zfield (gbar uE)))) : ℝ) ≤
      c0 * ((((scaleUp 2 2 (neLu M R)) 1 + 1) * ((scaleUp 2 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (neC0 2 M R - neP0 2 M R) (Real.cos (2 * t)) (f0pair (nGeo_two (le_refl 2) hdvd hM hR) i1 p hp + τ • es) +
      (inner ℝ (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by omega) (neS 2 M R)) (zfield (gbar uE)))
        (diagW (geomOf 2 2 (neS 2 M R)) (massW (geomOf 2 2 (neS 2 M R)) a)
          (ContinuousLinearMap.adjoint (tauExt 2 2 (neLu M R) (by omega) (neS 2 M R)) (zfield (gbar uE)))) : ℝ) := by
  have hz := zblock_ineq (le_refl 2) (by norm_num) hdvd hM hR t a ht hG1 hN hpsd (f0pair (nGeo_two (le_refl 2) hdvd hM hR) i1 p hp + τ • es)
  rw [Qx_pair hdvd hM hR t a ht hp hlnE hlnO hsE hsO hes τ] at hz
  rw [tauAdj_zfield_eq (le_refl 2) hdvd hM hR]
  exact hz

end

end AdalyFormal.NcwdhTwo

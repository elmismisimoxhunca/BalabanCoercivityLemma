import NuE3
import SoE2
import NuE2

/-!
# NuE3 -- the Z-energy of a chain vector: `<x_e, G1inv x_e> = c0 T1 qF1 e + K(e)` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.SitesOnly

open AdalyFormal.NcwdhTwo

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)

section
variable [CfData]
variable {ell M R : ℕ}
variable {C : ℕ} (hCp : CPos ell M R C)
include hCp

theorem inner_G1inv_zfield0 (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e)
        ((Pt ell M R (by omega) (C) t a).G1inv (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e)) : ℝ) =
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (C - neP0 ell M R) (Real.cos (2 * t)) e +
      (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (CoverOmega.Wt ell (isRowN ell M R) (fun j u => a * fSum ell j (fe (neP0 ell M R) e) u))) : ℝ) := by
  have hf := (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e).2
  have hG := G1inv_zfield0 hCp hell2 hE hdvd hM hR t a ht e hf
  have hxe : (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e) = ⟨zfield (fe (neP0 ell M R) e), hf⟩ := rfl
  rw [Submodule.coe_inner]
  have hco : (((Pt ell M R (by omega) (C) t a).G1inv (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e) :
      ↥(bondSupp (Pt ell M R (by omega) (C) t a).G)) : BondFnL2 (scaleUp ell 2 (neLu M R))) =
      zfield (ginvProf0 ell (isRowN ell M R) (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0)
        (C) t a (fe (neP0 ell M R) e)) := by
    rw [hxe]; exact hG
  rw [hco]
  show (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) _ : ℝ) = _
  unfold ginvProf0
  rw [zfield_add', inner_add_right]
  rw [Dpi_energy1 hell2 hdvd hM hR hCp.hge hCp.hlt t e]

end

#print axioms inner_G1inv_zfield0

end AdalyFormal.SitesOnly

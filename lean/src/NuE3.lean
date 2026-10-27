import NuE2

/-!
# NuE3 -- the Z-energy of a chain vector: `<x_e, G1inv x_e> = c0 T1 qF1 e + K(e)` (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

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

/-- the chain Z-field as an element of `E_0`. -/
noncomputable def xE (hg : NGeo ell M R) (hell3 : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (e : Fin (nN ell M R) → ℝ) :
    ↥(bondSupp (geomOf ell 2 (neS ell M R))) :=
  ⟨zfield (fe (neP0 ell M R) e), by
    refine zfield_mem_bondSupp _ (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) ?_ _ ?_
    · ext x; simp only [geomOf, Set.mem_setOf_eq]; exact neS_om0 x
    · intro v _ hv
      apply fe_supp
      unfold nN; intro h; apply hv; omega⟩

theorem inner_G1inv_zfield0 (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (ht : |t| < Real.pi / 2) (e : Fin (nN ell M R) → ℝ) :
    (inner ℝ (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e)
        ((Pt ell M R (by omega) (neC0 ell M R) t a).G1inv (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e)) : ℝ) =
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF1 (neC0 ell M R - neP0 ell M R) (Real.cos (2 * t)) e +
      (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (CoverOmega.Wt ell (isRowN ell M R) (fun j u => a * fSum ell j (fe (neP0 ell M R) e) u))) : ℝ) := by
  have hf := (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e).2
  have hG := G1inv_zfield0 hell2 hE hdvd hM hR t a ht e hf
  have hxe : (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e) = ⟨zfield (fe (neP0 ell M R) e), hf⟩ := rfl
  rw [Submodule.coe_inner]
  have hco : (((Pt ell M R (by omega) (neC0 ell M R) t a).G1inv (xE (nGeo_two hell2 hdvd hM hR) hell2 hM hR e) :
      ↥(bondSupp (Pt ell M R (by omega) (neC0 ell M R) t a).G)) : BondFnL2 (scaleUp ell 2 (neLu M R))) =
      zfield (ginvProf0 ell (isRowN ell M R) (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) (scaleUp ell 2 (neLu M R) 0)
        (neC0 ell M R) t a (fe (neP0 ell M R) e)) := by
    rw [hxe]; exact hG
  rw [hco]
  show (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R))) _ : ℝ) = _
  unfold ginvProf0
  rw [zfield_add', inner_add_right]
  rw [Dpi_energy1 hell2 hdvd hM hR (neC0_ge_P0 hell2 hM hR) (neC0_lt_Q0 hell2 hM hR) t e]

end

end AdalyFormal.NcwdhTwo

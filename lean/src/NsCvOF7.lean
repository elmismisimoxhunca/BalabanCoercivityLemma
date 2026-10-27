import NsCvOF6

/-!
# CvOF7 -- the energy of the saddle: `<x, G1inv x> = c0 T1 qF_c(e) + <Q x, zrow (a fSum)>` (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem inner_Wt_split (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t a : ℝ)
    (e : Fin (nN ell M R) → ℝ)
    (hrad : ∀ d : Fin (nN ell M R) → ℝ, d ∈ Vsub (rowOfN ell M R) → BF (neC ell M R - neP0 ell M R) (Real.cos t) e d = 0) :
    (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (Wt ell (isRowN ell M R) (rhoV ell M R (neC ell M R - neP0 ell M R) (Real.cos t) a e))) : ℝ) =
      c0 * ((((scaleUp ell 2 (neLu M R)) 1 + 1) * ((scaleUp ell 2 (neLu M R)) 2 + 1) : ℕ) : ℝ) *
        qF (neC ell M R - neP0 ell M R) (Real.cos t) e +
      (inner ℝ (zfield (fe (neP0 ell M R) e) : BondFnL2 (scaleUp ell 2 (neLu M R)))
        (zfield (Wt ell (isRowN ell M R) (fun j u => a * fSum ell j (fe (neP0 ell M R) e) u))) : ℝ) := by
  rw [← Dpi_energy hell3 hdvd hM hR t e, inner_zfield_zfield, inner_zfield_zfield, inner_zfield_zfield, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hv' : v ≤ scaleUp ell 2 (neLu M R) 0 := by have := Finset.mem_range.mp hv; omega
  have := ginv_eq_Wt hell3 hdvd hM hR t a e hrad v hv'
  unfold ginvProf at this
  rw [← mul_add]
  congr 1
  rw [← this]

#print axioms inner_Wt_split

end AdalyFormal.CoverOmega

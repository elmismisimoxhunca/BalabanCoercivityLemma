import NsCvO27
import GCz1

/-!
# CvO28 -- the constant Cartan gauge `h = cartan (pi/2)`: every ingredient of the genuine family commutes with `Ad_h` on a Cartan configuration (lane omega)

From the gauge-covariance library (`GCz1.bondEqv_gauge`, `BondEqv.baseEqv`) with the constant gauge `gamma = h` and `U` Cartan (`h U h^-1 = U`).
`Ad_h` fixes exactly the sigma_3-valued fields; so every operator maps sigma_3-valued fields to sigma_3-valued fields (charge conservation).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

theorem isCartan_comm {V W : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) (hW : IsCartan W) : V * W = W * V := by
  apply Subtype.ext
  obtain ⟨a1, a2⟩ := hV
  obtain ⟨b1, b2⟩ := hW
  show (V : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = (W : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, a1, a2, b1, b2, mul_comm]

/-- the constant gauge `h = cartan (pi/2)`. -/
noncomputable def hGauge (L : PeriodicLatticeExtent) : GaugeFn L := fun _ => cartan (Real.pi / 2)

theorem gaugeTransform_hGauge {L : PeriodicLatticeExtent} {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hU : CartanCfg U) : periodicGaugeTransform (hGauge L) U = U := by
  funext e
  unfold periodicGaugeTransform hGauge
  rw [isCartan_comm (cartan_isCartan _) (hU e), mul_assoc, mul_inv_cancel, mul_one]

#print axioms gaugeTransform_hGauge

end AdalyFormal.CoverOmega

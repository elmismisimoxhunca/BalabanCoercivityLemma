import NtCvO33

/-!
# CvO34 -- `Delta2` vanishes on sigma_3-valued fields; `G1inv = Ginv` there (lane omega)

Abstract in the family `P : IngrBParams` with Cartan `P.U` and `C^{(2)}` vanishing on sigma_3-valued fields.
`Delta2` is `Ad_h`-equivariant (`G1inv = Ginv - Delta2`, both equivariant by the gauge library); a sigma_3-valued `x` is `Ad_h`-fixed, so `Delta2 x` is sigma_3; polarisation of
`<u, Delta2 u> = 2 <H C2 u, J> = 0` on all `Ad_h`-fixed `u` gives `<w, Delta2 x> = 0` for every `w`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.CoverNested (cartan cartan_coe)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.GaugeCov
open AdalyFormal.IngredientFamilyR2

variable {L : PeriodicLatticeExtent}

theorem adBL_hGauge_apply (x : BondFnL2 L) (b : Bond L) : (adBL (hGauge L) x) b = RMap (cartan (Real.pi / 2)) (x b) := rfl

theorem adBL_hGauge_fixed_iff (x : BondFnL2 L) : adBL (hGauge L) x = x ↔ SigB (WithLp.ofLp x) := by
  constructor
  · intro h b
    have := congrArg (fun z : BondFnL2 L => z b) h
    simp only [adBL_hGauge_apply] at this
    exact (RMap_h_fixed_iff _).mp this
  · intro h
    refine PiLp.ext (fun b => ?_)
    rw [adBL_hGauge_apply]
    exact (RMap_h_fixed_iff _).mpr (h b)

theorem adEL_hGauge_fixed_iff (G : TowerGeom L) (x : ↥(bondSupp G)) :
    adEL (hGauge L) G x = x ↔ SigB (WithLp.ofLp (x : BondFnL2 L)) := by
  rw [← adBL_hGauge_fixed_iff]
  constructor
  · intro h; have := congrArg (fun z : ↥(bondSupp G) => (z : BondFnL2 L)) h; exact this
  · intro h; exact Subtype.ext h

theorem adBL_hGauge_sq (x : BondFnL2 L) : adBL (hGauge L) (adBL (hGauge L) x) = x := by
  refine PiLp.ext (fun b => ?_)
  rw [adBL_hGauge_apply, adBL_hGauge_apply]
  exact RMap_h_sq _

theorem adEL_hGauge_sq (G : TowerGeom L) (x : ↥(bondSupp G)) : adEL (hGauge L) G (adEL (hGauge L) G x) = x :=
  Subtype.ext (adBL_hGauge_sq (x : BondFnL2 L))

end AdalyFormal.CoverOmega

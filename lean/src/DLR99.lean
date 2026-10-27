import DLR98

/-!
# DL99 -- control: the curvature conclusion of the witnesses can FAIL (the flat field has `dv = 0` on every plaquette)

`flat_dv_zero L p` : for the constant field `U ≡ 1` every plaquette holonomy is `1`, so `dv = frobNorm (1 − 1) = 0`;
`flat_not_curved L` : `¬ ∃ p, 0 < dv (hol 1 p)`.  Hence `witness_curved`, `M0Core_two_domain_nonempty`, `M0Core_domain_curved`
assert something the flat member of the same class (it is in `GlobalRegular2` too, MC/ZGU1K) does not satisfy.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CurvBlock (dv)

theorem flat_dv_zero (L : PeriodicLatticeExtent) (p : PeriodicLatticePlaquette L) :
    dv (periodicPlaquetteHolonomy (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) p) = 0 := by
  unfold dv periodicPlaquetteHolonomy
  simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]

theorem flat_not_curved (L : PeriodicLatticeExtent) :
    ¬ ∃ p : PeriodicLatticePlaquette L,
      0 < dv (periodicPlaquetteHolonomy (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) p) := by
  rintro ⟨p, hp⟩
  rw [flat_dv_zero] at hp
  exact lt_irrefl 0 hp

#print axioms flat_dv_zero
#print axioms flat_not_curved

end AdalyFormal.DLayer

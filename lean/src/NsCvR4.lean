import CvR3
import NsCvNe3

/-!
# CvR4 -- the Cartan layer path is a Cartan configuration (lane cover_jacobi_20261016)

`neU ell M R t` (CvNe3: Cartan angle `t` on the direction-1 bonds of the layer, `1` elsewhere) satisfies `CartanCfg`, so the
pilot results of CvR2/CvR3 (the `sigma_3` block of the covariant gradient and of `Delta_U = D* D` is the flat one) apply
to the genuine path of `LayerPoleAt`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested

theorem cartan_isCartan (t : ℝ) : IsCartan (cartan t) := by
  unfold IsCartan
  simp [cartan_coe]

theorem layerCfg_cartan {L : PeriodicLatticeExtent} (c : ℕ) {v : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hv : IsCartan v) :
    CartanCfg (layerCfg (L := L) c v) := by
  intro e
  unfold layerCfg
  split_ifs
  · exact hv
  · unfold IsCartan; simp

theorem neU_cartan (ell M R : ℕ) (t : ℝ) : CartanCfg (neU ell M R t) :=
  layerCfg_cartan _ (cartan_isCartan t)


#print axioms cartan_isCartan
#print axioms layerCfg_cartan
#print axioms neU_cartan

end AdalyFormal.CoverJacobi

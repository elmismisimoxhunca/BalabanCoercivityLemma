import TL9e
import TL3e

/-!
# TL10a -- `Δ'_a`, `lapDir`, `N(Q')` and `R`
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2

section rr
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) {ell k : ℕ}

theorem desc_lapFull (U : Cfg L) :
    Desc (covS h) (covS h) (lapFull U) (lapFull (pullCfg h (fun _ => 0) U)) :=
  (desc_gradL2 h U).comp (desc_gradAdj h U)

theorem desc_Qpa [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ) :
    Desc (covS h) (covS h) (Qpa (geomOf ell k S) U a)
      (Qpa (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a) := by
  rw [Qpa_eq, Qpa_eq]
  exact (desc_QlevStack h hp hell S U).comp
    ((desc_diagOp (covLamIdx h S hp) (fun p : LamIdx (geomOf ell k S) => ajSeq a ell p.1 * (ell : ℝ) ^ (p.1 : ℕ))).comp
      (desc_QlevStack h hp hell S U).adjoint)

open Classical in
theorem desc_lapDir [Nonempty (DeckIdx Lt L)] (S : Tower L) (U : Cfg L) :
    Desc (covS h) (covS h) (lapDir (geomOf ell k S) U)
      (lapDir (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U)) :=
  (desc_siteMask h (S.Om 0)).comp ((desc_lapFull h U).comp (desc_siteMask h (S.Om 0)))

open Classical in
theorem desc_DelpA [Nonempty (DeckIdx Lt L)] (hp : PhiOK h (fun _ => 0) (ell ^ k)) (hell : 0 < ell) (S : Tower L) (U : Cfg L) (a : ℝ) :
    Desc (covS h) (covS h) (DelpA (geomOf ell k S) U a)
      (DelpA (geomOf ell k (towerPull h (fun _ => 0) S)) (pullCfg h (fun _ => 0) U) a) :=
  (desc_siteMask h (S.Om 0)).comp (((desc_lapFull h U).add (desc_Qpa h hp hell S U a)).comp (desc_siteMask h (S.Om 0)))

end rr


end AdalyFormal.Thin

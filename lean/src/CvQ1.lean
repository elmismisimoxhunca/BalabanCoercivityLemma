import CvD1
import AdalyFormal.Balaban.QjComposite

/-!
# CvQ1 -- the composite averaging `Q'_j` on the sigma_3 block of a Cartan background tower (lane cover_jacobi_20261016)

If every level `bg l` of the background tower is Cartan-valued, then the sigma_3 (diagonal) part of `Q'_j(bg) lam` is the FLAT composite block
average of the sigma_3 part of `lam`:  `diagP (Qcomposite bg ell j lam y) = flatQ ell j (diagP o lam) y`, where `flatQ` iterates
`flatAvg s ell lam y = ell^{-3} sum_{x in stepBlockOf y s ell} lam x` (no transport).  Proof: every transport `R(hol)` is a Cartan adjoint
action, which fixes `diagP`.  Whether the genuine tower `UbarTower su2LogExp ell U` of a Cartan `U` is Cartan is the next module (CvQ2).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.QjComposite
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)

variable {L : PeriodicLatticeExtent}

theorem coarsePathHolonomy_cartan {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : CartanCfg V)
    (s : ℕ) (y : PeriodicLatticeSite L) (path : List (Fin 3)) : IsCartan (coarsePathHolonomy s V y path) := by
  induction path generalizing y with
  | nil => exact isCartan_one
  | cons μ rest ih =>
    show IsCartan (V (y, μ) * coarsePathHolonomy s V _ rest)
    exact isCartan_mul (hV _) (ih _)

theorem stepAverage_diagP {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : CartanCfg V)
    (s ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    diagP (stepAverage s V ell lam y) = (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell, diagP (lam x) := by
  unfold stepAverage
  rw [map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => diagP_RMap (coarsePathHolonomy_cartan hV _ _ _) _)

/-- the flat (transport-free) strided block average. -/
noncomputable def flatAvg (s ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) : SuTwo :=
  (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell, lam x

/-- the flat composite: `ell`-block averages at strides `ell^0, ell^1, ...`. -/
noncomputable def flatQ (ell : ℕ) : ℕ → (PeriodicLatticeSite L → SuTwo) → (PeriodicLatticeSite L → SuTwo)
  | 0 => fun lam => lam
  | (j + 1) => fun lam => flatAvg (ell ^ j) ell (flatQ ell j lam)

theorem Qcomposite_diagP {bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hbg : ∀ l, CartanCfg (bg l)) (ell : ℕ) :
    ∀ (j : ℕ) (lam : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L),
      diagP (Qcomposite bg ell j lam y) = flatQ ell j (fun x => diagP (lam x)) y := by
  intro j
  induction j with
  | zero => intro lam y; rfl
  | succ j ih =>
    intro lam y
    show diagP (stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j lam) y) = flatAvg (ell ^ j) ell (flatQ ell j (fun x => diagP (lam x))) y
    rw [stepAverage_diagP (hbg j)]
    unfold flatAvg
    congr 1
    exact Finset.sum_congr rfl (fun x _ => ih lam x)

#print axioms coarsePathHolonomy_cartan
#print axioms stepAverage_diagP
#print axioms flatAvg
#print axioms flatQ
#print axioms Qcomposite_diagP

end AdalyFormal.CoverJacobi

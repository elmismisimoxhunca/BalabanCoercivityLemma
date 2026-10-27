import CvQ1
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.SuTwoLogExpCore

/-!
# CvQ2 -- the genuine background tower of a Cartan configuration is Cartan (lane cover_jacobi_20261016)

`UbarTower su2LogExp ell U l` is Cartan-valued for every `l` when `U` is (no branch/angle hypothesis needed): `su2Log` of a diagonal element
is a diagonal matrix, `su2Exp` of a diagonal matrix is a diagonal element of `SU(2)` (either `exp D`, or `1` when the guard fails),
and products/inverses of Cartan elements are Cartan.  With CvQ1: the sigma_3 block of `Q'_j(U)` is the flat composite block average,
for every Cartan `U` (hence along the whole Cartan layer path), for every `t`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.UbarTowerCov
open AdalyFormal.Balaban.QjComposite
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)

variable {L : PeriodicLatticeExtent}

/-- a diagonal `2x2` complex matrix. -/
def DiagM (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop := M 0 1 = 0 ∧ M 1 0 = 0

theorem su2Log_diag {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hg : IsCartan g) : DiagM (su2Log g) := by
  obtain ⟨h1, h2⟩ := hg
  unfold DiagM su2Log
  simp [Matrix.conjTranspose_apply, h1, h2]

theorem diagM_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 2) (Fin 2) ℂ) (h : ∀ i ∈ s, DiagM (f i)) :
    DiagM (∑ i ∈ s, f i) := by
  unfold DiagM at *
  constructor
  · rw [Matrix.sum_apply]; exact Finset.sum_eq_zero (fun i hi => (h i hi).1)
  · rw [Matrix.sum_apply]; exact Finset.sum_eq_zero (fun i hi => (h i hi).2)

theorem diagM_qsmul (q : ℚ) {M : Matrix (Fin 2) (Fin 2) ℂ} (h : DiagM M) : DiagM (q • M) := by
  obtain ⟨h1, h2⟩ := h
  unfold DiagM
  simp [h1, h2]

theorem su2Exp_cartan {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : DiagM D) : IsCartan (su2Exp D) := by
  classical
  by_cases h : NormedSpace.exp D ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  · rw [IsCartan, su2Exp_of_mem h]
    have hDd : D = Matrix.diagonal (fun i => D i i) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, hD.1, hD.2]
    rw [hDd, Matrix.exp_diagonal]
    simp [Matrix.diagonal_apply]
  · rw [su2Exp_of_not_mem h]
    exact isCartan_one

theorem inv_cartan' {g : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hg : IsCartan g) : IsCartan g⁻¹ := isCartan_inv hg

theorem stridedBlockedGauge_cartan {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hV : CartanCfg V)
    (s ell : ℕ) (c : PeriodicLatticeEdge L) : IsCartan (stridedBlockedGauge su2LogExp s ell V c) := by
  unfold stridedBlockedGauge
  have hb : IsCartan (coarseBondVar s ell V c) := coarsePathHolonomy_cartan hV _ _ _
  have hloop : ∀ x, IsCartan (loopVar s ell V c x) := by
    intro x
    unfold loopVar gammaVarStrided
    exact isCartan_mul (isCartan_mul (isCartan_mul (coarsePathHolonomy_cartan hV _ _ _) (coarsePathHolonomy_cartan hV _ _ _))
      (isCartan_inv (coarsePathHolonomy_cartan hV _ _ _))) (isCartan_inv hb)
  refine isCartan_mul ?_ hb
  simp only [su2LogExp_exp, su2LogExp_log]
  apply su2Exp_cartan
  exact diagM_sum _ _ (fun x _ => diagM_qsmul _ (su2Log_diag (hloop x)))

theorem UbarTower_cartan {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U) (ell : ℕ) :
    ∀ l, CartanCfg (UbarTower su2LogExp ell U l) := by
  intro l
  induction l with
  | zero => exact hU
  | succ l ih => intro c; exact stridedBlockedGauge_cartan ih _ _ c

#print axioms su2Log_diag
#print axioms diagM_sum
#print axioms diagM_qsmul
#print axioms su2Exp_cartan
#print axioms stridedBlockedGauge_cartan
#print axioms UbarTower_cartan

end AdalyFormal.CoverJacobi

import NsCvO32

/-!
# CvO33 -- `C^{(2)}` vanishes on sigma_3-valued fields along the staggered path (genuine `C2fullOf`) (lane omega)
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
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.UbarTowerCov (UbarTower)

variable {L : PeriodicLatticeExtent}

/-- a bond field of diagonal su(2) elements. -/
def SigB (A : Bond L → SuTwo) : Prop := ∀ b, diagP (A b) = A b

/-- coordinates of a sigma_3-valued field. -/
noncomputable def thetaOf (A : Bond L → SuTwo) : PeriodicLatticeEdge L → ℝ := fun b => (fromM2 ((A b : SuTwo) : M2)) 0

theorem suCoord_sig (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) : suCoord A = aF (thetaOf (WithLp.ofLp A)) := by
  funext b
  have h := hA b
  have h01 : ((A b : SuTwo) : M2) 0 1 = 0 := by
    have := congrArg (fun Z : SuTwo => (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1) h
    simp only [diagP_coe, Matrix.diagonal_apply] at this
    simpa using this.symm
  ext i
  fin_cases i
  · rfl
  · simp [suCoord, aF, fromM2, h01]
  · simp [suCoord, aF, fromM2, h01]

theorem C2rawB_sig (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1)
    (G : TowerGeom L) (hG : G.ell = ell) (j : ℕ) (hj : j ≤ 2) (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    C2rawB G (stagCfg c t) j A = 0 := by
  have hreg := stag_regTower_u hN hE hell c t htπ hc1 hc2
  have e : bgTower G (stagCfg c t : Cfg L) = UbarTower su2LogExp ell (stagCfg c t : PeriodicLinkConfiguration SU2 L) := by
    unfold bgTower; rw [hG]
  obtain ⟨-, -, c1, c2⟩ := stag_levels_sigma3 hN hE hell c t htπ hc1 hc2 (thetaOf (WithLp.ofLp A))
  rw [C2rawB_eq, e, hG, C2CompL_eq_C2CompX2 ell _ 2 hreg j hj, suCoord_sig A hA]
  interval_cases j
  · rw [C2CompX_zero]; ext b; simp [suCoordInv]
  · rw [c1]; ext b; simp [suCoordInv]
  · rw [c2]; ext b; simp [suCoordInv]

theorem C2fullOf_sig (hN : 2 ∣ L 1 + 1) {ell : ℕ} (hE : StagPar L ell) (hell : 0 < ell)
    (c : ℕ) (t : ℝ) (htπ : |t| < tcap ell) (hc1 : ell ≤ c) (hc2 : c + ell * ell < L 0 + 1)
    (G : TowerGeom L) (hG : G.ell = ell) (hk : G.k = 2) (A : BondFnL2 L) (hA : SigB (WithLp.ofLp A)) :
    C2fullOf G (stagCfg c t) A = 0 := by
  refine PiLp.ext (fun p => ?_)
  have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; omega
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G (stagCfg c t) p.1 A)) p.2.1 = 0
  rw [C2rawB_sig hN hE hell c t htπ hc1 hc2 G hG p.1 hj A hA]
  simp

#print axioms suCoord_sig
#print axioms C2rawB_sig
#print axioms C2fullOf_sig

end AdalyFormal.CoverOmega

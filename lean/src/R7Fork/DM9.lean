import R7Fork.DM8

/-!
# DM9 -- EXACT EQUIVALENCE at a flat proper tower with a nonzero class element:
   `InstIneq (gamma0 = 1/1728)  <=>  IsUnit G1inv`.
(=>) `InstIneq` forces `IsUnit N` (`unit_N_of_instIneq`), and `N = Q (Ring.inverse G1inv) Q*` is `0` when `G1inv` is not a unit (and `L^2(frakB)` is nontrivial).
(<=) `closed_point_proper`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000
namespace AdalyFormal.DirichletMono

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (OnLambdaT TT)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

/-- if `G1inv` is not a unit then `N = 0` -/
theorem Nmat_zero_of_not_unit (P : IngrBParams) (hG : ¬ IsUnit P.G1inv) : GenP.Nmat P = 0 := by
  have h : P.data.G1 P.G1inv = 0 := Ring.inverse_non_unit _ hG
  ext1 x
  simp [GenP.Nmat, h]

theorem unit_G1inv_of_unit_N (P : IngrBParams) (hne : Nonempty (BIdx P.G)) (hN : IsUnit (GenP.Nmat P)) :
    IsUnit P.G1inv := by
  by_contra hG
  rw [Nmat_zero_of_not_unit P hG] at hN
  have h01 : (0 : FSp P.G →L[ℝ] FSp P.G) = 1 := isUnit_zero_iff.mp hN
  obtain ⟨β⟩ := hne
  have hv : (WithLp.toLp 2 (Pi.single β suTwoWitness) : FSp P.G) ≠ 0 := by
    intro h
    have := congrFun (congrArg WithLp.ofLp h) β
    simp at this
    exact suTwoWitness_ne_zero this
  apply hv
  have := congrArg (fun T : FSp P.G →L[ℝ] FSp P.G => T (WithLp.toLp 2 (Pi.single β suTwoWitness))) h01
  simpa using this.symm

/-- a class element with nonzero energy gives a bond of `frakB` -/
theorem bidx_nonempty_of_class {ell M R k : ℕ} (hell : 0 < ell) {Lu : PeriodicLatticeExtent}
    (hu : ∀ μ, 1 ≤ Lu μ) (hMR : 1 ≤ R * M) {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
    {Lam : Set (PeriodicLatticeSite Lu)} (hL : LambdaOK ell M R k S Lam)
    (hne : ∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) :
    Nonempty (BIdx (geomOf ell k S)) := by
  obtain ⟨Bt, -, hBT, hpos⟩ := hne
  have : ∃ e : Bond Lu, Bt e ≠ 0 := by
    by_contra h
    push_neg at h
    have : bondEnergy Bt = 0 := by
      unfold bondEnergy; simp [h]
    linarith
  obtain ⟨e, he⟩ := this
  have htouch : e.1 ∈ Lam ∨ periodicLatticeShift e.1 e.2 ∈ Lam := by
    by_contra hnt
    exact he (hBT e hnt)
  have hb := touching_in_frakB hell hu hMR hS hL e htouch
  exact ⟨⟨Fin.last k, ⟨unitBondEmb ell k Lu hell e, hb⟩⟩⟩

/-- **THE EXACT STATEMENT at the multi-stratum proper tower `TT`:** the frozen inequality with `gamma0 = 1/1728` holds iff `G1inv` is invertible. -/
theorem tt_instIneq_iff_G1inv_unit {Lu : PeriodicLatticeExtent} (hLu : ∀ μ, Lu μ + 1 = 60) (hell : 0 < 2)
    (a : ℝ) (ha : 0 < a) :
    InstIneq 2 1 hell a Lu (1 / 1728 : ℝ) (TT (scaleUp 2 1 Lu)) (LamT Lu) flatCfg ↔
      IsUnit (gparams 2 1 Lu hell (TT (scaleUp 2 1 Lu)) flatCfg a (LamT Lu)).G1inv := by
  obtain ⟨h4, hd, hRM, hadm, hLam, -, hB⟩ := tt_hypotheses hLu
  constructor
  · intro hI
    have hN := unit_N_of_instIneq hell a (1 / 1728) ha (by norm_num) _ _ hI hB
    have hbi := bidx_nonempty_of_class hell (fun μ => by have := hLu μ; omega) (le_trans (by norm_num) hRM) hadm
      hLam.1 hB
    exact unit_G1inv_of_unit_N _ hbi hN
  · intro hG
    exact tt_floor hLu hell a ha hG

#print axioms unit_G1inv_of_unit_N
#print axioms bidx_nonempty_of_class
#print axioms tt_instIneq_iff_G1inv_unit

end AdalyFormal.DirichletMono

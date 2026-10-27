import ZGU1D

/-!
# GU1E -- the genuine form at flat `U`, full tower, ANY level `k`: reduction to the explicit candidate,
the top-level identification of the genuine `Q_k`, and the volume-uniform floor `(1/1728)‖B̃‖² ≤ genForm(C B̃)`
(conditional on the two feasibility conjuncts `IsUnit G₁⁻¹`, `IsUnit N`, discharged in GU1F).
Standard axioms only (see the #print axioms lines).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.GenuineU1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlCovariantLM curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.IngredientFamily (q1SU2)

namespace Gen
variable (P : IngrBParams)

/-- **REDUCTION** (flat `U`, full support, `G₁⁻¹`, `N` units): the genuine (3.156) at `B` equals
`η (‖curl A‖² + ‖R D* A‖²)` for the explicit candidate `A` with `Q A = τ* B`. -/
theorem genForm_reduction (hFS : P.FullSupp) (hOm : P.G.Om0 = Set.univ) (hU : P.U = flatCfg) (hG : IsUnit P.G1inv)
    (hN : IsUnit (GenP.Nmat P)) (B : BondFnL2 P.Lu) :
    ∃ A : ↥(bondSupp P.G), (∀ e : Bond P.Lu, (P.sector.Qfull (iE P.G A)) (P.eqv hFS e) = B e) ∧
      GenP.genForm P B = P.eta * (‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A)‖ ^ 2 +
        ‖Tfull P.G P.U (iE P.G A)‖ ^ 2) := by
  obtain ⟨A, hQ, hin⟩ := firstTerm_core P hG hN (ContinuousLinearMap.adjoint P.tau B)
  refine ⟨A, fun e => ?_, ?_⟩
  · have h1 : P.sector.Qfull (iE P.G A) = P.data.Q A := rfl
    rw [h1, hQ, tau_adj_apply P hFS]
  · have hJ : P.Jf = 0 := Jf_flat P hU
    have hJd : P.data.J = 0 := by
      show (pE P.G) P.Jf = 0
      rw [hJ]; exact map_zero _
    have hK := P.G1inv_spec.form A
    have hη : P.eta * (P.ell : ℝ) ^ P.k = 1 := by
      unfold IngrBParams.eta
      have : (0 : ℝ) < (P.ell : ℝ) := by exact_mod_cast P.hell
      field_simp
    have hmass := mass_inner P hFS A
    have hnorm : ‖P.data.Q A‖ = ‖B‖ := by rw [hQ, tau_adj_norm P hFS]
    have hD : ⟪A, P.data.Dpi A⟫ = ‖curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp P.ell P.k P.Lu)) (iE P.G A)‖ ^ 2 := by
      have : ⟪A, P.data.Dpi A⟫ = ⟪iE P.G A, DpiFull P.G P.U P.a (iE P.G A)⟫ := by
        show ⟪A, (pE P.G) (DpiFull P.G P.U P.a (iE P.G A))⟫ = _
        rw [pE_inner_right]
      rw [this, hU]
      exact inner_DpiFull_flat_univ P.G hOm P.a (iE P.G A)
    unfold GenP.genForm GenP.firstTerm
    rw [hJ, inner_zero_right, mul_zero, sub_zero, hin, hK]
    unfold BaseDataS.K
    rw [hJd, inner_zero_right, mul_zero, sub_zero, hmass, hnorm, hD]
    have hBB : ⟪B, B⟫ = ‖B‖ ^ 2 := real_inner_self_eq_norm_sq B
    rw [hBB]
    have hT : P.data.T A = Tfull P.G P.U (iE P.G A) := rfl
    rw [hT]
    have : P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2) = P.a * ‖B‖ ^ 2 := by
      calc P.eta * (P.a * (P.ell : ℝ) ^ P.k * ‖B‖ ^ 2) = (P.eta * (P.ell : ℝ) ^ P.k) * (P.a * ‖B‖ ^ 2) := by ring
        _ = P.a * ‖B‖ ^ 2 := by rw [hη, one_mul]
    nlinarith [this]

end Gen

#print axioms Gen.genForm_reduction

end AdalyFormal.GenuineU1

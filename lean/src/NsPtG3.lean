import NsPtG2

/-!
# PtG3 -- the kernel field is globally curl-free (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

variable {ell M R : ℕ}

theorem KD.curl_zero {x : BondFnL2 (scaleUp ell 2 (neLu M R))} (hk : KD ell M R x) (hP : PGeo ell M R) :
    curlCovariantCLM_L2 (flatCfg : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) (scaleUp ell 2 (neLu M R))) x = 0 := by
  have hg : NGeo ell M R := nGeo hP.hell hP.hdell hP.hM hP.hR
  refine PiLp.ext (fun p => ?_)
  rw [curl_flat_apply]
  by_cases hp : p ∈ plaqIn (geomOf ell 2 (neS ell M R)).Om0
  · have h := congrFun (congrArg WithLp.ofLp hk.hc) p
    rw [AdalyFormal.StatementLaneR6.plaqMask_apply, if_pos hp] at h
    rw [← curl_flat_apply]
    simpa using h
  · have hz : ∀ e ∈ periodicPlaquetteBoundaryEdges p, x e = 0 := by
      intro e he
      by_contra hne
      apply hp
      refine plaq_of_touch hP p e he ?_
      by_contra hno
      push_neg at hno
      exact hne (hk.zero_off1 hg hP.hM e hno.1 hno.2)
    obtain ⟨w, ⟨⟨μ, ν⟩, hlt⟩⟩ := p
    have e1 : (w, μ) ∈ periodicPlaquetteBoundaryEdges (w, (⟨(μ, ν), hlt⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections)) := by
      simp [periodicPlaquetteBoundaryEdges]
    have e2 : (periodicLatticeShift w μ, ν) ∈ periodicPlaquetteBoundaryEdges (w, (⟨(μ, ν), hlt⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections)) := by
      simp [periodicPlaquetteBoundaryEdges]
    have e3 : (periodicLatticeShift w ν, μ) ∈ periodicPlaquetteBoundaryEdges (w, (⟨(μ, ν), hlt⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections)) := by
      simp [periodicPlaquetteBoundaryEdges]
    have e4 : (w, ν) ∈ periodicPlaquetteBoundaryEdges (w, (⟨(μ, ν), hlt⟩ : AdalyFormal.Target.ClayStatement.PeriodicPlaquetteDirections)) := by
      simp [periodicPlaquetteBoundaryEdges]
    have z1 := hz _ e1
    have z2 := hz _ e2
    have z3 := hz _ e3
    have z4 := hz _ e4
    simp only [flatCurlValue]
    show (WithLp.ofLp x (w, μ)) + (WithLp.ofLp x (periodicLatticeShift w μ, ν)) - (WithLp.ofLp x (periodicLatticeShift w ν, μ))
      - (WithLp.ofLp x (w, ν)) = 0
    have z1' : (WithLp.ofLp x (w, μ)) = 0 := z1
    have z2' : (WithLp.ofLp x (periodicLatticeShift w μ, ν)) = 0 := z2
    have z3' : (WithLp.ofLp x (periodicLatticeShift w ν, μ)) = 0 := z3
    have z4' : (WithLp.ofLp x (w, ν)) = 0 := z4
    rw [z1', z2', z3', z4']; simp

#print axioms KD.curl_zero

end AdalyFormal.CoverOmega

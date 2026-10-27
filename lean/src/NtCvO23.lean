import NtCvO22
import ZLocOps
import CvD2

/-!
# CvO23 -- `Δ'` (localised, source-normalised) with ONE sigma_3 argument, on a Cartan configuration (lane omega)

For `U` Cartan and `z : Bond L → SuTwo` sigma_3-valued (`diagP (z b) = z b`), and an ARBITRARY bond field `w`:
* the commutator part of the bilinear form vanishes in both orders (`secondBilPlaq U p w z = secondBilPlaq U p z w = 0`),
* `deltaPrimeBilNormLoc U P w z = Σ_{p ∈ P} (holCos U p - 1) · ⟨curl_U w (p), curl_U z (p)⟩`.
Together with `inner_deltaKLocCLM` this gives `⟨w, Δ z⟩ = Σ_{p∈P} holCos U p · ⟨curl w(p), curl z(p)⟩` for EVERY `w` (charged and non-constant included).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent}

/-- a matrix with vanishing off-diagonal entries. -/
def IsDiagMat (D : Matrix (Fin 2) (Fin 2) ℂ) : Prop := D 0 1 = 0 ∧ D 1 0 = 0

theorem trace_diag_swap (X D M : Matrix (Fin 2) (Fin 2) ℂ) (hD : IsDiagMat D) (hM : IsDiagMat M) :
    Matrix.trace (X * D * M) = Matrix.trace (D * X * M) := by
  obtain ⟨d1, d2⟩ := hD
  obtain ⟨m1, m2⟩ := hM
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, d1, d2, m1, m2]
  ring

theorem pairBil_zero_of_right_diag (U : PeriodicLinkConfiguration SU2 L) (p : PeriodicLatticePlaquette L)
    (hM : IsDiagMat (imHolonomy U p)) (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (hg : IsDiagMat (g B)) : pairBil U p f g A B = 0 := by
  rw [pairBil_apply, sub_eq_zero]
  congr 1
  simp only [smulILM_apply, Matrix.smul_mul, Matrix.trace_smul]
  rw [trace_diag_swap (f A) (g B) (imHolonomy U p) hg hM]

theorem pairBil_zero_of_left_diag (U : PeriodicLinkConfiguration SU2 L) (p : PeriodicLatticePlaquette L)
    (hM : IsDiagMat (imHolonomy U p)) (f g : (Bond L → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) (A B : Bond L → SuTwo)
    (hf : IsDiagMat (f A)) : pairBil U p f g A B = 0 := by
  rw [pairBil_apply, sub_eq_zero]
  congr 1
  simp only [smulILM_apply, Matrix.smul_mul, Matrix.trace_smul]
  rw [trace_diag_swap (g B) (f A) (imHolonomy U p) hf hM]

theorem imHolonomy_diag {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (p : PeriodicLatticePlaquette L) :
    IsDiagMat (imHolonomy U p) := by
  have hH := holonomy_cartan hU p
  obtain ⟨h1, h2⟩ := hH
  unfold imHolonomy holonomyElemInv
  rw [inv_coe]
  constructor <;> simp [Matrix.conjTranspose_apply, h1, h2]

theorem sigma3_isDiag {X : SuTwo} (hX : diagP X = X) : IsDiagMat (X : Matrix (Fin 2) (Fin 2) ℂ) := by
  have := congrArg (fun Y : SuTwo => (Y : Matrix (Fin 2) (Fin 2) ℂ)) hX
  simp only [diagP_coe] at this
  constructor
  · rw [← this]; simp [Matrix.diagonal_apply]
  · rw [← this]; simp [Matrix.diagonal_apply]

theorem RMap_sigma3 {V : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hV : IsCartan V) {X : SuTwo} (hX : diagP X = X) :
    RMap V X = X := by
  have := RMap_diagP hV X
  rwa [hX] at this

theorem b_diag {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (p : PeriodicLatticePlaquette L)
    (z : Bond L → SuTwo) (hz : ∀ b, diagP (z b) = z b) :
    IsDiagMat (b1LM U p z) ∧ IsDiagMat (b2LM p z) ∧ IsDiagMat (b3LM p z) ∧ IsDiagMat (b4LM U p z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold b1LM a1LM
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, bondMatRLM_apply, smulILM_apply]
    rw [RMap_sigma3 (hU _) (hz _)]
    have := sigma3_isDiag (hz (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
    constructor <;> simp [this.1, this.2]
  · unfold b2LM a2LM
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, bondMatLM_apply, smulILM_apply]
    have := sigma3_isDiag (hz (p.1, p.2.1.2))
    constructor <;> simp [this.1, this.2]
  · unfold b3LM a3LM
    simp only [LinearMap.comp_apply, bondMatLM_apply, smulILM_apply]
    have := sigma3_isDiag (hz (p.1, p.2.1.1))
    constructor <;> simp [this.1, this.2]
  · unfold b4LM a4LM
    simp only [LinearMap.comp_apply, bondMatRLM_apply, smulILM_apply]
    rw [RMap_sigma3 (hU _) (hz _)]
    have := sigma3_isDiag (hz (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
    constructor <;> simp [this.1, this.2]

theorem secondBilPlaq_zero_right {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (p : PeriodicLatticePlaquette L)
    (w z : Bond L → SuTwo) (hz : ∀ b, diagP (z b) = z b) : secondBilPlaq U p w z = 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := b_diag hU p z hz
  have hM := imHolonomy_diag hU p
  rw [secondBilPlaq_apply]
  rw [pairBil_zero_of_right_diag U p hM _ _ w z d2, pairBil_zero_of_right_diag U p hM _ _ w z d3,
    pairBil_zero_of_right_diag U p hM _ _ w z d4, pairBil_zero_of_right_diag U p hM _ _ w z d3,
    pairBil_zero_of_right_diag U p hM _ _ w z d4, pairBil_zero_of_right_diag U p hM _ _ w z d4]
  ring

theorem secondBilPlaq_zero_left {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (p : PeriodicLatticePlaquette L)
    (w z : Bond L → SuTwo) (hz : ∀ b, diagP (z b) = z b) : secondBilPlaq U p z w = 0 := by
  obtain ⟨d1, d2, d3, d4⟩ := b_diag hU p z hz
  have hM := imHolonomy_diag hU p
  rw [secondBilPlaq_apply]
  rw [pairBil_zero_of_left_diag U p hM _ _ z w d1, pairBil_zero_of_left_diag U p hM _ _ z w d1,
    pairBil_zero_of_left_diag U p hM _ _ z w d1, pairBil_zero_of_left_diag U p hM _ _ z w d2,
    pairBil_zero_of_left_diag U p hM _ _ z w d2, pairBil_zero_of_left_diag U p hM _ _ z w d3]
  ring


theorem firstBilPlaq_cartan {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (p : PeriodicLatticePlaquette L)
    (w z : Bond L → SuTwo) :
    firstBilPlaq U p w z = 2 * (holCos U p - 1) * hsInner (curlValueCovariant U w p) (curlValueCovariant U z p) := by
  rw [firstBilPlaq_apply, reHolonomy_eq hU p]
  have h1 : (((holCos U p : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) - 1 = (((holCos U p - 1 : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_sub]
  rw [h1]
  simp only [smulILM_apply, curlMatLM_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  rw [AdalyFormal.Balaban.SuTwoInner.hsInner_def]
  set T := (((curlValueCovariant U w p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) * ((curlValueCovariant U z p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)).trace with hT
  have e : (((holCos U p - 1 : ℝ) : ℂ) * (Complex.I * (Complex.I * T))) = (((-(holCos U p - 1) : ℝ)) : ℂ) * T := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e, Complex.re_ofReal_mul]
  ring

open Classical in
/-- **`Δ'` with one sigma_3 argument, summed over a plaquette set `P`.** -/
theorem deltaPrimeBilNormLoc_sigma3 {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (P : Set (PeriodicLatticePlaquette L))
    (w z : Bond L → SuTwo) (hz : ∀ b, diagP (z b) = z b) :
    deltaPrimeBilNormLoc U P w z =
      ∑ p : PeriodicLatticePlaquette L, if p ∈ P then (holCos U p - 1) * hsInner (curlValueCovariant U w p) (curlValueCovariant U z p) else 0 := by
  classical
  have hw : ∀ p : PeriodicLatticePlaquette L, bilPlaq U p w z = 2 * (holCos U p - 1) * hsInner (curlValueCovariant U w p) (curlValueCovariant U z p) := by
    intro p; rw [bilPlaq_apply, firstBilPlaq_cartan hU, secondBilPlaq_zero_right hU p w z hz, add_zero]
  have hz' : ∀ p : PeriodicLatticePlaquette L, bilPlaq U p z w = 2 * (holCos U p - 1) * hsInner (curlValueCovariant U w p) (curlValueCovariant U z p) := by
    intro p; rw [bilPlaq_apply, firstBilPlaq_cartan hU, secondBilPlaq_zero_left hU p w z hz, add_zero,
      AdalyFormal.Balaban.SuTwoInner.hsInner_symm]
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs
  · rw [hw p, hz' p]; ring
  · ring


open AdalyFormal.Balaban.CStarDeltaKCOperator (curlCovariantLM_L2_toLp)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

open Classical in
/-- **`⟨w, Δ_loc z⟩ = Σ_{p∈P} cos θ_p ⟨curl w(p), curl z(p)⟩` for a sigma_3 field `z` on a Cartan configuration and ANY `w`.** -/
theorem inner_deltaKLocCLM_sigma3 {U : PeriodicLinkConfiguration SU2 L} (hU : CartanCfg U) (P : Set (PeriodicLatticePlaquette L))
    (w : BondFnL2 L) (z : Bond L → SuTwo) (hz : ∀ b, diagP (z b) = z b) :
    (inner ℝ w (deltaKLocCLM U P (WithLp.toLp 2 z)) : ℝ) =
      ∑ p : PeriodicLatticePlaquette L,
        if p ∈ P then holCos U p * hsInner (curlValueCovariant U (WithLp.ofLp w) p) (curlValueCovariant U z p) else 0 := by
  rw [inner_deltaKLocCLM]
  have hw : w = WithLp.toLp 2 (WithLp.ofLp w) := rfl
  have h1 : deltaPrimeBilL2NormLoc U P w (WithLp.toLp 2 z) = deltaPrimeBilNormLoc U P (WithLp.ofLp w) z := rfl
  rw [h1, deltaPrimeBilNormLoc_sigma3 hU P _ z hz]
  rw [PiLp.inner_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e1 : (curlCovariantLM_L2 U w) p = curlValueCovariant U (WithLp.ofLp w) p := by
    rw [hw, curlCovariantLM_L2_toLp]
  have e2 : (curlCovariantLM_L2 U (WithLp.toLp 2 z)) p = curlValueCovariant U z p := by
    rw [curlCovariantLM_L2_toLp]
  simp only [plaqMask_apply, e1, e2]
  split_ifs
  · show hsInner (curlValueCovariant U (WithLp.ofLp w) p) (curlValueCovariant U z p) + _ = _
    ring
  · simp

#print axioms inner_deltaKLocCLM_sigma3

end AdalyFormal.CoverOmega

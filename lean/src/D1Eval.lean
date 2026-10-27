import D1Ginv

/-!
# D1Eval -- evaluation of the literal `Δ` form at the path point `θ = π` on a single-bond field.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent}

/-- **central plaquette**: if the holonomy of `p` is the central element `-1`, the plaquette contributes `-‖curl‖²` to `⟨A,ΔA⟩`
(curl energy `‖c‖²` plus `½ bilPlaq = -2‖c‖²`). -/
theorem plaq_central (U : PeriodicLinkConfiguration SU2m L) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (h : ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1) :
    hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) + (1 / 2 : ℝ) * bilPlaq U p A A
      = - hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) := by
  have hinv : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    have : ((holonomyElemInv U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem U p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    rw [this, h]; simp
  have hre : reHolonomy U p = -1 := by
    unfold reHolonomy; rw [h, hinv]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  have him : imHolonomy U p = 0 := by
    unfold imHolonomy; rw [h, hinv]; simp
  rw [bilPlaq_atoms, him, hre]
  simp only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, sub_self, add_zero]
  have hc : (curlMatLM U p A) = ((curlValueCovariant U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  rw [hc]
  unfold hsInner
  set c := ((curlValueCovariant U A p : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)
  have e : smulILM c * smulILM c * (-1 - 1 : Matrix (Fin 2) (Fin 2) ℂ) = (2 : ℂ) • (c * c) := by
    simp only [smulILM_apply, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [e, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re]
  norm_num
  ring

/-- the form `⟨A,Δ_lit A⟩` as a sum over all plaquettes of (curl energy + ½ bilPlaq). -/
theorem delta_form_sum (U : PeriodicLinkConfiguration SU2m L) (A : BondFnL2 L) :
    (inner ℝ A (deltaKLocCLM U (Set.univ : Set (PeriodicLatticePlaquette L)) A) : ℝ) =
      ∑ p : PeriodicLatticePlaquette L,
        (hsInner (curlValueCovariant U (WithLp.ofLp A) p) (curlValueCovariant U (WithLp.ofLp A) p)
          + (1 / 2 : ℝ) * bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A)) := by
  classical
  rw [inner_deltaKLocCLM]
  simp only [plaqMask_univ]
  have h1 : (inner ℝ (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)
      (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A) : ℝ) =
      ∑ p : PeriodicLatticePlaquette L, hsInner (curlValueCovariant U (WithLp.ofLp A) p)
        (curlValueCovariant U (WithLp.ofLp A) p) := by
    simp only [PiLp.inner_apply]
    rfl
  have h2 : deltaPrimeBilL2NormLoc U (Set.univ : Set (PeriodicLatticePlaquette L)) A A =
      (1 / 2 : ℝ) * ∑ p : PeriodicLatticePlaquette L, bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A) := by
    show deltaPrimeBilNormLoc U Set.univ (WithLp.ofLp A) (WithLp.ofLp A) = _
    unfold deltaPrimeBilNormLoc
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul,
      deltaPrimeBilRawLoc_apply, Set.mem_univ, if_true]
    ring
  rw [h1, h2, Finset.sum_add_distrib, Finset.mul_sum]

#print axioms plaq_central
#print axioms delta_form_sum

end AdalyFormal.D1Literal

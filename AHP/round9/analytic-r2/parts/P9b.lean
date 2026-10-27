
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

/-! ## N. Smoothness of the plaquette operator along smooth link families

The frozen `D1Cont` proves continuity of `θ ↦ deltaKLocCLM (U θ) P` for continuous links.  The
same proof, with `ContDiff` in place of `Continuous`, gives smoothness for smooth links: every
matrix entry `⟪x, Δ(U θ) y⟫` is a finite expression in link matrices, their conjugate transposes,
products and real parts of traces. -/
section DeltaSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply curlValueCovariant)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2 (conjTR)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- Smooth links (Frobenius matrix norm). -/
def SmoothFam {L : PeriodicLatticeExtent} (U : ℝ → PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ e, ContDiff ℝ ⊤ (fun t => ((U t e : SU2) : M2))

theorem contDiff_trace2 {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun t => (Matrix.trace (f t)).re) := by
  have e : (fun t => (Matrix.trace (f t)).re) = fun t =>
      Complex.reCLM (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℝ ℂ) (f t)) := by
    funext t
    simp
  rw [e]
  exact Complex.reCLM.contDiff.comp ((LinearMap.toContinuousLinearMap _).contDiff.comp hf)

variable {L : PeriodicLatticeExtent} {U : ℝ → PeriodicLinkConfiguration SU2 L} (hU : SmoothFam U)
include hU

theorem cdF_inv (e : PeriodicLatticeEdge L) : ContDiff ℝ ⊤ (fun t => (((U t e)⁻¹ : SU2) : M2)) := by
  have e1 : (fun t => (((U t e)⁻¹ : SU2) : M2)) = fun t => conjTR ((U t e : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact conjTR.contDiff.comp (hU e)

theorem cdF_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    ContDiff ℝ ⊤ (fun t => ((RMap (U t e) X : SuTwo) : M2)) := by
  have e1 : (fun t => ((RMap (U t e) X : SuTwo) : M2)) =
      fun t => ((U t e : SU2) : M2) * (X : M2) * conjTR ((U t e : SU2) : M2) := by
    funext t
    exact RMap_coe_apply (U t e) X
  rw [e1]
  exact ((hU e).mul contDiff_const).mul (conjTR.contDiff.comp (hU e))

theorem cdF_holonomyElem (p : PeriodicLatticePlaquette L) :
    ContDiff ℝ ⊤ (fun t => ((holonomyElem (U t) p : SU2) : M2)) := by
  have e1 : (fun t => ((holonomyElem (U t) p : SU2) : M2)) = fun t =>
      ((U t (p.1, p.2.1.1) : SU2) : M2) * ((U t (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2) : M2) *
        (((U t (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2) : M2) *
        (((U t (p.1, p.2.1.2))⁻¹ : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact (((hU _).mul (hU _)).mul (cdF_inv hU _)).mul (cdF_inv hU _)

theorem cdF_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    ContDiff ℝ ⊤ (fun t => ((holonomyElemInv (U t) p : SU2) : M2)) := by
  have e1 : (fun t => ((holonomyElemInv (U t) p : SU2) : M2)) =
      fun t => conjTR ((holonomyElem (U t) p : SU2) : M2) := by
    funext t; rfl
  rw [e1]
  exact conjTR.contDiff.comp (cdF_holonomyElem hU p)

theorem cdF_reHolonomy (p : PeriodicLatticePlaquette L) : ContDiff ℝ ⊤ (fun t => reHolonomy (U t) p) := by
  unfold reHolonomy
  exact ((cdF_holonomyElem hU p).add (cdF_holonomyElemInv hU p)).const_smul _

theorem cdF_imHolonomy (p : PeriodicLatticePlaquette L) : ContDiff ℝ ⊤ (fun t => imHolonomy (U t) p) := by
  unfold imHolonomy
  exact ((cdF_holonomyElem hU p).sub (cdF_holonomyElemInv hU p)).const_smul _

theorem cdF_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => curlMatLM (U t) p A) := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact ((contDiff_const.add (cdF_RMap hU _ _)).sub (cdF_RMap hU _ _)).sub contDiff_const

theorem cdF_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => a1LM (U t) p A) := by
  show ContDiff ℝ ⊤ fun t => -(bondMatRLM (U t (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (cdF_RMap hU _ _).neg

theorem cdF_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => a4LM (U t) p A) := by
  show ContDiff ℝ ⊤ fun t => bondMatRLM (U t (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact cdF_RMap hU _ _

omit hU in
theorem cdF_smulI {f : ℝ → M2} (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun t => smulILM (f t)) := by
  show ContDiff ℝ ⊤ (fun t => Complex.I • f t)
  exact hf.const_smul _

omit hU in
theorem cdF_tr_re3 {f g h : ℝ → M2} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) (hh : ContDiff ℝ ⊤ h) :
    ContDiff ℝ ⊤ (fun t => (Matrix.trace (f t * g t * h t)).re) :=
  contDiff_trace2 ((hf.mul hg).mul hh)

theorem cdF_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => bilPlaq (U t) p A B) := by
  simp only [bilPlaq_atoms]
  have b1A : ContDiff ℝ ⊤ fun t => b1LM (U t) p A := cdF_smulI (cdF_a1 hU p A)
  have b4B : ContDiff ℝ ⊤ fun t => b4LM (U t) p B := cdF_smulI (cdF_a4 hU p B)
  have hre := cdF_reHolonomy hU p
  have him := cdF_imHolonomy hU p
  have hcA : ContDiff ℝ ⊤ fun t => smulILM (curlMatLM (U t) p A) := cdF_smulI (cdF_curlMat hU p A)
  have hcB : ContDiff ℝ ⊤ fun t => smulILM (curlMatLM (U t) p B) := cdF_smulI (cdF_curlMat hU p B)
  have k : ∀ (M : M2), ContDiff ℝ ⊤ fun _ : ℝ => M := fun M => contDiff_const
  refine ((((((cdF_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((cdF_tr_re3 (cdF_smulI b1A) (k _) him).sub (cdF_tr_re3 (k _) b1A him))).add
    ((cdF_tr_re3 (cdF_smulI b1A) (k _) him).sub (cdF_tr_re3 (k _) b1A him))).add
    ((cdF_tr_re3 (cdF_smulI b1A) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) b1A him))).add
    ((cdF_tr_re3 (k _) (k _) him).sub (cdF_tr_re3 (k _) (k _) him))).add
    ((cdF_tr_re3 (k _) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) (k _) him))).add
    ((cdF_tr_re3 (k _) b4B him).sub (cdF_tr_re3 (cdF_smulI b4B) (k _) him))

open Classical in
theorem cdF_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    ContDiff ℝ ⊤ (fun t => deltaPrimeBilNormLoc (U t) P A B) := by
  have h : ∀ A B : Bond L → SuTwo, ContDiff ℝ ⊤ fun t => deltaPrimeBilRawLoc (U t) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    refine ContDiff.sum (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [hp, if_true]; exact cdF_bilPlaq hU p A B
    · simp only [hp, if_false]; exact contDiff_const
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact contDiff_const.mul (contDiff_const.mul ((h A B).add (h B A)))

open Classical in
theorem cdF_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ContDiff ℝ ⊤ fun θ => (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
      (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine ContDiff.sum (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show ContDiff ℝ ⊤ fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine contDiff_const.mul (contDiff_trace2 ?_)
    exact (cdF_curlMat hU p (WithLp.ofLp x)).mul (cdF_curlMat hU p (WithLp.ofLp y))
  · simp only [hp, if_false]
    exact contDiff_const

theorem cdF_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    ContDiff ℝ ⊤ fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (cdF_curlInner hU P x y).add (cdF_deltaPrimeBil hU P _ _)

end DeltaSmooth

section DeltaSmoothCLM

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.StatementLaneR6 (deltaKLocCLM)

theorem contDiff_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : ℝ → E} (h : ∀ w : E, ContDiff ℝ ⊤ fun t => ⟪w, g t⟫) :
    ContDiff ℝ ⊤ g := by
  let b := stdOrthonormalBasis ℝ E
  have e : g = fun t => ∑ i, ⟪b i, g t⟫ • b i := by
    funext t
    exact (b.sum_repr' (g t)).symm
  rw [e]
  exact ContDiff.sum (fun i _ => (h (b i)).smul contDiff_const)

/-- Smoothness of the plaquette operator along smooth links (frozen `D1Cont`, `C^ω` version). -/
theorem contDiff_deltaKLocCLM {L : PeriodicLatticeExtent} {U : ℝ → PeriodicLinkConfiguration SU2 L}
    (hU : SmoothFam U) (P : Set (PeriodicLatticePlaquette L)) :
    ContDiff ℝ ⊤ (fun t => deltaKLocCLM (U t) P) :=
  contDiff_clm_apply_iff.mpr (fun y => contDiff_of_inner (fun w => cdF_inner_delta hU P w y))

/-- The derivative of the exterior path formula `A + P W* (M t - M 0) W I`, for a smooth operator
path `M`.  Stated for abstract carriers and instantiated later: for the concrete submodule carrier
the normed-space and plain instance paths of `E →L[ℝ] E` do not unify during elaboration. -/
theorem hasDerivAt_path_formula {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (M : ℝ → H →L[ℝ] H) (hM : ContDiff ℝ ⊤ M) (P : H →L[ℝ] E) (W : H →L[ℝ] H) (I : E →L[ℝ] H)
    (A : E →L[ℝ] E) (t₀ : ℝ) :
    HasDerivAt (fun t => A + P.comp (((ContinuousLinearMap.adjoint W).comp ((M t - M 0).comp W)).comp I))
      (deriv (fun t => A + P.comp (((ContinuousLinearMap.adjoint W).comp
        ((M t - M 0).comp W)).comp I)) t₀) t₀ := by
  have hM' := hM.differentiable (by simp)
  have h1 := (differentiable_const (ContinuousLinearMap.adjoint W)).clm_comp
    ((hM'.sub (differentiable_const (M 0))).clm_comp (differentiable_const W))
  have h2 := (differentiable_const P).clm_comp (h1.clm_comp (differentiable_const I))
  have hd := (differentiable_const A).add h2
  exact (hd t₀).hasDerivAt

end DeltaSmoothCLM

end AdalyFormal.Round9.Guarded.AnalyticR2

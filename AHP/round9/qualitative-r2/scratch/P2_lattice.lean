
/-! ## The plaquette Hessian along an analytic family of links

The frozen `D1Cont` proves that `θ ↦ deltaKLocCLM (U θ) P` is continuous when every link
matrix is.  The same chain of elementary operations (matrix products, adjoints, traces,
real parts, finite sums) preserves real-analyticity; below is that chain, statement by
statement, with `Continuous` replaced by entrywise analyticity.  The second section repeats
the frozen continuity chain over an arbitrary topological parameter space (used for joint
continuity in curvature and angle). -/
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent}

/-- A family of link configurations whose link matrices are entrywise real-analytic. -/
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : AnFam U)
include hU

theorem an_inv_coe (e : PeriodicLatticeEdge L) :
    AnM fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star

theorem an_holonomyElem (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).mul (hU _)).mul (an_inv_coe hU _)).mul (an_inv_coe hU _)

theorem an_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (an_holonomyElem hU p).star

theorem an_reHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact ((an_holonomyElem hU p).add (an_holonomyElemInv hU p)).smul _

theorem an_imHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact ((an_holonomyElem hU p).sub (an_holonomyElemInv hU p)).smul _

theorem an_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    AnM fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).mul (anM_const _)).mul (hU e).star

theorem an_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((anM_const _).add (an_RMap hU _ _)).sub (an_RMap hU _ _)).sub (anM_const _)

theorem an_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a1LM (U θ) p A := by
  show AnM fun θ =>
    -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (an_RMap hU _ _).neg

theorem an_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a4LM (U θ) p A := by
  show AnM fun θ =>
    bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact an_RMap hU _ _

theorem an_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    AnR fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ}, AnM f → AnM fun θ => smulILM (f θ) := by
    intro f hf
    exact hf.smul Complex.I
  have b1A : AnM fun θ => b1LM (U θ) p A := hI (an_a1 hU p A)
  have b4B : AnM fun θ => b4LM (U θ) p B := hI (an_a4 hU p B)
  have hre := an_reHolonomy hU p
  have him := an_imHolonomy hU p
  have hcA : AnM fun θ => smulILM (curlMatLM (U θ) p A) := hI (an_curlMat hU p A)
  have hcB : AnM fun θ => smulILM (curlMatLM (U θ) p B) := hI (an_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), AnM fun _ : ℝ => M := fun M => anM_const M
  exact ((((((AnM.tr_re3 hcA hcB (hre.sub (k 1))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) b4B him).sub (AnM.tr_re3 (hI b4B) b1A him))).add
    ((AnM.tr_re3 (k _) (k _) him).sub (AnM.tr_re3 (k _) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))

open Classical in
theorem an_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    AnR fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, AnR fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact AnR.sum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact an_bilPlaq hU p A B
      · simp only [hp, if_false]; exact anR_const 0)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact (anR_const _).mul ((anR_const _).mul ((h A B).add (h B A)))

open Classical in
theorem an_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine AnR.sum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show AnR fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    exact (anR_const _).mul
      ((an_curlMat hU p (WithLp.ofLp x)).mul (an_curlMat hU p (WithLp.ofLp y))).trace_re
  · simp only [hp, if_false, inner_zero_left]
    exact anR_const 0

/-- Every matrix coefficient of the plaquette Hessian is real-analytic in the parameter. -/
theorem an_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (an_curlInner hU P x y).add (an_deltaPrimeBil hU P _ _)

end

/-- `diag(e^{iθ}, e^{-iθ})` is entrywise real-analytic. -/
theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]

/-- The frozen exterior twist is an analytic family. -/
theorem anFam_Uth (Om : Set (PeriodicLatticeSite L)) : AnFam (AdalyFormal.D1Literal.Uth Om) := by
  intro e
  unfold AdalyFormal.D1Literal.Uth
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb Om
  · simp only [he, if_true]
    show AnM fun θ => AdalyFormal.D1Literal.uMat θ
    exact anM_uMat
  · simp only [he, if_false]
    exact anM_const _

/-! ### The frozen continuity chain over an arbitrary parameter space -/

section Param
variable {Y : Type*} [TopologicalSpace Y]

/-- A family of link configurations over a topological parameter space, continuous link by
link (the frozen `ContFam` with `ℝ` replaced by `Y`). -/
def ContFamY (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
include hU

theorem contY_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (hU e).star

theorem contY_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U y (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (contY_inv_coe hU _)).matrix_mul
    (contY_inv_coe hU _)

theorem contY_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y; rfl
  rw [this]
  exact (contY_holonomyElem hU p).star

theorem contY_reHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => reHolonomy (U y) p := by
  unfold reHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).add (contY_holonomyElemInv hU p))

theorem contY_imHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => imHolonomy (U y) p := by
  unfold imHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).sub (contY_holonomyElemInv hU p))

theorem contY_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U y e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star

theorem contY_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => curlMatLM (U y) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (contY_RMap hU _ _)).sub (contY_RMap hU _ _)).sub
    continuous_const)

theorem contY_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a1LM (U y) p A := by
  show Continuous fun y =>
    -(bondMatRLM (U y (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (contY_RMap hU _ _).neg

theorem contY_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a4LM (U y) p A := by
  show Continuous fun y =>
    bondMatRLM (U y (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact contY_RMap hU _ _

omit hU in
theorem contY_tr_re3 {f g h : Y → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun y => (Matrix.trace (f y * g y * h y)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)

theorem contY_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun y => bilPlaq (U y) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : Y → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f →
      Continuous fun y => smulILM (f y) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun y => b1LM (U y) p A := hI (contY_a1 hU p A)
  have b4B : Continuous fun y => b4LM (U y) p B := hI (contY_a4 hU p B)
  have hre := contY_reHolonomy hU p
  have him := contY_imHolonomy hU p
  have hcA : Continuous fun y => smulILM (curlMatLM (U y) p A) := hI (contY_curlMat hU p A)
  have hcB : Continuous fun y => smulILM (curlMatLM (U y) p B) := hI (contY_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : Y => M :=
    fun M => continuous_const
  refine ((((((contY_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) b4B him).sub (contY_tr_re3 (hI b4B) b1A him))).add
    ((contY_tr_re3 (k _) (k _) him).sub (contY_tr_re3 (k _) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))

open Classical in
theorem contY_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun y => deltaPrimeBilNormLoc (U y) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun y => deltaPrimeBilRawLoc (U y) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finsetSum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact contY_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))

open Classical in
theorem contY_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun w => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U w) (WithLp.ofLp x) p) (curlValueCovariant (U w) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((contY_curlMat hU p (WithLp.ofLp x)).matrix_mul
      (contY_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const

theorem contY_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w => (inner ℝ x (deltaKLocCLM (U w) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (contY_curlInner hU P x y).add (contY_deltaPrimeBil hU P _ _)

end

theorem contY_deltaKLocCLM {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun w => deltaKLocCLM (U w) P :=
  AdalyFormal.D1Literal.continuous_clm_of_inner (fun x y => contY_inner_delta hU P x y)

end Param

#print axioms AnFam
#print axioms an_inner_delta
#print axioms anM_uMat
#print axioms anFam_Uth
#print axioms ContFamY
#print axioms contY_deltaKLocCLM

#print axioms an_inv_coe
#print axioms an_holonomyElem
#print axioms an_holonomyElemInv
#print axioms an_reHolonomy
#print axioms an_imHolonomy
#print axioms an_RMap
#print axioms an_curlMat
#print axioms an_a1
#print axioms an_a4
#print axioms an_bilPlaq
#print axioms an_deltaPrimeBil
#print axioms an_curlInner
#print axioms contY_inv_coe
#print axioms contY_holonomyElem
#print axioms contY_holonomyElemInv
#print axioms contY_reHolonomy
#print axioms contY_imHolonomy
#print axioms contY_RMap
#print axioms contY_curlMat
#print axioms contY_a1
#print axioms contY_a4
#print axioms contY_tr_re3
#print axioms contY_bilPlaq
#print axioms contY_deltaPrimeBil
#print axioms contY_curlInner
#print axioms contY_inner_delta

end AdalyFormal.Round9.Guarded.QualitativeR2

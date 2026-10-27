import D1Lit

/-!
# D1Cont -- continuity in a parameter of the literal `Δ` (3.10): if every link matrix of a family `U θ` is continuous in `θ`,
then `θ ↦ deltaKLocCLM (U θ) P` is continuous (operator norm; the carrier is finite-dimensional).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.D1Literal

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent}

abbrev SU2m := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- family of link configurations continuous in the parameter -/
def ContFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)

section
variable {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : ContFam U)
include hU

theorem cont_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star

theorem cont_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (cont_inv_coe hU _)).matrix_mul (cont_inv_coe hU _)


theorem cont_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (cont_holonomyElem hU p).star

theorem cont_reHolonomy (p : PeriodicLatticePlaquette L) : Continuous fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact continuous_const.smul ((cont_holonomyElem hU p).add (cont_holonomyElemInv hU p))

theorem cont_imHolonomy (p : PeriodicLatticePlaquette L) : Continuous fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact continuous_const.smul ((cont_holonomyElem hU p).sub (cont_holonomyElemInv hU p))

theorem cont_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star

theorem cont_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (cont_RMap hU _ _)).sub (cont_RMap hU _ _)).sub continuous_const)

theorem cont_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => a1LM (U θ) p A := by
  show Continuous fun θ => -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (cont_RMap hU _ _).neg

theorem cont_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun θ => a4LM (U θ) p A := by
  show Continuous fun θ => bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact cont_RMap hU _ _

omit hU in
theorem cont_tr_re3 {f g h : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) : Continuous fun θ => (Matrix.trace (f θ * g θ * h θ)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)

theorem cont_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f → Continuous fun θ => smulILM (f θ) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun θ => b1LM (U θ) p A := hI (cont_a1 hU p A)
  have b4B : Continuous fun θ => b4LM (U θ) p B := hI (cont_a4 hU p B)
  have b4A : Continuous fun θ => b4LM (U θ) p A := hI (cont_a4 hU p A)
  have hre := cont_reHolonomy hU p
  have him := cont_imHolonomy hU p
  have hcA : Continuous fun θ => smulILM (curlMatLM (U θ) p A) := hI (cont_curlMat hU p A)
  have hcB : Continuous fun θ => smulILM (curlMatLM (U θ) p B) := hI (cont_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : ℝ => M := fun M => continuous_const
  refine ((((((cont_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((cont_tr_re3 (hI b1A) (k _) him).sub (cont_tr_re3 (k _) b1A him))).add
    ((cont_tr_re3 (hI b1A) (k _) him).sub (cont_tr_re3 (k _) b1A him))).add
    ((cont_tr_re3 (hI b1A) b4B him).sub (cont_tr_re3 (hI b4B) b1A him))).add
    ((cont_tr_re3 (k _) (k _) him).sub (cont_tr_re3 (k _) (k _) him))).add
    ((cont_tr_re3 (k _) b4B him).sub (cont_tr_re3 (hI b4B) (k _) him))).add
    ((cont_tr_re3 (k _) b4B him).sub (cont_tr_re3 (hI b4B) (k _) him))


open Classical in
theorem cont_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finset_sum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact cont_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))

open Classical in
theorem cont_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun θ => (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
      (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finset_sum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((cont_curlMat hU p (WithLp.ofLp x)).matrix_mul (cont_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const

theorem cont_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (cont_curlInner hU P x y).add (cont_deltaPrimeBil hU P _ _)


end

section clm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- a vector-valued function on a finite-dimensional Hilbert space is continuous iff all its inner products with fixed vectors are. -/
theorem continuous_of_inner {X : Type*} [TopologicalSpace X] {g : X → E}
    (h : ∀ w : E, Continuous fun t => (inner ℝ w (g t) : ℝ)) : Continuous g := by
  let b := stdOrthonormalBasis ℝ E
  have e : g = fun t => ∑ i, (inner ℝ (b i) (g t) : ℝ) • b i := by
    funext t
    exact ((b.sum_repr' (g t)).symm)
  rw [e]
  exact continuous_finset_sum _ (fun i _ => (h (b i)).smul continuous_const)

theorem continuous_clm_of_inner {X : Type*} [TopologicalSpace X] {f : X → E →L[ℝ] E}
    (h : ∀ x y : E, Continuous fun t => (inner ℝ x (f t y) : ℝ)) : Continuous f := by
  rw [continuous_clm_apply]
  intro y
  exact continuous_of_inner (fun w => h w y)
end clm

theorem cont_deltaKLocCLM {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : ContFam U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun θ => deltaKLocCLM (U θ) P :=
  continuous_clm_of_inner (fun x y => cont_inner_delta hU P x y)

#print axioms cont_deltaKLocCLM

end AdalyFormal.D1Literal

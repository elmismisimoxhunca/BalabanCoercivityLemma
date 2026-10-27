import CvN2
import NC3

/-!
# CvN3 -- the path `θ ↦ diag(e^{iθ}, e^{-iθ})` and continuity of the U-reading operators along a continuous path
(lane cover_necessary_20261016)

* `vPath θ ∈ SU(2)`, `vPath 0 = 1`, `vPath π = -1` (`negOne`), `θ ↦ vPath θ` continuous as matrices.
* For ANY path of configurations `U : ℝ → Cfg L` whose link matrices are continuous (`PathCont U`):
  `gradL2_continuous`: `θ ↦ D_{U θ}` is continuous (as a continuous linear map);
  `Delta_continuous`: `θ ↦ Δ(U θ)` of (3.10) (plaquette-localised, `ZR2Ops2.Delta`) is continuous.
  Both are proved through the real numbers `⟪w, O(θ) x⟫` (CvN1 `continuous_clm_of_inner`), which are finite sums of real parts of
  traces of products of the link matrices.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverNec

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (inner_eq_trace)

abbrev SU2m := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev M2m := Matrix (Fin 2) (Fin 2) ℂ

/-! ## 1. the path in `SU(2)` -/

noncomputable def vMat (t : ℝ) : M2m :=
  !![Complex.exp (t * Complex.I), 0; 0, Complex.exp (-(t * Complex.I))]

theorem exp_mul_conj (z : ℂ) (hz : (starRingEnd ℂ) z = -z) : Complex.exp z * (starRingEnd ℂ) (Complex.exp z) = 1 := by
  rw [← Complex.exp_conj, hz, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem vMat_mem (t : ℝ) : vMat t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hz1 : (starRingEnd ℂ) ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hz2 : (starRingEnd ℂ) (-((t : ℂ) * Complex.I)) = -(-((t : ℂ) * Complex.I)) := by rw [map_neg, hz1]
  have h1 := exp_mul_conj _ hz1
  have h2 := exp_mul_conj _ hz2
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h1, h2]
  · rw [vMat, Matrix.det_fin_two_of, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    simp

noncomputable def vPath (t : ℝ) : SU2m := ⟨vMat t, vMat_mem t⟩

theorem vPath_coe (t : ℝ) : ((vPath t : SU2m) : M2m) = vMat t := rfl

theorem vMat_continuous : Continuous vMat := by
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [vMat] <;> fun_prop

theorem vPath_zero : vPath 0 = 1 := by
  apply Subtype.ext
  show vMat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat]

theorem vPath_pi : vPath Real.pi = AdalyFormal.NoCover.negOne := by
  apply Subtype.ext
  show vMat Real.pi = -1
  have h1 : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have h2 : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, h1]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vMat, h1, h2]

/-! ## 2. continuous paths of configurations -/

variable {L : PeriodicLatticeExtent}

/-- every link matrix moves continuously -/
def PathCont (U : ℝ → Cfg L) : Prop := ∀ e : Bond L, Continuous fun t => ((U t e : SU2m) : M2m)

/-- one link moves along `vPath`, all others are `1`. -/
noncomputable def Upath (b : Bond L) (t : ℝ) : Cfg L := Function.update (fun _ => (1 : SU2m)) b (vPath t)

theorem Upath_cont (b : Bond L) : PathCont (Upath b) := by
  intro e
  by_cases h : e = b
  · subst h
    simp only [Upath, Function.update_self, vPath_coe]
    exact vMat_continuous
  · simp only [Upath, Function.update_of_ne h]
    exact continuous_const

theorem Upath_zero (b : Bond L) : Upath b 0 = fun _ => 1 := by
  rw [Upath, vPath_zero]; exact Function.update_eq_self_iff.mpr rfl

theorem Upath_pi (b : Bond L) : Upath b Real.pi = Function.update (fun _ => 1) b AdalyFormal.NoCover.negOne := by
  rw [Upath, vPath_pi]

theorem su_coe_inv (A : SU2m) : ((A⁻¹ : SU2m) : M2m) = star (A : M2m) := rfl

theorem su_coe_mul (A B : SU2m) : ((A * B : SU2m) : M2m) = (A : M2m) * (B : M2m) := rfl

/-! ## 3. atoms -/

theorem cont_inner_RMap {X : Type*} [TopologicalSpace X] (g : X → SU2m) (hg : Continuous fun t => ((g t : SU2m) : M2m))
    (W Y : SuTwo) : Continuous fun t => ⟪W, RMap (g t) Y⟫ := by
  simp only [inner_eq_trace, RMap_coe_apply]
  fun_prop

theorem cont_RMap_coe {X : Type*} [TopologicalSpace X] (g : X → SU2m) (hg : Continuous fun t => ((g t : SU2m) : M2m))
    (Y : SuTwo) : Continuous fun t => ((RMap (g t) Y : SuTwo) : M2m) := by
  simp only [RMap_coe_apply]
  fun_prop

theorem cont_hol {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) :
    Continuous fun t => ((periodicPlaquetteHolonomy (U t) p : SU2m) : M2m) := by
  have h1 := hU (p.1, p.2.1.1)
  have h2 := hU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
  have h3 := hU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
  have h4 := hU (p.1, p.2.1.2)
  show Continuous fun t => ((U t (p.1, p.2.1.1) * U t (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
    (U t (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (U t (p.1, p.2.1.2))⁻¹ : SU2m) : M2m)
  simp only [su_coe_mul, su_coe_inv]
  fun_prop

theorem cont_reHol {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) :
    Continuous fun t => reHolonomy (U t) p := by
  have h := cont_hol hU p
  unfold reHolonomy holonomyElemInv holonomyElem
  simp only [su_coe_inv]
  fun_prop

theorem cont_imHol {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) :
    Continuous fun t => imHolonomy (U t) p := by
  have h := cont_hol hU p
  unfold imHolonomy holonomyElemInv holonomyElem
  simp only [su_coe_inv]
  fun_prop

theorem cont_curlMat {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun t => curlMatLM (U t) p A := by
  have h1 := cont_RMap_coe (fun t => U t (p.1, p.2.1.1)) (hU _) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
  have h2 := cont_RMap_coe (fun t => U t (p.1, p.2.1.2)) (hU _) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
  simp only [curlMatLM_apply, curlValueCovariant, Submodule.coe_add, Submodule.coe_sub]
  fun_prop

theorem cont_b1 {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun t => b1LM (U t) p A := by
  have h1 := cont_RMap_coe (fun t => U t (p.1, p.2.1.2)) (hU _) (A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))
  simp only [b1LM, a1LM, LinearMap.comp_apply, smulILM_apply, LinearMap.neg_apply, bondMatRLM_apply]
  fun_prop

theorem cont_b4 {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun t => b4LM (U t) p A := by
  have h1 := cont_RMap_coe (fun t => U t (p.1, p.2.1.1)) (hU _) (A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2))
  simp only [b4LM, a4LM, LinearMap.comp_apply, smulILM_apply, bondMatRLM_apply]
  fun_prop

theorem cont_pairBil {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L)
    (f g : ℝ → (Bond L → SuTwo) →ₗ[ℝ] M2m) (A B : Bond L → SuTwo)
    (hf : Continuous fun t => f t A) (hg : Continuous fun t => g t B)
    (hf' : Continuous fun t => f t B) (hg' : Continuous fun t => g t A) :
    Continuous fun t => pairBil (U t) p (f t) (g t) A B := by
  have hI := cont_imHol hU p
  simp only [pairBil_apply, smulILM_apply]
  fun_prop

theorem cont_bilPlaq {U : ℝ → Cfg L} (hU : PathCont U) (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun t => bilPlaq (U t) p A B := by
  have hR := cont_reHol hU p
  have hcA := cont_curlMat hU p A
  have hcB := cont_curlMat hU p B
  have b1A := cont_b1 hU p A
  have b1B := cont_b1 hU p B
  have b4A := cont_b4 hU p A
  have b4B := cont_b4 hU p B
  have c2 : ∀ C : Bond L → SuTwo, Continuous fun _ : ℝ => b2LM p C := fun _ => continuous_const
  have c3 : ∀ C : Bond L → SuTwo, Continuous fun _ : ℝ => b3LM p C := fun _ => continuous_const
  rw [show (fun t => bilPlaq (U t) p A B) = fun t => firstBilPlaq (U t) p A B + secondBilPlaq (U t) p A B from rfl]
  refine Continuous.add ?_ ?_
  · simp only [firstBilPlaq_apply, smulILM_apply]
    fun_prop
  · simp only [secondBilPlaq_apply]
    refine ((((Continuous.add ?_ ?_).add ?_).add ?_).add ?_).add ?_
    · exact cont_pairBil hU p (fun t => b1LM (U t) p) (fun _ => b2LM p) A B b1A (c2 B) b1B (c2 A)
    · exact cont_pairBil hU p (fun t => b1LM (U t) p) (fun _ => b3LM p) A B b1A (c3 B) b1B (c3 A)
    · exact cont_pairBil hU p (fun t => b1LM (U t) p) (fun t => b4LM (U t) p) A B b1A b4B b1B b4A
    · exact cont_pairBil hU p (fun _ => b2LM p) (fun _ => b3LM p) A B (c2 A) (c3 B) (c2 B) (c3 A)
    · exact cont_pairBil hU p (fun _ => b2LM p) (fun t => b4LM (U t) p) A B (c2 A) b4B (c2 B) b4A
    · exact cont_pairBil hU p (fun _ => b3LM p) (fun t => b4LM (U t) p) A B (c3 A) b4B (c3 B) b4A

/-! ## 4. the operators -/

theorem gradL2_continuous {U : ℝ → Cfg L} (hU : PathCont U) : Continuous fun t => gradL2 (U t) := by
  refine continuous_clm_of_inner _ (fun f w => ?_)
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun b _ => ?_)
  show Continuous fun t => ⟪(WithLp.ofLp w) b, (WithLp.ofLp (gradL2 (U t) f)) b⟫
  simp only [gradL2_apply, gradValueCovariant, inner_sub_right]
  exact (cont_inner_RMap (fun t => U t b) (hU b) _ _).sub continuous_const

theorem curl_continuous {U : ℝ → Cfg L} (hU : PathCont U) (w : BondFnL2 L) :
    Continuous fun t => AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U t) w := by
  refine continuous_of_inner _ (fun z => ?_)
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  show Continuous fun t => ⟪(WithLp.ofLp z) p, curlValueCovariant (U t) (WithLp.ofLp w) p⟫
  simp only [curlValueCovariant, inner_sub_right, inner_add_right]
  exact (((continuous_const.add (cont_inner_RMap (fun t => U t (p.1, p.2.1.1)) (hU _) _ _)).sub
    (cont_inner_RMap (fun t => U t (p.1, p.2.1.2)) (hU _) _ _)).sub continuous_const)

theorem Delta_continuous (G : TowerGeom L) {U : ℝ → Cfg L} (hU : PathCont U) : Continuous fun t => Delta G (U t) := by
  refine continuous_clm_of_inner _ (fun x w => ?_)
  have e : ∀ t, ⟪w, Delta G (U t) x⟫ =
      ⟪plaqMask (plaqIn G.Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U t) w),
        plaqMask (plaqIn G.Om0) (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U t) x)⟫ +
      deltaPrimeBilL2NormLoc (U t) (plaqIn G.Om0) w x := fun t => by
    unfold Delta; exact inner_deltaKLocCLM (U t) (plaqIn G.Om0) w x
  simp only [e]
  refine Continuous.add ?_ ?_
  · have hm : Continuous (plaqMask (L := L) (plaqIn G.Om0)) := (plaqMask (plaqIn G.Om0)).continuous_of_finiteDimensional
    exact (hm.comp (curl_continuous hU w)).inner (hm.comp (curl_continuous hU x))
  · have e2 : ∀ t, deltaPrimeBilL2NormLoc (U t) (plaqIn G.Om0) w x =
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (deltaPrimeBilRawLoc (U t) (plaqIn G.Om0) (WithLp.ofLp w) (WithLp.ofLp x) +
          deltaPrimeBilRawLoc (U t) (plaqIn G.Om0) (WithLp.ofLp x) (WithLp.ofLp w))) := fun t => by
      show deltaPrimeBilNormLoc (U t) (plaqIn G.Om0) (WithLp.ofLp w) (WithLp.ofLp x) = _
      simp [deltaPrimeBilNormLoc, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
      ring
    simp only [e2, deltaPrimeBilRawLoc_apply]
    refine continuous_const.mul (continuous_const.mul (Continuous.add ?_ ?_)) <;>
      refine continuous_finsetSum _ (fun p _ => ?_) <;>
      by_cases hp : p ∈ plaqIn G.Om0 <;> simp only [hp, if_true, if_false] <;>
      first | exact cont_bilPlaq hU p _ _ | exact continuous_const

#print axioms vMat_mem
#print axioms vPath_zero
#print axioms vPath_pi
#print axioms Upath_cont
#print axioms cont_bilPlaq
#print axioms gradL2_continuous
#print axioms curl_continuous
#print axioms Delta_continuous

end AdalyFormal.CoverNec

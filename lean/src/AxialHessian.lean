import CircleActions
import SourcePrecision
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
open Matrix
namespace HConstruction.G0Final.Hessian
open HConstruction.Circle HConstruction.SmallNF HConstruction.Covariance HConstruction.Nonflat
open HConstruction.NfRepair.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL Bond)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKUnified (bfl2Equiv)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open HConstruction.SmallNF.Reproduced

abbrev Plaq := PeriodicLatticePlaquette witnessL
abbrev Scalars := Bond witnessL → ℝ

def axial (a : Scalars) : Bond witnessL → SuTwo := fun b => a b • pauliE2
def axialH (a : Scalars) : H := bfl2Equiv.symm (axial a)
def scalarCurl (a : Scalars) (p : Plaq) : ℝ :=
  a (p.1,p.2.1.1) + a (periodicLatticeShift p.1 p.2.1.1,p.2.1.2) -
    a (periodicLatticeShift p.1 p.2.1.2,p.2.1.1) - a (p.1,p.2.1.2)

theorem RMap_chosen_axis (b : Bond witnessL) (s : ℝ) :
    RMap (chosenU b) (s • pauliE2) = s • pauliE2 := by
  classical
  unfold chosenU nonflatU AdalyFormal.Balaban.NormalizedCounterexampleSearch.singleBondU
  split_ifs
  · exact RMap_rot_axis _ _
  · simp [RMap_one]

theorem curl_axial (a : Scalars) (p : Plaq) :
    curlValueCovariant chosenU (axial a) p = scalarCurl a p • pauliE2 := by
  simp only [curlValueCovariant, axial, RMap_chosen_axis, scalarCurl,
    add_smul, sub_smul]

theorem curl_axial_flat (a : Scalars) (p : Plaq) :
    curlValueCovariant (trivialU witnessL) (axial a) p = scalarCurl a p • pauliE2 := by
  simp [curlValueCovariant, axial, AdalyFormal.Balaban.CovariantHjMinimizer.trivialU, RMap_one, scalarCurl, add_smul, sub_smul]

theorem covCurl_axial_flat (a : Scalars) : covCurl chosenU (axialH a) = flatCurl (axialH a) := by
  apply (fiberEquiv _).injective
  funext p
  change (2 : ℝ) • curlValueCovariant chosenU (axial a) p =
    (2 : ℝ) • curlValueCovariant (trivialU witnessL) (axial a) p
  rw [curl_axial, curl_axial_flat]

/-- All transported source reads lie on the same matrix axis. -/
theorem a_reads_axis (a : Scalars) (p : Plaq) :
    a1LM chosenU p (axial a) = ((-a (periodicLatticeShift p.1 p.2.1.2,p.2.1.1)) • pauliE2 : SuTwo) ∧
    a2LM p (axial a) = ((-a (p.1,p.2.1.2)) • pauliE2 : SuTwo) ∧
    a3LM p (axial a) = (a (p.1,p.2.1.1) • pauliE2 : SuTwo) ∧
    a4LM chosenU p (axial a) = (a (periodicLatticeShift p.1 p.2.1.1,p.2.1.2) • pauliE2 : SuTwo) := by
  have he (b : Bond witnessL) : RMap (chosenU b) pauliE2 = pauliE2 := by
    simpa using RMap_chosen_axis b 1
  simp [a1LM, a2LM, a3LM, a4LM, bondMatRLM_apply, bondMatLM_apply, axial, he]

theorem axis_matrices_commute (s t : ℝ) :
    (Complex.I • ((s • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) *
      (Complex.I • ((t • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
    (Complex.I • ((t • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) *
      (Complex.I • ((s • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliE2, witnessM, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

theorem commutator_axial_zero (a : Scalars) (p : Plaq) :
    commutatorMatrixSumTransported chosenU (axial a) p = 0 := by
  have h (s t : ℝ) := sub_eq_zero.mpr (axis_matrices_commute s t)
  simp only [commutatorMatrixSumTransported, AprimeZW, AprimeWX, AprimeXY, AprimeYZ,
    axial, RMap_chosen_axis, ← neg_smul]
  simp only [h, add_zero, smul_zero]

theorem secondBilPlaq_axial_zero (a : Scalars) (p : Plaq) :
    secondBilPlaq chosenU p (axial a) (axial a) = 0 := by
  rw [secondBilPlaq_diag]
  simp [deltaPrimeSecondTermTransported, commutator_axial_zero]

/-- The actual real holonomy has only two scalar values. -/
theorem reHolonomy_cases (p : Plaq) :
    reHolonomy chosenU p = (255/257 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∨
    reHolonomy chosenU p = 1 := by
  rcases holonomy_singleBondU_trichotomy (rotElem (1/16)) p with h | h | h
  · left
    change holonomyElem chosenU p = rotElem (1/16) at h
    simp only [reHolonomy, holonomyElemInv, h, coe_inv, rotElem_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rotM, rotA, rotB, Matrix.conjTranspose_apply, Matrix.one_apply]
  · left
    change holonomyElem chosenU p = (rotElem (1/16))⁻¹ at h
    simp only [reHolonomy, holonomyElemInv, h, inv_inv, coe_inv, rotElem_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rotM, rotA, rotB, Matrix.conjTranspose_apply, Matrix.one_apply]
  · right
    change holonomyElem chosenU p = 1 at h
    simp only [reHolonomy, holonomyElemInv, h, inv_one]
    change (1/2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) + 1) = 1
    ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

def plaqWeight (p : Plaq) : ℝ :=
  if reHolonomy chosenU p = 1 then 1 else 255/257

theorem reHolonomy_weight (p : Plaq) :
    reHolonomy chosenU p = (plaqWeight p : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  classical
  unfold plaqWeight
  split_ifs with h
  · simpa using h
  · rcases reHolonomy_cases p with h' | h'
    · simpa using h'
    · contradiction

theorem plaqWeight_values (p : Plaq) : plaqWeight p = 255/257 ∨ plaqWeight p = 1 := by
  classical
  unfold plaqWeight
  split_ifs <;> simp

theorem plaqWeight_lower (p : Plaq) : (255/257 : ℝ) ≤ plaqWeight p := by
  rcases plaqWeight_values p with h | h <;> rw [h] <;> norm_num

theorem firstBilPlaq_axial (a b : Scalars) (p : Plaq) :
    firstBilPlaq chosenU p (axial a) (axial b) =
      2 * (plaqWeight p - 1) * scalarCurl a p * scalarCurl b p := by
  rw [firstBilPlaq_apply, curlMatLM_apply, curlMatLM_apply, curl_axial, curl_axial,
    reHolonomy_weight]
  simp [smulILM_apply, pauliE2, witnessM, Matrix.trace,
    Fin.sum_univ_two, Matrix.one_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Matrix.vecMul, dotProduct]
  ring

theorem bilPlaq_axial_diag (a : Scalars) (p : Plaq) :
    bilPlaq chosenU p (axial a) (axial a) =
      2 * (plaqWeight p - 1) * (scalarCurl a p)^2 := by
  rw [bilPlaq_apply, firstBilPlaq_axial, secondBilPlaq_axial_zero]
  ring

/-- This is the actual symmetrized correction, with its normalization factor two. -/
theorem correctionBil_axial (a : Scalars) :
    correctionBil chosenU (axialH a) (axialH a) =
      4 * ∑ p : Plaq, (plaqWeight p - 1) * (scalarCurl a p)^2 := by
  rw [correctionBil_apply]
  change 2 * deltaPrimeBil chosenU (axial a) (axial a) = _
  rw [deltaPrimeBil_apply, deltaPrimeBilRaw_apply]
  simp only [bilPlaq_axial_diag]
  rw [show (∑ p : Plaq, 2 * (plaqWeight p - 1) * scalarCurl a p ^ 2) =
      2 * ∑ p : Plaq, (plaqWeight p - 1) * scalarCurl a p ^ 2 by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring]
  ring

theorem inner_axis (s t : ℝ) : (inner ℝ (s • pauliE2) (t • pauliE2) : ℝ) = s*t := by
  simpa [assemble] using assemble_inner 0 s 0 0 t 0

/-- The factor four is the square of the source fine-spacing curl factor two. -/
theorem flatCurl_axial_energy (a : Scalars) :
    ‖flatCurl (axialH a)‖^2 = 4 * ∑ p : Plaq, (scalarCurl a p)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (∑ p : Plaq, inner ℝ
    ((2 : ℝ) • curlValueCovariant (trivialU witnessL) (axial a) p)
    ((2 : ℝ) • curlValueCovariant (trivialU witnessL) (axial a) p)) = _
  simp only [curl_axial_flat, smul_smul, inner_axis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Exact axial energy of SmallNF.deltaU, including correctionBil. -/
theorem deltaU_axial_energy (a : Scalars) :
    (inner ℝ (axialH a) (deltaU chosenU (axialH a)) : ℝ) =
      4 * ∑ p : Plaq, plaqWeight p * (scalarCurl a p)^2 := by
  simp only [deltaU, _root_.add_apply, inner_add_right,
    curlSquare_energy, inner_fromBil, correctionBil_axial, covCurl_axial_flat,
    flatCurl_axial_energy]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem deltaU_axial_lower (a : Scalars) :
    (255/257 : ℝ) * ‖flatCurl (axialH a)‖^2 ≤
      inner ℝ (axialH a) (deltaU chosenU (axialH a)) := by
  rw [deltaU_axial_energy, flatCurl_axial_energy]
  have h : (255/257 : ℝ) * (∑ p : Plaq, (scalarCurl a p)^2) ≤
      ∑ p : Plaq, plaqWeight p * (scalarCurl a p)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    exact mul_le_mul_of_nonneg_right (plaqWeight_lower p) (sq_nonneg _)
  nlinarith

/-- Every individual bracket atom vanishes even for two different axial inputs. -/
theorem pairBil_axis_zero (p : Plaq)
    (f g : (Bond witnessL → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
    (A B : Bond witnessL → SuTwo) (s t : ℝ)
    (hf : f A = Complex.I • ((s • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))
    (hg : g B = Complex.I • ((t • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    pairBil chosenU p f g A B = 0 := by
  rw [pairBil_apply, hf, hg]
  apply sub_eq_zero.mpr
  simpa only [smulILM_apply, Matrix.smul_mul] using
    congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.trace ((Complex.I • X) * imHolonomy chosenU p)).re)
      (axis_matrices_commute s t)

theorem secondBilPlaq_axial (a b : Scalars) (p : Plaq) :
    secondBilPlaq chosenU p (axial a) (axial b) = 0 := by
  obtain ⟨a1,a2,a3,a4⟩ := a_reads_axis a p
  obtain ⟨b1,b2,b3,b4⟩ := a_reads_axis b p
  have h1 (s t : ℝ) (f g : (Bond witnessL → SuTwo) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ)
      (hf : f (axial a) = Complex.I • ((s • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))
      (hg : g (axial b) = Complex.I • ((t • pauliE2 : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :=
    pairBil_axis_zero p f g (axial a) (axial b) s t hf hg
  rw [secondBilPlaq_apply]
  have h12 := h1 _ _ (b1LM chosenU p) (b2LM p)
    (congrArg smulILM a1) (congrArg smulILM b2)
  have h13 := h1 _ _ (b1LM chosenU p) (b3LM p)
    (congrArg smulILM a1) (congrArg smulILM b3)
  have h14 := h1 _ _ (b1LM chosenU p) (b4LM chosenU p)
    (congrArg smulILM a1) (congrArg smulILM b4)
  have h23 := h1 _ _ (b2LM p) (b3LM p)
    (congrArg smulILM a2) (congrArg smulILM b3)
  have h24 := h1 _ _ (b2LM p) (b4LM chosenU p)
    (congrArg smulILM a2) (congrArg smulILM b4)
  have h34 := h1 _ _ (b3LM p) (b4LM chosenU p)
    (congrArg smulILM a3) (congrArg smulILM b4)
  rw [h12,h13,h14,h23,h24,h34]
  norm_num

/-- Mixed-input version retains the actual source symmetrization. -/
theorem correctionBil_axial_pair (a b : Scalars) :
    correctionBil chosenU (axialH a) (axialH b) =
      4 * ∑ p : Plaq, (plaqWeight p - 1) * scalarCurl a p * scalarCurl b p := by
  rw [correctionBil_apply]
  change 2 * deltaPrimeBil chosenU (axial a) (axial b) = _
  rw [deltaPrimeBil_apply, deltaPrimeBilRaw_apply, deltaPrimeBilRaw_apply]
  simp only [bilPlaq_apply, firstBilPlaq_axial, secondBilPlaq_axial, add_zero]
  have hab : (∑ p : Plaq, 2 * (plaqWeight p - 1) * scalarCurl a p * scalarCurl b p) =
      2 * ∑ p : Plaq, (plaqWeight p - 1) * scalarCurl a p * scalarCurl b p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hba : (∑ p : Plaq, 2 * (plaqWeight p - 1) * scalarCurl b p * scalarCurl a p) =
      2 * ∑ p : Plaq, (plaqWeight p - 1) * scalarCurl a p * scalarCurl b p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hab,hba]
  ring

theorem flatCurl_axial_inner (a b : Scalars) :
    (inner ℝ (flatCurl (axialH a)) (flatCurl (axialH b)) : ℝ) =
      4 * ∑ p : Plaq, scalarCurl a p * scalarCurl b p := by
  change (∑ p : Plaq, inner ℝ
    ((2 : ℝ) • curlValueCovariant (trivialU witnessL) (axial a) p)
    ((2 : ℝ) • curlValueCovariant (trivialU witnessL) (axial b) p)) = _
  simp only [curl_axial_flat, smul_smul, inner_axis]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem deltaU_axial_bilinear (a b : Scalars) :
    (inner ℝ (axialH a) (deltaU chosenU (axialH b)) : ℝ) =
      4 * ∑ p : Plaq, plaqWeight p * scalarCurl a p * scalarCurl b p := by
  simp only [deltaU, _root_.add_apply, inner_add_right, inner_fromBil, correctionBil_axial_pair,
    curlSquare, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    covCurl_axial_flat, flatCurl_axial_inner]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Pointwise axial fields are covered, not merely an unconnected scalar model. -/
theorem axialH_of_pointwise (A : H)
    (hA : ∀ e : Bond witnessL, ∃ s : ℝ, bfl2Equiv A e = s • pauliE2) :
    A = axialH (fun e => axisCoord (bfl2Equiv A e)) := by
  apply bfl2Equiv.injective
  funext e
  change bfl2Equiv A e = axisCoord (bfl2Equiv A e) • pauliE2
  obtain ⟨s,hs⟩ := hA e
  rw [hs]
  have hc : axisCoord (s • pauliE2) = s := by
    simpa [assemble] using axisCoord_assemble 0 s 0
  rw [hc]

theorem deltaU_pointwise_axial_lower (A : H)
    (hA : ∀ e : Bond witnessL, ∃ s : ℝ, bfl2Equiv A e = s • pauliE2) :
    (255/257 : ℝ) * (inner ℝ A (flatDelta A) : ℝ) ≤ inner ℝ A (deltaU chosenU A) := by
  have he := axialH_of_pointwise A hA
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  rw [flatDelta_energy]
  exact deltaU_axial_lower _

theorem plaqWeight_cos (p : Plaq) : plaqWeight p = Real.cos theta ∨ plaqWeight p = 1 := by
  rw [cos_theta]
  exact plaqWeight_values p

/-- Unconditional source precision energy: no replacement of nativeLinearQ or siteRU. -/
theorem precisionU_axial_energy (a : Scalars) :
    (inner ℝ (axialH a) (precisionU chosenU 1 (axialH a)) : ℝ) =
      4 * ∑ p : Plaq, plaqWeight p * (scalarCurl a p)^2 +
      ‖gaugeConstraintU chosenU (axialH a)‖^2 +
      8 * ‖nativeLinearQ chosenU 2 (axialH a)‖^2 := by
  have h := deltaU_axial_energy a
  rw [deltaU_energy] at h
  rw [precisionU_energy]
  rw [h]
  ring

/-- Positivity of the remaining *actual* gauge and Q energies. -/
theorem precisionU_axial_curl_lower (a : Scalars) :
    (255/257 : ℝ) * ‖flatCurl (axialH a)‖^2 ≤
      inner ℝ (axialH a) (precisionU chosenU 1 (axialH a)) := by
  have h := deltaU_axial_lower a
  rw [deltaU_axial_energy] at h
  rw [precisionU_axial_energy]
  nlinarith [sq_nonneg ‖gaugeConstraintU chosenU (axialH a)‖,
    sq_nonneg ‖nativeLinearQ chosenU 2 (axialH a)‖]

#print axioms correctionBil_axial_pair
#print axioms flatCurl_axial_inner
#print axioms deltaU_axial_bilinear
#print axioms axialH_of_pointwise
#print axioms deltaU_pointwise_axial_lower
#print axioms pairBil_axis_zero
#print axioms secondBilPlaq_axial
#print axioms plaqWeight_cos
#print axioms precisionU_axial_energy
#print axioms precisionU_axial_curl_lower
#print axioms correctionBil_axial
#print axioms flatCurl_axial_energy
#print axioms deltaU_axial_energy
#print axioms deltaU_axial_lower
#print axioms reHolonomy_cases
#print axioms reHolonomy_weight
#print axioms plaqWeight_values
#print axioms plaqWeight_lower
#print axioms firstBilPlaq_axial
#print axioms RMap_chosen_axis
#print axioms curl_axial
#print axioms covCurl_axial_flat
#print axioms a_reads_axis
#print axioms axis_matrices_commute
#print axioms commutator_axial_zero
#print axioms secondBilPlaq_axial_zero
end HConstruction.G0Final.Hessian

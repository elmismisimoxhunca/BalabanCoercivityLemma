import QVIdentification
import Lean.Util.CollectAxioms
set_option autoImplicit false

namespace HConstruction.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.DeltaKUnified
open AdalyFormal.Balaban.RegularityHolonomy
open AdalyFormal.Balaban.ConstantA (BaseConstant usedAt)
open AdalyFormal.Balaban.VariationalProjectorH1
  (BalabanCovarianceData solutionOperator solutionOperator_apply)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU periodicLatticeShiftBack)
open AdalyFormal.Balaban.Q1Real (checkerConfigSuTwo checkerConfigSuTwo_ne_zero
  checkerConfigSuTwo_mem_q1RealKernel_trivialU)

noncomputable def taylorQuadraticTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : ℝ → E) : E :=
  (1 / 2 : ℝ) • deriv (deriv Q) 0

noncomputable def Dtilde2Shape {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Q : H → E) (B : H) : E :=
  taylorQuadraticTerm (fun t : ℝ => Q (t • B))

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

noncomputable def deltaKForm (D : BalabanCovarianceData H K) (bc : BaseConstant) (Qext : K → K)
    (J : H) (B : K) : ℝ :=
  (inner ℝ B (D.CompInv B) : ℝ)
    - usedAt bc 0 * (inner ℝ B B : ℝ)
    - 2 * (inner ℝ (solutionOperator D (Dtilde2Shape Qext B)) J : ℝ)

theorem taylorQuadraticTerm_sq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : E) :
    taylorQuadraticTerm (fun t : ℝ => t ^ 2 • w) = w := by
  unfold taylorQuadraticTerm
  have h1 : deriv (fun t : ℝ => t ^ 2 • w) = fun t => (2 * t) • w := by
    funext t
    have hbase : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := by
      simpa using hasDerivAt_pow 2 t
    have := hbase.smul_const w
    simpa [mul_comm] using this.deriv
  rw [h1]
  have h2 : deriv (fun t : ℝ => (2 * t) • w) 0 = (2 : ℝ) • w := by
    have hb : HasDerivAt (fun t : ℝ => (2:ℝ) * t) 2 (0:ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have := hb.smul_const w
    simpa using this.deriv
  rw [h2, smul_smul]
  norm_num

noncomputable def deltaKFormOnSubspace {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (D : BalabanCovarianceData H K)
    (bc : BaseConstant) (Qext : K → K) (J : H) (S : Submodule ℝ K) (B : S) : ℝ :=
  deltaKForm D bc Qext J (B : K)

noncomputable def deltaKFormOnSubspace156 (bc : BaseConstant)
    (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B : subspace156BFL2 Lambda S' ell U) : ℝ :=
  deltaKFormOnSubspace deltaKUnifiedData bc Qext J (subspace156BFL2 Lambda S' ell U) B

theorem deltaKFormOnSubspace156_eq (bc : BaseConstant)
    (Qext : BFL2 witnessL → BFL2 witnessL) (J : BFL2 witnessL)
    (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL)
    (B : subspace156BFL2 Lambda S' ell U) :
    deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B =
      deltaKForm deltaKUnifiedData bc Qext J (B : BFL2 witnessL) := rfl

def TheLemmaRegularU (bc : BaseConstant) (Qext : BFL2 witnessL → BFL2 witnessL)
    (J : BFL2 witnessL) (Lambda S' : Finset (PeriodicLatticeSite witnessL)) (ell : ℕ) : Prop :=
  ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ Mα₀thresh : ℝ, 0 < Mα₀thresh →
    ∀ U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) witnessL,
    IsRegularHolonomy U Mα₀thresh →
    ∀ B : subspace156BFL2 Lambda S' ell U,
      γ₀ * ‖(B : BFL2 witnessL)‖ ^ 2 ≤ deltaKFormOnSubspace156 bc Qext J Lambda S' ell U B

noncomputable def regB0 :
    subspace156BFL2 (Finset.univ : Finset (PeriodicLatticeSite witnessL)) ∅ witnessEll
      (trivialU witnessL) :=
  ⟨(bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo, by
    show (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ∈
      subspace156BFL2 Finset.univ ∅ witnessEll (trivialU witnessL)
    show checkerConfigSuTwo ∈ subspace156G Finset.univ ∅ witnessEll (trivialU witnessL)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro b hb; exact absurd (Finset.mem_univ b.1) hb
    · intro y hy; exact absurd hy (Finset.notMem_empty y)
    · exact checkerConfigSuTwo_mem_q1RealKernel_trivialU⟩

theorem regB0_ne_zero : (regB0 : BFL2 witnessL) ≠ 0 := by
  show (bfl2Equiv (Lat := witnessL)).symm checkerConfigSuTwo ≠ 0
  intro h
  apply checkerConfigSuTwo_ne_zero
  have hc := congrArg (bfl2Equiv (Lat := witnessL)) h
  simpa using hc

theorem regB0_norm_pos : (0 : ℝ) < ‖(regB0 : BFL2 witnessL)‖ := norm_pos_iff.mpr regB0_ne_zero

theorem norm_smul_real_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (B : E) :
    ‖t • B‖ ^ 2 = t ^ 2 * ‖B‖ ^ 2 := by
  rw [norm_smul]
  simp [mul_pow, Real.norm_eq_abs, sq_abs]

noncomputable def qextQuad (v0 : BFL2 witnessL) : BFL2 witnessL → BFL2 witnessL :=
  fun x => ‖x‖ ^ 2 • v0

theorem dtilde2_qextQuad (v0 B : BFL2 witnessL) :
    Dtilde2Shape (qextQuad v0) B = ‖B‖ ^ 2 • v0 := by
  show taylorQuadraticTerm (fun t : ℝ => qextQuad v0 (t • B)) = ‖B‖ ^ 2 • v0
  have heq : (fun t : ℝ => qextQuad v0 (t • B)) = fun t : ℝ => t ^ 2 • (‖B‖ ^ 2 • v0) := by
    funext t
    show ‖t • B‖ ^ 2 • v0 = t ^ 2 • (‖B‖ ^ 2 • v0)
    rw [norm_smul_real_sq, smul_smul]
  rw [heq]
  exact taylorQuadraticTerm_sq_smul (‖B‖ ^ 2 • v0)

theorem solutionOperator_deltaKUnifiedData_eq_id (x : BFL2 witnessL) :
    solutionOperator deltaKUnifiedData x = x := by
  rw [solutionOperator_apply]
  show GstarBFL2 ((1 : BFL2 witnessL →L[ℝ] BFL2 witnessL) (GinvBFL2 x)) = x
  rw [ContinuousLinearMap.one_apply]
  show GstarBFL2 (GinvBFL2 x) = x
  exact GstarBFL2_GinvBFL2 x

noncomputable def adversarialJ (bc : BaseConstant) : BFL2 witnessL :=
  ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖ ^ 2)) • (regB0 : BFL2 witnessL)

theorem deltaKFormOnSubspace156_adversarial_eq (bc : BaseConstant) :
    deltaKFormOnSubspace156 bc (qextQuad (regB0 : BFL2 witnessL)) (adversarialJ bc)
        Finset.univ ∅ witnessEll (trivialU witnessL) regB0 =
      (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 - (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 := by
  rw [deltaKFormOnSubspace156_eq]
  unfold deltaKForm
  have hCompInv : (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) =
      (1 / 2 : ℝ) • (regB0 : BFL2 witnessL) := rfl
  have hinnerCompInv : (inner ℝ (regB0 : BFL2 witnessL)
      (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) : ℝ) =
      (1 / 2 : ℝ) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 := by
    rw [hCompInv, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hself : (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hD2 : Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 • (regB0 : BFL2 witnessL) :=
    dtilde2_qextQuad (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL)
  have hH1 : solutionOperator deltaKUnifiedData
      (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 • (regB0 : BFL2 witnessL) := by
    rw [hD2]; exact solutionOperator_deltaKUnifiedData_eq_id _
  have hsrc : (inner ℝ (solutionOperator deltaKUnifiedData
      (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)))
      (adversarialJ bc) : ℝ) =
      ‖(regB0 : BFL2 witnessL)‖ ^ 2 *
        ((1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖ ^ 2) * ‖(regB0 : BFL2 witnessL)‖ ^ 2) := by
    rw [hH1]
    unfold adversarialJ
    rw [real_inner_smul_left, real_inner_smul_right, hself]
  show (inner ℝ (regB0 : BFL2 witnessL) (deltaKUnifiedData.CompInv (regB0 : BFL2 witnessL)) : ℝ)
      - usedAt bc 0 * (inner ℝ (regB0 : BFL2 witnessL) (regB0 : BFL2 witnessL) : ℝ)
      - 2 * (inner ℝ (solutionOperator deltaKUnifiedData
          (Dtilde2Shape (qextQuad (regB0 : BFL2 witnessL)) (regB0 : BFL2 witnessL)))
          (adversarialJ bc) : ℝ) = _
  rw [hinnerCompInv, hself, hsrc]
  unfold usedAt
  have hne : ‖(regB0 : BFL2 witnessL)‖ ^ 2 ≠ 0 := (pow_pos regB0_norm_pos 2).ne'
  field_simp

theorem adversarial_value_neg (bc : BaseConstant) :
    (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 -
        (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 < 0 := by
  have hle : (1 / 2 - bc.a) ≤ |1 / 2 - bc.a| := le_abs_self _
  have hbnd : (1 / 2 - bc.a) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 -
      (1 + |1 / 2 - bc.a|) * ‖(regB0 : BFL2 witnessL)‖ ^ 2 ≤
      -(‖(regB0 : BFL2 witnessL)‖ ^ 2) := by
    have hstep : (1 / 2 - bc.a) - (1 + |1 / 2 - bc.a|) ≤ -1 := by linarith
    nlinarith [sq_nonneg (‖(regB0 : BFL2 witnessL)‖), regB0_norm_pos]
  have hpos : (0 : ℝ) < ‖(regB0 : BFL2 witnessL)‖ ^ 2 := pow_pos regB0_norm_pos 2
  linarith

theorem theLemma_regularU_false_without_source_constraint (bc : BaseConstant) :
    ¬ TheLemmaRegularU bc (qextQuad (regB0 : BFL2 witnessL)) (adversarialJ bc)
        Finset.univ ∅ witnessEll := by
  rintro ⟨γ₀, hγ₀pos, hbound⟩
  have hb := hbound 1 one_pos (trivialU witnessL)
    (trivialU_isRegularHolonomy (by norm_num : (0:ℝ) ≤ 1)) regB0
  rw [deltaKFormOnSubspace156_adversarial_eq] at hb
  have hneg := adversarial_value_neg bc
  have hlhspos : (0 : ℝ) < γ₀ * ‖(regB0 : BFL2 witnessL)‖ ^ 2 :=
    mul_pos hγ₀pos (pow_pos regB0_norm_pos 2)
  linarith

theorem deltaKUnifiedData_first_two_terms_eq (bc : BaseConstant) (B : BFL2 witnessL) :
    (inner ℝ B (deltaKUnifiedData.CompInv B) : ℝ) - usedAt bc 0 * (inner ℝ B B : ℝ) =
      (1 / 2 - bc.a) * ‖B‖ ^ 2 := by
  have hCompInv : deltaKUnifiedData.CompInv B = (1 / 2 : ℝ) • B := rfl
  rw [hCompInv, real_inner_smul_right, real_inner_self_eq_norm_sq]
  unfold usedAt
  ring

namespace Source
open Matrix AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.CovariantHj
  AdalyFormal.Balaban.DeltaPrime
variable {L : PeriodicLatticeExtent}

noncomputable def piProj (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  X - (Matrix.trace X / (2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

noncomputable def FnuMu
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (ν μ : Fin 3) (y : PeriodicLatticeSite L) : Matrix (Fin 2) (Fin 2) ℂ :=
  if hlt : ν < μ then piProj (imHolonomy U (y, ⟨(ν, μ), hlt⟩))
  else if hgt : μ < ν then -piProj (imHolonomy U (y, ⟨(μ, ν), hgt⟩))
  else 0

noncomputable def DstarDir
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν : Fin 3)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ) (x : PeriodicLatticeSite L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  conjByAmbient (U (periodicLatticeShiftBack x ν, ν))⁻¹ (G (periodicLatticeShiftBack x ν)) - G x

noncomputable def Jfield
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ ν : Fin 3, if ν = μ then 0 else DstarDir U ν (fun y => FnuMu U ν μ y) x

noncomputable def Jsource
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    Bond L → Matrix (Fin 2) (Fin 2) ℂ :=
  fun b => Jfield U b.1 b.2

theorem FnuMu_trivialU (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    FnuMu (DeltaPrime.trivialU (L := L)) ν μ y = 0 := by
  unfold FnuMu
  split_ifs with h1 h2
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rw [imHolonomy_trivialU]; unfold piProj; simp
  · rfl

theorem DstarDir_trivialU_eq_zero_of_G_zero (ν : Fin 3)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ) (hG : ∀ y, G y = 0)
    (x : PeriodicLatticeSite L) : DstarDir (DeltaPrime.trivialU (L := L)) ν G x = 0 := by
  unfold DstarDir
  rw [hG, hG]
  simp [conjByAmbient_apply]

theorem Jfield_trivialU (x : PeriodicLatticeSite L) (μ : Fin 3) :
    Jfield (DeltaPrime.trivialU (L := L)) x μ = 0 := by
  unfold Jfield
  apply Finset.sum_eq_zero
  intro ν _
  split_ifs with h
  · rfl
  · exact DstarDir_trivialU_eq_zero_of_G_zero ν _ (fun y => FnuMu_trivialU ν μ y) x

theorem Jsource_trivialU_eq_zero (b : Bond L) : Jsource (DeltaPrime.trivialU (L := L)) b = 0 :=
  Jfield_trivialU b.1 b.2

end Source
end HConstruction.Reproduced

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`HConstruction.Reproduced.theLemma_regularU_false_without_source_constraint,
      `HConstruction.Reproduced.dtilde2_qextQuad,
      `HConstruction.Reproduced.regB0_ne_zero,
      `HConstruction.Reproduced.Source.Jsource_trivialU_eq_zero] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing reproduced declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {name}: {ax}"
    Lean.logInfo m!"REPRODUCED_AXIOMS {name}: {axioms}"

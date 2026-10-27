import Reproduced

/-!
Candidate at the NATIVE one-step fine-to-coarse type, not a coercivity claim.
CMP98 (149), printed p.40, bounds a remainder VARIATION. The kernel below is
(140), i.e. the j=1 seed of (141); it is not a second derivative. We normalize
eta=1/ell, so ell*eta=1 and (150)'s remainder argument is A itself.

C3/radius and the background are fixed outside Qext. This file does not assert
that a numerical C3 or this norm/stencil convention has been certified by the
paper. In particular no witness of the second conjunct is postulated.
-/
set_option autoImplicit false
namespace HConstruction.Predicate

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.SuTwoLogExp (su2NegOne)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalyQIdentification.QV (rawInChart hasDerivAt_rawInChart rawInChart_zero)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open HConstruction.Reproduced

noncomputable local instance : NormedAddCommGroup M2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ M2 := Matrix.linftyOpNormedSpace
noncomputable local instance : NormedSpace ℂ M2 := Matrix.linftyOpNormedSpace

variable {L : PeriodicLatticeExtent}
abbrev Fine (L : PeriodicLatticeExtent) := CoarseBond L 1 → SuTwo
abbrev Output (L : PeriodicLatticeExtent) (ell : ℕ) := CoarseBond L (1 * ell) → M2

noncomputable def linearQ (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : Fine L) : Output L ell :=
  fun c => ((q124Principal 1 ell U A c : SuTwo) : M2)

/-- The actual normalized physical nonlinear map, NOT its linearization. -/
noncomputable def actualQ (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : Fine L) : Output L ell :=
  fun c => rawInChart U ell A (ell : ℝ)⁻¹ c

/-- A ray equality, to reuse the certified first derivative without rebuilding SI1. -/
theorem actualQ_ray (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : Fine L) (t : ℝ) (c : CoarseBond L (1 * ell)) :
    actualQ U ell (t • A) c = rawInChart U ell A ((ell : ℝ)⁻¹ * t) c := by
  unfold actualQ rawInChart
  congr 2
  funext e
  congr 1
  change (ell : ℝ)⁻¹ • (t • _) = ((ell : ℝ)⁻¹ * t) • _
  rw [smul_smul]
  rfl

/-- (a), with an actual derivative, not merely a totalized deriv value. -/
def FirstJet (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (Q : Fine L → Output L ell) : Prop :=
  ∀ A c, HasDerivAt (fun t : ℝ => Q (t • A) c) (linearQ U ell A c) 0

/-- The two-block positive stencil; b ⊂ union means both endpoints lie in it. -/
noncomputable def kernel149 (ell : ℕ) (dA : Fine L)
    (c : CoarseBond L (1 * ell)) : ℝ :=
  let sites := blockOf c.1.1 ell ∪ blockOf
    (AdalyFormal.Balaban.QOne.pathSite c.1.1 c.2 ell) ell
  ∑ b : CoarseBond L 1,
    if b.1.1 ∈ sites ∧ periodicLatticeShift b.1.1 b.2 ∈ sites
    then (ell : ℝ)⁻¹ ^ 3 * ‖dA b‖ else 0

noncomputable def remainder (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (Q : Fine L → Output L ell) (A : Fine L) : Output L ell :=
  Q A - linearQ U ell A

/-- (b), the local derivative-of-remainder version of (149), at j=1.
Requires existence of the derivative, so nondifferentiable junk is not admitted
through Mathlib's convention deriv f x = 0 when f is not differentiable there.
This is a CANDIDATE norm realization, not a proved transcription-equivalence. -/
def VariationBound149 (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (C3 radius : ℝ) (Q : Fine L → Output L ell) : Prop :=
  0 < C3 ∧ 0 < radius ∧
    ∀ A : Fine L, ‖A‖ < radius → ∀ dA c, ∃ V : M2,
      HasDerivAt (fun t : ℝ => remainder U ell Q (A + t • dA) c) V 0 ∧
      ‖V‖ ≤ C3 * ‖A‖ * kernel149 ell dA c

/-- (c), equality in the source's native Hermitian convention. -/
def GenuineJ (U : PeriodicLinkConfiguration SU2 L)
    (J : Bond L → M2) : Prop := J = Source.Jsource U

/-- Three conjuncts, with U outside the predicate, not hidden behind a fixed J.
Not an exact predicate on the old deltaKForm endomorphism slot: see REPORT.md. -/
def IsFaithfulSourceCandidate (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (C3 radius : ℝ) (Q : Fine L → Output L ell)
    (J : Bond L → M2) : Prop :=
  FirstJet U ell Q ∧ VariationBound149 U ell C3 radius Q ∧ GenuineJ U J

/-- Uses the already-certified derivative; no SI1 proof is rerun here. -/
theorem actualQ_firstJet (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc : ∀ c : CoarseBond L (1 * ell), ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell U (c.1.1, c.2) x ≠ su2NegOne) :
    FirstJet U ell (actualQ U ell) := by
  intro A c
  have hd := hasDerivAt_rawInChart U ell hell hdvd A c (hnc c) (ell : ℝ)⁻¹
  have he : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)
  simpa only [actualQ_ray, mul_inv_cancel₀ he, one_smul, linearQ] using hd

/-- The source chart guard is paid at a genuine fitted, non-collapsed block size 2. -/
theorem trivial_loop_guard (ell : ℕ) (c : CoarseBond L (1 * ell))
    (x : PeriodicLatticeSite L) :
    loopVar 1 ell (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)
      (c.1.1, c.2) x ≠ su2NegOne := by
  have he : loopVar 1 ell (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L)
      (c.1.1, c.2) x = 1 := by
    simp [loopVar, AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided,
      AdalyFormal.Balaban.UbarTowerCov.coarseBondVar,
      AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]
  rw [he]
  exact AdalyFormal.Balaban.SuTwoLogExp.su2NegOne_ne_one.symm

theorem actualQ_witness_firstJet :
    FirstJet (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2
      (actualQ (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2) := by
  exact actualQ_firstJet _ 2 (by norm_num) (by decide)
    (fun c x _ => trivial_loop_guard 2 c x)

theorem actualQ_zero (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    actualQ U ell 0 = 0 := by
  funext c
  unfold actualQ rawInChart
  have hz : (fun e => AdalyFormal.Balaban.SuTwoLogExp.su2Exp
      ((ell : ℝ)⁻¹ • AdalySI1.Multiscale.M2.unitBondDir (0 : Fine L) e)) =
      AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L := by
    funext e
    simp [AdalySI1.Multiscale.M2.unitBondDir,
      AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]
  rw [hz, AdalySI1.ModifiedAverageDeriv.modifiedAverage_trivialU,
    AdalyFormal.Balaban.SuTwoLogExp.su2Log_one]
  rfl

theorem source_trivial_genuine :
    GenuineJ (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) 0 := by
  funext b
  exact (Source.Jsource_trivialU_eq_zero b).symm

/-- Full, lossless inverse chart for comparison to the old BFL2 source slot. -/
noncomputable def sourceCoordinates (J : BFL2 L) : Bond L → M2 :=
  fun b => (-Complex.I) • ((bfl2Equiv J b : SuTwo) : M2)

/-- Multiplication by -i is invertible; no scalar-coordinate projection. -/
theorem sourceCoordinates_eq_zero_iff (J : BFL2 L) :
    sourceCoordinates J = 0 ↔ J = 0 := by
  constructor
  · intro h
    apply bfl2Equiv.injective
    rw [map_zero]
    funext b
    apply Subtype.ext
    have hb := congrFun h b
    have hi := congrArg (fun X : M2 => Complex.I • X) hb
    simpa [sourceCoordinates, smul_smul] using hi
  · rintro rfl
    funext b
    change (-Complex.I) • ((0 : SuTwo) : M2) = 0
    simp

/-- The existing full i-chart transport, promoted to the old carrier without loss. -/
noncomputable def genuineSource (U : PeriodicLinkConfiguration SU2 L) : BFL2 L :=
  bfl2Equiv.symm (AdalyFormal.Balaban.DeltaKSuTwoFaithful.JsourceSu U)

/-- This is exactly the reproduced Jsource, not a replacement scalar functional. -/
theorem genuineSource_exact (U : PeriodicLinkConfiguration SU2 L) :
    sourceCoordinates (genuineSource U) = Source.Jsource U := by
  funext b
  change (-Complex.I) •
    ((AdalyFormal.Balaban.DeltaKSuTwoFaithful.JsourceSu U b : SuTwo) : M2) = _
  exact AdalyFormal.Balaban.DeltaKSuTwoFaithful.JsourceSu_recovers U b

theorem genuineSource_trivial :
    genuineSource (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) = 0 := by
  apply (sourceCoordinates_eq_zero_iff _).mp
  rw [genuineSource_exact]
  funext b
  exact Source.Jsource_trivialU_eq_zero b

theorem genuineSource_witness_ne_zero :
    genuineSource AdalyFormal.Balaban.CovariantOperators.witnessU ≠ 0 := by
  intro h
  have hz := (sourceCoordinates_eq_zero_iff _).mpr h
  rw [genuineSource_exact] at hz
  exact AdalyFormal.Balaban.SourceJ.Jsource_witnessU_ne_zero
    (congrFun hz (witnessY, (0 : Fin 3)))

/-- Actual counterexample source is not zero, for EVERY BaseConstant. -/
theorem adversarialJ_ne_zero (bc : AdalyFormal.Balaban.ConstantA.BaseConstant) :
    adversarialJ bc ≠ 0 := by
  have hc : 0 < (1 + |1 / 2 - bc.a|) / (2 * ‖(regB0 : BFL2 witnessL)‖ ^ 2) :=
    div_pos (by positivity) (mul_pos (by norm_num) (pow_pos regB0_norm_pos 2))
  exact smul_ne_zero hc.ne' regB0_ne_zero

/-- Rejects precisely the background in the frozen falsifying theorem.
It deliberately says NOTHING about every (possibly irregular) background. -/
theorem adversarialJ_fails_genuineJ (bc : AdalyFormal.Balaban.ConstantA.BaseConstant) :
    ¬ GenuineJ (AdalyFormal.Balaban.DeltaPrime.trivialU (L := witnessL))
      (sourceCoordinates (adversarialJ bc)) := by
  intro h
  have hz : sourceCoordinates (adversarialJ bc) = 0 := by
    funext b
    exact (congrFun h b).trans (Source.Jsource_trivialU_eq_zero b)
  exact adversarialJ_ne_zero bc ((sourceCoordinates_eq_zero_iff _).mp hz)

/-- The old qextQuad really has zero first derivative, regardless of direction. -/
theorem qextQuad_hasDerivAt_zero (v A : BFL2 witnessL) :
    HasDerivAt (fun t : ℝ => qextQuad v (t • A)) 0 0 := by
  have heq : (fun t : ℝ => qextQuad v (t • A)) =
      (fun t : ℝ => t ^ 2 • (‖A‖ ^ 2 • v)) := by
    funext t
    simp only [qextQuad, norm_smul_real_sq, smul_smul]
  rw [heq]
  simpa using ((hasDerivAt_pow 2 (0 : ℝ)).smul_const (‖A‖ ^ 2 • v))

/-- Rejection for every specified nonzero first jet. A concrete q124 nonzero
component is still required to specialize this theorem at the native types. -/
theorem qextQuad_fails_nonzero_firstJet (v : BFL2 witnessL)
    (q : BFL2 witnessL → BFL2 witnessL) (hq : ∃ A, q A ≠ 0) :
    ¬ (∀ A, HasDerivAt (fun t : ℝ => qextQuad v (t • A)) (q A) 0) := by
  intro h
  obtain ⟨A, hA⟩ := hq
  exact hA ((h A).unique (qextQuad_hasDerivAt_zero v A))

end HConstruction.Predicate

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`HConstruction.Predicate.actualQ_firstJet,
      `HConstruction.Predicate.trivial_loop_guard,
      `HConstruction.Predicate.actualQ_witness_firstJet,
      `HConstruction.Predicate.actualQ_zero,
      `HConstruction.Predicate.source_trivial_genuine,
      `HConstruction.Predicate.sourceCoordinates_eq_zero_iff,
      `HConstruction.Predicate.genuineSource_exact,
      `HConstruction.Predicate.genuineSource_trivial,
      `HConstruction.Predicate.genuineSource_witness_ne_zero,
      `HConstruction.Predicate.adversarialJ_ne_zero,
      `HConstruction.Predicate.adversarialJ_fails_genuineJ,
      `HConstruction.Predicate.qextQuad_hasDerivAt_zero,
      `HConstruction.Predicate.qextQuad_fails_nonzero_firstJet] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing predicate test: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard predicate axiom in {name}: {ax}"
    Lean.logInfo m!"PREDICATE_AXIOMS {name}: {axioms}"

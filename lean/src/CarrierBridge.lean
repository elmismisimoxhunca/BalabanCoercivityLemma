import SourcePredicate
import NonzeroJet

/-!
The native map is rectangular. These transports do not turn it into an
endomorphism by renaming its output or repeating coarse values. The only
endomorphism below is an explicitly named restriction along the already-existing
variational solution operator, with K the actual coarse-output Hilbert space.
No assertion identifies that restriction with CMP99b's unit-block D-tilde.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace HConstruction.Carrier
open HConstruction.Predicate HConstruction.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond witnessL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Log_antiHermitian su2Log_traceless)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.VariationalProjectorH1
  (BalabanCovarianceData solutionOperator interpolates)

noncomputable local instance : NormedAddCommGroup M2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ M2 := Matrix.linftyOpNormedSpace
noncomputable local instance : NormedSpace ℂ M2 := Matrix.linftyOpNormedSpace
variable {L : PeriodicLatticeExtent}

/-- The coarse analogue of BFL2, with one consistent PiLp instance family. -/
def CFL2 (L : PeriodicLatticeExtent) (ell : ℕ) : Type :=
  WithLp 2 (CoarseBond L (1 * ell) → SuTwo)
noncomputable instance (ell : ℕ) : NormedAddCommGroup (CFL2 L ell) :=
  PiLp.normedAddCommGroup (p := 2) (α := fun _ : CoarseBond L (1 * ell) => SuTwo)
noncomputable instance (ell : ℕ) : InnerProductSpace ℝ (CFL2 L ell) :=
  PiLp.innerProductSpace (𝕜 := ℝ) (f := fun _ : CoarseBond L (1 * ell) => SuTwo)
noncomputable instance (ell : ℕ) : FiniteDimensional ℝ (CFL2 L ell) :=
  (inferInstance : FiniteDimensional ℝ (PiLp 2 (fun _ : CoarseBond L (1 * ell) => SuTwo)))
noncomputable instance (ell : ℕ) : CompleteSpace (CFL2 L ell) :=
  FiniteDimensional.complete ℝ (CFL2 L ell)
noncomputable def cfl2Equiv (ell : ℕ) : CFL2 L ell ≃ₗ[ℝ] (CoarseBond L (1 * ell) → SuTwo) :=
  WithLp.linearEquiv 2 ℝ _

/-- Unit bonds and all fine bonds are genuinely bijective; no bond is discarded. -/
def unitBondEquiv : CoarseBond L 1 ≃ Bond L where
  toFun b := (b.1.1, b.2)
  invFun b := (⟨b.1, AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one b.1⟩, b.2)
  left_inv b := by cases b; rfl
  right_inv b := rfl

noncomputable def fineCoordinates : BFL2 L ≃ₗ[ℝ] Fine L :=
  bfl2Equiv.trans (LinearEquiv.funCongrLeft ℝ SuTwo unitBondEquiv)

@[simp] theorem fineCoordinates_apply (B : BFL2 L) (b : CoarseBond L 1) :
    fineCoordinates B b = bfl2Equiv B (b.1.1, b.2) := rfl

/-- The log is ALWAYS in su(2), including its totalized cut value. No projection. -/
theorem actualQ_mem (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : Fine L) (c : CoarseBond L (1 * ell)) : actualQ U ell A c ∈ suTwo :=
  ⟨su2Log_antiHermitian _, su2Log_traceless _⟩

noncomputable def nativeQ (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    BFL2 L → CFL2 L ell := fun B =>
  (cfl2Equiv ell).symm (fun c => ⟨actualQ U ell (fineCoordinates B) c, actualQ_mem U ell _ c⟩)

/-- ALL native outputs recovered exactly. This is the rectangular carrier bridge. -/
theorem nativeQ_exact (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (B : BFL2 L) (c : CoarseBond L (1 * ell)) :
    ((cfl2Equiv ell (nativeQ U ell B) c : SuTwo) : M2) =
      actualQ U ell (fineCoordinates B) c := rfl

@[simp] theorem nativeQ_zero (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    nativeQ U ell 0 = 0 := by
  apply (cfl2Equiv ell).injective
  funext c
  apply Subtype.ext
  change actualQ U ell (fineCoordinates 0) c = 0
  rw [map_zero, actualQ_zero]
  rfl

/-- This is a restriction of the INPUT to ran(H_D), not an extension of the
coarse OUTPUT onto fine bonds. H_D is the pre-existing variational operator. -/
noncomputable def variationalQext (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (D : BalabanCovarianceData (BFL2 L) (CFL2 L ell)) : CFL2 L ell → CFL2 L ell :=
  fun B => nativeQ U ell (solutionOperator D B)

theorem variationalQext_exact (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (D : BalabanCovarianceData (BFL2 L) (CFL2 L ell))
    (B : CFL2 L ell) (c : CoarseBond L (1 * ell)) :
    ((cfl2Equiv ell (variationalQext U ell D B) c : SuTwo) : M2) =
      actualQ U ell (fineCoordinates (solutionOperator D B)) c := rfl

/-- Normal form of the unchanged deltaKForm at the honest coarse carrier. -/
theorem deltaKForm_variational (U : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (D : BalabanCovarianceData (BFL2 L) (CFL2 L ell))
    (bc : AdalyFormal.Balaban.ConstantA.BaseConstant) (B : CFL2 L ell) :
    deltaKForm D bc (variationalQext U ell D) (genuineSource U) B =
      (inner ℝ B (D.CompInv B) : ℝ) - AdalyFormal.Balaban.ConstantA.usedAt bc 0 *
      (inner ℝ B B : ℝ) - 2 *
      (inner ℝ (solutionOperator D (Dtilde2Shape
        (fun X => nativeQ U ell (solutionOperator D X)) B)) (genuineSource U) : ℝ) := rfl

/-- The input restriction is injective, an actual copy of K inside H. -/
theorem variational_input_injective (ell : ℕ)
    (D : BalabanCovarianceData (BFL2 L) (CFL2 L ell)) :
    Function.Injective (fun B => fineCoordinates (solutionOperator D B)) := by
  intro B C h
  have h1 := fineCoordinates.injective h
  have h2 := congrArg D.Q h1
  simpa only [interpolates] using h2

/-- The already-certified native jet survives the input restriction exactly.
It is q124(H_D B), NOT B unless D.Q has separately been identified with q124. -/
theorem variationalQext_native_firstJet (U : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hjet : FirstJet U ell (actualQ U ell))
    (D : BalabanCovarianceData (BFL2 L) (CFL2 L ell))
    (B : CFL2 L ell) (c : CoarseBond L (1 * ell)) :
    HasDerivAt (fun t : ℝ => ((cfl2Equiv ell
      (variationalQext U ell D (t • B)) c : SuTwo) : M2))
      (linearQ U ell (fineCoordinates (solutionOperator D B)) c) 0 := by
  simpa only [variationalQext_exact, map_smul] using
    hjet (fineCoordinates (solutionOperator D B)) c

/-- Unconditional at the genuine fitted block-two background, all D. -/
theorem variationalQext_witness_firstJet
    (D : BalabanCovarianceData (BFL2 witnessL) (CFL2 witnessL 2))
    (B : CFL2 witnessL 2) (c : CoarseBond witnessL (1 * 2)) :
    HasDerivAt (fun t : ℝ => ((cfl2Equiv 2 (variationalQext
      (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2 D (t • B)) c : SuTwo) : M2))
      (linearQ (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2
        (fineCoordinates (solutionOperator D B)) c) 0 :=
  variationalQext_native_firstJet _ 2 actualQ_witness_firstJet D B c

/-- The true map survives the rectangular chart; no zero map was substituted. -/
theorem nativeQ_witness_ne_zero :
    nativeQ (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2 ≠ fun _ => 0 := by
  intro hn
  have hz : actualQ (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU witnessL) 2 = fun _ => 0 := by
    funext A c
    have h := congrFun hn (fineCoordinates.symm A)
    have h1 := congrArg (fun X : CFL2 witnessL 2 => ((cfl2Equiv 2 X c : SuTwo) : M2)) h
    simpa only [nativeQ_exact, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply,
      Submodule.coe_zero] using h1
  have hd := actualQ_witness_firstJet HConstruction.NonzeroJet.A0 HConstruction.NonzeroJet.c0
  rw [hz] at hd
  exact HConstruction.NonzeroJet.linearQ_A0_ne_zero
    (hd.unique (hasDerivAt_const (0 : ℝ) (0 : M2)))

/-- There are 192 fine bonds but only 24 coarse bonds at the genuine size-two witness. -/
theorem witness_bond_counts : Fintype.card (Bond witnessL) = 192 ∧
    Fintype.card (CoarseBond witnessL (1 * 2)) = 24 := by
  constructor <;> decide

/-- No lossless linear change of coordinates can make the old BFL2 carrier the
native coarse output. This rules out a bfl2Equiv-style chart-only solution. -/
theorem no_fine_coarse_linearEquiv :
    IsEmpty (BFL2 witnessL ≃ₗ[ℝ] CFL2 witnessL 2) := by
  refine ⟨fun e => ?_⟩
  have h := (bfl2Equiv.symm.trans (e.trans (cfl2Equiv 2))).finrank_eq
  have hf : Module.finrank ℝ (Bond witnessL → SuTwo) =
      192 * Module.finrank ℝ SuTwo := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, witness_bond_counts.1]
  have hc : Module.finrank ℝ (CoarseBond witnessL (1 * 2) → SuTwo) =
      24 * Module.finrank ℝ SuTwo := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, witness_bond_counts.2]
  rw [hf, hc] at h
  have hp : 0 < Module.finrank ℝ SuTwo := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero⟩
  omega

end HConstruction.Carrier

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`HConstruction.Carrier.nativeQ_exact,
      `HConstruction.Carrier.nativeQ_zero,
      `HConstruction.Carrier.variationalQext_exact,
      `HConstruction.Carrier.deltaKForm_variational,
      `HConstruction.Carrier.variational_input_injective,
      `HConstruction.Carrier.variationalQext_witness_firstJet,
      `HConstruction.Carrier.nativeQ_witness_ne_zero,
      `HConstruction.Carrier.no_fine_coarse_linearEquiv] do
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do throwError "Nonstandard carrier axiom {name}: {ax}"
    Lean.logInfo m!"CARRIER_AXIOMS {name}: {← Lean.collectAxioms name}"

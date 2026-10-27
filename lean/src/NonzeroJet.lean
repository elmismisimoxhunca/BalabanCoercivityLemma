import SourcePredicate
set_option autoImplicit false
namespace HConstruction.NonzeroJet
open HConstruction.Predicate
open HConstruction.Reproduced
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero RMap_one)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.DeltaKUnified (BFL2 bfl2Equiv)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.DeltaKR66
open AdalyFormal.DeltaKR85 (q124Principal Coeff124.ofPrincipalBackground)
open OneStep124
open AdalyFormal.Balaban.SuTwoLogExp (M2)

noncomputable local instance : NormedAddCommGroup M2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ M2 := Matrix.linftyOpNormedSpace
noncomputable local instance : NormedSpace ℂ M2 := Matrix.linftyOpNormedSpace

/-- The same fitted block size 2 on the existing 4^3 witness lattice. -/
def c0 : CoarseBond witnessL (1 * 2) := (⟨witnessY, by decide⟩, 0)
noncomputable def A0 : Fine witnessL := fun _ => suTwoWitness

lemma ad_zero : adOp (0 : SuTwo) = 0 := by
  ext X i j
  simp [adOp, adLM, adVal]

lemma g_zero : gOp (0 : SuTwo →L[ℝ] SuTwo) = 1 := by
  unfold gOp
  rw [tsum_eq_single 0]
  · simp [gCoeff]
  · intro n hn
    rw [zero_pow hn]
    ext X i j
    simp

lemma exp_zero : expOp (0 : SuTwo →L[ℝ] SuTwo) = 1 := by
  unfold expOp
  rw [tsum_eq_single 0]
  · simp [expCoeff]
  · intro n hn
    rw [zero_pow hn]
    ext X i j
    simp

lemma ginv_zero : gInvOp (0 : SuTwo →L[ℝ] SuTwo) = 1 := by
  simp [gInvOp, g_zero]

lemma logs_zero (c : CoarseBond witnessL (1 * 2)) (x : PeriodicLatticeSite witnessL) :
    (sourcePrincipalLogData 1 2 (trivialU witnessL)).Zx c x = 0 := by
  apply Subtype.ext
  change AdalyFormal.Balaban.SuTwoLogExp.su2Log
    (AdalyFormal.Balaban.UbarTowerCov.loopVar 1 2 (trivialU witnessL) (c.1.1, c.2) x) = 0
  simp [AdalyFormal.Balaban.UbarTowerCov.loopVar,
    AdalyFormal.Balaban.UbarTowerCov.gammaVarStrided,
    AdalyFormal.Balaban.UbarTowerCov.coarseBondVar,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU]

lemma meanlog_zero (c : CoarseBond witnessL (1 * 2)) :
    (sourcePrincipalLogData 1 2 (trivialU witnessL)).Z c = 0 := by
  simp [LogData.Z, logs_zero]

lemma card_c0 : (unitSitesOf 1 2 c0.1.1).card = 8 := by decide

lemma E1_zero (x : PeriodicLatticeSite witnessL) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E1 c0 x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero]

lemma E2_zero (x : PeriodicLatticeSite witnessL) :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E2 c0 x = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero]

lemma E3_zero :
    (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)).E3 c0 = 0 := by
  simp [Coeff124.ofPrincipalBackground, Coeff124.ofBackground,
    meanlog_zero, logs_zero, ad_zero, g_zero, ginv_zero, exp_zero, card_c0]
  ext X i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.ofNat_apply] <;> ring

lemma q124_A0 : q124Principal 1 2 (trivialU witnessL) A0 c0 = suTwoWitness := by
  rw [AdalyFormal.DeltaKR85.q124Principal_eq_unitToCoarseCov_add_delta]
  have hd : delta124 1 2 (trivialU witnessL)
      (Coeff124.ofPrincipalBackground 1 2 (trivialU witnessL)) A0 c0 = 0 := by
    simp [delta124, term2, term3, term4, term5, E1_zero, E2_zero, E3_zero]
  rw [hd, add_zero]
  simp [AdalyFormal.Balaban.TowerLawCov.unitToCoarseCov, A0,
    AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one,
    AdalyFormal.Balaban.TowerLawCov.coarsePathHolonomy_trivialU,
    RMap_one, card_c0, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ 16 suTwoWitness, smul_smul]
  norm_num

lemma linearQ_A0_ne_zero : linearQ (trivialU witnessL) 2 A0 c0 ≠ 0 := by
  intro h
  apply suTwoWitness_ne_zero
  have hq : q124Principal 1 2 (trivialU witnessL) A0 c0 = 0 := Subtype.ext h
  rw [q124_A0] at hq
  exact hq

/-- Original fine carrier, no repetition or interpolation of coarse outputs. -/
noncomputable def asBFL2 (A : Fine witnessL) : BFL2 witnessL :=
  bfl2Equiv.symm (fun b => A (⟨b.1,
    AdalyFormal.Balaban.StridedAveraging.mem_coarseLattice_one b.1⟩, b.2))

lemma asBFL2_smul (t : ℝ) (A : Fine witnessL) : asBFL2 (t • A) = t • asBFL2 A := by
  apply bfl2Equiv.injective
  rfl

/-- Restrict the frozen adversarial endomorphism to the native coarse outputs.
Restriction is used ONLY to falsify its first jet, never to fabricate a full
endomorphism or assert control on discarded fine outputs. -/
noncomputable def oldQuadNative (v : BFL2 witnessL) (A : Fine witnessL) : Output witnessL 2 :=
  fun c => ((bfl2Equiv (qextQuad v (asBFL2 A)) (c.1.1, c.2) : SuTwo) : M2)

lemma oldQuadNative_deriv (v : BFL2 witnessL) (A : Fine witnessL)
    (c : CoarseBond witnessL (1 * 2)) :
    HasDerivAt (fun t : ℝ => oldQuadNative v (t • A) c) 0 0 := by
  have he : (fun t : ℝ => oldQuadNative v (t • A) c) =
      fun t : ℝ => t ^ 2 •
        ((bfl2Equiv (‖asBFL2 A‖ ^ 2 • v) (c.1.1, c.2) : SuTwo) : M2) := by
    funext t
    simp only [oldQuadNative, asBFL2_smul, qextQuad, norm_smul_real_sq,
      mul_smul, map_smul, Pi.smul_apply]
    rfl
  rw [he]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt (fun t : ℝ => t ^ 2 •
    ((((bfl2Equiv (‖asBFL2 A‖ ^ 2 • v) (c.1.1, c.2) : SuTwo) : M2)) i j)) (0 : ℂ) 0
  convert (hasDerivAt_pow 2 (0 : ℝ)).smul_const
    ((((bfl2Equiv (‖asBFL2 A‖ ^ 2 • v) (c.1.1, c.2) : SuTwo) : M2)) i j) using 1
  all_goals first | (ext <;> rfl) | norm_num [Complex.ext_iff]

/-- Concrete unconditional rejection, using the certified q124 map at ell=2. -/
theorem qextQuad_fails_native_firstJet (v : BFL2 witnessL) :
    ¬ FirstJet (trivialU witnessL) 2 (oldQuadNative v) := by
  intro h
  exact linearQ_A0_ne_zero ((h A0 c0).unique (oldQuadNative_deriv v A0 c0))

end HConstruction.NonzeroJet

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`HConstruction.NonzeroJet.q124_A0,
      `HConstruction.NonzeroJet.linearQ_A0_ne_zero,
      `HConstruction.NonzeroJet.qextQuad_fails_native_firstJet] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard nonzero-jet axiom in {name}: {ax}"
    Lean.logInfo m!"NONZERO_JET_AXIOMS {name}: {axioms}"

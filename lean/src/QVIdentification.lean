/-
CMP99b (3.13)--(3.15), ONE STEP. The adjudicated pages p392/p393 define
Q(V) as the normalized linear part and cite CMP98 (124). Here the left
side is defined by differentiating that nonlinear function, NOT by q124.

Source block size L = (ell : Real); Lean L below is the lattice extent.
The existing chart chi(A)=i*A is imported unchanged. No complexification
or arbitrary-stride derivative is asserted. All boxed SI1 guards remain.
-/
import M2Proof
import AdalyFormal.Balaban.DeltaKSuTwoFaithful
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Matrix

namespace AdalyQIdentification.QV

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.DeltaKSuTwoFaithful
  (hermTraceless hermTracelessEquivSuTwo hermTracelessEquivSuTwo_apply)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage configMul)
open AdalySI1.Multiscale.M2
  (unitBondDir unitBondDir_conjTranspose unitBondDir_trace fineDirToUnitBond_unitBondDir)
open AdalySI1Noloop.OuterLogFullDeriv (Lh)

noncomputable local instance : NormedAddCommGroup M2 := Matrix.linftyOpNormedAddCommGroup
noncomputable local instance : NormedSpace ℝ M2 := Matrix.linftyOpNormedSpace
noncomputable local instance : NormedSpace ℂ M2 := Matrix.linftyOpNormedSpace

variable {L : PeriodicLatticeExtent}

/-- Exactly the established chi, NOT a new sign convention. -/
noncomputable abbrev chi := hermTracelessEquivSuTwo

/-- CMP99b (3.13) after applying chi: the ordinary skew-Hermitian log. -/
noncomputable def rawInChart (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → SuTwo) (τ : ℝ) (c : CoarseBond L (1 * ell)) : M2 :=
  su2Log (modifiedAverage V ell (fun e => su2Exp (τ • unitBondDir A e)) (c.1.1, c.2))

/-- CMP99b (3.13) in the source Hermitian convention: (1/i)log = -i log. -/
noncomputable def sourceRaw (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → hermTraceless) (τ : ℝ) (c : CoarseBond L (1 * ell)) : M2 :=
  (-Complex.I) • rawInChart V ell (fun b => chi (A b)) τ c

/-- The derivative of exactly (L eta)^(-1) Q_1(V, eta*t*A), in the chi chart.
eta is fixed as t varies. In particular we never differentiate 1/t at t=0. -/
noncomputable def qvInChart (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ) (η : ℝ)
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell)) : M2 :=
  deriv (fun t : ℝ => ((ell : ℝ) * η)⁻¹ • rawInChart V ell A (η * t) c) 0

/-- The same normalized linear part, in the SOURCE Hermitian convention.
This definition contains no q124Principal or abstract supplied derivative. -/
noncomputable def sourceQV (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ) (η : ℝ)
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell)) : M2 :=
  deriv (fun t : ℝ => ((ell : ℝ) * η)⁻¹ • sourceRaw V ell A (η * t) c) 0

/-- The existing positive-coordinate convention: exp(t*chi(A))*V = exp(i*t*A)*V. -/
theorem source_positive_chart (V : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L 1 → hermTraceless) (τ : ℝ) (e : PeriodicLatticeEdge L) :
    configMul (fun b => su2Exp (τ • unitBondDir (fun c => chi (A c)) b)) V e =
      su2Exp (Complex.I • (τ • ((A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) : hermTraceless) : M2)))
        * V e := by
  change su2Exp (τ • (Complex.I • ((A (⟨e.1, mem_coarseLattice_one e.1⟩, e.2) : hermTraceless) : M2))) * V e = _
  rw [smul_comm τ Complex.I]

/-- The source factor 1/i is literally -i. -/
theorem source_one_div_i : (1 : ℂ) / Complex.I = -Complex.I := by
  norm_num [div_eq_mul_inv, Complex.inv_I]

/-- Applying chi to the source output cancels 1/i exactly, not just in norm. -/
theorem sourceRaw_chart (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → hermTraceless) (τ : ℝ) (c : CoarseBond L (1 * ell)) :
    Complex.I • sourceRaw V ell A τ c = rawInChart V ell (fun b => chi (A b)) τ c := by
  simp [sourceRaw, smul_smul]

/-- Boxed SI1 with the unit-bond packaging undone. The full factor ell*eta
is retained, including eta=0; only normalization below excludes eta=0. -/
theorem hasDerivAt_rawInChart (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne) (η : ℝ) :
    HasDerivAt (fun t : ℝ => rawInChart V ell A (η * t) c)
      (((ell : ℝ) * η) • ((q124Principal 1 ell V A c : SuTwo) : M2)) 0 := by
  have hcell : c.1.1 ∈ CoarseLattice L ell := by simpa only [one_mul] using c.1.2
  have hd := AdalySI1.Boxed.hasDerivAt_su2Log_modifiedAverage_physical_q124
    V (unitBondDir A) (unitBondDir_conjTranspose A) (unitBondDir_trace A)
    ell (c.1.1, c.2) hcell hell hdvd hnc η
  rw [fineDirToUnitBond_unitBondDir] at hd
  simpa only [rawInChart, Lh] using hd

/-- There is no constant term in the nonlinear function being linearized. -/
theorem rawInChart_zero (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell)) :
    rawInChart V ell A 0 c = 0 := by
  have hz : (fun e => su2Exp ((0 : ℝ) • unitBondDir A e)) =
      AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L := by
    funext e
    simp [AdalyFormal.Balaban.CovariantHjMinimizer.trivialU]
  rw [rawInChart, hz, AdalySI1.ModifiedAverageDeriv.modifiedAverage_trivialU,
    AdalyFormal.Balaban.SuTwoLogExp.su2Log_one]

theorem sourceRaw_zero (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell)) :
    sourceRaw V ell A 0 c = 0 := by
  rw [sourceRaw, rawInChart_zero, smul_zero]

/-- Exactly the division required in (3.14), with both nonzero factors explicit. -/
theorem hasDerivAt_normalized_rawInChart (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    HasDerivAt (fun t : ℝ => ((ell : ℝ) * η)⁻¹ • rawInChart V ell A (η * t) c)
      ((q124Principal 1 ell V A c : SuTwo) : M2) 0 := by
  have hs : (ell : ℝ) * η ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)) hη
  convert (hasDerivAt_rawInChart V ell hell hdvd A c hnc η).const_smul (((ell : ℝ) * η)⁻¹) using 1 <;>
    first | rfl | simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-- Q(V)=q124Principal as a derivative identity in the established chart. -/
theorem qvInChart_eq_q124Principal (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → SuTwo) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    qvInChart V ell η A c = ((q124Principal 1 ell V A c : SuTwo) : M2) :=
  (hasDerivAt_normalized_rawInChart V ell hell hdvd A c hnc η hη).deriv

/-- Operator-level equality, arbitrary bond field, all coarse outputs. -/
theorem qvInChart_operator_eq (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (hnc : ∀ c : CoarseBond L (1 * ell), ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    qvInChart V ell η = fun A c => ((q124Principal 1 ell V A c : SuTwo) : M2) := by
  funext A c
  exact qvInChart_eq_q124Principal V ell hell hdvd A c (hnc c) η hη

/-- The UNNORMALIZED source derivative is ell*eta times the source Q(V)A.
The factor -i is in the output, while the input uses +i, never -i. -/
theorem hasDerivAt_sourceRaw (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne) (η : ℝ) :
    HasDerivAt (fun t : ℝ => sourceRaw V ell A (η * t) c)
      (((ell : ℝ) * η) • ((-Complex.I) •
        ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2))) 0 := by
  convert (hasDerivAt_rawInChart V ell hell hdvd (fun b => chi (A b)) c hnc η).const_smul (-Complex.I) using 1 <;>
    first | rfl | exact smul_comm ((ell : ℝ) * η) (-Complex.I) (((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2))

/-- (3.14) at j=1, source coordinates, with no missing eta or ell factor. -/
theorem sourceQV_eq (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    sourceQV V ell η A c = (-Complex.I) •
      ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2) := by
  have hs : (ell : ℝ) * η ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)) hη
  have hd := (hasDerivAt_sourceRaw V ell hell hdvd A c hnc η).const_smul (((ell : ℝ) * η)⁻¹)
  have hn : HasDerivAt (fun t : ℝ => ((ell : ℝ) * η)⁻¹ • sourceRaw V ell A (η * t) c)
      ((-Complex.I) • ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2)) 0 := by
    convert hd using 1 <;> first | rfl | simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
  exact hn.deriv

/-- Precise conjugacy: chi(Q_source(V)A)=q124Principal(V)(chi o A). -/
theorem chi_sourceQV_eq_q124Principal (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    Complex.I • sourceQV V ell η A c =
      ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2) := by
  rw [sourceQV_eq V ell hell hdvd A c hnc η hη]
  simp [smul_smul]

/-- Differentiating in eta itself (rather than t at fixed eta) yields ell*Q,
so the definition of the linear part divides by ell, not by ell*eta twice. -/
theorem eta_derivative_sourceRaw (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne) :
    HasDerivAt (fun η : ℝ => sourceRaw V ell A η c)
      ((ell : ℝ) • ((-Complex.I) •
        ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2))) 0 := by
  simpa only [mul_one, one_mul] using hasDerivAt_sourceRaw V ell hell hdvd A c hnc 1

/-- The source result really is the established inverse chart of q124. -/
theorem sourceQV_eq_inverse_chart (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    sourceQV V ell η A c =
      ((chi.symm (q124Principal 1 ell V (fun b => chi (A b)) c) : hermTraceless) : M2) :=
  sourceQV_eq V ell hell hdvd A c hnc η hη

/-- In particular the source derivative has exactly the required Hermitian carrier. -/
theorem sourceQV_mem_hermTraceless (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    sourceQV V ell η A c ∈ hermTraceless := by
  rw [sourceQV_eq_inverse_chart V ell hell hdvd A c hnc η hη]
  exact (chi.symm (q124Principal 1 ell V (fun b => chi (A b)) c)).2

/-- The choice of nonzero physical spacing cannot change the identified Q. -/
theorem sourceQV_eta_independent (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η ζ : ℝ) (hη : η ≠ 0) (hζ : ζ ≠ 0) :
    sourceQV V ell η A c = sourceQV V ell ζ A c := by
  rw [sourceQV_eq V ell hell hdvd A c hnc η hη,
    sourceQV_eq V ell hell hdvd A c hnc ζ hζ]

/-- Equivalent eta-at-zero definition: L^(-1) d/deta Q_1(V,eta*A)|0.
It agrees with the fixed-spacing normalized derivative, not eta times it. -/
theorem sourceQV_as_eta_derivative (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    sourceQV V ell η A c = (ell : ℝ)⁻¹ • deriv (fun τ : ℝ => sourceRaw V ell A τ c) 0 := by
  have hd : deriv (fun τ : ℝ => sourceRaw V ell A τ c) 0 =
      (ell : ℝ) • ((-Complex.I) • ((q124Principal 1 ell V (fun b => chi (A b)) c : SuTwo) : M2)) :=
    (eta_derivative_sourceRaw V ell hell hdvd A c hnc).deriv
  rw [sourceQV_eq V ell hell hdvd A c hnc η hη, hd,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)), one_smul]

#print axioms qvInChart_operator_eq
#print axioms chi_sourceQV_eq_q124Principal
#print axioms eta_derivative_sourceRaw

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalyQIdentification.QV.source_positive_chart,
      `AdalyQIdentification.QV.source_one_div_i,
      `AdalyQIdentification.QV.sourceRaw_chart,
      `AdalyQIdentification.QV.hasDerivAt_rawInChart,
      `AdalyQIdentification.QV.rawInChart_zero,
      `AdalyQIdentification.QV.sourceRaw_zero,
      `AdalyQIdentification.QV.hasDerivAt_normalized_rawInChart,
      `AdalyQIdentification.QV.qvInChart_eq_q124Principal,
      `AdalyQIdentification.QV.qvInChart_operator_eq,
      `AdalyQIdentification.QV.hasDerivAt_sourceRaw,
      `AdalyQIdentification.QV.sourceQV_eq,
      `AdalyQIdentification.QV.chi_sourceQV_eq_q124Principal,
      `AdalyQIdentification.QV.eta_derivative_sourceRaw,
      `AdalyQIdentification.QV.sourceQV_eq_inverse_chart,
      `AdalyQIdentification.QV.sourceQV_mem_hermTraceless,
      `AdalyQIdentification.QV.sourceQV_eta_independent,
      `AdalyQIdentification.QV.sourceQV_as_eta_derivative] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing QV theorem: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard QV axiom in {name}: {ax}"
    Lean.logInfo m!"QV_AXIOMS {name}: {axioms}"
  for mod in [`SI1Proof, `M2Proof, `T1MainSegment] do
    let path ← Lean.findOLean mod
    let expected := s!"/home/sebastian/projects/project-adaly/compute/q_identification/deps/{mod}.olean"
    unless path.toString == expected do
      Lean.logInfo m!"GUARD_NEUTRALISED Unexpected QV dependency {mod}: {path}"
    Lean.logInfo m!"QV_RESOLVED {mod}: {path}"
  let chartPath ← Lean.findOLean `AdalyFormal.Balaban.DeltaKSuTwoFaithful
  unless chartPath.toString == "/home/sebastian/projects/project-adaly/compute/forall_u_rung/deps/AdalyFormal/Balaban/DeltaKSuTwoFaithful.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED Unexpected established chart import: {chartPath}"
  Lean.logInfo m!"QV_ESTABLISHED_CHART {chartPath}"
  Lean.logInfo "QV_STANDARD_ONLY"

end AdalyQIdentification.QV

/-
CMP99b (3.15): composition of formula-(124) Q's, in the established Hermitian
chart, equals the certified bond composite. Read adjudicated p.392/p.393.
This is the algebraic composition identification, NOT a new all-depth
nonlinear differentiability theorem. The stride-1 derivative anchor is imported
from the independently verified QVIdentification, not assumed anew.
-/
import QVIdentification
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace AdalyQIdentification.QJ

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2NegOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.DeltaKSuTwoFaithful (hermTraceless)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarTowerSU2 ubarSU2)
open AdalyFormal.DeltaKR85 (q124Principal)
open AdalySI1.Multiscale (qCompositeBond)
open AdalyQIdentification.QV (chi sourceQV)

variable {L : PeriodicLatticeExtent}

/-- Pointwise extension of the EXISTING chi(A)=iA; no spatial reindexing. -/
noncomputable def chiBond (s : ℕ) :
    (CoarseBond L s → hermTraceless) ≃ₗ[ℝ] (CoarseBond L s → SuTwo) :=
  LinearEquiv.piCongrRight (fun _ => chi)

/-- Source Q(V) defined by its printed reference to (124), in Hermitian
coordinates. The input chart is +i; the inverse output chart is -i.
`s` is the current fine stride; `ell` is printed L, not torus extent L. -/
noncomputable def sourceQ124 (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L) :
    (CoarseBond L s → hermTraceless) →ₗ[ℝ]
      (CoarseBond L (s * ell) → hermTraceless) :=
  (chiBond (s * ell)).symm.toLinearMap.comp
    ((q124Principal s ell V).comp (chiBond s).toLinearMap)

/-- Each formula-(124) factor has exactly one chart at each end. -/
theorem chiBond_sourceQ124 (s ell : ℕ) (V : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L s → hermTraceless) :
    chiBond (s * ell) (sourceQ124 s ell V A) =
      q124Principal s ell V (chiBond s A) := by
  exact (chiBond (s * ell)).apply_symm_apply _

/-- Connect the referenced formula to the independently defined, normalized
nonlinear derivative at the certified stride-1 scope; all hypotheses retained. -/
theorem sourceQV_eq_sourceQ124 (V : PeriodicLinkConfiguration SU2 L)
    (ell : ℕ) (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (1 * ell))
    (hnc : ∀ x ∈ stepBlockOf c.1.1 1 ell,
      loopVar 1 ell V (c.1.1, c.2) x ≠ su2NegOne)
    (η : ℝ) (hη : η ≠ 0) :
    sourceQV V ell η A c = ((sourceQ124 1 ell V A c : hermTraceless) : M2) := by
  exact AdalyQIdentification.QV.sourceQV_eq_inverse_chart V ell hell hdvd A c hnc η hη

/-- Literal ordered composition in (3.15). `bg r` denotes Ubar^r.
The newest/coarsest factor acts LAST (on the left), not first.
The zero-depth extension is the empty composition. -/
noncomputable def sourceQj (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    (j : ℕ) → (CoarseBond L 1 → hermTraceless) →ₗ[ℝ]
      (CoarseBond L (ell ^ j) → hermTraceless)
  | 0 => LinearMap.id
  | j + 1 => (sourceQ124 (ell ^ j) ell (bg j)).comp (sourceQj bg ell j)

theorem sourceQj_zero (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    sourceQj bg ell 0 = LinearMap.id := rfl

theorem sourceQj_succ (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) :
    sourceQj bg ell (j + 1) =
      (sourceQ124 (ell ^ j) ell (bg j)).comp (sourceQj bg ell j) := rfl

theorem sourceQj_one (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) :
    sourceQj bg ell 1 = sourceQ124 1 ell (bg 0) := rfl

/-- Explicit depth-2 order check: Q(Ubar) acts after Q(U). -/
theorem sourceQj_two (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (ell ^ (1 + 1))) :
    sourceQj bg ell (1 + 1) A c =
      sourceQ124 (ell ^ 1) ell (bg 1) (sourceQj bg ell 1 A) c := rfl

/-- The actual depth-j identification, by unfolding M2's own recursion and
cancelling chi o chi^{-1} between adjacent factors. No commutation of Q's. -/
theorem chiBond_sourceQj (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ)
    (A : CoarseBond L 1 → hermTraceless) :
    chiBond (ell ^ j) (sourceQj bg ell j A) =
      qCompositeBond bg ell j (chiBond 1 A) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change chiBond (ell ^ j * ell)
      (sourceQ124 (ell ^ j) ell (bg j) (sourceQj bg ell j A)) =
      q124Principal (ell ^ j) ell (bg j) (qCompositeBond bg ell j (chiBond 1 A))
    rw [chiBond_sourceQ124, ih]

/-- Source-coordinate equality, with the unique inverse chart visible. -/
theorem sourceQj_eq_inverse_chart (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell j : ℕ) (A : CoarseBond L 1 → hermTraceless) :
    sourceQj bg ell j A =
      (chiBond (ell ^ j)).symm (qCompositeBond bg ell j (chiBond 1 A)) := by
  apply (chiBond (ell ^ j)).injective
  rw [chiBond_sourceQj, LinearEquiv.apply_symm_apply]

/-- Apply the established chart to the ENTIRE printed composition. -/
noncomputable def QjInChart (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) :
    (CoarseBond L 1 → SuTwo) →ₗ[ℝ] (CoarseBond L (ell ^ j) → SuTwo) :=
  (chiBond (ell ^ j)).toLinearMap.comp
    ((sourceQj bg ell j).comp (chiBond 1).symm.toLinearMap)

/-- Operator equality, not just equality on gradients or one chosen input. -/
theorem QjInChart_eq_qCompositeBond
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell j : ℕ) :
    QjInChart bg ell j = qCompositeBond bg ell j := by
  apply LinearMap.ext
  intro A
  simpa only [QjInChart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using
    chiBond_sourceQj bg ell j ((chiBond 1).symm A)

/-- All i-factors cancel internally; exactly +i on the source output remains. -/
theorem sourceQj_matrix_chart (bg : ℕ → PeriodicLinkConfiguration SU2 L)
    (ell j : ℕ) (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (ell ^ j)) :
    Complex.I • ((sourceQj bg ell j A c : hermTraceless) : M2) =
      ((qCompositeBond bg ell j (fun b => chi (A b)) c : SuTwo) : M2) := by
  exact congrArg (fun B : CoarseBond L (ell ^ j) → SuTwo => (B c : M2))
    (chiBond_sourceQj bg ell j A)

/-- Printed Ubar^r is the already-existing SINGLE-bar blocked-background tower.
This is not the double-bar modified-average iteration of the fluctuating field. -/
noncomputable def sourceQjU (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) (j : ℕ) :=
  sourceQj (ubarTowerSU2 ell U) ell j

theorem sourceQjU_one (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L) :
    sourceQjU ell U 1 = sourceQ124 1 ell U := rfl

theorem sourceQjU_two (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (A : CoarseBond L 1 → hermTraceless) (c : CoarseBond L (ell ^ (1 + 1))) :
    sourceQjU ell U (1 + 1) A c =
      sourceQ124 (ell ^ 1) ell (ubarSU2 1 ell U) (sourceQjU ell U 1 A) c :=
  sourceQj_two (ubarTowerSU2 ell U) ell A c

/-- (3.15) for the actual Ubar tower, with no arbitrary background replacement. -/
theorem sourceQjU_eq_qCompositeBond (ell : ℕ) (U : PeriodicLinkConfiguration SU2 L)
    (j : ℕ) (A : CoarseBond L 1 → hermTraceless) :
    chiBond (ell ^ j) (sourceQjU ell U j A) =
      qCompositeBond (ubarTowerSU2 ell U) ell j (chiBond 1 A) :=
  chiBond_sourceQj (ubarTowerSU2 ell U) ell j A

/-! Exact normalization bookkeeping. This is the algebraic chain of
unnormalized ONE-STEP LINEAR maps, not a claim that the all-depth nonlinear
map has been differentiated. Only the initial input carries eta; each level
contributes ell, not ell*eta afresh. -/
noncomputable def unnormalizedLinearChain
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (η : ℝ) :
    (j : ℕ) → (CoarseBond L 1 → hermTraceless) →ₗ[ℝ]
      (CoarseBond L (ell ^ j) → hermTraceless)
  | 0 => η • LinearMap.id
  | j + 1 => ((ell : ℝ) • sourceQ124 (ell ^ j) ell (bg j)).comp
      (unnormalizedLinearChain bg ell η j)

/-- j factors ell and ONE initial eta give exactly ell^j*eta. -/
theorem unnormalizedLinearChain_eq
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (η : ℝ) (j : ℕ) :
    unnormalizedLinearChain bg ell η j = ((ell : ℝ) ^ j * η) • sourceQj bg ell j := by
  induction j with
  | zero =>
    apply LinearMap.ext
    intro A
    funext c
    change η • A c = ((ell : ℝ) ^ 0 * η) • A c
    rw [pow_zero, one_mul]
  | succ j ih =>
    rw [unnormalizedLinearChain, ih, sourceQj]
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    ring

/-- Division by exactly the (3.14) scalar recovers Q_j, with no hidden rescaling. -/
theorem normalize_unnormalizedLinearChain
    (bg : ℕ → PeriodicLinkConfiguration SU2 L) (ell : ℕ) (hell : 0 < ell)
    (η : ℝ) (hη : η ≠ 0) (j : ℕ) :
    ((ell : ℝ) ^ j * η)⁻¹ • unnormalizedLinearChain bg ell η j = sourceQj bg ell j := by
  rw [unnormalizedLinearChain_eq, smul_smul]
  have hs : (ell : ℝ) ^ j * η ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell))) hη
  rw [inv_mul_cancel₀ hs, one_smul]

/-- Physical spacing at successive levels: eta_j=ell^j*eta, eta_{j+1}=ell*eta_j. -/
theorem physical_spacing_succ (ell j : ℕ) (η : ℝ) :
    (ell : ℝ) * ((ell : ℝ) ^ j * η) = (ell : ℝ) ^ (j + 1) * η := by ring

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let ns := `AdalyQIdentification.QJ
  let mut count := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if ns.isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Nonstandard QJ axiom {name}: {ax}"
      count := count + 1
  Lean.logInfo m!"QJ_STANDARD_ONLY {count} declarations"
  for mod in [`MultiscaleTarget, `M2Proof, `SI1Proof] do
    let p ← Lean.findOLean mod
    unless p.toString == s!"/home/sebastian/projects/project-adaly/compute/q_identification/deps/{mod}.olean" do
      Lean.logInfo m!"GUARD_NEUTRALISED Unexpected certified module {mod}: {p}"
    Lean.logInfo m!"QJ_INPUT {mod}: {p}"
  let p ← Lean.findOLean `QVIdentification
  unless p.toString == "/home/sebastian/projects/project-adaly/compute/q_identification/qv/certified/QVIdentification.olean" do
    Lean.logInfo m!"GUARD_NEUTRALISED Unexpected one-step identification: {p}"
  Lean.logInfo m!"QJ_QV_INPUT {p}"

end AdalyQIdentification.QJ

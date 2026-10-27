import DK2DepthOffsetContours

set_option autoImplicit false
noncomputable section
namespace Prop1.ScaleFittedRepair

open AdalyFormal.Target.ClayStatement
  (PeriodicLatticeExtent PeriodicLatticeSite PeriodicLatticeEdge PeriodicLinkConfiguration)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.AdmissibleSubspace (CoarseLattice)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_mem_coarseLattice)
open AdalyFormal.Balaban.UbarTowerCov (gammaVarStrided coarseBondVar loopVar)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_conj_sub_one)
open DepthUniformity.Strided (orientedPlaqHolS)
open DepthUniformity.Fitted (SublatticePlaqBound ScaleFittedPropagation coarseLattice_antitone)
open Prop1.ScaleFittedProof (block_sites_input_aligned)

variable {L : PeriodicLatticeExtent}

/-- Proposition 1 at one fitted corner. Its only smallness assumption is on
the INPUT curvature. Winding coarse bonds are never assumed near the identity. -/
theorem fitted_plaquette_estimate (ell : ℕ) (hell : 0 < ell)
    (s : ℕ) (hs : 0 < s) (hd : ∀ μ : Fin 3, s*ell ∣ L μ+1)
    (V : PeriodicLinkConfiguration SU2 L) (β : ℝ) (hβ : 0 ≤ β)
    (hsmall : (ell : ℝ)^2*β ≤ 1/400) (hin : SublatticePlaqBound s V β)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L (s*ell)) (μ ν : Fin 3) :
    frobNorm (((orientedPlaqHolS (s*ell) (ubarSU2 s ell V) y μ ν : SU2) : M2)-1) ≤
      (ell : ℝ)^2*β + 44465*((ell : ℝ)^2*β)^2 := by
  classical
  let b := (ell : ℝ)^2*β
  let w := fun _ : Fin 3 → Fin ell => ((((ell : ℚ)^3)⁻¹ : ℚ) : ℝ)
  let e : Fin 4 → PeriodicLatticeEdge L :=
    ![(y, μ), (coarseShift y (s*ell) μ, ν), (coarseShift y (s*ell) ν, μ), (y, ν)]
  let C := fun i => coarseBondVar s ell V (e i)
  let G : Fin 4 → (Fin 3 → Fin ell) → SU2 :=
    fun i o => gammaVarStrided s ell V (e i) (offsetPoint s (e i).1 o)
  have he : ∀ i, (e i).1 ∈ CoarseLattice L (s*ell) := by
    intro i
    fin_cases i
    · exact hy
    · exact coarseShift_mem_coarseLattice hd hy μ
    · exact coarseShift_mem_coarseLattice hd hy ν
    · exact hy
  have hds : ∀ α : Fin 3, s ∣ L α+1 := fun α => dvd_trans (dvd_mul_right s ell) (hd α)
  have hys := coarseLattice_antitone (dvd_mul_right s ell) hy
  have hb : 0 ≤ b := mul_nonneg (sq_nonneg _) hβ
  have hw : ∀ o ∈ (Finset.univ : Finset (Fin 3 → Fin ell)), 0 ≤ w o := by
    intro o _
    dsimp [w]
    positivity
  have hsum : ∑ o : Fin 3 → Fin ell, w o = 1 := by
    have hn : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hloop : ∀ i o, o ∈ (Finset.univ : Finset (Fin 3 → Fin ell)) →
      frobNorm (((G i o * (C i)⁻¹ : SU2) : M2)-1) ≤ 3*b := by
    intro i o _
    exact fitted_loop_norm s ell hs hd V β hβ hin (e i) (he i)
      (offsetPoint s (e i).1 o) (offsetPoint_mem s ell hs hd (e i).1 (he i) o)
  have hP : frobNorm (((C 0 * C 1 * (C 2)⁻¹ * (C 3)⁻¹ : SU2) : M2)-1) ≤ b := by
    exact fitted_rectangle_norm s ell hds V β hβ hin y hys μ ν
  have hrect : ∀ o ∈ (Finset.univ : Finset (Fin 3 → Fin ell)),
      frobNorm (((G 0 o * G 1 o * (G 2 o)⁻¹ * (G 3 o)⁻¹ : SU2) : M2)-1) ≤ b := by
    intro o _
    have hmatch := gamma_offset_rectangle s ell hs hd V y hy μ ν o
    change frobNorm (((orientedPlaqHolS (s*ell)
      (fun c => gammaVarStrided s ell V c (offsetPoint s c.1 o)) y μ ν : SU2) : M2)-1) ≤ b
    rw [hmatch, frobNorm_conj_sub_one]
    exact fitted_rectangle_norm s ell hds V β hβ hin (offsetPoint s y o)
      (block_sites_input_aligned s ell y hy _ (offsetPoint_mem s ell hs hd y hy o)) μ ν
  have h := contour_mean_plaquette_bound Finset.univ w hw hsum C G b hb hsmall hloop hP hrect
  have hraw : ∀ i, loopMean Finset.univ w (fun o => G i o * (C i)⁻¹) * C i =
      ubarSU2 s ell V (e i) := by
    intro i
    exact (raw_bond_offset_mean s ell hs hd V (e i) (he i)).symm
  dsimp only at h
  rw [hraw 0, hraw 1, hraw 2, hraw 3] at h
  exact h

/-- Unconditional discharge of the EXACT imported residual. Constants are
C0=44465 (dimension-only) and c2'=1/(400 ell^2). No added lattice-size bound,
periodic-gauge premise, or contour smallness assumption. -/
theorem scale_fitted_propagation (ell : ℕ) (hell : 0 < ell) :
    ScaleFittedPropagation (L := L) ell 44465 (400*(ell : ℝ)^2)⁻¹ := by
  intro s hs hd V β hβ hc hin y hy μ ν
  have hn : (ell : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hell)
  have heq : (ell : ℝ)^2 * (400*(ell : ℝ)^2)⁻¹ = 1/400 := by
    field_simp
  have hsmall : (ell : ℝ)^2*β ≤ 1/400 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg (ell : ℝ))
    rwa [heq] at h
  exact fitted_plaquette_estimate ell hell s hs hd V β hβ hsmall hin y hy μ ν

/-- Positive constants, uniform over every periodic extent; the target is not
redefined or replaced by a theorem with additional geometric hypotheses. -/
theorem proposition_one (ell : ℕ) (hell : 2 ≤ ell) :
    ∃ C0 c2' : ℝ, 0 < C0 ∧ 0 < c2' ∧
      ScaleFittedPropagation (L := L) ell C0 c2' := by
  refine ⟨44465, (400*(ell : ℝ)^2)⁻¹, by norm_num, ?_, ?_⟩
  · have h : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
    positivity
  · exact scale_fitted_propagation ell (by omega)

end Prop1.ScaleFittedRepair

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[`Prop1.ScaleFittedRepair.fitted_plaquette_estimate,
      `Prop1.ScaleFittedRepair.scale_fitted_propagation,
      `Prop1.ScaleFittedRepair.proposition_one] do
    let axioms ← Lean.collectAxioms n
    Lean.logInfo m!"PROPOSITION_ONE_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom in {n}: {ax}"
  Lean.logInfo "PROPOSITION_ONE_COMPLETE"

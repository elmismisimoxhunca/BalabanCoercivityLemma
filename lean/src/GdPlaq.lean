import GdNQ

/-!
# GdPlaq -- plaquette-wise locality of the full-torus `Δ`:  if two configurations agree on every plaquette outside a set `Pz` and the field `X` vanishes on every
bond of every plaquette in `Pz`, then `Δ_U X = Δ_{U'} X` (`deltaK_univ_congr_apply`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlCovariantLM_L2_toLp)
open AdalyFormal.StatementLaneR6

variable {L : PeriodicLatticeExtent}

section locality
variable {U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
  {p : PeriodicLatticePlaquette L}

theorem edge_zero_1 {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : A (p.1, p.2.1.1) = 0 :=
  hA _ ((edge_mem p _).mpr (Or.inl rfl))
theorem edge_zero_2 {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 :=
  hA _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))
theorem edge_zero_3 {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 :=
  hA _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))
theorem edge_zero_4 {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : A (p.1, p.2.1.2) = 0 :=
  hA _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))

theorem curlValue_zero_of {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    curlValueCovariant U A p = 0 := by
  unfold curlValueCovariant
  rw [edge_zero_1 hA, edge_zero_2 hA, edge_zero_3 hA, edge_zero_4 hA]
  simp

theorem a_zero_of {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    a1LM U p A = 0 ∧ a2LM p A = 0 ∧ a3LM p A = 0 ∧ a4LM U p A = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a1LM_apply]; unfold AprimeZW; rw [edge_zero_3 hA]; simp
  · rw [a2LM_apply]; unfold AprimeWX; rw [edge_zero_4 hA]; simp
  · rw [a3LM_apply]; unfold AprimeXY; rw [edge_zero_1 hA]; simp
  · rw [a4LM_apply]; unfold AprimeYZ; rw [edge_zero_2 hA]; simp

theorem curlMat_zero_of {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    curlMatLM U p A = 0 := by
  rw [curlMatLM_apply, curlValue_zero_of hA]; rfl

theorem b_zero_of {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) :
    b1LM U p A = 0 ∧ b2LM p A = 0 ∧ b3LM p A = 0 ∧ b4LM U p A = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := a_zero_of (U := U) hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [b1LM, h1]
  · simp [b2LM, h2]
  · simp [b3LM, h3]
  · simp [b4LM, h4]

theorem bilPlaq_zero_left {A : Bond L → SuTwo} (hA : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) (B : Bond L → SuTwo) :
    bilPlaq U p A B = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := b_zero_of (U := U) hA
  have hc := curlMat_zero_of (U := U) hA
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp [pairBil_apply, hc, h1, h2, h3, h4]

theorem bilPlaq_zero_right (A : Bond L → SuTwo) {B : Bond L → SuTwo} (hB : ∀ e ∈ periodicPlaquetteBoundaryEdges p, B e = 0) :
    bilPlaq U p A B = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := b_zero_of (U := U) hB
  have hc := curlMat_zero_of (U := U) hB
  rw [bilPlaq_apply, firstBilPlaq_apply, secondBilPlaq_apply]
  simp [pairBil_apply, hc, h1, h2, h3, h4]

end locality

#print axioms bilPlaq_zero_left
#print axioms bilPlaq_zero_right


section delta
variable {U U' : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}

open Classical in
theorem deltaPrimeBilRaw_congr_X (Pz : Set (PeriodicLatticePlaquette L))
    (hag : ∀ p, p ∉ Pz → ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e)
    (A X : Bond L → SuTwo) (hX : ∀ p ∈ Pz, ∀ e ∈ periodicPlaquetteBoundaryEdges p, X e = 0) :
    deltaPrimeBilRawLoc U Set.univ A X = deltaPrimeBilRawLoc U' Set.univ A X ∧
    deltaPrimeBilRawLoc U Set.univ X A = deltaPrimeBilRawLoc U' Set.univ X A := by
  constructor
  · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Set.mem_univ, if_true]
    by_cases hp : p ∈ Pz
    · rw [bilPlaq_zero_right A (hX p hp), bilPlaq_zero_right A (hX p hp)]
    · rw [bilPlaq_congr (hag p hp)]
  · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Set.mem_univ, if_true]
    by_cases hp : p ∈ Pz
    · rw [bilPlaq_zero_left (hX p hp), bilPlaq_zero_left (hX p hp)]
    · rw [bilPlaq_congr (hag p hp)]


theorem second_term_congr (Pz : Set (PeriodicLatticePlaquette L))
    (hag : ∀ p, p ∉ Pz → ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e)
    (Y X : BondFnL2 L) (hX : ∀ p ∈ Pz, ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp X) e = 0) :
    deltaPrimeBilL2NormLoc U Set.univ Y X = deltaPrimeBilL2NormLoc U' Set.univ Y X := by
  obtain ⟨h1, h2⟩ := deltaPrimeBilRaw_congr_X (U := U) (U' := U') Pz hag
      (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L Y) (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L X) hX
  unfold deltaPrimeBilL2NormLoc
  simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe]
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
  rw [h1, h2]


theorem curlL2_apply (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) :
    (curlCovariantLM_L2 U x) p = curlValueCovariant U (WithLp.ofLp x) p := by
  have hx : x = WithLp.toLp 2 (WithLp.ofLp x) := rfl
  rw [hx, curlCovariantLM_L2_toLp]

theorem first_term_congr (Pz : Set (PeriodicLatticePlaquette L))
    (hag : ∀ p, p ∉ Pz → ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e)
    (Y X : BondFnL2 L) (hX : ∀ p ∈ Pz, ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp X) e = 0) :
    (inner ℝ (plaqMask Set.univ (curlCovariantLM_L2 U Y)) (plaqMask Set.univ (curlCovariantLM_L2 U X)) : ℝ)
      = inner ℝ (plaqMask Set.univ (curlCovariantLM_L2 U' Y)) (plaqMask Set.univ (curlCovariantLM_L2 U' X)) := by
  rw [plaqMask_univ, plaqMask_univ, plaqMask_univ, plaqMask_univ]
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curlL2_apply, curlL2_apply, curlL2_apply, curlL2_apply]
  by_cases hp : p ∈ Pz
  · rw [curlValue_zero_of (U := U) (hX p hp), curlValue_zero_of (U := U') (hX p hp)]
    simp
  · rw [curlValue_congr (hag p hp), curlValue_congr (hag p hp)]


/-- **plaquette-wise locality of the full-torus `Δ`.** -/
theorem deltaK_univ_congr_apply (Pz : Set (PeriodicLatticePlaquette L))
    (hag : ∀ p, p ∉ Pz → ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = U' e)
    (X : BondFnL2 L) (hX : ∀ p ∈ Pz, ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp X) e = 0) :
    deltaKLocCLM U (Set.univ : Set (PeriodicLatticePlaquette L)) X = deltaKLocCLM U' Set.univ X := by
  refine ext_inner_left ℝ (fun Y => ?_)
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM, first_term_congr Pz hag Y X hX, second_term_congr Pz hag Y X hX]

#print axioms deltaPrimeBilRaw_congr_X
#print axioms second_term_congr
#print axioms first_term_congr
#print axioms deltaK_univ_congr_apply

end delta

end AdalyFormal.D1Guarded

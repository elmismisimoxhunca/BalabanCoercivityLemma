import GdV
import GdStat

/-!
# GdGen1 -- geometry for an ARBITRARY configuration `U`.

* `deltaK_set_congr`: `deltaKLocCLM U P X = deltaKLocCLM U Q X` if `X` vanishes on every bond of every plaquette on which `P`, `Q` disagree.
* `edge_ends_not_om1_of_notIn`: a plaquette with a corner outside `Ω₀` has all corners outside `Ω₁` (collar `4 ≤ R M`).
* `Wop_zero_on_notIn`: for `A ∈ E₀` vanishing on the level-0 bonds, `W A` vanishes on every bond of every plaquette not in `plaqIn Ω₀`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)

variable {L : PeriodicLatticeExtent}

section sets
variable {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}

open Classical in
theorem deltaPrimeBilRawLoc_set_congr (P Q : Set (PeriodicLatticePlaquette L)) (A X : Bond L → SuTwo)
    (hX : ∀ p, ¬ (p ∈ P ↔ p ∈ Q) → ∀ e ∈ periodicPlaquetteBoundaryEdges p, X e = 0) :
    deltaPrimeBilRawLoc U P A X = deltaPrimeBilRawLoc U Q A X ∧ deltaPrimeBilRawLoc U P X A = deltaPrimeBilRawLoc U Q X A := by
  constructor
  · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hpq : p ∈ P ↔ p ∈ Q
    · by_cases hp : p ∈ P
      · rw [if_pos hp, if_pos (hpq.mp hp)]
      · rw [if_neg hp, if_neg (fun h => hp (hpq.mpr h))]
    · have := bilPlaq_zero_right (U := U) (p := p) A (hX p hpq)
      by_cases hp : p ∈ P <;> by_cases hq : p ∈ Q <;> simp [hp, hq, this]
  · rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hpq : p ∈ P ↔ p ∈ Q
    · by_cases hp : p ∈ P
      · rw [if_pos hp, if_pos (hpq.mp hp)]
      · rw [if_neg hp, if_neg (fun h => hp (hpq.mpr h))]
    · have := bilPlaq_zero_left (U := U) (p := p) (hX p hpq) A
      by_cases hp : p ∈ P <;> by_cases hq : p ∈ Q <;> simp [hp, hq, this]

theorem deltaK_set_congr (P Q : Set (PeriodicLatticePlaquette L)) (X : BondFnL2 L)
    (hX : ∀ p, ¬ (p ∈ P ↔ p ∈ Q) → ∀ e ∈ periodicPlaquetteBoundaryEdges p, (WithLp.ofLp X) e = 0) :
    deltaKLocCLM U P X = deltaKLocCLM U Q X := by
  classical
  refine ext_inner_left ℝ (fun Y => ?_)
  rw [inner_deltaKLocCLM, inner_deltaKLocCLM]
  have e1 : (inner ℝ (plaqMask P (curlCovariantLM_L2 U Y)) (plaqMask P (curlCovariantLM_L2 U X)) : ℝ) =
      inner ℝ (plaqMask Q (curlCovariantLM_L2 U Y)) (plaqMask Q (curlCovariantLM_L2 U X)) := by
    simp only [PiLp.inner_apply, plaqMask_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hpq : p ∈ P ↔ p ∈ Q
    · by_cases hp : p ∈ P
      · rw [if_pos hp, if_pos hp, if_pos (hpq.mp hp), if_pos (hpq.mp hp)]
      · rw [if_neg hp, if_neg hp, if_neg (fun h => hp (hpq.mpr h)), if_neg (fun h => hp (hpq.mpr h))]
    · have h0 : (curlCovariantLM_L2 U X) p = 0 := by
        rw [curlL2_apply]; exact curlValue_zero_of (hX p hpq)
      by_cases hp : p ∈ P <;> by_cases hq : p ∈ Q <;> simp [hp, hq, h0]
  have e2 : deltaPrimeBilL2NormLoc U P Y X = deltaPrimeBilL2NormLoc U Q Y X := by
    obtain ⟨h1, h2⟩ := deltaPrimeBilRawLoc_set_congr (U := U) P Q
      (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L Y) (AdalyFormal.Balaban.BondSU2Space.bondFnL2Equiv L X) hX
    unfold deltaPrimeBilL2NormLoc
    simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe]
    unfold deltaPrimeBilNormLoc
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply]
    rw [h1, h2]
  rw [e1, e2]

#print axioms deltaPrimeBilRawLoc_set_congr
#print axioms deltaK_set_congr

end sets

/-- a plaquette with a corner outside `Ω₀` has all corners outside `Ω₁`. -/
theorem edge_ends_not_om1_of_notIn {ell M R k : ℕ} {S : Tower L} (hS : Admissible ell M R k S) (h4 : 4 ≤ R * M)
    {p : PeriodicLatticePlaquette L} (hp : p ∉ plaqIn (S.Om 0)) {e' : Bond L} (he' : e' ∈ periodicPlaquetteBoundaryEdges p) :
    e'.1 ∉ S.Om 1 ∧ periodicLatticeShift e'.1 e'.2 ∉ S.Om 1 := by
  have hp' : ∃ e ∈ periodicPlaquetteBoundaryEdges p, ¬ (e.1 ∈ S.Om 0 ∧ periodicLatticeShift e.1 e.2 ∈ S.Om 0) := by
    by_contra hcon
    push Not at hcon
    exact hp hcon
  obtain ⟨e, he, hne⟩ := hp'
  obtain ⟨n1, n2⟩ := edge_ends_near he
  obtain ⟨m1, m2⟩ := edge_ends_near he'
  have key : ∀ z, z ∉ S.Om 0 → pdist z p.1 ≤ 2 → ∀ c, pdist c p.1 ≤ 2 → c ∉ S.Om 1 := by
    intro z hz hzd c hc hc1
    have h := AdalyFormal.StatementLaneR8.pdist_triangle z p.1 c
    rw [AdalyFormal.StatementLaneR8.pdist_comm p.1 c] at h
    exact hz (near_om1 hS hc1 (by omega) (Nat.zero_le _))
  have hz : ∃ z, z ∉ S.Om 0 ∧ pdist z p.1 ≤ 2 := by
    by_cases h1 : e.1 ∈ S.Om 0
    · exact ⟨periodicLatticeShift e.1 e.2, fun h => hne ⟨h1, h⟩, n2⟩
    · exact ⟨e.1, h1, n1⟩
  obtain ⟨z, hz0, hzd⟩ := hz
  exact ⟨key z hz0 hzd _ m1, key z hz0 hzd _ m2⟩

#print axioms edge_ends_not_om1_of_notIn

section assembled
variable {ell M R k : ℕ} {S : Tower L}

/-- **the gauge-fixed field vanishes on the bonds of every plaquette not in `plaqIn Ω₀`** (any `U`; fields vanishing on level-0 bonds). -/
theorem Wop_zero_on_notIn (hS : Admissible ell M R k S) (hell0 : 0 < ell) (h4 : 4 ≤ R * M) (U : Cfg L) (a : ℝ)
    (A : ↥(bondSupp (geomOf ell k S))) (hA0 : ∀ b ∈ bondsLam (geomOf ell k S) 0, (WithLp.ofLp (iE (geomOf ell k S) A)) b = 0)
    {p : PeriodicLatticePlaquette L} (hp : p ∉ plaqIn (S.Om 0)) (e' : Bond L) (he' : e' ∈ periodicPlaquetteBoundaryEdges p) :
    (WithLp.ofLp (Wop (geomOf ell k S) U a (iE (geomOf ell k S) A))) e' = 0 := by
  obtain ⟨n1, n2⟩ := edge_ends_not_om1_of_notIn hS h4 hp he'
  have hfz : ∀ c : PeriodicLatticeSite L, c ∉ S.Om 1 →
      (WithLp.ofLp (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A))))) c = 0 := by
    intro c hc
    by_cases hc0 : c ∈ S.Om 0
    · refine Gp_Rproj_lam0 (geomOf ell k S) U a _ (x := c) ?_
      refine ⟨fun μ => by simp, hc0, ?_⟩
      simpa using hc
    · exact Gp_Rproj_out (geomOf ell k S) U a _ (x := c) hc0
  have hgrad : (WithLp.ofLp (gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))))) e' = 0 := by
    rw [gradL2_apply]
    unfold AdalyFormal.Balaban.CovariantOperators.gradValueCovariant
    rw [hfz _ n1, hfz _ n2]
    simp
  have hA : (WithLp.ofLp (iE (geomOf ell k S) A)) e' = 0 := by
    by_cases hb : e' ∈ bondsOm0 (geomOf ell k S)
    · by_contra hne
      have hnl : e' ∉ bondsLam (geomOf ell k S) 0 := fun h => hne (hA0 e' h)
      rcases endpoint_om1 hell0 hS e' hb hnl with h | h
      · exact n1 h
      · exact n2 h
    · exact A.2 e' hb
  have hW : Wop (geomOf ell k S) U a (iE (geomOf ell k S) A) = iE (geomOf ell k S) A - gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))) := rfl
  rw [hW]
  show (WithLp.ofLp (iE (geomOf ell k S) A)) e' - (WithLp.ofLp (gradL2 U (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U (gradAdj U (iE (geomOf ell k S) A)))))) e' = 0
  rw [hA, hgrad, sub_zero]

#print axioms Wop_zero_on_notIn

end assembled

end AdalyFormal.D1Guarded

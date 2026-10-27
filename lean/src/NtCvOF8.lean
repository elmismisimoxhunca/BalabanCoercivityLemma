import NtCvOF7

/-!
# CvOF8 -- `firstTerm` on the Z-profile `B = zfield g` at a chain saddle (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open scoped Matrix RealInnerProductSpace
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverJacobi
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG

variable {ell M R : ℕ}

theorem zrow_congr_nested (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (ρ ρ' : ℕ → ℕ → ℝ)
    (h : ∀ j, j ≤ 2 → ∀ r, isRowN ell M R j r → ρ j r = ρ' j r) :
    zrow (geomOf ell 2 (neS ell M R)) ρ = zrow (geomOf ell 2 (neS ell M R)) ρ' := by
  have hg := nGeo hell3 hdvd hM hR
  refine PiLp.ext (fun p => ?_)
  show (if p.2.1.2 = 1 then dgS (ρ (p.1 : ℕ) (p.2.1.1 0).val) else 0) = (if p.2.1.2 = 1 then dgS (ρ' (p.1 : ℕ) (p.2.1.1 0).val) else 0)
  by_cases h1 : p.2.1.2 = 1
  · rw [if_pos h1, if_pos h1]
    congr 1
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    have hmem : (p.2.1.1, (1 : Fin 3)) ∈ bondsLam (geomOf ell 2 (neS ell M R)) (p.1 : ℕ) := by
      have := p.2.2
      have hq : ((p.2.1.1, (1 : Fin 3))) = p.2.1 := Prod.ext rfl h1.symm
      rw [hq]
      exact this
    exact h _ hj _ (((bondsLam_one_iff hg hM hj p.2.1.1).mp hmem).2)
  · rw [if_neg h1, if_neg h1]

/-- `Ring.inverse` of a unit applied to an image. -/
theorem ring_inverse_apply_of_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : E →L[ℝ] E) (hN : IsUnit N) (v y : E) (h : N v = y) : Ring.inverse N y = v := by
  obtain ⟨u, rfl⟩ := hN
  rw [Ring.inverse_unit, ← h]
  have : ((↑u⁻¹ : E →L[ℝ] E) * (↑u : E →L[ℝ] E)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  show ((↑u⁻¹ : E →L[ℝ] E) * (↑u : E →L[ℝ] E)) v = v
  rw [this]; rfl

theorem zfield_Wt_mem (hell3 : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (ρ : ℕ → ℕ → ℝ) :
    (zfield (Wt ell (isRowN ell M R) ρ) : BondFnL2 (scaleUp ell 2 (neLu M R))) ∈ bondSupp (geomOf ell 2 (neS ell M R)) := by
  have hg := nGeo hell3 hdvd hM hR
  refine zfield_mem_bondSupp _ (fun v => neP0 ell M R ≤ v ∧ v < neQ0 ell M R) ?_ _ ?_
  · ext x; simp only [geomOf, Set.mem_setOf_eq]; exact neS_om0 x
  · intro v _ hv
    exact Wt_outside hg hv ρ

end AdalyFormal.CoverOmega

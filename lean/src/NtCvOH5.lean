import NtCvOH4

/-!
# CvOH5 -- `StagSetup` for the nested instance (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {ell M R : ℕ}

theorem ne_QN (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neQ0 ell M R ≤ neN ell M R := (ne_geo3 hell hM hR).QN

theorem nested_stagSetup (hell3 : 3 ≤ ell) (hE : StagOK ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    StagSetup (scaleUp ell 2 (neLu M R)) ell (neC ell M R) (geomOf ell 2 (neS ell M R)) (isRowN ell M R) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  have hdiv : ∀ μ, ell * ell ∣ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    rw [ne_scaleUp hell hM]
    exact ⟨M * (4 * R + (2 * CfData.cf + 6)), by unfold neN; ring⟩
  have hlo : ell ≤ neC ell M R := by
    obtain ⟨c1, c2, c3, c4, c5⟩ := ne_lin_c (M := M) hell3
    have h1 : ell ≤ ell * M := Nat.le_mul_of_pos_right _ hM
    unfold neC neA'; omega
  have hN2 : 2 ∣ scaleUp ell 2 (neLu M R) 1 + 1 := by
    rw [ne_scaleUp hell hM]
    exact ⟨ell * (ell * (M * (2 * R + CfData.cf + 3))), by unfold neN; ring⟩
  have hpar : StagPar (scaleUp ell 2 (neLu M R)) ell := by
    rcases hE with hE | ⟨hO, h3⟩
    · exact Or.inl hE
    · refine Or.inr ⟨hO, h3, ?_⟩
      rw [ne_scaleUp hell hM]
      have h1 : 1 ≤ M := hM
      have h2 : ell * ell ≤ ell * (ell * M) := by
        calc ell * ell = ell * (ell * 1) := by ring
          _ ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      have h3 : ell ≤ ell * ell := Nat.le_mul_self ell
      unfold neN
      omega
  refine ⟨hN2, hpar, hell, hdiv, hlo, ?_, rfl, rfl, ?_, ?_⟩
  · rw [ne_scaleUp hell hM]
    have h1 := layer_hi hg
    have h2 := ne_QN hell3 hM hR
    have h3 : neB' ell M R < neQ0 ell M R := by
      have := hg.hB'A; have := hg.hAB; have := hg.hBQ1; have := hg.hQ1Q0; omega
    have h4 : ell * ell = ell ^ 2 := (pow_two ell).symm
    rw [h4]
    omega
  · intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    exact crs_of_bondsLam hg hM hj p.2.1 p.2.2
  · intro j hj y
    exact bondsLam_one_iff hg hM hj y

#print axioms nested_stagSetup

end AdalyFormal.CoverOmega

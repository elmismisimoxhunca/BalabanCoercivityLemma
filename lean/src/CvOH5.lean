import CvOH4

/-!
# CvOH5 -- `StagSetup` for the nested instance (lane omega)
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverOmega

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {ell M R : ℕ}

theorem ne_QN (hell : 3 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neQ0 ell M R ≤ neN ell M R := (ne_geo3 hell hM hR).QN

theorem nested_stagSetup (hell3 : 3 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) :
    StagSetup (scaleUp ell 2 (neLu M R)) ell (neC ell M R) (geomOf ell 2 (neS ell M R)) (isRowN ell M R) := by
  have hg := nGeo hell3 hdvd hM hR
  have hell : 0 < ell := by omega
  have hdiv : ∀ μ, ell * ell ∣ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    rw [ne_scaleUp hell hM]
    exact ⟨M * (4 * R + 17), by unfold neN; ring⟩
  have hlo : ell ≤ neC ell M R := by
    obtain ⟨m', hm'⟩ := hdvd
    have hm0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
    unfold neC; rw [hm']; nlinarith [Nat.zero_le (ell * (ell * (R * (ell * m')))), Nat.mul_pos hell hm0]
  refine ⟨?_, hE, hell, hdiv, hlo, ?_, rfl, rfl, ?_, ?_⟩
  · rw [ne_scaleUp hell hM]
    exact dvd_trans hE ⟨ell * (M * (4 * R + 17)), by unfold neN; ring⟩
  · rw [ne_scaleUp hell hM]
    have h1 := layer_hi hg
    have h2 := ne_QN hell3 hM hR
    have h3 : neB' ell M R < neQ0 ell M R := by
      have := hg.hB'A; have := hg.hAB; have := hg.hBQ1; have := hg.hQ1Q0; omega
    have h4 : ell ≤ ell ^ 2 := by nlinarith
    omega
  · intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    exact crs_of_bondsLam hg hM hj p.2.1 p.2.2
  · intro j hj y
    exact bondsLam_one_iff hg hM hj y

#print axioms nested_stagSetup

end AdalyFormal.CoverOmega

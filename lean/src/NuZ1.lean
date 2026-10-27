import NuTwoGeo
import NuTwoUnc
import NuQ4
import NtCvOH5

/-!
# NuZ1 -- `NGeo` at `ell = 2` and the `Z0Setup` of the nested instance (lane ncwdh_ell2_20261018)
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.NcwdhTwo

open AdalyFormal.Target.ClayStatement
open AdalyFormal.CoverNested
open AdalyFormal.CoverOmega
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG

section
variable [CfData]
variable {ell M R : ℕ}

/-- `NGeo` holds for every `ell ≥ 2`. -/
theorem nGeo_two (hell : 2 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) : NGeo ell M R := by
  have G := ne_geo3_two hell hM hR
  obtain ⟨-, -, w2, gap, w2', QN, d0, d1, d2, b0P, b0Q, b1P, b1Q, b2A', b2B', b2A, b2B, cP, cQ, cP2, cQ2⟩ := G
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin_two hell hM hR
  have h1 : ∀ x, M * ell ∣ x → ell ∣ x := fun x hx => dvd_trans (Dvd.intro_left M rfl) hx
  have h2 : ∀ x, M * ell ^ 2 ∣ x → ell ^ 2 ∣ x := fun x hx => dvd_trans (Dvd.intro_left M rfl) hx
  have h2' : ∀ x, ell ^ 2 ∣ x → ell ∣ x := fun x hx => dvd_trans (dvd_pow_self ell (by norm_num)) hx
  refine ⟨by omega, hdvd, ?_, ?_, w2, ne_gap_pos_two hell hM hR, w2', ?_, ?_, h1 _ b1P, h1 _ b1Q, h2 _ b2A', h2 _ b2B', h2 _ b2A, h2 _ b2B,
    h2' _ (h2 _ b2B'), h2' _ (h2 _ b2A), h2' _ (h2 _ b2B), h2' _ (h2 _ b2A'), cP, cQ, by simpa using Nat.mul_le_mul hR hM⟩
  · simp only [neP0, neP1, neA']; omega
  · simp only [neP1, neA']; omega
  · simp only [neB, neQ1]; omega
  · simp only [neQ1, neQ0]; omega

theorem ne_QN_two (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) : neQ0 ell M R ≤ neN ell M R := (ne_geo3_two hell hM hR).QN


/-- the `Z0Setup` of the nested instance (even `ell ≥ 2`), at the lower endpoint `neC0` of the central direction-0 bond of the thin component. -/
theorem nested_z0Setup (hell2 : 2 ≤ ell) (hE : 2 ∣ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) (t : ℝ)
    (ht : |t| < Real.pi / 2) :
    Z0Setup (scaleUp ell 2 (neLu M R)) ell (neC0 ell M R) t (geomOf ell 2 (neS ell M R)) (isRowN ell M R) := by
  have hg := nGeo_two hell2 hdvd hM hR
  have hell : 0 < ell := by omega
  have hcf := CfData.hcf
  have hdiv : ∀ μ, ell * ell ∣ scaleUp ell 2 (neLu M R) μ + 1 := by
    intro μ
    rw [ne_scaleUp hell hM]
    exact ⟨M * (4 * R + (2 * CfData.cf + 6)), by unfold neN; ring⟩
  have hN2 : 2 ∣ scaleUp ell 2 (neLu M R) 1 + 1 := by
    rw [ne_scaleUp hell hM]
    exact ⟨ell * (ell * (M * (2 * R + CfData.cf + 3))), by unfold neN; ring⟩
  have e1 : ell * M ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hell)
  have e2 : ell * ell ≤ ell * (ell * M) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hM)
  have e3 : CfData.cf * (ell * M) ≤ CfData.cf * (ell * (ell * M)) := Nat.mul_le_mul_left _ e1
  have e4 : 10 * (ell * M) ≤ CfData.cf * (ell * M) := Nat.mul_le_mul_right _ hcf
  have e5 : ell ≤ ell * M := Nat.le_mul_of_pos_right _ hM
  have e6 : ell * (ell * M) ≤ ell * (ell * (R * M)) := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ne_lin_two hell2 hM hR
    exact c7
  have hlo : ell ≤ neC0 ell M R := by
    unfold neC0 neA'; omega
  have hhi : neC0 ell M R + ell * ell < scaleUp ell 2 (neLu M R) 0 + 1 := by
    rw [ne_scaleUp hell hM]
    unfold neC0 neA' neN; omega
  refine ⟨⟨hN2, hE, hell, hdiv, hlo, hhi, ht⟩, rfl, rfl, ?_, ?_⟩
  · intro p
    have hj : (p.1 : ℕ) ≤ 2 := by have := p.1.2; simp [geomOf] at this ⊢; omega
    exact crs_of_bondsLam hg hM hj p.2.1 p.2.2
  · intro j hj y
    exact bondsLam_one_iff hg hM hj y

end

end AdalyFormal.NcwdhTwo

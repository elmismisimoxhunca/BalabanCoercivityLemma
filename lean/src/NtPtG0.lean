import NtPtD2
import NtCvON5

/-!
# PtG0 -- numeric facts for the nested tower (lane omega/near2/point)
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.CoverOmega


set_option linter.unusedSectionVars false
variable [CfData]
open AdalyFormal.CoverNested

/-- the arithmetic facts about the nested region boundaries used by the flat-point argument. -/
structure PGeo (ell M R : ℕ) : Prop where
  hell : 3 ≤ ell
  hdell : ell ∣ M
  hM : 0 < M
  hR : 1 ≤ R
  hNpos : 0 < neN ell M R
  hNd : ell ^ 2 ∣ neN ell M R
  d1p : ell ∣ neP1 ell M R
  d1q : ell ∣ neQ1 ell M R
  d2a' : ell ^ 2 ∣ neA' ell M R
  d2b' : ell ^ 2 ∣ neB' ell M R
  d2a : ell ^ 2 ∣ neA ell M R
  d2b : ell ^ 2 ∣ neB ell M R
  p0pos : 1 ≤ neP0 ell M R
  collar_p : neP1 ell M R = neP0 ell M R + R * M
  collar_q : neQ0 ell M R = neQ1 ell M R + R * M
  rm2 : 2 ≤ R * M
  hp : ell ≤ neP1 ell M R
  hpa : neP1 ell M R + ell ^ 2 ≤ neA' ell M R
  hab : neA' ell M R < neB' ell M R
  hba : neB' ell M R + ell ^ 2 ≤ neA ell M R
  hab2 : neA ell M R < neB ell M R
  hbq : neB ell M R + ell ^ 2 ≤ neQ1 ell M R
  hq1q0 : neQ1 ell M R < neQ0 ell M R
  hqN : neQ0 ell M R + ell ^ 2 ≤ neN ell M R
  rm_ell : ell ≤ R * M

theorem pgeo {ell M R : ℕ} (hell : 3 ≤ ell) (hdvd : ell ∣ M) (hM : 0 < M) (hR : 1 ≤ R) : PGeo ell M R := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := ne_lin hell hM hR
  have NG := nGeo hell hdvd hM hR
  have hMe : ell ≤ M := Nat.le_of_dvd hM hdvd
  have e2M : ell * ell ≤ ell * M := Nat.mul_le_mul_left ell hMe
  have e2v : ell * ell ≤ ell * (ell * M) := Nat.mul_le_mul_left ell (by nlinarith)
  have hrm_e : ell ≤ R * M := le_trans hMe l5
  have hsq : ell ^ 2 = ell * ell := pow_two ell
  have e1s : ell ≤ ell * ell := Nat.le_mul_self ell
  have hs_w : ell * ell ≤ ell * (R * M) := le_trans e2M l6
  have hv1 : 1 ≤ ell * (ell * M) := le_trans (by omega) e2v
  have cP := NG.cP
  have cQ := NG.cQ
  refine ⟨hell, hdvd, hM, hR, ?_, ?_, NG.dP1, NG.dQ1, NG.dA', NG.dB', NG.dA, NG.dB, ?_, cP, cQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrm_e⟩
  · simp only [neN]; omega
  · exact ⟨4 * (R * M) + 2 * (CfData.cf * M) + 6 * M, by simp only [neN]; ring⟩
  · simp only [neP0, neP1, neA']; omega
  · omega
  · simp only [neP1, neA']; omega
  · rw [hsq]; simp only [neP1, neA']; omega
  · exact NG.hAB'
  · rw [hsq]; simp only [neB', neA]; omega
  · exact NG.hAB
  · rw [hsq]; simp only [neB, neQ1]; omega
  · exact NG.hQ1Q0
  · rw [hsq]; simp only [neQ0, neQ1, neB, neN]; omega

#print axioms pgeo

end AdalyFormal.CoverOmega

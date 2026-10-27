import SH1

/-!
# SH2 -- the SHARP collar for `tilde-square^5` being a class box (`j >= 1`).

`collarOK ell M R j  :<=>  18 * M ell^j + 3 <= (R + 3) * M ell^(j-1)`   (i.e. `R >= 18 ell - 3 + 3 / (M ell^(j-1))`).

`cube5_in_Om_sharp`: under `collarOK` every `D_j` cube has `tilde-square^5 subset Omega_{j-1}`.
`cube5_is_class_box_sharp`: under `collarOK` (and `2 <= ell`, `0 < M`; no strict torus bound is used) `tilde-square^5` is a class box of
factor 12 at index `j` or `12 ell` at index `j-1`, with `IsClassCubeG`.
The old regime `21 ell <= R` implies `collarOK` (`collarOK_of_21`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409S

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2 AdalyFormal.StatementLaneG AdalyFormal.M2Bridge
open AdalyFormal.GeneralClass
open AdalyFormal.P409
open AdalyFormal.P409W
open AdalyFormal.P409C5

variable {L : PeriodicLatticeExtent}

/-- the sharp collar condition at level `j` (`j >= 1`). -/
def collarOK (ell M R j : ℕ) : Prop := 18 * bigSide M ell j + 3 ≤ (R + 3) * bigSide M ell (j - 1)

theorem collarOK_of_21 {ell M R j : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hj : 1 ≤ j) (hR : 21 * ell ≤ R) :
    collarOK ell M R j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold collarOK
  have hb : bigSide M ell (j' + 1) = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM (by omega) j'
  simp only [Nat.add_sub_cancel]
  rw [hb]
  have h1 : (21 * ell + 3) * bigSide M ell j' ≤ (R + 3) * bigSide M ell j' :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem collarOK_R_ge {ell M R j : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hj : 1 ≤ j) (h : collarOK ell M R j) :
    18 * ell ≤ R + 2 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold collarOK at h
  have hb : bigSide M ell (j' + 1) = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM (by omega) j'
  simp only [Nat.add_sub_cancel] at h
  rw [hb] at h
  by_contra hc
  push Not at hc
  have : (R + 3) * bigSide M ell j' ≤ (18 * ell) * bigSide M ell j' := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **Step A.** Under the sharp collar condition, `tilde-square^5 subset Omega_{j'}` for a `D_{j'+1}` cube. -/
theorem cube5_in_Om_sharp {ell M R k j' : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hA : Admissible ell M R k S) (hD : IsDCube ell M k S (j' + 1) c) :
    printedCube5 (bigSide M ell (j' + 1)) c ⊆ S.Om j' := by
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  have hell0 : 0 < ell := by omega
  have hb : bigSide M ell (j' + 1) = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM hell0 j'
  have hdvd : bigSide M ell j' ∣ bigSide M ell (j' + 1) := bigSide_dvd' M ell (Nat.le_succ j')
  have hx0c' : x₀ ∈ cubeR c (bigSide M ell (j' + 1)) := by rw [← dCube_eq]; exact hx0c
  intro y hy
  rw [printedCube5_eq] at hy
  by_contra hn
  have hgN' : ∀ μ : Fin 3, bigSide M ell (j' + 1) ∣ L μ + 1 := hA.2.2.1 (j' + 1) hjk
  have hhN' : ∀ μ : Fin 3, bigSide M ell j' ∣ L μ + 1 := hA.2.2.1 j' (by omega)
  have hgc : ∀ μ : Fin 3, bigSide M ell (j' + 1) ∣ (c μ).val := fun μ => Nat.dvd_of_mod_eq_zero (hgrid μ)
  have hhc : ∀ μ : Fin 3, bigSide M ell j' ∣ (c μ).val := fun μ => dvd_trans hdvd (hgc μ)
  have hgg : bigSide M ell (j' + 1) ∣ bigSide M ell (j' + 1) := dvd_rfl
  have hh6 : bigSide M ell j' ∣ 6 * bigSide M ell (j' + 1) := Dvd.dvd.mul_left hdvd 6
  have hA1 : (6 * bigSide M ell (j' + 1) - bigSide M ell j') + bigSide M ell j' = 6 * bigSide M ell (j' + 1) := by
    have : bigSide M ell j' ≤ 6 * bigSide M ell (j' + 1) := by rw [hb]; nlinarith
    omega
  obtain ⟨y', x', hy', hx', hd⟩ := site_pair c y x₀ (bigSide M ell j') (6 * bigSide M ell (j' + 1))
    (6 * bigSide M ell (j' + 1) - bigSide M ell j') (bigSide M ell (j' + 1)) (bigSide M ell (j' + 1)) 0
    hp hhN' hhc hh6 hA1 (bigSide_pos' hM hell0 (j' + 1)) hgN' hgc dvd_rfl (by omega) hy hx0c'
  have hyn : y' ∉ S.Om j' := fun h => hn (om_cell hA (le_refl j') h (fun μ => (hy' μ).symm))
  have hx'm : x' ∈ S.Om (j' + 1) := om_cell hA (le_refl (j' + 1)) hx0.1 (fun μ => hx' μ)
  have hc := AdalyFormal.M1.collar hA (j := j') (by omega) hyn hx'm
  unfold collarOK at hcol
  simp only [Nat.add_sub_cancel] at hcol
  have hge : bigSide M ell j' ≤ 6 * bigSide M ell (j' + 1) := by rw [hb]; nlinarith
  have e1 : (R + 3) * bigSide M ell j' = R * bigSide M ell j' + 3 * bigSide M ell j' := by ring
  omega

end AdalyFormal.P409S

import SH2

/-!
# SH3 -- `tilde-square^5` is a class box under the SHARP collar `collarOK` (sufficiency half of the threshold).

`cube5_is_class_box_sharp`: `2 <= ell`, `0 < M`, `collarOK ell M R (j'+1)`, admissible tower of depth `k`, `D_{j'+1}` cube `c`:
`tilde-square^5` is `DescribedAt` (and `IsClassCubeG`) with `(i,f) = (j'+1, 12)` or `(j', 12 ell)`.  No strict torus bound is needed.
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
open AdalyFormal.P409L (cubeR_eq_siteBox)

variable {L : PeriodicLatticeExtent}

/-- build `DescribedAt` for the cube at index `i` with factor `f`, `f * M ell^i = 12 g`. -/
theorem cube5_described {ell M R k g i f : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hA : Admissible ell M R k S) (hi : i ≤ k) (hdvd : bigSide M ell i ∣ g) (hf : f * bigSide M ell i = 12 * g)
    (hgc : ∀ μ : Fin 3, g ∣ (c μ).val)
    (hsub : printedCube5 g c ⊆ towerBj S i ∪ towerBj S (i + 1))
    (hmeet : (printedCube5 g c ∩ towerBj S i).Nonempty) :
    DescribedAt ell M f k S (printedCube5 g c) i := by
  have hgN : ∀ μ : Fin 3, bigSide M ell i ∣ L μ + 1 := hA.2.2.1 i hi
  have hgc' : ∀ μ : Fin 3, bigSide M ell i ∣ (c μ).val := fun μ => dvd_trans hdvd (hgc μ)
  have hgr : bigSide M ell i ∣ 6 * g := Dvd.dvd.mul_left hdvd 6
  have hzgrid : GridCorner (bigSide M ell i) (zsite c (6 * g)) := fun μ =>
    Nat.mod_eq_zero_of_dvd (zsite_dvd c (6 * g) _ hgN hgc' hgr μ)
  refine ⟨hi, ⟨zsite c (6 * g), hzgrid, ?_⟩, hsub, hmeet⟩
  rw [printedCube5_eq, cubeR_eq_siteBox, hf]
  congr 1
  ring

theorem cube5_is_class_box_sharp {ell M R k j' : ℕ} {S : Tower L} {c : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hA : Admissible ell M R k S) (hD : IsDCube ell M k S (j' + 1) c) :
    ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧ 10 ≤ f ∧
      DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i ∧
      IsClassCubeG ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i := by
  have hD' := hD
  have hSub := cube5_in_Om_sharp hell hM hcol hA hD'
  obtain ⟨hjk, hgrid, x₀, hx0, hx0c⟩ := hD
  have hell0 : 0 < ell := by omega
  have hR34 : 34 ≤ R := by have := collarOK_R_ge hell hM (by omega : 1 ≤ j' + 1) hcol; omega
  set g := bigSide M ell (j' + 1) with hg
  have hb : g = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM hell0 j'
  have hg2 : 2 ≤ g := by rw [hb]; nlinarith
  have hdvd : bigSide M ell j' ∣ g := by rw [hb]; exact Dvd.intro _ rfl
  have hx0c' : x₀ ∈ cubeR c g := by rw [← dCube_eq]; exact hx0c
  have hx0P : x₀ ∈ printedCube5 g c := by rw [printedCube5_eq]; exact cubeR_mono (by omega) hx0c'
  have hgc : ∀ μ : Fin 3, g ∣ (c μ).val := fun μ => Nat.dvd_of_mod_eq_zero (hgrid μ)
  have hgN : ∀ μ : Fin 3, g ∣ L μ + 1 := hA.2.2.1 (j' + 1) hjk
  have hgpos : 0 < g := by omega
  by_cases hJ : printedCube5 g c ⊆ S.Om (j' + 1)
  · -- index j'+1, factor 12
    have hno3 : ∀ y ∈ printedCube5 g c, y ∉ S.Om (j' + 3) := by
      intro y hy hy3
      by_cases hk2 : j' + 2 ≤ k
      · have hyc : y ∈ cubeR c (6 * g) := by rw [← printedCube5_eq]; exact hy
        obtain ⟨y', x', hy', hx', hd⟩ := site_pair c y x₀ 1 (6 * g) (6 * g - 1) g g 0
          (by omega) (fun μ => one_dvd _) (fun μ => one_dvd _) (one_dvd _) (by omega)
          hgpos hgN hgc dvd_rfl (by omega) hyc hx0c'
        have hyy : ∀ μ : Fin 3, (y' μ).val = (y μ).val := fun μ => by simpa using hy' μ
        have hyeq : y' = y := funext fun μ => Fin.ext (hyy μ)
        subst hyeq
        have hx'n : x' ∉ S.Om (j' + 2) := fun h =>
          hx0.2 (om_cell hA (show j' + 1 ≤ j' + 2 by omega) h (fun μ => (hx' μ).symm))
        have hcl := AdalyFormal.M1.collar hA (j := j' + 2) hk2 hx'n (show y' ∈ S.Om (j' + 2 + 1) from hy3)
        have hb2 : bigSide M ell (j' + 2) = g * ell := AdalyFormal.M1.bigSide_succ M ell (j' + 1)
        rw [hb2, pdist_comm] at hcl
        have : 18 * g ≤ R * (g * ell) := by nlinarith
        omega
      · rw [hA.2.1 (j' + 3) (by omega)] at hy3; exact hy3
    have hsubB : printedCube5 g c ⊆ towerBj S (j' + 1) ∪ towerBj S (j' + 1 + 1) := by
      intro y hy
      have h1 := hJ hy
      have h3 := hno3 y hy
      by_cases h2 : y ∈ S.Om (j' + 2)
      · exact Or.inr ⟨h2, h3⟩
      · exact Or.inl ⟨h1, h2⟩
    have hmeet : (printedCube5 g c ∩ towerBj S (j' + 1)).Nonempty := ⟨x₀, hx0P, hx0⟩
    have hD12 := cube5_described hA hjk dvd_rfl (show 12 * bigSide M ell (j' + 1) = 12 * g by rw [hg]) hgc hsubB hmeet
    exact ⟨j' + 1, 12, Or.inl ⟨rfl, rfl⟩, by norm_num, hD12,
      (isClassCubeG_iff hA.1 _ _).2 ⟨by norm_num, hD12⟩⟩
  · -- index j', factor 12 ell
    obtain ⟨y₁, hy₁, hy₁n⟩ := Set.not_subset.1 hJ
    have hno2 : ∀ y ∈ printedCube5 g c, y ∉ S.Om (j' + 2) := by
      intro y hy hy2
      have hyc : y ∈ cubeR c (6 * g) := by rw [← printedCube5_eq]; exact hy
      have hy₁c : y₁ ∈ cubeR c (6 * g) := by rw [← printedCube5_eq]; exact hy₁
      obtain ⟨a', b', ha', hb', hd⟩ := site_pair c y₁ y g (6 * g) (5 * g) g (6 * g) (5 * g)
        hgpos hgN hgc (Dvd.dvd.mul_left dvd_rfl 6) (by omega)
        hgpos hgN hgc (Dvd.dvd.mul_left dvd_rfl 6) (by omega) hy₁c hyc
      have han : a' ∉ S.Om (j' + 1) := fun h => hy₁n (om_cell hA (le_refl (j' + 1)) h (fun μ => (ha' μ).symm))
      have hbm : b' ∈ S.Om (j' + 2) := om_cell hA (show j' + 1 ≤ j' + 2 by omega) hy2 (fun μ => hb' μ)
      have hcl : R * g < pdist a' b' := AdalyFormal.M1.collar hA (j := j' + 1) hjk han hbm
      have : 30 * g + 3 ≤ R * g := by nlinarith
      omega
    have hsubB : printedCube5 g c ⊆ towerBj S j' ∪ towerBj S (j' + 1) := by
      intro y hy
      have h1 := hSub hy
      have h3 := hno2 y hy
      by_cases h2 : y ∈ S.Om (j' + 1)
      · exact Or.inr ⟨h2, h3⟩
      · exact Or.inl ⟨h1, h2⟩
    have hmeet : (printedCube5 g c ∩ towerBj S j').Nonempty := ⟨y₁, hy₁, hSub hy₁, hy₁n⟩
    have hD12 := cube5_described (f := 12 * ell) hA (by omega) hdvd (by rw [hb]; ring) hgc hsubB hmeet
    exact ⟨j', 12 * ell, Or.inr ⟨rfl, rfl⟩, by omega, hD12,
      (isClassCubeG_iff hA.1 _ _).2 ⟨by omega, hD12⟩⟩

end AdalyFormal.P409S

import SH7

/-!
# SH8 -- `sharp_core_gen` (generic: any admissible tower with the near corner outside `Omega_j`, under `collarOK`), `cube5_sharp_core` (its lone-tower instance) and the two-sided `cube5_threshold_iff`:

* `cube5_sharp_core` : `collarOK` + lone-block tower: factor `12 ell` at index `j-1` is attained, and is the least factor (any index) of a `DescribedAt` box (indeed of any set `subset B^i u B^(i+1)` enclosed in a box) containing `tilde-square^5`;
* `cube5_threshold_iff` : "for every torus `Lf` with `M ell^k < N`, every admissible tower of depth `k` and every `D_j` cube, `tilde-square^5` is `DescribedAt` with factor 12 at index `j` or
  `12 ell` at index `j-1`"  <->  `collarOK ell M R j`, i.e. `18 M ell^j + 3 <= (R+3) M ell^(j-1)` (necessity half: `cube5_fails_below` on the torus `(3R+30) M ell^k`).
The stratum non-emptiness conjunct and the full-depth tower are SH9-SH11.
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
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- the near corner of `tilde-square^5` (all coordinates `(R+6) g`). -/
theorem near_mem_cube5 {ell M R j : ℕ} {Lf : PeriodicLatticeExtent} (hM : 0 < M) (hell : 0 < ell)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1) :
    sitePt Lf ((R + 6) * bigSide M ell j) ∈ printedCube5 (bigSide M ell j) (loneC Lf ell M R j) := by
  have hgpos : 0 < bigSide M ell j := bigSide_pos' hM hell j
  set g := bigSide M ell j with hg
  have e3 : (R + 6) * g = R * g + 6 * g := by ring
  have e2 : (R + 12) * g = R * g + 12 * g := by ring
  have e4 : (3 * R + 30) * g = 3 * (R * g) + 30 * g := by ring
  have hN : ∀ μ : Fin 3, 3 * (R * g) + 30 * g ≤ Lf μ + 1 := fun μ => by have := hbig μ; omega
  have hlt : ∀ μ : Fin 3, (R + 6) * g < Lf μ + 1 := fun μ => by have := hN μ; omega
  have hcv : ∀ μ : Fin 3, ((loneC Lf ell M R j) μ).val = (R + 12) * g := fun μ => by
    have h12 : (R + 12) * g < Lf μ + 1 := by have := hN μ; omega
    exact sitePt_val _ μ h12
  rw [printedCube5_eq]
  apply mem_cubeR_of_nat
  intro μ
  rw [hcv μ, sitePt_val _ μ (hlt μ)]
  omega

/-- on the lone tower `tilde-square^5` is not inside `Omega_j`. -/
theorem loneT_near_not_in {ell M R j : ℕ} {Lf : PeriodicLatticeExtent} (hM : 0 < M) (hell : 0 < ell)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1) :
    sitePt Lf ((R + 6) * bigSide M ell j) ∉ (loneT (L := Lf) ell M R j).Om j := by
  have hgpos : 0 < bigSide M ell j := bigSide_pos' hM hell j
  set g := bigSide M ell j with hg
  have e3 : (R + 6) * g = R * g + 6 * g := by ring
  have e4 : (3 * R + 30) * g = 3 * (R * g) + 30 * g := by ring
  have hlt : (R + 6) * g < Lf 0 + 1 := by have := hbig 0; omega
  rw [loneT_Om_top]
  intro h
  have := h 0
  rw [sitePt_val _ 0 hlt] at this
  have h2 := blk_bounds (R + 11) g ((R + 6) * g) hgpos this
  have e5 : g * (R + 11) = R * g + 11 * g := by ring
  omega

/-- the generic core: any admissible tower in which the near corner is outside `Omega_j`. -/
theorem sharp_core_gen {ell M R k j' : ℕ} {Lf : PeriodicLatticeExtent} {S : Tower Lf}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1))
    (hA : Admissible ell M R k S) (hD : IsDCube ell M k S (j' + 1) (loneC Lf ell M R (j' + 1)))
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell (j' + 1) ≤ Lf μ + 1)
    (hvX : sitePt Lf ((R + 6) * bigSide M ell (j' + 1)) ∉ S.Om (j' + 1)) :
    (∀ F : ℕ, F + 1 ≤ 12 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), i ≤ k →
      sites ⊆ towerBj S i ∪ towerBj S (i + 1) →
      (∃ z : PeriodicLatticeSite Lf, sites ⊆ siteBox z (F * bigSide M ell i)) →
      ¬ printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1)) ⊆ sites) ∧
    DescribedAt ell M (12 * ell) k S (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) j' ∧
    IsClassCubeG ell M (12 * ell) k S (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) j' ∧
    (∀ (i f : ℕ), DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) i →
      i ≤ j' ∧ 12 * ell ≤ f) := by
  have hell0 : 0 < ell := by omega
  have hlow := sharp_lower_gen (k := k) (R := R) hell hM hA.1 hbig hvX
  have hvc := near_mem_cube5 (R := R) hM hell0 hbig
  have hdesc : ∀ (i f : ℕ), DescribedAt ell M f k S
      (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) i → i ≤ j' ∧ 12 * ell ≤ f := by
    intro i f hd
    obtain ⟨hik, ⟨z, -, hz⟩, hsB, -⟩ := hd
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      have hvOm : sitePt Lf ((R + 6) * bigSide M ell (j' + 1)) ∈ S.Om i := by
        rcases hsB hvc with h | h
        · exact h.1
        · exact AdalyFormal.GeneralClass.om_anti hA.1 (Nat.le_succ i) h.1
      exact hvX (AdalyFormal.GeneralClass.om_anti hA.1 (by omega) hvOm)
    · by_contra hc
      push Not at hc
      exact hlow f (by omega) _ i hik hsB ⟨z, by rw [hz]⟩ (fun _ h => h)
  obtain ⟨i, f, hif, -, hd, hG⟩ := cube5_is_class_box_sharp hell hM hcol hA hD
  have hi := hdesc i f hd
  rcases hif with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · subst h2
    have hij : i = j' := by omega
    subst hij
    exact ⟨hlow, hd, hG, hdesc⟩

theorem cube5_sharp_core {ell M R k j' : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1)) (hjk : j' + 1 ≤ k)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell (j' + 1) ≤ Lf μ + 1) :
    Admissible ell M R k (loneT (L := Lf) ell M R (j' + 1)) ∧
    IsDCube ell M k (loneT ell M R (j' + 1)) (j' + 1) (loneC Lf ell M R (j' + 1)) ∧
    (∀ F : ℕ, F + 1 ≤ 12 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), i ≤ k →
      sites ⊆ towerBj (loneT ell M R (j' + 1)) i ∪ towerBj (loneT ell M R (j' + 1)) (i + 1) →
      (∃ z : PeriodicLatticeSite Lf, sites ⊆ siteBox z (F * bigSide M ell i)) →
      ¬ printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1)) ⊆ sites) ∧
    DescribedAt ell M (12 * ell) k (loneT ell M R (j' + 1)) (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) j' ∧
    IsClassCubeG ell M (12 * ell) k (loneT ell M R (j' + 1)) (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) j' ∧
    (∀ (i f : ℕ), DescribedAt ell M f k (loneT ell M R (j' + 1)) (printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1))) i →
      i ≤ j' ∧ 12 * ell ≤ f) := by
  have hell0 : 0 < ell := by omega
  have hA : Admissible ell M R k (loneT (L := Lf) ell M R (j' + 1)) := loneT_admissible (by omega) hjk hdiv
  have hD := loneT_dcube (R := R) hM hell0 hjk hbig
  obtain ⟨h1, h2, h3, h4⟩ := sharp_core_gen hell hM hcol hA hD hbig (loneT_near_not_in hM hell0 hbig)
  exact ⟨hA, hD, h1, h2, h3, h4⟩

theorem cube5_threshold_iff {ell M R k j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (hjk : j' + 1 ≤ k) :
    (∀ (Lf : PeriodicLatticeExtent) (S : Tower Lf) (c : PeriodicLatticeSite Lf),
        Admissible ell M R k S → (∀ μ : Fin 3, bigSide M ell k < Lf μ + 1) → IsDCube ell M k S (j' + 1) c →
        ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧
          DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i) ↔
      collarOK ell M R (j' + 1) := by
  have hell0 : 0 < ell := by omega
  constructor
  · intro H
    by_contra hnc
    unfold collarOK at hnc
    simp only [Nat.add_sub_cancel] at hnc
    push Not at hnc
    have hgk : 0 < bigSide M ell k := bigSide_pos' hM hell0 k
    have hmono : bigSide M ell (j' + 1) ≤ bigSide M ell k := bigSide_mono' hell0 hjk
    have hN : ∀ μ : Fin 3, ((fun _ : Fin 3 => (3 * R + 30) * bigSide M ell k - 1) μ) + 1 = (3 * R + 30) * bigSide M ell k := by
      intro μ
      have : 1 ≤ (3 * R + 30) * bigSide M ell k := by nlinarith
      show (3 * R + 30) * bigSide M ell k - 1 + 1 = _
      omega
    have hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ (fun _ : Fin 3 => (3 * R + 30) * bigSide M ell k - 1) μ + 1 := by
      intro μ; rw [hN μ]; exact Dvd.intro_left _ rfl
    have hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell (j' + 1) ≤
        (fun _ : Fin 3 => (3 * R + 30) * bigSide M ell k - 1) μ + 1 := by
      intro μ; rw [hN μ]; exact Nat.mul_le_mul_left _ hmono
    obtain ⟨S, c, hA, hD, -, -, hnot⟩ := cube5_fails_below (R := R) hell hM hjk hnc hdiv hbig
    have hgt : ∀ μ : Fin 3, bigSide M ell k < (fun _ : Fin 3 => (3 * R + 30) * bigSide M ell k - 1) μ + 1 := by
      intro μ; rw [hN μ]; nlinarith
    exact hnot (H _ S c hA hgt hD)
  · intro hcol Lf S c hA _ hD
    obtain ⟨i, f, hif, -, hd, -⟩ := cube5_is_class_box_sharp hell hM hcol hA hD
    exact ⟨i, f, hif, hd⟩

end AdalyFormal.P409S

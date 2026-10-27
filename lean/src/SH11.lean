import SH10

/-!
# SH11 -- the final statements on the FULL-DEPTH tower `deepT` (all strata `B^0 .. B^k` non-empty).

* `cube5_sharp_all`  : `collarOK` => (12 ell is exactly the least factor, at every level `j >= 1` and every depth `k >= j`).
* `cube5_fails_below_deep` : not `collarOK` => (a non-degenerate tower on which `tilde-square^5` is in no box of index `>= j-1`, hence not of factor 12 at `j` nor `12 ell` at `j-1`).
* `collarOK_iff_Rstar` : `collarOK` is `R >= 18 ell - 3 + ceil(3 / (M ell^(j-1)))`, i.e. `R >= 18 ell - 2` as soon as `M ell^(j-1) >= 3`.
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

theorem deep_bigj {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hjk : j ≤ k)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1 := fun μ => by
  have hgk : bigSide M ell j ≤ bigSide M ell k := bigSide_mono' (by omega) hjk
  have := hbig μ
  have h1 : (3 * R + 30) * bigSide M ell j ≤ (5 * R + 40) * bigSide M ell k := Nat.mul_le_mul (by omega) hgk
  omega

theorem cube5_sharp_all {ell M R k j' : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hcol : collarOK ell M R (j' + 1)) (hjk : j' + 1 ≤ k)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf),
      Admissible ell M R k S ∧ (∀ μ : Fin 3, bigSide M ell k < Lf μ + 1) ∧ IsDCube ell M k S (j' + 1) c ∧
      (∀ i : ℕ, i ≤ k → ∃ q, q ∈ towerBj S i) ∧
      (∀ F : ℕ, F + 1 ≤ 12 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), i ≤ k →
        sites ⊆ towerBj S i ∪ towerBj S (i + 1) →
        (∃ z : PeriodicLatticeSite Lf, sites ⊆ siteBox z (F * bigSide M ell i)) →
        ¬ printedCube5 (bigSide M ell (j' + 1)) c ⊆ sites) ∧
      (∀ F : ℕ, F + 1 ≤ 12 * ell → ¬ ∃ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ),
        IsClassSetW ell M F k S sites i ∧ printedCube5 (bigSide M ell (j' + 1)) c ⊆ sites) ∧
      (∀ (i f : ℕ), DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i → i ≤ j' ∧ 12 * ell ≤ f) ∧
      DescribedAt ell M (12 * ell) k S (printedCube5 (bigSide M ell (j' + 1)) c) j' ∧
      IsClassCubeG ell M (12 * ell) k S (printedCube5 (bigSide M ell (j' + 1)) c) j' := by
  have hell0 : 0 < ell := by omega
  have hR : 1 ≤ R := by have := collarOK_R_ge hell hM (by omega : 1 ≤ j' + 1) hcol; omega
  have hbigj := deep_bigj (R := R) hell hjk hbig
  have hA := deep_admissible (R := R) (j := j' + 1) (by omega) hjk hdiv
  have hD := deep_dcube (R := R) hell hM hjk hbig
  have hvX := deep_near_not_in (R := R) hell hM hjk hbig
  obtain ⟨h1, h2, h3, h4⟩ := sharp_core_gen hell hM hcol hA hD hbigj hvX
  have hgk : 0 < bigSide M ell k := bigSide_pos' hM hell0 k
  refine ⟨deepT ell M R (j' + 1) k, loneC Lf ell M R (j' + 1), hA, ?_, hD, deep_strata hell hM hR hjk hbig, h1, ?_, h4, h2, h3⟩
  · intro μ
    have := hbig μ
    nlinarith
  · rintro F hF ⟨sites, i, ⟨hik, hsB, -, hbox, -⟩, hsub⟩
    exact h1 F hF sites i hik hsB hbox hsub

theorem cube5_fails_below_deep {ell M R k j' : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hjk : j' + 1 ≤ k)
    (hlow : (R + 3) * bigSide M ell j' < 18 * bigSide M ell (j' + 1) + 3)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf),
      Admissible ell M R k S ∧ (∀ μ : Fin 3, bigSide M ell k < Lf μ + 1) ∧ IsDCube ell M k S (j' + 1) c ∧
      (∀ i : ℕ, i ≤ k → ∃ q, q ∈ towerBj S i) ∧
      (∃ y ∈ printedCube5 (bigSide M ell (j' + 1)) c, y ∉ S.Om j') ∧
      (∀ (i f : ℕ) (sites : Set (PeriodicLatticeSite Lf)), j' ≤ i → DescribedAt ell M f k S sites i →
        ¬ printedCube5 (bigSide M ell (j' + 1)) c ⊆ sites) ∧
      ¬ ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧
        DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i := by
  have hell0 : 0 < ell := by omega
  have hbigj := deep_bigj (R := R) hell hjk hbig
  have hA := deep_admissible (R := R) (j := j' + 1) (by omega) hjk hdiv
  have hD := deep_dcube (R := R) hell hM hjk hbig
  obtain ⟨hy1, hy2⟩ := loneT_far_not_in (R := R) hell hM hlow hbigj
  have hgk : bigSide M ell (j' + 1) ≤ bigSide M ell k := bigSide_mono' hell0 hjk
  have hy3 : sitePt Lf ((R + 18) * bigSide M ell (j' + 1) - bigSide M ell j') ∉
      (deepT (L := Lf) ell M R (j' + 1) k).Om j' := by
    rw [deepT_Om]
    rintro (h | h)
    · exact hy2 h
    · have h1 := far_lower (R := R) hell hM hbig j' (by omega) _ h
      have hN0 := hbigj 0
      have e3 : (R + 18) * bigSide M ell (j' + 1) = R * bigSide M ell (j' + 1) + 18 * bigSide M ell (j' + 1) := by ring
      have e4 : (3 * R + 30) * bigSide M ell (j' + 1) = 3 * (R * bigSide M ell (j' + 1)) + 30 * bigSide M ell (j' + 1) := by ring
      have hp : 0 < bigSide M ell j' := bigSide_pos' hM hell0 j'
      have hlt0 : (R + 18) * bigSide M ell (j' + 1) - bigSide M ell j' < Lf 0 + 1 := by omega
      rw [sitePt_val _ 0 hlt0] at h1
      have hmul : (R + 18) * bigSide M ell (j' + 1) ≤ (2 * R + 30) * bigSide M ell k := Nat.mul_le_mul (by omega) hgk
      have hgj : bigSide M ell j' ≤ bigSide M ell (j' + 1) := bigSide_mono' hell0 (Nat.le_succ j')
      omega
  have hno : ∀ (i f : ℕ) (sites : Set (PeriodicLatticeSite Lf)), j' ≤ i → DescribedAt ell M f k (deepT ell M R (j' + 1) k) sites i →
      ¬ printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1)) ⊆ sites := by
    intro i f sites hi hd hsub
    obtain ⟨-, -, hsB, -⟩ := hd
    have hmem := hsB (hsub hy1)
    have hOi : sitePt Lf ((R + 18) * bigSide M ell (j' + 1) - bigSide M ell j') ∈
        (deepT (L := Lf) ell M R (j' + 1) k).Om i := by
      rcases hmem with h | h
      · exact h.1
      · exact AdalyFormal.GeneralClass.om_anti hA.1 (Nat.le_succ i) h.1
    exact hy3 (AdalyFormal.GeneralClass.om_anti hA.1 hi hOi)
  have hgk' : 0 < bigSide M ell k := bigSide_pos' hM hell0 k
  refine ⟨deepT ell M R (j' + 1) k, loneC Lf ell M R (j' + 1), hA, ?_, hD, deep_strata hell hM hR (by omega) hbig, ⟨_, hy1, hy3⟩, hno, ?_⟩
  · intro μ
    have := hbig μ
    nlinarith
  · rintro ⟨i, f, hif, hd⟩
    have hi : j' ≤ i := by rcases hif with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    exact hno i f _ hi hd (fun _ h => h)

/-! ### the closed form of the sharp collar -/

/-- `ceil(3/h)` for `h >= 1`. -/
def ceil3 (h : ℕ) : ℕ := (h + 2) / h

theorem ceil3_spec {h : ℕ} (hh : 0 < h) : 3 ≤ ceil3 h * h ∧ (ceil3 h - 1) * h < 3 := by
  have h1 := Nat.div_add_mod (h + 2) h
  have h2 := Nat.mod_lt (h + 2) hh
  unfold ceil3
  generalize (h + 2) / h = q at *
  generalize (h + 2) % h = r at *
  have hq : q ≠ 0 := by
    rintro rfl
    simp at h1
    omega
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have e : (q' + 1) * h = h * q' + h := by ring
  have e' : h * (q' + 1) = h * q' + h := by ring
  have e'' : q' * h = h * q' := by ring
  constructor
  · rw [Nat.succ_eq_add_one, e]; rw [Nat.succ_eq_add_one] at h1; omega
  · rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, e'']; rw [Nat.succ_eq_add_one] at h1; omega

theorem collarOK_iff_Rstar {ell M R j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) :
    collarOK ell M R (j' + 1) ↔ 18 * ell - 3 + ceil3 (bigSide M ell j') ≤ R := by
  have hell0 : 0 < ell := by omega
  have hb : bigSide M ell (j' + 1) = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM hell0 j'
  obtain ⟨hs1, hs2⟩ := ceil3_spec hp
  unfold collarOK
  simp only [Nat.add_sub_cancel]
  rw [hb]
  set h := bigSide M ell j' with hh
  set c := ceil3 h with hc
  have hcpos : 1 ≤ c := by
    by_contra hc0
    push Not at hc0
    have : c = 0 := by omega
    rw [this] at hs1
    omega
  obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [hc'] at hs1 hs2 ⊢
  simp only [Nat.add_sub_cancel] at hs2
  have e1 : 18 * ell - 3 + (c' + 1) = 18 * ell + c' - 2 := by omega
  rw [e1]
  constructor
  · intro H
    by_contra hn
    push Not at hn
    -- R + 3 <= 18 ell + c' - 0 ... : R + 2 < 18 ell + c'
    have h2 : R + 3 ≤ 18 * ell + c' := by omega
    have h3 : (R + 3) * h ≤ (18 * ell + c') * h := Nat.mul_le_mul_right h h2
    nlinarith
  · intro H
    have h2 : 18 * ell + c' + 1 ≤ R + 3 := by omega
    have h3 : (18 * ell + c' + 1) * h ≤ (R + 3) * h := Nat.mul_le_mul_right h h2
    nlinarith

theorem collarOK_iff_of_three {ell M R j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (h3 : 3 ≤ bigSide M ell j') :
    collarOK ell M R (j' + 1) ↔ 18 * ell ≤ R + 2 := by
  rw [collarOK_iff_Rstar hell hM]
  have : ceil3 (bigSide M ell j') = 1 := by
    unfold ceil3
    apply Nat.div_eq_of_lt_le <;> omega
  rw [this]
  omega

theorem collarOK_iff_of_two {ell M R j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (h2 : bigSide M ell j' = 2) :
    collarOK ell M R (j' + 1) ↔ 18 * ell ≤ R + 1 := by
  rw [collarOK_iff_Rstar hell hM]
  have : ceil3 (bigSide M ell j') = 2 := by
    unfold ceil3
    rw [h2]
  rw [this]
  omega

theorem collarOK_iff_of_one {ell M R j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M) (h1 : bigSide M ell j' = 1) :
    collarOK ell M R (j' + 1) ↔ 18 * ell ≤ R := by
  rw [collarOK_iff_Rstar hell hM]
  have : ceil3 (bigSide M ell j') = 3 := by
    unfold ceil3
    rw [h1]
  rw [this]
  omega

end AdalyFormal.P409S

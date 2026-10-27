import SH5

/-!
# SH6 -- below the sharp collar `tilde-square^5` is NOT inside `Omega_{j-1}` on the lone-block tower, hence in no class box of index `>= j-1` (any factor).

`cube5_fails_below` : `(R + 3) * M ell^(j-1) < 18 * M ell^j + 3` (the negation of `collarOK`), torus `M ell^k | N`, `(3R+30) M ell^j <= N`.
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

/-- the far corner block's lowest site is in `tilde-square^5` and not in `Omega_{j'}` when the collar is too small. -/
theorem loneT_far_not_in {ell M R j' : ℕ} (hell : 2 ≤ ell) (hM : 0 < M)
    (hlow : (R + 3) * bigSide M ell j' < 18 * bigSide M ell (j' + 1) + 3)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell (j' + 1) ≤ L μ + 1) :
    sitePt L ((R + 18) * bigSide M ell (j' + 1) - bigSide M ell j') ∈
        printedCube5 (bigSide M ell (j' + 1)) (loneC L ell M R (j' + 1)) ∧
      sitePt L ((R + 18) * bigSide M ell (j' + 1) - bigSide M ell j') ∉ (loneT (L := L) ell M R (j' + 1)).Om j' := by
  have hell0 : 0 < ell := by omega
  have hb : bigSide M ell (j' + 1) = bigSide M ell j' * ell := AdalyFormal.M1.bigSide_succ M ell j'
  have hp : 0 < bigSide M ell j' := bigSide_pos' hM hell0 j'
  set g := bigSide M ell (j' + 1) with hg
  set h := bigSide M ell j' with hh
  have hg2 : 2 * h ≤ g := by rw [hb]; nlinarith
  have hdvd : h ∣ g := by rw [hb]; exact Dvd.intro _ rfl
  have e1 : (R + 18) * g = R * g + 18 * g := by ring
  have e2 : (R + 12) * g = R * g + 12 * g := by ring
  have e3 : (R + 11) * g = R * g + 11 * g := by ring
  have e4 : (3 * R + 30) * g = 3 * (R * g) + 30 * g := by ring
  have e5 : (R + 3) * h = R * h + 3 * h := by ring
  have hRg : 0 ≤ R * g := Nat.zero_le _
  have hN : ∀ μ : Fin 3, 3 * (R * g) + 30 * g ≤ L μ + 1 := fun μ => by have := hbig μ; omega
  set Y := (R + 18) * g - h with hY
  have hYlt : ∀ μ : Fin 3, Y < L μ + 1 := fun μ => by have := hN μ; omega
  have hYd : h ∣ Y := Nat.dvd_sub (Dvd.dvd.mul_left hdvd _) dvd_rfl
  have hYe : Y + h = (R + 18) * g := by
    have : h ≤ (R + 18) * g := by rw [e1]; omega
    omega
  clear_value Y
  refine ⟨?_, ?_⟩
  · rw [printedCube5_eq]
    apply mem_cubeR_of_nat
    intro μ
    show ((loneC L ell M R (j' + 1)) μ).val ≤ ((sitePt L Y) μ).val + 6 * g ∧ _
    have h2 : (R + 12) * g < L μ + 1 := by have := hN μ; omega
    unfold loneC
    rw [sitePt_val _ μ h2, sitePt_val _ μ (hYlt μ)]
    constructor <;> omega
  · rw [loneT_Om_below]
    rintro ⟨w, hw, z, hz, hd⟩
    have key : ∀ μ : Fin 3, 6 * g - h + 1 ≤ pcd (L μ + 1) (z μ).val (w μ).val := by
      intro μ
      have hzy : (z μ).val / h = Y / h := by
        have := hz μ
        rw [sitePt_val _ μ (hYlt μ)] at this
        exact this
      have hzb := blk_bounds (Y / h) h (z μ).val hp hzy
      have hYe : h * (Y / h) = Y := Nat.mul_div_cancel' hYd
      rw [hYe] at hzb
      have hwb := blk_bounds (R + 11) g (w μ).val (by omega) (hw μ)
      have hwlt := (w μ).isLt
      have hzlt := (z μ).isLt
      have hNμ := hN μ
      have e6 : g * (R + 11) = R * g + 11 * g := by ring
      rw [e6] at hwb
      unfold pcd
      split_ifs <;> omega
    unfold pdist at hd
    rw [Fin.sum_univ_three] at hd
    have hd2 : pcd (L 0 + 1) (z 0).val (w 0).val + pcd (L 1 + 1) (z 1).val (w 1).val +
        pcd (L 2 + 1) (z 2).val (w 2).val ≤ R * h := hd
    have k0 := key 0; have k1 := key 1; have k2 := key 2
    have hh6 : h ≤ 6 * g := by omega
    omega

theorem cube5_fails_below {ell M R k j' : ℕ} {Lf : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hjk : j' + 1 ≤ k)
    (hlow : (R + 3) * bigSide M ell j' < 18 * bigSide M ell (j' + 1) + 3)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell (j' + 1) ≤ Lf μ + 1) :
    ∃ (S : Tower Lf) (c : PeriodicLatticeSite Lf), Admissible ell M R k S ∧ IsDCube ell M k S (j' + 1) c ∧
      (∃ y ∈ printedCube5 (bigSide M ell (j' + 1)) c, y ∉ S.Om j') ∧
      (∀ (i f : ℕ) (sites : Set (PeriodicLatticeSite Lf)), j' ≤ i → DescribedAt ell M f k S sites i →
        ¬ printedCube5 (bigSide M ell (j' + 1)) c ⊆ sites) ∧
      ¬ ∃ i f : ℕ, ((i = j' + 1 ∧ f = 12) ∨ (i + 1 = j' + 1 ∧ f = 12 * ell)) ∧
        DescribedAt ell M f k S (printedCube5 (bigSide M ell (j' + 1)) c) i := by
  have hell0 : 0 < ell := by omega
  have hA : Admissible ell M R k (loneT (L := Lf) ell M R (j' + 1)) := loneT_admissible (by omega) hjk hdiv
  have hD := loneT_dcube (R := R) hM hell0 hjk hbig
  obtain ⟨hy1, hy2⟩ := loneT_far_not_in (R := R) hell hM hlow hbig
  have hno : ∀ (i f : ℕ) (sites : Set (PeriodicLatticeSite Lf)), j' ≤ i → DescribedAt ell M f k (loneT ell M R (j' + 1)) sites i →
      ¬ printedCube5 (bigSide M ell (j' + 1)) (loneC Lf ell M R (j' + 1)) ⊆ sites := by
    intro i f sites hi hd hsub
    obtain ⟨-, -, hsB, -⟩ := hd
    have hmem := hsB (hsub hy1)
    have hOi : sitePt Lf ((R + 18) * bigSide M ell (j' + 1) - bigSide M ell j') ∈
        (loneT (L := Lf) ell M R (j' + 1)).Om i := by
      rcases hmem with h | h
      · exact h.1
      · exact AdalyFormal.GeneralClass.om_anti hA.1 (Nat.le_succ i) h.1
    exact hy2 (AdalyFormal.GeneralClass.om_anti hA.1 hi hOi)
  refine ⟨loneT ell M R (j' + 1), loneC Lf ell M R (j' + 1), hA, hD, ⟨_, hy1, hy2⟩, hno, ?_⟩
  rintro ⟨i, f, hif, hd⟩
  have hi : j' ≤ i := by rcases hif with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  exact hno i f _ hi hd (fun _ h => h)

end AdalyFormal.P409S

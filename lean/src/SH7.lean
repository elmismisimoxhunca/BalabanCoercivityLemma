import SH6

/-!
# SH7 -- the lower bound behind the sharpness of `12 ell`: `sharp_lower_gen` (any tower whose `Omega_j` misses the near corner `(R+6) g` of `tilde-square^5`; NO collar hypothesis)
and its lone-tower instance `loneT_sharp_lower`.

Statement: `tilde-square^5` is contained in NO set `sites subset B^i u B^(i+1)` that is enclosed in a periodic box of side `F * M ell^i` with `F + 1 <= 12 ell` (any index `i <= k`).
(The assembly with the positive half, `cube5_sharp_all`, is SH11; `cube5_sharp_core` is SH8.)
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

/-- two points of `tilde-square^5` at opposite ends of the same axis, and the near corner (not in `Omega_j`). -/
theorem sharp_lower_gen {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} {S : Tower Lf} (hell : 2 ≤ ell) (hM : 0 < M)
    (hnest : ∀ i : ℕ, S.Om (i + 1) ⊆ S.Om i)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1)
    (hvX : sitePt Lf ((R + 6) * bigSide M ell j) ∉ S.Om j) :
    ∀ F : ℕ, F + 1 ≤ 12 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), i ≤ k →
      sites ⊆ towerBj S i ∪ towerBj S (i + 1) →
      (∃ z : PeriodicLatticeSite Lf, sites ⊆ siteBox z (F * bigSide M ell i)) →
      ¬ printedCube5 (bigSide M ell j) (loneC Lf ell M R j) ⊆ sites := by
  have hell0 : 0 < ell := by omega
  intro F hF sites i hik hsB ⟨z, hz⟩ hsub
  set g := bigSide M ell j with hg
  have hgpos : 0 < g := bigSide_pos' hM hell0 j
  have e1 : (R + 18) * g = R * g + 18 * g := by ring
  have e2 : (R + 12) * g = R * g + 12 * g := by ring
  have e3 : (R + 6) * g = R * g + 6 * g := by ring
  have e4 : (3 * R + 30) * g = 3 * (R * g) + 30 * g := by ring
  have hN : ∀ μ : Fin 3, 3 * (R * g) + 30 * g ≤ Lf μ + 1 := fun μ => by have := hbig μ; omega
  have hlt0 : (R + 6) * g < Lf 0 + 1 := by have := hN 0; omega
  have hlt1 : (R + 6) * g < Lf 1 + 1 := by have := hN 1; omega
  have hlt2 : (R + 6) * g < Lf 2 + 1 := by have := hN 2; omega
  have hhi1 : (R + 18) * g - 1 < Lf 1 + 1 := by have := hN 1; omega
  -- the near corner v and the far-in-axis-1 corner p2
  let v : PeriodicLatticeSite Lf := sitePt Lf ((R + 6) * g)
  let p2 : PeriodicLatticeSite Lf := pt3 Lf ((R + 6) * g) ((R + 18) * g - 1) ((R + 6) * g)
  have hv0 : (v 0).val = (R + 6) * g := sitePt_val _ 0 hlt0
  have hv1 : (v 1).val = (R + 6) * g := sitePt_val _ 1 hlt1
  have hv2 : (v 2).val = (R + 6) * g := sitePt_val _ 2 hlt2
  have hp0 : (p2 0).val = (R + 6) * g := pt3_val0 _ _ _ hlt0
  have hp1 : (p2 1).val = (R + 18) * g - 1 := pt3_val1 _ _ _ hhi1
  have hp2 : (p2 2).val = (R + 6) * g := pt3_val2 _ _ _ hlt2
  have hcv : ∀ μ : Fin 3, ((loneC Lf ell M R j) μ).val = (R + 12) * g := fun μ => by
    have h12 : (R + 12) * g < Lf μ + 1 := by have := hN μ; omega
    exact sitePt_val _ μ h12
  have hvc : v ∈ printedCube5 g (loneC Lf ell M R j) := by
    rw [printedCube5_eq]
    apply mem_cubeR_of_nat
    intro μ
    rw [hcv μ]
    fin_cases μ
    · show (R + 12) * g ≤ (v 0).val + 6 * g ∧ (v 0).val < (R + 12) * g + 6 * g; rw [hv0]; omega
    · show (R + 12) * g ≤ (v 1).val + 6 * g ∧ (v 1).val < (R + 12) * g + 6 * g; rw [hv1]; omega
    · show (R + 12) * g ≤ (v 2).val + 6 * g ∧ (v 2).val < (R + 12) * g + 6 * g; rw [hv2]; omega
  have hp2c : p2 ∈ printedCube5 g (loneC Lf ell M R j) := by
    rw [printedCube5_eq]
    apply mem_cubeR_of_nat
    intro μ
    rw [hcv μ]
    fin_cases μ
    · show (R + 12) * g ≤ (p2 0).val + 6 * g ∧ (p2 0).val < (R + 12) * g + 6 * g; rw [hp0]; omega
    · show (R + 12) * g ≤ (p2 1).val + 6 * g ∧ (p2 1).val < (R + 12) * g + 6 * g; rw [hp1]; omega
    · show (R + 12) * g ≤ (p2 2).val + 6 * g ∧ (p2 2).val < (R + 12) * g + 6 * g; rw [hp2]; omega
  -- v is not in Omega_j, so i < j
  have hvs : v ∈ sites := hsub hvc
  have hij : i + 1 ≤ j := by
    by_contra hc
    push Not at hc
    have hvOm : v ∈ S.Om i := by
      rcases hsB hvs with h | h
      · exact h.1
      · exact AdalyFormal.GeneralClass.om_anti hnest (Nat.le_succ i) h.1
    exact hvX (AdalyFormal.GeneralClass.om_anti hnest (by omega) hvOm)
  have m1 := hz hvs
  have m2 := hz (hsub hp2c)
  unfold siteBox at m1 m2
  simp only [Set.mem_setOf_eq] at m1 m2
  have hlt := pcd_lt_of_offs (Lf 1 + 1) (v 1).val (p2 1).val (z 1).val (s := F * bigSide M ell i) (Nat.succ_pos _)
    (v 1).isLt (p2 1).isLt (z 1).isLt (m1 1) (m2 1)
  have hd : pcd (Lf 1 + 1) (v 1).val (p2 1).val = 12 * g - 1 := by
    rw [hv1, hp1]
    have := hN 1
    unfold pcd
    split_ifs <;> omega
  rw [hd] at hlt
  have hmono : bigSide M ell (i + 1) ≤ g := bigSide_mono' hell0 hij
  have hsucc : bigSide M ell (i + 1) = bigSide M ell i * ell := AdalyFormal.M1.bigSide_succ M ell i
  have hip : 0 < bigSide M ell i := bigSide_pos' hM hell0 i
  have h12 : 12 * g ≤ F * bigSide M ell i := by omega
  have h13 : (12 * ell) * bigSide M ell i ≤ F * bigSide M ell i := by
    rw [hsucc] at hmono
    nlinarith
  have h14 := Nat.le_of_mul_le_mul_right h13 hip
  omega


/-- the lone-tower instance. -/
theorem loneT_sharp_lower {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1) (hnest : ∀ i : ℕ, (loneT (L := Lf) ell M R j).Om (i + 1) ⊆ (loneT (L := Lf) ell M R j).Om i) :
    ∀ F : ℕ, F + 1 ≤ 12 * ell → ∀ (sites : Set (PeriodicLatticeSite Lf)) (i : ℕ), i ≤ k →
      sites ⊆ towerBj (loneT ell M R j) i ∪ towerBj (loneT ell M R j) (i + 1) →
      (∃ z : PeriodicLatticeSite Lf, sites ⊆ siteBox z (F * bigSide M ell i)) →
      ¬ printedCube5 (bigSide M ell j) (loneC Lf ell M R j) ⊆ sites := by
  have hell0 : 0 < ell := by omega
  have hgpos : 0 < bigSide M ell j := bigSide_pos' hM hell0 j
  refine sharp_lower_gen hell hM hnest hbig ?_
  have e3 : (R + 6) * bigSide M ell j = R * bigSide M ell j + 6 * bigSide M ell j := by ring
  have e4 : (3 * R + 30) * bigSide M ell j = 3 * (R * bigSide M ell j) + 30 * bigSide M ell j := by ring
  have hlt : (R + 6) * bigSide M ell j < Lf 0 + 1 := by have := hbig 0; omega
  rw [loneT_Om_top]
  intro h
  have := h 0
  rw [sitePt_val _ 0 hlt] at this
  have h2 := blk_bounds (R + 11) (bigSide M ell j) ((R + 6) * bigSide M ell j) hgpos this
  have e5 : bigSide M ell j * (R + 11) = R * bigSide M ell j + 11 * bigSide M ell j := by ring
  omega

end AdalyFormal.P409S

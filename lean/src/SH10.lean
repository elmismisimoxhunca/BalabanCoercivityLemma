import SH9

/-!
# SH10 -- the FULL-DEPTH tower: union of the near lone tower (level `j`) and a far lone tower (level `k`).

`unionTower S T` (pointwise union of the domains) of two admissible towers (same `ell M R k`, same torus) is admissible (`admissible_union`).
`deepT ell M R j k` = near lone tower (block index `R+11`, level `j`) union far lone tower (block index `3R+30`, level `k`).  Coordinate-0 extents separate them:
near `x_0 < (2R+12) M ell^j`, far `x_0 >= (2R+30) M ell^k`.  So all strata `B^0..B^k` are non-empty (for `R >= 1`) while the `D_j` cube sees only the near tower.
Torus hypothesis for the deep tower: `(5R+40) M ell^k <= N`, `M ell^k | N`.
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

def unionTower (S T : Tower L) : Tower L := ⟨fun i => S.Om i ∪ T.Om i⟩

theorem admissible_union {ell M R k : ℕ} {S T : Tower L} (hS : Admissible ell M R k S) (hT : Admissible ell M R k T) :
    Admissible ell M R k (unionTower S T) := by
  obtain ⟨n1, e1, d1, b1, c1, z1⟩ := hS
  obtain ⟨n2, e2, d2, b2, c2, z2⟩ := hT
  refine ⟨?_, ?_, d1, ?_, ?_, ?_⟩
  · intro j
    exact Set.union_subset_union (n1 j) (n2 j)
  · intro j hj
    show S.Om j ∪ T.Om j = ∅
    rw [e1 j hj, e2 j hj]; simp
  · intro j hj x hx y hxy
    rcases hx with hx | hx
    · exact Or.inl (b1 j hj x hx y hxy)
    · exact Or.inr (b2 j hj x hx y hxy)
  · intro j hj x hx y hy
    have hx1 : x ∉ S.Om j := fun h => hx (Or.inl h)
    have hx2 : x ∉ T.Om j := fun h => hx (Or.inr h)
    rcases hy with hy | hy
    · exact c1 j hj x hx1 y hy
    · exact c2 j hj x hx2 y hy
  · intro x
    constructor
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, z, hz, hd⟩ := (z1 x).1 hx
        exact ⟨y, Or.inl hy, z, hz, hd⟩
      · obtain ⟨y, hy, z, hz, hd⟩ := (z2 x).1 hx
        exact ⟨y, Or.inr hy, z, hz, hd⟩
    · rintro ⟨y, hy, z, hz, hd⟩
      rcases hy with hy | hy
      · exact Or.inl ((z1 x).2 ⟨y, hy, z, hz, hd⟩)
      · exact Or.inr ((z2 x).2 ⟨y, hy, z, hz, hd⟩)

/-- the full-depth tower. -/
def deepT (ell M R j k : ℕ) : Tower L := unionTower (loneT ell M R j) (loneQ ell M R k (3 * R + 30))

theorem deepT_Om (ell M R j k i : ℕ) :
    (deepT (L := L) ell M R j k).Om i = (loneT (L := L) ell M R j).Om i ∪ (loneQ (L := L) ell M R k (3 * R + 30)).Om i := rfl

theorem deep_admissible {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hdiv : ∀ μ : Fin 3, bigSide M ell k ∣ Lf μ + 1) : Admissible ell M R k (deepT (L := Lf) ell M R j k) :=
  admissible_union (loneT_admissible hj hjk hdiv)
    (lone_admissible (by omega) le_rfl (loneBlock_closed _ _) hdiv)

/-- the far tower lies to the right: coordinate 0 at least `(2R+30) g_k`. -/
theorem far_lower {ell M R k : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    ∀ i, i ≤ k → ∀ x ∈ (loneQ (L := Lf) ell M R k (3 * R + 30)).Om i, (2 * R + 30) * bigSide M ell k ≤ (x 0).val := by
  intro i hi x hx
  have e1 : (3 * R + 30 + 1) * bigSide M ell k + 2 * (R * bigSide M ell k) = (5 * R + 31) * bigSide M ell k := by ring
  have e2 : (5 * R + 40) * bigSide M ell k = (5 * R + 31) * bigSide M ell k + 9 * bigSide M ell k := by ring
  have hN : ∀ μ : Fin 3, (3 * R + 30 + 1) * bigSide M ell k + 2 * (R * bigSide M ell k) ≤ Lf μ + 1 := fun μ => by
    have := hbig μ; omega
  have hout := (lone_outer (R := R) (q := 3 * R + 30) hell hM (by omega) hN i hi x hx).1
  have hT : R * Tsum ell M k i ≤ R * bigSide M ell k := Nat.mul_le_mul_left R (Tsum_le ell M k i hell)
  have e3 : (3 * R + 30) * bigSide M ell k = (2 * R + 30) * bigSide M ell k + R * bigSide M ell k := by ring
  omega

/-- the near tower lies to the left: coordinate 0 below `(2R+12) g_j`. -/
theorem near_upper {ell M R j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1) :
    ∀ i, i ≤ j → ∀ x ∈ (loneT (L := Lf) ell M R j).Om i, (x 0).val < (2 * R + 12) * bigSide M ell j := by
  intro i hi x hx
  have e1 : (R + 11 + 1) * bigSide M ell j + 2 * (R * bigSide M ell j) = (3 * R + 12) * bigSide M ell j := by ring
  have e2 : (3 * R + 30) * bigSide M ell j = (3 * R + 12) * bigSide M ell j + 18 * bigSide M ell j := by ring
  have hN : ∀ μ : Fin 3, (R + 11 + 1) * bigSide M ell j + 2 * (R * bigSide M ell j) ≤ Lf μ + 1 := fun μ => by
    have := hbig μ; omega
  have hout := (lone_outer (R := R) (q := R + 11) hell hM (by omega) hN i hi x hx).2
  have hT : R * Tsum ell M j i ≤ R * bigSide M ell j := Nat.mul_le_mul_left R (Tsum_le ell M j i hell)
  have e3 : (R + 11 + 1) * bigSide M ell j = (R + 12) * bigSide M ell j := by ring
  have e4 : (2 * R + 12) * bigSide M ell j = (R + 12) * bigSide M ell j + R * bigSide M ell j := by ring
  omega

theorem deep_dcube {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hjk : j ≤ k)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    IsDCube ell M k (deepT ell M R j k) j (loneC Lf ell M R j) := by
  have hell0 : 0 < ell := by omega
  have hgk : bigSide M ell j ≤ bigSide M ell k := bigSide_mono' hell0 hjk
  have hbigj : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1 := fun μ => by
    have := hbig μ
    have h1 : (3 * R + 30) * bigSide M ell j ≤ (5 * R + 40) * bigSide M ell k :=
      Nat.mul_le_mul (by omega) hgk
    omega
  obtain ⟨hjk', hgrid, x₀, ⟨hx0, hx0n⟩, hx0c⟩ := loneT_dcube (R := R) hM hell0 hjk hbigj
  refine ⟨hjk', hgrid, x₀, ⟨Or.inl hx0, ?_⟩, hx0c⟩
  rw [deepT_Om]
  rintro (h | h)
  · exact hx0n h
  · -- far tower
    by_cases hjk1 : j + 1 ≤ k
    · have := far_lower (R := R) hell hM hbig (j + 1) hjk1 x₀ h
      have h2 := near_upper (R := R) hell hM hbigj j le_rfl x₀ hx0
      have hmul : (2 * R + 12) * bigSide M ell j ≤ (2 * R + 30) * bigSide M ell k :=
        Nat.mul_le_mul (by omega) hgk
      omega
    · rw [loneQ_Om_above ell M R k _ (j + 1) (by omega)] at h
      exact Set.notMem_empty _ h

theorem deep_near_not_in {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hjk : j ≤ k)
    (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    sitePt Lf ((R + 6) * bigSide M ell j) ∉ (deepT (L := Lf) ell M R j k).Om j := by
  have hell0 : 0 < ell := by omega
  have hgk : bigSide M ell j ≤ bigSide M ell k := bigSide_mono' hell0 hjk
  have hbigj : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1 := fun μ => by
    have := hbig μ
    have h1 : (3 * R + 30) * bigSide M ell j ≤ (5 * R + 40) * bigSide M ell k :=
      Nat.mul_le_mul (by omega) hgk
    omega
  rw [deepT_Om]
  rintro (h | h)
  · exact loneT_near_not_in hM hell0 hbigj h
  · have h1 := far_lower (R := R) hell hM hbig j hjk _ h
    have e3 : (R + 6) * bigSide M ell j = R * bigSide M ell j + 6 * bigSide M ell j := by ring
    have e4 : (3 * R + 30) * bigSide M ell j = 3 * (R * bigSide M ell j) + 30 * bigSide M ell j := by ring
    have hlt : (R + 6) * bigSide M ell j < Lf 0 + 1 := by have := hbigj 0; omega
    rw [sitePt_val _ 0 hlt] at h1
    have hmul : (R + 6) * bigSide M ell j ≤ (2 * R + 30) * bigSide M ell k := Nat.mul_le_mul (by omega) hgk
    have hpos : 0 < bigSide M ell j := bigSide_pos' hM hell0 j
    have e5 : (R + 6) * bigSide M ell j < (2 * R + 30) * bigSide M ell k := by
      have : (R + 6) * bigSide M ell j < (R + 7) * bigSide M ell j := by nlinarith
      have h8 : (R + 7) * bigSide M ell j ≤ (2 * R + 30) * bigSide M ell k := Nat.mul_le_mul (by omega) hgk
      omega
    omega

/-- all strata `B^0 .. B^k` of the deep tower are non-empty (`R >= 1`). -/
theorem deep_strata {ell M R k j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (hjk : j ≤ k) (hbig : ∀ μ : Fin 3, (5 * R + 40) * bigSide M ell k ≤ Lf μ + 1) :
    ∀ i, i ≤ k → ∃ q, q ∈ towerBj (deepT (L := Lf) ell M R j k) i := by
  have hell0 : 0 < ell := by omega
  have hgk : bigSide M ell j ≤ bigSide M ell k := bigSide_mono' hell0 hjk
  have hbigj : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1 := fun μ => by
    have := hbig μ
    have h1 : (3 * R + 30) * bigSide M ell j ≤ (5 * R + 40) * bigSide M ell k :=
      Nat.mul_le_mul (by omega) hgk
    omega
  have e1 : (3 * R + 30 + 1) * bigSide M ell k + 2 * (R * bigSide M ell k) = (5 * R + 31) * bigSide M ell k := by ring
  have e2 : (5 * R + 40) * bigSide M ell k = (5 * R + 31) * bigSide M ell k + 9 * bigSide M ell k := by ring
  have hNf : ∀ μ : Fin 3, (3 * R + 30 + 1) * bigSide M ell k + 2 * (R * bigSide M ell k) ≤ Lf μ + 1 := fun μ => by
    have := hbig μ; omega
  have e1' : (R + 11 + 1) * bigSide M ell j + 2 * (R * bigSide M ell j) = (3 * R + 12) * bigSide M ell j := by ring
  have e2' : (3 * R + 30) * bigSide M ell j = (3 * R + 12) * bigSide M ell j + 18 * bigSide M ell j := by ring
  have hNn : ∀ μ : Fin 3, (R + 11 + 1) * bigSide M ell j + 2 * (R * bigSide M ell j) ≤ Lf μ + 1 := fun μ => by
    have := hbigj μ; omega
  intro i hi
  by_cases hij : i ≤ j
  · -- near witness
    have hw := lone_strata_gen (q := R + 11) hell hM hR (by omega) hNn i hij
    refine ⟨pt3 Lf ((R + 11) * bigSide M ell j - R * Tsum ell M j i) ((R + 11) * bigSide M ell j) ((R + 11) * bigSide M ell j), ?_, ?_⟩
    · rw [deepT_Om]; exact Or.inl hw.1
    · rw [deepT_Om]
      rintro (h | h)
      · exact hw.2 h
      · by_cases hik : i + 1 ≤ k
        · have h1 := far_lower (R := R) hell hM hbig (i + 1) hik _ h
          have hl0 : (R + 11) * bigSide M ell j - R * Tsum ell M j i < Lf 0 + 1 := by
            have := hbigj 0
            have e3 : (R + 11) * bigSide M ell j = R * bigSide M ell j + 11 * bigSide M ell j := by ring
            have e4 : (3 * R + 30) * bigSide M ell j = 3 * (R * bigSide M ell j) + 30 * bigSide M ell j := by ring
            omega
          rw [pt3_val0 (L := Lf) _ _ _ hl0] at h1
          have hmul : (R + 12) * bigSide M ell j ≤ (2 * R + 30) * bigSide M ell k := Nat.mul_le_mul (by omega) hgk
          have e3 : (R + 11) * bigSide M ell j + bigSide M ell j = (R + 12) * bigSide M ell j := by ring
          have hpos : 0 < bigSide M ell j := bigSide_pos' hM hell0 j
          omega
        · rw [loneQ_Om_above ell M R k _ (i + 1) (by omega)] at h
          exact Set.notMem_empty _ h
  · -- far witness
    have hw := lone_strata_gen (m := k) (q := 3 * R + 30) hell hM hR (by omega) hNf i hi
    refine ⟨pt3 Lf ((3 * R + 30) * bigSide M ell k - R * Tsum ell M k i) ((3 * R + 30) * bigSide M ell k) ((3 * R + 30) * bigSide M ell k), ?_, ?_⟩
    · rw [deepT_Om]; exact Or.inr hw.1
    · rw [deepT_Om]
      rintro (h | h)
      · rw [loneT_Om_above ell M R j (i + 1) (by omega)] at h
        exact Set.notMem_empty _ h
      · exact hw.2 h

end AdalyFormal.P409S

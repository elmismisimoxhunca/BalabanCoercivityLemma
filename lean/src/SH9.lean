import SH8

/-!
# SH9 -- every stratum `B^i`, `0 <= i <= j`, of the lone-block tower is non-empty (for `R >= 1`).

Outer bound: `Omega_i subset {x | LO i <= x_0 < HI i}` with `LO i = (R+11) g - R T_i`, `HI i = (R+12) g + R T_i`, `T_i = sum_{t in [i,j)} M ell^t <= g`.
Inner witness: the site with coordinates `(LO i, (R+11) g, (R+11) g)` lies in `Omega_i` but (as `LO (i+1) = LO i + R M ell^i > LO i`) not in `Omega_{i+1}`.
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
open AdalyFormal.P409L (collarSum collarSum_zero_lt)
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- `T_i = sum_{t in [i,j)} M ell^t`. -/
def Tsum (ell M j i : ℕ) : ℕ := ∑ t ∈ Finset.Ico i j, bigSide M ell t

theorem Tsum_succ (ell M j i : ℕ) (h : i < j) : Tsum ell M j i = bigSide M ell i + Tsum ell M j (i + 1) := by
  unfold Tsum
  exact Finset.sum_eq_sum_Ico_succ_bot h _

theorem Tsum_top (ell M j : ℕ) : Tsum ell M j j = 0 := by simp [Tsum]

theorem Tsum_dvd (ell M j i : ℕ) : bigSide M ell i ∣ Tsum ell M j i := by
  unfold Tsum
  refine Finset.dvd_sum (fun t ht => ?_)
  exact bigSide_dvd' M ell (Finset.mem_Ico.1 ht).1

theorem Tsum_le (ell M j i : ℕ) (hell : 2 ≤ ell) : Tsum ell M j i ≤ bigSide M ell j := by
  have h1 : Tsum ell M j i ≤ Tsum ell M j 0 := by
    unfold Tsum
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left (Nat.zero_le i))
  have h2 : Tsum ell M j 0 = M * collarSum ell 0 j := by
    unfold Tsum collarSum bigSide
    rw [Finset.mul_sum]
  have h3 := collarSum_zero_lt hell j
  have h4 : M * collarSum ell 0 j ≤ M * ell ^ j := Nat.mul_le_mul_left M (by omega)
  unfold bigSide
  omega

theorem pcd_ext (N y z s lo hi : ℕ) (hy : lo ≤ y ∧ y < hi) (hz : z < N) (h : pcd N z y ≤ s) (hlo : s ≤ lo)
    (hhi : hi + s ≤ N) : lo - s ≤ z ∧ z < hi + s := by
  unfold pcd at h
  split_ifs at h <;> omega

theorem blk_transfer (gi lo hi z x : ℕ) (hg : 0 < gi) (hlo : gi ∣ lo) (hhi : gi ∣ hi) (h : x / gi = z / gi)
    (hz : lo ≤ z ∧ z < hi) : lo ≤ x ∧ x < hi := by
  obtain ⟨a, ha⟩ := hlo
  obtain ⟨b, hb⟩ := hhi
  have h1 : a ≤ z / gi := (Nat.le_div_iff_mul_le hg).2 (by rw [ha] at hz; linarith [hz.1])
  have h2 : z / gi < b := (Nat.div_lt_iff_lt_mul hg).2 (by rw [hb] at hz; linarith [hz.2])
  have h3 := Nat.div_add_mod x gi
  have h4 := Nat.mod_lt x hg
  rw [h] at h3
  have m1 : gi * a ≤ gi * (z / gi) := Nat.mul_le_mul_left gi h1
  have m2 : gi * (z / gi + 1) ≤ gi * b := Nat.mul_le_mul_left gi h2
  have e : gi * (z / gi + 1) = gi * (z / gi) + gi := by ring
  constructor
  · rw [ha]; omega
  · rw [hb]; omega

theorem loneT_Om_lt (ell M R j i : ℕ) (hlt : i < j) :
    (loneT (L := L) ell M R j).Om i =
      nbhdOp (bigSide M ell i) (R * bigSide M ell i) ((loneT (L := L) ell M R j).Om (i + 1)) :=
  loneOm_below ell M R j _ hlt

theorem pdist_pt3_axis0 (a a' b c : ℕ) (ha : a < L 0 + 1) (ha' : a' < L 0 + 1) (hb : b < L 1 + 1) (hc : c < L 2 + 1) :
    pdist (pt3 L a b c) (pt3 L a' b c) = pcd (L 0 + 1) a a' := by
  unfold pdist
  rw [Fin.sum_univ_three]
  show pcd (L 0 + 1) ((pt3 L a b c) 0).val ((pt3 L a' b c) 0).val + pcd (L 1 + 1) ((pt3 L a b c) 1).val ((pt3 L a' b c) 1).val +
    pcd (L 2 + 1) ((pt3 L a b c) 2).val ((pt3 L a' b c) 2).val = _
  rw [pt3_val0 _ _ _ ha, pt3_val0 _ _ _ ha', pt3_val1 _ _ _ hb, pt3_val1 _ _ _ hb, pt3_val2 _ _ _ hc, pt3_val2 _ _ _ hc]
  have h1 : pcd (L 1 + 1) b b = 0 := by unfold pcd; simp
  have h2 : pcd (L 2 + 1) c c = 0 := by unfold pcd; simp
  rw [h1, h2]; rfl

/-- the lone tower with the block at index `q` (any `q`); `loneT` is `q = R + 11`. -/
def loneQ (ell M R m q : ℕ) : Tower L := loneTower ell M R m (loneBlock (bigSide M ell m) q)

theorem loneT_eq_loneQ (ell M R j : ℕ) : (loneT (L := L) ell M R j) = loneQ ell M R j (R + 11) := rfl

theorem loneQ_Om_top (ell M R m q : ℕ) : (loneQ (L := L) ell M R m q).Om m = loneBlock (bigSide M ell m) q :=
  loneOm_top ell M R m _

theorem loneQ_Om_above (ell M R m q i : ℕ) (h : m < i) : (loneQ (L := L) ell M R m q).Om i = ∅ :=
  loneOm_above ell M R m _ h

theorem loneQ_Om_lt (ell M R m q i : ℕ) (hlt : i < m) :
    (loneQ (L := L) ell M R m q).Om i =
      nbhdOp (bigSide M ell i) (R * bigSide M ell i) ((loneQ (L := L) ell M R m q).Om (i + 1)) :=
  loneOm_below ell M R m _ hlt

/-- outer bound (coordinate 0): `Omega_i subset {q g - R T_i <= x_0 < (q+1) g + R T_i}`. -/
theorem lone_outer {ell M R m q : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hRq : R ≤ q)
    (hN : ∀ μ : Fin 3, (q + 1) * bigSide M ell m + 2 * (R * bigSide M ell m) ≤ Lf μ + 1) :
    ∀ i, i ≤ m → ∀ x ∈ (loneQ (L := Lf) ell M R m q).Om i,
      q * bigSide M ell m - R * Tsum ell M m i ≤ (x 0).val ∧
        (x 0).val < (q + 1) * bigSide M ell m + R * Tsum ell M m i := by
  have hell0 : 0 < ell := by omega
  have hgpos : 0 < bigSide M ell m := bigSide_pos' hM hell0 m
  set g := bigSide M ell m with hg
  have hT : ∀ i, R * Tsum ell M m i ≤ R * g := fun i => Nat.mul_le_mul_left R (Tsum_le ell M m i hell)
  have hq1 : R * g ≤ q * g := Nat.mul_le_mul_right g hRq
  have e1 : (q + 1) * g = q * g + g := by ring
  intro i
  induction' hd : m - i with d ih generalizing i
  · intro hij x hx
    have hij' : i = m := by omega
    subst hij'
    rw [loneQ_Om_top] at hx
    rw [Tsum_top]
    have := blk_bounds q g (x 0).val hgpos (hx 0)
    have e5 : g * q = q * g := by ring
    omega
  · intro hij x hx
    have hlt : i < m := by omega
    rw [loneQ_Om_lt ell M R m q i hlt] at hx
    obtain ⟨y, hy, z, hz, hdist⟩ := hx
    obtain ⟨hy1, hy2⟩ := ih (i + 1) (by omega) (by omega) y hy
    have hTs := Tsum_succ ell M m i hlt
    have hTi := hT (i + 1)
    have hTi' := hT i
    have hgi : bigSide M ell i ≤ bigSide M ell m := bigSide_mono' hell0 hlt.le
    have hcoord : pcd (Lf 0 + 1) (z 0).val (y 0).val ≤ R * bigSide M ell i :=
      le_trans (pcd_le_pdist_coord z y 0) hdist
    have hRg : R * bigSide M ell i ≤ R * g := Nat.mul_le_mul_left R hgi
    have hRT : R * Tsum ell M m i = R * bigSide M ell i + R * Tsum ell M m (i + 1) := by rw [hTs]; ring
    have hN0 := hN 0
    have hext := pcd_ext (Lf 0 + 1) (y 0).val (z 0).val (R * bigSide M ell i)
      (q * g - R * Tsum ell M m (i + 1)) ((q + 1) * g + R * Tsum ell M m (i + 1)) ⟨hy1, hy2⟩ (z 0).isLt hcoord
      (by omega) (by omega)
    have hd1 : bigSide M ell i ∣ q * g - R * Tsum ell M m i :=
      Nat.dvd_sub (Dvd.dvd.mul_left (bigSide_dvd' M ell hlt.le) _) (Dvd.dvd.mul_left (Tsum_dvd ell M m i) _)
    have hd2 : bigSide M ell i ∣ (q + 1) * g + R * Tsum ell M m i :=
      dvd_add (Dvd.dvd.mul_left (bigSide_dvd' M ell hlt.le) _) (Dvd.dvd.mul_left (Tsum_dvd ell M m i) _)
    have hbl : (x 0).val / bigSide M ell i = (z 0).val / bigSide M ell i := (hz 0).symm
    refine blk_transfer (bigSide M ell i) _ _ (z 0).val (x 0).val (bigSide_pos' hM hell0 i) hd1 hd2 hbl ⟨?_, ?_⟩
    · have := hext.1
      omega
    · have := hext.2
      omega

/-- inner witness: the site `(q g - R T_i, q g, q g)` lies in `Omega_i`. -/
theorem lone_inner {ell M R m q : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hRq : R ≤ q)
    (hN : ∀ μ : Fin 3, (q + 1) * bigSide M ell m + 2 * (R * bigSide M ell m) ≤ Lf μ + 1) :
    ∀ i, i ≤ m → pt3 Lf (q * bigSide M ell m - R * Tsum ell M m i) (q * bigSide M ell m) (q * bigSide M ell m) ∈
      (loneQ (L := Lf) ell M R m q).Om i := by
  have hell0 : 0 < ell := by omega
  have hgpos : 0 < bigSide M ell m := bigSide_pos' hM hell0 m
  set g := bigSide M ell m with hg
  have hT : ∀ i, R * Tsum ell M m i ≤ R * g := fun i => Nat.mul_le_mul_left R (Tsum_le ell M m i hell)
  have hq1 : R * g ≤ q * g := Nat.mul_le_mul_right g hRq
  have e1 : (q + 1) * g = q * g + g := by ring
  intro i
  induction' hd : m - i with d ih generalizing i
  · intro hij
    have hij' : i = m := by omega
    subst hij'
    rw [loneQ_Om_top, Tsum_top]
    intro μ
    have h0 : q * g - R * 0 < Lf 0 + 1 := by have := hN 0; omega
    have h1 : q * g < Lf 1 + 1 := by have := hN 1; omega
    have h2 : q * g < Lf 2 + 1 := by have := hN 2; omega
    have e5 : g * q = q * g := by ring
    fin_cases μ
    · show ((pt3 Lf (q * g - R * 0) (q * g) (q * g)) 0).val / g = q
      rw [pt3_val0 _ _ _ h0]
      have := Nat.mul_div_cancel q hgpos
      simpa using this
    · show ((pt3 Lf (q * g - R * 0) (q * g) (q * g)) 1).val / g = q
      rw [pt3_val1 _ _ _ h1]
      exact Nat.mul_div_cancel _ hgpos
    · show ((pt3 Lf (q * g - R * 0) (q * g) (q * g)) 2).val / g = q
      rw [pt3_val2 _ _ _ h2]
      exact Nat.mul_div_cancel _ hgpos
  · intro hij
    have hlt : i < m := by omega
    have hTs := Tsum_succ ell M m i hlt
    have hRT : R * Tsum ell M m i = R * bigSide M ell i + R * Tsum ell M m (i + 1) := by rw [hTs]; ring
    have hTi := hT i
    have hgi : bigSide M ell i ≤ bigSide M ell m := bigSide_mono' hell0 hlt.le
    have hRg : R * bigSide M ell i ≤ R * g := Nat.mul_le_mul_left R hgi
    have hprev := ih (i + 1) (by omega) (by omega)
    rw [loneQ_Om_lt ell M R m q i hlt]
    refine ⟨_, hprev, pt3 Lf (q * g - R * Tsum ell M m i) (q * g) (q * g), fun μ => rfl, ?_⟩
    have hl0 : q * g - R * Tsum ell M m i < Lf 0 + 1 := by have := hN 0; omega
    have hl0' : q * g - R * Tsum ell M m (i + 1) < Lf 0 + 1 := by have := hN 0; omega
    have h1 : q * g < Lf 1 + 1 := by have := hN 1; omega
    have h2 : q * g < Lf 2 + 1 := by have := hN 2; omega
    rw [pdist_pt3_axis0 _ _ _ _ hl0 hl0' h1 h2]
    unfold pcd
    split_ifs <;> omega

/-- every stratum `B^i`, `i <= m`, of the lone tower is non-empty (`R >= 1`): the witness has coordinate 0 equal to `q g - R T_i`. -/
theorem lone_strata_gen {ell M R m q : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R) (hRq : R ≤ q)
    (hN : ∀ μ : Fin 3, (q + 1) * bigSide M ell m + 2 * (R * bigSide M ell m) ≤ Lf μ + 1) :
    ∀ i, i ≤ m → pt3 Lf (q * bigSide M ell m - R * Tsum ell M m i) (q * bigSide M ell m) (q * bigSide M ell m) ∈
      towerBj (loneQ (L := Lf) ell M R m q) i := by
  have hell0 : 0 < ell := by omega
  intro i hi
  refine ⟨lone_inner hell hM hRq hN i hi, ?_⟩
  by_cases hij : i = m
  · subst hij
    rw [loneQ_Om_above ell M R i q (i + 1) (by omega)]
    exact Set.notMem_empty _
  · have hlt : i < m := by omega
    intro hmem
    have hout := lone_outer hell hM hRq hN (i + 1) (by omega) _ hmem
    have hTs := Tsum_succ ell M m i hlt
    have hRT : R * Tsum ell M m i = R * bigSide M ell i + R * Tsum ell M m (i + 1) := by rw [hTs]; ring
    have hgi : bigSide M ell i ≤ bigSide M ell m := bigSide_mono' hell0 hlt.le
    have hT : R * Tsum ell M m i ≤ R * bigSide M ell m := Nat.mul_le_mul_left R (Tsum_le ell M m i hell)
    have hq1 : R * bigSide M ell m ≤ q * bigSide M ell m := Nat.mul_le_mul_right _ hRq
    have hpos : 1 ≤ R * bigSide M ell i := by
      have := bigSide_pos' hM hell0 i
      nlinarith
    have hl0 : q * bigSide M ell m - R * Tsum ell M m i < Lf 0 + 1 := by have := hN 0; omega
    have hv := pt3_val0 (L := Lf) (q * bigSide M ell m - R * Tsum ell M m i) (q * bigSide M ell m) (q * bigSide M ell m) hl0
    have := hout.1
    rw [hv] at this
    omega

theorem lone_strata {ell M R j : ℕ} {Lf : PeriodicLatticeExtent} (hell : 2 ≤ ell) (hM : 0 < M) (hR : 1 ≤ R)
    (hbig : ∀ μ : Fin 3, (3 * R + 30) * bigSide M ell j ≤ Lf μ + 1) :
    ∀ i, i ≤ j → ∃ q, q ∈ towerBj (loneT (L := Lf) ell M R j) i := by
  intro i hi
  have e1 : (R + 11 + 1) * bigSide M ell j = R * bigSide M ell j + 12 * bigSide M ell j := by ring
  have e2 : (3 * R + 30) * bigSide M ell j = 3 * (R * bigSide M ell j) + 30 * bigSide M ell j := by ring
  have hN : ∀ μ : Fin 3, (R + 11 + 1) * bigSide M ell j + 2 * (R * bigSide M ell j) ≤ Lf μ + 1 := fun μ => by
    have := hbig μ
    omega
  exact ⟨_, lone_strata_gen (q := R + 11) hell hM hR (by omega) hN i hi⟩

end AdalyFormal.P409S

import Q409W2

/-!
# Q409W3 -- packaged statements.

1. `p409_setw_holds` : on the unit-torus scale-up `scaleUp ell k Lu`, for EVERY `k`, `Lu`, tower, patch (`kappa = 1`,
   centre stratum `j`, ball radius `5 * M * ell^j`): `IsClassSetW` with factor `10*ell + 1` contains `patch cap Omega_0`.
2. `degenerate_no_setw` : if the fine torus is one level-`k` block per direction (`L mu + 1 = bigSide M ell k`, i.e.
   `Lu mu + 1 = M`), the tower `Om j = univ (j <= k)` is admissible, has a patch, and NO set at all satisfies `IsClassSetW`
   (any factor): the hypothesis `M < Lu mu + 1` of (1) cannot be dropped.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409W

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.GeneralClass (IsClassSetW)
open AdalyFormal.M1 (strat IsPatch patch gsp)

theorem setw_contains {L : PeriodicLatticeExtent} {ell M R k c j : ℕ} {S : Tower L} {w : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hc : 4 ≤ c) (hR : (c + 3) * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hp : IsPatch ell M k 1 S j w) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassSetW ell M (2 * c * ell + 1) k S sites i ∧
      {y | y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0} ⊆ sites := by
  obtain ⟨i, hij, hdvd, hle, hsub, hmeet, htwo⟩ := setw_core hell hM hc hR hA hgt hp
  have hG : gsp ell M 1 j = bigSide M ell j := by simp [gsp]
  have hmem : ∀ y, y ∈ patch ell M 1 c j w ↔ pdist w y ≤ c * bigSide M ell j := by
    intro y; show pdist w y ≤ c * gsp ell M 1 j ↔ _; rw [hG]
  have hgpos : 0 < bigSide M ell i := bigSide_pos' hM (by omega) i
  obtain ⟨z, hz⟩ := box_site w (c * bigSide M ell j) ((2 * c * ell + 1) * bigSide M ell i) (by nlinarith)
  refine ⟨{y | y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0}, i, ⟨le_trans hij hp.1, ?_, ?_, ⟨z, ?_⟩, ?_⟩, subset_rfl⟩
  · intro y hy; exact hsub y hy.1 hy.2
  · obtain ⟨y, h1, h2, h3⟩ := hmeet
    exact ⟨y, ⟨h1, h2⟩, h3⟩
  · intro y hy; exact hz y ((hmem y).1 hy.1)
  · obtain ⟨a, b, ha, hb, μ, hμ⟩ := htwo
    exact ⟨a, ha, b, hb, μ, hμ⟩

/-- headline: the union-of-blocks reading holds for every admissible tower, at factor `10*ell + 1`. -/
theorem p409_setw_holds {ell M R k j : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hLu : ∀ μ : Fin 3, M < Lu μ + 1) (hR : 8 * ell ≤ R)
    {S : Tower (scaleUp ell k Lu)} (hA : Admissible ell M R k S)
    {w : PeriodicLatticeSite (scaleUp ell k Lu)} (hp : IsPatch ell M k 1 S j w) :
    ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (i : ℕ),
      IsClassSetW ell M (10 * ell + 1) k S sites i ∧
      {y | y ∈ patch ell M 1 5 j w ∧ y ∈ S.Om 0} ⊆ sites := by
  have hgt : ∀ μ : Fin 3, bigSide M ell k < scaleUp ell k Lu μ + 1 := by
    intro μ
    have h1 : 0 < ell ^ k := pow_pos (by omega) k
    have h2 : M * ell ^ k < (Lu μ + 1) * ell ^ k := Nat.mul_lt_mul_of_pos_right (hLu μ) h1
    have h3 : 0 < (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) h1
    show M * ell ^ k < (Lu μ + 1) * ell ^ k - 1 + 1
    omega
  have := setw_contains (c := 5) (j := j) hell hM (by norm_num) (by omega) hA hgt hp
  simpa using this

/-- the same, for an arbitrary torus `L` (side `L mu + 1`), radius `c`, factor `2*c*ell + 1`. -/
theorem p409_setw_holds_general {L : PeriodicLatticeExtent} {ell M R k c j : ℕ} {S : Tower L}
    {w : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hc : 4 ≤ c) (hR : (c + 3) * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hp : IsPatch ell M k 1 S j w) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassSetW ell M (2 * c * ell + 1) k S sites i ∧
      {y | y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0} ⊆ sites :=
  setw_contains hell hM hc hR hA hgt hp

/-- the tower with `Om j = univ` for `j <= k`. -/
def TUniv (L : PeriodicLatticeExtent) (k : ℕ) : Tower L :=
  ⟨fun j => if j ≤ k then Set.univ else ∅⟩

theorem TUniv_om_le {L : PeriodicLatticeExtent} {k j : ℕ} (h : j ≤ k) : (TUniv L k).Om j = Set.univ := by
  simp [TUniv, h]

theorem TUniv_om_gt {L : PeriodicLatticeExtent} {k j : ℕ} (h : k < j) : (TUniv L k).Om j = ∅ := by
  simp [TUniv, Nat.not_le.mpr h]

theorem degenerate_admissible {L : PeriodicLatticeExtent} {ell M k : ℕ} (R : ℕ) (hk : 1 ≤ k)
    (hL : ∀ μ : Fin 3, L μ + 1 = bigSide M ell k) : Admissible ell M R k (TUniv L k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h : j + 1 ≤ k
    · rw [TUniv_om_le (by omega)]; trivial
    · rw [TUniv_om_gt (by omega)] at hx; exact absurd hx (Set.notMem_empty _)
  · intro j hj; exact TUniv_om_gt hj
  · intro j hj μ
    rw [hL μ]
    unfold bigSide
    exact Nat.mul_dvd_mul_left M (pow_dvd_pow ell hj)
  · intro j hj x hx y _
    rw [TUniv_om_le hj]; trivial
  · intro j hj x hx
    rw [TUniv_om_le hj] at hx
    exact absurd trivial hx
  · intro x
    have h0 : (TUniv L k).Om 0 = Set.univ := TUniv_om_le (Nat.zero_le k)
    constructor
    · intro _
      refine ⟨x, ?_, x, fun _ => rfl, ?_⟩
      · rw [TUniv_om_le hk]; trivial
      · rw [pdist_self]; exact Nat.zero_le _
    · intro _; rw [h0]; trivial

theorem degenerate_patch {L : PeriodicLatticeExtent} {ell M k : ℕ} (R : ℕ) (hM : 0 < M) (hell : 2 ≤ ell) (hk : 1 ≤ k)
    (hL : ∀ μ : Fin 3, L μ + 1 = bigSide M ell k) :
    ∃ w : PeriodicLatticeSite L, IsPatch ell M k 1 (TUniv L k) k w := by
  have hA := degenerate_admissible (ell := ell) (M := M) R hk hL
  have hpos : 0 < M * ell ^ k := bigSide_pos' hM (by omega) k
  refine ⟨fun μ => ⟨0, Nat.succ_pos _⟩, le_refl _, fun μ => Nat.zero_mod _, fun μ => ⟨0, Nat.succ_pos _⟩, ?_, ?_, fun μ => rfl⟩
  · rw [TUniv_om_le (Nat.zero_le k)]; trivial
  · have := (AdalyFormal.M1.strat_eq_iff hA (le_refl k) (fun μ => ⟨0, Nat.succ_pos _⟩ : PeriodicLatticeSite L)).1
    refine (this ?_).2
    show _ ∈ (TUniv L k).Om k \ (TUniv L k).Om (k + 1)
    rw [TUniv_om_le (le_refl k), TUniv_om_gt (Nat.lt_succ_self k)]
    exact ⟨trivial, Set.notMem_empty _⟩

/-- degenerate torus (one level-`k` block per direction): NO set satisfies `IsClassSetW`, at any factor and index. -/
theorem degenerate_no_setw {L : PeriodicLatticeExtent} {ell M k : ℕ}
    (hL : ∀ μ : Fin 3, L μ + 1 = bigSide M ell k) (F : ℕ)
    (sites : Set (PeriodicLatticeSite L)) (i : ℕ) :
    ¬ IsClassSetW ell M F k (TUniv L k) sites i := by
  rintro ⟨hik, -, ⟨y, -, hyB⟩, -, a, -, b, -, μ, hμ⟩
  have hi : i = k := by
    by_contra hne
    have : (TUniv L k).Om (i + 1) = Set.univ := TUniv_om_le (by omega)
    exact hyB.2 (by rw [this]; trivial)
  subst hi
  have ha : (a μ).val / bigSide M ell i = 0 := Nat.div_eq_of_lt (by rw [← hL μ]; exact (a μ).isLt)
  have hb : (b μ).val / bigSide M ell i = 0 := Nat.div_eq_of_lt (by rw [← hL μ]; exact (b μ).isLt)
  exact hμ (ha.trans hb.symm)

end AdalyFormal.P409W

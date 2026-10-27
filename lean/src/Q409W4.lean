import Q409W3

/-!
# Q409W4 -- the same containment with the set a genuine UNION OF LEVEL-`i` BLOCKS (`BlockClosed (bigSide M ell i) sites`).

`setwB_contains`: for every admissible tower and patch (hypotheses as `setw_contains`) there are `sites`, `i` with
`IsClassSetW ell M (2*c*ell+1) k S sites i`, `BlockClosed (bigSide M ell i) sites`, and `patch cap Omega_0 subset sites`.
The set is the union of the level-`i` blocks meeting `patch cap Omega_0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409W

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.GeneralClass (IsClassSetW)
open AdalyFormal.M1 (strat IsPatch patch gsp)

variable {L : PeriodicLatticeExtent}

theorem bigSide_dvd' (M ell : ℕ) {i t : ℕ} (h : i ≤ t) : bigSide M ell i ∣ bigSide M ell t := by
  unfold bigSide
  exact Nat.mul_dvd_mul_left M (pow_dvd_pow ell h)

theorem om_cell {ell M R k : ℕ} {S : Tower L} (hA : Admissible ell M R k S) {i t : ℕ} (hit : i ≤ t)
    {x y : PeriodicLatticeSite L} (hx : x ∈ S.Om t)
    (hxy : ∀ μ : Fin 3, (y μ).val / bigSide M ell i = (x μ).val / bigSide M ell i) : y ∈ S.Om t := by
  by_cases htk : t ≤ k
  · obtain ⟨q, hq⟩ := bigSide_dvd' M ell hit
    refine hA.2.2.2.1 t htk x hx y (fun μ => ?_)
    have hi : 0 < bigSide M ell i ∨ bigSide M ell i = 0 := by omega
    rw [hq, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hxy μ]
  · rw [hA.2.1 t (by omega)] at hx
    exact absurd hx (Set.notMem_empty _)

theorem setwB_contains {ell M R k c j : ℕ} {S : Tower L} {w : PeriodicLatticeSite L}
    (hell : 2 ≤ ell) (hM : 0 < M) (hc : 4 ≤ c) (hR : (c + 3) * ell ≤ R)
    (hA : Admissible ell M R k S) (hgt : ∀ μ : Fin 3, bigSide M ell k < L μ + 1)
    (hp : IsPatch ell M k 1 S j w) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassSetW ell M (2 * c * ell + 1) k S sites i ∧
      BlockClosed (bigSide M ell i) sites ∧
      {y | y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0} ⊆ sites := by
  obtain ⟨i, hij, hdvd, hle, hsub, hmeet, htwo⟩ := setw_core hell hM hc hR hA hgt hp
  have hjk : j ≤ k := hp.1
  have hik : i ≤ k := le_trans hij hjk
  have hG : gsp ell M 1 j = bigSide M ell j := by simp [gsp]
  have hmem : ∀ y, y ∈ patch ell M 1 c j w ↔ pdist w y ≤ c * bigSide M ell j := by
    intro y; show pdist w y ≤ c * gsp ell M 1 j ↔ _; rw [hG]
  have hgpos : 0 < bigSide M ell i := bigSide_pos' hM (by omega) i
  have hgN : ∀ μ : Fin 3, bigSide M ell i ∣ L μ + 1 := hA.2.2.1 i hik
  have hgw : ∀ μ : Fin 3, bigSide M ell i ∣ (w μ).val := by
    intro μ
    have h1 : (w μ).val % gsp ell M 1 j = 0 := hp.2.1 μ
    rw [hG] at h1
    exact dvd_trans hdvd (Nat.dvd_of_mod_eq_zero h1)
  have hgr : bigSide M ell i ∣ c * bigSide M ell j := Dvd.dvd.mul_left hdvd c
  obtain ⟨z, hz⟩ := box_site_cell w (c * bigSide M ell j) (bigSide M ell i) hgpos hgN hgw hgr
  let sites : Set (PeriodicLatticeSite L) :=
    {x | ∃ y : PeriodicLatticeSite L, (y ∈ patch ell M 1 c j w ∧ y ∈ S.Om 0) ∧
      ∀ μ : Fin 3, (y μ).val / bigSide M ell i = (x μ).val / bigSide M ell i}
  have hself : ∀ y, y ∈ patch ell M 1 c j w → y ∈ S.Om 0 → y ∈ sites :=
    fun y h1 h2 => ⟨y, ⟨h1, h2⟩, fun _ => rfl⟩
  refine ⟨sites, i, ⟨hik, ?_, ?_, ⟨z, ?_⟩, ?_⟩, ?_, fun y hy => hself y hy.1 hy.2⟩
  · intro x ⟨y, ⟨hy1, hy0⟩, hxy⟩
    have hyb := hsub y hy1 hy0
    have hyi : y ∈ S.Om i ∧ y ∉ S.Om (i + 2) := by
      rcases hyb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, fun h3 => h2 (hA.1 (i + 1) h3)⟩
      · exact ⟨hA.1 i h1, h2⟩
    have hxy' : ∀ μ : Fin 3, (x μ).val / bigSide M ell i = (y μ).val / bigSide M ell i := fun μ => (hxy μ).symm
    have hxi : x ∈ S.Om i := om_cell hA (le_refl i) hyi.1 hxy'
    have hxn : x ∉ S.Om (i + 2) := fun h => hyi.2 (om_cell hA (show i ≤ i + 2 by omega) h hxy)
    by_cases hx1 : x ∈ S.Om (i + 1)
    · exact Or.inr ⟨hx1, hxn⟩
    · exact Or.inl ⟨hxi, hx1⟩
  · obtain ⟨y, h1, h2, h3⟩ := hmeet
    exact ⟨y, hself y h1 h2, h3⟩
  · intro x ⟨y, ⟨hy1, hy0⟩, hxy⟩
    have hb := hz y x ((hmem y).1 hy1) hxy
    intro μ
    refine lt_of_lt_of_le (hb μ) ?_
    nlinarith
  · obtain ⟨a, b, ha, hb, μ, hμ⟩ := htwo
    exact ⟨a, hself a ha.1 ha.2, b, hself b hb.1 hb.2, μ, hμ⟩
  · intro x ⟨y, hy, hxy⟩ y' hy'
    exact ⟨y, hy, fun μ => (hxy μ).trans (hy' μ).symm⟩

/-- headline, genuine union of level-`i` blocks, `l^1` ball radius `5 G_j`, factor `10 ell + 1`. -/
theorem p409_setwB_holds {ell M R k j : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 2 ≤ ell) (hM : 0 < M) (hLu : ∀ μ : Fin 3, M < Lu μ + 1) (hR : 8 * ell ≤ R)
    {S : Tower (scaleUp ell k Lu)} (hA : Admissible ell M R k S)
    {w : PeriodicLatticeSite (scaleUp ell k Lu)} (hp : IsPatch ell M k 1 S j w) :
    ∃ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (i : ℕ),
      IsClassSetW ell M (10 * ell + 1) k S sites i ∧ BlockClosed (bigSide M ell i) sites ∧
      {y | y ∈ patch ell M 1 5 j w ∧ y ∈ S.Om 0} ⊆ sites := by
  have hgt : ∀ μ : Fin 3, bigSide M ell k < scaleUp ell k Lu μ + 1 := by
    intro μ
    have h1 : 0 < ell ^ k := pow_pos (by omega) k
    have h2 : M * ell ^ k < (Lu μ + 1) * ell ^ k := Nat.mul_lt_mul_of_pos_right (hLu μ) h1
    have h3 : 0 < (Lu μ + 1) * ell ^ k := Nat.mul_pos (Nat.succ_pos _) h1
    show M * ell ^ k < (Lu μ + 1) * ell ^ k - 1 + 1
    omega
  have := setwB_contains (c := 5) (j := j) hell hM (by norm_num) (by omega) hA hgt hp
  simpa using this

end AdalyFormal.P409W

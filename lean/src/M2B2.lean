import M1B
import M1G3

/-!
# M2B2 -- B0 (`classCube_of_patch`) TESTED: a stratum-`j` patch that sees a stratum-`(j-1)` site lies in NO class cube
(m2_bridge_20261014, Layer B)

PLAN §2.2 B0 asks that every M1 patch (lane B G3: the `ℓ¹` ball `patch ell M κ c j w` of radius `c·κ·M·ell^j`, `c ≥ 5`) lie in a class cube.
* `strat_cases_of_mem` : every site of a class cube of index `i` has stratum `i` or `i+1`.
* `cube_index_forced` : a class cube containing a site of stratum `j-1` and a site of stratum `j` has index exactly `j-1`.
* `pcd_lt_of_offs`, `far_pair` : two sites of a periodic box of side `s` have coordinate-wise circular distance `< s`; on a torus of side
  `N ≥ 2r + s` with `s ≤ 2r` the points `w ∓ r e₀` do not.
* **`patch_inter_not_in_class_cube`** (sharpest form): the same with `patch ∩ Ω₀` in place of `patch`, given two patch sites `p₁, p₂ ∈ Ω₀` at coordinate-`σ`
  circular distance `≥ f·M·ell^(j-1)` (so the conclusion is about the part of the patch where `U` matters); `pdist_update` computes `pdist` for a one-coordinate change.
* **`patch_not_in_class_cube`** (whole ball; IMPLIED by the `∩ Ω₀` form, kept as the unconditional geometric core) : if the patch `(j,w)` (any `κ, c`) contains a site of stratum `j-1` and the anchor of stratum `j`, and
  `f·M·ell^(j-1) ≤ 2·c·κ·M·ell^j`, and the torus side `N₀ ≥ 2·c·κ·M·ell^j + f·M·ell^(j-1)`, then NO class cube (factor `f`, any index) contains
  the patch.  For `f = 12`, `κ = 1`, `c = 5`, `ell ≥ 2` the size hypothesis holds (`12 ≤ 10 ell`).  NO hypothesis on `R`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2Bridge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_triangle)
open AdalyFormal.M1 (strat strat_eq_iff strat_le IsPatch patch gsp IsPatch.anchor)

variable {L : PeriodicLatticeExtent}

/-- every site of a class cube of index `i` has stratum `i` or `i+1`. -/
theorem strat_cases_of_mem {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hq : IsClassCube ell M f k S sites i)
    {x : PeriodicLatticeSite L} (hx : x ∈ sites) : strat S k x = i ∨ strat S k x = i + 1 := by
  have hik : i ≤ k := hq.1.1
  rcases hq.1.2.2.1 hx with h | h
  · exact Or.inl (((strat_eq_iff hA hik x).mp h).2)
  · by_cases hk : i + 1 ≤ k
    · exact Or.inr (((strat_eq_iff hA hk x).mp h).2)
    · exfalso
      have : S.Om (i + 1) = ∅ := hA.2.1 (i + 1) (by omega)
      have h1 := h.1
      rw [this] at h1
      exact h1

/-- a class cube containing a stratum-`(j-1)` site and a stratum-`j` site has index `j-1`. -/
theorem cube_index_forced {ell M R f k : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i j : ℕ} (hq : IsClassCube ell M f k S sites i)
    {v x : PeriodicLatticeSite L} (hv : v ∈ sites) (hx : x ∈ sites) (hvj : strat S k v + 1 = j) (hxj : strat S k x = j) :
    i + 1 = j := by
  have h1 := strat_cases_of_mem hA hq hv
  have h2 := strat_cases_of_mem hA hq hx
  omega

theorem pcd_lt_of_offs (N a b z s : ℕ) (hN : 0 < N) (ha : a < N) (hb : b < N) (hz : z < N)
    (hoa : (a + N - z) % N < s) (hob : (b + N - z) % N < s) : pcd N a b < s := by
  have ea : (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
    split_ifs with h
    · have : a + N - z = (a - z) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have eb : (b + N - z) % N = if z ≤ b then b - z else b + N - z := by
    split_ifs with h
    · have : b + N - z = (b - z) + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  rw [ea] at hoa; rw [eb] at hob
  unfold pcd
  split_ifs at hoa hob ⊢ <;> omega

/-- two points of the circle `ℤ/N` at distance `r` on either side of `w`, at mutual distance `≥ s`. -/
theorem far_pair (N w r s : ℕ) (hw : w < N) (h1 : s ≤ 2 * r) (h2 : 2 * r + s ≤ N) :
    ∃ a b : ℕ, a < N ∧ b < N ∧ pcd N w a ≤ r ∧ pcd N w b ≤ r ∧ s ≤ pcd N a b := by
  by_cases hr : r ≤ w
  · by_cases hr2 : w + r < N
    · exact ⟨w - r, w + r, by omega, hr2, by unfold pcd; split_ifs <;> omega, by unfold pcd; split_ifs <;> omega,
        by unfold pcd; split_ifs <;> omega⟩
    · exact ⟨w - r, w + r - N, by omega, by omega, by unfold pcd; split_ifs <;> omega, by unfold pcd; split_ifs <;> omega,
        by unfold pcd; split_ifs <;> omega⟩
  · by_cases hr2 : w + r < N
    · exact ⟨w + N - r, w + r, by omega, hr2, by unfold pcd; split_ifs <;> omega, by unfold pcd; split_ifs <;> omega,
        by unfold pcd; split_ifs <;> omega⟩
    · exact ⟨w + N - r, w + r - N, by omega, by omega, by unfold pcd; split_ifs <;> omega, by unfold pcd; split_ifs <;> omega,
        by unfold pcd; split_ifs <;> omega⟩

theorem pcd_self' (N a : ℕ) : pcd N a a = 0 := by unfold pcd; simp

theorem pdist_update (w : PeriodicLatticeSite L) (σ : Fin 3) (c : ℕ) (hc : c < L σ + 1) :
    pdist w (Function.update w σ ⟨c, hc⟩) = pcd (L σ + 1) (w σ).val c := by
  unfold pdist
  rw [Finset.sum_eq_single σ]
  · simp
  · intro μ _ h
    rw [Function.update_of_ne h, pcd_self']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **no box of side `s` contains an `ℓ¹` ball of radius `r` with `s ≤ 2r`, on a torus with `N₀ ≥ 2r + s`.** -/
theorem ball_not_in_box (w z : PeriodicLatticeSite L) (r s : ℕ) (h1 : s ≤ 2 * r) (h2 : 2 * r + s ≤ L 0 + 1) :
    ¬ ({y | pdist w y ≤ r} ⊆ siteBox z s) := by
  intro hsub
  obtain ⟨a, b, ha, hb, hwa, hwb, hab⟩ := far_pair (L 0 + 1) (w 0).val r s (w 0).isLt h1 h2
  set pa : PeriodicLatticeSite L := Function.update w 0 ⟨a, ha⟩ with hpa
  set pb : PeriodicLatticeSite L := Function.update w 0 ⟨b, hb⟩ with hpb
  have hd : ∀ (c : ℕ) (hc : c < L 0 + 1), pcd (L 0 + 1) (w 0).val c ≤ r →
      pdist w (Function.update w 0 ⟨c, hc⟩) ≤ r := by
    intro c hc hcr
    unfold pdist
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · simpa using hcr
    · intro μ _ h
      rw [Function.update_of_ne h, pcd_self']
    · intro h; exact absurd (Finset.mem_univ _) h
  have hma : pa ∈ siteBox z s := hsub (hd a ha hwa)
  have hmb : pb ∈ siteBox z s := hsub (hd b hb hwb)
  unfold siteBox at hma hmb
  simp only [Set.mem_setOf_eq] at hma hmb
  have := pcd_lt_of_offs (L 0 + 1) (pa 0).val (pb 0).val (z 0).val (s := s) (Nat.succ_pos _) (pa 0).isLt (pb 0).isLt
    (z 0).isLt (hma 0) (hmb 0)
  simp only [hpa, hpb, Function.update_self] at this
  omega

/-- **B0 fails for the down-case patch.**  Hypotheses: the patch `(j,w)` of lane B's G3 contains a site `v` of stratum `j-1`
(it always contains an anchor `x₀` of stratum `j`), `f·M·ell^(j-1) ≤ 2·c·(κ·M·ell^j)` (e.g. `f = 12, c = 5, κ = 1, ell ≥ 2`),
and the torus is wide enough in direction `0`.  Conclusion: NO class cube (any index `i`) contains the patch. -/
theorem patch_not_in_class_cube {ell M R k κ c f j : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell) (hc3 : 3 ≤ c) {w : PeriodicLatticeSite L}
    (hp : IsPatch ell M k κ S j w) {v : PeriodicLatticeSite L} (hv : v ∈ patch ell M κ c j w) (hvj : strat S k v + 1 = j)
    (hf : f * bigSide M ell (j - 1) ≤ 2 * (c * gsp ell M κ j))
    (hN : 2 * (c * gsp ell M κ j) + f * bigSide M ell (j - 1) ≤ L 0 + 1) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M f k S sites i ∧ patch ell M κ c j w ⊆ sites := by
  rintro ⟨sites, i, hq, hsub⟩
  obtain ⟨x₀, -, hxs, hd0⟩ := hp.anchor hκ hM hell
  have hx0 : x₀ ∈ patch ell M κ c j w := by
    show pdist w x₀ ≤ c * gsp ell M κ j
    rw [pdist_comm]
    have : 3 * gsp ell M κ j ≤ c * gsp ell M κ j := Nat.mul_le_mul_right _ hc3
    omega
  have hidx := cube_index_forced hA hq (hsub hv) (hsub hx0) hvj hxs
  have hi : i = j - 1 := by omega
  obtain ⟨z, -, hz⟩ := hq.1.2.1
  rw [hz, hi] at hsub
  exact ball_not_in_box w z (c * gsp ell M κ j) (f * bigSide M ell (j - 1)) hf hN hsub


/-- **B0 fails for the down-case patch, in its sharpest form: even the part of the patch inside `Ω₀` lies in no class cube.**
Extra hypotheses over `patch_not_in_class_cube`: two sites `p₁, p₂` of the patch, both in `Ω₀`, whose coordinate-`σ` circular distance is `≥ f·M·ell^(j-1)`
(the side of the only possible cube), and `v` (stratum `j-1`) also in `Ω₀`. -/
theorem patch_inter_not_in_class_cube {ell M R k κ c f j : ℕ} {S : Tower L} (hA : Admissible ell M R k S)
    (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell) (hc3 : 3 ≤ c) {w : PeriodicLatticeSite L}
    (hp : IsPatch ell M k κ S j w) {v : PeriodicLatticeSite L} (hv : v ∈ patch ell M κ c j w) (hv0 : v ∈ S.Om 0)
    (hvj : strat S k v + 1 = j) {p1 p2 : PeriodicLatticeSite L} (hp1 : p1 ∈ patch ell M κ c j w) (hp10 : p1 ∈ S.Om 0)
    (hp2 : p2 ∈ patch ell M κ c j w) (hp20 : p2 ∈ S.Om 0) (σ : Fin 3)
    (hfar : f * bigSide M ell (j - 1) ≤ pcd (L σ + 1) (p1 σ).val (p2 σ).val) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M f k S sites i ∧
        {y | y ∈ patch ell M κ c j w ∧ y ∈ S.Om 0} ⊆ sites := by
  rintro ⟨sites, i, hq, hsub⟩
  obtain ⟨x₀, hx0j, hxs, hd0⟩ := hp.anchor hκ hM hell
  have hx0 : x₀ ∈ patch ell M κ c j w := by
    show pdist w x₀ ≤ c * gsp ell M κ j
    rw [pdist_comm]
    have : 3 * gsp ell M κ j ≤ c * gsp ell M κ j := Nat.mul_le_mul_right _ hc3
    omega
  have hx00 : x₀ ∈ S.Om 0 := AdalyFormal.M1.om_anti hA (Nat.zero_le j) hx0j
  have hidx := cube_index_forced hA hq (hsub ⟨hv, hv0⟩) (hsub ⟨hx0, hx00⟩) hvj hxs
  have hi : i = j - 1 := by omega
  obtain ⟨z, -, hz⟩ := hq.1.2.1
  have m1 : p1 ∈ siteBox z (f * bigSide M ell (j - 1)) := by rw [← hi, ← hz]; exact hsub ⟨hp1, hp10⟩
  have m2 : p2 ∈ siteBox z (f * bigSide M ell (j - 1)) := by rw [← hi, ← hz]; exact hsub ⟨hp2, hp20⟩
  unfold siteBox at m1 m2
  simp only [Set.mem_setOf_eq] at m1 m2
  have := pcd_lt_of_offs (L σ + 1) (p1 σ).val (p2 σ).val (z σ).val (s := f * bigSide M ell (j - 1)) (Nat.succ_pos _)
    (p1 σ).isLt (p2 σ).isLt (z σ).isLt (m1 σ) (m2 σ)
  omega

end AdalyFormal.M2Bridge

#print axioms AdalyFormal.M2Bridge.cube_index_forced
#print axioms AdalyFormal.M2Bridge.far_pair
#print axioms AdalyFormal.M2Bridge.ball_not_in_box
#print axioms AdalyFormal.M2Bridge.patch_not_in_class_cube
#print axioms AdalyFormal.M2Bridge.patch_inter_not_in_class_cube

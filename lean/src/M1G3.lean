import M1A

/-!
# M1G3 -- G3 `patch_cover`: stratum-adapted patches on a COARSE grid; at most two strata per patch; every bond in a core;
multiplicity bounded independently of `k` AND of the patch scale `κ`  (M1 lane B, 2026-10-13)

Level-`j` coarse spacing `G_j = κ M ell^j` (`gsp`).  Patch index `(j, w)`: `j ≤ k`, `w` a corner of the `G_j`-grid whose `G_j`-cell
contains a site `x₀ ∈ Ω₀` of stratum `j` (`IsPatch`).  Patch = `ℓ¹` ball `{y | |w - y| ≤ c G_j}` (`patch`), core = `{y | |w - y| ≤ 4 G_j}`
(`pcore`); `c` is a fixed ratio (`c ≥ 5` for the bumps of `M1G4`).
* `patch_strat_bounds`: if `(c+3) κ ell ≤ R`, the strata in the patch lie in `[j-1, j+1]`.
* `patch_two_strata` (with `2 (c+3) κ ≤ R`): any two sites of a patch have strata differing by at most one; `patch_strata_pair`: there is
  `i` with every stratum in the patch equal to `i` or `i+1`.
* `patch_cover`: every `x ∈ Ω₀` and `x + e_μ` lie in the core of ONE patch.  No hypothesis on `R`.
* `card_grid_near1` (1D: at most `3(2c+1)` multiples of `G` within circular distance `c G`; NO divisibility of the torus side by `G`),
  `card_grid_near` (3D: `(3(2c+1))^3`), `patch_mult`: every site lies in at most `3 (3(2c+1))^3` patches -- free of `k` and of `κ`.
The earlier fine-grid version (centres on the `M ell^j` grid; multiplicity `3(2κ+1)^3`, growing with `κ`) is kept in
`superseded/M1G3fine.lean` (compiled in the clean builds as a leaf, imported by nothing): a growing multiplicity makes the IMS remainder `Σ_p |∇h_p|²` NOT small in `κ`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8 (pdist_comm pdist_shift_le pdist_triangle pcd_le_diff pdist_self)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

variable {L : PeriodicLatticeExtent}

open Classical

/-- coarse spacing at level `j`: `κ M ell^j`. -/
def gsp (ell M κ j : ℕ) : ℕ := κ * bigSide M ell j

theorem bigSide_succ (M ell j : ℕ) : bigSide M ell (j + 1) = bigSide M ell j * ell := by
  unfold bigSide; rw [pow_succ]; ring

theorem gsp_pos {ell M κ : ℕ} (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell) (j : ℕ) : 0 < gsp ell M κ j :=
  Nat.mul_pos hκ (Nat.mul_pos hM (pow_pos hell j))

/-- the corner of the `g`-cell of `x`. -/
def cellCorner (g : ℕ) (x : PeriodicLatticeSite L) : PeriodicLatticeSite L :=
  fun μ => ⟨(x μ).val / g * g, lt_of_le_of_lt (Nat.div_mul_le_self _ _) (x μ).isLt⟩

theorem cellCorner_div {g : ℕ} (hg : 0 < g) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((cellCorner g x) μ).val / g = (x μ).val / g := by
  show (x μ).val / g * g / g = _
  exact Nat.mul_div_cancel _ hg

theorem pdist_cellCorner_le {g : ℕ} (hg : 0 < g) (x : PeriodicLatticeSite L) :
    pdist (cellCorner g x) x ≤ 3 * (g - 1) := by
  unfold pdist
  have h : ∀ μ : Fin 3, pcd (L μ + 1) ((cellCorner g x) μ).val (x μ).val ≤ g - 1 := by
    intro μ
    have hle : ((cellCorner g x) μ).val ≤ (x μ).val := Nat.div_mul_le_self _ _
    refine le_trans (pcd_le_diff _ _ _ hle) ?_
    show (x μ).val - (x μ).val / g * g ≤ g - 1
    have h1 := Nat.mod_add_div (x μ).val g
    have h2 := Nat.mod_lt (x μ).val hg
    rw [Nat.mul_comm g] at h1
    omega
  rw [Fin.sum_univ_three]
  have := h 0; have := h 1; have := h 2
  omega

/-- a grid corner in the cell of `x` IS the cell corner of `x`. -/
theorem eq_cellCorner {g : ℕ} {w x : PeriodicLatticeSite L} (hw : GridCorner g w)
    (hq : ∀ μ, (x μ).val / g = (w μ).val / g) : w = cellCorner g x := by
  funext μ
  apply Fin.ext
  show (w μ).val = (x μ).val / g * g
  rw [hq μ]
  have := Nat.div_add_mod (w μ).val g
  rw [hw μ] at this
  rw [Nat.mul_comm]; omega

/-- patch index `(j, w)`. -/
def IsPatch (ell M k κ : ℕ) (S : Tower L) (j : ℕ) (w : PeriodicLatticeSite L) : Prop :=
  j ≤ k ∧ GridCorner (gsp ell M κ j) w ∧
    ∃ x₀ : PeriodicLatticeSite L, x₀ ∈ S.Om 0 ∧ strat S k x₀ = j ∧
      ∀ μ, (x₀ μ).val / gsp ell M κ j = (w μ).val / gsp ell M κ j

/-- the patch: `ℓ¹` ball of radius `c G_j`. -/
def patch (ell M κ c j : ℕ) (w : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  {y | pdist w y ≤ c * gsp ell M κ j}

/-- the core: `ℓ¹` ball of radius `4 G_j`. -/
def pcore (ell M κ j : ℕ) (w : PeriodicLatticeSite L) : Set (PeriodicLatticeSite L) :=
  {y | pdist w y ≤ 4 * gsp ell M κ j}

theorem pcore_sub_patch {ell M κ c j : ℕ} (hc : 4 ≤ c) (w : PeriodicLatticeSite L) :
    pcore ell M κ j w ⊆ patch ell M κ c j w :=
  fun _ hy => le_trans hy (Nat.mul_le_mul_right _ hc)

/-- the anchor of a patch: a stratum-`j` site of `Ω₀` within `3 G_j` of the corner. -/
theorem IsPatch.anchor {ell M k κ : ℕ} {S : Tower L} {j : ℕ} {w : PeriodicLatticeSite L} (hκ : 0 < κ) (hM : 0 < M)
    (hell : 0 < ell) (hp : IsPatch ell M k κ S j w) :
    ∃ x₀ : PeriodicLatticeSite L, x₀ ∈ S.Om j ∧ strat S k x₀ = j ∧ pdist x₀ w ≤ 3 * gsp ell M κ j := by
  obtain ⟨-, hgrid, x₀, hx0, hs, hq⟩ := hp
  have hg := gsp_pos hκ hM hell (ell := ell) j
  refine ⟨x₀, ?_, hs, ?_⟩
  · have := mem_strat_of_mem0 (k := k) hx0; rwa [hs] at this
  · rw [eq_cellCorner hgrid hq, pdist_comm]
    have := pdist_cellCorner_le hg x₀
    omega

/-- **strata in a patch lie in `[j-1, j+1]`** (`(c+3) κ ell ≤ R`). -/
theorem patch_strat_bounds {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR : (c + 3) * κ * ell ≤ R) {j : ℕ} {w : PeriodicLatticeSite L} (hp : IsPatch ell M k κ S j w)
    {y : PeriodicLatticeSite L} (hy : y ∈ patch ell M κ c j w) : j ≤ strat S k y + 1 ∧ strat S k y ≤ j + 1 := by
  obtain ⟨x₀, hx0j, hs, hd0⟩ := hp.anchor hκ hM hell
  have hy' : pdist w y ≤ c * gsp ell M κ j := hy
  have hd : pdist x₀ y ≤ (c + 3) * κ * bigSide M ell j := by
    have := pdist_triangle x₀ w y
    unfold gsp at hd0 hy'
    have e : (c + 3) * κ * bigSide M ell j = 3 * (κ * bigSide M ell j) + c * (κ * bigSide M ell j) := by ring
    omega
  constructor
  · rcases Nat.eq_zero_or_pos j with h0 | hj
    · omega
    · have hmem : y ∈ S.Om (j - 1) := by
        by_contra hn
        have hz : x₀ ∈ S.Om (j - 1 + 1) := by rw [Nat.sub_add_cancel hj]; exact hx0j
        have hc := collar hA (j := j - 1) (by have := hp.1; omega) hn hz
        rw [pdist_comm] at hc
        have hb : (c + 3) * κ * bigSide M ell j ≤ R * bigSide M ell (j - 1) := by
          have e : bigSide M ell j = bigSide M ell (j - 1) * ell := by
            rw [← bigSide_succ, Nat.sub_add_cancel hj]
          rw [e]
          calc (c + 3) * κ * (bigSide M ell (j - 1) * ell) = (c + 3) * κ * ell * bigSide M ell (j - 1) := by ring
            _ ≤ R * bigSide M ell (j - 1) := Nat.mul_le_mul_right _ hR
        omega
      have := le_strat_of_mem (k := k) (show j - 1 ≤ k by have := hp.1; omega) hmem
      omega
  · have hc : pdist x₀ y ≤ R * bigSide M ell (strat S k x₀ + 1) := by
      rw [hs, bigSide_succ]
      have hκR : (c + 3) * κ ≤ R * ell := by
        have h1 : (c + 3) * κ ≤ (c + 3) * κ * ell := Nat.le_mul_of_pos_right _ hell
        have h2 : R ≤ R * ell := Nat.le_mul_of_pos_right R hell
        omega
      calc pdist x₀ y ≤ (c + 3) * κ * bigSide M ell j := hd
        _ ≤ (R * ell) * bigSide M ell j := Nat.mul_le_mul_right _ hκR
        _ = R * (bigSide M ell j * ell) := by ring
    have := strat_close hA hc
    rw [hs] at this
    exact this

/-- **any two sites of a patch have strata differing by at most one** (`(c+3) κ ell ≤ R`, `2 (c+3) κ ≤ R`). -/
theorem patch_two_strata {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR1 : (c + 3) * κ * ell ≤ R) (hR2 : 2 * (c + 3) * κ ≤ R) {j : ℕ} {w : PeriodicLatticeSite L}
    (hp : IsPatch ell M k κ S j w) {y y' : PeriodicLatticeSite L} (hy : y ∈ patch ell M κ c j w)
    (hy' : y' ∈ patch ell M κ c j w) : strat S k y ≤ strat S k y' + 1 := by
  by_contra hlt
  push Not at hlt
  have b1 := patch_strat_bounds hA hκ hM hell hR1 hp hy
  have b2 := patch_strat_bounds hA hκ hM hell hR1 hp hy'
  have hyk := strat_le S k y
  have hjk : j + 1 ≤ k := by omega
  have hyin : y ∈ S.Om (j + 1) := (le_strat_iff hA (by omega) hjk y).mp (by omega)
  have hy'out : y' ∉ S.Om j := by
    intro h
    have := le_strat_of_mem (k := k) (by omega) h
    omega
  have hc := collar hA (j := j) (by omega) hy'out hyin
  have ht := pdist_triangle y' w y
  have hcm := pdist_comm y' w
  have h1 : pdist w y' ≤ c * gsp ell M κ j := hy'
  have h2 : pdist w y ≤ c * gsp ell M κ j := hy
  unfold gsp at h1 h2
  have h3 : 2 * (c + 3) * κ * bigSide M ell j ≤ R * bigSide M ell j := Nat.mul_le_mul_right _ hR2
  have e : 2 * (c + 3) * κ * bigSide M ell j = c * (κ * bigSide M ell j) + c * (κ * bigSide M ell j)
      + 6 * (κ * bigSide M ell j) := by ring
  omega

/-- **the patch meets at most two (consecutive) strata.** -/
theorem patch_strata_pair {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR1 : (c + 3) * κ * ell ≤ R) (hR2 : 2 * (c + 3) * κ ≤ R) {j : ℕ} {w : PeriodicLatticeSite L}
    (hp : IsPatch ell M k κ S j w) :
    ∃ i : ℕ, ∀ y ∈ patch ell M κ c j w, strat S k y = i ∨ strat S k y = i + 1 := by
  by_cases hw : ∃ v ∈ patch ell M κ c j w, strat S k v + 1 = j
  · obtain ⟨v, hv, hvj⟩ := hw
    refine ⟨j - 1, fun y hy => ?_⟩
    have b := patch_strat_bounds hA hκ hM hell hR1 hp hy
    have p := patch_two_strata hA hκ hM hell hR1 hR2 hp hy hv
    omega
  · push Not at hw
    refine ⟨j, fun y hy => ?_⟩
    have b := patch_strat_bounds hA hκ hM hell hR1 hp hy
    have hne := hw y hy
    omega

/-- **G3 cover (`patch_cover`)**: every `x ∈ Ω₀` and its forward neighbour lie in the core of the patch
`(strat x, corner of x's level-(strat x) coarse cell)`. -/
theorem patch_cover {ell M k κ : ℕ} {S : Tower L} (hκ : 0 < κ) (hM : 0 < M) (hell : 0 < ell)
    {x : PeriodicLatticeSite L} (hx : x ∈ S.Om 0) (μ : Fin 3) :
    ∃ (j : ℕ) (w : PeriodicLatticeSite L), IsPatch ell M k κ S j w ∧ x ∈ pcore ell M κ j w ∧
      periodicLatticeShift x μ ∈ pcore ell M κ j w := by
  set j := strat S k x with hjdef
  set g := gsp ell M κ j with hg
  have hgpos : 0 < g := gsp_pos hκ hM hell j
  refine ⟨j, cellCorner g x, ⟨strat_le S k x, fun ν => ?_, x, hx, rfl, fun ν => (cellCorner_div hgpos x ν).symm⟩, ?_, ?_⟩
  · show (x ν).val / g * g % g = 0
    exact Nat.mul_mod_left _ _
  · show pdist (cellCorner g x) x ≤ 4 * g
    have := pdist_cellCorner_le hgpos x
    omega
  · show pdist (cellCorner g x) (periodicLatticeShift x μ) ≤ 4 * g
    have h1 := pdist_cellCorner_le hgpos x
    have h2 := pdist_triangle (cellCorner g x) x (periodicLatticeShift x μ)
    have h3 := pdist_shift_le x μ
    omega

/-! ## multiplicity -/

/-- the shifted offset of `a` relative to `c` lies in `[0, 2 t]` when the circular distance is `≤ t`. -/
theorem off_le (N t a c : ℕ) (hN : 0 < N) (ha : a < N) (hc : c < N) (hd : pcd N a c ≤ t) :
    (a + (N - c) + t) % N ≤ 2 * t := by
  by_cases hNs : N ≤ 2 * t
  · exact le_trans (Nat.mod_lt _ hN).le hNs
  · push Not at hNs
    unfold pcd at hd
    by_cases hac : a ≤ c
    · rw [if_pos hac] at hd
      rcases min_le_iff.mp hd with h | h
      · have e : a + (N - c) + t = N + (t - (c - a)) := by omega
        rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
      · have e : a + (N - c) + t = (N - (c - a)) + t := by omega
        rw [e, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [if_neg hac] at hd
      rcases min_le_iff.mp hd with h | h
      · have e : a + (N - c) + t = N + ((a - c) + t) := by omega
        rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega
      · have e : a + (N - c) + t = N + (N + (t - (N - (a - c)))) := by omega
        rw [e, Nat.add_mod_left, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]; omega

/-- **1D count**: at most `3 (2c+1)` multiples of `G` in `[0, N)` within circular distance `c G` of `y` (no divisibility). -/
theorem card_grid_near1 (N G c y : ℕ) (hG : 0 < G) (hy : y < N) :
    ((Finset.univ : Finset (Fin N)).filter (fun t => t.val % G = 0 ∧ pcd N t.val y ≤ c * G)).card ≤ 3 * (2 * c + 1) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le y) hy
  set F := (Finset.univ : Finset (Fin N)).filter (fun t => t.val % G = 0 ∧ pcd N t.val y ≤ c * G) with hF
  set K := (N - y) + c * G with hK
  by_cases hNs : N ≤ 2 * c * G
  · have hmaps : ∀ t ∈ F, (fun t : Fin N => t.val / G) t ∈ Finset.range (2 * c + 1) := by
      intro t _
      rw [Finset.mem_range]
      have h1 : t.val / G < 2 * c * G / G + 1 :=
        Nat.lt_succ_of_le (Nat.div_le_div_right (le_trans t.isLt.le hNs))
      rw [Nat.mul_div_cancel _ hG] at h1
      exact h1
    have hinj : Set.InjOn (fun t : Fin N => t.val / G) F := by
      intro t ht t' ht' heq
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
      have h1 := Nat.div_add_mod t.val G
      have h2 := Nat.div_add_mod t'.val G
      have heq' : t.val / G = t'.val / G := heq
      rw [ht.1] at h1; rw [ht'.1] at h2
      exact Fin.ext (by rw [← h1, ← h2, heq'])
    calc F.card ≤ (Finset.range (2 * c + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = 2 * c + 1 := Finset.card_range _
      _ ≤ 3 * (2 * c + 1) := by omega
  · push Not at hNs
    let f : Fin N → ℕ × ℕ := fun t => ((t.val + K) / N, (t.val + K) % N / G)
    have hmaps : ∀ t ∈ F, f t ∈ Finset.range 3 ×ˢ Finset.range (2 * c + 1) := by
      intro t ht
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      constructor
      · show (t.val + K) / N < 3
        rw [Nat.div_lt_iff_lt_mul hN]
        have := t.isLt
        have e2 : 2 * c * G = c * G + c * G := by ring
        omega
      · show (t.val + ((N - y) + c * G)) % N / G < 2 * c + 1
        have h0 := off_le N (c * G) t.val y hN t.isLt hy ht.2
        rw [← Nat.add_assoc]
        have h2 : (t.val + (N - y) + c * G) % N / G ≤ 2 * (c * G) / G := Nat.div_le_div_right h0
        rw [show 2 * (c * G) = (2 * c) * G by ring, Nat.mul_div_cancel _ hG] at h2
        omega
    have hinj : Set.InjOn f F := by
      intro t ht t' ht' heq
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
      have hε : (t.val + K) / N = (t'.val + K) / N := congrArg Prod.fst heq
      have hq : (t.val + K) % N / G = (t'.val + K) % N / G := congrArg Prod.snd heq
      have a1 := Nat.div_add_mod (t.val + K) N
      have a2 := Nat.div_add_mod (t'.val + K) N
      have b1 := Nat.div_add_mod ((t.val + K) % N) G
      have b2 := Nat.div_add_mod ((t'.val + K) % N) G
      set A := N * ((t.val + K) / N) + G * ((t.val + K) % N / G) with hA
      have e1 : t.val + K = A + (t.val + K) % N % G := by rw [hA]; omega
      have e2 : t'.val + K = A + (t'.val + K) % N % G := by rw [hA, hε, hq]; omega
      have m1 : (t.val + K) % G = K % G := by rw [Nat.add_mod, ht.1, Nat.zero_add, Nat.mod_mod]
      have m2 : (t'.val + K) % G = K % G := by rw [Nat.add_mod, ht'.1, Nat.zero_add, Nat.mod_mod]
      have hr : (A + (t.val + K) % N % G) % G = (A + (t'.val + K) % N % G) % G := by
        rw [← e1, ← e2, m1, m2]
      have hr' : (t.val + K) % N % G ≡ (t'.val + K) % N % G [MOD G] := Nat.ModEq.add_left_cancel' A hr
      have r1 : (t.val + K) % N % G < G := Nat.mod_lt _ hG
      have r2 : (t'.val + K) % N % G < G := Nat.mod_lt _ hG
      have hreq := Nat.ModEq.eq_of_lt_of_lt hr' r1 r2
      apply Fin.ext
      omega
    calc F.card ≤ (Finset.range 3 ×ˢ Finset.range (2 * c + 1)).card := Finset.card_le_card_of_injOn f hmaps hinj
      _ = 3 * (2 * c + 1) := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

/-- **3D count**: at most `(3(2c+1))^3` corners of the `G`-grid within `ℓ¹` distance `c G` of `y`. -/
theorem card_grid_near (G c : ℕ) (hG : 0 < G) (y : PeriodicLatticeSite L) :
    ((Finset.univ : Finset (PeriodicLatticeSite L)).filter (fun z => GridCorner G z ∧ pdist z y ≤ c * G)).card
      ≤ (3 * (2 * c + 1)) ^ 3 := by
  set T : (μ : Fin 3) → Finset (Fin (L μ + 1)) := fun μ =>
    (Finset.univ : Finset (Fin (L μ + 1))).filter (fun t => t.val % G = 0 ∧ pcd (L μ + 1) t.val (y μ).val ≤ c * G) with hT
  have hsub : (Finset.univ : Finset (PeriodicLatticeSite L)).filter (fun z => GridCorner G z ∧ pdist z y ≤ c * G)
      ⊆ Fintype.piFinset T := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Fintype.mem_piFinset]
    intro μ
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hz.1 μ, le_trans ?_ hz.2⟩
    unfold pdist
    exact Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ μ)
  calc _ ≤ (Fintype.piFinset T).card := Finset.card_le_card hsub
    _ = ∏ μ, (T μ).card := Fintype.card_piFinset T
    _ ≤ ∏ _μ : Fin 3, (3 * (2 * c + 1)) := Finset.prod_le_prod' (fun μ _ =>
        card_grid_near1 (L μ + 1) G c (y μ).val hG (y μ).isLt)
    _ = (3 * (2 * c + 1)) ^ 3 := by simp

/-- the finite set of patch indices containing `y`. -/
noncomputable def patchesAt (ell M k κ c : ℕ) (S : Tower L) (y : PeriodicLatticeSite L) :
    Finset (Fin (k + 1) × PeriodicLatticeSite L) :=
  (Finset.univ : Finset (Fin (k + 1) × PeriodicLatticeSite L)).filter
    (fun p => IsPatch ell M k κ S p.1.val p.2 ∧ y ∈ patch ell M κ c p.1.val p.2)

/-- **G3 multiplicity (`patch_mult`)**: a site lies in at most `3 (3(2c+1))^3` patches -- free of `k` and `κ`
(`(c+3) κ ell ≤ R`). -/
theorem patch_mult {ell M R k κ c : ℕ} {S : Tower L} (hA : Admissible ell M R k S) (hκ : 0 < κ) (hM : 0 < M)
    (hell : 1 ≤ ell) (hR : (c + 3) * κ * ell ≤ R) (y : PeriodicLatticeSite L) :
    (patchesAt ell M k κ c S y).card ≤ 3 * (3 * (2 * c + 1)) ^ 3 := by
  set F := patchesAt ell M k κ c S y with hF
  have hfib : ∀ a ∈ F.image Prod.fst, (F.filter (fun p => p.1 = a)).card ≤ (3 * (2 * c + 1)) ^ 3 := by
    intro a _
    have hgpos : 0 < gsp ell M κ a.val := gsp_pos hκ hM hell _
    refine le_trans ?_ (card_grid_near (gsp ell M κ a.val) c hgpos y)
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      simp only [hF, patchesAt, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp ⊢
      obtain ⟨⟨hpat, hy⟩, rfl⟩ := hp
      refine ⟨hpat.2.1, ?_⟩
      have : pdist p.2 y ≤ c * gsp ell M κ p.1.val := hy
      exact this
    · intro p hp p' hp' h
      simp only [hF, patchesAt, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp hp'
      exact Prod.ext (hp.2.trans hp'.2.symm) h
  have himg : (F.image Prod.fst).card ≤ 3 := by
    have hsub : (F.image Prod.fst).image Fin.val ⊆ Finset.Icc (strat S k y - 1) (strat S k y + 1) := by
      intro v hv
      simp only [Finset.mem_image, hF, patchesAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨a, ⟨p, ⟨hpat, hy⟩, rfl⟩, rfl⟩ := hv
      have := patch_strat_bounds hA hκ hM hell hR hpat hy
      rw [Finset.mem_Icc]; omega
    have h1 : ((F.image Prod.fst).image Fin.val).card = (F.image Prod.fst).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have h2 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h2
    omega
  calc F.card ≤ (3 * (2 * c + 1)) ^ 3 * (F.image Prod.fst).card := Finset.card_le_mul_card_image F _ hfib
    _ ≤ (3 * (2 * c + 1)) ^ 3 * 3 := Nat.mul_le_mul_left _ himg
    _ = 3 * (3 * (2 * c + 1)) ^ 3 := by ring

#print axioms pcore_sub_patch
#print axioms eq_cellCorner
#print axioms IsPatch.anchor
#print axioms patch_strat_bounds
#print axioms patch_two_strata
#print axioms patch_strata_pair
#print axioms pdist_cellCorner_le
#print axioms patch_cover
#print axioms off_le
#print axioms card_grid_near1
#print axioms card_grid_near
#print axioms patch_mult

end AdalyFormal.M1

import M1B

/-!
# M1Cov -- the headline's coverage hypothesis `CoversOm0p 12` FAILS on admissible towers, for every `R` (`ell = 3`, `M = 3 = ell^1`, `k = 1`)
(M1 lane B, 2026-10-13; statement fact)

Slab tower `TS R` on the fine torus of side `N = 18R + 216` (unit torus side `6R + 72`): `Ω₁ = {9R+18 ≤ x₀ < 9R+108}` (ten level-1 blocks of
side 9), `Ω₀ = {6R+18 ≤ x₀ < 12R+108}` (`Ω₁` widened by `R M = 3R`), `Ω_j = ∅` for `j ≥ 2`.  `TS_admissible : Admissible 3 3 R 1 (TS R)`.
The site `x*` with `x*₀ = 9R + 63` (middle of the slab) lies in NO class cube of factor 12: an index-0 cube (side 36) through `x*` stays
inside `Ω₁` and so misses `B⁰`; an index-1 cube (side 108) is longer than the slab (90) and leaves `Ω₁`.  Hence
`slab_not_covered : ¬ CoversOm0p 3 3 12 1 (TS R)` and `slab_no_class : ¬ ClassCoupled 3 3 12 1 (TS R) α₀ η U` for every `U`:
at these towers the headline's inner claim `CoercG8At` holds vacuously, whereas `M1CoreAll` (no coverage hypothesis) asks for `InstIneq`
there.  `coverage_fails_slab` packages: for every `R` there is a unit torus with `TorusOK 3 3`, an admissible tower, and coverage failing.
Scope: `ell = 3`, `M = 3` (`m = 1`) only; general `m` is not treated here.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

variable {L : PeriodicLatticeExtent}

/-- the slab tower. -/
def TS (R : ℕ) (L : PeriodicLatticeExtent) : Tower L :=
  ⟨fun j => if j = 0 then {x | 6 * R + 18 ≤ (x 0).val ∧ (x 0).val < 12 * R + 108}
    else if j = 1 then {x | 9 * R + 18 ≤ (x 0).val ∧ (x 0).val < 9 * R + 108} else ∅⟩

theorem TS_om0 (R : ℕ) (L : PeriodicLatticeExtent) (x : PeriodicLatticeSite L) :
    x ∈ (TS R L).Om 0 ↔ 6 * R + 18 ≤ (x 0).val ∧ (x 0).val < 12 * R + 108 := by simp [TS]

theorem TS_om1 (R : ℕ) (L : PeriodicLatticeExtent) (x : PeriodicLatticeSite L) :
    x ∈ (TS R L).Om 1 ↔ 9 * R + 18 ≤ (x 0).val ∧ (x 0).val < 9 * R + 108 := by simp [TS]

theorem TS_omHi (R : ℕ) (L : PeriodicLatticeExtent) {j : ℕ} (hj : 2 ≤ j) : (TS R L).Om j = ∅ := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [TS, h0, h1]

/-- the periodic offset, without `%` by a variable. -/
theorem off_cases (N a z : ℕ) (ha : a < N) (hz : z < N) :
    (a + N - z) % N = if z ≤ a then a - z else a + N - z := by
  split_ifs with h
  · have : a + N - z = (a - z) + N := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- arithmetic of the slab, with the torus side as a variable `N` (avoids rewriting the side inside `Fin` types). -/
theorem pcd_slab_far (R a b N : ℕ) (hN : N = 18 * R + 216) (ha : a < N) (hb : b < N)
    (hx : ¬ (6 * R + 18 ≤ a ∧ a < 12 * R + 108)) (hy : 9 * R + 18 ≤ b ∧ b < 9 * R + 108) : 3 * R < pcd N a b := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem pcd_slab_clamp (R a N : ℕ) (hN : N = 18 * R + 216) (hx : 6 * R + 18 ≤ a ∧ a < 12 * R + 108) :
    pcd N a (if a < 9 * R + 18 then 9 * R + 18 else if a < 9 * R + 108 then a else 9 * R + 107) ≤ 3 * R := by
  subst hN; unfold pcd; split_ifs <;> omega

theorem pcd_slab_near (R a b N : ℕ) (hN : N = 18 * R + 216) (ha : a < N) (hb : b < N)
    (hy : 9 * R + 18 ≤ b ∧ b < 9 * R + 108) (h : pcd N a b ≤ 3 * R) : 6 * R + 18 ≤ a ∧ a < 12 * R + 108 := by
  subst hN; unfold pcd at h; split_ifs at h <;> omega

theorem TS_admissible (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) : Admissible 3 3 R 1 (TS R L) := by
  have hx0 : ∀ x : PeriodicLatticeSite L, (x 0).val < 18 * R + 216 := fun x => by have := (x 0).isLt; have := hN 0; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · rw [TS_om1] at hx; rw [TS_om0]; omega
      · rw [TS_omHi R L (le_refl 2)] at hx; exact hx.elim
    · rw [TS_omHi R L (by omega : 2 ≤ j + 1)] at hx; exact hx.elim
  · intro j hj; exact TS_omHi R L (by omega)
  · intro j hj μ
    rw [hN μ]
    interval_cases j
    · exact ⟨6 * R + 72, by simp [bigSide]; ring⟩
    · exact ⟨2 * R + 24, by simp [bigSide]; ring⟩
  · intro j hj
    interval_cases j
    · intro x hx y hy
      rw [TS_om0] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
    · intro x hx y hy
      rw [TS_om1] at hx ⊢
      have := hy 0
      simp [bigSide] at this
      omega
  · intro j hj x hx y hy
    interval_cases j
    · rw [TS_om0] at hx; rw [TS_om1] at hy
      have hxl := hx0 x; have hyl := hx0 y
      have hlt : 3 * R < pcd (L 0 + 1) (x 0).val (y 0).val :=
        pcd_slab_far R _ _ _ (hN 0) (x 0).isLt (y 0).isLt hx hy
      unfold pdist
      show R * bigSide 3 3 0 < _
      simp only [bigSide, pow_zero, mul_one]
      have := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      omega
    · rw [TS_omHi R L (le_refl 2)] at hy; exact hy.elim
  · intro x
    rw [TS_om0]
    have hxl := hx0 x
    constructor
    · intro hx
      let v : ℕ := if (x 0).val < 9 * R + 18 then 9 * R + 18 else if (x 0).val < 9 * R + 108 then (x 0).val else 9 * R + 107
      have hv : v < L 0 + 1 := by rw [hN 0]; simp only [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · rw [TS_om1]; simp only [Function.update_self]; simp only [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, bigSide, pow_zero, mul_one]
          have := pcd_slab_clamp R (x 0).val (L 0 + 1) (hN 0) hx
          simp only [v]; omega
        · intro μ _ h
          rw [Function.update_of_ne h, AdalyFormal.StatementLaneR8.pcd_self]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨y, hy, z, hz, hd⟩
      rw [TS_om1] at hy
      have hz0 : (z 0).val / 3 = (x 0).val / 3 := hz 0
      have hlt := Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (z μ).val (y μ).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have hzl := hx0 z; have hyl := hx0 y
      have h3 : pcd (L 0 + 1) (z 0).val (y 0).val ≤ 3 * R := by
        have := le_trans hlt hd
        first | omega | (simp only [bigSide, pow_zero, mul_one] at this; omega)
      have := pcd_slab_near R _ _ _ (hN 0) (z 0).isLt (y 0).isLt hy h3
      omega

/-- the middle site. -/
def xmid (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) : PeriodicLatticeSite L :=
  fun μ => if μ = 0 then ⟨9 * R + 63, by have := hN μ; omega⟩ else ⟨0, by have := hN μ; omega⟩

theorem xmid0 (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) : ((xmid R hN) 0).val = 9 * R + 63 := by
  simp [xmid]

/-- **no class cube of factor 12 contains the middle site.** -/
theorem xmid_no_cube (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) (sites : Set (PeriodicLatticeSite L)) (j : ℕ)
    (hq : IsClassCube 3 3 12 1 (TS R L) sites j) : xmid R hN ∉ sites := by
  obtain ⟨⟨hj1, ⟨z, hz, rfl⟩, hsub, hne⟩, -⟩ := hq
  have hmem : ∀ y : PeriodicLatticeSite L, y ∈ siteBox z (12 * bigSide 3 3 j) →
      (if (z 0).val ≤ (y 0).val then (y 0).val - (z 0).val else (y 0).val + (L 0 + 1) - (z 0).val)
        < 12 * bigSide 3 3 j := by
    intro y hy
    have := hy 0
    rwa [off_cases (L 0 + 1) _ _ (y 0).isLt (z 0).isLt] at this
  intro hxs
  have hN0 := hN 0
  interval_cases j
  · -- index 0: side 36; every point of the box is in Ω₁, so the box misses B⁰
    obtain ⟨y, hys, hyB⟩ := hne
    have h1 := hmem _ hxs
    have h2 := hmem _ hys
    rw [xmid0] at h1
    simp only [bigSide, pow_zero, mul_one] at h1 h2
    have hy1 : y ∈ (TS R L).Om 1 := by
      rw [TS_om1]
      have := (y 0).isLt; have := (z 0).isLt
      split_ifs at h1 h2 <;> omega
    exact hyB.2 (by simpa using hy1)
  · -- index 1: side 108 > slab width 90
    have hz9 : (z 0).val % 9 = 0 := by have := hz 0; simpa [bigSide] using this
    have hzin : z ∈ siteBox z (12 * bigSide 3 3 1) := by
      intro μ
      have hzl : (z μ).val < L μ + 1 := (z μ).isLt
      have : ((z μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) = 0 := by
        rw [Nat.add_sub_cancel_left, Nat.mod_self]
      rw [this]; simp [bigSide]
    have hz1 : z ∈ (TS R L).Om 1 := by
      rcases hsub hzin with h | h
      · exact h.1
      · exact absurd h.1 (by simp [TS])
    rw [TS_om1] at hz1
    -- the far point of the box in direction 0
    have hfar : (z 0).val + 107 < L 0 + 1 := by omega
    set w : PeriodicLatticeSite L := Function.update z 0 ⟨(z 0).val + 107, hfar⟩ with hw
    have hwin : w ∈ siteBox z (12 * bigSide 3 3 1) := by
      intro μ
      by_cases hμ : μ = 0
      · subst hμ
        simp only [hw, Function.update_self]
        rw [off_cases _ _ _ (by omega) (z 0).isLt, if_pos (by omega)]
        simp [bigSide]
      · simp only [hw, Function.update_of_ne hμ]
        have hzl : (z μ).val < L μ + 1 := (z μ).isLt
        have : ((z μ).val + (L μ + 1) - (z μ).val) % (L μ + 1) = 0 := by
          rw [Nat.add_sub_cancel_left, Nat.mod_self]
        rw [this]; simp [bigSide]
    have hw1 : w ∈ (TS R L).Om 1 := by
      rcases hsub hwin with h | h
      · exact h.1
      · exact absurd h.1 (by simp [TS])
    rw [TS_om1] at hw1
    simp only [hw, Function.update_self] at hw1
    omega

theorem xmid_om0 (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) : xmid R hN ∈ (TS R L).Om 0 := by
  rw [TS_om0, xmid0]; omega

/-- **coverage fails on the slab tower.** -/
theorem slab_not_covered (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) : ¬ CoversOm0p 3 3 12 1 (TS R L) := by
  intro h
  obtain ⟨sites, j, hq, hx⟩ := h.1 (xmid R hN) (xmid_om0 R hN)
  exact xmid_no_cube R hN sites j hq hx

/-- the headline's class hypothesis is unsatisfiable on the slab tower, for every configuration. -/
theorem slab_no_class (R : ℕ) (hN : ∀ μ, L μ + 1 = 18 * R + 216) (α₀ η : ℝ) (U : LinkCfg L) :
    ¬ ClassCoupled 3 3 12 1 (TS R L) α₀ η U := fun h => slab_not_covered R hN h.1

/-- **for every `R`**: a unit torus with `TorusOK 3 3`, an admissible tower of height 1, and the coverage hypothesis failing. -/
theorem coverage_fails_slab (R : ℕ) :
    ∃ Lu : PeriodicLatticeExtent, TorusOK 3 3 Lu ∧ Admissible 3 3 R 1 (TS R (scaleUp 3 1 Lu)) ∧
      ¬ CoversOm0p 3 3 12 1 (TS R (scaleUp 3 1 Lu)) := by
  refine ⟨fun _ => 6 * R + 71, ⟨fun μ => ⟨2 * R + 24, by ring⟩, fun μ => by show 3 < 6 * R + 71 + 1; omega, fun μ => ⟨2 * R + 24, by ring⟩⟩, ?_, ?_⟩
  · apply TS_admissible
    intro μ; simp [scaleUp]; ring_nf
  · apply slab_not_covered
    intro μ; simp [scaleUp]; ring_nf

#print axioms TS_admissible
#print axioms xmid_no_cube
#print axioms slab_not_covered
#print axioms slab_no_class
#print axioms coverage_fails_slab

end AdalyFormal.M1

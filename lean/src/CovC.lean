import CovB

/-!
# CovC -- the corner of `GT`: the twelve edges of the unit cell at `(M-1, M-1, M-1)` carry no clause 3
(m2_coverage, 2026-10-14)

* `gt_no_cube_of` : no class cube of `GT` contains, along every axis `σ`, a site in block `0` and a site in block `1`.
* `gt_edge_no_cube` : for every bond `(x, μ)` with `x_μ = M-1` and `x_ν ∈ {M-1, M}` (`ν ≠ μ`) -- the twelve edges of the
  unit cell `[M-1, M]³` -- the premise of clause 3 of `PerCubeRegular2` (every `CurlReads` of the `ddA` stencil inside one
  class cube) holds for NO class cube: the printed class, as frozen in r8, imposes no `ddA` bound on these twelve bonds.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M2Coverage

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)

section corner
variable {L : PeriodicLatticeExtent} {n M : ℕ} (hM : 0 < M) (hn : 25 ≤ n) (hL : ∀ μ, L μ + 1 = 2 * n * M)
include hM hn hL

theorem gt_no_cube_of (sites : Set (PeriodicLatticeSite L)) (i : ℕ) (hq : IsClassCube 2 M 12 1 (GT L n M) sites i)
    (P Q : Fin 3 → PeriodicLatticeSite L)
    (hP : ∀ σ, P σ ∈ sites ∧ ((P σ) σ).val / M = 0) (hQ : ∀ σ, Q σ ∈ sites ∧ ((Q σ) σ).val / M = 1) : False := by
  obtain ⟨⟨hik, ⟨z, hgrid, hz⟩, hsub, ⟨c, hcs, hcB⟩⟩, -⟩ := hq
  have hzM : ∀ σ, (z σ).val % M = 0 := by
    intro σ
    have h := hgrid σ
    rcases Nat.lt_or_ge i 1 with h0 | h1
    · have hi : i = 0 := by omega
      subst hi; rw [bs0] at h; exact h
    · have hi : i = 1 := by omega
      subst hi; rw [bs1] at h
      exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.trans (Dvd.intro 2 rfl) (Nat.dvd_of_mod_eq_zero h))
  set b : Fin 3 → ℕ := fun σ => (z σ).val / M with hbdef
  have hb : ∀ σ, b σ < 2 * n := fun σ => blk_lt M _ _ hM (xlt hM hn hL z σ)
  have hzb : z = mkG hL (fun σ => M * b σ) (fun σ => mulb_lt hM hn hL (b σ) (hb σ)) := by
    funext σ
    apply Fin.ext
    rw [mkG_val]
    have := Nat.div_add_mod (z σ).val M
    rw [hzM σ] at this
    simp only [hbdef]; omega
  have hmem : ∀ c', ∀ y, y ∈ siteBox z (c' * M) → ∀ σ, inB (2 * n) (b σ) c' ((y σ).val / M) := by
    intro c' y hy
    rw [hzb, mem_boxBG hM hn hL b hb] at hy
    exact hy
  rcases Nat.lt_or_ge i 1 with h0 | h1
  · have hi : i = 0 := by omega
    subst hi
    rw [bs0] at hz
    have hcl : GH n M c := by
      have h := hcB.2
      exact Classical.byContradiction (fun hn' => h (by rw [show (0 : ℕ) + 1 = 1 from rfl, gt_om1]; exact hn'))
    have key : ∀ σ, ((c σ).val / M / 2 = 6 ∨ (c σ).val / M / 2 = n - 6) → False := by
      intro σ hσ
      have a1 := hmem 12 _ (hz ▸ (hP σ).1) σ
      have a2 := hmem 12 _ (hz ▸ (hQ σ).1) σ
      have a3 := hmem 12 _ (hz ▸ hcs) σ
      have p1 := (hP σ).2
      have q1 := (hQ σ).2
      have bl := hb σ
      have cl := blk_lt M _ _ hM (xlt hM hn hL c σ)
      rw [p1] at a1; rw [q1] at a2
      rw [inB_iff (by omega) bl] at a1 a2
      rw [inB_iff cl bl] at a3
      omega
    unfold GH holeQ at hcl
    rw [col_eq, col_eq, col_eq] at hcl
    rcases hcl with ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
  · have hi : i = 1 := by omega
    subst hi
    rw [bs1, show 12 * (M * 2) = 24 * M by ring] at hz
    have hbe : ∀ σ, b σ % 2 = 0 := by
      intro σ
      have h := hgrid σ
      rw [bs1] at h
      have h2 : M * 2 ∣ (z σ).val := Nat.dvd_of_mod_eq_zero h
      obtain ⟨q, hq⟩ := h2
      simp only [hbdef]; rw [hq, show M * 2 * q = M * (2 * q) by ring, Nat.mul_div_cancel_left _ hM]; omega
    have hw0 : ∀ σ, inB (2 * n) (b σ) 24 0 ∧ inB (2 * n) (b σ) 24 1 := by
      intro σ
      have a1 := hmem 24 _ (hz ▸ (hP σ).1) σ
      have a2 := hmem 24 _ (hz ▸ (hQ σ).1) σ
      rw [(hP σ).2] at a1; rw [(hQ σ).2] at a2
      exact ⟨a1, a2⟩
    have hsub1 : ∀ y, y ∈ sites → ¬ GH n M y := by
      intro y hy
      rcases hsub hy with h | h
      · have h1 := h.1; rw [gt_om1] at h1; exact h1
      · have h1 := h.1; rw [gt_omj (by norm_num)] at h1; exact h1.elim
    set qb : ℕ := if b 0 = 0 ∨ 2 * n - 12 < b 0 then 12 else 2 * n - 12 with hqb
    have hqbl : qb < 2 * n := by simp only [hqb]; split_ifs <;> omega
    have hqin : inB (2 * n) (b 0) 24 qb := by
      have w0 := (inB_iff (by omega) (hb 0)).1 (hw0 0).1
      have w1 := (inB_iff (by omega) (hb 0)).1 (hw0 0).2
      have e := hbe 0
      have bl := hb 0
      rw [inB_iff hqbl bl]
      simp only [hqb]; split_ifs <;> omega
    set y := mkG hL (fun σ => M * (if σ = 0 then qb else 0)) (fun σ => by
      split_ifs
      · exact mulb_lt hM hn hL _ hqbl
      · simp only [mul_zero]; have : 0 < 2 * n * M := by positivity
        exact this) with hy
    have hyin : y ∈ sites := by
      rw [hz, hzb, mem_boxBG hM hn hL b hb]
      intro σ
      rw [hy, mkG_val, Nat.mul_div_cancel_left _ hM]
      by_cases h : σ = 0
      · subst h; simp only [if_pos rfl]; exact hqin
      · simp only [if_neg h]; exact (hw0 σ).1
    apply hsub1 y hyin
    show holeQ n ((y 0).val / (M * 2)) ((y 1).val / (M * 2)) ((y 2).val / (M * 2))
    rw [col_eq, col_eq, col_eq, hy, mkG_val, mkG_val, mkG_val,
      Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM]
    refine holeQ_axis n 0 (fun σ => (if σ = 0 then qb else 0) / 2) ?_ (fun σ hσ => ?_)
    · simp only [if_pos rfl, hqb]; split_ifs <;> omega
    · simp only [if_neg hσ]

theorem val_shift_self (x : PeriodicLatticeSite L) (σ : Fin 3) (hx : (x σ).val = M - 1) :
    (periodicLatticeShift x σ σ).val = M := by
  rw [shiftG_val hL, if_pos rfl, hx, show M - 1 + 1 = M by omega]
  apply Nat.mod_eq_of_lt
  have : M * 1 < 2 * n * M := by
    have := Nat.mul_lt_mul_of_pos_left (show 1 < 2 * n by omega) hM
    rw [mul_comm M (2 * n)] at this; exact this
  omega

omit hn in
theorem val_back_self (x : PeriodicLatticeSite L) (σ : Fin 3) (hx : (x σ).val = M) :
    (periodicLatticeShiftBack x σ σ).val = M - 1 := by
  have h := congrArg (fun y : PeriodicLatticeSite L => (y σ).val) (periodicLatticeShift_shiftBack x σ)
  rw [shiftG_val hL, if_pos rfl, hx] at h
  have hl := (periodicLatticeShiftBack x σ σ).isLt
  have hL' := hL σ
  set v := (periodicLatticeShiftBack x σ σ).val
  by_cases h1 : v + 1 < 2 * n * M
  · rw [Nat.mod_eq_of_lt h1] at h; omega
  · have : v + 1 = 2 * n * M := by omega
    rw [this, Nat.mod_self] at h; omega

theorem gt_edge_no_cube (x : PeriodicLatticeSite L) (μ : Fin 3) (hxμ : (x μ).val = M - 1)
    (hxν : ∀ ν, ν ≠ μ → (x ν).val = M - 1 ∨ (x ν).val = M) :
    ¬ ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube 2 M 12 1 (GT L n M) sites i ∧
      ∀ ν : Fin 3, ν ≠ μ → CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ := by
  classical
  rintro ⟨sites, i, hq, hst⟩
  obtain ⟨ν0, hν0, -⟩ := AdalyFormal.M2Route.third_axis μ μ
  have hx : x ∈ sites := (hst ν0 hν0).2.2.1.1
  have hxμs : periodicLatticeShift x μ ∈ sites := (hst ν0 hν0).2.2.1.2
  have hxsh : ∀ ν, ν ≠ μ → periodicLatticeShift x ν ∈ sites := fun ν hν => (hst ν hν).2.2.2.2.2
  have hxb : ∀ ν, ν ≠ μ → periodicLatticeShiftBack x ν ∈ sites := fun ν hν => (hst ν hν).1.2.2.2.1
  have hMd : (M - 1) / M = 0 := Nat.div_eq_of_lt (by omega)
  have hM1 : M / M = 1 := Nat.div_self hM
  refine gt_no_cube_of hM hn hL sites i hq
    (fun σ => if σ = μ then x else if (x σ).val = M - 1 then x else periodicLatticeShiftBack x σ)
    (fun σ => if σ = μ then periodicLatticeShift x μ else if (x σ).val = M - 1 then periodicLatticeShift x σ else x)
    (fun σ => ?_) (fun σ => ?_)
  · by_cases h : σ = μ
    · subst h; rw [if_pos (rfl : σ = σ)]; exact ⟨hx, by rw [hxμ]; exact hMd⟩
    · rw [if_neg h]
      by_cases h2 : (x σ).val = M - 1
      · rw [if_pos h2]; exact ⟨hx, by rw [h2]; exact hMd⟩
      · rw [if_neg h2]
        have h3 : (x σ).val = M := by have := hxν σ h; omega
        exact ⟨hxb σ h, by rw [val_back_self hM hL x σ h3]; exact hMd⟩
  · by_cases h : σ = μ
    · subst h; rw [if_pos (rfl : σ = σ)]; exact ⟨hxμs, by rw [val_shift_self hM hn hL x σ hxμ]; exact hM1⟩
    · rw [if_neg h]
      by_cases h2 : (x σ).val = M - 1
      · rw [if_pos h2]; exact ⟨hxsh σ h, by rw [val_shift_self hM hn hL x σ h2]; exact hM1⟩
      · rw [if_neg h2]
        have h3 : (x σ).val = M := by have := hxν σ h; omega
        exact ⟨hx, by rw [h3]; exact hM1⟩

end corner

end AdalyFormal.M2Coverage

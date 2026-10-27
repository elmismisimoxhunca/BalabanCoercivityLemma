import Q409W0

/-!
# Q409W1 -- site-level shifts, the coordinate shift identity, and the box that contains an `l^1` ball.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.P409W

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane

theorem coord_box (N a r s : ℕ) (hN : 0 < N) (ha : a < N) (hs : 2 * r + 1 ≤ s) :
    ∃ z : ℕ, z < N ∧ (z = 0 ∨ (r ≤ a ∧ z = a - r) ∨ (a < r ∧ z = a + N - r)) ∧
      ∀ b : ℕ, b < N → pcd N a b ≤ r → (b + N - z) % N < s := by
  by_cases hNs : N ≤ s
  · refine ⟨0, hN, Or.inl rfl, fun b hb _ => ?_⟩
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    omega
  · push Not at hNs
    refine ⟨if r ≤ a then a - r else a + N - r, ?_, ?_, fun b hb hbr => ?_⟩
    · split_ifs <;> omega
    · split_ifs with h
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
      · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
    · have hm := Nat.mod_add_div (b + N - (if r ≤ a then a - r else a + N - r)) N
      have hq : (b + N - (if r ≤ a then a - r else a + N - r)) / N < 3 :=
        Nat.div_lt_of_lt_mul (by split_ifs <;> omega)
      have hlt := Nat.mod_lt (b + N - (if r ≤ a then a - r else a + N - r)) hN
      generalize (b + N - (if r ≤ a then a - r else a + N - r)) % N = m at *
      generalize (b + N - (if r ≤ a then a - r else a + N - r)) / N = q at *
      unfold pcd at hbr
      interval_cases q <;> split_ifs at hm hbr ⊢ <;> omega

variable {L : PeriodicLatticeExtent}

theorem pcd_le_pdist_coord (x y : PeriodicLatticeSite L) (σ : Fin 3) :
    pcd (L σ + 1) (x σ).val (y σ).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)

theorem box_site (w : PeriodicLatticeSite L) (r s : ℕ) (hs : 2 * r + 1 ≤ s) :
    ∃ z : PeriodicLatticeSite L, ∀ y : PeriodicLatticeSite L, pdist w y ≤ r → y ∈ siteBox z s := by
  have h : ∀ μ : Fin 3, ∃ z : ℕ, z < L μ + 1 ∧ ∀ b : ℕ, b < L μ + 1 → pcd (L μ + 1) (w μ).val b ≤ r →
      (b + (L μ + 1) - z) % (L μ + 1) < s := fun μ => by
    obtain ⟨z, h1, -, h3⟩ := coord_box (L μ + 1) (w μ).val r s (Nat.succ_pos _) (w μ).isLt hs
    exact ⟨z, h1, h3⟩
  choose zf hzf hz using h
  refine ⟨fun μ => ⟨zf μ, hzf μ⟩, fun y hy μ => ?_⟩
  exact hz μ (y μ).val (y μ).isLt (le_trans (pcd_le_pdist_coord w y μ) hy)

theorem coord_box_cell (N g a r : ℕ) (hg : 0 < g) (hgN : g ∣ N) (hga : g ∣ a) (hgr : g ∣ r) (ha : a < N) :
    ∃ z : ℕ, z < N ∧ ∀ b b' : ℕ, b < N → b' < N → b / g = b' / g → pcd N a b ≤ r → (b' + N - z) % N < 2 * r + g := by
  have hN : 0 < N := by omega
  by_cases hNs : N ≤ 2 * r + g
  · refine ⟨0, hN, fun b b' _ hb' _ _ => ?_⟩
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hb']
    omega
  · push Not at hNs
    obtain ⟨z, hz1, hz2, hz3⟩ := coord_box N a r (2 * r + 1) hN ha (by omega)
    have hgz : g ∣ z := by
      rcases hz2 with rfl | ⟨h, rfl⟩ | ⟨h, rfl⟩
      · exact dvd_zero g
      · exact Nat.dvd_sub hga hgr
      · have : a + N - r = (a + N) - r := rfl
        rw [this]; exact Nat.dvd_sub (dvd_add hga hgN) hgr
    refine ⟨z, hz1, fun b b' hb hb' hbb hbr => ?_⟩
    have h1 := hz3 b hb hbr
    have hs : g ∣ N - z := Nat.dvd_sub hgN hgz
    have key := div_shift g N b b' (N - z) hg hgN hs hbb
    have e1 : b + N - z = b + (N - z) := by omega
    have e2 : b' + N - z = b' + (N - z) := by omega
    rw [e1] at h1
    rw [e2]
    set u := (b + (N - z)) % N with hu
    set u' := (b' + (N - z)) % N with hu'
    have hm := Nat.div_add_mod u' g
    have hml := Nat.mod_lt u' hg
    have hq := Nat.mul_div_le u g
    rw [← key] at hm
    nlinarith

theorem box_site_cell (w : PeriodicLatticeSite L) (r g : ℕ) (hg : 0 < g) (hgN : ∀ μ : Fin 3, g ∣ L μ + 1)
    (hgw : ∀ μ : Fin 3, g ∣ (w μ).val) (hgr : g ∣ r) :
    ∃ z : PeriodicLatticeSite L, ∀ y y' : PeriodicLatticeSite L, pdist w y ≤ r →
      (∀ μ : Fin 3, (y μ).val / g = (y' μ).val / g) → y' ∈ siteBox z (2 * r + g) := by
  have h : ∀ μ : Fin 3, ∃ z : ℕ, z < L μ + 1 ∧ ∀ b b' : ℕ, b < L μ + 1 → b' < L μ + 1 → b / g = b' / g →
      pcd (L μ + 1) (w μ).val b ≤ r → (b' + (L μ + 1) - z) % (L μ + 1) < 2 * r + g :=
    fun μ => coord_box_cell (L μ + 1) g (w μ).val r hg (hgN μ) (hgw μ) hgr (w μ).isLt
  choose zf hzf hz using h
  refine ⟨fun μ => ⟨zf μ, hzf μ⟩, fun y y' hy hyy μ => ?_⟩
  exact hz μ (y μ).val (y' μ).val (y μ).isLt (y' μ).isLt (hyy μ) (le_trans (pcd_le_pdist_coord w y μ) hy)

/-- shift the `μ`-coordinate by `s` (mod the side). -/
def sh (x : PeriodicLatticeSite L) (μ : Fin 3) (s : ℕ) : PeriodicLatticeSite L := fun ν =>
  if ν = μ then ⟨((x ν).val + s) % (L ν + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ else x ν

theorem sh_self (x : PeriodicLatticeSite L) (μ : Fin 3) (s : ℕ) :
    ((sh x μ s) μ).val = ((x μ).val + s) % (L μ + 1) := by
  simp [sh]

theorem sh_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (s : ℕ) (h : ν ≠ μ) : (sh x μ s) ν = x ν := by
  simp [sh, h]

theorem pdist_sh_le (x : PeriodicLatticeSite L) (μ : Fin 3) (s : ℕ) (hs : s ≤ L μ + 1) :
    pdist x (sh x μ s) ≤ s ∧ pdist x (sh x μ s) ≤ L μ + 1 - s := by
  have key : pdist x (sh x μ s) = pcd (L μ + 1) (x μ).val ((sh x μ s) μ).val := by
    unfold pdist
    rw [Finset.sum_eq_single μ]
    · intro ν _ hν
      rw [sh_ne x μ ν s hν]; unfold pcd; simp
    · intro h; exact absurd (Finset.mem_univ μ) h
  rw [key, sh_self]
  exact pcd_shift_le _ _ _ (x μ).isLt hs

/-- two sites agreeing off `μ`: the `l^1` distance to a third site changes only through the `μ`-term. -/
theorem pdist_swap (x y t : PeriodicLatticeSite L) (μ : Fin 3) (h : ∀ ν, ν ≠ μ → y ν = x ν) :
    pdist y t + pcd (L μ + 1) (x μ).val (t μ).val = pdist x t + pcd (L μ + 1) (y μ).val (t μ).val := by
  unfold pdist
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases μ
  · have h1 := h 1 (by decide); have h2 := h 2 (by decide)
    simp only [Fin.zero_eta, h1, h2]; omega
  · have h1 := h 0 (by decide); have h2 := h 2 (by decide)
    simp only [Fin.mk_one, h1, h2]; omega
  · have h1 := h 0 (by decide); have h2 := h 1 (by decide)
    simp only [Fin.reduceFinMk, h1, h2]; omega

end AdalyFormal.P409W

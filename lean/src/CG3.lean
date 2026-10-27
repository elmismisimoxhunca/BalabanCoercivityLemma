import CG1

/-!
# CG3 -- cyclic cell boxes: one or two adjacent `s`-cells per axis, one axis a single cell, lie in ONE class cube
(`s` any common divisor of the class-cube grids that is used as the cell side; cells are taken cyclically on the torus).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2

variable {L : PeriodicLatticeExtent}

theorem shift_val' (x : PeriodicLatticeSite L) (μ τ : Fin 3) :
    ((periodicLatticeShift x μ) τ).val = if τ = μ then ((x μ).val + 1) % (L μ + 1) else (x τ).val := by
  unfold periodicLatticeShift
  by_cases hτ : τ = μ
  · subst hτ
    simp only [Function.update_self, if_true]
    rw [Fin.val_add]
    rcases Nat.eq_zero_or_pos (L τ) with h | h
    · simp [h]
    · rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < L τ + 1)]
  · simp [hτ]

theorem cell_add {s : ℕ} (hs : 0 < s) (u r : ℕ) (hr : r < s) : (s * u + r) / s = u := by
  rw [add_comm, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hr]; simp

/-- the sites whose cell coordinates are `u_τ` (one cell) or `u_τ, (u_τ+1) mod n_τ` (two cells, when `two τ`). -/
def CellReg (s : ℕ) (n u : Fin 3 → ℕ) (two : Fin 3 → Prop) : Set (PeriodicLatticeSite L) :=
  {x | ∀ τ, (x τ).val / s = u τ ∨ (two τ ∧ (x τ).val / s = (u τ + 1) % n τ)}

theorem cellbox_core {ell M R c k : ℕ} {S : Tower L} (s : ℕ) (hs : 2 ≤ s)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (n u : Fin 3 → ℕ) (hn : ∀ τ, L τ + 1 = s * n τ) (hu : ∀ τ, u τ < n τ)
    (two : Fin 3 → Prop) [DecidablePred two]
    (μ ν ρ : Fin 3) (hμν : μ < ν) (hρμ : ρ ≠ μ) (hρν : ρ ≠ ν) (hall : ∀ τ : Fin 3, τ = μ ∨ τ = ν ∨ τ = ρ)
    (hρ1 : ¬ two ρ)
    {Om : Set (PeriodicLatticeSite L)} (hOm0 : Om ⊆ S.Om 0)
    (hΩ : ∀ x ∈ CellReg s n u two, x ∈ Om)
    (hWidx : ∀ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i →
      (∃ y ∈ sites, y ∈ CellReg s n u two) → s ∣ bigSide M ell i) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧
      CellReg s n u two ⊆ sites := by
  have hs0 : 0 < s := by omega
  have hμν' : μ ≠ ν := ne_of_lt hμν
  have hsn : ∀ τ, s * u τ + s ≤ L τ + 1 := fun τ => by
    have h2 : s * (u τ + 1) ≤ s * n τ := Nat.mul_le_mul_left _ (hu τ)
    have h3 : s * (u τ + 1) = s * u τ + s := by ring
    have := hn τ; omega
  let yv : Fin 3 → ℕ := fun τ => if two τ then s * u τ + s - 1 else s * u τ
  have hyv_lt : ∀ τ, yv τ < L τ + 1 := by
    intro τ; have := hsn τ; simp only [yv]; split_ifs <;> omega
  let ysite : PeriodicLatticeSite L := fun τ => ⟨yv τ, hyv_lt τ⟩
  have hy1 : ∀ τ, (ysite τ).val = yv τ := fun τ => rfl
  let s1 := periodicLatticeShift ysite μ
  let s2 := periodicLatticeShift ysite ν
  let s3 := periodicLatticeShift s1 ν
  let s3' := periodicLatticeShift s2 μ
  -- cell of the base coordinate and of its successor
  have hycell : ∀ τ, yv τ / s = u τ := by
    intro τ; simp only [yv]; split_ifs
    · have : s * u τ + s - 1 = s * u τ + (s - 1) := by omega
      rw [this]; exact cell_add hs0 _ _ (by omega)
    · have := cell_add hs0 (u τ) 0 hs0; simpa using this
  let wc : Fin 3 → ℕ := fun τ => if two τ then (u τ + 1) % n τ else u τ
  have hwcell : ∀ τ, ((yv τ + 1) % (L τ + 1)) / s = wc τ := by
    intro τ
    have := hsn τ
    simp only [yv, wc]; split_ifs with h
    · have h1 : s * u τ + s - 1 + 1 = s * (u τ + 1) + 0 := by ring_nf; omega
      rw [h1, hn τ, cell_mod hs0]
      simp [Nat.mul_div_cancel_left _ hs0]
    · rw [Nat.mod_eq_of_lt (by omega)]
      rw [show s * u τ + 1 = s * u τ + 1 from rfl]
      exact cell_add hs0 _ _ (by omega)
  have hs1v : ∀ τ, (s1 τ).val = if τ = μ then (yv μ + 1) % (L μ + 1) else yv τ := by
    intro τ; rw [shift_val']
  have hs2v : ∀ τ, (s2 τ).val = if τ = ν then (yv ν + 1) % (L ν + 1) else yv τ := by
    intro τ; rw [shift_val']
  have hs3v : ∀ τ, (s3 τ).val = if τ = ν then (yv ν + 1) % (L ν + 1) else if τ = μ then (yv μ + 1) % (L μ + 1) else yv τ := by
    intro τ; rw [shift_val']
    by_cases h : τ = ν
    · subst h; simp [hs1v, hμν'.symm]
    · simp [h, hs1v]
  have hs3'v : ∀ τ, (s3' τ).val = if τ = μ then (yv μ + 1) % (L μ + 1) else if τ = ν then (yv ν + 1) % (L ν + 1) else yv τ := by
    intro τ; rw [shift_val']
    by_cases h : τ = μ
    · subst h; simp [hs2v, hμν']
    · simp [h, hs2v]
  have hv0 : ∀ τ, (ysite τ).val / s = u τ := fun τ => by rw [hy1]; exact hycell τ
  have hv1 : ∀ τ, (s1 τ).val / s = if τ = μ then wc μ else u τ := by
    intro τ; rw [hs1v]; by_cases h : τ = μ
    · subst h; simp [hwcell]
    · simp [h, hycell]
  have hv2 : ∀ τ, (s2 τ).val / s = if τ = ν then wc ν else u τ := by
    intro τ; rw [hs2v]; by_cases h : τ = ν
    · subst h; simp [hwcell]
    · simp [h, hycell]
  have hv3 : ∀ τ, (s3 τ).val / s = if τ = ν then wc ν else if τ = μ then wc μ else u τ := by
    intro τ; rw [hs3v]; by_cases h : τ = ν
    · subst h; simp [hwcell]
    · by_cases h' : τ = μ
      · subst h'; simp [h, hwcell]
      · simp [h, h', hycell]
  have hv3' : ∀ τ, (s3' τ).val / s = if τ = μ then wc μ else if τ = ν then wc ν else u τ := by
    intro τ; rw [hs3'v]; by_cases h : τ = μ
    · subst h; simp [hwcell]
    · by_cases h' : τ = ν
      · subst h'; simp [h, hwcell]
      · simp [h, h', hycell]
  -- the vertices lie in the region
  have hwc_ok : ∀ τ, wc τ = u τ ∨ (two τ ∧ wc τ = (u τ + 1) % n τ) := by
    intro τ; simp only [wc]; split_ifs with h
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl rfl
  have hreg : ∀ v : PeriodicLatticeSite L, (∀ τ, (v τ).val / s = u τ ∨ (v τ).val / s = wc τ) → v ∈ CellReg s n u two := by
    intro v hv τ
    rcases hv τ with h | h
    · exact Or.inl h
    · rw [h]; exact hwc_ok τ
  have hy_reg : ysite ∈ CellReg s n u two := hreg _ (fun τ => Or.inl (hv0 τ))
  have hs1_reg : s1 ∈ CellReg s n u two := hreg _ (fun τ => by rw [hv1]; split_ifs <;> first | exact Or.inl rfl | (subst_vars; exact Or.inr rfl))
  have hs2_reg : s2 ∈ CellReg s n u two := hreg _ (fun τ => by rw [hv2]; split_ifs <;> first | exact Or.inl rfl | (subst_vars; exact Or.inr rfl))
  have hs3_reg : s3 ∈ CellReg s n u two := hreg _ (fun τ => by rw [hv3]; split_ifs <;> first | exact Or.inl rfl | (subst_vars; exact Or.inr rfl))
  have hs3'_reg : s3' ∈ CellReg s n u two := hreg _ (fun τ => by rw [hv3']; split_ifs <;> first | exact Or.inl rfl | (subst_vars; exact Or.inr rfl))
  let pl : PeriodicLatticePlaquette L := (ysite, ⟨(μ, ν), hμν⟩)
  have hp : ∀ e ∈ periodicPlaquetteBoundaryEdges pl, CubeBond (S.Om 0) e := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, pl, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨hOm0 (hΩ _ hy_reg), hOm0 (hΩ _ hs1_reg)⟩
    · exact ⟨hOm0 (hΩ _ hs1_reg), hOm0 (hΩ _ hs3_reg)⟩
    · exact ⟨hOm0 (hΩ _ hs2_reg), hOm0 (hΩ _ hs3'_reg)⟩
    · exact ⟨hOm0 (hΩ _ hy_reg), hOm0 (hΩ _ hs2_reg)⟩
  obtain ⟨sites, i, hcl, hb⟩ := hcov.2 pl hp
  have hbm : ∀ e ∈ periodicPlaquetteBoundaryEdges pl, CubeBond sites e := hb
  have b1 := hbm (ysite, μ) (by simp [periodicPlaquetteBoundaryEdges, pl])
  have b2 := hbm (s1, ν) (by simp [periodicPlaquetteBoundaryEdges, pl, s1])
  have b3 := hbm (s2, μ) (by simp [periodicPlaquetteBoundaryEdges, pl, s2])
  have hy_s : ysite ∈ sites := b1.1
  have hs1_s : s1 ∈ sites := b1.2
  have hs3_s : s3 ∈ sites := b2.2
  have hs2_s : s2 ∈ sites := b3.1
  refine ⟨sites, i, hcl, ?_⟩
  have hWi : s ∣ bigSide M ell i := hWidx sites i hcl ⟨ysite, hy_s, hy_reg⟩
  have key : ∀ (v : PeriodicLatticeSite L) (x : PeriodicLatticeSite L), v ∈ sites →
      (∀ τ, (x τ).val / s = (v τ).val / s) → x ∈ sites :=
    fun v x hv hc => classCube_sat hadm hcl hs0 hWi hv (fun τ => (hc τ).symm)
  intro x hx
  have hxμ := hx μ
  have hxν := hx ν
  have hxρ : (x ρ).val / s = u ρ := by
    rcases hx ρ with h | ⟨h, -⟩
    · exact h
    · exact absurd h hρ1
  -- choose the vertex
  by_cases hA : (x μ).val / s = u μ <;> by_cases hB : (x ν).val / s = u ν
  · refine key ysite x hy_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hv0]; exact hA
    · rw [hv0]; exact hB
    · rw [hv0]; exact hxρ
  · have hB' : two ν ∧ (x ν).val / s = (u ν + 1) % n ν := by
      rcases hxν with h | h; exact absurd h hB; exact h
    refine key s2 x hs2_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hv2]; simp [hμν']; exact hA
    · rw [hv2]; simp [wc, hB'.1]; exact hB'.2
    · rw [hv2]; simp [hρν]; exact hxρ
  · have hA' : two μ ∧ (x μ).val / s = (u μ + 1) % n μ := by
      rcases hxμ with h | h; exact absurd h hA; exact h
    refine key s1 x hs1_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hv1]; simp [wc, hA'.1]; exact hA'.2
    · rw [hv1]; simp [hμν'.symm]; exact hB
    · rw [hv1]; simp [hρμ]; exact hxρ
  · have hA' : two μ ∧ (x μ).val / s = (u μ + 1) % n μ := by
      rcases hxμ with h | h; exact absurd h hA; exact h
    have hB' : two ν ∧ (x ν).val / s = (u ν + 1) % n ν := by
      rcases hxν with h | h; exact absurd h hB; exact h
    refine key s3 x hs3_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hv3]; simp [wc, hA'.1, hμν']; exact hA'.2
    · rw [hv3]; simp [wc, hB'.1]; exact hB'.2
    · rw [hv3]; simp [hρν, hρμ]; exact hxρ

end AdalyFormal.CoverGeom

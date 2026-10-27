import ZR6A
import ZR8Geo

/-!
# CG1 -- covering geometry for the uniform ball charts (lane cover_geom, unif_20261016)

W-cell calculus for class cubes and the box covering lemma `box_in_class_cube`.
No residual, no new axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace AdalyFormal.CoverGeom

open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle)

variable {L : PeriodicLatticeExtent}

/-- `(W m + r) mod (W n) = W (m mod n) + r` for `r < W`. -/
theorem cell_mod {W m n r : ℕ} (hr : r < W) : (W * m + r) % (W * n) = W * (m % n) + r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hW : 0 < W := by omega
    have h1 : W * m + r = (W * (m % n) + r) + (W * n) * (m / n) := by
      have := Nat.mod_add_div m n
      calc W * m + r = W * (m % n + n * (m / n)) + r := by rw [this]
        _ = _ := by ring
    rw [h1, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have : m % n < n := Nat.mod_lt _ hn
    calc W * (m % n) + r < W * (m % n) + W := by omega
      _ = W * (m % n + 1) := by ring
      _ ≤ W * n := Nat.mul_le_mul_left _ this

/-- membership of a coordinate in an aligned cyclic interval depends only on the `W`-cell -/
theorem coord_cell {W N z s a b : ℕ} (hW : 0 < W) (hN : W ∣ N) (hz : W ∣ z) (hs : W ∣ s) (hzN : z < N)
    (haN : a < N) (hab : a / W = b / W) (h : (a + N - z) % N < s) : (b + N - z) % N < s := by
  obtain ⟨n, rfl⟩ := hN
  obtain ⟨zq, rfl⟩ := hz
  obtain ⟨sq, rfl⟩ := hs
  have hzn : zq < n := by
    by_contra hc
    have : W * n ≤ W * zq := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hzn
  have hform : ∀ c : ℕ, c / W = a / W → (c + W * (zq + d + 1) - W * zq) % (W * (zq + d + 1))
      = W * ((a / W + (d + 1)) % (zq + d + 1)) + c % W := by
    intro c hc
    have hc1 : c = W * (a / W) + c % W := by rw [← hc]; exact (Nat.div_add_mod c W).symm
    have hcw : c % W < W := Nat.mod_lt _ hW
    have e1 : c + W * (zq + d + 1) - W * zq = W * (a / W + (d + 1)) + c % W := by
      have : W * (a / W + (d + 1)) = W * (a / W) + W * d + W := by ring
      have h2 : W * (zq + d + 1) = W * zq + W * d + W := by ring
      rw [this, h2]
      omega
    rw [e1]
    exact cell_mod hcw
  have hb' : b / W = a / W := hab.symm
  rw [hform a rfl] at h
  rw [hform b hb']
  have haw : a % W < W := Nat.mod_lt _ hW
  have hbw : b % W < W := Nat.mod_lt _ hW
  by_contra hcon
  have h1 : W * sq ≤ W * ((a / W + (d + 1)) % (zq + d + 1)) + b % W := by omega
  have h3 : sq ≤ (a / W + (d + 1)) % (zq + d + 1) := by
    by_contra hh
    have : (a / W + (d + 1)) % (zq + d + 1) + 1 ≤ sq := by omega
    have : W * ((a / W + (d + 1)) % (zq + d + 1) + 1) ≤ W * sq := Nat.mul_le_mul_left _ this
    have h5 : W * ((a / W + (d + 1)) % (zq + d + 1) + 1) = W * ((a / W + (d + 1)) % (zq + d + 1)) + W := by ring
    omega
  have : W * sq ≤ W * ((a / W + (d + 1)) % (zq + d + 1)) := Nat.mul_le_mul_left _ h3
  omega

/-- the finest cell width of a ball at stratum `j`: `W = M ℓ^{j-2}` (natural subtraction: `W = M` for `j ≤ 2`). -/
def cellW (ell M j : ℕ) : ℕ := M * ell ^ (j - 2)

theorem cellW_pos {ell M : ℕ} (j : ℕ) (hM : 0 < M) (hell : 0 < ell) : 0 < cellW ell M j :=
  Nat.mul_pos hM (pow_pos hell _)

theorem cellW_dvd_bigSide_of_le {ell M j i : ℕ} (h : j ≤ i + 2) : cellW ell M j ∣ bigSide M ell i := by
  unfold cellW bigSide
  exact Nat.mul_dvd_mul_left M (pow_dvd_pow ell (by omega))

theorem cellW_dvd_bigSide_pred (ell M j : ℕ) : cellW ell M j ∣ bigSide M ell (j - 1) :=
  cellW_dvd_bigSide_of_le (by omega)

/-- a class cube of index `i` is a union of `W`-cells for every `W ∣ M ℓ^i`. -/
theorem classCube_sat {ell M R c k : ℕ} {S : Tower L} (hadm : Admissible ell M R k S)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hc : IsClassCube ell M c k S sites i)
    {W : ℕ} (hW : 0 < W) (hWi : W ∣ bigSide M ell i)
    {x y : PeriodicLatticeSite L} (hx : x ∈ sites) (hxy : ∀ μ, (x μ).val / W = (y μ).val / W) :
    y ∈ sites := by
  obtain ⟨⟨hik, ⟨z, hgrid, rfl⟩, -, -⟩, -⟩ := hc
  intro μ
  have hxμ := hx μ
  refine coord_cell hW (dvd_trans hWi (hadm.2.2.1 i hik μ)) ?_ ?_ (z μ).isLt (x μ).isLt (hxy μ) hxμ
  · exact dvd_trans hWi (Nat.dvd_of_mod_eq_zero (hgrid μ))
  · exact dvd_trans hWi (dvd_mul_left _ _)

/-- the index of a class cube through a site of `Ω_{j-1}` is `≥ j-2`. -/
theorem classCube_index_ge {ell M c k : ℕ} {S : Tower L} (hmono : ∀ j, S.Om (j + 1) ⊆ S.Om j)
    {sites : Set (PeriodicLatticeSite L)} {i : ℕ} (hc : IsClassCube ell M c k S sites i) {j : ℕ}
    {y : PeriodicLatticeSite L} (hy : y ∈ sites) (hyj : y ∈ S.Om (j - 1)) : j ≤ i + 2 := by
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hmono
  obtain ⟨⟨-, -, hsub, -⟩, -⟩ := hc
  have hnot : y ∉ S.Om (i + 2) := by
    rcases hsub hy with h | h
    · intro h2; exact h.2 (hanti (by omega : i + 1 ≤ i + 2) h2)
    · exact h.2
  by_contra hcon
  exact hnot (hanti (by omega : i + 2 ≤ j - 1) hyj)

/-- `Ω_{j-1}` is a union of `W`-cells. -/
theorem om_cell_closed {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hjk : j - 1 ≤ k)
    {W : ℕ} (hW : 0 < W) (hWd : W ∣ bigSide M ell (j - 1))
    {x y : PeriodicLatticeSite L} (hx : x ∈ S.Om (j - 1)) (hxy : ∀ μ, (x μ).val / W = (y μ).val / W) :
    y ∈ S.Om (j - 1) := by
  obtain ⟨t, ht⟩ := hWd
  refine hadm.2.2.2.1 (j - 1) hjk x hx y (fun μ => ?_)
  rw [ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hxy μ]

theorem shift_val {x : PeriodicLatticeSite L} (μ τ : Fin 3) (h : (x μ).val + 1 < L μ + 1) :
    ((periodicLatticeShift x μ) τ).val = if τ = μ then (x μ).val + 1 else (x τ).val := by
  unfold periodicLatticeShift
  by_cases hτ : τ = μ
  · subst hτ
    simp only [Function.update_self, if_true]
    exact Fin.val_add_one_of_lt (Fin.lt_def.mpr (by simp; omega))
  · simp [hτ]

theorem cross_cells {W q : ℕ} (hW : 0 < W) (hq : 1 ≤ q) :
    (q * W - 1) / W = q - 1 ∧ (q * W - 1 + 1) / W = q := by
  have h1 : 1 ≤ q * W := Nat.mul_pos hq hW
  constructor
  · apply Nat.div_eq_of_lt_le
    · have : (q - 1) * W + W = q * W := by
        obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
        simp; ring
      omega
    · have : (q - 1 + 1) * W = q * W := by congr 1; omega
      omega
  · have : q * W - 1 + 1 = W * q := by rw [Nat.sub_add_cancel h1]; ring
    rw [this]; exact Nat.mul_div_cancel_left _ hW

theorem box_core {ell M R c k j : ℕ} {S : Tower L} (W : ℕ) (hW : 0 < W)
    (hWpred : W ∣ bigSide M ell (j - 1)) (hWidx : ∀ i, j ≤ i + 2 → W ∣ bigSide M ell i) (hjk : j - 1 ≤ k)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (μ ν ρ : Fin 3) (hμν : μ < ν) (hρμ : ρ ≠ μ) (hρν : ρ ≠ ν)
    (hall : ∀ τ : Fin 3, τ = μ ∨ τ = ν ∨ τ = ρ)
    (lo hi : Fin 3 → ℕ) (hle : ∀ τ, lo τ ≤ hi τ) (hhi : ∀ τ, hi τ < L τ + 1)
    (hone : ∀ τ, hi τ / W ≤ lo τ / W + 1)
    (hfree : hi ρ / W = lo ρ / W)
    (hwide : ∀ τ, τ ≠ ρ → hi τ / W ≠ lo τ / W ∨ lo τ < hi τ)
    (hΩ : ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) →
      ∃ x ∈ S.Om (j - 1), ∀ τ, (p τ).val / W = (x τ).val / W) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧ j ≤ i + 2 ∧
      ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) → p ∈ sites := by
  have hμν' : μ ≠ ν := ne_of_lt hμν
  have hmono := hadm.1
  have hanti : Antitone S.Om := antitone_nat_of_succ_le hmono
  -- base coordinates
  let yv : Fin 3 → ℕ := fun τ => if hi τ / W = lo τ / W then lo τ else (hi τ / W) * W - 1
  have hcr : ∀ τ, hi τ / W ≠ lo τ / W → hi τ / W = lo τ / W + 1 := by
    intro τ h
    have h1 := hone τ
    have h2 : lo τ / W ≤ hi τ / W := Nat.div_le_div_right (hle τ)
    omega
  have hyv_cell : ∀ τ, yv τ / W = lo τ / W := by
    intro τ
    by_cases h : hi τ / W = lo τ / W
    · simp [yv, h]
    · have hq := hcr τ h
      have hz0 := Nat.zero_le (lo τ / W)
      simp only [yv, h, if_false]
      rw [(cross_cells hW (by omega : 1 ≤ hi τ / W)).1]; omega
  have hyv_lo : ∀ τ, lo τ ≤ yv τ := by
    intro τ
    by_cases h : hi τ / W = lo τ / W
    · simp [yv, h]
    · have hq := hcr τ h
      simp only [yv, h, if_false]
      have h1 : lo τ < W * (lo τ / W) + W := by
        have := Nat.mod_lt (lo τ) hW
        have := Nat.div_add_mod (lo τ) W
        omega
      rw [hq]
      have : (lo τ / W + 1) * W = W * (lo τ / W) + W := by ring
      omega
  have hyv_hi : ∀ τ, yv τ ≤ hi τ := by
    intro τ
    by_cases h : hi τ / W = lo τ / W
    · simp only [yv, h, if_true]; exact hle τ
    · simp only [yv, h, if_false]
      have := Nat.div_mul_le_self (hi τ) W
      omega
  have hyv_hi1 : ∀ τ, τ ≠ ρ → yv τ + 1 ≤ hi τ := by
    intro τ hτ
    by_cases h : hi τ / W = lo τ / W
    · have : lo τ < hi τ := by
        rcases hwide τ hτ with h' | h'
        · exact absurd h h'
        · exact h'
      simp only [yv, h, if_true]; omega
    · simp only [yv, h, if_false]
      have hq := hcr τ h
      have hz0 := Nat.zero_le (lo τ / W)
      have := Nat.div_mul_le_self (hi τ) W
      have h1 : 1 ≤ (hi τ / W) * W := Nat.mul_pos (by omega) hW
      omega
  have hyv_pc : ∀ τ pv, lo τ ≤ pv → pv ≤ hi τ → pv / W = yv τ / W ∨ pv / W = (yv τ + 1) / W := by
    intro τ pv h1 h2
    have a1 : lo τ / W ≤ pv / W := Nat.div_le_div_right h1
    have a2 : pv / W ≤ hi τ / W := Nat.div_le_div_right h2
    by_cases h : hi τ / W = lo τ / W
    · left; rw [hyv_cell]; omega
    · have hq := hcr τ h
      by_cases h3 : pv / W = lo τ / W
      · left; rw [hyv_cell]; exact h3
      · right
        have hz0 := Nat.zero_le (lo τ / W)
        have e : (yv τ + 1) / W = hi τ / W := by
          simp only [yv, h, if_false]
          exact (cross_cells hW (by omega : 1 ≤ hi τ / W)).2
        rw [e]; omega
  have hlt : ∀ τ, yv τ < L τ + 1 := fun τ => by have := hyv_hi τ; have := hhi τ; omega
  let ysite : PeriodicLatticeSite L := fun τ => ⟨yv τ, hlt τ⟩
  have hy1 : ∀ τ, (ysite τ).val = yv τ := fun τ => rfl
  let s1 := periodicLatticeShift ysite μ
  let s2 := periodicLatticeShift ysite ν
  let s3 := periodicLatticeShift s1 ν
  let s3' := periodicLatticeShift s2 μ
  have hs1 : ∀ τ, (s1 τ).val = if τ = μ then yv μ + 1 else yv τ := by
    intro τ
    exact shift_val μ τ (by have := hyv_hi1 μ hρμ.symm; have := hhi μ; simp [hy1]; omega)
  have hs2 : ∀ τ, (s2 τ).val = if τ = ν then yv ν + 1 else yv τ := by
    intro τ
    exact shift_val ν τ (by have := hyv_hi1 ν hρν.symm; have := hhi ν; simp [hy1]; omega)
  have hs3 : ∀ τ, (s3 τ).val = if τ = ν then yv ν + 1 else (if τ = μ then yv μ + 1 else yv τ) := by
    intro τ
    have : (s1 ν).val + 1 < L ν + 1 := by
      rw [hs1 ν]; simp [hμν'.symm]; have := hyv_hi1 ν hρν.symm; have := hhi ν; omega
    rw [shift_val ν τ this, hs1 ν, hs1 τ]
    simp [hμν'.symm]
  have hs3' : ∀ τ, (s3' τ).val = if τ = μ then yv μ + 1 else (if τ = ν then yv ν + 1 else yv τ) := by
    intro τ
    have : (s2 μ).val + 1 < L μ + 1 := by
      rw [hs2 μ]; simp [hμν']; have := hyv_hi1 μ hρμ.symm; have := hhi μ; omega
    rw [shift_val μ τ this, hs2 μ, hs2 τ]
    simp [hμν']
  -- all vertices lie in the box, hence in Ω_{j-1}
  have hmem : ∀ v : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (v τ).val ∧ (v τ).val ≤ hi τ) →
      v ∈ S.Om (j - 1) := by
    intro v hv
    obtain ⟨x, hx, hxv⟩ := hΩ v hv
    exact om_cell_closed hadm hjk hW hWpred hx (fun τ => (hxv τ).symm)
  have hb1 : ∀ τ, τ ≠ ρ → yv τ + 1 ≤ hi τ := hyv_hi1
  have hy_in : ysite ∈ S.Om (j - 1) :=
    hmem _ (fun τ => by rw [hy1]; exact ⟨hyv_lo τ, hyv_hi τ⟩)
  have hs1_in : s1 ∈ S.Om (j - 1) := hmem _ (fun τ => by
    rw [hs1]; split_ifs with h
    · subst h; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρμ.symm⟩
    · exact ⟨hyv_lo τ, hyv_hi τ⟩)
  have hs2_in : s2 ∈ S.Om (j - 1) := hmem _ (fun τ => by
    rw [hs2]; split_ifs with h
    · subst h; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρν.symm⟩
    · exact ⟨hyv_lo τ, hyv_hi τ⟩)
  have hs3_in : s3 ∈ S.Om (j - 1) := hmem _ (fun τ => by
    rw [hs3]; split_ifs with h h'
    · subst h; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρν.symm⟩
    · subst h'; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρμ.symm⟩
    · exact ⟨hyv_lo τ, hyv_hi τ⟩)
  have hs3'_in : s3' ∈ S.Om (j - 1) := hmem _ (fun τ => by
    rw [hs3']; split_ifs with h h'
    · subst h; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρμ.symm⟩
    · subst h'; exact ⟨by have := hyv_lo τ; omega, hb1 τ hρν.symm⟩
    · exact ⟨hyv_lo τ, hyv_hi τ⟩)
  have h0 : ∀ v, v ∈ S.Om (j - 1) → v ∈ S.Om 0 := fun v hv => hanti (Nat.zero_le _) hv
  let pl : PeriodicLatticePlaquette L := (ysite, ⟨(μ, ν), hμν⟩)
  have hp : ∀ e ∈ periodicPlaquetteBoundaryEdges pl, CubeBond (S.Om 0) e := by
    intro e he
    simp only [periodicPlaquetteBoundaryEdges, pl, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨h0 _ hy_in, h0 _ hs1_in⟩
    · exact ⟨h0 _ hs1_in, h0 _ hs3_in⟩
    · exact ⟨h0 _ hs2_in, h0 _ hs3'_in⟩
    · exact ⟨h0 _ hy_in, h0 _ hs2_in⟩
  obtain ⟨sites, i, hcl, hb⟩ := hcov.2 pl hp
  have hbm : ∀ e ∈ periodicPlaquetteBoundaryEdges pl, CubeBond sites e := hb
  have b1 := hbm (ysite, μ) (by simp [periodicPlaquetteBoundaryEdges, pl])
  have b2 := hbm (s1, ν) (by simp [periodicPlaquetteBoundaryEdges, pl, s1])
  have b3 := hbm (s2, μ) (by simp [periodicPlaquetteBoundaryEdges, pl, s2])
  have hy_s : ysite ∈ sites := b1.1
  have hs1_s : s1 ∈ sites := b1.2
  have hs3_s : s3 ∈ sites := b2.2
  have hs2_s : s2 ∈ sites := b3.1
  have hidx : j ≤ i + 2 := classCube_index_ge hmono hcl hy_s hy_in
  refine ⟨sites, i, hcl, hidx, ?_⟩
  intro p hp'
  have hWi : W ∣ bigSide M ell i := hWidx i hidx
  have key : ∀ v, v ∈ sites → (∀ τ, (p τ).val / W = (v τ).val / W) → p ∈ sites :=
    fun v hv hc => classCube_sat hadm hcl hW hWi hv (fun τ => (hc τ).symm)
  have hρc : (p ρ).val / W = yv ρ / W := by
    rw [hyv_cell]
    have a1 : lo ρ / W ≤ (p ρ).val / W := Nat.div_le_div_right (hp' ρ).1
    have a2 : (p ρ).val / W ≤ hi ρ / W := Nat.div_le_div_right (hp' ρ).2
    omega
  have cpμ := hyv_pc μ _ (hp' μ).1 (hp' μ).2
  have cpν := hyv_pc ν _ (hp' ν).1 (hp' ν).2
  rcases cpμ with hμ0 | hμ1 <;> rcases cpν with hν0 | hν1
  · refine key ysite hy_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hy1]; exact hμ0
    · rw [hy1]; exact hν0
    · rw [hy1]; exact hρc
  · refine key s2 hs2_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hs2]; simp [hμν']; exact hμ0
    · rw [hs2]; simp; exact hν1
    · rw [hs2]; simp [hρν]; exact hρc
  · refine key s1 hs1_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hs1]; simp; exact hμ1
    · rw [hs1]; simp [hμν'.symm]; exact hν0
    · rw [hs1]; simp [hρμ]; exact hρc
  · refine key s3 hs3_s (fun τ => ?_)
    rcases hall τ with rfl | rfl | rfl
    · rw [hs3]; simp [hμν']; exact hμ1
    · rw [hs3]; simp; exact hν1
    · rw [hs3]; simp [hρν, hρμ]; exact hρc

/-- **BOX COVERING LEMMA.**  A coordinate box `[lo, hi]` of the torus that
 * meets at most two `W`-cells in each axis (`W = M ℓ^{j-2}`) and exactly one `W`-cell in at least one axis `ρ`,
 * has, in each of the other two axes, either width `≥ 2` or two `W`-cells,
 * meets only `W`-cells that meet `Ω_{j-1}`,
lies inside ONE class cube, whose index `i` satisfies `j ≤ i + 2`.  Hypotheses: `Admissible` and `CoversOm0p` only. -/
theorem box_in_class_cube {ell M R c k j : ℕ} {S : Tower L} (hM : 0 < M) (hell : 0 < ell) (hjk : j - 1 ≤ k)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (lo hi : Fin 3 → ℕ) (hle : ∀ τ, lo τ ≤ hi τ) (hhi : ∀ τ, hi τ < L τ + 1)
    (hone : ∀ τ, hi τ / cellW ell M j ≤ lo τ / cellW ell M j + 1)
    (hfree : ∃ ρ, hi ρ / cellW ell M j = lo ρ / cellW ell M j ∧
      ∀ τ, τ ≠ ρ → hi τ / cellW ell M j ≠ lo τ / cellW ell M j ∨ lo τ < hi τ)
    (hΩ : ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) →
      ∃ x ∈ S.Om (j - 1), ∀ τ, (p τ).val / cellW ell M j = (x τ).val / cellW ell M j) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧ j ≤ i + 2 ∧
      ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) → p ∈ sites := by
  obtain ⟨ρ, hρ, hwd⟩ := hfree
  have hW := cellW_pos j hM hell
  have hWp := cellW_dvd_bigSide_pred ell M j
  have hWi : ∀ i, j ≤ i + 2 → cellW ell M j ∣ bigSide M ell i := fun i h => cellW_dvd_bigSide_of_le h
  fin_cases ρ
  · exact box_core (cellW ell M j) hW hWp hWi hjk hadm hcov 1 2 0 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) lo hi hle hhi hone hρ hwd hΩ
  · exact box_core (cellW ell M j) hW hWp hWi hjk hadm hcov 0 2 1 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) lo hi hle hhi hone hρ hwd hΩ
  · exact box_core (cellW ell M j) hW hWp hWi hjk hadm hcov 0 1 2 (by decide) (by decide) (by decide)
      (by intro τ; fin_cases τ <;> simp) lo hi hle hhi hone hρ hwd hΩ

theorem succ_div_le {a W : ℕ} (hW : 0 < W) : (a + 1) / W ≤ a / W + 1 := by
  have h1 := Nat.div_add_mod a W
  have h2 := Nat.mod_lt a hW
  have : (a + 1) / W < a / W + 2 := by
    rw [Nat.div_lt_iff_lt_mul hW]
    have e : (a / W + 2) * W = W * (a / W) + 2 * W := by ring
    omega
  omega

/-- **UNIT-CELL COVERING.**  The 8 vertices `x + {0,1}^3` of a unit 3-cell lie in one class cube as soon as the cell does not cross a `W`-plane in at least one axis
(`x_ρ / W = (x_ρ + 1) / W`), i.e. unless it is centred at a `W`-vertex. -/
theorem unitCell_in_class_cube {ell M R c k j : ℕ} {S : Tower L} (hM : 0 < M) (hell : 0 < ell) (hjk : j - 1 ≤ k)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (x : PeriodicLatticeSite L) (hx : ∀ τ, (x τ).val + 1 < L τ + 1)
    (hfree : ∃ ρ, (x ρ).val / cellW ell M j = ((x ρ).val + 1) / cellW ell M j)
    (hΩ : ∀ p : PeriodicLatticeSite L, (∀ τ, (x τ).val ≤ (p τ).val ∧ (p τ).val ≤ (x τ).val + 1) →
      ∃ y ∈ S.Om (j - 1), ∀ τ, (p τ).val / cellW ell M j = (y τ).val / cellW ell M j) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧ j ≤ i + 2 ∧
      ∀ p : PeriodicLatticeSite L, (∀ τ, (x τ).val ≤ (p τ).val ∧ (p τ).val ≤ (x τ).val + 1) → p ∈ sites := by
  have hW := cellW_pos j hM hell
  obtain ⟨ρ, hρ⟩ := hfree
  exact box_in_class_cube hM hell hjk hadm hcov (fun τ => (x τ).val) (fun τ => (x τ).val + 1)
    (fun τ => Nat.le_succ _) (fun τ => hx τ) (fun τ => succ_div_le hW)
    ⟨ρ, hρ.symm, fun τ _ => Or.inr (Nat.lt_succ_self _)⟩ hΩ

/-- consumer form for balls: a box inside `Ball w r ⊆ Ω_{j-1}` needs no cell hypothesis. -/
theorem box_in_class_cube_of_ball {ell M R c k j : ℕ} {S : Tower L} (hM : 0 < M) (hell : 0 < ell) (hjk : j - 1 ≤ k)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (lo hi : Fin 3 → ℕ) (hle : ∀ τ, lo τ ≤ hi τ) (hhi : ∀ τ, hi τ < L τ + 1)
    (hone : ∀ τ, hi τ / cellW ell M j ≤ lo τ / cellW ell M j + 1)
    (hfree : ∃ ρ, hi ρ / cellW ell M j = lo ρ / cellW ell M j ∧
      ∀ τ, τ ≠ ρ → hi τ / cellW ell M j ≠ lo τ / cellW ell M j ∨ lo τ < hi τ)
    {w : PeriodicLatticeSite L} {r : ℕ} (hball : ∀ x ∈ Ball w r, x ∈ S.Om (j - 1))
    (hbox : ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) → p ∈ Ball w r) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧ j ≤ i + 2 ∧
      ∀ p : PeriodicLatticeSite L, (∀ τ, lo τ ≤ (p τ).val ∧ (p τ).val ≤ hi τ) → p ∈ sites :=
  box_in_class_cube hM hell hjk hadm hcov lo hi hle hhi hone hfree
    (fun p hp => ⟨p, hball p (hbox p hp), fun τ => rfl⟩)

/-- collar: for `j ≥ 1`, `R ≥ 10 ℓ + 1`, every site within `7 M ℓ^j + M ℓ^{j-1}` of the centre `w` (which is within `3 M ℓ^j` of `Ω_j`) lies in `Ω_{j-1}`. -/
theorem near_ball_in_Om {ell M R k j : ℕ} {S : Tower L} (hadm : Admissible ell M R k S) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hR : 10 * ell + 1 ≤ R) {w x₀ p : PeriodicLatticeSite L} (hx₀ : x₀ ∈ S.Om j)
    (hw : pdist w x₀ ≤ 3 * (M * ell ^ j)) (hp : pdist w p ≤ 7 * (M * ell ^ j) + M * ell ^ (j - 1)) :
    p ∈ S.Om (j - 1) := by
  by_contra hnot
  have h5 := hadm.2.2.2.2.1 (j - 1) (by omega) p hnot x₀ (by
    have : j - 1 + 1 = j := by omega
    rw [this]; exact hx₀)
  have htri : pdist p x₀ ≤ pdist p w + pdist w x₀ := pdist_triangle p w x₀
  rw [pdist_comm p w] at htri
  have hpow : ell ^ j = ell ^ (j - 1) * ell := by
    rw [← pow_succ]; congr 1; omega
  unfold bigSide at h5
  have e1 : M * ell ^ j = ell * (M * ell ^ (j - 1)) := by rw [hpow]; ring
  have e2 : R * (M * ell ^ (j - 1)) ≥ (10 * ell + 1) * (M * ell ^ (j - 1)) := Nat.mul_le_mul_right _ hR
  have e3 : (10 * ell + 1) * (M * ell ^ (j - 1)) = 7 * (ell * (M * ell ^ (j - 1))) + M * ell ^ (j - 1) + 3 * (ell * (M * ell ^ (j - 1))) := by ring
  rw [e1] at hw hp
  omega

/-- **whole-cell boxes.**  The box of `n_τ ∈ {1,2}` consecutive `W`-cells from cell `u_τ` in each axis, with `n_ρ = 1` for some `ρ` (and `W ≥ 2` unless
`n = 2` off `ρ`), lies in one class cube. -/
theorem cells_in_class_cube {ell M R c k j : ℕ} {S : Tower L} (hM : 0 < M) (hell : 0 < ell) (hjk : j - 1 ≤ k)
    (hadm : Admissible ell M R k S) (hcov : CoversOm0p ell M c k S)
    (u n : Fin 3 → ℕ) (hn : ∀ τ, n τ = 1 ∨ n τ = 2) (ρ : Fin 3) (hρ : n ρ = 1)
    (hW2 : ∀ τ, τ ≠ ρ → n τ = 2 ∨ 2 ≤ cellW ell M j)
    (hN : ∀ τ, cellW ell M j * (u τ + n τ) ≤ L τ + 1)
    (hΩ : ∀ p : PeriodicLatticeSite L, (∀ τ, cellW ell M j * u τ ≤ (p τ).val ∧ (p τ).val < cellW ell M j * (u τ + n τ)) →
      ∃ x ∈ S.Om (j - 1), ∀ τ, (p τ).val / cellW ell M j = (x τ).val / cellW ell M j) :
    ∃ (sites : Set (PeriodicLatticeSite L)) (i : ℕ), IsClassCube ell M c k S sites i ∧ j ≤ i + 2 ∧
      ∀ p : PeriodicLatticeSite L, (∀ τ, cellW ell M j * u τ ≤ (p τ).val ∧ (p τ).val < cellW ell M j * (u τ + n τ)) →
        p ∈ sites := by
  have hW := cellW_pos j hM hell
  set W := cellW ell M j with hWdef
  have hlo : ∀ τ, (W * u τ) / W = u τ := fun τ => Nat.mul_div_cancel_left _ hW
  have hhiq : ∀ τ, (W * (u τ + n τ) - 1) / W = u τ + n τ - 1 := by
    intro τ
    have hq : 1 ≤ u τ + n τ := by have := hn τ; omega
    have := (cross_cells (W := W) (q := u τ + n τ) hW hq).1
    rwa [mul_comm (u τ + n τ) W] at this
  have hpos : ∀ τ, 1 ≤ W * (u τ + n τ) := fun τ => by
    have := hn τ
    exact Nat.mul_pos hW (by omega)
  obtain ⟨sites, i, hcl, hidx, hall⟩ := box_in_class_cube (c := c) (S := S) hM hell hjk hadm hcov
    (fun τ => W * u τ) (fun τ => W * (u τ + n τ) - 1)
    (fun τ => by
      have h1 := hn τ
      have : W * u τ ≤ W * (u τ + n τ) := Nat.mul_le_mul_left _ (by omega)
      have h2 : W * (u τ + n τ) = W * u τ + W * n τ := by ring
      have h3 : 1 ≤ W * n τ := Nat.mul_pos hW (by omega)
      omega)
    (fun τ => by have := hN τ; have := hpos τ; omega)
    (fun τ => by
      show (W * (u τ + n τ) - 1) / W ≤ (W * u τ) / W + 1
      rw [hhiq, hlo]; have := hn τ; omega)
    ⟨ρ, by show (W * (u ρ + n ρ) - 1) / W = (W * u ρ) / W; rw [hhiq, hlo, hρ]; omega,
      fun τ hτ => by
        rcases hW2 τ hτ with h | h
        · left
          show (W * (u τ + n τ) - 1) / W ≠ (W * u τ) / W
          rw [hhiq, hlo, h]; omega
        · right
          show W * u τ < W * (u τ + n τ) - 1
          have h1 := hn τ
          have h2 : W * (u τ + n τ) = W * u τ + W * n τ := by ring
          have h3 : W * 1 ≤ W * n τ := Nat.mul_le_mul_left _ (by omega)
          have h4 : 2 ≤ W * n τ := by
            rcases h1 with h1 | h1
            · rw [h1]; omega
            · rw [h1]; omega
          omega⟩
    (fun p hp => hΩ p (fun τ => ⟨(hp τ).1, by have := (hp τ).2; have := hpos τ; omega⟩))
  exact ⟨sites, i, hcl, hidx, fun p hp => hall p (fun τ => ⟨(hp τ).1, by have := (hp τ).2; omega⟩)⟩

end AdalyFormal.CoverGeom

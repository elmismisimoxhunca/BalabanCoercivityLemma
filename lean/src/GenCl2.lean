import GenCl1
import NC4

/-!
# GenCl2 -- the isolated-block tower and its uncovered site (lane general_class_20261015)

Fine torus side `N = ell(5RM+17M)` (NC4's `ncLu`, `ncN`), height `k = 1`.  With `s = M·ell` (a level-1 big block):
* `Ω₁ = {P1 ≤ x₀ < Q1}` (NC4's thick slab, carrying `Λ`) `∪` ONE isolated level-1 block
  `[P1', P1'+s) × [s, 2s) × [s, 2s)` (`P1' = ell(4RM+5M)`);
* `Ω₀` is DEFINED by the printed base law (p.396): the union of the `M`-blocks within `ℓ¹`-distance `RM` of `Ω₁`;
* `Ω_j = ∅`, `j ≥ 2`.
`gc_admissible`: the tower is `Admissible` (any `ell, M ≥ 1`, `R`).
`gc_uncoveredW`: if `2F ≤ ell` and `F ≤ R + 1`, the centre `x_c` of the isolated block lies in NO set of the non-box superset
`IsClassSetW .. F ..` (index 0: a set of extent `≤ F M` through `x_c` stays inside the block, so it misses `B⁰`; index 1: a set
inside `Ω₁` meeting two level-1 blocks reaches the thick slab, farther than `F M ell` from `x_c`).
Hence (GenCl1 `isClassCubeG_toW`) `x_c` lies in no general class cube of any factor `f ≤ F`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 16000000

namespace AdalyFormal.GeneralClass

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.NoCover
open AdalyFormal.NonVac (pcd_self' iv_iff iv_block mem_box_N shift_val_N pcd_gt_right2 pcd_gt_left2)

abbrev GSite (ell M R : ℕ) := PeriodicLatticeSite (scaleUp ell 1 (ncLu M R))

/-- `Ω₁`: the thick slab and one isolated level-1 block. -/
def gcOm1 (ell M R : ℕ) : Set (GSite ell M R) :=
  {x | (ncP1 ell M R ≤ (x 0).val ∧ (x 0).val < ncQ1 ell M R) ∨
    ((ncP1' ell M R ≤ (x 0).val ∧ (x 0).val < ncP1' ell M R + M * ell) ∧
      (M * ell ≤ (x 1).val ∧ (x 1).val < 2 * (M * ell)) ∧ (M * ell ≤ (x 2).val ∧ (x 2).val < 2 * (M * ell)))}

/-- `Ω₀` by the printed base law. -/
def gcOm0 (ell M R : ℕ) : Set (GSite ell M R) :=
  {x | ∃ y ∈ gcOm1 ell M R, ∃ z : GSite ell M R, (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M}

def gcS (ell M R : ℕ) : Tower (scaleUp ell 1 (ncLu M R)) :=
  ⟨fun j => if j = 0 then gcOm0 ell M R else if j = 1 then gcOm1 ell M R else ∅⟩

theorem gcS_om0 (ell M R : ℕ) : (gcS ell M R).Om 0 = gcOm0 ell M R := by simp [gcS]
theorem gcS_om1 (ell M R : ℕ) : (gcS ell M R).Om 1 = gcOm1 ell M R := by simp [gcS]
theorem gcS_omHi (ell M R : ℕ) (j : ℕ) (hj : 2 ≤ j) : (gcS ell M R).Om j = ∅ := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [gcS, h0, h1]

theorem pdist_self' {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) : pdist x x = 0 := by
  unfold pdist; simp [pcd_self']

theorem gcOm1_sub (ell M R : ℕ) : gcOm1 ell M R ⊆ gcOm0 ell M R :=
  fun x hx => ⟨x, hx, x, fun _ => rfl, by rw [pdist_self']; exact Nat.zero_le _⟩

theorem blk_div {s lo x : ℕ} (hs : 0 < s) (hlo : s ∣ lo) (hx : lo ≤ x ∧ x < lo + s) : x / s = lo / s := by
  obtain ⟨t, rfl⟩ := hlo
  rw [Nat.mul_div_cancel_left t hs]
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm]; exact hx.1
  · rw [add_mul, one_mul, mul_comm]; exact hx.2

theorem gc_admissible {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) : Admissible ell M R 1 (gcS ell M R) := by
  have hN := nc_scaleUp (ell := ell) (R := R) hell hM
  obtain ⟨e1, e2, e3, -, e5⟩ := nc_expand ell M R
  have hs : 0 < M * ell := Nat.mul_pos hM hell
  have dX : M * ell ∣ ell * (R * M) := ⟨R, by ring⟩
  have dY : M * ell ∣ ell * M := ⟨1, by ring⟩
  have dP1 : M * ell ∣ ncP1 ell M R := by rw [e1]; exact Nat.dvd_add dX dY
  have dQ1 : M * ell ∣ ncQ1 ell M R := by rw [e2]; exact Nat.dvd_add (Dvd.dvd.mul_left dX 3) (Dvd.dvd.mul_left dY 4)
  have dP1' : M * ell ∣ ncP1' ell M R := by rw [e3]; exact Nat.dvd_add (Dvd.dvd.mul_left dX 4) (Dvd.dvd.mul_left dY 5)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h0 : j = 0
    · subst h0; rw [gcS_om1, gcS_om0]; exact gcOm1_sub ell M R
    · rw [gcS_omHi ell M R (j + 1) (by omega)]; exact Set.empty_subset _
  · intro j hj; exact gcS_omHi ell M R j (by omega)
  · intro j hj μ
    rw [hN μ, e5]
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp only [bigSide, pow_zero, mul_one]
      exact ⟨5 * (ell * R) + 17 * ell, by ring⟩
    · simp only [bigSide, pow_one]
      exact Nat.dvd_add (Dvd.dvd.mul_left dX 5) (Dvd.dvd.mul_left dY 17)
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [gcS_om0]
      rintro x ⟨y', hy', z, hz, hd⟩ y hy
      simp only [bigSide, pow_zero, mul_one] at hy
      exact ⟨y', hy', z, fun μ => (hz μ).trans (hy μ).symm, hd⟩
    · rw [gcS_om1]
      intro x hx y hy
      simp only [bigSide, pow_one] at hy
      rcases hx with hx | ⟨h0, h1, h2⟩
      · exact Or.inl (iv_block hs dP1 dQ1 (hy 0) hx)
      · refine Or.inr ⟨iv_block hs dP1' (Nat.dvd_add dP1' (dvd_refl _)) (hy 0) h0,
          iv_block hs (dvd_refl _) (Dvd.dvd.mul_left (dvd_refl _) 2) (hy 1) h1,
          iv_block hs (dvd_refl _) (Dvd.dvd.mul_left (dvd_refl _) 2) (hy 2) h2⟩
  · intro j hj x hx y hy
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · rw [gcS_om0] at hx; rw [gcS_om1] at hy
      simp only [bigSide, pow_zero, mul_one]
      by_contra hc
      exact hx ⟨y, hy, x, fun _ => rfl, by omega⟩
    · rw [gcS_omHi ell M R 2 le_rfl] at hy; exact hy.elim
  · intro x
    rw [gcS_om0, gcS_om1]
    exact Iff.rfl

/-! ## arithmetic windows -/

theorem win (N x z w lo W A H : ℕ) (hx : x = lo + H) (hxN : x < N) (hzN : z < N) (hwN : w < N)
    (h1 : (x + N - z) % N < A) (h2 : (w + N - z) % N < A) (hA : A ≤ H) (hHA : H + A ≤ W) (hlo : lo + W ≤ N) :
    lo ≤ w ∧ w < lo + W := by
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hwN hzN] at h2
  split_ifs at h1 h2 <;> omega

theorem win2 (N x z c A : ℕ) (hxN : x < N) (hzN : z < N) (hcN : c < N)
    (h1 : (x + N - z) % N < A) (h2 : (c + N - z) % N < A) (hcx : c < x) (hA1 : A ≤ x - c) (hA2 : A ≤ c + N - x) : False := by
  rw [off_cases N _ _ hxN hzN] at h1
  rw [off_cases N _ _ hcN hzN] at h2
  split_ifs at h1 h2 <;> omega

/-! ## the centre of the isolated block -/

/-- `x_c = (P1' + M⌊ell/2⌋, s + M⌊ell/2⌋, s + M⌊ell/2⌋)`, `s = M ell`. -/
def xcG (ell M R : ℕ) (hell : 0 < ell) (hM : 0 < M) : GSite ell M R :=
  fun μ => ⟨if μ = 0 then ncP1' ell M R + M * (ell / 2) else M * ell + M * (ell / 2), by
    have h := nc_scaleUp (ell := ell) (R := R) hell hM μ
    obtain ⟨-, -, e3, -, e5⟩ := nc_expand ell M R
    have hh : M * (ell / 2) ≤ M * ell := Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    have hme : M * ell = ell * M := Nat.mul_comm _ _
    split_ifs <;> omega⟩

theorem xcG_val {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) :
    ((xcG ell M R hell hM) 0).val = ncP1' ell M R + M * (ell / 2) ∧
    ((xcG ell M R hell hM) 1).val = M * ell + M * (ell / 2) ∧
    ((xcG ell M R hell hM) 2).val = M * ell + M * (ell / 2) := by
  simp [xcG]

theorem half_lt {ell : ℕ} (hell : 0 < ell) : ell / 2 < ell := Nat.div_lt_self hell (by norm_num)

theorem xcG_om1 {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) : xcG ell M R hell hM ∈ gcOm1 ell M R := by
  obtain ⟨h0, h1, h2⟩ := xcG_val (R := R) hell hM
  have hh : M * (ell / 2) < M * ell := Nat.mul_lt_mul_of_pos_left (half_lt hell) hM
  right
  rw [h0, h1, h2]
  omega

theorem xcG_om0 {ell M R : ℕ} (hell : 0 < ell) (hM : 0 < M) : xcG ell M R hell hM ∈ (gcS ell M R).Om 0 := by
  rw [gcS_om0]; exact gcOm1_sub ell M R (xcG_om1 hell hM)

/-- **the centre of the isolated block is in no set of the non-box superset `IsClassSetW .. F ..`** (`2F ≤ ell`, `F ≤ R + 1`). -/
theorem gc_uncoveredW {ell M R F : ℕ} (hell : 0 < ell) (hM : 0 < M) (hF2 : 2 * F ≤ ell) (hFR : F ≤ R + 1)
    (sites : Set (GSite ell M R)) (j : ℕ) (hW : IsClassSetW ell M F 1 (gcS ell M R) sites j) :
    xcG ell M R hell hM ∉ sites := by
  obtain ⟨hj, hsub, ⟨w, hw, hwB⟩, ⟨z, hbox⟩, a, ha, b, hb, μ, hab⟩ := hW
  intro hx
  have hN := nc_scaleUp (ell := ell) (R := R) hell hM
  obtain ⟨e1, e2, e3, -, e5⟩ := nc_expand ell M R
  have hlt : ∀ y : GSite ell M R, ∀ ν, (y ν).val < ncN ell M R := fun y ν => by
    have := (y ν).isLt; have := hN ν; omega
  obtain ⟨hx0, hx1, hx2⟩ := xcG_val (R := R) hell hM
  have hme : M * ell = ell * M := Nat.mul_comm _ _
  have hFh : F ≤ ell / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hh2 : 2 * (ell / 2) ≤ ell := Nat.mul_div_le ell 2
  have hA : F * M ≤ M * (ell / 2) := by rw [mul_comm F M]; exact Nat.mul_le_mul_left _ hFh
  have hHA : M * (ell / 2) + F * M ≤ M * ell := by
    have : (ell / 2) + F ≤ ell := by omega
    have := Nat.mul_le_mul_left M this
    rw [mul_add] at this; rw [mul_comm F M]; exact this
  have hXR : 0 ≤ ell * (R * M) := Nat.zero_le _
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · -- index 0: the window of side `F M` through `x_c` stays inside the isolated block
    simp only [bigSide, pow_zero, mul_one] at hbox
    have bx := (mem_box_N hN z _ _).1 (hbox hx)
    have bw := (mem_box_N hN z _ _).1 (hbox hw)
    rw [hx0, hx1, hx2] at bx
    have w0 := win (ncN ell M R) _ _ _ (ncP1' ell M R) (M * ell) (F * M) (M * (ell / 2)) rfl
      (by rw [← hx0]; exact hlt _ 0) (hlt z 0) (hlt w 0) bx.1 bw.1 hA hHA (by rw [e3, e5]; omega)
    have w1 := win (ncN ell M R) _ _ _ (M * ell) (M * ell) (F * M) (M * (ell / 2)) rfl
      (by rw [← hx1]; exact hlt _ 1) (hlt z 1) (hlt w 1) bx.2.1 bw.2.1 hA hHA (by rw [e5]; omega)
    have w2 := win (ncN ell M R) _ _ _ (M * ell) (M * ell) (F * M) (M * (ell / 2)) rfl
      (by rw [← hx2]; exact hlt _ 2) (hlt z 2) (hlt w 2) bx.2.2 bw.2.2 hA hHA (by rw [e5]; omega)
    have hw1 : w ∈ (gcS ell M R).Om 1 := by
      rw [gcS_om1]; right; refine ⟨w0, ⟨w1.1, by omega⟩, ⟨w2.1, by omega⟩⟩
    exact hwB.2 hw1
  · -- index 1: inside `Ω₁`, two different level-1 blocks force a point of the thick slab into the window
    simp only [bigSide, pow_one] at hbox hab
    have inOm1 : ∀ y ∈ sites, y ∈ gcOm1 ell M R := by
      intro y hy
      rcases hsub hy with h | h
      · have := h.1; rw [gcS_om1] at this; exact this
      · have := h.1; rw [gcS_omHi ell M R 2 le_rfl] at this; exact this.elim
    have hs : 0 < M * ell := Nat.mul_pos hM hell
    have dP1' : M * ell ∣ ncP1' ell M R := by
      rw [e3]; exact Nat.dvd_add (Dvd.dvd.mul_left ⟨R, by ring⟩ 4) (Dvd.dvd.mul_left ⟨1, by ring⟩ 5)
    have blk : ∀ y : GSite ell M R,
        ((ncP1' ell M R ≤ (y 0).val ∧ (y 0).val < ncP1' ell M R + M * ell) ∧
          (M * ell ≤ (y 1).val ∧ (y 1).val < 2 * (M * ell)) ∧ (M * ell ≤ (y 2).val ∧ (y 2).val < 2 * (M * ell))) →
        ∀ ν : Fin 3, (y ν).val / (M * ell) = (if ν = 0 then ncP1' ell M R else M * ell) / (M * ell) := by
      intro y ⟨h0, h1, h2⟩ ν
      have hν : ν = 0 ∨ ν = 1 ∨ ν = 2 := by omega
      rcases hν with rfl | rfl | rfl
      · simpa using blk_div hs dP1' h0
      · simpa using blk_div hs (dvd_refl _) (by omega : M * ell ≤ (y 1).val ∧ (y 1).val < M * ell + M * ell)
      · simpa using blk_div hs (dvd_refl _) (by omega : M * ell ≤ (y 2).val ∧ (y 2).val < M * ell + M * ell)
    -- one of `a`, `b` is in the thick slab
    have hslab : ∃ c ∈ sites, ncP1 ell M R ≤ (c 0).val ∧ (c 0).val < ncQ1 ell M R := by
      rcases inOm1 a ha with hA' | hA'
      · exact ⟨a, ha, hA'⟩
      rcases inOm1 b hb with hB' | hB'
      · exact ⟨b, hb, hB'⟩
      exact (hab ((blk a hA' μ).trans (blk b hB' μ).symm)).elim
    obtain ⟨c, hc, hc0, hc1⟩ := hslab
    have bx := (mem_box_N hN z _ _).1 (hbox hx)
    have bc := (mem_box_N hN z _ _).1 (hbox hc)
    have hFs : F * (M * ell) ≤ ell * (R * M) + ell * M := by
      have := Nat.mul_le_mul_right (M * ell) hFR
      calc F * (M * ell) ≤ (R + 1) * (M * ell) := this
        _ = ell * (R * M) + ell * M := by ring
    have hhs : M * (ell / 2) < M * ell := Nat.mul_lt_mul_of_pos_left (half_lt hell) hM
    rw [e1] at hc0; rw [e2] at hc1
    exact win2 (ncN ell M R) _ _ _ (F * (M * ell)) (hlt _ 0) (hlt z 0) (hlt c 0) bx.1 bc.1
      (by rw [hx0, e3]; omega) (by rw [hx0, e3]; omega) (by rw [hx0, e3, e5]; omega)

/-- hence: in no general class cube of factor `f ≤ F`. -/
theorem gc_uncoveredG {ell M R F : ℕ} (hell : 0 < ell) (hM : 0 < M) (hF2 : 2 * F ≤ ell) (hFR : F ≤ R + 1)
    (f : ℕ) (sites : Set (GSite ell M R)) (j : ℕ) (hf : f ≤ F) (hq : IsClassCubeG ell M f 1 (gcS ell M R) sites j) :
    xcG ell M R hell hM ∉ sites := by
  have hN := nc_scaleUp (ell := ell) (R := R) hell hM
  obtain ⟨-, -, -, -, e5⟩ := nc_expand ell M R
  have hj : j ≤ 1 := hq.2.1.1
  have hs : 0 < bigSide M ell j := Nat.mul_pos hM (pow_pos hell j)
  have h2 : 2 * bigSide M ell j ≤ scaleUp ell 1 (ncLu M R) 0 + 1 := by
    rw [hN 0, e5]
    have : j = 0 ∨ j = 1 := by omega
    have hme : M * ell = ell * M := Nat.mul_comm _ _
    have hMl : M ≤ M * ell := Nat.le_mul_of_pos_right M hell
    rcases this with rfl | rfl <;> simp only [bigSide, pow_zero, pow_one, mul_one] <;> omega
  exact gc_uncoveredW hell hM hF2 hFR sites j (isClassCubeG_toW hq hf hs h2)

/-- general-class coverage fails on the isolated-block tower. -/
theorem gc_not_coversG {ell M R F : ℕ} (hell : 0 < ell) (hM : 0 < M) (hF2 : 2 * F ≤ ell) (hFR : F ≤ R + 1) :
    ¬ CoversOm0G ell M F 1 (gcS ell M R) := by
  intro h
  obtain ⟨f, sites, j, hf, hq, hx⟩ := h _ (xcG_om0 (R := R) hell hM)
  exact gc_uncoveredG hell hM hF2 hFR f sites j hf hq hx

#print axioms gc_admissible
#print axioms xcG_om0
#print axioms gc_uncoveredW
#print axioms gc_uncoveredG
#print axioms gc_not_coversG

end AdalyFormal.GeneralClass

import NsPtA

/-!
# PtA2 -- the abstract three-level chain (lane omega/near2/point)

`chain_main`: a function `g` on `N^3` (values in a real vector space) with the left boundary value `0`, the right boundary value `kappa`,
and the cube-sum row relations of the nested tower (level 1 along x0 on the three level-1 regions, level 1 transversally in the gap, level 2 along x0 on the two
level-2 regions) has `kappa = 0`, all level-1 cube sums over `Lambda_1` vanish and all level-2 cube sums over `Lambda_2` vanish.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.CoverOmega

open Finset

section chain
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem step_le {m x y : ℕ} (hx : m ∣ x) (hy : m ∣ y) (h : x < y) : x + m ≤ y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at h
    · exact h0
  have : s < t := Nat.lt_of_mul_lt_mul_left h
  nlinarith

/-- generic chain: a relation `f (Y+m) = f Y` on admissible `Y` gives constancy along multiples of `m`. -/
theorem chain_gen (f : ℕ → E) (m lo hi : ℕ)
    (hrel : ∀ Y, m ∣ Y → lo ≤ Y → Y + m ≤ hi → f (Y + m) = f Y) :
    ∀ s t, m ∣ s → m ∣ t → lo ≤ s → s ≤ t → t ≤ hi → f t = f s := by
  intro s t hs ht hlo hst hth
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := ht
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  · have hab : a ≤ b := Nat.le_of_mul_le_mul_left hst h0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    have key := const_chain f (m * a) m k (fun i hik => by
      have h1 : m ∣ m * a + i * m := dvd_add (dvd_mul_right m a) (dvd_mul_left m i)
      have h2 : lo ≤ m * a + i * m := by omega
      have h3 : m * a + i * m + m ≤ hi := by
        have h4 : (i + 1) * m ≤ k * m := Nat.mul_le_mul_right m hik
        have e : m * (a + k) = m * a + k * m := by ring
        have e2 : (i + 1) * m = i * m + m := by ring
        omega
      have := hrel (m * a + i * m) h1 h2 h3
      rw [show m * a + (i + 1) * m = m * a + i * m + m by ring]
      exact this) k le_rfl
    rw [show m * (a + k) = m * a + k * m by ring]
    exact key

theorem sum3_const (ell : ℕ) (v : E) :
    ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ k ∈ range ell, v = ((ell : ℝ) ^ 3) • v := by
  simp only [Finset.sum_const, Finset.card_range]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1; ring

theorem cube2_split (g : ℕ → ℕ → ℕ → E) (ell a b c : ℕ) :
    cube g (ell ^ 2) a b c = ∑ i ∈ range ell, ∑ j ∈ range ell, ∑ k ∈ range ell,
      cube g ell (a + ell * i) (b + ell * j) (c + ell * k) := by
  rw [pow_two]
  exact cube_tower g ell ell a b c

theorem cube2_of_const (g : ℕ → ℕ → ℕ → E) (ell a b c : ℕ) (v : E)
    (h : ∀ i j k, i < ell → j < ell → k < ell → cube g ell (a + ell * i) (b + ell * j) (c + ell * k) = v) :
    cube g (ell ^ 2) a b c = ((ell : ℝ) ^ 3) • v := by
  rw [cube2_split, ← sum3_const ell v]
  refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => ?_)))
  exact h i j k (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)

theorem chain_main (ell p1 a' b' a b q1 N : ℕ) (hell : 0 < ell)
    (hNd : ell ^ 2 ∣ N)
    (d1p : ell ∣ p1) (d1q : ell ∣ q1)
    (d2a' : ell ^ 2 ∣ a') (d2b' : ell ^ 2 ∣ b') (d2a : ell ^ 2 ∣ a) (d2b : ell ^ 2 ∣ b)
    (hNpos : 0 < N) (hp : ell ≤ p1) (hpa : p1 + ell ^ 2 ≤ a') (hab : a' < b') (hba : b' + ell ^ 2 ≤ a) (hab2 : a < b)
    (hbq : b + ell ^ 2 ≤ q1)
    (g : ℕ → ℕ → ℕ → E) (κ : E)
    (hL : ∀ x, x < p1 → ∀ y z, g x y z = 0)
    (hR : ∀ x, q1 ≤ x → x < q1 + ell → ∀ y z, g x y z = κ)
    (h1 : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
        ((p1 ≤ Y0 + ell ∧ Y0 + 2 * ell ≤ a') ∨ (b' ≤ Y0 ∧ Y0 + 2 * ell ≤ a) ∨ (b ≤ Y0 ∧ Y0 + ell ≤ q1)) →
        cube g ell (Y0 + ell) Y1 Y2 = cube g ell Y0 Y1 Y2)
    (h1y : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 + ell < N → Y2 < N → b' ≤ Y0 → Y0 + ell ≤ a →
        cube g ell Y0 (Y1 + ell) Y2 = cube g ell Y0 Y1 Y2)
    (h1z : ∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 + ell < N → b' ≤ Y0 → Y0 + ell ≤ a →
        cube g ell Y0 Y1 (Y2 + ell) = cube g ell Y0 Y1 Y2)
    (h2 : ∀ Y0 Y1 Y2, ell ^ 2 ∣ Y0 → ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < N → Y2 < N →
        ((a' ≤ Y0 + ell ^ 2 ∧ Y0 + ell ^ 2 ≤ b') ∨ (a ≤ Y0 + ell ^ 2 ∧ Y0 + ell ^ 2 ≤ b)) →
        cube g (ell ^ 2) (Y0 + ell ^ 2) Y1 Y2 = cube g (ell ^ 2) Y0 Y1 Y2) :
    κ = 0 ∧
    (∀ Y0 Y1 Y2, ell ∣ Y0 → ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ((p1 ≤ Y0 ∧ Y0 < a') ∨ (b' ≤ Y0 ∧ Y0 < a) ∨ (b ≤ Y0 ∧ Y0 < q1)) → cube g ell Y0 Y1 Y2 = 0) ∧
    (∀ Y0 Y1 Y2, ell ^ 2 ∣ Y0 → ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < N → Y2 < N →
      ((a' ≤ Y0 ∧ Y0 < b') ∨ (a ≤ Y0 ∧ Y0 < b)) → cube g (ell ^ 2) Y0 Y1 Y2 = 0) := by
  have hell2 : ell ∣ ell ^ 2 := dvd_pow_self ell (by norm_num)
  have hl2 : ell ≤ ell ^ 2 := Nat.le_of_dvd (pow_pos hell 2) hell2
  have dla' : ell ∣ a' := dvd_trans hell2 d2a'
  have dlb' : ell ∣ b' := dvd_trans hell2 d2b'
  have dla : ell ∣ a := dvd_trans hell2 d2a
  have dlb : ell ∣ b := dvd_trans hell2 d2b
  -- transverse coordinates of sub-cubes
  have hNl : ell ∣ N := dvd_trans hell2 hNd
  have sub_t : ∀ Y1 j, ell ^ 2 ∣ Y1 → Y1 < N → j < ell → Y1 + ell * j < N ∧ ell ∣ Y1 + ell * j := by
    intro Y1 j hY hN hj
    have h1' : Y1 + ell ^ 2 ≤ N := step_le hY hNd hN
    refine ⟨?_, dvd_add (dvd_trans hell2 hY) (dvd_mul_right _ _)⟩
    have : ell * j < ell ^ 2 := by
      calc ell * j < ell * ell := Nat.mul_lt_mul_of_pos_left hj hell
        _ = ell ^ 2 := (pow_two ell).symm
    omega
  -- LEFT: level-1 cube sums vanish for Y0 in [p1 - ell, a' - ell]
  have left0 : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ∣ t → p1 ≤ t + ell → t + ell ≤ a' → cube g ell t Y1 Y2 = 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi
    have hdp : ell ∣ p1 - ell := Nat.dvd_sub d1p dvd_rfl
    have hchain := chain_gen (fun Y => cube g ell Y Y1 Y2) ell (p1 - ell) (a' - ell)
      (fun Y hY hlo' hhi' => h1 Y Y1 Y2 hY hY1 hY2 hN1 hN2 (Or.inl ⟨by omega, by omega⟩))
      (p1 - ell) t hdp ht le_rfl (by omega) (by omega)
    try simp only at hchain
    rw [hchain]
    refine cube_zero_of g ell _ _ _ (fun i j k hi _ _ => hL _ (by omega) _ _)
  have mul_lt_sq : ∀ i, i < ell → ell * i + ell ≤ ell ^ 2 := by
    intro i hi
    have := Nat.mul_le_mul_left ell (Nat.succ_le_of_lt hi)
    calc ell * i + ell = ell * (i + 1) := by ring
      _ ≤ ell * ell := this
      _ = ell ^ 2 := (pow_two ell).symm
  -- THIN: level-2 cube sums vanish for Y0 in [a' - ell^2, b']
  have thin : ∀ Y1 Y2, ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ^ 2 ∣ t → a' ≤ t + ell ^ 2 → t ≤ b' → cube g (ell ^ 2) t Y1 Y2 = 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2
    have base : cube g (ell ^ 2) (a' - ell ^ 2) Y1 Y2 = 0 := by
      rw [cube2_split]
      refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun k hk => ?_)))
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hk' := Finset.mem_range.mp hk
      obtain ⟨hj1, hj2⟩ := sub_t Y1 j hY1 hN1 hj'
      obtain ⟨hk1, hk2⟩ := sub_t Y2 k hY2 hN2 hk'
      have hdv : ell ∣ a' - ell ^ 2 + ell * i := by
        have : ell ∣ a' - ell ^ 2 := Nat.dvd_sub dla' hell2
        exact dvd_add this (dvd_mul_right _ _)
      have hle := mul_lt_sq i hi'
      exact left0 (Y1 + ell * j) (Y2 + ell * k) hj2 hk2 hj1 hk1 _ hdv (by omega) (by omega)
    intro t ht hlo hhi
    have hdt : ell ^ 2 ∣ a' - ell ^ 2 := Nat.dvd_sub d2a' dvd_rfl
    have := chain_gen (fun Y => cube g (ell ^ 2) Y Y1 Y2) (ell ^ 2) (a' - ell ^ 2) b'
      (fun Y hY hlo' hhi' => h2 Y Y1 Y2 hY hY1 hY2 hN1 hN2 (Or.inl ⟨by omega, by omega⟩))
      (a' - ell ^ 2) t hdt ht le_rfl (by omega) hhi
    try simp only at this
    rw [this]; exact base
  -- GAP: level-1 value propagates along x0
  have gap0 : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ∣ t → b' ≤ t → t + ell ≤ a → cube g ell t Y1 Y2 = cube g ell b' Y1 Y2 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi
    exact chain_gen (fun Y => cube g ell Y Y1 Y2) ell b' (a - ell)
      (fun Y hY hlo' hhi' => h1 Y Y1 Y2 hY hY1 hY2 hN1 hN2 (Or.inr (Or.inl ⟨hlo', by omega⟩)))
      b' t dlb' ht le_rfl (by omega) (by omega)
  have hN0 : (0 : ℕ) < N := hNpos
  -- transverse constancy at Y0 = b'
  have gapT : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      cube g ell b' Y1 Y2 = cube g ell b' 0 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2
    have hA : cube g ell b' Y1 Y2 = cube g ell b' Y1 0 := by
      have := chain_gen (fun Y => cube g ell b' Y1 Y) ell 0 (N - 1)
        (fun Y hY _ hhi' => h1z b' Y1 Y dlb' hY1 hY hN1 (by omega) le_rfl (by omega))
        0 Y2 (dvd_zero _) hY2 (Nat.zero_le _) (Nat.zero_le _) (by omega)
      simpa using this
    have hB : cube g ell b' Y1 0 = cube g ell b' 0 0 := by
      have := chain_gen (fun Y => cube g ell b' Y 0) ell 0 (N - 1)
        (fun Y hY _ hhi' => h1y b' Y 0 dlb' hY (dvd_zero _) (by omega) hN0 le_rfl (by omega))
        0 Y1 (dvd_zero _) hY1 (Nat.zero_le _) (Nat.zero_le _) (by omega)
      simpa using this
    rw [hA, hB]
  -- all gap level-1 values equal the common value
  have gapall : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ∣ t → b' ≤ t → t + ell ≤ a → cube g ell t Y1 Y2 = cube g ell b' 0 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi
    rw [gap0 Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi, gapT Y1 Y2 hY1 hY2 hN1 hN2]
  -- the gap value is zero
  have gapzero : cube g ell b' 0 0 = 0 := by
    have hc2 : cube g (ell ^ 2) b' 0 0 = ((ell : ℝ) ^ 3) • cube g ell b' 0 0 := by
      refine cube2_of_const g ell b' 0 0 _ (fun i j k hi hj hk => ?_)
      have hle := mul_lt_sq i hi
      exact gapall (0 + ell * j) (0 + ell * k) (dvd_add (dvd_zero _) (dvd_mul_right _ _))
        (dvd_add (dvd_zero _) (dvd_mul_right _ _))
        (sub_t 0 j (dvd_zero _) hN0 hj).1 (sub_t 0 k (dvd_zero _) hN0 hk).1 _
        (dvd_add dlb' (dvd_mul_right _ _)) (by omega) (by omega)
    have hz := thin 0 0 (dvd_zero _) (dvd_zero _) hN0 hN0 b' d2b' (by omega) le_rfl
    rw [hc2] at hz
    exact smul_pow_eq_zero hell hz
  have gapval : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ∣ t → b' ≤ t → t + ell ≤ a → cube g ell t Y1 Y2 = 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi
    rw [gapall Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi, gapzero]
  -- FAT: level-2 cube sums vanish for Y0 in [a - ell^2, b]
  have fat : ∀ Y1 Y2, ell ^ 2 ∣ Y1 → ell ^ 2 ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ^ 2 ∣ t → a ≤ t + ell ^ 2 → t ≤ b → cube g (ell ^ 2) t Y1 Y2 = 0 := by
    intro Y1 Y2 hY1 hY2 hN1 hN2
    have base : cube g (ell ^ 2) (a - ell ^ 2) Y1 Y2 = 0 := by
      rw [cube2_split]
      refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun k hk => ?_)))
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hk' := Finset.mem_range.mp hk
      obtain ⟨hj1, hj2⟩ := sub_t Y1 j hY1 hN1 hj'
      obtain ⟨hk1, hk2⟩ := sub_t Y2 k hY2 hN2 hk'
      have hdv : ell ∣ a - ell ^ 2 + ell * i := by
        have : ell ∣ a - ell ^ 2 := Nat.dvd_sub dla hell2
        exact dvd_add this (dvd_mul_right _ _)
      have hle := mul_lt_sq i hi'
      exact gapval (Y1 + ell * j) (Y2 + ell * k) hj2 hk2 hj1 hk1 _ hdv (by omega) (by omega)
    intro t ht hlo hhi
    have hdt : ell ^ 2 ∣ a - ell ^ 2 := Nat.dvd_sub d2a dvd_rfl
    have := chain_gen (fun Y => cube g (ell ^ 2) Y Y1 Y2) (ell ^ 2) (a - ell ^ 2) b
      (fun Y hY hlo' hhi' => h2 Y Y1 Y2 hY hY1 hY2 hN1 hN2 (Or.inr ⟨by omega, by omega⟩))
      (a - ell ^ 2) t hdt ht le_rfl (by omega) hhi
    try simp only at this
    rw [this]; exact base
  -- RIGHT: anchor value
  have rightq : ∀ Y1 Y2, cube g ell q1 Y1 Y2 = ((ell : ℝ) ^ 3) • κ := by
    intro Y1 Y2
    exact cube_const g ell q1 Y1 Y2 κ (fun i j k hi _ _ => hR _ (by omega) (by omega) _ _)
  have rightall : ∀ Y1 Y2, ell ∣ Y1 → ell ∣ Y2 → Y1 < N → Y2 < N →
      ∀ t, ell ∣ t → b ≤ t → t ≤ q1 → cube g ell t Y1 Y2 = ((ell : ℝ) ^ 3) • κ := by
    intro Y1 Y2 hY1 hY2 hN1 hN2 t ht hlo hhi
    have := chain_gen (fun Y => cube g ell Y Y1 Y2) ell b q1
      (fun Y hY hlo' hhi' => h1 Y Y1 Y2 hY hY1 hY2 hN1 hN2 (Or.inr (Or.inr ⟨hlo', hhi'⟩)))
      t q1 ht d1q hlo hhi le_rfl
    try simp only at this
    rw [← this, rightq]
  have kappa0 : κ = 0 := by
    have hc2 : cube g (ell ^ 2) b 0 0 = ((ell : ℝ) ^ 3) • (((ell : ℝ) ^ 3) • κ) := by
      refine cube2_of_const g ell b 0 0 _ (fun i j k hi hj hk => ?_)
      have hle := mul_lt_sq i hi
      exact rightall (0 + ell * j) (0 + ell * k) (dvd_add (dvd_zero _) (dvd_mul_right _ _))
        (dvd_add (dvd_zero _) (dvd_mul_right _ _))
        (sub_t 0 j (dvd_zero _) hN0 hj).1 (sub_t 0 k (dvd_zero _) hN0 hk).1 _
        (dvd_add dlb (dvd_mul_right _ _)) (by omega) (by omega)
    have hz := fat 0 0 (dvd_zero _) (dvd_zero _) hN0 hN0 b d2b (by omega) le_rfl
    rw [hc2] at hz
    exact smul_pow_eq_zero hell (smul_pow_eq_zero hell hz)
  refine ⟨kappa0, ?_, ?_⟩
  · intro Y0 Y1 Y2 h0 h1' h2' hN1 hN2 hcase
    rcases hcase with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact left0 Y1 Y2 h1' h2' hN1 hN2 Y0 h0 (by omega) (by have := step_le h0 dla' hhi; omega)
    · exact gapval Y1 Y2 h1' h2' hN1 hN2 Y0 h0 hlo (by have := step_le h0 dla hhi; omega)
    · rw [rightall Y1 Y2 h1' h2' hN1 hN2 Y0 h0 hlo hhi.le, kappa0, smul_zero]
  · intro Y0 Y1 Y2 h0 h1' h2' hN1 hN2 hcase
    rcases hcase with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact thin Y1 Y2 h1' h2' hN1 hN2 Y0 h0 (by omega) hhi.le
    · exact fat Y1 Y2 h1' h2' hN1 hN2 Y0 h0 (by omega) hhi.le

end chain

end AdalyFormal.CoverOmega

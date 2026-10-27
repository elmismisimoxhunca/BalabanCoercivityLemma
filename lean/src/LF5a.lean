import Mathlib

/-!
# LF5a -- combinatorial lemmas (Mathlib only): 1D paths, the cube Poincaré inequality, fibre sums

* `norm_sub_le_path`: `‖f s - f s'‖ ≤ Σ_{t < m-1} ‖f (t+1) - f t‖` for `s, s' < m`.
* `cube_path`: on the cube `[0,m)³` (`cube m`), `‖W i - W i'‖² ≤ 9 m · cubeE m W`,
  `cubeE m W = Σ_ν Σ_{i ∈ cube, i ν + 1 < m} ‖W (i + e_ν) - W i‖²`.
* `cube_poincare`: `Σ_{i ∈ cube} ‖W i - avg W‖² ≤ 9 m⁴ · cubeE m W`.
* `sum_comp_le`: `Σ_{a∈s} g (f a) ≤ M Σ_{b∈t} g b` if `f` maps `s` into `t`, fibres have `≤ M` elements, `g ≥ 0`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.LemIFlat

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sub_le_path_le (f : ℕ → E) (m s k : ℕ) (hk : s + k < m) :
    ‖f (s + k) - f s‖ ≤ ∑ t ∈ Finset.range (m - 1), ‖f (t + 1) - f t‖ := by
  have e : f (s + k) - f s = ∑ i ∈ Finset.range k, (f (s + i + 1) - f (s + i)) := by
    have := Finset.sum_range_sub (fun i => f (s + i)) k
    simp only [Nat.add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.add_assoc]
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hmap : ∑ i ∈ Finset.range k, ‖f (s + i + 1) - f (s + i)‖
      = ∑ t ∈ (Finset.range k).map (addLeftEmbedding s), ‖f (t + 1) - f t‖ := by
    rw [Finset.sum_map]; rfl
  rw [hmap]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro t ht
  simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  rw [Finset.mem_range]; omega

theorem norm_sub_le_path (f : ℕ → E) (m s s' : ℕ) (hs : s < m) (hs' : s' < m) :
    ‖f s - f s'‖ ≤ ∑ t ∈ Finset.range (m - 1), ‖f (t + 1) - f t‖ := by
  rcases le_total s s' with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [norm_sub_rev]; exact norm_sub_le_path_le f m s k hs'
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact norm_sub_le_path_le f m s' k hs

/-- the index cube `[0,m)³`. -/
def cube (m : ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset (fun _ : Fin 3 => Finset.range m)

theorem mem_cube (m : ℕ) (i : Fin 3 → ℕ) : i ∈ cube m ↔ ∀ ν, i ν < m := by
  simp [cube, Fintype.mem_piFinset]

theorem card_cube (m : ℕ) : (cube m).card = m ^ 3 := by
  simp [cube, Fintype.card_piFinset, Finset.prod_const]

/-- the edge energy of `W` on the cube. -/
noncomputable def cubeE (m : ℕ) (W : (Fin 3 → ℕ) → E) : ℝ :=
  ∑ ν : Fin 3, ∑ i ∈ (cube m).filter (fun i => i ν + 1 < m), ‖W (Function.update i ν (i ν + 1)) - W i‖ ^ 2

theorem cubeE_nonneg (m : ℕ) (W : (Fin 3 → ℕ) → E) : 0 ≤ cubeE m W :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- one line of the cube carries at most the whole edge energy. -/
theorem line_le (m : ℕ) (W : (Fin 3 → ℕ) → E) (i : Fin 3 → ℕ) (hi : i ∈ cube m) (ν : Fin 3) :
    ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖ ^ 2 ≤ cubeE m W := by
  classical
  have hinj : Set.InjOn (fun t => Function.update i ν t) (Finset.range (m - 1) : Set ℕ) := by
    intro a _ b _ h
    have := congrFun h ν
    simpa using this
  have hsub : (Finset.range (m - 1)).image (fun t => Function.update i ν t) ⊆ (cube m).filter (fun i' => i' ν + 1 < m) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Finset.mem_filter, mem_cube]
    refine ⟨fun μ => ?_, by simp; omega⟩
    by_cases h : μ = ν
    · subst h; simp; omega
    · rw [Function.update_of_ne h]; exact (mem_cube m i).mp hi μ
  have h1 : ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖ ^ 2
      = ∑ x ∈ (Finset.range (m - 1)).image (fun t => Function.update i ν t),
          ‖W (Function.update x ν (x ν + 1)) - W x‖ ^ 2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [Function.update_idem]
  rw [h1]
  calc _ ≤ ∑ x ∈ (cube m).filter (fun i' => i' ν + 1 < m), ‖W (Function.update x ν (x ν + 1)) - W x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ cubeE m W := by
        unfold cubeE
        exact Finset.single_le_sum (f := fun ν' => ∑ i ∈ (cube m).filter (fun i => i ν' + 1 < m),
          ‖W (Function.update i ν' (i ν' + 1)) - W i‖ ^ 2) (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Finset.mem_univ ν)

theorem line_sq_le (m : ℕ) (W : (Fin 3 → ℕ) → E) (i : Fin 3 → ℕ) (hi : i ∈ cube m) (ν : Fin 3) :
    (∑ t ∈ Finset.range (m - 1), ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖) ^ 2
      ≤ m * cubeE m W := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (m - 1))
    (f := fun t => ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖)
  rw [Finset.card_range] at h1
  have h2 := line_le m W i hi ν
  have h3 : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have h4 := cubeE_nonneg m W
  calc _ ≤ ((m - 1 : ℕ) : ℝ) * ∑ t ∈ Finset.range (m - 1),
        ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖ ^ 2 := h1
    _ ≤ (m : ℝ) * cubeE m W := mul_le_mul h3 h2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- along one coordinate. -/
theorem seg_le (m : ℕ) (W : (Fin 3 → ℕ) → E) (i : Fin 3 → ℕ) (hi : i ∈ cube m) (ν : Fin 3) (s : ℕ) (hs : s < m) :
    ‖W i - W (Function.update i ν s)‖
      ≤ ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i ν (t + 1)) - W (Function.update i ν t)‖ := by
  have h := norm_sub_le_path (fun t => W (Function.update i ν t)) m (i ν) s ((mem_cube m i).mp hi ν) hs
  simpa [Function.update_eq_self] using h

theorem cube_path (m : ℕ) (W : (Fin 3 → ℕ) → E) (i i' : Fin 3 → ℕ) (hi : i ∈ cube m) (hi' : i' ∈ cube m) :
    ‖W i - W i'‖ ^ 2 ≤ 9 * m * cubeE m W := by
  classical
  have hm := (mem_cube m i).mp hi
  have hm' := (mem_cube m i').mp hi'
  set i1 := Function.update i 0 (i' 0) with hi1
  set i2 := Function.update i1 1 (i' 1) with hi2
  have hc1 : i1 ∈ cube m := by
    rw [mem_cube]; intro μ; by_cases h : μ = 0
    · subst h; simp [hi1]; exact hm' 0
    · rw [hi1, Function.update_of_ne h]; exact hm μ
  have hc2 : i2 ∈ cube m := by
    rw [mem_cube]; intro μ; by_cases h : μ = 1
    · subst h; simp [hi2]; exact hm' 1
    · rw [hi2, Function.update_of_ne h]; exact (mem_cube m i1).mp hc1 μ
  have hlast : Function.update i2 2 (i' 2) = i' := by
    funext μ
    fin_cases μ <;> simp [hi2, hi1, Function.update_of_ne]
  have s1 := seg_le m W i hi 0 (i' 0) (hm' 0)
  have s2 := seg_le m W i1 hc1 1 (i' 1) (hm' 1)
  have s3 := seg_le m W i2 hc2 2 (i' 2) (hm' 2)
  rw [hlast] at s3
  set l1 := ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i 0 (t + 1)) - W (Function.update i 0 t)‖
  set l2 := ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i1 1 (t + 1)) - W (Function.update i1 1 t)‖
  set l3 := ∑ t ∈ Finset.range (m - 1), ‖W (Function.update i2 2 (t + 1)) - W (Function.update i2 2 t)‖
  have q1 := line_sq_le m W i hi 0
  have q2 := line_sq_le m W i1 hc1 1
  have q3 := line_sq_le m W i2 hc2 2
  have htri : ‖W i - W i'‖ ≤ l1 + l2 + l3 := by
    calc ‖W i - W i'‖ = ‖(W i - W i1) + (W i1 - W i2) + (W i2 - W i')‖ := by congr 1; abel
      _ ≤ ‖W i - W i1‖ + ‖W i1 - W i2‖ + ‖W i2 - W i'‖ := norm_add₃_le
      _ ≤ l1 + l2 + l3 := by linarith
  have h0 : 0 ≤ ‖W i - W i'‖ := norm_nonneg _
  have hl1 : 0 ≤ l1 := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hl2 : 0 ≤ l2 := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hl3 : 0 ≤ l3 := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq : ‖W i - W i'‖ ^ 2 ≤ (l1 + l2 + l3) ^ 2 := pow_le_pow_left₀ h0 htri 2
  nlinarith [sq_nonneg (l1 - l2), sq_nonneg (l2 - l3), sq_nonneg (l1 - l3)]

/-- **one point vs the cube average**. -/
theorem cube_dev (m : ℕ) (hm : 0 < m) (W : (Fin 3 → ℕ) → E) (i : Fin 3 → ℕ) (hi : i ∈ cube m) :
    ‖W i - ((1 : ℝ) / (m : ℝ) ^ 3) • ∑ i' ∈ cube m, W i'‖ ^ 2 ≤ 9 * m * cubeE m W := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hcard : ((cube m).card : ℝ) = (m : ℝ) ^ 3 := by rw [card_cube]; push_cast; ring
  have e : W i - ((1 : ℝ) / (m : ℝ) ^ 3) • ∑ i' ∈ cube m, W i'
      = ((1 : ℝ) / (m : ℝ) ^ 3) • ∑ i' ∈ cube m, (W i - W i') := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_cube, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hc : (1 : ℝ) / (m : ℝ) ^ 3 * ((m ^ 3 : ℕ) : ℝ) = 1 := by push_cast; field_simp
    rw [hc, one_smul]
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow]
  have h1 : ‖∑ i' ∈ cube m, (W i - W i')‖ ^ 2 ≤ (m : ℝ) ^ 3 * ∑ i' ∈ cube m, ‖W i - W i'‖ ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := cube m) (f := fun i' => ‖W i - W i'‖)
    rw [card_cube] at hcs
    push_cast at hcs
    have h2 : ‖∑ i' ∈ cube m, (W i - W i')‖ ≤ ∑ i' ∈ cube m, ‖W i - W i'‖ := norm_sum_le _ _
    have h3 : ‖∑ i' ∈ cube m, (W i - W i')‖ ^ 2 ≤ (∑ i' ∈ cube m, ‖W i - W i'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  have h2 : ∑ i' ∈ cube m, ‖W i - W i'‖ ^ 2 ≤ (m : ℝ) ^ 3 * (9 * m * cubeE m W) := by
    have h := Finset.sum_le_sum (fun i' hi' => cube_path m W i i' hi hi')
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
    exact h
  have hE := cubeE_nonneg m W
  calc ((1 : ℝ) / (m : ℝ) ^ 3) ^ 2 * ‖∑ i' ∈ cube m, (W i - W i')‖ ^ 2
      ≤ ((1 : ℝ) / (m : ℝ) ^ 3) ^ 2 * ((m : ℝ) ^ 3 * ((m : ℝ) ^ 3 * (9 * m * cubeE m W))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) (by positivity)
    _ = 9 * m * cubeE m W := by field_simp

/-- **cube Poincaré**. -/
theorem cube_poincare (m : ℕ) (hm : 0 < m) (W : (Fin 3 → ℕ) → E) :
    ∑ i ∈ cube m, ‖W i - ((1 : ℝ) / (m : ℝ) ^ 3) • ∑ i' ∈ cube m, W i'‖ ^ 2 ≤ 9 * (m : ℝ) ^ 4 * cubeE m W := by
  have hcard : ((cube m).card : ℝ) = (m : ℝ) ^ 3 := by rw [card_cube]; push_cast; ring
  calc ∑ i ∈ cube m, ‖W i - ((1 : ℝ) / (m : ℝ) ^ 3) • ∑ i' ∈ cube m, W i'‖ ^ 2
      ≤ ∑ _i ∈ cube m, 9 * (m : ℝ) * cubeE m W := Finset.sum_le_sum (fun i hi => cube_dev m hm W i hi)
    _ = 9 * (m : ℝ) ^ 4 * cubeE m W := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring

end

/-- fibre-sum bound. -/
theorem sum_comp_le {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β) (g : β → ℝ) (M : ℕ)
    (hmap : ∀ a ∈ s, f a ∈ t) (hfib : ∀ b ∈ t, (s.filter (fun a => f a = b)).card ≤ M) (hg : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, g (f a) ≤ M * ∑ b ∈ t, g b := by
  rw [Finset.sum_comp]
  have himg : s.image f ⊆ t := by
    intro b hb; rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb; exact hmap a ha
  calc ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card • g b
      ≤ ∑ b ∈ s.image f, (M : ℝ) * g b := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib b (himg hb)) (hg b (himg hb))
    _ = M * ∑ b ∈ s.image f, g b := by rw [Finset.mul_sum]
    _ ≤ M * ∑ b ∈ t, g b :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg himg (fun b hb _ => hg b hb))
          (Nat.cast_nonneg _)

#print axioms norm_sub_le_path
#print axioms line_le
#print axioms cube_path
#print axioms cube_dev
#print axioms cube_poincare
#print axioms sum_comp_le

#print axioms norm_sub_le_path_le
#print axioms mem_cube
#print axioms card_cube
#print axioms cubeE_nonneg
#print axioms line_sq_le
#print axioms seg_le

end AdalyFormal.LemIFlat

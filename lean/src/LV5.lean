import LV4

/-!
# LV5 -- generic summation by parts on a lattice with a marked region, layer algebra, AM-GM, the directional
layer estimate

* `parts_small` / `parts_big` : summation by parts of `Σ ⟨Φ(z+me) - Φ z, F z μ⟩` over the rows with both ends outside
  `Rg` (resp. at least one end in `Rg`), for `F` exactly conserved (`Σ_μ (F(z - m e_μ) μ - F z μ) = 0`).
* `cube_layer` : `Σ_{i ∈ cube m} [i μ = s] g i = Σ_{k ∈ face m μ} g (update k μ s)`.
* `layer_alg` : `Σ⟨Φ_k,F_k⟩ - K⟨P,F̄⟩ = K⟨K⁻¹ΣΦ_k - P, F̄⟩ + Σ⟨Φ_k - P, F_k - F̄⟩` when `Σ F_k = K F̄`.
* `amgm` : `2|⟨x,y⟩| ≤ p‖x‖² + ‖y‖²/p`.
* `layer_dev` : `‖ℓ⁻² Σ_{k ∈ face} W(update k μ s) - ℓ⁻³ Σ_{i ∈ cube} W i‖² ≤ ℓ⁻¹ · (μ-edge energy of W on the cube)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.FlatCoercivity (eU)

variable {L : PeriodicLatticeExtent}

/-! ## summation by parts -/

section parts
variable {m : ℕ} (hdvd : ∀ μ : Fin 3, m ∣ L μ + 1) (Rg : Set (PeriodicLatticeSite L))
  (Φ : PeriodicLatticeSite L → SuTwo) (F : PeriodicLatticeSite L → Fin 3 → SuTwo)
  (hcons : ∀ z, ∑ μ : Fin 3, (F (z - m • eU L μ) μ - F z μ) = 0)
include hdvd hcons

open Classical in
theorem parts_small :
    ∑ μ : Fin 3, ∑ z ∈ latF L m,
        (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ (z + m • eU L μ) - Φ z, F z μ⟫ else 0)
      = ∑ μ : Fin 3, ∑ z ∈ latF L m,
        (if z ∉ Rg then
          ((if z + m • eU L μ ∈ Rg then ⟪Φ z, F z μ⟫ else 0)
            - (if z - m • eU L μ ∈ Rg then ⟪Φ z, F (z - m • eU L μ) μ⟫ else 0)) else 0) := by
  -- reindex the first half
  have hre : ∀ μ : Fin 3, ∑ z ∈ latF L m,
      (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ (z + m • eU L μ), F z μ⟫ else 0)
      = ∑ z ∈ latF L m, (if z - m • eU L μ ∉ Rg ∧ z ∉ Rg then ⟪Φ z, F (z - m • eU L μ) μ⟫ else 0) := by
    intro μ
    rw [sum_latF, sum_latF]
    have h := lat_translate hdvd (m • eU L μ) (onLat_smul_eU hdvd μ)
      (fun z => if z - m • eU L μ ∉ Rg ∧ z ∉ Rg then ⟪Φ z, F (z - m • eU L μ) μ⟫ else 0)
    simp only [add_sub_cancel_right] at h
    rw [← h]
  have hsplit : ∀ μ : Fin 3, ∑ z ∈ latF L m,
      (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ (z + m • eU L μ) - Φ z, F z μ⟫ else 0)
      = ∑ z ∈ latF L m, (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ (z + m • eU L μ), F z μ⟫ else 0)
        - ∑ z ∈ latF L m, (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ z, F z μ⟫ else 0) := by
    intro μ
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    split_ifs <;> simp [inner_sub_left]
  simp only [hsplit, hre]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_comm.trans (Eq.trans ?_ Finset.sum_comm)
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have hc : ∑ μ : Fin 3, (⟪Φ z, F (z - m • eU L μ) μ⟫ - ⟪Φ z, F z μ⟫) = 0 := by
    simp only [← inner_sub_right]
    rw [← inner_sum, hcons z, inner_zero_right]
  have hpt : ∀ μ : Fin 3,
      ((if z - m • eU L μ ∉ Rg ∧ z ∉ Rg then ⟪Φ z, F (z - m • eU L μ) μ⟫ else 0)
        - (if z ∉ Rg ∧ z + m • eU L μ ∉ Rg then ⟪Φ z, F z μ⟫ else 0))
      = (if z ∉ Rg then
          ((if z + m • eU L μ ∈ Rg then ⟪Φ z, F z μ⟫ else 0)
            - (if z - m • eU L μ ∈ Rg then ⟪Φ z, F (z - m • eU L μ) μ⟫ else 0)) else 0)
        + (if z ∉ Rg then (⟪Φ z, F (z - m • eU L μ) μ⟫ - ⟪Φ z, F z μ⟫) else 0) := by
    intro μ
    by_cases h1 : z - m • eU L μ ∈ Rg <;> by_cases h2 : z ∈ Rg <;> by_cases h3 : z + m • eU L μ ∈ Rg <;>
      simp [h1, h2, h3] <;> ring
  rw [Finset.sum_congr rfl (fun μ _ => hpt μ), Finset.sum_add_distrib]
  by_cases h2 : z ∈ Rg
  · simp [h2]
  · simp only [h2, not_false_eq_true, if_true]
    rw [hc, add_zero]

open Classical in
theorem parts_big :
    ∑ μ : Fin 3, ∑ Z ∈ latF L m,
        (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ (Z + m • eU L μ) - Φ Z, F Z μ⟫ else 0)
      = ∑ μ : Fin 3, ∑ Z ∈ latF L m,
        (if Z ∉ Rg then
          ((if Z - m • eU L μ ∈ Rg then ⟪Φ Z, F (Z - m • eU L μ) μ⟫ else 0)
            - (if Z + m • eU L μ ∈ Rg then ⟪Φ Z, F Z μ⟫ else 0)) else 0) := by
  have hre : ∀ μ : Fin 3, ∑ Z ∈ latF L m,
      (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ (Z + m • eU L μ), F Z μ⟫ else 0)
      = ∑ Z ∈ latF L m, (if Z - m • eU L μ ∈ Rg ∨ Z ∈ Rg then ⟪Φ Z, F (Z - m • eU L μ) μ⟫ else 0) := by
    intro μ
    rw [sum_latF, sum_latF]
    have h := lat_translate hdvd (m • eU L μ) (onLat_smul_eU hdvd μ)
      (fun Z => if Z - m • eU L μ ∈ Rg ∨ Z ∈ Rg then ⟪Φ Z, F (Z - m • eU L μ) μ⟫ else 0)
    simp only [add_sub_cancel_right] at h
    rw [← h]
  have hsplit : ∀ μ : Fin 3, ∑ Z ∈ latF L m,
      (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ (Z + m • eU L μ) - Φ Z, F Z μ⟫ else 0)
      = ∑ Z ∈ latF L m, (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ (Z + m • eU L μ), F Z μ⟫ else 0)
        - ∑ Z ∈ latF L m, (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ Z, F Z μ⟫ else 0) := by
    intro μ
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    split_ifs <;> simp [inner_sub_left]
  simp only [hsplit, hre]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_comm.trans (Eq.trans ?_ Finset.sum_comm)
  refine Finset.sum_congr rfl (fun Z _ => ?_)
  have hc : ∑ μ : Fin 3, (⟪Φ Z, F (Z - m • eU L μ) μ⟫ - ⟪Φ Z, F Z μ⟫) = 0 := by
    simp only [← inner_sub_right]
    rw [← inner_sum, hcons Z, inner_zero_right]
  have hpt : ∀ μ : Fin 3,
      ((if Z - m • eU L μ ∈ Rg ∨ Z ∈ Rg then ⟪Φ Z, F (Z - m • eU L μ) μ⟫ else 0)
        - (if Z ∈ Rg ∨ Z + m • eU L μ ∈ Rg then ⟪Φ Z, F Z μ⟫ else 0))
      = (if Z ∉ Rg then
          ((if Z - m • eU L μ ∈ Rg then ⟪Φ Z, F (Z - m • eU L μ) μ⟫ else 0)
            - (if Z + m • eU L μ ∈ Rg then ⟪Φ Z, F Z μ⟫ else 0)) else 0)
        + (if Z ∈ Rg then (⟪Φ Z, F (Z - m • eU L μ) μ⟫ - ⟪Φ Z, F Z μ⟫) else 0) := by
    intro μ
    by_cases h1 : Z - m • eU L μ ∈ Rg <;> by_cases h2 : Z ∈ Rg <;> by_cases h3 : Z + m • eU L μ ∈ Rg <;>
      simp [h1, h2, h3] <;> ring
  rw [Finset.sum_congr rfl (fun μ _ => hpt μ), Finset.sum_add_distrib]
  by_cases h2 : Z ∈ Rg
  · simp only [h2, if_true]
    rw [hc, add_zero]
  · simp [h2]

end parts

/-! ## layers of the cube -/

theorem cube_layer {M : Type*} [AddCommMonoid M] (m : ℕ) (μ : Fin 3) (s : ℕ) (hs : s < m)
    (g : (Fin 3 → ℕ) → M) :
    ∑ i ∈ cube m, (if i μ = s then g i else 0) = ∑ k ∈ face m μ, g (Function.update k μ s) := by
  classical
  rw [cube_split m μ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.update_self]
  rw [Finset.sum_ite_eq' (Finset.range m) s, if_pos (Finset.mem_range.mpr hs)]

theorem face_le_cube (m : ℕ) (μ : Fin 3) (s : ℕ) (hs : s < m) (g : (Fin 3 → ℕ) → ℝ) (hg : ∀ i, 0 ≤ g i) :
    ∑ k ∈ face m μ, g (Function.update k μ s) ≤ ∑ i ∈ cube m, g i := by
  classical
  rw [← cube_layer m μ s hs g]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs
  · exact le_refl _
  · exact hg i

theorem card_face_real (m : ℕ) (hm : 0 < m) (μ : Fin 3) : ((face m μ).card : ℝ) = (m : ℝ) ^ 2 := by
  rw [card_face m hm μ]; push_cast; ring

/-! ## the layer identity -/

theorem layer_alg {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Finset ι)
    (Φ F : ι → E) (P Fb : E) (K : ℝ) (hK0 : K ≠ 0) (hK : (s.card : ℝ) = K) (hF : ∑ k ∈ s, F k = K • Fb) :
    ∑ k ∈ s, ⟪Φ k, F k⟫ - K * ⟪P, Fb⟫
      = K * ⟪K⁻¹ • ∑ k ∈ s, Φ k - P, Fb⟫ + ∑ k ∈ s, ⟪Φ k - P, F k - Fb⟫ := by
  have e1 : ∑ k ∈ s, ⟪Φ k - P, F k - Fb⟫
      = ∑ k ∈ s, ⟪Φ k, F k⟫ - ⟪∑ k ∈ s, Φ k, Fb⟫ - ⟪P, ∑ k ∈ s, F k⟫ + (s.card : ℝ) * ⟪P, Fb⟫ := by
    simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum,
      Finset.sum_const, nsmul_eq_mul]
    ring
  rw [e1, hF, hK, inner_sub_left, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  field_simp
  ring

theorem amgm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) (p : ℝ) (hp : 0 < p) :
    2 * |⟪x, y⟫| ≤ p * ‖x‖ ^ 2 + ‖y‖ ^ 2 / p := by
  have h1 : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
  have h2 : 0 ≤ (p * ‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
  have h3 : 2 * (‖x‖ * ‖y‖) ≤ p * ‖x‖ ^ 2 + ‖y‖ ^ 2 / p := by
    rw [div_eq_mul_inv]
    have hpi : 0 < p⁻¹ := inv_pos.mpr hp
    have : p * ‖x‖ ^ 2 + ‖y‖ ^ 2 * p⁻¹ - 2 * (‖x‖ * ‖y‖) = (p * ‖x‖ - ‖y‖) ^ 2 * p⁻¹ := by
      field_simp; ring
    nlinarith [mul_nonneg h2 hpi.le]
  linarith

/-! ## the directional layer estimate -/

/-- the `μ`-edge energy of a cube function -/
noncomputable def cubeEd {E : Type*} [NormedAddCommGroup E] (m : ℕ) (W : (Fin 3 → ℕ) → E) (μ : Fin 3) : ℝ :=
  ∑ i ∈ (cube m).filter (fun i => i μ + 1 < m), ‖W (Function.update i μ (i μ + 1)) - W i‖ ^ 2

theorem cubeE_eq {E : Type*} [NormedAddCommGroup E] (m : ℕ) (W : (Fin 3 → ℕ) → E) :
    cubeE m W = ∑ μ : Fin 3, cubeEd m W μ := rfl

theorem cubeEd_eq {E : Type*} [NormedAddCommGroup E] (m : ℕ) (W : (Fin 3 → ℕ) → E) (μ : Fin 3) :
    cubeEd m W μ = ∑ k ∈ face m μ, ∑ t ∈ Finset.range (m - 1),
      ‖W (Function.update k μ (t + 1)) - W (Function.update k μ t)‖ ^ 2 := by
  classical
  unfold cubeEd
  rw [Finset.sum_filter, cube_split m μ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Function.update_self, Function.update_idem]
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem layer_dev {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) (hm : 0 < m)
    (W : (Fin 3 → ℕ) → E) (μ : Fin 3) (s : ℕ) (hs : s < m) :
    ‖((m : ℝ) ^ 2)⁻¹ • ∑ k ∈ face m μ, W (Function.update k μ s) - ((m : ℝ) ^ 3)⁻¹ • ∑ i ∈ cube m, W i‖ ^ 2
      ≤ (m : ℝ)⁻¹ * cubeEd m W μ := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set lam : (Fin 3 → ℕ) → ℝ := fun k => ∑ r ∈ Finset.range (m - 1),
    ‖W (Function.update k μ (r + 1)) - W (Function.update k μ r)‖ with hlam
  have hlam0 : ∀ k, 0 ≤ lam k := fun k => Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  -- the difference as a double sum
  have hdiff : ((m : ℝ) ^ 2)⁻¹ • ∑ k ∈ face m μ, W (Function.update k μ s) - ((m : ℝ) ^ 3)⁻¹ • ∑ i ∈ cube m, W i
      = ((m : ℝ) ^ 3)⁻¹ • ∑ k ∈ face m μ, ∑ t ∈ Finset.range m,
          (W (Function.update k μ s) - W (Function.update k μ t)) := by
    rw [cube_split m μ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub]
    congr 1
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  have hnorm : ‖((m : ℝ) ^ 2)⁻¹ • ∑ k ∈ face m μ, W (Function.update k μ s)
      - ((m : ℝ) ^ 3)⁻¹ • ∑ i ∈ cube m, W i‖ ≤ ((m : ℝ) ^ 2)⁻¹ * ∑ k ∈ face m μ, lam k := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : ‖∑ k ∈ face m μ, ∑ t ∈ Finset.range m, (W (Function.update k μ s) - W (Function.update k μ t))‖
        ≤ ∑ k ∈ face m μ, ∑ t ∈ Finset.range m, lam k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => (norm_sum_le _ _).trans ?_))
      refine Finset.sum_le_sum (fun t ht => ?_)
      exact norm_sub_le_path (fun r => W (Function.update k μ r)) m s t hs (Finset.mem_range.mp ht)
    have h2 : ∑ k ∈ face m μ, ∑ t ∈ Finset.range m, lam k = (m : ℝ) * ∑ k ∈ face m μ, lam k := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.mul_sum]
    calc ((m : ℝ) ^ 3)⁻¹ * ‖∑ k ∈ face m μ, ∑ t ∈ Finset.range m,
            (W (Function.update k μ s) - W (Function.update k μ t))‖
        ≤ ((m : ℝ) ^ 3)⁻¹ * ((m : ℝ) * ∑ k ∈ face m μ, lam k) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((m : ℝ) ^ 2)⁻¹ * ∑ k ∈ face m μ, lam k := by field_simp
  -- square
  have hsq1 : (∑ k ∈ face m μ, lam k) ^ 2 ≤ (m : ℝ) ^ 2 * ∑ k ∈ face m μ, lam k ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := face m μ) (f := lam)
    rw [card_face_real m hm μ] at this
    exact this
  have hsq2 : ∀ k, lam k ^ 2 ≤ (m : ℝ) * ∑ r ∈ Finset.range (m - 1),
      ‖W (Function.update k μ (r + 1)) - W (Function.update k μ r)‖ ^ 2 := by
    intro k
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (m - 1))
      (f := fun r => ‖W (Function.update k μ (r + 1)) - W (Function.update k μ r)‖)
    rw [Finset.card_range] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    have : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
    exact this
  have hn0 := norm_nonneg (((m : ℝ) ^ 2)⁻¹ • ∑ k ∈ face m μ, W (Function.update k μ s)
      - ((m : ℝ) ^ 3)⁻¹ • ∑ i ∈ cube m, W i)
  calc ‖((m : ℝ) ^ 2)⁻¹ • ∑ k ∈ face m μ, W (Function.update k μ s)
        - ((m : ℝ) ^ 3)⁻¹ • ∑ i ∈ cube m, W i‖ ^ 2
      ≤ (((m : ℝ) ^ 2)⁻¹ * ∑ k ∈ face m μ, lam k) ^ 2 := pow_le_pow_left₀ hn0 hnorm 2
    _ = ((m : ℝ) ^ 4)⁻¹ * (∑ k ∈ face m μ, lam k) ^ 2 := by rw [mul_pow]; ring
    _ ≤ ((m : ℝ) ^ 4)⁻¹ * ((m : ℝ) ^ 2 * ∑ k ∈ face m μ, lam k ^ 2) :=
        mul_le_mul_of_nonneg_left hsq1 (by positivity)
    _ ≤ ((m : ℝ) ^ 4)⁻¹ * ((m : ℝ) ^ 2 * ∑ k ∈ face m μ, ((m : ℝ) * ∑ r ∈ Finset.range (m - 1),
          ‖W (Function.update k μ (r + 1)) - W (Function.update k μ r)‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hsq2 k))
          (by positivity)) (by positivity)
    _ = (m : ℝ)⁻¹ * cubeEd m W μ := by
        rw [cubeEd_eq, ← Finset.mul_sum]
        field_simp

#print axioms parts_small
#print axioms parts_big
#print axioms cube_layer
#print axioms face_le_cube
#print axioms card_face_real
#print axioms layer_alg
#print axioms amgm
#print axioms cubeE_eq
#print axioms cubeEd_eq
#print axioms layer_dev

end AdalyFormal.LemIFlat

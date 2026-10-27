import LV3

/-!
# LV4 -- row-vs-flux errors and flux variation (all controlled by the gradient energy `E1`)

* `err_small` : `Σ_{z ∈ nℤ³} n ‖Rw n c z μ - Fl n n c z μ‖² ≤ 36 E1(c_μ)`.
* `err_big`   : `Σ_{Z ∈ (nℓ)ℤ³} (nℓ) ‖Rw (nℓ) c Z μ - Fl n (nℓ) c Z μ‖² ≤ 144 ℓ³ E1(c_μ)`.
* `Fl_shift`  : `Σ_{z ∈ nℤ³} ‖Fl n n c (z + off a) μ - Fl n n c (z + off b) μ‖² ≤ n⁻³ · 36 (R+n)² E1(c_μ)`
  (coordinates of `a, b` at most `R`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU)

variable {L : PeriodicLatticeExtent}

theorem single_le (μ ν : Fin 3) (t : ℕ) : (Pi.single μ t : Fin 3 → ℕ) ν ≤ t := by
  by_cases h : ν = μ
  · subst h; simp
  · simp [h]

theorem face_coord (m : ℕ) (μ : Fin 3) (x : Fin 3 → ℕ) (hx : x ∈ face m μ) (ν : Fin 3) :
    (x + (Pi.single μ (m - 1) : Fin 3 → ℕ)) ν ≤ m := by
  rw [mem_face] at hx
  rw [Pi.add_apply]
  by_cases h : ν = μ
  · subst h; rw [hx.2]; simp
  · simp only [Pi.single_apply, h, if_false, add_zero]; exact (hx.1 ν).le

theorem Rw_pair (m : ℕ) (c : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3) :
    Rw m c z μ = ((m : ℝ) ^ 3 * (Finset.range m).card)⁻¹ •
      ∑ u ∈ cube m, ∑ t ∈ Finset.range m, c (z + off L u + off L ((Pi.single μ t : Fin 3 → ℕ)), μ) := by
  unfold Rw
  rw [Finset.card_range, show ((m : ℝ) ^ 3 * ((m : ℕ) : ℝ))⁻¹ = ((m : ℝ) ^ 4)⁻¹ by ring]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun t _ => ?_))
  rw [off_single]

theorem Fl_pair (n m : ℕ) (hm : 0 < m) (c : Bond L → SuTwo) (z : PeriodicLatticeSite L) (μ : Fin 3)
    (a : Fin 3 → ℕ) :
    Fl n m c (z + off L a) μ = ((n : ℝ) ^ 3 * (face m μ).card)⁻¹ •
      ∑ v ∈ cube n, ∑ x ∈ face m μ, c (z + off L v + off L (a + (x + (Pi.single μ (m - 1) : Fin 3 → ℕ))), μ) := by
  unfold Fl flx
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  · rw [card_face m hm μ, mul_inv]; push_cast; ring
  · refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun x _ => ?_))
    rw [off_add, off_add, off_single]
    congr 2
    abel

/-- **row-vs-flux error, small rows** -/
theorem err_small (c : Bond L → SuTwo) (μ : Fin 3) {n : ℕ} (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1) :
    ∑ z ∈ latF L n, (n : ℝ) * ‖Rw n c z μ - Fl n n c z μ‖ ^ 2 ≤ 36 * E1 (fun x => c (x, μ)) := by
  have hF : ∀ z, Fl n n c z μ = ((n : ℝ) ^ 3 * (face n μ).card)⁻¹ •
      ∑ v ∈ cube n, ∑ x ∈ face n μ, c (z + off L v + off L (x + (Pi.single μ (n - 1) : Fin 3 → ℕ)), μ) := by
    intro z
    have h := Fl_pair n n hn c z μ 0
    rw [off_zero, add_zero] at h
    rw [h]
    simp only [zero_add]
  have hP := pair_le (fun x => c (x, μ)) hn hdvd (Finset.range n) (face n μ)
    (by rw [Finset.card_range]; exact hn) (by rw [card_face n hn μ]; positivity)
    (fun t => (Pi.single μ t : Fin 3 → ℕ)) (fun x => x + (Pi.single μ (n - 1) : Fin 3 → ℕ)) n
    (fun t ht ν => (single_le μ ν t).trans (Finset.mem_range.mp ht).le)
    (fun x hx ν => face_coord n μ x hx ν)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Finset.mul_sum]
  calc (n : ℝ) * ∑ z ∈ latF L n, ‖Rw n c z μ - Fl n n c z μ‖ ^ 2
      ≤ (n : ℝ) * (((n : ℝ) ^ 3)⁻¹ * (36 * (n : ℝ) ^ 2) * E1 (fun x => c (x, μ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hnr.le
        refine le_trans (le_of_eq ?_) hP
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Rw_pair, hF]
    _ = 36 * E1 (fun x => c (x, μ)) := by field_simp

/-- **row-vs-flux error, big rows** (`N = n ℓ`). -/
theorem err_big (c : Bond L → SuTwo) (μ : Fin 3) {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ)
    (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1) :
    ∑ Z ∈ latF L (n * ℓ), ((n * ℓ : ℕ) : ℝ) * ‖Rw (n * ℓ) c Z μ - Fl n (n * ℓ) c Z μ‖ ^ 2
      ≤ 144 * (ℓ : ℝ) ^ 3 * E1 (fun x => c (x, μ)) := by
  have hN : 0 < n * ℓ := Nat.mul_pos hn hℓ
  have hR : ∀ Z, Rw (n * ℓ) c Z μ = ((n : ℝ) ^ 3 * (cube ℓ ×ˢ Finset.range (n * ℓ)).card)⁻¹ •
      ∑ v ∈ cube n, ∑ p ∈ cube ℓ ×ˢ Finset.range (n * ℓ),
        c (Z + off L v + off L (n • p.1 + (Pi.single μ p.2 : Fin 3 → ℕ)), μ) := by
    intro Z
    unfold Rw
    rw [cube_decomp n ℓ hn, Finset.card_product, card_cube, Finset.card_range]
    congr 1
    · push_cast; ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun t _ => ?_))
      rw [off_add, off_add, off_single]
      congr 2
      abel
  have hF : ∀ Z, Fl n (n * ℓ) c Z μ = ((n : ℝ) ^ 3 * (face (n * ℓ) μ).card)⁻¹ •
      ∑ v ∈ cube n, ∑ x ∈ face (n * ℓ) μ, c (Z + off L v + off L (x + (Pi.single μ (n * ℓ - 1) : Fin 3 → ℕ)), μ) := by
    intro Z
    have h := Fl_pair n (n * ℓ) hN c Z μ 0
    rw [off_zero, add_zero] at h
    rw [h]
    simp only [zero_add]
  have hP := pair_le (fun x => c (x, μ)) hn hdvd (cube ℓ ×ˢ Finset.range (n * ℓ)) (face (n * ℓ) μ)
    (by rw [Finset.card_product, card_cube, Finset.card_range]; positivity)
    (by rw [card_face (n * ℓ) hN μ]; positivity)
    (fun p => n • p.1 + (Pi.single μ p.2 : Fin 3 → ℕ)) (fun x => x + (Pi.single μ (n * ℓ - 1) : Fin 3 → ℕ)) (2 * (n * ℓ))
    (by
      intro p hp ν
      rw [Finset.mem_product, mem_cube, Finset.mem_range] at hp
      have h1 := hp.1 ν
      have h2 := single_le μ ν p.2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : n * p.1 ν ≤ n * ℓ := Nat.mul_le_mul_left n h1.le
      omega)
    (fun x hx ν => (face_coord (n * ℓ) μ x hx ν).trans (by omega))
  -- the big lattice is inside the small one
  have hsub : latF L (n * ℓ) ⊆ latF L n := by
    intro Z hZ
    rw [mem_latF] at hZ ⊢
    intro ν
    exact (Dvd.intro _ rfl).trans (hZ ν)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [← Finset.mul_sum]
  have hmono : ∑ Z ∈ latF L (n * ℓ), ‖Rw (n * ℓ) c Z μ - Fl n (n * ℓ) c Z μ‖ ^ 2
      ≤ ∑ Z ∈ latF L n, ‖Rw (n * ℓ) c Z μ - Fl n (n * ℓ) c Z μ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  calc ((n * ℓ : ℕ) : ℝ) * ∑ Z ∈ latF L (n * ℓ), ‖Rw (n * ℓ) c Z μ - Fl n (n * ℓ) c Z μ‖ ^ 2
      ≤ ((n * ℓ : ℕ) : ℝ) * (((n : ℝ) ^ 3)⁻¹ * (36 * ((2 * (n * ℓ) : ℕ) : ℝ) ^ 2) * E1 (fun x => c (x, μ))) := by
        refine mul_le_mul_of_nonneg_left (hmono.trans ?_) (by positivity)
        refine le_trans (le_of_eq ?_) hP
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [hR, hF]
    _ = 144 * (ℓ : ℝ) ^ 3 * E1 (fun x => c (x, μ)) := by push_cast; field_simp; ring

/-- **flux variation** across translates. -/
theorem Fl_shift (c : Bond L → SuTwo) (μ : Fin 3) {n : ℕ} (hn : 0 < n) (hdvd : ∀ ν : Fin 3, n ∣ L ν + 1)
    (a b : Fin 3 → ℕ) (R : ℕ) (ha : ∀ ν, a ν ≤ R) (hb : ∀ ν, b ν ≤ R) :
    ∑ z ∈ latF L n, ‖Fl n n c (z + off L a) μ - Fl n n c (z + off L b) μ‖ ^ 2
      ≤ ((n : ℝ) ^ 3)⁻¹ * (36 * ((R + n : ℕ) : ℝ) ^ 2) * E1 (fun x => c (x, μ)) := by
  have hP := pair_le (fun x => c (x, μ)) hn hdvd (face n μ) (face n μ)
    (by rw [card_face n hn μ]; positivity) (by rw [card_face n hn μ]; positivity)
    (fun x => a + (x + (Pi.single μ (n - 1) : Fin 3 → ℕ))) (fun x => b + (x + (Pi.single μ (n - 1) : Fin 3 → ℕ))) (R + n)
    (fun x hx ν => by
      have := face_coord n μ x hx ν; have := ha ν
      simp only [Pi.add_apply] at *; omega)
    (fun x hx ν => by
      have := face_coord n μ x hx ν; have := hb ν
      simp only [Pi.add_apply] at *; omega)
  refine le_trans (le_of_eq ?_) hP
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Fl_pair n n hn, Fl_pair n n hn]

#print axioms single_le
#print axioms face_coord
#print axioms Rw_pair
#print axioms Fl_pair
#print axioms err_small
#print axioms err_big
#print axioms Fl_shift

end AdalyFormal.LemIFlat

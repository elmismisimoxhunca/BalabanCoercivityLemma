import LV8

/-!
# LV9 -- the patch bounds: `DPh ≤ (2/ℓ²) Gs`, `LPh ≤ 54 ℓ⁴ Gs`, `FBs ≤ Fbg`, `LF ≤ 72 ℓ²(ℓ+1)² Σ_μ E1(c_μ)`

All on the two-stratum patch (`Rg` a union of `ℓ^{j+1}`-blocks, `ℓ^{j+1} ∣ L+1`).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.FlatCoercivity (eU)
open AdalyFormal.StatementLane (BlockClosed)

variable {L : PeriodicLatticeExtent}

/-- the big block average is the mean of the cell averages. -/
theorem phm_big (n ℓ : ℕ) (hn : 0 < n) (φ : PeriodicLatticeSite L → SuTwo) (Z : PeriodicLatticeSite L) :
    Phm (n * ℓ) φ Z = (((ℓ : ℝ) ^ 3)⁻¹) • ∑ i ∈ cube ℓ, Phm n φ (Z + off L (n • i)) := by
  unfold Phm
  rw [cube_decomp n ℓ hn]
  simp only [← Finset.smul_sum, smul_smul]
  congr 1
  · push_cast; field_simp
  · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [off_add, add_assoc]

theorem cell_up (n : ℕ) (Z : PeriodicLatticeSite L) (i : Fin 3 → ℕ) (ν : Fin 3) :
    Z + off L (n • Function.update i ν (i ν + 1)) = Z + off L (n • i) + n • eU L ν := by
  have h := off_smul_update (L := L) n i ν (i ν + 1)
  have e : off L (n • Function.update i ν (i ν + 1)) = off L (n • i) + n • eU L ν := by
    rw [h, show n * (i ν + 1) = n * i ν + n by ring, add_nsmul]
    abel
  rw [e, add_assoc]

theorem le_ite_self (A : Prop) [Decidable A] (x : ℝ) (hx : 0 ≤ x) : (if A then x else 0) ≤ x := by
  split_ifs <;> linarith

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

open Classical in
/-- cube energies of the virtual blocks are small-row energies. -/
theorem cubeE_le (φ : PeriodicLatticeSite L → SuTwo) :
    ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then cubeE ell (fun i => Phm (ell ^ j) φ (Z + off L (ell ^ j • i))) else 0)
      ≤ ((ell ^ j : ℕ) : ℝ) * Gs ell j Rg φ := by
  have hn : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hell j
  have hGs : ((ell ^ j : ℕ) : ℝ) * Gs ell j Rg φ = ∑ ν : Fin 3, ∑ z ∈ latF L (ell ^ j),
      (if z ∉ Rg ∧ z + ell ^ j • eU L ν ∉ Rg then ‖Phm (ell ^ j) φ (z + ell ^ j • eU L ν) - Phm (ell ^ j) φ z‖ ^ 2
        else 0) := by
    unfold Gs
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    split_ifs
    · field_simp
    · simp
  rw [hGs]
  simp only [regroup hell hdvd]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun Z hZ => ?_)
  rw [mem_latF] at hZ
  by_cases hZR : Z ∈ Rg
  · rw [if_neg (not_not.mpr hZR)]
    exact Finset.sum_nonneg (fun ν _ => Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity))
  · rw [if_pos hZR, cubeE_eq]
    refine Finset.sum_le_sum (fun ν _ => ?_)
    unfold cubeEd
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum (fun i hi => ?_)
    split_ifs with h1 h2
    · beta_reduce
      rw [cell_up]
    · exfalso
      apply h2
      refine ⟨fun h => hZR ((cell_Rg hell hRg hdvd Z hZ i hi).mp h), fun h => ?_⟩
      have := (up_Rg hell hRg hdvd Z hZ hZR i hi ν).mp h
      omega
    · positivity
    · exact le_refl 0

open Classical in
/-- `DPh ≤ (2/ℓ²) Gs` (directional layer estimate). -/
theorem bound_DPh (φ : PeriodicLatticeSite L → SuTwo) :
    DPh ell j Rg φ ≤ 2 / (ell : ℝ) ^ 2 * Gs ell j Rg φ := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnr : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast hn
  have hlr : (0 : ℝ) < ell := by exact_mod_cast hell
  set W : PeriodicLatticeSite L → (Fin 3 → ℕ) → SuTwo := fun Z i => Phm (ell ^ j) φ (Z + off L (ell ^ j • i)) with hW
  have hB : ∀ Z, Phm (ell ^ j * ell) φ Z = (((ell : ℝ) ^ 3)⁻¹) • ∑ i ∈ cube ell, W Z i := fun Z => phm_big _ _ hn φ Z
  have htop : ∀ Z μ, ‖Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 ≤ (ell : ℝ)⁻¹ * cubeEd ell (W Z) μ := by
    intro Z μ
    have h := layer_dev ell hell (W Z) μ (ell - 1) (by omega)
    have e : Ptop ell j φ Z μ = (((ell : ℝ) ^ 2)⁻¹) • ∑ k ∈ face ell μ, W Z (Function.update k μ (ell - 1)) := by
      unfold Ptop
      congr 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [hW]
      rw [tz_eq (ell ^ j) ell Z k μ hk]
    rw [e, hB]; exact h
  have hbot : ∀ Z μ, ‖Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 ≤ (ell : ℝ)⁻¹ * cubeEd ell (W Z) μ := by
    intro Z μ
    have h := layer_dev ell hell (W Z) μ 0 hell
    have e : Pbot ell j φ Z μ = (((ell : ℝ) ^ 2)⁻¹) • ∑ k ∈ face ell μ, W Z (Function.update k μ 0) := by
      unfold Pbot
      congr 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [hW]
      rw [bz_eq (ell ^ j) ell Z k μ hk]
    rw [e, hB]; exact h
  have hcube := cubeE_le hell hRg hdvd φ
  have hpt : ∀ μ Z, (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)
        + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then
          ((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)) else 0)
      ≤ 2 * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * (ell : ℝ)⁻¹) *
          (if Z ∉ Rg then cubeEd ell (W Z) μ else 0) := by
    intro μ Z
    have hc0 : 0 ≤ cubeEd ell (W Z) μ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hN : (0 : ℝ) < ((ell ^ j * ell : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hn hell
    by_cases h0 : Z ∈ Rg
    · simp [h0]
    · rw [if_pos h0, if_pos h0]
      have a1 := le_ite_self (Z + (ell ^ j * ell) • eU L μ ∈ Rg)
        (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Ptop ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2) (by positivity)
      have a2 := le_ite_self (Z - (ell ^ j * ell) • eU L μ ∈ Rg)
        (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * ‖Pbot ell j φ Z μ - Phm (ell ^ j * ell) φ Z‖ ^ 2) (by positivity)
      have b1 := mul_le_mul_of_nonneg_left (htop Z μ) (le_of_lt (inv_pos.mpr hN))
      have b2 := mul_le_mul_of_nonneg_left (hbot Z μ) (le_of_lt (inv_pos.mpr hN))
      nlinarith
  unfold DPh
  calc ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), _
      ≤ ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), 2 * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * (ell : ℝ)⁻¹) *
          (if Z ∉ Rg then cubeEd ell (W Z) μ else 0) :=
        Finset.sum_le_sum (fun μ _ => Finset.sum_le_sum (fun Z _ => hpt μ Z))
    _ = 2 * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * (ell : ℝ)⁻¹) *
          ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then cubeE ell (W Z) else 0) := by
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun Z _ => ?_)
        rw [← Finset.mul_sum, cubeE_eq]
        split_ifs <;> simp
    _ ≤ 2 * (((ell ^ j * ell : ℕ) : ℝ)⁻¹ * (ell : ℝ)⁻¹) * (((ell ^ j : ℕ) : ℝ) * Gs ell j Rg φ) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 2 / (ell : ℝ) ^ 2 * Gs ell j Rg φ := by push_cast; field_simp

open Classical in
/-- `LPh ≤ 54 ℓ⁴ Gs` (cube Poincaré in the virtual blocks). -/
theorem bound_LPh (φ : PeriodicLatticeSite L → SuTwo) :
    LPh ell j Rg φ ≤ 54 * (ell : ℝ) ^ 4 * Gs ell j Rg φ := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnr : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast hn
  set W : PeriodicLatticeSite L → (Fin 3 → ℕ) → SuTwo := fun Z i => Phm (ell ^ j) φ (Z + off L (ell ^ j • i)) with hW
  have hB : ∀ Z, Phm (ell ^ j * ell) φ Z = ((1 : ℝ) / (ell : ℝ) ^ 3) • ∑ i ∈ cube ell, W Z i := by
    intro Z; rw [one_div]; exact phm_big _ _ hn φ Z
  have hP : ∀ Z, ∑ i ∈ cube ell, ‖W Z i - Phm (ell ^ j * ell) φ Z‖ ^ 2 ≤ 9 * (ell : ℝ) ^ 4 * cubeE ell (W Z) := by
    intro Z; rw [hB]; exact cube_poincare ell hell (W Z)
  have htop : ∀ Z μ, ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ)⁻¹
      * ‖Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2
      ≤ ((ell ^ j : ℕ) : ℝ)⁻¹ * (9 * (ell : ℝ) ^ 4 * cubeE ell (W Z)) := by
    intro Z μ
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((le_of_eq ?_).trans ((face_le_cube ell μ (ell - 1) (by omega)
      (fun i => ‖W Z i - Phm (ell ^ j * ell) φ Z‖ ^ 2) (fun _ => sq_nonneg _)).trans (hP Z))) (by positivity)
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [hW]
    rw [tz_eq (ell ^ j) ell Z k μ hk]
  have hbot : ∀ Z μ, ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ)⁻¹
      * ‖Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z‖ ^ 2
      ≤ ((ell ^ j : ℕ) : ℝ)⁻¹ * (9 * (ell : ℝ) ^ 4 * cubeE ell (W Z)) := by
    intro Z μ
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((le_of_eq ?_).trans ((face_le_cube ell μ 0 hell
      (fun i => ‖W Z i - Phm (ell ^ j * ell) φ Z‖ ^ 2) (fun _ => sq_nonneg _)).trans (hP Z))) (by positivity)
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [hW]
    rw [bz_eq (ell ^ j) ell Z k μ hk]
  have hcube := cubeE_le hell hRg hdvd φ
  have hpt : ∀ μ Z, (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)
        + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z‖ ^ 2 else 0)) else 0)
      ≤ 18 * (ell : ℝ) ^ 4 * ((ell ^ j : ℕ) : ℝ)⁻¹ * (if Z ∉ Rg then cubeE ell (W Z) else 0) := by
    intro μ Z
    have hc0 : 0 ≤ cubeE ell (W Z) := cubeE_nonneg ell (W Z)
    by_cases h0 : Z ∈ Rg
    · simp [h0]
    · rw [if_pos h0, if_pos h0]
      have a1 := le_ite_self (Z + (ell ^ j * ell) • eU L μ ∈ Rg) _
        (Finset.sum_nonneg (fun k _ => by positivity) : (0 : ℝ) ≤ ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (tz (ell ^ j) ell Z k μ) - Phm (ell ^ j * ell) φ Z‖ ^ 2)
      have a2 := le_ite_self (Z - (ell ^ j * ell) • eU L μ ∈ Rg) _
        (Finset.sum_nonneg (fun k _ => by positivity) : (0 : ℝ) ≤ ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ)⁻¹ * ‖Phm (ell ^ j) φ (bz (ell ^ j) Z k) - Phm (ell ^ j * ell) φ Z‖ ^ 2)
      have b1 := htop Z μ
      have b2 := hbot Z μ
      nlinarith
  unfold LPh
  calc ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), _
      ≤ ∑ μ : Fin 3, ∑ Z ∈ latF L (ell ^ j * ell), 18 * (ell : ℝ) ^ 4 * ((ell ^ j : ℕ) : ℝ)⁻¹ *
          (if Z ∉ Rg then cubeE ell (W Z) else 0) :=
        Finset.sum_le_sum (fun μ _ => Finset.sum_le_sum (fun Z _ => hpt μ Z))
    _ = 54 * (ell : ℝ) ^ 4 * ((ell ^ j : ℕ) : ℝ)⁻¹ *
          ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then cubeE ell (W Z) else 0) := by
        simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 54 * (ell : ℝ) ^ 4 * ((ell ^ j : ℕ) : ℝ)⁻¹ * (((ell ^ j : ℕ) : ℝ) * Gs ell j Rg φ) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 54 * (ell : ℝ) ^ 4 * Gs ell j Rg φ := by field_simp

open Classical in
/-- `FBs ≤ Fbg` (every interface face is a big row, counted once). -/
theorem bound_FBs (c : Bond L → SuTwo) :
    FBs ell j Rg c ≤ Fbg ell j Rg c := by
  have hdN : ∀ μ : Fin 3, ell ^ j * ell ∣ L μ + 1 := hdvd
  unfold FBs Fbg
  refine Finset.sum_le_sum (fun μ _ => ?_)
  set w := (ell ^ j * ell) • eU L μ with hw
  set g : PeriodicLatticeSite L → ℝ := fun Z =>
    ((ell ^ j * ell : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 with hg
  have hg0 : ∀ Z, 0 ≤ g Z := fun Z => by simp only [hg]; positivity
  have hsplit : ∀ Z, (if Z ∉ Rg then ((if Z + w ∈ Rg then g Z else 0) + (if Z - w ∈ Rg then g (Z - w) else 0)) else 0)
      = (if Z ∉ Rg ∧ Z + w ∈ Rg then g Z else 0) + (if Z ∉ Rg ∧ Z - w ∈ Rg then g (Z - w) else 0) := by
    intro Z
    by_cases h1 : Z ∈ Rg <;> by_cases h2 : Z + w ∈ Rg <;> by_cases h3 : Z - w ∈ Rg <;> simp [h1, h2, h3]
  show ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg then ((if Z + w ∈ Rg then g Z else 0)
      + (if Z - w ∈ Rg then g (Z - w) else 0)) else 0)
    ≤ ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∈ Rg ∨ Z + w ∈ Rg then g Z else 0)
  rw [Finset.sum_congr rfl (fun Z _ => hsplit Z), Finset.sum_add_distrib]
  have hre : ∑ Z ∈ latF L (ell ^ j * ell), (if Z ∉ Rg ∧ Z - w ∈ Rg then g (Z - w) else 0)
      = ∑ Z ∈ latF L (ell ^ j * ell), (if Z + w ∉ Rg ∧ Z ∈ Rg then g Z else 0) := by
    rw [sum_latF, sum_latF]
    have h := lat_translate hdN w (onLat_smul_eU hdN μ)
      (fun Z => if Z ∉ Rg ∧ Z - w ∈ Rg then g (Z - w) else 0)
    simp only [add_sub_cancel_right] at h
    exact h.symm
  rw [hre, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun Z _ => ?_)
  have := hg0 Z
  by_cases h1 : Z ∈ Rg <;> by_cases h2 : Z + w ∈ Rg <;> simp [h1, h2, this]

theorem layer_var (c : Bond L → SuTwo) (μ : Fin 3) (σ : PeriodicLatticeSite L) (hσ : OnLatN (ell ^ j) σ) :
    ∑ Z ∈ latF L (ell ^ j * ell), ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
      ‖Fl (ell ^ j) (ell ^ j) c (Z + σ + off L (ell ^ j • k)) μ
        - (((ell : ℝ) ^ 2)⁻¹) • ∑ k' ∈ face ell μ, Fl (ell ^ j) (ell ^ j) c (Z + σ + off L (ell ^ j • k')) μ‖ ^ 2
      ≤ 36 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E1 (fun x => c (x, μ)) := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnr : (0 : ℝ) < ((ell ^ j : ℕ) : ℝ) := by exact_mod_cast hn
  have hlr : (0 : ℝ) < ell := by exact_mod_cast hell
  have hdn' := hdn hell hRg hdvd
  have hK := card_face_real ell hell μ
  set F : PeriodicLatticeSite L → SuTwo := fun z => Fl (ell ^ j) (ell ^ j) c z μ with hF
  -- deviation from the mean
  have h1 : ∀ Z, ∀ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
      ‖F (Z + σ + off L (ell ^ j • k)) - (((ell : ℝ) ^ 2)⁻¹) • ∑ k' ∈ face ell μ, F (Z + σ + off L (ell ^ j • k'))‖ ^ 2
      ≤ ((ell ^ j : ℕ) : ℝ) * (((ell : ℝ) ^ 2)⁻¹ * ∑ k' ∈ face ell μ,
          ‖F (Z + σ + off L (ell ^ j • k)) - F (Z + σ + off L (ell ^ j • k'))‖ ^ 2) := by
    intro Z k _
    exact mul_le_mul_of_nonneg_left (dev_avg (face ell μ) _ hK (by positivity)
      (fun k => F (Z + σ + off L (ell ^ j • k))) k) hnr.le
  -- the lattice sums of pair differences
  have hsub : latF L (ell ^ j * ell) ⊆ latF L (ell ^ j) := by
    intro Z hZ
    rw [mem_latF] at hZ ⊢
    intro ν
    exact (Dvd.intro _ rfl).trans (hZ ν)
  have h2 : ∀ k ∈ face ell μ, ∀ k' ∈ face ell μ,
      ∑ Z ∈ latF L (ell ^ j * ell), ‖F (Z + σ + off L (ell ^ j • k)) - F (Z + σ + off L (ell ^ j • k'))‖ ^ 2
      ≤ ((ell ^ j : ℝ) ^ 3)⁻¹ * (36 * ((ell ^ j * ell + ell ^ j : ℕ) : ℝ) ^ 2) * E1 (fun x => c (x, μ)) := by
    intro k hk k' hk'
    have hcoord : ∀ q ∈ face ell μ, ∀ ν, (ell ^ j • q) ν ≤ ell ^ j * ell := by
      intro q hq ν
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Nat.mul_le_mul_left _ ((((mem_face ell μ q).mp hq).1 ν).le)
    have hsh := Fl_shift c μ hn hdn' (ell ^ j • k) (ell ^ j • k') (ell ^ j * ell) (hcoord k hk) (hcoord k' hk')
    have htr : ∑ z ∈ latF L (ell ^ j), ‖F (z + σ + off L (ell ^ j • k)) - F (z + σ + off L (ell ^ j • k'))‖ ^ 2
        = ∑ z ∈ latF L (ell ^ j), ‖F (z + off L (ell ^ j • k)) - F (z + off L (ell ^ j • k'))‖ ^ 2 := by
      rw [sum_latF, sum_latF]
      exact lat_translate hdn' σ hσ (fun z => ‖F (z + off L (ell ^ j • k)) - F (z + off L (ell ^ j • k'))‖ ^ 2)
    calc ∑ Z ∈ latF L (ell ^ j * ell), ‖F (Z + σ + off L (ell ^ j • k)) - F (Z + σ + off L (ell ^ j • k'))‖ ^ 2
        ≤ ∑ z ∈ latF L (ell ^ j), ‖F (z + σ + off L (ell ^ j • k)) - F (z + σ + off L (ell ^ j • k'))‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ = ∑ z ∈ latF L (ell ^ j), ‖F (z + off L (ell ^ j • k)) - F (z + off L (ell ^ j • k'))‖ ^ 2 := htr
      _ ≤ _ := by push_cast at hsh ⊢; exact hsh
  calc ∑ Z ∈ latF L (ell ^ j * ell), ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
        ‖F (Z + σ + off L (ell ^ j • k)) - (((ell : ℝ) ^ 2)⁻¹) • ∑ k' ∈ face ell μ, F (Z + σ + off L (ell ^ j • k'))‖ ^ 2
      ≤ ∑ Z ∈ latF L (ell ^ j * ell), ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * (((ell : ℝ) ^ 2)⁻¹ *
          ∑ k' ∈ face ell μ, ‖F (Z + σ + off L (ell ^ j • k)) - F (Z + σ + off L (ell ^ j • k'))‖ ^ 2) :=
        Finset.sum_le_sum (fun Z _ => Finset.sum_le_sum (fun k hk => h1 Z k hk))
    _ = ((ell ^ j : ℕ) : ℝ) * ((ell : ℝ) ^ 2)⁻¹ * ∑ k ∈ face ell μ, ∑ k' ∈ face ell μ,
          ∑ Z ∈ latF L (ell ^ j * ell), ‖F (Z + σ + off L (ell ^ j • k)) - F (Z + σ + off L (ell ^ j • k'))‖ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k' _ => Finset.sum_congr rfl (fun Z _ => ?_))
        ring
    _ ≤ ((ell ^ j : ℕ) : ℝ) * ((ell : ℝ) ^ 2)⁻¹ * ∑ k ∈ face ell μ, ∑ k' ∈ face ell μ,
          ((ell ^ j : ℝ) ^ 3)⁻¹ * (36 * ((ell ^ j * ell + ell ^ j : ℕ) : ℝ) ^ 2) * E1 (fun x => c (x, μ)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun k' hk' => h2 k hk k' hk')))
          (by positivity)
    _ = 36 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E1 (fun x => c (x, μ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hK]
        push_cast
        field_simp
        try ring

open Classical in
/-- `LF ≤ 72 ℓ² (ℓ+1)² Σ_μ E1(c_μ)` (flux variation along the interface layers). -/
theorem bound_LF (c : Bond L → SuTwo) :
    LF ell j Rg c ≤ 72 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * ∑ μ : Fin 3, E1 (fun x => c (x, μ)) := by
  have hn : 0 < ell ^ j := pow_pos hell j
  have hdn' := hdn hell hRg hdvd
  unfold LF
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun μ _ => ?_)
  have htop : ∀ Z, ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
        - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2
      = ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
        ‖Fl (ell ^ j) (ell ^ j) c (Z + (ell ^ j * (ell - 1)) • eU L μ + off L (ell ^ j • k)) μ
        - (((ell : ℝ) ^ 2)⁻¹) • ∑ k' ∈ face ell μ,
            Fl (ell ^ j) (ell ^ j) c (Z + (ell ^ j * (ell - 1)) • eU L μ + off L (ell ^ j • k')) μ‖ ^ 2 := by
    intro Z
    rw [face_rel c (ell ^ j) ell hn hell Z μ]
    unfold tz
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [add_right_comm Z (off L _) _]
  have hbot : ∀ Z, ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
        ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
          - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2
      = ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
        ‖Fl (ell ^ j) (ell ^ j) c (Z + -(ell ^ j • eU L μ) + off L (ell ^ j • k)) μ
        - (((ell : ℝ) ^ 2)⁻¹) • ∑ k' ∈ face ell μ,
            Fl (ell ^ j) (ell ^ j) c (Z + -(ell ^ j • eU L μ) + off L (ell ^ j • k')) μ‖ ^ 2 := by
    intro Z
    rw [face_rel c (ell ^ j) ell hn hell (Z - (ell ^ j * ell) • eU L μ) μ]
    simp only [tz_down (ell ^ j) ell hell Z]
    unfold bz
    have e : ∀ k, Z + off L (ell ^ j • k) - ell ^ j • eU L μ = Z + -(ell ^ j • eU L μ) + off L (ell ^ j • k) := by
      intro k; abel
    simp only [e]
  have hVt := layer_var hell hRg hdvd c μ ((ell ^ j * (ell - 1)) • eU L μ) (onLat_mul_smul hdn' (ell - 1) μ)
  have hVb := layer_var hell hRg hdvd c μ (-(ell ^ j • eU L μ)) (onLat_neg hdn' _ (onLat_smul_eU hdn' μ))
  have hpt : ∀ Z, (if Z ∉ Rg then
      ((if Z + (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 else 0)
        + (if Z - (ell ^ j * ell) • eU L μ ∈ Rg then ∑ k ∈ face ell μ,
          ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2 else 0)) else 0)
      ≤ ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2
        + ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2 := by
    intro Z
    have p1 : (0 : ℝ) ≤ ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have p2 : (0 : ℝ) ≤ ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
            ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    split_ifs <;> linarith
  calc _ ≤ ∑ Z ∈ latF L (ell ^ j * ell), (∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) *
            ‖Fl (ell ^ j) (ell ^ j) c (tz (ell ^ j) ell Z k μ) μ - Fl (ell ^ j) (ell ^ j * ell) c Z μ‖ ^ 2
        + ∑ k ∈ face ell μ, ((ell ^ j : ℕ) : ℝ) * ‖Fl (ell ^ j) (ell ^ j) c (bz (ell ^ j) Z k - ell ^ j • eU L μ) μ
            - Fl (ell ^ j) (ell ^ j * ell) c (Z - (ell ^ j * ell) • eU L μ) μ‖ ^ 2) :=
        Finset.sum_le_sum (fun Z _ => hpt Z)
    _ ≤ 36 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E1 (fun x => c (x, μ))
        + 36 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E1 (fun x => c (x, μ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_congr rfl (fun Z _ => htop Z), Finset.sum_congr rfl (fun Z _ => hbot Z)]
        exact add_le_add hVt hVb
    _ = 72 * (ell : ℝ) ^ 2 * ((ell : ℝ) + 1) ^ 2 * E1 (fun x => c (x, μ)) := by ring

#print axioms phm_big
#print axioms cell_up
#print axioms cubeE_le
#print axioms le_ite_self
#print axioms bound_DPh
#print axioms bound_LPh
#print axioms bound_FBs
#print axioms layer_var
#print axioms bound_LF

end patch

end AdalyFormal.LemIFlat

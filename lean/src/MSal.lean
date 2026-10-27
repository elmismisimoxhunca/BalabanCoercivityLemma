import MS1
import PSiteC18

/-!
# MSal -- LOCAL and ALIGNED telescoping of the nested composite (the hypothesis form the blocking estimates can supply)

PSiteC13 `NsZ_telescope_local` / PSiteC15 `level_data` assume the averaged-background bound at EVERY site of the blocks; the
staircases of the step averages only visit `ℓ^i`-ALIGNED sites (`PathIn_aligned`).  The tree/campaign blocking estimates
(`TowerClass`, BC1b; `link_tower_na_loc`, `cube_tower_class_na`, curvature_blocking NB25/NB26) bound the averaged links
only at aligned sites.  Here the same statements with the hypothesis restricted to aligned sites:
* `coarseShift_mem_coarse`, `PathIn_aligned`;
* `stepAverage_drift_sq_local_al`, `NsZ_stepAverage_drift_al`, `NsZ_telescope_local_al`;
* `level_data_al` : PSiteC15 `level_data` with `hT` only on the averaged links `(z, μ)` whose BOTH coarse endpoints
  `z, z + ℓ^i e_μ` lie in one level-`j` block, `z` `ℓ^i`-aligned (the links the staircases use).
* `PathIn2`, `PathIn2_of_PathIn`, `hol_dev_local2`, `chainZ_block_single`.
Proof texts are those of PSiteC12/13/15 (copied) with the link set restricted as stated.
Because only links with both endpoints in one block enter, a PER-BLOCK gauge can be used for these hypotheses (MS7).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1Site

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage stepAverage_trivialU Qcomposite
  Qcomposite_zero Qcomposite_succ stepAverage_add stepAverage_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_apply_ne coarseShift_val_eq)
open AdalyFormal.Balaban.PoincareBridge (coarseLattice_fits)

variable {L : PeriodicLatticeExtent}

theorem coarseShift_mem_coarse (s : ℕ) (hdvd : ∀ ν, s ∣ L ν + 1) (y : PeriodicLatticeSite L)
    (hy : y ∈ CoarseLattice L s) (μ : Fin 3) : coarseShift y s μ ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  by_cases hν : ν = μ
  · subst hν
    rw [coarseShift_val_eq, Nat.mod_mod_of_dvd _ (hdvd ν), Nat.add_mod_right]
    exact hy ν
  · rw [coarseShift_apply_ne y s μ ν hν]; exact hy ν

theorem PathIn_aligned (B : Set (PeriodicLatticeSite L)) (s : ℕ) (hdvd : ∀ ν, s ∣ L ν + 1) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), y ∈ CoarseLattice L s → PathIn B s y p →
      PathIn (B ∩ {z | z ∈ CoarseLattice L s}) s y p := by
  intro p
  induction p with
  | nil => intro _ _ _; trivial
  | cons μ rest ih =>
    intro y hy hP
    obtain ⟨hyB, hrest⟩ := hP
    exact ⟨⟨hyB, hy⟩, ih _ (coarseShift_mem_coarse s hdvd y hy μ) hrest⟩

/-- the path visits bases in `B` and each step ends in `C` -/
def PathIn2 (B C : Set (PeriodicLatticeSite L)) (s : ℕ) : PeriodicLatticeSite L → List (Fin 3) → Prop
  | _, [] => True
  | y, μ :: rest => y ∈ B ∧ coarseShift y s μ ∈ C ∧ PathIn2 B C s (coarseShift y s μ) rest

theorem PathIn2_of_PathIn (B C : Set (PeriodicLatticeSite L)) (s : ℕ) (hBC : B ⊆ C) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), PathIn B s y p →
      AdalyFormal.Balaban.TowerLawCov.coarsePathEndpoint s y p ∈ C → PathIn2 B C s y p := by
  intro p
  induction p with
  | nil => intro _ _ _; trivial
  | cons μ rest ih =>
    intro y hP hend
    obtain ⟨hyB, hrest⟩ := hP
    refine ⟨hyB, ?_, ih _ hrest hend⟩
    cases rest with
    | nil => exact hend
    | cons ν rest' => exact hBC hrest.1

theorem hol_dev_local2 (B C : Set (PeriodicLatticeSite L)) (s : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ}
    (hV : ∀ z ∈ B, ∀ μ : Fin 3, coarseShift z s μ ∈ C → frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ) :
    ∀ (p : List (Fin 3)) (y : PeriodicLatticeSite L), PathIn2 B C s y p →
      frobNorm (((coarsePathHolonomy s V y p : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ (p.length : ℝ) * δ := by
  intro p
  induction p with
  | nil =>
    intro y _
    show frobNorm (((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ _
    rw [AdalyFormal.Balaban.SuTwoLogExp.coe_one, sub_self, List.length_nil, Nat.cast_zero, zero_mul]
    exact le_of_eq AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero
  | cons μ rest ih =>
    intro y hy
    obtain ⟨hyB, hyC, hrest⟩ := hy
    show frobNorm (((V (y, μ) * coarsePathHolonomy s V (coarseShift y s μ) rest :
      Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ _
    refine le_trans (AdalyFormal.Balaban.RegularUQChain.frobNorm_su_mul_sub_one_le _ _) ?_
    have h1 := hV y hyB μ hyC
    have h2 := ih (coarseShift y s μ) hrest
    rw [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem stepBlock_sub_block {y x : PeriodicLatticeSite L} {s ell : ℕ} (hs : 0 < s) (hx : x ∈ stepBlockOf y s ell) :
    x ∈ blockOf y (s * ell) := by
  rw [← blockOf_biUnion hs, Finset.mem_biUnion]
  exact ⟨x, hx, by rw [mem_blockOf]; intro μ; exact ⟨le_rfl, by omega⟩⟩

/-- the chain of a top set: every chain block lies in ONE top block -/
theorem chainZ_block_single (ell : ℕ) (hell : 0 < ell) : ∀ (j : ℕ) (Λ : Finset (PeriodicLatticeSite L)),
    Λ ⊆ CoarseLattice L (ell ^ j) → ∀ i, i ≤ j → ∀ c ∈ chainZ ell j Λ i,
      ∃ y ∈ Λ, blockOf c (ell ^ i) ⊆ blockOf y (ell ^ j) := by
  intro j
  induction j with
  | zero =>
    intro Λ _ i hi c hc
    have : i = 0 := by omega
    subst this
    exact ⟨c, hc, Finset.Subset.refl _⟩
  | succ j ih =>
    intro Λ hΛ i hi c hc
    by_cases hij : i = j + 1
    · subst hij
      simp only [chainZ, if_true] at hc
      exact ⟨c, hc, Finset.Subset.refl _⟩
    · simp only [chainZ, if_neg hij] at hc
      have h1 : Λ ⊆ CoarseLattice L (ell ^ j * ell) := by rwa [← pow_succ]
      obtain ⟨y', hy', hsub⟩ := ih _ (upZ_subset_coarse h1) i (by omega) c hc
      unfold upZ at hy'
      rw [Finset.mem_biUnion] at hy'
      obtain ⟨y, hy, hy'y⟩ := hy'
      refine ⟨y, hy, hsub.trans ?_⟩
      intro x hx
      have hbu := blockOf_biUnion (L := L) (y := y) (s := ell ^ j) (ell := ell) (pow_pos hell j)
      rw [← pow_succ] at hbu
      rw [← hbu, Finset.mem_biUnion]
      exact ⟨y', hy'y, hx⟩

/-- pointwise LOCAL drift, links needed only at ALIGNED sites of the box -/
theorem stepAverage_drift_sq_local_al (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ ν, s ∣ L ν + 1)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1)
    (hV : ∀ z ∈ blockOf y (s * ell), z ∈ CoarseLattice L s → ∀ μ : Fin 3, coarseShift z s μ ∈ blockOf y (s * ell) →
      frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ)
    (g : PeriodicLatticeSite L → SuTwo) :
    ‖stepAverage s V ell g y - stepAverage s (trivialU L) ell g y‖ ^ 2
      ≤ (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
  have hcard := card_stepBlockOf_le y (ell := ell) hs
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  set ε : ℝ := 6 * ((ell : ℝ) - 1) * δ with hε
  have hpt : ∀ x ∈ stepBlockOf y s ell,
      ‖RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x) - g x‖ ≤ ε * ‖g x‖ := by
    intro x hx
    have h1 := AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le
      (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x)
    have hpath := PathIn_aligned (↑(blockOf y (s * ell)) : Set (PeriodicLatticeSite L)) s hdvd
      (coarseGammaPath s y x) y hy (gammaPath_PathIn hs hfit hx)
    have hend : AdalyFormal.Balaban.TowerLawCov.coarsePathEndpoint s y (coarseGammaPath s y x)
        ∈ (↑(blockOf y (s * ell)) : Set (PeriodicLatticeSite L)) := by
      have hxm := mem_stepBlockOf.mp hx
      rw [AdalyFormal.Balaban.QjComposite.coarsePathEndpoint_coarseGammaPath (fun μ => ⟨(hxm μ).1, (hxm μ).2.2⟩)]
      exact Finset.mem_coe.mpr (stepBlock_sub_block hs hx)
    have hpath2 := PathIn2_of_PathIn _ _ s Set.inter_subset_left (coarseGammaPath s y x) y hpath hend
    have h2 := hol_dev_local2 ((↑(blockOf y (s * ell)) : Set (PeriodicLatticeSite L)) ∩ {z | z ∈ CoarseLattice L s})
      (↑(blockOf y (s * ell))) s V
      (fun z hz μ hzs => hV z (Finset.mem_coe.mp hz.1) hz.2 μ (Finset.mem_coe.mp hzs)) (coarseGammaPath s y x) y hpath2
    have h3 := gammaPath_length_le y x hs hx
    have h3' : ((coarseGammaPath s y x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have : ((coarseGammaPath s y x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_mul, Nat.cast_sub hell] at this
      simpa using this
    have h4 : frobNorm
        (((coarsePathHolonomy s V y (coarseGammaPath s y x) : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 3 * ((ell : ℝ) - 1) * δ :=
      h2.trans (mul_le_mul_of_nonneg_right h3' hδ0)
    calc _ ≤ 2 * _ * ‖g x‖ := h1
      _ ≤ 2 * (3 * ((ell : ℝ) - 1) * δ) * ‖g x‖ := by gcongr
      _ = ε * ‖g x‖ := by rw [hε]; ring
  have hdiff : stepAverage s V ell g y - stepAverage s (trivialU L) ell g y
      = (1 / (ell : ℝ) ^ 3) • ∑ x ∈ stepBlockOf y s ell,
          (RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x) - g x) := by
    rw [stepAverage_trivialU, Finset.sum_sub_distrib, smul_sub]
    rfl
  have h1 : ‖stepAverage s V ell g y - stepAverage s (trivialU L) ell g y‖
      ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ε * ‖g x‖ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum hpt)
  have h2 := jensen_block (stepBlockOf y s ell) hell hcard (fun x => ε * ‖g x‖)
  calc _ ≤ ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ε * ‖g x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, (ε * ‖g x‖) ^ 2 := h2
    _ = ε ^ 2 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
        simp_rw [mul_pow, ← Finset.mul_sum]; ring

theorem coarse_of_coarse_mul {s ell : ℕ} {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L (s * ell)) :
    y ∈ CoarseLattice L s := by
  rw [mem_CoarseLattice] at hy ⊢
  intro ν
  exact Nat.mod_eq_zero_of_dvd (dvd_trans (Dvd.intro _ rfl) (Nat.dvd_of_mod_eq_zero (hy ν)))

/-- LOCAL ALIGNED one-step drift on `Z` -/
theorem NsZ_stepAverage_drift_al (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ ν, s ∣ L ν + 1)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {Z : Finset (PeriodicLatticeSite L)} (hZ : Z ⊆ CoarseLattice L (s * ell))
    (hfit : ∀ y ∈ Z, ∀ μ, (y μ).val + s * ell ≤ L μ + 1)
    (hV : ∀ y ∈ Z, ∀ z ∈ blockOf y (s * ell), z ∈ CoarseLattice L s → ∀ μ : Fin 3,
      coarseShift z s μ ∈ blockOf y (s * ell) → frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ)
    (g : PeriodicLatticeSite L → SuTwo) :
    NsZ (s * ell) Z (stepAverage s V ell g - stepAverage s (trivialU L) ell g)
      ≤ (6 * ((ell : ℝ) - 1) * δ) * NsZ s (upZ s ell Z) g := by
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  refine le_of_sq_le_sq' (mul_nonneg hε0 (NsZ_nonneg _ _ _)) ?_
  rw [NsZ_sq, mul_pow, NsZ_sq]
  have hpt := fun y (hy : y ∈ Z) => stepAverage_drift_sq_local_al s ell hs hell hdvd V hδ0 y
    (coarse_of_coarse_mul (hZ hy)) (hfit y hy) (hV y hy) g
  have h1 : ∑ y ∈ Z, ‖(stepAverage s V ell g - stepAverage s (trivialU L) ell g) y‖ ^ 2
      ≤ ∑ y ∈ Z, (6 * ((ell : ℝ) - 1) * δ) ^ 2 *
          ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) :=
    Finset.sum_le_sum (fun y hy => hpt y hy)
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_upZ hs hell hZ (fun x => ‖g x‖ ^ 2)] at h1
  have hℓ : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  calc ((s : ℝ) * ell) ^ 3 * ∑ y ∈ Z, ‖(stepAverage s V ell g - stepAverage s (trivialU L) ell g) y‖ ^ 2
      ≤ ((s : ℝ) * ell) ^ 3 * ((6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((1 / (ell : ℝ) ^ 3) *
          ∑ x ∈ upZ s ell Z, ‖g x‖ ^ 2)) := by gcongr
    _ = (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((s : ℝ) ^ 3 * ∑ x ∈ upZ s ell Z, ‖g x‖ ^ 2) := by
        field_simp

theorem NsZ_telescope_local_al (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (δ : ℕ → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (J : ℕ) (Zs : ℕ → Finset (PeriodicLatticeSite L))
    (hdvd : ∀ i, i < J → ∀ ν, ell ^ i ∣ L ν + 1)
    (hZc : ∀ i, i ≤ J → Zs i ⊆ CoarseLattice L (ell ^ i))
    (hchain : ∀ i, i < J → Zs i = upZ (ell ^ i) ell (Zs (i + 1)))
    (hfit : ∀ i, i < J → ∀ y ∈ Zs (i + 1), ∀ μ, (y μ).val + ell ^ i * ell ≤ L μ + 1)
    (hV : ∀ i, i < J → ∀ y ∈ Zs (i + 1), ∀ z ∈ blockOf y (ell ^ i * ell), z ∈ CoarseLattice L (ell ^ i) →
      ∀ μ : Fin 3, coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ i * ell) →
        frobNorm ((bg i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (f : PeriodicLatticeSite L → SuTwo) :
    ∀ j, j ≤ J → NsZ (ell ^ j) (Zs j)
        (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
      ≤ (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * NsZ 1 (Zs 0) f := by
  intro j
  induction j with
  | zero => intro _; simp [Qcomposite_zero, NsZ_zero]
  | succ j ih =>
    intro hj
    have ih := ih (Nat.le_of_succ_le hj)
    have hjJ : j < J := Nat.lt_of_succ_le hj
    have hs : 0 < ell ^ j := pow_pos hell j
    have hZ : Zs (j + 1) ⊆ CoarseLattice L (ell ^ j * ell) := by
      have := hZc (j + 1) hj; rwa [pow_succ] at this
    have hdec : Qcomposite bg ell (j + 1) f - Qcomposite (fun _ => trivialU L) ell (j + 1) f
        = stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
          + (stepAverage (ell ^ j) (bg j) ell (Qcomposite (fun _ => trivialU L) ell j f)
              - stepAverage (ell ^ j) (trivialU L) ell (Qcomposite (fun _ => trivialU L) ell j f)) := by
      funext y
      simp only [Qcomposite_succ, Pi.sub_apply, Pi.add_apply, stepAverage_sub]
      abel
    rw [hdec, pow_succ]
    refine le_trans (NsZ_add_le _ _ _ _) ?_
    have h1 := NsZ_stepAverage_le (ell ^ j) ell hs hell (bg j) hZ
      (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
    have h2 := NsZ_stepAverage_drift_al (ell ^ j) ell hs hell (hdvd j hjJ) (bg j) (hδ0 j) hZ (hfit j hjJ) (hV j hjJ)
      (Qcomposite (fun _ => trivialU L) ell j f)
    have h3 := NsZ_flat_le_chain ell hell J Zs hZc hchain f j (Nat.le_of_succ_le hj)
    rw [← hchain j hjJ] at h1 h2
    have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ j := by
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
      have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
      have := hδ0 j
      positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hε0
    rw [Finset.sum_range_succ, add_mul]
    linarith

/-- PSiteC15 `level_data` with the tower hypothesis at ALIGNED sites only. -/
theorem level_data_al (ell k : ℕ) (hell : 2 ≤ ell) (hdvd : ∀ μ, ell ^ k ∣ L μ + 1)
    {G : TowerGeom L} (hP : ProperTower G ell k) (U : Cfg L) (δ : ℕ → ℝ) (hδ0 : ∀ i, 0 ≤ δ i)
    {j : ℕ} (hj : j ≤ k)
    (hT : ∀ i, i < j → ∀ y0 ∈ G.Lam j, ∀ z ∈ blockOf y0 (ell ^ j), z ∈ CoarseLattice L (ell ^ i) → ∀ μ : Fin 3,
      coarseShift z (ell ^ i) μ ∈ blockOf y0 (ell ^ j) →
      frobNorm ((bgTower G U i (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ i)
    (E : ℝ) (hE : ∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i ≤ E)
    (g : PeriodicLatticeSite L → SuTwo) :
    (∑ x ∈ Rj G ell j, ‖g x‖ ^ 2
      ≤ 3 * ((ell : ℝ) ^ j) ^ 2 * ∑ y ∈ LamF G j, ∑ b ∈ inBlockBonds y (ell ^ j),
            ‖g (periodicLatticeShift b.1 b.2) - g b.1‖ ^ 2
        + 2 * NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g) ^ 2)
    ∧ NsZ (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g)
        ≤ NsZ (ell ^ j) (LamF G j) (Qcomposite (bgTower G U) ell j g) + E * NsZ 1 (Rj G ell j) g := by
  have hell0 : 0 < ell := by omega
  have hdvdj : ∀ μ, ell ^ j ∣ L μ + 1 := fun μ => Dvd.dvd.trans (pow_dvd_pow ell hj) (hdvd μ)
  have hLY : LamF G j ⊆ CoarseLattice L (ell ^ j) := fun y hy => hP.coarse j hj y (mem_LamF.mp hy)
  have hncast : (((ell ^ j : ℕ)) : ℝ) = (ell : ℝ) ^ j := by push_cast; rfl
  constructor
  · -- Poincare (as in level_data)
    rw [sum_Rj hP hj]
    have hp : ∀ y ∈ LamF G j, ∑ x ∈ blockOf y (ell ^ j), ‖g x‖ ^ 2 ≤
        3 * ((ell : ℝ) ^ j) ^ 2 * ∑ b ∈ inBlockBonds y (ell ^ j), ‖g (periodicLatticeShift b.1 b.2) - g b.1‖ ^ 2
          + 2 * (((ell : ℝ) ^ j) ^ 3 * ‖Qcomposite (fun _ => trivialU L) ell j g y‖ ^ 2) := by
      intro y hy
      have hfit := coarseLattice_fits hdvdj (hLY hy)
      have h := block_poincare_vector (pow_pos hell0 j) hfit g
      rw [hncast] at h
      have hF := Qflat_eq_blockMean ell hell0 g j y (hLY hy)
      rw [hF]
      simp only [hncast]
      nlinarith [h]
    have hs := Finset.sum_le_sum hp
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have hN := NsZ_sq (ell ^ j) (LamF G j) (Qcomposite (fun _ => trivialU L) ell j g)
    rw [hncast] at hN
    rw [hN]
    linarith [hs]
  · -- telescoping, aligned
    have hZc := chainZ_sub ell j (LamF G j) hLY
    have hchain := chainZ_step ell j (LamF G j) hLY
    have htel := NsZ_telescope_local_al ell hell0 (bgTower G U) δ hδ0 j (chainZ ell j (LamF G j))
      (fun i hi ν => Dvd.dvd.trans (pow_dvd_pow ell (by omega : i ≤ k)) (hdvd ν))
      (fun i hi => hZc i hi) (fun i hi => hchain i hi)
      (by
        intro i hi y hy μ
        have hy' := hZc (i + 1) (by omega) hy
        have hdv : ∀ ν, ell ^ (i + 1) ∣ L ν + 1 := fun ν =>
          Dvd.dvd.trans (pow_dvd_pow ell (by omega : i + 1 ≤ k)) (hdvd ν)
        have := coarseLattice_fits hdv hy' μ
        rwa [pow_succ] at this)
      (by
        intro i hi y hy z hz hzal μ hzs
        obtain ⟨y0, hy0, hsub⟩ := chainZ_block_single ell hell0 j (LamF G j) hLY (i + 1) (by omega) y hy
        have hz' : z ∈ blockOf y (ell ^ (i + 1)) := by rwa [pow_succ]
        have hzs' : coarseShift z (ell ^ i) μ ∈ blockOf y (ell ^ (i + 1)) := by rwa [pow_succ]
        exact hT i hi y0 (mem_LamF.mp hy0) z (hsub hz') hzal μ (hsub hzs'))
      g j le_rfl
    rw [chainZ_top] at htel
    have hmono : NsZ 1 (chainZ ell j (LamF G j) 0) g ≤ NsZ 1 (Rj G ell j) g := by
      refine NsZ_mono 1 ?_ g
      intro c hc
      have hblk := chainZ_blocks ell hell0 j (LamF G j) hLY 0 (Nat.zero_le j) c hc
      have hcb : c ∈ blockOf c (ell ^ 0) := by
        rw [mem_blockOf]; intro μ; simp
      exact hblk hcb
    have hE0 : 0 ≤ E := by
      refine le_trans ?_ hE
      refine Finset.sum_nonneg (fun i _ => ?_)
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell0
      have : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
      have := hδ0 i
      positivity
    set Q : PeriodicLatticeSite L → SuTwo := Qcomposite (bgTower G U) ell j g with hQ
    set F : PeriodicLatticeSite L → SuTwo := Qcomposite (fun _ => trivialU L) ell j g with hF
    have hFeq : F = Q - (Q - F) := by abel
    calc NsZ (ell ^ j) (LamF G j) F = NsZ (ell ^ j) (LamF G j) (Q - (Q - F)) := by rw [← hFeq]
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + NsZ (ell ^ j) (LamF G j) (Q - F) := NsZ_sub_le _ _ _ _
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * NsZ 1 (chainZ ell j (LamF G j) 0) g := by
          linarith [htel]
      _ ≤ NsZ (ell ^ j) (LamF G j) Q + E * NsZ 1 (Rj G ell j) g := by
          have h1 : (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * NsZ 1 (chainZ ell j (LamF G j) 0) g
              ≤ E * NsZ 1 (Rj G ell j) g :=
            mul_le_mul hE hmono (NsZ_nonneg _ _ _) hE0
          linarith

#print axioms coarseShift_mem_coarse
#print axioms PathIn_aligned
#print axioms PathIn2_of_PathIn
#print axioms hol_dev_local2
#print axioms stepBlock_sub_block
#print axioms chainZ_block_single
#print axioms stepAverage_drift_sq_local_al
#print axioms NsZ_stepAverage_drift_al
#print axioms NsZ_telescope_local_al
#print axioms level_data_al

#print axioms coarse_of_coarse_mul

end AdalyFormal.M1Site

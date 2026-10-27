import PSiteC12

/-!
# SiteC13 -- LOCAL one-step contraction / drift on finite sets `Z ⊆ Y_{s·ell}` and LOCAL telescoping along a chain `Z_0 ⊇ … ⊇ Z_J`
(`Z_i = ⋃_{c ∈ Z_{i+1}} stepBlockOf c ell^i ell`).  Only the links BASED in the blocks of `Z_{i+1}` are used.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.SiteCoercivity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage stepAverage_trivialU Qcomposite
  Qcomposite_zero Qcomposite_succ stepAverage_add stepAverage_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)

variable {L : PeriodicLatticeExtent}

/-- level-normalised norm on a finite set of centres -/
noncomputable def NsZ (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) : ℝ :=
  Real.sqrt ((s : ℝ) ^ 3) * Nf Z g

theorem NsZ_nonneg (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) :
    0 ≤ NsZ s Z g := mul_nonneg (Real.sqrt_nonneg _) (Nf_nonneg _ _)

theorem NsZ_sq (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) :
    NsZ s Z g ^ 2 = (s : ℝ) ^ 3 * ∑ y ∈ Z, ‖g y‖ ^ 2 := by
  unfold NsZ
  rw [mul_pow, Nf_sq, Real.sq_sqrt (by positivity)]

theorem NsZ_sub_le (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) (g h : PeriodicLatticeSite L → SuTwo) :
    NsZ s Z (g - h) ≤ NsZ s Z g + NsZ s Z h := by
  unfold NsZ
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Nf_sub_le _ _ _) (Real.sqrt_nonneg _)

theorem NsZ_add_le (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) (g h : PeriodicLatticeSite L → SuTwo) :
    NsZ s Z (g + h) ≤ NsZ s Z g + NsZ s Z h := by
  unfold NsZ
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Nf_add_le _ _ _) (Real.sqrt_nonneg _)

theorem NsZ_zero (s : ℕ) (Z : Finset (PeriodicLatticeSite L)) : NsZ s Z (0 : PeriodicLatticeSite L → SuTwo) = 0 := by
  have h := NsZ_sq s Z (0 : PeriodicLatticeSite L → SuTwo)
  simp only [Pi.zero_apply, norm_zero] at h
  simpa using h

theorem NsZ_mono (s : ℕ) {Z Z' : Finset (PeriodicLatticeSite L)} (h : Z ⊆ Z') (g : PeriodicLatticeSite L → SuTwo) :
    NsZ s Z g ≤ NsZ s Z' g := by
  refine le_of_sq_le_sq' (NsZ_nonneg _ _ _) ?_
  rw [NsZ_sq, NsZ_sq]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)) (by positivity)

/-- the union of the stride-`s` sub-blocks of the blocks `Z` -/
def upZ (s ell : ℕ) (Z : Finset (PeriodicLatticeSite L)) : Finset (PeriodicLatticeSite L) :=
  Z.biUnion (fun y => stepBlockOf y s ell)

theorem sum_upZ {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell) {Z : Finset (PeriodicLatticeSite L)}
    (hZ : Z ⊆ CoarseLattice L (s * ell)) (F : PeriodicLatticeSite L → ℝ) :
    ∑ y ∈ Z, ∑ x ∈ stepBlockOf y s ell, F x = ∑ x ∈ upZ s ell Z, F x := by
  unfold upZ
  rw [Finset.sum_biUnion]
  intro y hy y' hy' hne
  exact stepBlock_disjoint hs hell (hZ hy) (hZ hy') hne

theorem upZ_subset_coarse {s ell : ℕ} {Z : Finset (PeriodicLatticeSite L)} (hZ : Z ⊆ CoarseLattice L (s * ell)) :
    upZ s ell Z ⊆ CoarseLattice L s := by
  intro x hx
  unfold upZ at hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact stepBlock_mem_coarse (hZ hy) hxy

/-- LOCAL one-step contraction -/
theorem NsZ_stepAverage_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    {Z : Finset (PeriodicLatticeSite L)} (hZ : Z ⊆ CoarseLattice L (s * ell))
    (g : PeriodicLatticeSite L → SuTwo) :
    NsZ (s * ell) Z (stepAverage s V ell g) ≤ NsZ s (upZ s ell Z) g := by
  refine le_of_sq_le_sq' (NsZ_nonneg _ _ _) ?_
  rw [NsZ_sq, NsZ_sq]
  have hpt := fun y => stepAverage_sq_le s ell hs hell V g y
  have h1 : ∑ y ∈ Z, ‖stepAverage s V ell g y‖ ^ 2
      ≤ ∑ y ∈ Z, (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2 :=
    Finset.sum_le_sum (fun y _ => hpt y)
  rw [← Finset.mul_sum, sum_upZ hs hell hZ (fun x => ‖g x‖ ^ 2)] at h1
  have hℓ : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  calc ((s : ℝ) * ell) ^ 3 * ∑ y ∈ Z, ‖stepAverage s V ell g y‖ ^ 2
      ≤ ((s : ℝ) * ell) ^ 3 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ upZ s ell Z, ‖g x‖ ^ 2) := by gcongr
    _ = (s : ℝ) ^ 3 * ∑ x ∈ upZ s ell Z, ‖g x‖ ^ 2 := by field_simp


/-- pointwise LOCAL drift: only the links based in the box of `y` matter -/
theorem stepAverage_drift_sq_local (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (y : PeriodicLatticeSite L) (hfit : ∀ μ, (y μ).val + s * ell ≤ L μ + 1)
    (hV : ∀ z ∈ blockOf y (s * ell), ∀ μ : Fin 3, frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ)
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
    have h2 := hol_dev_local (↑(blockOf y (s * ell)) : Set (PeriodicLatticeSite L)) s V
      (fun z hz μ => hV z (Finset.mem_coe.mp hz) μ) (coarseGammaPath s y x) y (gammaPath_PathIn hs hfit hx)
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

/-- LOCAL one-step drift on `Z` -/
theorem NsZ_stepAverage_drift (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {Z : Finset (PeriodicLatticeSite L)} (hZ : Z ⊆ CoarseLattice L (s * ell))
    (hfit : ∀ y ∈ Z, ∀ μ, (y μ).val + s * ell ≤ L μ + 1)
    (hV : ∀ y ∈ Z, ∀ z ∈ blockOf y (s * ell), ∀ μ : Fin 3,
      frobNorm ((V (z, μ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ)
    (g : PeriodicLatticeSite L → SuTwo) :
    NsZ (s * ell) Z (stepAverage s V ell g - stepAverage s (trivialU L) ell g)
      ≤ (6 * ((ell : ℝ) - 1) * δ) * NsZ s (upZ s ell Z) g := by
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  refine le_of_sq_le_sq' (mul_nonneg hε0 (NsZ_nonneg _ _ _)) ?_
  rw [NsZ_sq, mul_pow, NsZ_sq]
  have hpt := fun y (hy : y ∈ Z) => stepAverage_drift_sq_local s ell hs hell V hδ0 y (hfit y hy) (hV y hy) g
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


/-- the flat nested composite is a contraction along a chain -/
theorem NsZ_flat_le_chain (ell : ℕ) (hell : 0 < ell) (J : ℕ) (Zs : ℕ → Finset (PeriodicLatticeSite L))
    (hZc : ∀ i, i ≤ J → Zs i ⊆ CoarseLattice L (ell ^ i))
    (hchain : ∀ i, i < J → Zs i = upZ (ell ^ i) ell (Zs (i + 1)))
    (f : PeriodicLatticeSite L → SuTwo) :
    ∀ j, j ≤ J → NsZ (ell ^ j) (Zs j) (Qcomposite (fun _ => trivialU L) ell j f) ≤ NsZ 1 (Zs 0) f := by
  intro j
  induction j with
  | zero => intro _; simp [Qcomposite_zero]
  | succ j ih =>
    intro hj
    have ih := ih (Nat.le_of_succ_le hj)
    have hs : 0 < ell ^ j := pow_pos hell j
    rw [Qcomposite_succ, pow_succ]
    have hZ : Zs (j + 1) ⊆ CoarseLattice L (ell ^ j * ell) := by
      have := hZc (j + 1) hj; rwa [pow_succ] at this
    refine le_trans (NsZ_stepAverage_le (ell ^ j) ell hs hell _ hZ _) ?_
    rw [← hchain j (Nat.lt_of_succ_le hj)]
    exact ih

theorem NsZ_telescope_local (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (δ : ℕ → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (J : ℕ) (Zs : ℕ → Finset (PeriodicLatticeSite L))
    (hZc : ∀ i, i ≤ J → Zs i ⊆ CoarseLattice L (ell ^ i))
    (hchain : ∀ i, i < J → Zs i = upZ (ell ^ i) ell (Zs (i + 1)))
    (hfit : ∀ i, i < J → ∀ y ∈ Zs (i + 1), ∀ μ, (y μ).val + ell ^ i * ell ≤ L μ + 1)
    (hV : ∀ i, i < J → ∀ y ∈ Zs (i + 1), ∀ z ∈ blockOf y (ell ^ i * ell), ∀ μ : Fin 3,
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
    have h2 := NsZ_stepAverage_drift (ell ^ j) ell hs hell (bg j) (hδ0 j) hZ (hfit j hjJ) (hV j hjJ)
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

end AdalyFormal.SiteCoercivity

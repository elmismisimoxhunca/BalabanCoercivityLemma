import PSiteC6
import BC1

/-!
# ASAl1 -- ALIGNED-bond versions of the one-step drift and the telescope of the nested site composite.

`PSiteC4.stepAverage_drift_sq`, `PSiteC5.Ns_stepAverage_drift`, `PSiteC6.Ns_telescope` assume `frobSupBond V ≤ δ` (ALL edges of the
fine torus).  The averages only read links on staircase paths from `s`-aligned sites inside `s`-aligned blocks, so the same conclusions
hold under the bound on the `s`-ALIGNED bonds only (`BC1.norm_RMap_coarseHol_sub_self_aligned`).  This is what the curvature-blocking
class (`link_tower_na`: aligned bonds) provides.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
namespace AdalyFormal.AsmM0

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf stepAverage stepAverage_trivialU Qcomposite
  Qcomposite_zero Qcomposite_succ stepAverage_add stepAverage_smul)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.ClassPropagationUbar (card_stepBlockOf_le gammaPath_length_le)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.SiteCoercivity (jensen_block Ns Ns_nonneg Ns_sq Ns_add_le Ns_sub_le Ns_stepAverage_le Ns_flat_le Ns_zero)
open AdalyFormal.SiteCoercivity (sum_stepBlock_le stepBlock_disjoint)

variable {L : PeriodicLatticeExtent}

/-- aligned-bond bound on a background -/
def AlignedLinkBound (s : ℕ) (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (δ : ℝ) : Prop :=
  ∀ z ∈ CoarseLattice L s, ∀ μ : Fin 3, frobNorm (((V (z, μ) : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ δ

theorem AlignedLinkBound.nonneg {s : ℕ} {V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} {δ : ℝ}
    (h : AlignedLinkBound s V δ) (hdvd : ∀ μ : Fin 3, s ∣ L μ + 1) : 0 ≤ δ := by
  have hz : (fun _ => (⟨0, by omega⟩ : Fin (L _ + 1)) : PeriodicLatticeSite L) ∈ CoarseLattice L s := by
    rw [mem_CoarseLattice]; intro ν; simp
  exact le_trans (AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _) (h _ hz 0)

theorem stepAverage_drift_sq_al (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ : AlignedLinkBound s V δ)
    (g : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) (hy : y ∈ CoarseLattice L s) :
    ‖stepAverage s V ell g y - stepAverage s (trivialU L) ell g y‖ ^ 2
      ≤ (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
  have hcard := card_stepBlockOf_le y (ell := ell) hs
  have hδ0 : 0 ≤ δ := hδ.nonneg hdvd
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  set ε : ℝ := 6 * ((ell : ℝ) - 1) * δ with hε
  have hpt : ∀ x ∈ stepBlockOf y s ell,
      ‖RMap (coarsePathHolonomy s V y (coarseGammaPath s y x)) (g x) - g x‖ ≤ ε * ‖g x‖ := by
    intro x hx
    have hvis : ∀ z ∈ CoarseLattice L s, ∀ μ : Fin 3, ‖RMap (V (z, μ)) (g x) - g x‖ ≤ 2 * δ * ‖g x‖ := by
      intro z hz μ
      refine le_trans (AdalyFormal.Balaban.RMapLipschitz.norm_RMap_sub_self_le (V (z, μ)) (g x)) ?_
      have := hδ z hz μ
      nlinarith [norm_nonneg (g x)]
    have h1 := AdalyFormal.BondComposite.norm_RMap_coarseHol_sub_self_aligned hdvd V (g x) (2 * δ * ‖g x‖) hvis
      (coarseGammaPath s y x) y hy
    have h3 := gammaPath_length_le y x hs hx
    have h3' : ((coarseGammaPath s y x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have : ((coarseGammaPath s y x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_mul, Nat.cast_sub hell] at this
      simpa using this
    have h2a : 0 ≤ 2 * δ * ‖g x‖ := by positivity
    calc _ ≤ ((coarseGammaPath s y x).length : ℝ) * (2 * δ * ‖g x‖) := h1
      _ ≤ (3 * ((ell : ℝ) - 1)) * (2 * δ * ‖g x‖) := mul_le_mul_of_nonneg_right h3' h2a
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

theorem Ns_stepAverage_drift_al (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, s ∣ L μ + 1)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ : AlignedLinkBound s V δ)
    (g : PeriodicLatticeSite L → SuTwo) :
    Ns (s * ell) (stepAverage s V ell g - stepAverage s (trivialU L) ell g)
      ≤ (6 * ((ell : ℝ) - 1) * δ) * Ns s g := by
  have hδ0 : 0 ≤ δ := hδ.nonneg hdvd
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  refine AdalyFormal.SiteCoercivity.le_of_sq_le_sq' (mul_nonneg hε0 (Ns_nonneg _ _)) ?_
  rw [Ns_sq, mul_pow, Ns_sq]
  have hal : ∀ y ∈ CoarseLattice L (s * ell), y ∈ CoarseLattice L s := by
    intro y hy
    rw [mem_CoarseLattice] at hy ⊢
    intro ν
    exact Nat.mod_eq_zero_of_dvd (dvd_trans (Dvd.intro _ rfl) (Nat.dvd_of_mod_eq_zero (hy ν)))
  have h1 : ∑ y ∈ CoarseLattice L (s * ell), ‖(stepAverage s V ell g - stepAverage s (trivialU L) ell g) y‖ ^ 2
      ≤ ∑ y ∈ CoarseLattice L (s * ell), (6 * ((ell : ℝ) - 1) * δ) ^ 2 *
          ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) :=
    Finset.sum_le_sum (fun y hy => stepAverage_drift_sq_al s ell hs hell hdvd V hδ g y (hal y hy))
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 := sum_stepBlock_le hs hell (fun x => ‖g x‖ ^ 2) (fun x => sq_nonneg _)
  have hℓ : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  calc ((s : ℝ) * ell) ^ 3 * ∑ y ∈ CoarseLattice L (s * ell), ‖(stepAverage s V ell g - stepAverage s (trivialU L) ell g) y‖ ^ 2
      ≤ ((s : ℝ) * ell) ^ 3 * ((6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((1 / (ell : ℝ) ^ 3) *
          ∑ y ∈ CoarseLattice L (s * ell), ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2)) := by gcongr
    _ = (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((s : ℝ) ^ 3 *
          ∑ y ∈ CoarseLattice L (s * ell), ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by
        field_simp
    _ ≤ (6 * ((ell : ℝ) - 1) * δ) ^ 2 * ((s : ℝ) ^ 3 * ∑ x ∈ CoarseLattice L s, ‖g x‖ ^ 2) := by gcongr

theorem Ns_telescope_al (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (δ : ℕ → ℝ)
    (J : ℕ) (hdvd : ∀ j, j ≤ J → ∀ μ : Fin 3, ell ^ j ∣ L μ + 1)
    (hδ : ∀ i, i < J → AlignedLinkBound (ell ^ i) (bg i) (δ i)) (f : PeriodicLatticeSite L → SuTwo) :
    ∀ j : ℕ, j ≤ J → Ns (ell ^ j) (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
      ≤ (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * Ns 1 f := by
  intro j
  induction j with
  | zero => intro _; simp [Qcomposite_zero, Ns_zero]
  | succ j ih =>
    intro hj
    have ih := ih (Nat.le_of_succ_le hj)
    have hδj : AlignedLinkBound (ell ^ j) (bg j) (δ j) := hδ j (Nat.lt_of_succ_le hj)
    have hs : 0 < ell ^ j := pow_pos hell j
    have hdec : Qcomposite bg ell (j + 1) f - Qcomposite (fun _ => trivialU L) ell (j + 1) f
        = stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
          + (stepAverage (ell ^ j) (bg j) ell (Qcomposite (fun _ => trivialU L) ell j f)
              - stepAverage (ell ^ j) (trivialU L) ell (Qcomposite (fun _ => trivialU L) ell j f)) := by
      funext y
      simp only [Qcomposite_succ, Pi.sub_apply, Pi.add_apply, AdalyFormal.SiteCoercivity.stepAverage_sub]
      abel
    rw [hdec, pow_succ]
    refine le_trans (Ns_add_le _ _ _) ?_
    have h1 := Ns_stepAverage_le (ell ^ j) ell hs hell (bg j)
      (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
    have h2 := Ns_stepAverage_drift_al (ell ^ j) ell hs hell (hdvd j (Nat.le_of_succ_le hj)) (bg j) hδj
      (Qcomposite (fun _ => trivialU L) ell j f)
    have h3 := Ns_flat_le ell hell f j
    have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ j := by
      have hδ0 : 0 ≤ δ j := hδj.nonneg (hdvd j (Nat.le_of_succ_le hj))
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
      have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
      positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hε0
    rw [Finset.sum_range_succ, add_mul]
    linarith

#print axioms stepAverage_drift_sq_al
#print axioms Ns_stepAverage_drift_al
#print axioms Ns_telescope_al

end AdalyFormal.AsmM0

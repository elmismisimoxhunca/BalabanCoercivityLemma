import PSiteC4

/-!
# SC5 -- level-normalised norms `Ns s g = sqrt(s³ Σ_{y ∈ Y_s} ‖g y‖²)` (`Y_s` = the stride-`s` centres), their triangle inequality,
one-step contraction and one-step drift in these norms.
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
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond)

variable {L : PeriodicLatticeExtent}

noncomputable def plY (Y : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) :
    PiLp 2 (fun _ : Y => SuTwo) := WithLp.toLp 2 (fun y : Y => g y.1)

noncomputable def Nf (Y : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) : ℝ := ‖plY Y g‖

theorem Nf_nonneg (Y : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) : 0 ≤ Nf Y g :=
  norm_nonneg _

theorem Nf_sq (Y : Finset (PeriodicLatticeSite L)) (g : PeriodicLatticeSite L → SuTwo) :
    Nf Y g ^ 2 = ∑ y ∈ Y, ‖g y‖ ^ 2 := by
  unfold Nf plY
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [WithLp.ofLp_toLp]
  exact Finset.sum_coe_sort Y (fun y => ‖g y‖ ^ 2)

theorem Nf_add_le (Y : Finset (PeriodicLatticeSite L)) (g h : PeriodicLatticeSite L → SuTwo) :
    Nf Y (g + h) ≤ Nf Y g + Nf Y h := by
  have : plY Y (g + h) = plY Y g + plY Y h := rfl
  unfold Nf
  rw [this]
  exact norm_add_le _ _

theorem Nf_sub_le (Y : Finset (PeriodicLatticeSite L)) (g h : PeriodicLatticeSite L → SuTwo) :
    Nf Y (g - h) ≤ Nf Y g + Nf Y h := by
  have : plY Y (g - h) = plY Y g - plY Y h := rfl
  unfold Nf
  rw [this]
  exact norm_sub_le _ _

/-- the level-normalised norm at stride `s` -/
noncomputable def Ns (s : ℕ) (g : PeriodicLatticeSite L → SuTwo) : ℝ :=
  Real.sqrt ((s : ℝ) ^ 3) * Nf (CoarseLattice L s) g

theorem Ns_nonneg (s : ℕ) (g : PeriodicLatticeSite L → SuTwo) : 0 ≤ Ns s g :=
  mul_nonneg (Real.sqrt_nonneg _) (Nf_nonneg _ _)

theorem Ns_sq (s : ℕ) (g : PeriodicLatticeSite L → SuTwo) :
    Ns s g ^ 2 = (s : ℝ) ^ 3 * ∑ y ∈ CoarseLattice L s, ‖g y‖ ^ 2 := by
  unfold Ns
  rw [mul_pow, Nf_sq, Real.sq_sqrt (by positivity)]

theorem Ns_sub_le (s : ℕ) (g h : PeriodicLatticeSite L → SuTwo) : Ns s (g - h) ≤ Ns s g + Ns s h := by
  unfold Ns
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Nf_sub_le _ _ _) (Real.sqrt_nonneg _)

theorem Ns_add_le (s : ℕ) (g h : PeriodicLatticeSite L → SuTwo) : Ns s (g + h) ≤ Ns s g + Ns s h := by
  unfold Ns
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Nf_add_le _ _ _) (Real.sqrt_nonneg _)

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  nlinarith

/-- ONE-STEP CONTRACTION in the level-normalised norms (any background `V`). -/
theorem Ns_stepAverage_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (g : PeriodicLatticeSite L → SuTwo) :
    Ns (s * ell) (stepAverage s V ell g) ≤ Ns s g := by
  refine le_of_sq_le_sq' (Ns_nonneg _ _) ?_
  rw [Ns_sq, Ns_sq]
  have hpt := fun y => stepAverage_sq_le s ell hs hell V g y
  have h1 : ∑ y ∈ CoarseLattice L (s * ell), ‖stepAverage s V ell g y‖ ^ 2
      ≤ ∑ y ∈ CoarseLattice L (s * ell), (1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2 :=
    Finset.sum_le_sum (fun y _ => hpt y)
  rw [← Finset.mul_sum] at h1
  have h2 := sum_stepBlock_le hs hell (fun x => ‖g x‖ ^ 2) (fun x => sq_nonneg _)
  have hℓ : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  push_cast
  calc ((s : ℝ) * ell) ^ 3 * ∑ y ∈ CoarseLattice L (s * ell), ‖stepAverage s V ell g y‖ ^ 2
      ≤ ((s : ℝ) * ell) ^ 3 * ((1 / (ell : ℝ) ^ 3) *
          ∑ y ∈ CoarseLattice L (s * ell), ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) := by gcongr
    _ = (s : ℝ) ^ 3 * ∑ y ∈ CoarseLattice L (s * ell), ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2 := by
        field_simp
    _ ≤ (s : ℝ) ^ 3 * ∑ x ∈ CoarseLattice L s, ‖g x‖ ^ 2 := by gcongr

/-- ONE-STEP DRIFT in the level-normalised norms: `Ns_{sℓ}((S(V) − S(1)) g) ≤ 6(ℓ-1)δ · Ns_s g`. -/
theorem Ns_stepAverage_drift (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) {δ : ℝ} (hδ : frobSupBond V ≤ δ)
    (g : PeriodicLatticeSite L → SuTwo) :
    Ns (s * ell) (stepAverage s V ell g - stepAverage s (trivialU L) ell g)
      ≤ (6 * ((ell : ℝ) - 1) * δ) * Ns s g := by
  have hδ0 : 0 ≤ δ := le_trans (by
    unfold frobSupBond
    exact (Finset.le_sup'_iff _).mpr ⟨(0, 0), Finset.mem_univ _, AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _⟩) hδ
  have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ := by
    have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
    positivity
  refine le_of_sq_le_sq' (mul_nonneg hε0 (Ns_nonneg _ _)) ?_
  rw [Ns_sq, mul_pow, Ns_sq]
  have hpt := fun y => stepAverage_drift_sq s ell hs hell V hδ g y
  have h1 : ∑ y ∈ CoarseLattice L (s * ell), ‖(stepAverage s V ell g - stepAverage s (trivialU L) ell g) y‖ ^ 2
      ≤ ∑ y ∈ CoarseLattice L (s * ell), (6 * ((ell : ℝ) - 1) * δ) ^ 2 *
          ((1 / (ell : ℝ) ^ 3) * ∑ x ∈ stepBlockOf y s ell, ‖g x‖ ^ 2) :=
    Finset.sum_le_sum (fun y _ => hpt y)
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

end AdalyFormal.SiteCoercivity

import PSiteC5

/-!
# SC6 -- telescoping: the nested composite `Q'_j` for ANY background tower `bg` stays within `Σ_{i<j} 6(ℓ-1) δ_i · Ns_1 f`
(level-normalised norm) of the FLAT nested composite, whenever `frobSupBond (bg i) ≤ δ_i` for `i < j`.
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

theorem stepAverage_sub (s ell : ℕ)
    (V : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (g h : PeriodicLatticeSite L → SuTwo) (y : PeriodicLatticeSite L) :
    stepAverage s V ell (g - h) y = stepAverage s V ell g y - stepAverage s V ell h y := by
  have : g - h = g + (-1 : ℝ) • h := by
    funext x; simp [sub_eq_add_neg]
  rw [this, stepAverage_add, stepAverage_smul]
  simp [sub_eq_add_neg]

theorem Ns_zero (s : ℕ) : Ns s (0 : PeriodicLatticeSite L → SuTwo) = 0 := by
  have h := Ns_sq s (0 : PeriodicLatticeSite L → SuTwo)
  simp only [Pi.zero_apply, norm_zero] at h
  simpa using h

/-- the flat nested composite is a contraction from the start -/
theorem Ns_flat_le (ell : ℕ) (hell : 0 < ell) (f : PeriodicLatticeSite L → SuTwo) :
    ∀ j : ℕ, Ns (ell ^ j) (Qcomposite (fun _ => trivialU L) ell j f) ≤ Ns 1 f := by
  intro j
  induction j with
  | zero => simp [Qcomposite_zero]
  | succ j ih =>
    rw [Qcomposite_succ, pow_succ]
    exact le_trans (Ns_stepAverage_le (ell ^ j) ell (pow_pos hell j) hell _ _) ih

theorem Ns_telescope (ell : ℕ) (hell : 0 < ell)
    (bg : ℕ → PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (δ : ℕ → ℝ)
    (J : ℕ) (hδ : ∀ i, i < J → frobSupBond (bg i) ≤ δ i) (f : PeriodicLatticeSite L → SuTwo) :
    ∀ j : ℕ, j ≤ J → Ns (ell ^ j) (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
      ≤ (∑ i ∈ Finset.range j, 6 * ((ell : ℝ) - 1) * δ i) * Ns 1 f := by
  intro j
  induction j with
  | zero => intro _; simp [Qcomposite_zero, Ns_zero]
  | succ j ih =>
    intro hj
    have ih := ih (Nat.le_of_succ_le hj)
    have hδj : frobSupBond (bg j) ≤ δ j := hδ j (Nat.lt_of_succ_le hj)
    have hs : 0 < ell ^ j := pow_pos hell j
    have hdec : Qcomposite bg ell (j + 1) f - Qcomposite (fun _ => trivialU L) ell (j + 1) f
        = stepAverage (ell ^ j) (bg j) ell (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
          + (stepAverage (ell ^ j) (bg j) ell (Qcomposite (fun _ => trivialU L) ell j f)
              - stepAverage (ell ^ j) (trivialU L) ell (Qcomposite (fun _ => trivialU L) ell j f)) := by
      funext y
      simp only [Qcomposite_succ, Pi.sub_apply, Pi.add_apply, stepAverage_sub]
      abel
    rw [hdec, pow_succ]
    refine le_trans (Ns_add_le _ _ _) ?_
    have h1 := Ns_stepAverage_le (ell ^ j) ell hs hell (bg j)
      (Qcomposite bg ell j f - Qcomposite (fun _ => trivialU L) ell j f)
    have h2 := Ns_stepAverage_drift (ell ^ j) ell hs hell (bg j) hδj
      (Qcomposite (fun _ => trivialU L) ell j f)
    have h3 := Ns_flat_le ell hell f j
    have hε0 : 0 ≤ 6 * ((ell : ℝ) - 1) * δ j := by
      have hδ0 : 0 ≤ δ j := le_trans (by
        unfold frobSupBond
        exact (Finset.le_sup'_iff _).mpr ⟨(0, 0), Finset.mem_univ _, AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _⟩) hδj
      have hℓ1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
      have : (0:ℝ) ≤ (ell:ℝ) - 1 := by linarith
      positivity
    have h4 := mul_le_mul_of_nonneg_left h3 hε0
    rw [Finset.sum_range_succ, add_mul]
    linarith

end AdalyFormal.SiteCoercivity

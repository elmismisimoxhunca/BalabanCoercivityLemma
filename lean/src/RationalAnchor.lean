import ResidualGate

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.G0Cert
open HConstruction.SmallNF HConstruction.Covariance HConstruction.SNFRepair HConstruction.Nonflat
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)

/-- The rational anchor retains the ACTUAL nonflat Hessian and site projection.
Only the bond averaging operator is replaced by its flat value. -/
def flatBondQ : H →L[ℝ] K := nativeLinearQ (trivialU witnessL) 2

def rationalAnchor : H →L[ℝ] H :=
  deltaU chosenU + (covGrad chosenU).comp
    ((siteRU chosenU).comp (covGrad chosenU).adjoint) +
    (8 : ℝ) • flatBondQ.adjoint.comp flatBondQ

theorem rationalAnchor_energy (A : H) :
    (inner ℝ A (rationalAnchor A) : ℝ) =
      inner ℝ A (deltaU chosenU A) + ‖gaugeConstraintU chosenU A‖^2 +
        8 * ‖flatBondQ A‖^2 := by
  rw [rationalAnchor, ← gaugeU_identity]
  simp only [add_apply, smul_apply, inner_add_right, inner_smul_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

theorem chosenPrecision_energy_split (A : H) :
    (inner ℝ A (chosenPrecision A) : ℝ) =
      inner ℝ A (deltaU chosenU A) + ‖gaugeConstraintU chosenU A‖^2 +
        8 * ‖nativeLinearQ chosenU 2 A‖^2 := by
  rw [chosenPrecision, precisionU, ← gaugeU_identity]
  simp only [add_apply, smul_apply, inner_add_right, inner_smul_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]
  ring

/-- Young estimate with rational constants; no unproved spectral input. -/
theorem averaging_young {E : Type*} [NormedAddCommGroup E]
    (q qf : E) :
    (3/4 : ℝ) * ‖qf‖^2 - 3 * ‖q - qf‖^2 ≤ ‖q‖^2 := by
  have ht : ‖qf‖ ≤ ‖q‖ + ‖q - qf‖ := by
    calc
      ‖qf‖ = ‖q - (q - qf)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖q‖ + ‖q - qf‖ := norm_sub_le _ _
  have hs : ‖qf‖^2 ≤ (‖q‖ + ‖q - qf‖)^2 := by
    nlinarith [norm_nonneg qf, norm_nonneg q, norm_nonneg (q-qf)]
  nlinarith [sq_nonneg (‖q‖ - 3 * ‖q-qf‖)]

/-- A fully source-identified reduction. The three displayed numerical estimates
are obligations, NOT assertions of this file. The negative Hessian floor is
essential; dropping it would incorrectly treat the bare Hessian as positive. -/
theorem chosen_lower_of_three_bounds
    (hanchor : ∀ A : H, (9/20 : ℝ) * ‖A‖^2 ≤ inner ℝ A (rationalAnchor A))
    (hdelta : ∀ A : H, -(3/5 : ℝ) * ‖A‖^2 ≤ inner ℝ A (deltaU chosenU A))
    (haverage : ∀ A : H,
      ‖nativeLinearQ chosenU 2 A - flatBondQ A‖ ≤ (1/15 : ℝ) * ‖A‖) :
    ∀ A : H, (97/1200 : ℝ) * ‖A‖^2 ≤ inner ℝ A (chosenPrecision A) := by
  intro A
  have ha := hanchor A
  rw [rationalAnchor_energy] at ha
  have hd := hdelta A
  have hq := haverage A
  have hq2 : ‖nativeLinearQ chosenU 2 A - flatBondQ A‖^2 ≤
      (1/225 : ℝ) * ‖A‖^2 := by
    nlinarith [norm_nonneg (nativeLinearQ chosenU 2 A - flatBondQ A), norm_nonneg A]
  have hy := averaging_young (nativeLinearQ chosenU 2 A) (flatBondQ A)
  rw [chosenPrecision_energy_split]
  nlinarith [sq_nonneg ‖gaugeConstraintU chosenU A‖]

/-- Positive form lower bounds give a quantitative inverse on a finite real
Hilbert space, not merely a totalized Ring.inverse. -/
theorem inverse_of_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (k : ℝ) (hk : 0 < k)
    (hT : ∀ x : E, k * ‖x‖^2 ≤ inner ℝ x (T x)) :
    ∃ G : E →L[ℝ] E, (∀ x, T (G x) = x) ∧ (∀ x, G (T x) = x) ∧
      (∀ x, ‖G x‖ ≤ k⁻¹ * ‖x‖) := by
  have hi : Function.Injective T := by
    intro x y hxy
    have hz : T (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    have h := hT (x-y)
    rw [hz, inner_zero_right] at h
    have hs : ‖x-y‖^2 ≤ 0 := (mul_le_mul_iff_left₀ hk).mp (by simpa [mul_comm] using h)
    have hn : ‖x-y‖ = 0 := by nlinarith [sq_nonneg ‖x-y‖, norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  obtain ⟨G, hright, hleft⟩ := (twoSidedInverse_iff_injective T).mpr hi
  refine ⟨G, hright, hleft, ?_⟩
  intro x
  have h := hT (G x)
  rw [hright] at h
  have hc := real_inner_le_norm (G x) x
  have hn : k * ‖G x‖ ≤ ‖x‖ := by
    by_cases hz : ‖G x‖ = 0
    · rw [hz, mul_zero]; exact norm_nonneg x
    · have hp : 0 < ‖G x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hk).mpr (by nlinarith)

/-- Quantitative matrix-element bound, applicable to every pair of unit
coordinate injections once their isometry is proved. -/
theorem inverse_pairing_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (G : E →L[ℝ] E) (C : ℝ)
    (hG : ∀ x, ‖G x‖ ≤ C * ‖x‖) (x y : E) :
    |inner ℝ x (G y)| ≤ C * ‖x‖ * ‖y‖ := by
  calc
    |inner ℝ x (G y)| ≤ ‖x‖ * ‖G y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (C * ‖y‖) := mul_le_mul_of_nonneg_left (hG y) (norm_nonneg x)
    _ = C * ‖x‖ * ‖y‖ := by ring

/-- Conditional certificate target with explicit inverse and kernel constants.
No hypothesis here has been discharged by a Python computation. -/
theorem chosen_G0_of_three_bounds
    (hanchor : ∀ A : H, (9/20 : ℝ) * ‖A‖^2 ≤ inner ℝ A (rationalAnchor A))
    (hdelta : ∀ A : H, -(3/5 : ℝ) * ‖A‖^2 ≤ inner ℝ A (deltaU chosenU A))
    (haverage : ∀ A : H,
      ‖nativeLinearQ chosenU 2 A - flatBondQ A‖ ≤ (1/15 : ℝ) * ‖A‖) :
    ∃ G : H →L[ℝ] H,
      (∀ A, chosenPrecision (G A) = A) ∧
      (∀ A, G (chosenPrecision A) = A) ∧
      (∀ A, ‖G A‖ ≤ (1200/97 : ℝ) * ‖A‖) ∧
      (∀ A B, |inner ℝ A (G B)| ≤ (1200/97 : ℝ) * ‖A‖ * ‖B‖) := by
  obtain ⟨G,hr,hl,hb⟩ := inverse_of_lower chosenPrecision (97/1200 : ℝ)
    (by norm_num) (chosen_lower_of_three_bounds hanchor hdelta haverage)
  have hb' : ∀ A, ‖G A‖ ≤ (1200/97 : ℝ) * ‖A‖ := by
    intro A
    simpa using hb A
  exact ⟨G,hr,hl,hb',inverse_pairing_bound G _ hb'⟩

end HConstruction.G0Cert

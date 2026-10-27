import CvD1

/-!
# CvD2 -- `<A, Delta_k A>` on the sigma_3 block: weight `cos(theta_p)` per plaquette (lane cover_jacobi_20261016)

`delta_sigma3_form`: for `CartanCfg U` and a sigma_3-valued bond field `A` (`diagP (A b) = A b`),
`deltaKQuadFormNormalizedCorrected U A = sum_p holCos U p * <curl_U A (p), curl_U A (p)>`.
So the genuine quadratic form of the printed `Delta_k` on the sigma_3 block is the flat plaquette form with weight
`cos(theta_p) = Re U(dp)_{00}` on each plaquette.  (The `D*D` term gives weight 1, the first `Delta'` term gives `cos(theta_p) - 1`,
the commutator term gives 0.)  Identification of `holCos` with `1`/`cos t` along `neU`: next module.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.CoverJacobi

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.NormalizationAudit

variable {L : PeriodicLatticeExtent}

theorem re_trace_self (X : SuTwo) : (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ))).re = -2 * hsInner X X := by
  rw [hsInner_def]; ring

theorem firstTerm_sigma3 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    deltaPrimeFirstTerm U A p =
      -2 * (holCos U p - 1) * hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) := by
  unfold deltaPrimeFirstTerm
  have h : reHolonomy U p - 1 = (((holCos U p - 1 : ℝ)) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [reHolonomy_eq hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_sub]
  rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, re_trace_self]
  ring

theorem diag_comm (f g : Fin 2 → ℂ) : Matrix.diagonal f * Matrix.diagonal g - Matrix.diagonal g * Matrix.diagonal f = 0 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have : (fun i => f i * g i) = (fun i => g i * f i) := funext (fun i => mul_comm _ _)
  rw [this]; simp

theorem exists_diag (Y : SuTwo) (h : diagP Y = Y) :
    ∃ g : Fin 2 → ℂ, (Y : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal g := by
  refine ⟨fun i => (Y : Matrix (Fin 2) (Fin 2) ℂ) i i, ?_⟩
  have := congrArg (fun X : SuTwo => (X : Matrix (Fin 2) (Fin 2) ℂ)) h
  simpa [diagP_coe] using this.symm

theorem comm_sigma3 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (A : Bond L → SuTwo) (hA : ∀ b, diagP (A b) = A b) (p : PeriodicLatticePlaquette L) :
    commutatorMatrixSum U A p = 0 := by
  have hR : ∀ (V : Matrix.specialUnitaryGroup (Fin 2) ℂ), IsCartan V → ∀ b, RMap V (A b) = A b := by
    intro V hV b
    have := RMap_diagP hV (A b)
    rwa [hA b] at this
  have d1 : diagP (AprimeZW U A p) = AprimeZW U A p := by
    unfold AprimeZW
    rw [map_neg, diagP_RMap (hU _), hA, hR _ (hU _)]
  have d2 : diagP (AprimeWX A p) = AprimeWX A p := by
    unfold AprimeWX
    rw [map_neg, hA]
  have d3 : diagP (AprimeXY A p) = AprimeXY A p := by
    unfold AprimeXY
    rw [hA]
  have d4 : diagP (AprimeYZ U A p) = AprimeYZ U A p := by
    unfold AprimeYZ
    rw [diagP_RMap (hU _), hA, hR _ (hU _)]
  obtain ⟨g1, e1⟩ := exists_diag _ d1
  obtain ⟨g2, e2⟩ := exists_diag _ d2
  obtain ⟨g3, e3⟩ := exists_diag _ d3
  obtain ⟨g4, e4⟩ := exists_diag _ d4
  simp only [commutatorMatrixSum]
  rw [e1, e2, e3, e4]
  simp only [diag_comm, add_zero, smul_zero]

theorem secondTerm_sigma3 {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (A : Bond L → SuTwo) (hA : ∀ b, diagP (A b) = A b) (p : PeriodicLatticePlaquette L) :
    deltaPrimeSecondTerm U A p = 0 := by
  unfold deltaPrimeSecondTerm
  rw [comm_sigma3 hU A hA p]
  simp

/-- **the printed `Delta_k` on the sigma_3 block of a Cartan configuration: weight `cos(theta_p)` on each plaquette.** -/
theorem delta_sigma3_form {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L} (hU : CartanCfg U)
    (A : Bond L → SuTwo) (hA : ∀ b, diagP (A b) = A b) :
    deltaKQuadFormNormalizedCorrected U A =
      ∑ p : PeriodicLatticePlaquette L, holCos U p * hsInner (curlValueCovariant U A p) (curlValueCovariant U A p) := by
  rw [deltaKQuadFormNormalizedCorrected_eq]
  unfold dstarDQuadForm covPlaqInner deltaPrimeQuadFormTransported
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [deltaPrimeFirstTermTransported_eq_neg, deltaPrimeSecondTermTransported_eq_neg, firstTerm_sigma3 hU,
    secondTerm_sigma3 hU A hA]
  ring

#print axioms re_trace_self
#print axioms firstTerm_sigma3
#print axioms diag_comm
#print axioms exists_diag
#print axioms comm_sigma3
#print axioms secondTerm_sigma3
#print axioms delta_sigma3_form

end AdalyFormal.CoverJacobi

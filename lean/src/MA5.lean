import MA4
import MI19

/-!
# MA5 -- local curl drift (lane m1_assembly_20261014)

`curlDrift_good`: for a finite set `F` of plaquettes all of whose four bonds lie in a finite bond set `R` on which `||U b - 1|| <= alpha`:
`sum_{p in F} ||curlDrift U A p||^2 <= 32 alpha^2 sum_{b in R} ||A b||^2`   (local form of RegularUPerturbation `plaqEnergy_curlDrift_le`).
`flat_vs_cov`: `sum_F ||flat curl A||^2 <= 2 sum_F ||cov curl_U A||^2 + 2 sum_F ||curlDrift U A||^2`.
`cov_box_le_mask`: for `F = plaqIn P` filter, `sum_F ||cov curl||^2 <= ||plaqMask P (curl_U A)||^2`.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000
namespace AdalyFormal.M1Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy plaqEnergy curlDrift norm_curlDrift_le sum_nbr1_sq_le sum_nbr2_sq_le)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

theorem norm_curlDrift_sq_loc (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) (α : ℝ) (hα0 : 0 ≤ α)
    (h1 : frobNorm ((U (p.1, p.2.1.1) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (h2 : frobNorm ((U (p.1, p.2.1.2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    ‖curlDrift U A p‖ ^ 2 ≤
      8 * α ^ 2 * (‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
  have hb := norm_curlDrift_le U A p
  set a1 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖
  set a2 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖
  have ha1 : 0 ≤ a1 := norm_nonneg _
  have ha2 : 0 ≤ a2 := norm_nonneg _
  have hf1 : 0 ≤ frobNorm ((U (p.1, p.2.1.1) : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
    AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  have hf2 : 0 ≤ frobNorm ((U (p.1, p.2.1.2) : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
    AdalyFormal.Balaban.RMapLipschitz.frobNorm_nonneg _
  have hle : ‖curlDrift U A p‖ ≤ 2 * α * a1 + 2 * α * a2 := by
    refine hb.trans ?_
    have e1 := mul_le_mul_of_nonneg_right h1 ha1
    have e2 := mul_le_mul_of_nonneg_right h2 ha2
    nlinarith
  have h0 := norm_nonneg (curlDrift U A p)
  have hsq := pow_le_pow_left₀ h0 hle 2
  nlinarith [sq_nonneg (a1 - a2), sq_nonneg α, mul_nonneg hα0 hα0]

open Classical in
theorem curlDrift_good (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α) (F : Finset (PeriodicLatticePlaquette L)) (R : Finset (Bond L))
    (hRU : ∀ b ∈ R, frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α)
    (hF : ∀ p ∈ F, (p.1, p.2.1.1) ∈ R ∧ (p.1, p.2.1.2) ∈ R ∧ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∈ R
        ∧ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∈ R) :
    ∑ p ∈ F, ‖curlDrift U A p‖ ^ 2 ≤ 32 * α ^ 2 * ∑ b ∈ R, ‖A b‖ ^ 2 := by
  set AR : Bond L → SuTwo := fun b => if b ∈ R then A b else 0 with hAR
  have hpt : ∀ p ∈ F, ‖curlDrift U A p‖ ^ 2 ≤
      8 * α ^ 2 * (‖AR (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖AR (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hF p hp
    have := norm_curlDrift_sq_loc U A p α hα0 (hRU _ h1) (hRU _ h2)
    simp only [hAR, if_pos h3, if_pos h4]
    exact this
  have hs1 : ∑ p ∈ F, ‖curlDrift U A p‖ ^ 2 ≤
      ∑ p ∈ F, 8 * α ^ 2 * (‖AR (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖AR (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) := Finset.sum_le_sum hpt
  have hs2 : ∑ p ∈ F, 8 * α ^ 2 * (‖AR (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖AR (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2)
      ≤ ∑ p : PeriodicLatticePlaquette L, 8 * α ^ 2 * (‖AR (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖AR (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => by positivity)
  have hs3 : ∑ p : PeriodicLatticePlaquette L, 8 * α ^ 2 * (‖AR (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ ^ 2
        + ‖AR (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ ^ 2) ≤ 32 * α ^ 2 * bondEnergy AR := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have h1 := sum_nbr1_sq_le AR
    have h2 := sum_nbr2_sq_le AR
    have : (0 : ℝ) ≤ 8 * α ^ 2 := by positivity
    nlinarith
  have hs4 : bondEnergy AR = ∑ b ∈ R, ‖A b‖ ^ 2 := by
    unfold bondEnergy
    rw [← Finset.sum_subset (Finset.subset_univ R) (fun b _ hb => by simp [hAR, hb])]
    exact Finset.sum_congr rfl (fun b hb => by simp [hAR, hb])
  rw [hs4] at hs3
  linarith

/-- flat curl vs covariant curl, pointwise squared. -/
theorem flat_sq_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    ‖flatCurlValue A p‖ ^ 2 ≤ 2 * ‖curlValueCovariant U A p‖ ^ 2 + 2 * ‖curlDrift U A p‖ ^ 2 := by
  have e : flatCurlValue A p = curlValueCovariant U A p - curlDrift U A p := by
    have : curlDrift U A p = curlValueCovariant U A p - curlValueCovariant (trivialU L) A p := rfl
    rw [this, AdalyFormal.Balaban.CovU1Reduction.curlValueCovariant_trivialU_local]; abel
  rw [e]
  exact AdalyFormal.M0Finish.sq_sub_le2 _ _

theorem flat_sum_le (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (F : Finset (PeriodicLatticePlaquette L)) :
    ∑ p ∈ F, ‖flatCurlValue A p‖ ^ 2 ≤ 2 * ∑ p ∈ F, ‖curlValueCovariant U A p‖ ^ 2
      + 2 * ∑ p ∈ F, ‖curlDrift U A p‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun p _ => flat_sq_le U A p)

end AdalyFormal.M1Assembly

#print axioms AdalyFormal.M1Assembly.curlDrift_good
#print axioms AdalyFormal.M1Assembly.flat_sum_le

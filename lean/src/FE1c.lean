import FE1b
import AdalyFormal.Balaban.BlockPoincareSharp

/-!
# FE1c -- CMP96 Lemma 2.4 / (2.128) at U = 1, su(2)-valued, for GENERAL block side `ell >= 2` (the replacement for `lemma24_flat`, which is `ell = 2` and `4 <= L`).
Scalar input: `BlockPoincareSharp.lemma24_sharpened` (`ell*Sum|Q1 B|^2 + Sum|d1 B|^2 >= (1/54) ell^-5 ||B||^2`, every `ell >= 2`, `ell < L+1`, `ell | L+1`, axial `B`);
the su(2) lift is the coordinatewise one of `SuTwoGeomU1` (energies are sums of three scalar energies).  At `ell = 2` the constant `(1/54)*ell^-5` is exactly `1/1728`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace AdalyFormal.FlatEllGeneral

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.LineIntegralAveraging (lineCoarseRestrict)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.CovariantOperators (SuTwo curlCovariantLM)
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.CovU1Reduction (flatCurlValue curlCovariantLM_trivialU_eq_flatCurlLM)
open AdalyFormal.Balaban.BlockPoincareLemma24 (coarseQEnergy totalCurlEnergy bondNormSq)

/-- the su(2) Lemma 2.4 at `U = 1`, general `ell >= 2`: for axial `B` with `Q_1 B = 0`,
`(1/54) ell^-5 Sum_b ||B b||^2 <= Sum_p ||flatCurlValue B p||^2`. -/
theorem lemma24_flat_gen {L : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → SuTwo)
    (hB : ∀ y ∈ CoarseLattice L ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0)
    (hQ : ∀ c, lineCoarseRestrictSuTwo ell B c = 0) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖B b‖ ^ 2 ≤
      ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B p‖ ^ 2 := by
  have hcomp : ∀ i : Fin 3, ((ell : ℝ) * coarseQEnergy ell (suComp i B) + totalCurlEnergy (suComp i B)
      ≥ (1 / 54) * (1 / (ell : ℝ) ^ 5) * bondNormSq (suComp i B)) := fun i =>
    AdalyFormal.Balaban.BlockPoincareSharp.lemma24_sharpened hell2 hstrict hdvd (suComp i B)
      (suComp_mem_admissible ell i B hB)
  have hq0 : ∀ i : Fin 3, coarseQEnergy ell (suComp i B) = 0 := by
    intro i
    unfold coarseQEnergy
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [← suCoordLM_lineCoarseRestrictSuTwo i ell B c, hQ c, map_zero]; simp
  have hN : ∑ b : Bond L, ‖B b‖ ^ 2 = ∑ i : Fin 3, bondNormSq (suComp i B) := by
    unfold bondNormSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suComp_apply]
  have hP : ∑ p : PeriodicLatticePlaquette L, ‖flatCurlValue B p‖ ^ 2 = ∑ i : Fin 3, totalCurlEnergy (suComp i B) := by
    unfold totalCurlEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_flatCurlValue]
  rw [hN, hP, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := hcomp i
  rw [hq0 i, mul_zero, zero_add, ge_iff_le] at h
  exact h

/-- the same, for the trivial-background covariant curl (the form `lemma24_flat` has) -/
theorem lemma24_flat_gen' {L : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < L μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (B : Bond L → SuTwo)
    (hB : ∀ y ∈ CoarseLattice L ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0)
    (hQ : ∀ c, lineCoarseRestrictSuTwo ell B c = 0) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) * ∑ b : Bond L, ‖B b‖ ^ 2 ≤
      ∑ p : PeriodicLatticePlaquette L,
        ‖curlCovariantLM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) B p‖ ^ 2 := by
  have h := lemma24_flat_gen hell2 hstrict hdvd B hB hQ
  have hc : ∀ p, curlCovariantLM (AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L) B p = flatCurlValue B p := by
    intro p; rw [curlCovariantLM_trivialU_eq_flatCurlLM]; rfl
  simp only [hc]; exact h

/-- the constant is the printed `(1/(12 d^2)) ell^{-(d+1)}` shape at `d = 3` only up to the exponent: `(1/54) ell^-5` equals `1/1728` at `ell = 2`
(and equals `(1/108) ell^-4` there), and is below `(1/108) ell^-4` for every `ell >= 3`. -/
theorem const_ell2 : (1 / 54 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 5) = 1 / 1728 := by norm_num

theorem const_printed_ell2 : (1 / 54 : ℝ) * (1 / ((2 : ℕ) : ℝ) ^ 5) = (1 / 108) * (1 / ((2 : ℕ) : ℝ) ^ 4) := by norm_num

theorem const_le_printed (ell : ℕ) (h2 : 2 ≤ ell) :
    (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) ≤ (1 / 108) * (1 / (ell : ℝ) ^ 4) := by
  have h : (2 : ℝ) ≤ ell := by exact_mod_cast h2
  have h4 : (0 : ℝ) < (ell : ℝ) ^ 4 := by positivity
  rw [show (1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5) = (1 / 54) * (1 / (ell : ℝ) ^ 4) * (1 / ell) by field_simp,
      show (1 / 108 : ℝ) * (1 / (ell : ℝ) ^ 4) = (1 / 54) * (1 / (ell : ℝ) ^ 4) * (1 / 2) by field_simp; ring]
  have : 1 / (ell : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h
  have hp : (0 : ℝ) ≤ (1 / 54) * (1 / (ell : ℝ) ^ 4) := by positivity
  exact mul_le_mul_of_nonneg_left this hp


/-- the su(2) Lemma 2.4 input at `U = 1` with constant `γ` (block side `ell`, unit torus `Lu`): axial `B` with `Q_1 B = 0` has `γ ‖B‖² ≤ Σ‖curl B‖²`. -/
def Lemma24Su (ell : ℕ) (Lu : PeriodicLatticeExtent) (γ : ℝ) : Prop :=
  ∀ B : Bond Lu → SuTwo,
    (∀ y ∈ CoarseLattice Lu ell, ∀ x ∈ blockOf y ell, ∀ b ∈ staircasePath y x, B b = 0) →
    (∀ c, lineCoarseRestrictSuTwo ell B c = 0) →
    γ * ∑ b : Bond Lu, ‖B b‖ ^ 2 ≤ ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue B p‖ ^ 2

theorem lemma24Su_sharp {Lu : PeriodicLatticeExtent} {ell : ℕ} (hell2 : 2 ≤ ell)
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hdvd : ∀ μ : Fin 3, ell ∣ (Lu μ + 1)) :
    Lemma24Su ell Lu ((1 / 54 : ℝ) * (1 / (ell : ℝ) ^ 5)) :=
  fun B hB hQ => lemma24_flat_gen hell2 hstrict hdvd B hB hQ

/-- scalar `Lemma24Conclusion`-shaped input (constant `γ`) lifts to su(2) -/
theorem lemma24Su_of_scalar {Lu : PeriodicLatticeExtent} {ell : ℕ} (γ : ℝ)
    (h : ∀ B : Bond Lu → ℝ, B ∈ admissibleSubspaceInter Lu ell →
      (ell : ℝ) * coarseQEnergy ell B + totalCurlEnergy B ≥ γ * bondNormSq B) :
    Lemma24Su ell Lu γ := by
  intro B hB hQ
  have hq0 : ∀ i : Fin 3, coarseQEnergy ell (suComp i B) = 0 := by
    intro i
    unfold coarseQEnergy
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [← suCoordLM_lineCoarseRestrictSuTwo i ell B c, hQ c, map_zero]; simp
  have hN : ∑ b : Bond Lu, ‖B b‖ ^ 2 = ∑ i : Fin 3, bondNormSq (suComp i B) := by
    unfold bondNormSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suComp_apply]
  have hP : ∑ p : PeriodicLatticePlaquette Lu, ‖flatCurlValue B p‖ ^ 2 = ∑ i : Fin 3, totalCurlEnergy (suComp i B) := by
    unfold totalCurlEnergy
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [norm_sq_suTwo_eq_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [suCoordLM_flatCurlValue i B p]
  rw [hN, hP, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h' := h (suComp i B) (suComp_mem_admissible ell i B hB)
  rw [hq0 i, mul_zero, zero_add, ge_iff_le] at h'
  exact h'

#print axioms lemma24Su_sharp
#print axioms lemma24Su_of_scalar
#print axioms lemma24_flat_gen
#print axioms lemma24_flat_gen'
#print axioms const_le_printed

end AdalyFormal.FlatEllGeneral

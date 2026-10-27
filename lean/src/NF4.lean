import AdalyFormal.Balaban.LemmaAssemblyNormalized
import AdalyFormal.Balaban.DeltaPrimeBound

/-!
# NF4 -- the tree's `Δ′` absorption (`LemmaAssembly`/`LemmaAssemblyNormalized`/`DeltaPrimeBound`) re-proved with the
PLAQUETTE-DEFECT hypothesis `PlaqDef α₀ U : ∀ p, ‖U(∂p) - 1‖_F ≤ 4√2·α₀` in place of `GaugeRegular α₀ U` (link smallness).
The two per-plaquette estimates are the tree's proofs VERBATIM except that the single use of
`frobNorm_holonomy_sub_one_le hα₀ U hreg p` is replaced by `hpl p`.  Link smallness `α₀ = α/n` forces only `‖Δ′‖ ≲ α/n`
(the tree's `DeltaPrimeBound`); the scaled budget needs `‖Δ′‖ ≲ α n⁻²`, i.e. plaquette-defect smallness `α₀ ~ α n⁻²`.
`plaqDef_of_gaugeRegular` shows `PlaqDef` is implied by `GaugeRegular` (a strict generalisation).
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace AdalyFormal.NonflatHunit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHj
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LineIntegralCovariant
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.AlphaAnalyticity
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaKFull (deltaKQuadFormCorrected)
open AdalyFormal.Balaban.NormalizationAudit
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg frobSq_holonomy_of_gaugeRegular
  frobNorm_holonomy_sub_one_le dstarDQuadForm_eq_sum_norm_sq sum_plaqBondSq_le abs_im_trace_comm_le
  abs_im_trace_commSum_le norm_AprimeXY norm_AprimeWX norm_AprimeYZ norm_AprimeZW
  frobSq_reHolonomy_sub_one_le frobSq_imHolonomy_le abs_re_trace_le abs_im_trace_le frobNorm_sub_le_sqrt_two
  frobNorm_mul_le frobNorm_coe_suTwo frobNorm_eq)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq
  frobSq_eq_trace frobSq_mul_right_isometry frobSq_sub_le frobSq_mul_le norm_sq_eq_half_frobSq)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-- plaquette-defect regularity: every plaquette holonomy is within `4√2·α₀` of `1` (Frobenius). -/
def PlaqDef (α₀ : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ p : PeriodicLatticePlaquette L,
    frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * α₀

theorem plaqDef_of_gaugeRegular {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hreg : GaugeRegular α₀ U) : PlaqDef α₀ U :=
  fun p => frobNorm_holonomy_sub_one_le hα₀ U hreg p

theorem abs_deltaPrimeFirstTerm_le' {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hpl : PlaqDef α₀ U) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |deltaPrimeFirstTerm U A p| ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by
  set K := (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ) with hK
  set R := reHolonomy U p - 1 with hR
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfK : frobNorm K = Real.sqrt 2 * ‖curlValueCovariant U A p‖ := frobNorm_coe_suTwo _
  -- the curvature factor
  have hRle : frobNorm R ≤ 4 * Real.sqrt 2 * α₀ := by
    have h1 : frobSq R ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
      frobSq_reHolonomy_sub_one_le U p
    have h2 := hpl p
    calc frobNorm R = Real.sqrt (frobSq R) := frobNorm_eq _
      _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :=
          Real.sqrt_le_sqrt h1
      _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
      _ ≤ 4 * Real.sqrt 2 * α₀ := h2
  have hK0 : 0 ≤ frobNorm K := frobNorm_nonneg _
  have hR0 : 0 ≤ frobNorm R := frobNorm_nonneg _
  have hn0 : 0 ≤ ‖curlValueCovariant U A p‖ := norm_nonneg _
  have hstep : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * (frobNorm K * frobNorm K * frobNorm R) := by
    have e1 : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * frobNorm (K * K * R) := by
      unfold deltaPrimeFirstTerm
      rw [← hK, ← hR]
      exact abs_re_trace_le _
    have e2 : frobNorm (K * K * R) ≤ frobNorm (K * K) * frobNorm R := frobNorm_mul_le _ _
    have e3 : frobNorm (K * K) ≤ frobNorm K * frobNorm K := frobNorm_mul_le _ _
    have e4 : frobNorm (K * K * R) ≤ frobNorm K * frobNorm K * frobNorm R := by
      calc frobNorm (K * K * R) ≤ frobNorm (K * K) * frobNorm R := e2
        _ ≤ frobNorm K * frobNorm K * frobNorm R :=
            mul_le_mul_of_nonneg_right e3 hR0
    calc |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * frobNorm (K * K * R) := e1
      _ ≤ Real.sqrt 2 * (frobNorm K * frobNorm K * frobNorm R) :=
          mul_le_mul_of_nonneg_left e4 (Real.sqrt_nonneg 2)
  refine hstep.trans ?_
  rw [hfK]
  have hfin : Real.sqrt 2 * (Real.sqrt 2 * ‖curlValueCovariant U A p‖
        * (Real.sqrt 2 * ‖curlValueCovariant U A p‖) * frobNorm R)
      = 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * frobNorm R := by
    have h : Real.sqrt 2 * (Real.sqrt 2 * ‖curlValueCovariant U A p‖
          * (Real.sqrt 2 * ‖curlValueCovariant U A p‖) * frobNorm R)
        = (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt 2
          * (‖curlValueCovariant U A p‖ * ‖curlValueCovariant U A p‖) * frobNorm R := by ring
    rw [h, hs2, sq]
  rw [hfin]
  have hmul : 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * frobNorm R
      ≤ 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀) := by
    have hcoef : (0 : ℝ) ≤ 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hRle hcoef
  refine hmul.trans (le_of_eq ?_)
  have h : 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀)
      = 8 * (Real.sqrt 2 * Real.sqrt 2) * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by ring
  rw [h, hs2]
  ring

theorem abs_deltaPrimeSecondTerm_le' {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hpl : PlaqDef α₀ U) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |deltaPrimeSecondTerm U A p| ≤ 72 * α₀ * plaqBondSq A p := by
  set M := imHolonomy U p with hM
  set a1 := (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha1
  set a2 := (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) with ha2
  set a3 := (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) with ha3
  set a4 := (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha4
  set S := ((a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1)
      + (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3)) with hS
  -- (i) the `I •` factor turns the real part into (minus) the imaginary part
  have hcs : commutatorMatrixSum U A p = Complex.I • S := rfl
  have hre : deltaPrimeSecondTerm U A p = -(Matrix.trace (S * M)).im := by
    unfold deltaPrimeSecondTerm
    rw [← hM, hcs, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, abs_neg]
  -- (ii) the six-term trace bound
  have hbound := abs_im_trace_commSum_le a1 a2 a3 a4 M S hS
  -- (iii) the Frobenius norms of the `A′` components, in terms of the bond values
  have hf : ∀ (X : SuTwo), frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 * ‖X‖ :=
    frobNorm_coe_suTwo
  set x1 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ with hx1
  set x2 := ‖A (p.1, p.2.1.2)‖ with hx2
  set x3 := ‖A (p.1, p.2.1.1)‖ with hx3
  set x4 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ with hx4
  have hfa1 : frobNorm a1 = Real.sqrt 2 * x1 := by
    rw [ha1, hf, hx1, norm_AprimeZW]
  have hfa2 : frobNorm a2 = Real.sqrt 2 * x2 := by
    rw [ha2, hf, hx2, norm_AprimeWX]
  have hfa3 : frobNorm a3 = Real.sqrt 2 * x3 := by
    rw [ha3, hf, hx3, norm_AprimeXY]
  have hfa4 : frobNorm a4 = Real.sqrt 2 * x4 := by
    rw [ha4, hf, hx4, norm_AprimeYZ]
  -- (iv) the curvature factor
  have hMle : frobNorm M ≤ 6 * α₀ := by
    have h1 : frobSq M ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
      rw [hM]; exact frobSq_imHolonomy_le U p
    have h2 := hpl p
    have h3 : frobNorm M ≤ 4 * Real.sqrt 2 * α₀ := by
      calc frobNorm M = Real.sqrt (frobSq M) := frobNorm_eq _
        _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) :=
            Real.sqrt_le_sqrt h1
        _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
        _ ≤ 4 * Real.sqrt 2 * α₀ := h2
    have h4 : Real.sqrt 2 ≤ 3 / 2 := AdalyFormal.Balaban.AlphaAnalyticity.sqrt_two_le
    nlinarith [h3, h4, hα₀]
  have hM0 : 0 ≤ frobNorm M := frobNorm_nonneg _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx10 : 0 ≤ x1 := norm_nonneg _
  have hx20 : 0 ≤ x2 := norm_nonneg _
  have hx30 : 0 ≤ x3 := norm_nonneg _
  have hx40 : 0 ≤ x4 := norm_nonneg _
  -- (v) assemble: 4·‖M‖_F·(Σ_{i<j} 2 x_i x_j) ≤ 12·‖M‖_F·Σ x_i² ≤ 72·α₀·Σ x_i²
  have hpair : frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
        + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
        + frobNorm a3 * frobNorm a4
      ≤ 3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
    rw [hfa1, hfa2, hfa3, hfa4]
    have hexp : Real.sqrt 2 * x1 * (Real.sqrt 2 * x2) + Real.sqrt 2 * x1 * (Real.sqrt 2 * x3)
        + Real.sqrt 2 * x1 * (Real.sqrt 2 * x4) + Real.sqrt 2 * x2 * (Real.sqrt 2 * x3)
        + Real.sqrt 2 * x2 * (Real.sqrt 2 * x4) + Real.sqrt 2 * x3 * (Real.sqrt 2 * x4)
        = (Real.sqrt 2 * Real.sqrt 2) * (x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4
            + x3 * x4) := by ring
    rw [hexp, hs2]
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4),
      sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x3 - x4)]
  have hfin : 4 * frobNorm M * (frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
        + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
        + frobNorm a3 * frobNorm a4)
      ≤ 72 * α₀ * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
    have hsum0 : 0 ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 := by positivity
    have hstep1 : 4 * frobNorm M * (frobNorm a1 * frobNorm a2 + frobNorm a1 * frobNorm a3
          + frobNorm a1 * frobNorm a4 + frobNorm a2 * frobNorm a3 + frobNorm a2 * frobNorm a4
          + frobNorm a3 * frobNorm a4)
        ≤ 4 * frobNorm M * (3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)) := by
      have h40 : (0 : ℝ) ≤ 4 * frobNorm M := by linarith
      exact mul_le_mul_of_nonneg_left hpair h40
    refine hstep1.trans ?_
    nlinarith [hMle, hsum0, hM0]
  refine hbound.trans (hfin.trans (le_of_eq ?_))
  unfold plaqBondSq
  rw [← hx1, ← hx2, ← hx3, ← hx4]
  ring

open AdalyFormal.Balaban.LemmaAssemblyNormalized (sum_plaqBondSq_eq)
open AdalyFormal.Balaban.DeltaPrimeBound (dstarDQuadForm_le_bondEnergy norm_sq_toLp)

theorem abs_deltaPrimeQuadForm_le_sharp' {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hpl : PlaqDef α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadForm U A| ≤ 16 * α₀ * dstarDQuadForm U A + 288 * α₀ * bondEnergy A := by
  have hterm : ∀ p : PeriodicLatticePlaquette L,
      |deltaPrimePlaqTerm U A p|
        ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p := by
    intro p
    have h1 := abs_deltaPrimeFirstTerm_le' hα₀ U hpl A p
    have h2 := abs_deltaPrimeSecondTerm_le' hα₀ U hpl A p
    unfold deltaPrimePlaqTerm
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hstep : |deltaPrimeQuadForm U A|
      ≤ ∑ p : PeriodicLatticePlaquette L,
          (16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 + 72 * α₀ * plaqBondSq A p) := by
    unfold deltaPrimeQuadForm
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => hterm p))
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← dstarDQuadForm_eq_sum_norm_sq, sum_plaqBondSq_eq]
  ring

theorem abs_deltaPrimeNormTransported_le_bondEnergy' {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hpl : PlaqDef α₀ U) (A : Bond L → SuTwo) :
    |deltaPrimeQuadFormNormalizedTransported U A| ≤ 272 * α₀ * bondEnergy A := by
  have h := abs_deltaPrimeQuadForm_le_sharp' hα₀ U hpl A
  have hd := dstarDQuadForm_le_bondEnergy U A
  have h8 : 8 * α₀ * dstarDQuadForm U A ≤ 8 * α₀ * (16 * bondEnergy A) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  unfold deltaPrimeQuadFormNormalizedTransported
  rw [abs_neg, deltaPrimeQuadFormNormalized_eq_half, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1 / 2 : ℝ))]
  linarith

/-- **`Δ′` AT A PLAQUETTE-SMALL BACKGROUND**: `|⟨x, Δ′_norm x⟩| ≤ 272 α₀ ‖x‖²` under `PlaqDef α₀ U`. -/
theorem abs_inner_deltaPrime_le_plaq {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hpl : PlaqDef α₀ U) (x : BondFnL2 L) :
    |(inner ℝ x (AdalyFormal.Balaban.DeltaPrimeOperator.deltaPrimeCLMNormalized U x) : ℝ)|
      ≤ 272 * α₀ * ‖x‖ ^ 2 := by
  obtain ⟨A, rfl⟩ : ∃ A : Bond L → SuTwo, x = WithLp.toLp 2 A := ⟨WithLp.ofLp x, rfl⟩
  rw [AdalyFormal.Balaban.DeltaPrimeOperator.inner_deltaPrimeCLMNormalized_eq, norm_sq_toLp]
  exact abs_deltaPrimeNormTransported_le_bondEnergy' hα₀ U hpl A

#print axioms plaqDef_of_gaugeRegular
#print axioms abs_deltaPrimeFirstTerm_le'
#print axioms abs_deltaPrimeSecondTerm_le'
#print axioms abs_deltaPrimeQuadForm_le_sharp'
#print axioms abs_deltaPrimeNormTransported_le_bondEnergy'
#print axioms abs_inner_deltaPrime_le_plaq

end AdalyFormal.NonflatHunit

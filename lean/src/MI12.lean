import MI9
import DLR26
import NF4

/-!
# MI12 -- per-plaquette curvature bounds and the holonomy regime (M1 lane E, 2026-10-13)

Regime (lane C's form, `HolRegime`): every plaquette with its four corners in `Ω_{j0}` has `dv(U(∂p)) ≤ ρ/ℓ^{2 j0}`.
* `dpFirst_le_p`, `dpSecond_le_p`, `bilPlaq_quad_le_p`, `bilPlaq_dv` : NF4 / DL26 per-term bounds with the curvature
  hypothesis at ONE plaquette (the NF4 proofs read `PlaqDef` only at `p`; re-proved here with the local hypothesis).
* `strat_near`, `pdist_corner1`, `pdist_corner2` : the corners of a plaquette are within `pdist ≤ 2`, strata differ by `≤ 1`.
* `hol_strat` : on `plaqIn Ω₀`, `dv(U(∂p)) ≤ ρ ℓ² / ℓ^{2 strat p₀}`.
(The stratified `Δ'` bound is MI13, the curvature/curl commutator MI14.)
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.M1IMS

open scoped RealInnerProductSpace
open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.StatementLane (Tower Admissible bigSide pdist)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf mem_blockOf CoarseLattice mem_CoarseLattice Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.Balaban.DeltaPrimeOperator (bilPlaq bilPlaq_diag)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.LemmaAssembly (plaqBondSq plaqBondSq_nonneg frobNorm_coe_suTwo abs_im_trace_commSum_le
  norm_AprimeXY norm_AprimeWX norm_AprimeYZ norm_AprimeZW frobSq_reHolonomy_sub_one_le frobSq_imHolonomy_le
  abs_re_trace_le frobNorm_mul_le frobNorm_eq)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg)

variable {L : PeriodicLatticeExtent}

/-! ## 1. per-plaquette `Δ'` bounds (NF4 with a LOCAL curvature hypothesis) -/

theorem dpFirst_le_p {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (hpl : frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * α₀) :
    |deltaPrimeFirstTerm U A p| ≤ 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by
  set K := (curlValueCovariant U A p : Matrix (Fin 2) (Fin 2) ℂ) with hK
  set R := reHolonomy U p - 1 with hR
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfK : frobNorm K = Real.sqrt 2 * ‖curlValueCovariant U A p‖ := frobNorm_coe_suTwo _
  have hRle : frobNorm R ≤ 4 * Real.sqrt 2 * α₀ := by
    have h1 : frobSq R ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) :=
      frobSq_reHolonomy_sub_one_le U p
    calc frobNorm R = Real.sqrt (frobSq R) := frobNorm_eq _
      _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) := Real.sqrt_le_sqrt h1
      _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
      _ ≤ 4 * Real.sqrt 2 * α₀ := hpl
  have hK0 : 0 ≤ frobNorm K := frobNorm_nonneg _
  have hR0 : 0 ≤ frobNorm R := frobNorm_nonneg _
  have hstep : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * (frobNorm K * frobNorm K * frobNorm R) := by
    have e1 : |deltaPrimeFirstTerm U A p| ≤ Real.sqrt 2 * frobNorm (K * K * R) := by
      unfold deltaPrimeFirstTerm
      rw [← hK, ← hR]
      exact abs_re_trace_le _
    have e2 : frobNorm (K * K * R) ≤ frobNorm (K * K) * frobNorm R := frobNorm_mul_le _ _
    have e3 : frobNorm (K * K) ≤ frobNorm K * frobNorm K := frobNorm_mul_le _ _
    have e4 : frobNorm (K * K * R) ≤ frobNorm K * frobNorm K * frobNorm R :=
      e2.trans (mul_le_mul_of_nonneg_right e3 hR0)
    exact e1.trans (mul_le_mul_of_nonneg_left e4 (Real.sqrt_nonneg 2))
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
      ≤ 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀) :=
    mul_le_mul_of_nonneg_left hRle (by positivity)
  refine hmul.trans (le_of_eq ?_)
  have h : 2 * Real.sqrt 2 * ‖curlValueCovariant U A p‖ ^ 2 * (4 * Real.sqrt 2 * α₀)
      = 8 * (Real.sqrt 2 * Real.sqrt 2) * α₀ * ‖curlValueCovariant U A p‖ ^ 2 := by ring
  rw [h, hs2]
  ring

theorem dpSecond_le_p {α₀ : ℝ} (hα₀ : 0 ≤ α₀)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (hpl : frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * α₀) :
    |deltaPrimeSecondTerm U A p| ≤ 72 * α₀ * plaqBondSq A p := by
  set M := imHolonomy U p with hM
  set a1 := (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha1
  set a2 := (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) with ha2
  set a3 := (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) with ha3
  set a4 := (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) with ha4
  set S := ((a1 * a2 - a2 * a1) + (a1 * a3 - a3 * a1) + (a1 * a4 - a4 * a1)
      + (a2 * a3 - a3 * a2) + (a2 * a4 - a4 * a2) + (a3 * a4 - a4 * a3)) with hS
  have hcs : commutatorMatrixSum U A p = Complex.I • S := rfl
  have hre : deltaPrimeSecondTerm U A p = -(Matrix.trace (S * M)).im := by
    unfold deltaPrimeSecondTerm
    rw [← hM, hcs, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, abs_neg]
  have hbound := abs_im_trace_commSum_le a1 a2 a3 a4 M S hS
  have hf : ∀ (X : SuTwo), frobNorm (X : Matrix (Fin 2) (Fin 2) ℂ) = Real.sqrt 2 * ‖X‖ :=
    frobNorm_coe_suTwo
  set x1 := ‖A (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)‖ with hx1
  set x2 := ‖A (p.1, p.2.1.2)‖ with hx2
  set x3 := ‖A (p.1, p.2.1.1)‖ with hx3
  set x4 := ‖A (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)‖ with hx4
  have hfa1 : frobNorm a1 = Real.sqrt 2 * x1 := by rw [ha1, hf, hx1, norm_AprimeZW]
  have hfa2 : frobNorm a2 = Real.sqrt 2 * x2 := by rw [ha2, hf, hx2, norm_AprimeWX]
  have hfa3 : frobNorm a3 = Real.sqrt 2 * x3 := by rw [ha3, hf, hx3, norm_AprimeXY]
  have hfa4 : frobNorm a4 = Real.sqrt 2 * x4 := by rw [ha4, hf, hx4, norm_AprimeYZ]
  have hMle : frobNorm M ≤ 6 * α₀ := by
    have h1 : frobSq M ≤ frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := by
      rw [hM]; exact frobSq_imHolonomy_le U p
    have h3 : frobNorm M ≤ 4 * Real.sqrt 2 * α₀ := by
      calc frobNorm M = Real.sqrt (frobSq M) := frobNorm_eq _
        _ ≤ Real.sqrt (frobSq ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1)) := Real.sqrt_le_sqrt h1
        _ = frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) := (frobNorm_eq _).symm
        _ ≤ 4 * Real.sqrt 2 * α₀ := hpl
    have h4 : Real.sqrt 2 ≤ 3 / 2 := AdalyFormal.Balaban.AlphaAnalyticity.sqrt_two_le
    nlinarith [h3, h4, hα₀]
  have hM0 : 0 ≤ frobNorm M := frobNorm_nonneg _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx10 : 0 ≤ x1 := norm_nonneg _
  have hx20 : 0 ≤ x2 := norm_nonneg _
  have hx30 : 0 ≤ x3 := norm_nonneg _
  have hx40 : 0 ≤ x4 := norm_nonneg _
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
        ≤ 4 * frobNorm M * (3 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2)) :=
      mul_le_mul_of_nonneg_left hpair (by linarith)
    refine hstep1.trans ?_
    nlinarith [hMle, hsum0, hM0]
  refine hbound.trans (hfin.trans (le_of_eq ?_))
  unfold plaqBondSq
  rw [← hx1, ← hx2, ← hx3, ← hx4]
  ring

theorem bilPlaq_quad_le_p (U : Cfg L) {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L)
    (hpl : frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * α₀) :
    |bilPlaq U p A A| ≤ 136 * α₀ * plaqBondSq A p := by
  rw [bilPlaq_diag, AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTermTransported_eq_neg,
    AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTermTransported_eq_neg]
  have h1 := dpFirst_le_p hα₀ U A p hpl
  have h2 := dpSecond_le_p hα₀ U A p hpl
  have h3 := curl_sq_le_pbs U A p
  have h4 : 16 * α₀ * ‖curlValueCovariant U A p‖ ^ 2 ≤ 16 * α₀ * (4 * plaqBondSq A p) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : -AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTerm U A p
      + -AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTerm U A p
      = -(AdalyFormal.Balaban.DeltaPrime.deltaPrimeFirstTerm U A p
        + AdalyFormal.Balaban.DeltaPrime.deltaPrimeSecondTerm U A p) := by ring
  rw [e, abs_neg]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- `|bilPlaq U p A A| ≤ (34/√2) dv(U(∂p)) ‖A‖²_{∂p}` (the curvature read at `p` only). -/
theorem bilPlaq_dv (U : Cfg L) (A : Bond L → SuTwo) (p : PeriodicLatticePlaquette L) :
    |bilPlaq U p A A| ≤ (34 / Real.sqrt 2) * AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
      * plaqBondSq A p := by
  set d := AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
  have hd0 : 0 ≤ d := frobNorm_nonneg _
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpl : frobNorm ((holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ 4 * Real.sqrt 2 * (d / (4 * Real.sqrt 2)) := by
    rw [mul_div_cancel₀ _ (by positivity)]; exact le_rfl
  have h := bilPlaq_quad_le_p U (by positivity : 0 ≤ d / (4 * Real.sqrt 2)) A p hpl
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## 2. the stratified curvature regime -/

section strat
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}

/-- lane C's holonomy regime (`site_coercive_M1_hol`, `hhol`). -/
def HolRegime (S : Tower Lf) (ell k : ℕ) (U : Cfg Lf) (ρ : ℝ) : Prop :=
  ∀ j0, j0 ≤ k → ∀ p : PeriodicLatticePlaquette Lf,
    p.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.1 ∈ S.Om j0 → periodicLatticeShift p.1 p.2.1.2 ∈ S.Om j0 →
    periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S.Om j0 →
    AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ ρ / (ell : ℝ) ^ (2 * j0)

variable (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR1 : 1 ≤ R) (hM1 : 1 ≤ M)
include hS hell hR1 hM1

/-- sites within ℓ¹ distance 2 have strata within one. -/
theorem strat_near {x y : PeriodicLatticeSite Lf} (h : pdist x y ≤ 2) :
    AdalyFormal.M1.strat S k y ≤ AdalyFormal.M1.strat S k x + 1 := by
  refine AdalyFormal.M1.strat_close hS (le_trans h ?_)
  unfold bigSide
  have : 1 ≤ ell ^ (AdalyFormal.M1.strat S k x + 1) := Nat.one_le_pow _ _ (by omega)
  have : 2 ≤ ell ^ (AdalyFormal.M1.strat S k x + 1) := by
    calc 2 ≤ ell := hell
      _ = ell ^ 1 := (pow_one ell).symm
      _ ≤ ell ^ (AdalyFormal.M1.strat S k x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc 2 ≤ ell ^ (AdalyFormal.M1.strat S k x + 1) := this
    _ ≤ R * (M * ell ^ (AdalyFormal.M1.strat S k x + 1)) := by
        have h1 : ell ^ (AdalyFormal.M1.strat S k x + 1) ≤ M * ell ^ (AdalyFormal.M1.strat S k x + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))

theorem pdist_corner1 (x : PeriodicLatticeSite Lf) (μ : Fin 3) : pdist x (periodicLatticeShift x μ) ≤ 2 :=
  le_trans (AdalyFormal.StatementLaneR8.pdist_shift_le x μ) (by norm_num)

theorem pdist_corner2 (x : PeriodicLatticeSite Lf) (μ ν : Fin 3) :
    pdist x (periodicLatticeShift (periodicLatticeShift x μ) ν) ≤ 2 := by
  have h1 := AdalyFormal.StatementLaneR8.pdist_shift_le x μ
  have h2 := AdalyFormal.StatementLaneR8.pdist_shift_le (periodicLatticeShift x μ) ν
  have h3 := AdalyFormal.StatementLaneR8.pdist_triangle x (periodicLatticeShift x μ) (periodicLatticeShift (periodicLatticeShift x μ) ν)
  omega

/-- on `plaqIn Ω₀` the regime gives `dv ≤ ρ ℓ² / ℓ^{2 strat p₀}`. -/
theorem hol_strat (U : Cfg Lf) (ρ : ℝ) (hρ : 0 ≤ ρ) (hreg : HolRegime S ell k U ρ) (p : PeriodicLatticePlaquette Lf)
    (hp : p ∈ plaqIn (S.Om 0)) :
    AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p)
      ≤ ρ * (ell : ℝ) ^ 2 / ((ell : ℝ) ^ AdalyFormal.M1.strat S k p.1) ^ 2 := by
  classical
  set x := p.1
  set μ := p.2.1.1
  set ν := p.2.1.2
  have hm : ∀ e ∈ periodicPlaquetteBoundaryEdges p, e.1 ∈ S.Om 0 ∧ periodicLatticeShift e.1 e.2 ∈ S.Om 0 := hp
  have hxμ := hm (x, μ) (by simp [periodicPlaquetteBoundaryEdges, x, μ])
  have hxν := hm (x, ν) (by simp [periodicPlaquetteBoundaryEdges, x, ν])
  have hμν := hm (periodicLatticeShift x μ, ν) (by simp [periodicPlaquetteBoundaryEdges, x, μ, ν])
  set s := AdalyFormal.M1.strat S k x
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  -- all corners have stratum ≥ s − 1
  have hcorner : ∀ z, z ∈ S.Om 0 → pdist z x ≤ 2 → s - 1 ≤ AdalyFormal.M1.strat S k z := by
    intro z _ hz
    have := strat_near hS hell hR1 hM1 hz
    omega
  set j0 := s - 1
  have hj0k : j0 ≤ k := le_trans (Nat.sub_le _ _) (AdalyFormal.M1.strat_le S k x)
  have hin : ∀ z, z ∈ S.Om 0 → pdist z x ≤ 2 → z ∈ S.Om j0 := fun z hz h =>
    AdalyFormal.M1.mem_of_le_strat hS hz (hcorner z hz h)
  have h1 := hreg j0 hj0k p (hin x hxμ.1 (by rw [AdalyFormal.StatementLaneR8.pdist_self]; omega))
    (hin _ hxμ.2 (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact pdist_corner1 hS hell hR1 hM1 x μ))
    (hin _ hxν.2 (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact pdist_corner1 hS hell hR1 hM1 x ν))
    (hin _ hμν.2 (by rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact pdist_corner2 hS hell hR1 hM1 x μ ν))
  refine h1.trans ?_
  have hpos : (0 : ℝ) < (ell : ℝ) ^ (2 * j0) := by positivity
  have hpos2 : (0 : ℝ) < ((ell : ℝ) ^ s) ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos hpos2]
  have hpow : ((ell : ℝ) ^ s) ^ 2 ≤ (ell : ℝ) ^ 2 * (ell : ℝ) ^ (2 * j0) := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hellr (by omega)
  nlinarith

end strat

end AdalyFormal.M1IMS

#print axioms AdalyFormal.M1IMS.dpFirst_le_p
#print axioms AdalyFormal.M1IMS.dpSecond_le_p
#print axioms AdalyFormal.M1IMS.bilPlaq_quad_le_p
#print axioms AdalyFormal.M1IMS.bilPlaq_dv
#print axioms AdalyFormal.M1IMS.strat_near
#print axioms AdalyFormal.M1IMS.pdist_corner1
#print axioms AdalyFormal.M1IMS.pdist_corner2
#print axioms AdalyFormal.M1IMS.hol_strat
#print axioms AdalyFormal.M1IMS.HolRegime

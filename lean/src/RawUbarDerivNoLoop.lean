/-
Owned SI1 noloop scratch file (compute/m1_si1_noloop/phi/). Imports the frozen `AdalyFormal`
package read-only, plus READ-ONLY hash-verified copies of `RawAverageDeriv.lean`,
`IngredientDeriv.lean`, `ModifiedAverageDeriv.lean` (from `compute/m1_si1_long`, reused a second
time via `compute/m1_si1_phi2/phi/deps/`'s own already hash-checked copies — hashes re-verified
identical, `518a0c11…`, `767f9f97…`, `930e4938…`) and `NonzeroExpDeriv.lean` (from
`compute/m1_si1_phi2/exp/`, hash `e950ff15…`). None of these four files is edited.

## TARGET AND THE ACTUAL SOURCE MISMATCH THIS FILE FIXES

`compute/m1_si1_phi2/phi/RawUbarDeriv.lean` supplied `hasDerivAt_ubarSU2_coe_configMul`, but its
per-point hypotheses `hnc1 : loopVar 1 ell V0 c x ≠ 1` / `hnc2 : loopVar 1 ell V0 c x ≠ su2NegOne`
over EVERY nonanchor block point are source-false: `compute/m1_si1_phi2/audit/RESULT.md` found a
concrete (period-4, block-2) fitted example where a NONANCHOR loop is identically `1` for every
background, making `hnc1` unsatisfiable there. The launch instructions for THIS stage are explicit:
identity loops are allowed; only the `-I` principal-log-chart cut may be excluded. This file drops
`hnc1` entirely and rebuilds the derivative from a single hypothesis per point,
`loopVar 1 ell V0 c x ≠ su2NegOne`.

**The one genuinely new piece** (§4 below, `hasDerivAt_su2Log_su2_curve_at_one`): `su2Log`
differentiates along ANY curve that passes THROUGH THE IDENTITY at the base point — not merely
along curves of the specific `t ↦ su2Exp(t•H)` shape `IngredientDeriv.hasDerivAt_su2Log_su2Exp_smul`
already covers. `su2Log`'s own `κ(g) = θ(g)/sin θ(g)` closed form has a genuine `0/0` (Lean
convention: literally `0`, not the true limit `1`) exactly at `g = 1`, so composing it naively with
an arbitrary curve does not differentiate directly from the closed form. The fix routes around the
closed form entirely: `NormedSpace.exp : M2 → M2` has strict Fréchet derivative `= 1` (the identity
CLM) at `0` UNCONDITIONALLY in any Banach algebra (`hasStrictFDerivAt_exp_zero`, already reused
elsewhere in this tree for the SAME fact at a different basepoint); the inverse-function theorem
then gives a genuine smooth LOCAL INVERSE `g₀` of `exp` near `(0,1)`, with `HasFDerivAt g₀ 1 1`. By
injectivity of `exp` on the IFT's source neighbourhood, `g₀` and `su2Log` AGREE on every point close
enough to `1` (both are exact one-sided inverses of `exp` there — `su2Log` via
`RegularityGap.su2_exp_log_of_ne_negOne`, already compiled, needing only `g ≠ -I`), so `su2Log`
inherits `g₀`'s derivative along any curve landing close enough to `1`. "Close enough" is supplied
by an entirely algebraic (arccos-free) continuity argument: `su2Log g = κ(g) • Yof g`
(`RegularityGap.su2Log_eq_kappa_smul`, already compiled) with `Yof g = (g:M2) −
(cos θ(g):ℂ)•1 = (g:M2) − ((trace(g:M2)).re/2:ℂ)•1` (`BlockingLinkEstimate.cos_su2Angle` eliminates
the `arccos` entirely from `Yof`'s formula, leaving a manifestly continuous — indeed polynomial —
function of `g:M2`) and `0 ≤ κ(g) ≤ π/2` once `θ(g) ≤ π/2` (`Bch2.kappa_nonneg`/`kappa_le`, and
`θ(g) ≤ π/2 ↔ 0 ≤ (trace(g:M2)).re` unfolds `su2Angle` directly via `Real.arccos_le_pi_div_two`, no
extra machinery). No new axiom, no new `NormedSpace`/norm instance on `M2` is introduced anywhere in
this argument (deliberately — `BlockingLinkEstimate.lean`'s own §1 docstring flags introducing a
SECOND norm instance on `M2` as a known instance-diamond hazard in this tree; every inequality here
stays inside the ALREADY-ACTIVE ambient `Matrix.linftyOpNormedRing`/`linftyOpNormedAlgebra` local
instances via ordinary `‖r • X‖ = |r| * ‖X‖` and continuity of algebraic operations, never via
`frobNorm`/`nu`, which this tree keeps deliberately uninstantiated as a norm).
-/
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.SuTwoLogExpTorus
import AdalyFormal.Balaban.UbarTowerCovariance
import AdalyFormal.Balaban.TowerLawCovariant
import AdalyFormal.Balaban.QjComposite
import AdalyFormal.Balaban.RegularityGap
import AdalyFormal.Balaban.BlockingLinkEstimate
import AdalyFormal.Balaban.Bch2
import RawAverageDeriv
import NonzeroExpDeriv

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1.RawUbarDerivNoLoop

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2LogExp su2NegOne su2Exp_zero
  su2Log_one su2LogExp_log su2LogExp_exp coe_mul coe_inv coe_one su2Angle su2Kappa)
open AdalyFormal.Balaban.SuTwoLogExp (su2Log_traceless su2Log_antiHermitian
  su2Exp_coe_of_antiHerm_traceless)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_apply)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar gammaVarStrided loopVar cPlusS
  stridedBlockedGauge)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarseGammaPath_self)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf)
open AdalySI1.IngredientDeriv (dirDeriv)
open AdalySI1.ModifiedAverageDeriv (configMul)
open AdalySI1.RawAverageDeriv (holonomyDirDeriv hasDerivAt_coarsePathHolonomy_configMul_aux
  hasDerivAt_coarseBondVar_configMul hasDerivAt_conjTranspose_curve hasDerivAt_su2Log_su2_curve
  traceArg_ne_center conjTransposeLM conjTransposeLM_apply)
open AdalyFormal.Balaban.RegularityGap (Yof su2_exp_log_of_ne_negOne su2Log_eq_kappa_smul
  real_smul_eq)
open AdalyFormal.Balaban.BlockingLinkEstimate (cos_su2Angle)
open AdalyFormal.Balaban.Bch2 (kappa_nonneg kappa_le)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — two mechanical bridges (verbatim reuse of `m1_si1_phi2/phi/RawUbarDeriv.lean`'s §0). -/

theorem configMul_zero_eq (V0 : PeriodicLinkConfiguration SU2 L) (A : PeriodicLatticeEdge L → M2) :
    configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0 = V0 := by
  funext e
  show su2Exp ((0 : ℝ) • A e) * V0 e = V0 e
  rw [zero_smul, su2Exp_zero, one_mul]

theorem qsmul_eq_rsmul (ell : ℕ) (X : M2) :
    ((ell : ℚ) ^ 3)⁻¹ • X = ((ell : ℝ) ^ 3)⁻¹ • X := by
  rw [← Rat.cast_smul_eq_qsmul ℝ (((ell : ℚ) ^ 3)⁻¹) X]
  congr 1
  push_cast
  ring

/-! ## §1 — `coarsePathHolonomy` derivative at any base site/path (verbatim reuse of §1). -/

theorem hasDerivAt_coarsePathHolonomy_configMul (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    HasDerivAt
      (fun t : ℝ => ((coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y p : SU2)
        : M2))
      (holonomyDirDeriv V0 A ell y p) 0 := by
  have h := hasDerivAt_coarsePathHolonomy_configMul_aux V0 A hah htr ell p y
    (fun _ : ℝ => (1 : SU2)) 0 (hasDerivAt_const (0 : ℝ) (((1 : SU2) : M2)))
  simp only [Submonoid.coe_one, one_mul, zero_mul, zero_add] at h
  exact h

theorem hasDerivAt_coarsePathHolonomy_configMul_inv (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (y : PeriodicLatticeSite L)
    (p : List (Fin 3)) :
    HasDerivAt
      (fun t : ℝ =>
        (((coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y p : SU2)⁻¹ : SU2)
          : M2))
      (holonomyDirDeriv V0 A ell y p)ᴴ 0 := by
  have h := hasDerivAt_coarsePathHolonomy_configMul V0 A hah htr ell y p
  have h2 := hasDerivAt_conjTranspose_curve (0 : ℝ) h
  have hfun : ∀ t : ℝ,
      (((coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y p : SU2)⁻¹ : SU2)
        : M2)
        = (((coarsePathHolonomy ell (configMul (fun e => su2Exp (t • A e)) V0) y p : SU2) : M2))ᴴ :=
    fun t => coe_inv _
  simpa only [hfun] using h2

/-! ## §2 — value facts at `t = 0` (verbatim reuse of §2). -/

theorem coarsePathHolonomy_configMul_zero (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (ell : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    coarsePathHolonomy ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) y p
      = coarsePathHolonomy ell V0 y p := by
  rw [configMul_zero_eq]

theorem loopVar_configMul_zero (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    loopVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c x = loopVar 1 ell V0 c x := by
  rw [configMul_zero_eq]

/-! ## §3 — `loopVar`'s own derivative (verbatim reuse of §3). -/

theorem hasDerivAt_gammaVarStrided_configMul (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    HasDerivAt
      (fun t : ℝ => ((gammaVarStrided 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2)
        : M2))
      (((holonomyDirDeriv V0 A 1 c.1 (coarseGammaPath 1 c.1 x)
            * ((coarsePathHolonomy 1 V0 x (List.replicate ell c.2) : SU2) : M2))
          + (((coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x) : SU2) : M2))
            * holonomyDirDeriv V0 A 1 x (List.replicate ell c.2))
          * (((coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x) : SU2) : M2))ᴴ
        + ((((coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x) : SU2) : M2))
            * (((coarsePathHolonomy 1 V0 x (List.replicate ell c.2) : SU2) : M2)))
          * (holonomyDirDeriv V0 A 1 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))ᴴ) 0 := by
  have h1 := hasDerivAt_coarsePathHolonomy_configMul V0 A hah htr 1 c.1 (coarseGammaPath 1 c.1 x)
  have h2 := hasDerivAt_coarsePathHolonomy_configMul V0 A hah htr 1 x (List.replicate ell c.2)
  have h3inv := hasDerivAt_coarsePathHolonomy_configMul_inv V0 A hah htr 1
    (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x)
  have h12 := h1.mul h2
  have h123 := h12.mul h3inv
  have heval1 : (fun t : ℝ =>
      ((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) c.1
          (coarseGammaPath 1 c.1 x) : SU2) : M2)) 0
      = ((coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x) : SU2) : M2) := by
    show ((coarsePathHolonomy 1 (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) c.1
        (coarseGammaPath 1 c.1 x) : SU2) : M2) = _
    rw [coarsePathHolonomy_configMul_zero]
  have heval2 : (fun t : ℝ =>
      ((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) x
          (List.replicate ell c.2) : SU2) : M2)) 0
      = ((coarsePathHolonomy 1 V0 x (List.replicate ell c.2) : SU2) : M2) := by
    show ((coarsePathHolonomy 1 (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) x
        (List.replicate ell c.2) : SU2) : M2) = _
    rw [coarsePathHolonomy_configMul_zero]
  have heval3 : (fun t : ℝ =>
      (((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) (cPlusS 1 ell c)
          (coarseGammaPath 1 c.1 x) : SU2)⁻¹ : SU2) : M2)) 0
      = (((coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x) : SU2) : M2))ᴴ := by
    show (((coarsePathHolonomy 1 (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) (cPlusS 1 ell c)
        (coarseGammaPath 1 c.1 x) : SU2)⁻¹ : SU2) : M2) = _
    rw [coarsePathHolonomy_configMul_zero, coe_inv]
  simp only [Pi.mul_apply, heval1, heval2, heval3] at h123
  have hfun : ∀ t : ℝ,
      ((gammaVarStrided 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)
        = (((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) c.1
              (coarseGammaPath 1 c.1 x) : SU2) : M2)
            * ((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) x
              (List.replicate ell c.2) : SU2) : M2))
          * (((coarsePathHolonomy 1 (configMul (fun e => su2Exp (t • A e)) V0) (cPlusS 1 ell c)
              (coarseGammaPath 1 c.1 x) : SU2)⁻¹ : SU2) : M2) := by
    intro t
    show ((_ * _ * _⁻¹ : SU2) : M2) = _
    rw [coe_mul, coe_mul]
  exact h123.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

theorem hasDerivAt_loopVar_configMul (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) :
    HasDerivAt
      (fun t : ℝ => ((loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2))
      ((((holonomyDirDeriv V0 A 1 c.1 (coarseGammaPath 1 c.1 x)
              * ((coarsePathHolonomy 1 V0 x (List.replicate ell c.2) : SU2) : M2))
            + (((coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x) : SU2) : M2))
              * holonomyDirDeriv V0 A 1 x (List.replicate ell c.2))
            * (((coarsePathHolonomy 1 V0 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x) : SU2) : M2))ᴴ
          + ((((coarsePathHolonomy 1 V0 c.1 (coarseGammaPath 1 c.1 x) : SU2) : M2))
              * (((coarsePathHolonomy 1 V0 x (List.replicate ell c.2) : SU2) : M2)))
            * (holonomyDirDeriv V0 A 1 (cPlusS 1 ell c) (coarseGammaPath 1 c.1 x))ᴴ)
          * (((coarseBondVar 1 ell V0 c : SU2) : M2))ᴴ
        + ((gammaVarStrided 1 ell V0 c x : SU2) : M2)
          * (holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))ᴴ) 0 := by
  have hg := hasDerivAt_gammaVarStrided_configMul V0 A hah htr ell c x
  have hb := hasDerivAt_coarseBondVar_configMul V0 A hah htr 1 ell c
  have hbinv := hasDerivAt_conjTranspose_curve (0 : ℝ) hb
  have hbinvfun : ∀ t : ℝ,
      (((coarseBondVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2)⁻¹ : SU2) : M2)
        = (((coarseBondVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2))ᴴ :=
    fun t => coe_inv _
  have hbinv' : HasDerivAt (fun t : ℝ =>
      (((coarseBondVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2)⁻¹ : SU2) : M2))
      (holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))ᴴ 0 :=
    hbinv.congr_of_eventuallyEq (Filter.Eventually.of_forall hbinvfun)
  have hgb := hg.mul hbinv'
  have hgeval : ((gammaVarStrided 1 ell (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) c x : SU2)
      : M2) = ((gammaVarStrided 1 ell V0 c x : SU2) : M2) := by
    rw [configMul_zero_eq]
  have hbeval : (((coarseBondVar 1 ell (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) c : SU2)⁻¹
      : SU2) : M2) = (((coarseBondVar 1 ell V0 c : SU2) : M2))ᴴ := by
    rw [configMul_zero_eq, coe_inv]
  simp only [hgeval, hbeval] at hgb
  have hfun : ∀ t : ℝ,
      ((loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)
        = ((gammaVarStrided 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x : SU2) : M2)
          * (((coarseBondVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2)⁻¹ : SU2)
            : M2) := by
    intro t
    show ((_ * _⁻¹ : SU2) : M2) = _
    rw [coe_mul]
  exact hgb.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

/-! ## §4 — NEW: `su2Log` differentiates through curves landing exactly AT the identity.

Only `g ≠ su2NegOne` is excluded anywhere below — matching the launch instructions exactly:
identity loops are allowed, only the `-I` principal-log chart cut is not. -/

theorem cos_su2Angle_eq_trace_div (g : SU2) :
    Real.cos (su2Angle g) = (Matrix.trace (g : M2)).re / 2 := cos_su2Angle g

theorem Yof_eq_ambient (g : SU2) :
    Yof g = (g : M2) - (((Matrix.trace (g : M2)).re / 2 : ℝ) : ℂ) • (1 : M2) := by
  unfold Yof
  rw [cos_su2Angle_eq_trace_div]

theorem continuous_yofAmbient : Continuous (fun Z : M2 => Z - (((Matrix.trace Z).re / 2 : ℝ) : ℂ) • (1 : M2)) := by
  have hlin : Continuous (fun Z : M2 => Matrix.trace Z) :=
    (Matrix.traceLinearMap (Fin 2) ℂ ℂ).continuous_of_finiteDimensional
  fun_prop

theorem su2Log_eq_kappa_rsmul (g : SU2) : su2Log g = (su2Kappa g : ℝ) • Yof g := by
  rw [su2Log_eq_kappa_smul, real_smul_eq]

theorem su2Angle_le_pi_div_two_iff (g : SU2) :
    su2Angle g ≤ Real.pi / 2 ↔ 0 ≤ (Matrix.trace (g : M2)).re := by
  unfold su2Angle
  rw [Real.arccos_le_pi_div_two]
  constructor
  · intro h; linarith
  · intro h; linarith

theorem hasDerivAt_su2Log_su2_curve_at_one {V : ℝ → SU2} {G' : M2} (t0 : ℝ)
    (hG : HasDerivAt (fun t => ((V t : SU2) : M2)) G' t0) (hval : V t0 = 1) :
    HasDerivAt (fun t => su2Log (V t)) G' t0 := by
  -- Step 1: `exp` has strict Fréchet derivative `= identity` at `0` in `M2`.
  have hstrict : HasStrictFDerivAt (NormedSpace.exp : M2 → M2)
      ((ContinuousLinearEquiv.refl ℝ M2 : M2 →L[ℝ] M2)) (0 : M2) := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero
  set Φ := hstrict.toOpenPartialHomeomorph NormedSpace.exp with hΦdef
  set g0 := hstrict.localInverse NormedSpace.exp (ContinuousLinearEquiv.refl ℝ M2) (0 : M2)
    with hg0def
  have hg0strict : HasStrictFDerivAt g0
      (((ContinuousLinearEquiv.refl ℝ M2).symm : M2 →L[ℝ] M2)) (NormedSpace.exp (0 : M2)) :=
    hstrict.to_localInverse
  rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl, NormedSpace.exp_zero]
    at hg0strict
  have hg0fd : HasFDerivAt g0 (1 : M2 →L[ℝ] M2) (1 : M2) := hg0strict.hasFDerivAt
  have hsrc_nhds : Φ.source ∈ nhds (0 : M2) :=
    Φ.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have htgt_nhds : Φ.target ∈ nhds (1 : M2) := by
    have h1 : NormedSpace.exp (0 : M2) = (1 : M2) := NormedSpace.exp_zero
    rw [← h1]
    exact Φ.open_target.mem_nhds hstrict.image_mem_toOpenPartialHomeomorph_target
  -- Step 2: `(V t : M2) → 1` and `trace (V t : M2).re → 2` at `t0`.
  have hVtend := hG.continuousAt.tendsto
  simp only [hval, coe_one] at hVtend
  have htrace_tend :
      Filter.Tendsto (fun t => (Matrix.trace ((V t : SU2) : M2)).re) (nhds t0) (nhds 2) := by
    have hcont : Continuous (fun Z : M2 => (Matrix.trace Z).re) := by
      have hlin : Continuous (fun Z : M2 => Matrix.trace Z) :=
        (Matrix.traceLinearMap (Fin 2) ℂ ℂ).continuous_of_finiteDimensional
      fun_prop
    have h := hcont.continuousAt (x := (1 : M2))
    have h2 := h.tendsto.comp hVtend
    have h3 : (Matrix.trace (1 : M2)).re = 2 := by
      simp [Matrix.trace_fin_two]
    rwa [h3] at h2
  -- Step 3: `su2Angle (V t) ≤ π/2` eventually, hence `su2Kappa (V t) ∈ [0, π/2]` eventually,
  -- and `Yof (V t) → 0` (all inside the ambient `M2` norm, no second instance introduced).
  have hangle_le : ∀ᶠ t in nhds t0, su2Angle (V t) ≤ Real.pi / 2 := by
    have hpos : ∀ᶠ t in nhds t0, (0 : ℝ) < (Matrix.trace ((V t : SU2) : M2)).re :=
      htrace_tend.eventually (eventually_gt_nhds (by norm_num))
    filter_upwards [hpos] with t ht
    exact (su2Angle_le_pi_div_two_iff (V t)).2 (le_of_lt ht)
  have hYof_tend : Filter.Tendsto (fun t => Yof (V t)) (nhds t0) (nhds (0 : M2)) := by
    have heq : (fun t => Yof (V t))
        = (fun Z : M2 => Z - (((Matrix.trace Z).re / 2 : ℝ) : ℂ) • (1 : M2)) ∘
          (fun t => ((V t : SU2) : M2)) := by
      funext t; simp only [Function.comp_apply]; exact Yof_eq_ambient (V t)
    rw [heq]
    have h := continuous_yofAmbient.continuousAt (x := (1 : M2)) |>.tendsto
    have h3 : (1 : M2) - (((Matrix.trace (1 : M2)).re / 2 : ℝ) : ℂ) • (1 : M2) = (0 : M2) := by
      have h4 : (Matrix.trace (1 : M2)).re = 2 := by simp
      rw [h4]; norm_num
    rw [h3] at h
    exact h.comp hVtend
  have hsu2Log_tend : Filter.Tendsto (fun t => su2Log (V t)) (nhds t0) (nhds (0 : M2)) := by
    have hbound : ∀ᶠ t in nhds t0, ‖su2Log (V t)‖ ≤ (Real.pi / 2) * ‖Yof (V t)‖ := by
      filter_upwards [hangle_le] with t ht
      rw [su2Log_eq_kappa_rsmul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (kappa_nonneg (V t))]
      exact mul_le_mul_of_nonneg_right (kappa_le ht) (norm_nonneg _)
    have hRHS_tend : Filter.Tendsto (fun t => (Real.pi / 2) * ‖Yof (V t)‖) (nhds t0) (nhds 0) := by
      have h := (continuous_norm.continuousAt (x := (0 : M2))).tendsto.comp hYof_tend
      simp only [norm_zero] at h
      simpa using h.const_mul (Real.pi / 2)
    have hnorm_tend : Filter.Tendsto (fun t => ‖su2Log (V t)‖) (nhds t0) (nhds 0) := by
      have hnn : ∀ᶠ t in nhds t0, (0:ℝ) ≤ ‖su2Log (V t)‖ := Filter.Eventually.of_forall
        (fun t => norm_nonneg _)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS_tend hnn hbound
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm_tend
  -- Step 4: eventually, `su2Log (V t) ∈ Φ.source`, and there it agrees with `g0`.
  have hev_source : ∀ᶠ t in nhds t0, su2Log (V t) ∈ Φ.source :=
    hsu2Log_tend.eventually hsrc_nhds
  have hev_target : ∀ᶠ t in nhds t0, ((V t : SU2) : M2) ∈ Φ.target :=
    hVtend.eventually htgt_nhds
  have hev_ne : ∀ᶠ t in nhds t0, V t ≠ su2NegOne := by
    filter_upwards [hangle_le] with t ht heq
    have hangle_neg_one : su2Angle su2NegOne = Real.pi := by
      unfold su2Angle su2NegOne
      simp [Matrix.trace_fin_two]
    rw [heq, hangle_neg_one] at ht
    linarith [Real.pi_pos]
  have heq_ev : ∀ᶠ t in nhds t0, g0 ((V t : SU2) : M2) = su2Log (V t) := by
    filter_upwards [hev_source, hev_target, hev_ne] with t hsrc htgt hne
    have hexp1 : NormedSpace.exp (su2Log (V t)) = ((V t : SU2) : M2) := by
      have h := su2_exp_log_of_ne_negOne (V t) hne
      have h2 : ((su2Exp (su2Log (V t)) : SU2) : M2) = NormedSpace.exp (su2Log (V t)) :=
        su2Exp_coe_of_antiHerm_traceless (su2Log_antiHermitian (V t)) (su2Log_traceless (V t))
      rw [← h2, h]
    have hexp2 : NormedSpace.exp (g0 ((V t : SU2) : M2)) = ((V t : SU2) : M2) := by
      have h := hstrict.eventually_right_inverse
      have h' := h.self_of_nhds
      exact Φ.right_inv htgt
    have hg0_mem_src : g0 ((V t : SU2) : M2) ∈ Φ.source := Φ.map_target htgt
    exact Φ.injOn hg0_mem_src hsrc (hexp2.trans hexp1.symm)
  have h0_in : g0 ((V t0 : SU2) : M2) = su2Log (V t0) := by
    have h1 : ((V t0 : SU2) : M2) = (1 : M2) := by rw [hval]; exact coe_one
    rw [h1]
    have h2 : NormedSpace.exp (0 : M2) = (1 : M2) := NormedSpace.exp_zero
    have h3 := hstrict.localInverse_apply_image
    rw [h2] at h3
    rw [← hg0def] at h3
    rw [h3, hval, su2Log_one]
  -- Step 5: assemble via the chain rule and eventual equality.
  have hval' : ((V t0 : SU2) : M2) = (1 : M2) := by rw [hval]; exact coe_one
  have hg0fd' := hg0fd
  rw [← hval'] at hg0fd'
  have hcomp := hg0fd'.comp_hasDerivAt t0 hG
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [heq_ev] with t ht using ht.symm

/-! ## §5 — the algebra-average bracket: value identity to `ubarSU2`, traceless/anti-Hermitian for
EVERY configuration, and its own `HasDerivAt`, over a SINGLE `≠ su2NegOne` hypothesis per point
(no `≠ 1` exclusion anywhere — identity loops, including but not limited to the block-anchor
`x = c.1`, are handled uniformly by §4 above). -/

noncomputable def ubarBracket (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) : M2 :=
  ∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (loopVar 1 ell V c x)

theorem ubarSU2_eq_exp_bracket_mul_bondVar (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) :
    ubarSU2 1 ell V c = su2Exp (ubarBracket V ell c) * coarseBondVar 1 ell V c := by
  rw [ubarSU2_apply]; rfl

theorem sum_qsmul_su2Log_conjTranspose (s : Finset (PeriodicLatticeSite L))
    (f : PeriodicLatticeSite L → SU2) (w : ℚ) :
    (∑ x ∈ s, w • su2Log (f x))ᴴ = -(∑ x ∈ s, w • su2Log (f x)) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.conjTranspose_add, ih, neg_add]
    congr 1
    rw [Matrix.conjTranspose_smul, su2Log_antiHermitian, smul_neg, star_trivial]

theorem sum_qsmul_su2Log_trace (s : Finset (PeriodicLatticeSite L))
    (f : PeriodicLatticeSite L → SU2) (w : ℚ) :
    Matrix.trace (∑ x ∈ s, w • su2Log (f x)) = 0 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.trace_add, ih, add_zero, Matrix.trace_smul,
      su2Log_traceless, smul_zero]

theorem ubarBracket_conjTranspose (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) : (ubarBracket V ell c)ᴴ = -(ubarBracket V ell c) :=
  sum_qsmul_su2Log_conjTranspose _ _ _

theorem ubarBracket_trace (V : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) : Matrix.trace (ubarBracket V ell c) = 0 :=
  sum_qsmul_su2Log_trace _ _ _

theorem ubarBracket_configMul_zero (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (ell : ℕ) (c : PeriodicLatticeEdge L) :
    ubarBracket (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) ell c = ubarBracket V0 ell c := by
  unfold ubarBracket
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [loopVar_configMul_zero]

theorem hasDerivAt_su2Log_loopVar_point (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (x : PeriodicLatticeSite L) (hnc2 : loopVar 1 ell V0 c x ≠ su2NegOne) :
    HasDerivAt (fun t : ℝ =>
        su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x))
      (deriv (fun t : ℝ =>
        su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0) 0 := by
  by_cases h1 : loopVar 1 ell V0 c x = 1
  · have hL := hasDerivAt_loopVar_configMul V0 A hah htr ell c x
    have h0 : loopVar 1 ell (configMul (fun e => su2Exp ((0:ℝ) • A e)) V0) c x = 1 := by
      rw [loopVar_configMul_zero]; exact h1
    have hres := hasDerivAt_su2Log_su2_curve_at_one (V :=
      fun t => loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x) (0 : ℝ) hL h0
    exact hres.deriv.symm ▸ hres
  · have hx := hasDerivAt_su2Log_su2_curve (g0 := loopVar 1 ell V0 c x) (0 : ℝ)
      (hasDerivAt_loopVar_configMul V0 A hah htr ell c x) h1 hnc2
      (loopVar_configMul_zero V0 A ell c x)
    exact hx.deriv.symm ▸ hx

theorem hasDerivAt_ubarBracket_configMul (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) :
    HasDerivAt (fun t : ℝ => ubarBracket (configMul (fun e => su2Exp (t • A e)) V0) ell c)
      (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
        deriv (fun t : ℝ =>
          su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0) 0 := by
  have heq : (fun t : ℝ => ubarBracket (configMul (fun e => su2Exp (t • A e)) V0) ell c)
      = (fun t : ℝ => ∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
          su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) := by
    funext t
    unfold ubarBracket
    exact Finset.sum_congr rfl (fun x _ => qsmul_eq_rsmul ell _)
  rw [heq]
  refine HasDerivAt.fun_sum (fun x hx => ?_)
  exact (hasDerivAt_su2Log_loopVar_point V0 A hah htr ell c x (hnc2 x hx)).const_smul
    (((ell : ℝ) ^ 3)⁻¹)

/-! ## §6 — the nonzero-basepoint `su2Exp` composition and the FINAL ASSEMBLY, over the single
`≠ su2NegOne` hypothesis (no `≠ 1` exclusion — the `hnc1` this stage's launch instructions ordered
dropped). -/

theorem hasDerivAt_su2Exp_coe_of_hasDerivAt {G : ℝ → M2} {D X : M2} (hG : HasDerivAt G D 0)
    (hG0 : G 0 = X) (hGah : ∀ t, (G t)ᴴ = -(G t)) (hGtr : ∀ t, Matrix.trace (G t) = 0) :
    HasDerivAt (fun t : ℝ => ((su2Exp (G t) : SU2) : M2)) ((fderiv ℝ NormedSpace.exp X) D) 0 := by
  have hanalytic : AnalyticAt ℝ NormedSpace.exp X :=
    NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) X
  have hfd := hanalytic.differentiableAt.hasFDerivAt
  have hraw := hfd.comp_hasDerivAt_of_eq 0 hG hG0.symm
  exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => su2Exp_coe_of_antiHerm_traceless (hGah t) (hGtr t)))

theorem hasDerivAt_ubarSU2_coe_configMul_noloop (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) :
    HasDerivAt
      (fun t : ℝ => ((ubarSU2 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2))
      ((fderiv ℝ NormedSpace.exp (ubarBracket V0 ell c))
            (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
              deriv (fun t : ℝ =>
                su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
          * ((coarseBondVar 1 ell V0 c : SU2) : M2)
        + ((su2Exp (ubarBracket V0 ell c) : SU2) : M2)
          * holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2)) 0 := by
  have hbrDeriv := hasDerivAt_ubarBracket_configMul V0 A hah htr ell c hnc2
  have hbr0 : ubarBracket (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) ell c
      = ubarBracket V0 ell c := ubarBracket_configMul_zero V0 A ell c
  have hexp := hasDerivAt_su2Exp_coe_of_hasDerivAt hbrDeriv hbr0
    (fun t => ubarBracket_conjTranspose (configMul (fun e => su2Exp (t • A e)) V0) ell c)
    (fun t => ubarBracket_trace (configMul (fun e => su2Exp (t • A e)) V0) ell c)
  have hbond := hasDerivAt_coarseBondVar_configMul V0 A hah htr 1 ell c
  have hprod := hexp.mul hbond
  have hexpeval : ((su2Exp (ubarBracket (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) ell c)
      : SU2) : M2) = ((su2Exp (ubarBracket V0 ell c) : SU2) : M2) := by
    rw [ubarBracket_configMul_zero]
  have hbondeval : ((coarseBondVar 1 ell (configMul (fun e => su2Exp ((0 : ℝ) • A e)) V0) c
      : SU2) : M2) = ((coarseBondVar 1 ell V0 c : SU2) : M2) := by
    rw [configMul_zero_eq]
  simp only [hexpeval, hbondeval] at hprod
  have hfun : ∀ t : ℝ,
      ((ubarSU2 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2)
        = ((su2Exp (ubarBracket (configMul (fun e => su2Exp (t • A e)) V0) ell c) : SU2) : M2)
          * ((coarseBondVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2) := by
    intro t
    rw [ubarSU2_eq_exp_bracket_mul_bondVar, coe_mul]
  exact hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)

#print axioms hasDerivAt_su2Log_su2_curve_at_one
#print axioms hasDerivAt_su2Log_loopVar_point
#print axioms hasDerivAt_ubarBracket_configMul
#print axioms hasDerivAt_su2Exp_coe_of_hasDerivAt
#print axioms hasDerivAt_ubarSU2_coe_configMul_noloop

end AdalySI1.RawUbarDerivNoLoop

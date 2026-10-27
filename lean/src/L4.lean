/-
Owned SI1 step1 L4 file (compute/m1_si1_step1/l4/). Imports the frozen `AdalyFormal` package
read-only, plus READ-ONLY hash-verified copies placed in `l4/deps/`: `T1MainSegment.lean`,
`GopTransport.lean`, `M2RouteAudit.lean`, `NonzeroExpDeriv.lean` (identical to
`compute/m1_si1_step1/deps/`'s own paid copies), `DexpRodriguesG.lean` (identical to the paid
`compute/m1_si1_step1/DexpRodriguesG.lean`, SHA-256 `120ab3a1…`), and `IngredientDeriv.lean` /
`ModifiedAverageDeriv.lean` / `RawAverageDeriv.lean` / `RawUbarDerivNoLoop.lean` (identical to
`compute/m1_si1_noloop/phi/{deps/,}`'s own paid copies). None of these files is edited.

TARGET (L4, `compute/m1_si1_astra_match/expand/CHANNEL_EXPANSION.md` §7 row L4): for an `SU(2)`
curve `W` whose matrix coercion has derivative `V` at `0` and `W 0 ≠ -I`, identify
`deriv (fun t => su2Log (W t)) 0` with `gInvOp (-adOp (principalSuTwoLog (W 0))) v`,
`v := V * (W 0)⁻¹ : SuTwo`.

STRATEGY (the genuinely new piece, not previously identified by `compute/m1_si1_l18/l4/RESULT.md`,
which searched for a coefficient-matching identity between `su2Log`'s `arccos`/`sin` closed form
and `gInvOp`'s torus/`diagonalizer` closed form and found neither route tractable): route around
BOTH closed forms entirely via the chain rule and the ALREADY-PAID exponential differential
`AdalySI1.DexpRodrigues.dexp_eq_gOp`. If `Z(t) := su2Log (W t)` has ANY derivative `D` at `0`
(existence supplied by the ALREADY-PAID `hasDerivAt_su2Log_su2_curve`/`_at_one`, closed form not
used), then differentiating the identity `su2Exp (Z t) = W t` (valid on a neighbourhood of `0` by
continuity, since `W 0 ≠ su2NegOne` is an open condition) via the chain rule and matching against
the given `V` pins `D` down through `dexp_eq_gOp` applied at `Z 0`, up to inverting the operator
`gOp (-adOp (Z 0))`. Both remaining hypotheses below (`hD`'s existence and `hunit`) are each
independently already paid ELSEWHERE in the campaign (`hasDerivAt_su2Log_su2_curve`/`_at_one` here;
`gOp_ad_isUnit` in `compute/deltak_r82/PrincipalRadial.lean`, whose OWN transitive import closure
was measured here at 72 files / 13,310 lines spanning the entire `deltak_r53`–`deltak_r82` ladder,
far larger than `compute/m1_si1_l18/l4/RESULT.md`'s "would be a legitimate read-only import"
estimate) — they are stated as explicit hypotheses here rather than re-derived, exactly as
`compute/deltak_r66/StructuralBlockOne.lean::gInvOp_neg_mul_expOp_eq_gInvOp` already does for a
sibling fact in this same campaign.
-/
import DexpRodriguesG
import RawUbarDerivNoLoop

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace AdalySI1.L4

open Matrix
attribute [local instance 2000] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne su2Log_one
  su2Log_antiHermitian su2Log_traceless su2Exp_coe_of_antiHerm_traceless coe_inv coe_one)
open AdalyFormal.Balaban.RegularityGap (su2_exp_log_of_ne_negOne)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open OneStep124 (adOp gOp gInvOp)
open AdalyFormal.DeltaKR66 (principalSuTwoLog)
open AdalySI1.DexpRodrigues (dexp_eq_gOp)
open AdalySI1.RawUbarDerivNoLoop (hasDerivAt_su2Log_su2_curve_at_one)
open AdalySI1.RawAverageDeriv (hasDerivAt_su2Log_su2_curve hasDerivAt_conjTranspose_curve)

/-! ## §0 — `trace` differentiates unconditionally (mirrors `RawAverageDeriv.conjTransposeCLM`). -/

def traceLM : M2 →ₗ[ℝ] ℂ where
  toFun M := Matrix.trace M
  map_add' := Matrix.trace_add
  map_smul' r M := by simp [Matrix.trace_smul]

noncomputable def traceCLM : M2 →L[ℝ] ℂ := traceLM.toContinuousLinearMap

theorem traceCLM_apply (M : M2) : traceCLM M = Matrix.trace M := rfl

theorem hasDerivAt_trace_curve {G : ℝ → M2} {G' : M2} (t0 : ℝ) (hG : HasDerivAt G G' t0) :
    HasDerivAt (fun t => Matrix.trace (G t)) (Matrix.trace G') t0 :=
  traceCLM.hasFDerivAt.comp_hasDerivAt t0 hG

/-! ## §1 — the general L4 equality, parametrized by exactly two named residual facts:
existence of `su2Log`'s derivative along the curve (`hD`), and invertibility of the relevant
`gOp` (`hunit`). Both are independently already paid elsewhere in this campaign; see the file
docstring. -/

theorem su2Log_deriv_eq_gInvOp {W : ℝ → SU2} {V D : M2}
    (hW : HasDerivAt (fun t => ((W t : SU2) : M2)) V 0)
    (hne : W 0 ≠ su2NegOne)
    (hD : HasDerivAt (fun t => su2Log (W t)) D 0)
    (v : SuTwo) (hv : (v : M2) = V * Ring.inverse ((W 0 : SU2) : M2))
    (hunit : IsUnit (gOp (-(adOp (principalSuTwoLog (W 0)))))) :
    D = ((gInvOp (-(adOp (principalSuTwoLog (W 0)))) v : SuTwo) : M2) := by
  set Z0 : SuTwo := principalSuTwoLog (W 0) with hZ0def
  have hZ0M2 : (Z0 : M2) = su2Log (W 0) := rfl
  -- `D` lies in `su(2)`: differentiate the identically-true membership of `su2Log (W t)`.
  have hDah : Dᴴ = -D := by
    have hcurve : ∀ t : ℝ, (su2Log (W t))ᴴ = -(su2Log (W t)) := fun t => su2Log_antiHermitian (W t)
    have h1 := hasDerivAt_conjTranspose_curve (0 : ℝ) hD
    have h2 : HasDerivAt (fun t => -(su2Log (W t))) (-D) 0 := hD.neg
    have h3 : HasDerivAt (fun t => (su2Log (W t))ᴴ) (-D) 0 :=
      h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hcurve)
    exact h1.unique h3
  have hDtr : Matrix.trace D = 0 := by
    have hcurve : ∀ t : ℝ, Matrix.trace (su2Log (W t)) = 0 := fun t => su2Log_traceless (W t)
    have h1 := hasDerivAt_trace_curve (0 : ℝ) hD
    have h2 : HasDerivAt (fun t => Matrix.trace (su2Log (W t))) (0 : ℂ) 0 :=
      (hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq (Filter.Eventually.of_forall hcurve)
    exact h1.unique h2
  set Dsu : SuTwo := ⟨D, hDah, hDtr⟩ with hDsudef
  have hDsuM2 : (Dsu : M2) = D := rfl
  -- `exp (su2Log (W 0)) = W 0`, transported to the ambient `M2` exponential.
  have hexp0 : su2Exp (su2Log (W 0)) = W 0 := su2_exp_log_of_ne_negOne (W 0) hne
  have hexpM2 : NormedSpace.exp (Z0 : M2) = ((W 0 : SU2) : M2) := by
    rw [hZ0M2]
    have h2 : ((su2Exp (su2Log (W 0)) : SU2) : M2) = NormedSpace.exp (su2Log (W 0)) :=
      su2Exp_coe_of_antiHerm_traceless (su2Log_antiHermitian (W 0)) (su2Log_traceless (W 0))
    rw [← h2, hexp0]
  -- `exp` is analytic (hence differentiable) at every point of `M2`, in particular at `Z0`.
  have hanalytic : AnalyticAt ℝ (NormedSpace.exp : M2 → M2) (Z0 : M2) :=
    NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := M2) (Z0 : M2)
  have hfd : HasFDerivAt (NormedSpace.exp : M2 → M2)
      (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z0 : M2)) (Z0 : M2) :=
    hanalytic.differentiableAt.hasFDerivAt
  -- Chain rule: `t ↦ exp (su2Log (W t))` has derivative `(fderiv exp Z0) D` at `0`.
  have hcompRaw : HasDerivAt (fun t => NormedSpace.exp (su2Log (W t)))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z0 : M2)) D) 0 := by
    have hbase : (fun t => su2Log (W t)) 0 = (Z0 : M2) := hZ0M2.symm
    have := hfd.comp_hasDerivAt_of_eq (0 : ℝ) hD hbase
    exact this
  -- Eventually near `0`, `W t ≠ su2NegOne` (continuity, open condition), hence
  -- `exp (su2Log (W t)) = (W t : M2)` there too.
  have hcontM2 : ContinuousAt (fun t => ((W t : SU2) : M2)) 0 := hW.continuousAt
  have hne0M2 : ((W 0 : SU2) : M2) ≠ ((su2NegOne : SU2) : M2) := by
    intro h; exact hne (Subtype.ext h)
  have hev_ne : ∀ᶠ t in nhds (0 : ℝ), ((W t : SU2) : M2) ≠ ((su2NegOne : SU2) : M2) :=
    hcontM2.eventually_ne hne0M2
  have heq_ev : (fun t : ℝ => NormedSpace.exp (su2Log (W t))) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ => ((W t : SU2) : M2)) := by
    filter_upwards [hev_ne] with t ht
    have htne : W t ≠ su2NegOne := fun h => ht (by rw [h])
    have h1 := su2_exp_log_of_ne_negOne (W t) htne
    have h2 : ((su2Exp (su2Log (W t)) : SU2) : M2) = NormedSpace.exp (su2Log (W t)) :=
      su2Exp_coe_of_antiHerm_traceless (su2Log_antiHermitian (W t)) (su2Log_traceless (W t))
    show NormedSpace.exp (su2Log (W t)) = ((W t : SU2) : M2)
    rw [← h2, h1]
  have hcomp : HasDerivAt (fun t => ((W t : SU2) : M2))
      ((fderiv ℝ (NormedSpace.exp : M2 → M2) (Z0 : M2)) D) 0 :=
    hcompRaw.congr_of_eventuallyEq heq_ev.symm
  -- Uniqueness of derivatives: `V = (fderiv exp Z0) D`.
  have hVeq : V = (fderiv ℝ (NormedSpace.exp : M2 → M2) (Z0 : M2)) D := hW.unique hcomp
  -- `dexp_eq_gOp` at `Z0`, applied to `Dsu`.
  have hkey := dexp_eq_gOp Z0 Dsu
  rw [hDsuM2] at hkey
  -- `exp (-(Z0:M2)) = Ring.inverse ((W 0 : SU2):M2)`.
  have hexpneg : NormedSpace.exp (-(Z0 : M2)) = Ring.inverse ((W 0 : SU2) : M2) := by
    rw [← hexpM2]; exact (Ring.inverse_exp (Z0 : M2)).symm
  rw [hexpneg, ← hVeq] at hkey
  rw [← hv] at hkey
  -- `v = gOp (-(adOp Z0)) Dsu` as `SuTwo` elements, then invert with `hunit`.
  have hveq : v = gOp (-(adOp Z0)) Dsu := by
    apply Subtype.coe_injective
    exact hkey
  have hcancel : gInvOp (-(adOp Z0)) (gOp (-(adOp Z0)) Dsu) = Dsu := by
    have hone : gInvOp (-(adOp Z0)) * gOp (-(adOp Z0)) = 1 := Ring.inverse_mul_cancel _ hunit
    have := congrFun (congrArg (DFunLike.coe) hone) Dsu
    simpa using this
  rw [← hveq] at hcancel
  rw [← hDsuM2, hcancel]

#print axioms su2Log_deriv_eq_gInvOp

end AdalySI1.L4

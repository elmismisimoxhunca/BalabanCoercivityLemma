/-
Owned SI1 noloop file (compute/m1_si1_noloop/outer/). Imports the frozen `AdalyFormal` package
read-only, plus READ-ONLY hash-verified copies of `ModifiedAverageDeriv`/`RawAverageDeriv`/
`SI1AssembleDeriv` already sitting inside THIS workflow's own `compute/m1_si1_noloop/prod/deps/`
(hashes re-verified below against `compute/m1_si1_long/audit/CERTIFICATE_INVENTORY.md`'s live
hashes — `2f42a3c2…`/`767f9f97…`/`930e4938…` — matching exactly; nothing is re-copied since
`prod/deps/` already sits inside `compute/m1_si1_noloop`), and THIS SAME workflow's own
already-compiled `compute/m1_si1_noloop/prod/ProdFullAssembleDerivNoLoop.lean`
(`hasDerivAt_modifiedAverage_coe_configMul_noloop`, READY). None of these is edited.

## TARGET

Differentiate the OUTER source logarithm of the modified average, `su2Log ∘ modifiedAverage`, at
`t = 0`, with the physical output scale `h`/`Lh := ell*h`, over the identity-loops-allowed raw
ratio (single `hnc2 : ... ≠ su2NegOne` hypothesis, no `hnc1`, no `hell`) — this stage's launch
charge: "Outer su2Log of modifiedAverage at 0 with physical h, no assumed unpaid remainder, no
identity-loop ban."

**This file does NOT assume a quadratic remainder** (unlike the paid, still-open
`compute/m1_si1_long/outer/OuterLogDeriv.lean`, which is explicitly CONDITIONAL on an unsupplied
`hbound`). It supplies the derivative unconditionally via the ordinary INVERSE FUNCTION THEOREM,
reusing `compute/m1_si1_phi2/audit/SOURCE_AUDIT.md`'s own finding that this generic identity-log
step is sound in isolation ("The new outer identity-log proof itself demonstrates the appropriate
distinction [between the −I principal-log cut and the identity]") — §1–§5 below are that SAME
generic machinery, copied verbatim from the superseded `compute/m1_si1_phi2/outer/
OuterLogFullDeriv.lean` (its own §1–§5), since that machinery never depended on phi's noncentrality
hypotheses at all — it is about `su2Log`'s differentiability at `g = 1`, entirely independent of
`modifiedAverage`'s inner structure. `su2Log`'s own closed-form `(κ(g)/2)•(g−gᴴ)` has a genuine
CORNER at `g = 1` (`arccos` at the boundary of `[-1,1]`) so the naive product/quotient-rule route
used elsewhere in this tree for NONCENTRAL points does not reach `g = 1`; `su2Log` genuinely IS
differentiable there, as the local inverse of `NormedSpace.exp` (Mathlib's
`HasFDerivWithinAt.of_local_left_inverse` applied to the unconditional `hasFDerivAt_exp_zero`),
just not via that formula.

The ONLY thing this file changes vs. the superseded `m1_si1_phi2/outer/OuterLogFullDeriv.lean` is
§6/§7: the applied theorem now calls THIS workflow's own noloop product-rule theorem
(`AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop`, single `hnc2`, no
`hnc1`, no `hell`) instead of the superseded `AdalySI1Phi2.ProdAssemble.
hasDerivAt_modifiedAverage_coe_configMul` (which carried the illegal, source-false `hnc1`
nonanchor-loop-≠-1 exclusion that `compute/m1_si1_phi2/audit/RESULT.md` found refuted by a fitted
period-4 block-2 example — a nonanchor loop identically `1` for every background). This file makes
NO claim comparing the resulting derivative to `q124Principal` or any boxed SI1 equality — those
remain separate, later, unaffected stages (`compute/m1_si1_phi2/audit/SOURCE_AUDIT.md` §36/20: "The
physical theorem multiplies the actual directional derivative by h; merely defining `Lh` does not
establish its equality to the scaled q" — that further identification is explicitly out of this
stage's scope, unattempted here).
-/
import ModifiedAverageDeriv
import RawAverageDeriv
import SI1AssembleDeriv
import ProdFullAssembleDerivNoLoop

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1Noloop.OuterLogFullDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one su2Angle
  su2Kappa su2NegOne coe_one coe_su2NegOne su2NegOne_ne_one su2Exp_of_mem su2Exp_of_not_mem)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobNorm_su2Log_le)
open AdalyFormal.Balaban.RegularityGap (su2_exp_log_of_ne_negOne)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalySI1.ModifiedAverageDeriv (modifiedAverage modifiedAverage_trivialU)
open AdalySI1.RawAverageDeriv (reTraceCLM reTraceCLM_apply)
open AdalySI1.SI1AssembleDeriv (opNorm_le_two_mul_frobNorm)
open Filter Topology

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the zero-perturbation base case for the ACTUAL `su2Log ∘ modifiedAverage` composition
-/

theorem base_zero (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (A : PeriodicLatticeEdge L → M2) (c : PeriodicLatticeEdge L) :
    modifiedAverage V0 ell (fun e => su2Exp ((0 : ℝ) • A e)) c = 1 := by
  have hconst : (fun e => su2Exp ((0 : ℝ) • A e)) = trivialU L := by
    funext e
    show su2Exp ((0 : ℝ) • A e) = 1
    rw [zero_smul, su2Exp_zero]
  rw [hconst, modifiedAverage_trivialU]

/-! ## §2 — `su2Log`, extended to a total closed-form map on `M2`, agreeing with `su2Log` on the
image of `SU2` by unfolding definitions only (no new formula). -/

noncomputable def su2AngleM2 (Y : M2) : ℝ := Real.arccos ((Matrix.trace Y).re / 2)

noncomputable def su2KappaM2 (Y : M2) : ℝ := su2AngleM2 Y / Real.sin (su2AngleM2 Y)

noncomputable def su2LogM2 (Y : M2) : M2 := ((su2KappaM2 Y : ℂ) / 2) • (Y - Yᴴ)

theorem su2AngleM2_coe (g : SU2) : su2AngleM2 (g : M2) = su2Angle g := rfl

theorem su2KappaM2_coe (g : SU2) : su2KappaM2 (g : M2) = su2Kappa g := rfl

theorem su2LogM2_coe (g : SU2) : su2LogM2 (g : M2) = su2Log g := rfl

theorem su2AngleM2_one : su2AngleM2 (1 : M2) = 0 := by
  have htr : Matrix.trace (1 : M2) = (2 : ℂ) := by
    simp [Matrix.trace_one]
  unfold su2AngleM2
  rw [htr]
  norm_num

theorem su2LogM2_one : su2LogM2 (1 : M2) = 0 := by
  rw [show (1 : M2) = ((1 : SU2) : M2) from coe_one.symm, su2LogM2_coe, su2Log_one]

theorem continuous_su2AngleM2 : Continuous su2AngleM2 := by
  have heq : su2AngleM2 = fun Y => Real.arccos (reTraceCLM Y / 2) := by
    funext Y
    rw [su2AngleM2, reTraceCLM_apply]
  rw [heq]
  exact Real.continuous_arccos.comp (reTraceCLM.continuous.div_const 2)

/-! ## §3 — `su2LogM2` restricted to the image of `SU2` is continuous at `1`, via the ALREADY
COMPILED unconditional bound `frobNorm_su2Log_le`, squeezed against `su2Angle`'s ordinary
continuity. No quadratic remainder is used or assumed. -/

def suImage : Set M2 := Set.range (fun (h : SU2) => (h : M2))

theorem frobNorm_su2LogM2_le_of_mem {Y : M2} (hY : Y ∈ suImage) :
    frobNorm (su2LogM2 Y) ≤ Real.sqrt 2 * su2AngleM2 Y := by
  obtain ⟨g, rfl⟩ := hY
  rw [su2LogM2_coe, su2AngleM2_coe]
  exact frobNorm_su2Log_le g

theorem tendsto_su2LogM2_nhdsWithin :
    Tendsto su2LogM2 (nhdsWithin (1 : M2) suImage) (nhds (0 : M2)) := by
  have hangle : Tendsto su2AngleM2 (nhdsWithin (1 : M2) suImage) (nhds (0 : ℝ)) := by
    have hc := (continuous_su2AngleM2.continuousAt (x := (1 : M2))).tendsto
    rw [su2AngleM2_one] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun Y => Real.sqrt 2 * su2AngleM2 Y)
      (nhdsWithin (1 : M2) suImage) (nhds (0 : ℝ)) := by
    simpa using hangle.const_mul (Real.sqrt 2)
  have hb : Tendsto (fun Y => frobNorm (su2LogM2 Y)) (nhdsWithin (1 : M2) suImage) (nhds (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall (fun Y => frobNorm_nonneg _))
      (eventually_of_mem self_mem_nhdsWithin (fun Y hY => frobNorm_su2LogM2_le_of_mem hY)) hupper
  have h2b : Tendsto (fun Y => 2 * frobNorm (su2LogM2 Y)) (nhdsWithin (1 : M2) suImage) (nhds (0 : ℝ)) := by
    simpa using hb.const_mul (2 : ℝ)
  exact squeeze_zero_norm'
    (Eventually.of_forall (fun Y => opNorm_le_two_mul_frobNorm (su2LogM2 Y))) h2b

/-! ## §4 — `su2LogM2` has Fréchet derivative `id` at `1`, restricted to `suImage`, via the inverse
function theorem applied to `NormedSpace.exp`. -/

theorem normedExp_su2Log_eq_coe (g : SU2) (h2 : g ≠ su2NegOne) :
    NormedSpace.exp (su2Log g) = (g : M2) := by
  by_cases hmem : NormedSpace.exp (su2Log g) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  · have hexp := su2_exp_log_of_ne_negOne g h2
    have hcoe := su2Exp_of_mem hmem
    rw [hexp] at hcoe
    exact hcoe.symm
  · exfalso
    have hexp := su2_exp_log_of_ne_negOne g h2
    have h1 : su2Exp (su2Log g) = 1 := su2Exp_of_not_mem hmem
    rw [h1] at hexp
    apply hmem
    rw [← hexp]
    simp [su2Log_one, NormedSpace.exp_zero]

def hasFDerivWithinAt_su2LogM2 :=
  HasFDerivWithinAt.of_local_left_inverse (g := su2LogM2) (f' := ContinuousLinearEquiv.refl ℝ M2)
    (t := (Set.univ : Set M2)) (s := suImage) (a := (1 : M2))
    (by rw [nhdsWithin_univ, su2LogM2_one]; exact tendsto_su2LogM2_nhdsWithin)
    (by rw [su2LogM2_one]; exact hasFDerivAt_exp_zero.hasFDerivWithinAt)
    (⟨1, coe_one⟩ : (1 : M2) ∈ suImage)
    (by
      have hne1 : (1 : M2) ≠ ((su2NegOne : SU2) : M2) := by
        rw [coe_su2NegOne]
        intro h
        have h00 := congrFun (congrFun h 0) 0
        simp only [Matrix.one_apply] at h00
        norm_num at h00
      have hne_ev : ∀ᶠ x in nhds (1 : M2), x ≠ ((su2NegOne : SU2) : M2) :=
        (isOpen_compl_singleton).mem_nhds hne1
      filter_upwards [self_mem_nhdsWithin, hne_ev.filter_mono nhdsWithin_le_nhds]
        with x hxmem hxne
      obtain ⟨h, rfl⟩ := hxmem
      have hh : h ≠ su2NegOne := fun heq => hxne (by rw [heq])
      rw [su2LogM2_coe]
      exact normedExp_su2Log_eq_coe h hh)

/-! ## §5 — the general chain-rule step: any `SU2`-valued curve through `1`, differentiated via
`M2`, composes with `su2LogM2`'s restricted derivative to give `su2Log ∘ (curve)`'s derivative.
Genuinely new, reusable assembly; not tied to `modifiedAverage`. -/

def hasDerivAt_su2Log_of_hasDerivAt_coe {f : ℝ → SU2} {D : M2}
    (hf : HasDerivAt (fun t => ((f t : SU2) : M2)) D 0) (hf0 : f 0 = 1) :=
  have hmaps : ∀ᶠ t in nhds (0 : ℝ), ((f t : SU2) : M2) ∈ suImage :=
    Eventually.of_forall (fun t => ⟨f t, rfl⟩)
  have hy : (1 : M2) = ((f 0 : SU2) : M2) := by rw [hf0]; exact coe_one.symm
  have heq : (su2LogM2 ∘ (fun t => ((f t : SU2) : M2))) = (fun t => su2Log (f t)) :=
    funext (fun t => su2LogM2_coe (f t))
  heq ▸ hasFDerivWithinAt_su2LogM2.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hf hmaps hy

/-! ## §6 — applied to `modifiedAverage`: the actual outer-log derivative, unconditional, no
assumed remainder, no identity-loop ban (single `hnc2`, no `hnc1`, no `hell`). -/

def hasDerivAt_su2Log_modifiedAverage_coe_configMul_noloop
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) :=
  hasDerivAt_su2Log_of_hasDerivAt_coe
    (AdalySI1Noloop.ProdAssemble.hasDerivAt_modifiedAverage_coe_configMul_noloop V0 A hah htr ell c
      hnc2)
    (base_zero V0 ell A c)

/-! ## §7 — physical spacing `h`, `Lh := ell*h`: reparametrizing the unit-speed curve multiplies the
derivative by `h` exactly (same bookkeeping as the paid `outer/OuterLogDeriv.lean §3`, reproduced
here rather than imported to avoid a cross-tranche module-name collision). -/

theorem hasDerivAt_const_mul_zero (h : ℝ) : HasDerivAt (fun t : ℝ => h * t) h 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).const_mul h

theorem hasDerivAt_scale_reparam {f : ℝ → M2} {D : M2} (hf : HasDerivAt f D 0) (h : ℝ) :
    HasDerivAt (fun t : ℝ => f (h * t)) (h • D) 0 :=
  HasDerivAt.scomp_of_eq (0 : ℝ) hf (hasDerivAt_const_mul_zero h) (by ring)

noncomputable def Lh (ell : ℕ) (h : ℝ) : ℝ := (ell : ℝ) * h

def hasDerivAt_su2Log_modifiedAverage_physical_noloop
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) (h : ℝ) :=
  hasDerivAt_scale_reparam
    (hasDerivAt_su2Log_modifiedAverage_coe_configMul_noloop V0 A hah htr ell c hnc2) h

#print axioms base_zero
#print axioms su2AngleM2_one
#print axioms su2LogM2_one
#print axioms continuous_su2AngleM2
#print axioms tendsto_su2LogM2_nhdsWithin
#print axioms normedExp_su2Log_eq_coe
#print axioms hasFDerivWithinAt_su2LogM2
#print axioms hasDerivAt_su2Log_of_hasDerivAt_coe
#print axioms hasDerivAt_su2Log_modifiedAverage_coe_configMul_noloop
#print axioms hasDerivAt_su2Log_modifiedAverage_physical_noloop

end AdalySI1Noloop.OuterLogFullDeriv

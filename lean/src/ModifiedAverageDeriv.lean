/-
Owned SI1 scratch file (compute/m1_si1_execution/modified/). Imports the frozen `AdalyFormal`
package read-only; does not modify it.
-/
import AdalyFormal.Balaban.Q1Real
import AdalyFormal.Balaban.BlockedBackground
import AdalyFormal.Balaban.SuTwoLogExpCore
import AdalyFormal.Balaban.CovariantHjMinimizer
import AdalyFormal.Balaban.AdmissibleSubspace
import AdalyFormal.Balaban.QOne
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebraExp

set_option autoImplicit false

/-!
# CMP98 (56)-(63)/(89)'s modified relative average `𝓜_V`, defined independently of `q124Principal`

## Source, image-verified this pass (not carried over from any prior report)

Printed pp.27-28 of `compute/balaban_su2_papers/balaban_CMP98_1985_averaging.pdf`, read directly
from `compute/sol_q1_gate/renders/CMP98_p27_p28-11.png` (printed p.27) and
`CMP98_p27_p28-12.png` (printed p.28), both hashes already recorded in
`compute/cmp98_defining/RENDER_HASHES.txt` and independently re-read as part of this SI1 pass
(2026-09-09):

* **(56)** `R(X)Y = X Y X⁻¹` — conjugation, for `X` an ARBITRARY invertible matrix acting on ANY
  matrix `Y` (p.27). Restricted here to the `SU(2)` GROUP itself (`groupConj`), never to the Lie
  algebra `RMap` restriction `CovariantOperators.RMap` already uses for the linearized `q124`
  channels — this file's object is the actual nonlinear map, not its derivative.
* **(58)** `(R_{0,y}V₁)(Γ_{y,x}) = ∏_{b⊂Γ_{y,x}} R(V₀(Γ_{y,b₋})) V₁,b`, the tree-frame/endpoint
  transport (`rZeroPath` below), for a general bond field `V₁` (not only ones satisfying the axial
  gauge condition (58) states as `=1`; here `V₁` is arbitrary, exactly what CMP98 (89)/(63) need).
* **(59)** `R̄_{0,c} := R((V̄₀)_c)` — conjugation by the background's OWN raw average (15) at `c`
  (`barRZero`/inlined below). This is the one factor of (89)/(63) NOT named in the dispatching
  NEXT_PROOF_PACKET.md's own summary sentence; it is real, and is exactly the raw average (15), so
  this file discharges it entirely from already-compiled `BlockedBackground.ubarSU2`.
* **(63)** the full assembled identity
  `V̄_c(V̄₀)_c⁻¹ = exp[-Σ_{x∈B(c₋)} L⁻ᵈ log(R_{0,c₋}V₁)(Γ_{c₋,x})] · (V̄₁V₀)_c(V̄₀)_c⁻¹ · R̄_{0,c} ·
   exp[Σ_{x'∈B(c₊)} L⁻ᵈ log(R_{0,c₊}V₁)(Γ_{c₊,x'})]`,
  which is eq. (89)'s abbreviated `(R_{0,c₋}V₁)⁻¹ · Ṽ₁ · R̄_{0,c} · (R_{0,c₊}V₁)` written out. This
  file builds `modifiedAverage V0 ell V1 c := V̄_c(V̄₀)_c⁻¹` literally as this four-factor product,
  at the `s = 1` scope `Q1Real.lean`'s own `rZeroA`/`q1RealMain` already use (a single averaging
  step, general block size `ell`, general background `V0` — NOT the (90)-(91) inductive `j`-fold
  tower, which is not attempted in this pass).
* **`(15)`** — the raw average itself, `BlockedBackground.ubarSU2`, REUSED, never redefined.

## What is deliberately NOT claimed here

This file is Step 1 of `NEXT_PROOF_PACKET.md` §3 ("lock the nonlinear definition") only: `𝓜_V`
is DEFINED, its value at the trivial field is PROVED to be the identity, its CMP98 weight is
pinned by a transparent unfold lemma, and its `su2Exp` chart-domain guard is named as an explicit
predicate. NO differentiability statement, NO comparison to `q124Principal`/`rZeroA`, and NO
Fréchet derivative are claimed or attempted — that is SI1's full target, still open.
-/

namespace AdalySI1.ModifiedAverageDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.Q1Real (GammaPath)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.AdmissibleSubspace (blockOf)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one su2Exp_of_mem)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.SuTwoLogExp (su2Alg mem_su2Alg su2Log_mem_su2Alg
  exp_antiHerm_traceless_mem_special)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_zero)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — CMP98 (56): conjugation, restricted to the `SU(2)` group -/

/-- **CMP98 (56)**, `R(X)Y = XYX⁻¹`, restricted from "any invertible matrix acting on any matrix"
to the `SU(2)` GROUP acting on itself by conjugation — closed for free (`SU2` is a group). -/
def groupConj (g h : SU2) : SU2 := g * h * g⁻¹

@[simp] theorem groupConj_one_right (g : SU2) : groupConj g 1 = 1 := by
  simp [groupConj]

#print axioms groupConj_one_right

/-! ## §2 — CMP98 (15)'s pointwise bond product, feeding `(V̄₁V₀)_c` -/

/-- The bond-wise product configuration `V₁·V₀` whose raw average (15) is `(89)`'s
`(V̄₁V₀)_c`. -/
def configMul (V1 V0 : PeriodicLinkConfiguration SU2 L) : PeriodicLinkConfiguration SU2 L :=
  fun e => V1 e * V0 e

@[simp] theorem configMul_trivialU_left (V0 : PeriodicLinkConfiguration SU2 L) :
    configMul (trivialU L) V0 = V0 := by
  funext e; simp [configMul, trivialU]

#print axioms configMul_trivialU_left

/-! ## §3 — CMP98 (58): the tree-gauge transport product `(R_{0,y}V₁)(steps)`

Built by a single `List.foldl`, threading BOTH the accumulated `V₀`-holonomy from the path's own
base (the transport factor `R(V₀(Γ_{y,b₋}))`) and the running ORDERED product of conjugated bond
values — no recomputation of any contour, so the transport factor used at each bond is, by
construction, `V₀` evaluated on EXACTLY the steps already consumed, i.e. literally `Γ_{y,b₋}`.
Every step reads `PeriodicLinkConfiguration`'s POSITIVE-bond storage and completes the reverse
direction by GROUP INVERSION (`(V (next,μ))⁻¹`), the same convention
`Target.ClayStatement.periodicPathHolonomy` already uses. -/
def rZeroPathStep (V0 V1 : PeriodicLinkConfiguration SU2 L) :
    (PeriodicLatticeSite L × SU2 × SU2) → (Fin 3 × Bool) → (PeriodicLatticeSite L × SU2 × SU2) :=
  fun st step =>
    let x := st.1
    let transportSoFar := st.2.1
    let prod := st.2.2
    let next := periodicLatticeStep x step
    -- **Reverse-branch fix (was the [b,-b]-fold defect).** The naive `(V1 (next,μ))⁻¹` is the bare
    -- group inverse of the POSITIVE bond value; it is not the relative field's own value on the
    -- reversed bond. With `g := V0 (next,μ)`, `u := V1 (next,μ)`, the total field is `W = u*g`
    -- (`configMul`'s order), so the reversed total field is `W⁻¹ = g⁻¹u⁻¹` and the reversed
    -- background alone is `g⁻¹`; the relative coordinate solving `W⁻¹ = V1' * g⁻¹` is therefore
    -- `V1' = g⁻¹u⁻¹g`, i.e. `groupConj g⁻¹ u⁻¹` — NOT `u⁻¹`. This is what `rZeroPathStep_fold`
    -- below certifies: with this fix, a forward step followed by its own reverse cancels exactly.
    let bondFactor : SU2 :=
      if step.2 then V1 (x, step.1)
      else groupConj (V0 (next, step.1))⁻¹ (V1 (next, step.1))⁻¹
    let bgFactor : SU2 := if step.2 then V0 (x, step.1) else (V0 (next, step.1))⁻¹
    (next, transportSoFar * bgFactor, prod * groupConj transportSoFar bondFactor)

/-- **`(R_{0,y}V₁)(steps)`, CMP98 (58), literally**, for the field `V₁` and background `V₀`, along
an arbitrary signed path `steps` based at `y` (used below at `steps = GammaPath y x`, CMP95
(1.7)'s own staircase, matching (63)'s `Γ_{c₋,x}`/`Γ_{c₊,x'}` notation exactly — NOT the narrower
single-direction segment `Q1Real.rZeroA` uses for its own, different, linearized purpose). -/
noncomputable def rZeroPath (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) : SU2 :=
  (steps.foldl (rZeroPathStep V0 V1) (base, 1, 1)).2.2

theorem rZeroPathStep_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L)
    (st : PeriodicLatticeSite L × SU2 × SU2) (step : Fin 3 × Bool) :
    (rZeroPathStep V0 (trivialU L) st step).2.2 = st.2.2 := by
  simp [rZeroPathStep, trivialU]

theorem foldl_rZeroPathStep_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L)
    (steps : List (Fin 3 × Bool)) :
    ∀ (st : PeriodicLatticeSite L × SU2 × SU2),
      (steps.foldl (rZeroPathStep V0 (trivialU L)) st).2.2 = st.2.2 := by
  induction steps with
  | nil => intro st; rfl
  | cons step rest ih =>
    intro st
    rw [List.foldl_cons, ih (rZeroPathStep V0 (trivialU L) st step)]
    exact rZeroPathStep_trivialU_right V0 st step

/-- **Value at zero, the transport level**: the trivial field transports to the identity along
any path, for any background. -/
theorem rZeroPath_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) :
    rZeroPath V0 (trivialU L) base steps = 1 := by
  unfold rZeroPath
  exact foldl_rZeroPathStep_trivialU_right V0 steps (base, 1, 1)

#print axioms rZeroPathStep_trivialU_right
#print axioms foldl_rZeroPathStep_trivialU_right
#print axioms rZeroPath_trivialU_right

/-! ## §3b — the `[b,-b]` fold, CORRECTED: a forward step followed by its own reverse is the
identity, after the fix above. This is the exact obligation Astra's audit named unmet. -/

/-- Physical round-trip on the periodic lattice: stepping forward then backward in the SAME
direction returns to the starting site. General (no periodicity edge case excluded: `Fin (L μ+1)`
additive-group cancellation handles wraparound uniformly). -/
theorem periodicLatticeStep_forward_backward {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    periodicLatticeStep (periodicLatticeStep x (μ, true)) (μ, false) = x := by
  funext ν
  by_cases h : ν = μ
  · subst h
    simp [periodicLatticeStep, Function.update_self, add_sub_cancel_right]
  · simp [periodicLatticeStep, Function.update_of_ne h]

/-- **The `[b,-b]` fold is the identity, at the transport-step level.** With the reverse-branch
fix above: a forward bond step then its own reverse restores BOTH the background transport prefix
and the accumulated tree-frame product to their starting values, for every background `V0`, field
`V1`, base site and direction — not merely at the trivial field. This is the genuine group
calculation `u * (g⁻¹u⁻¹g —conjugated by g—) = u * u⁻¹ = 1` that the unfixed file could not
state, let alone prove. -/
theorem rZeroPathStep_fold (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (μ : Fin 3) :
    ([(μ, true), (μ, false)] : List (Fin 3 × Bool)).foldl (rZeroPathStep V0 V1) (base, 1, 1)
      = (base, 1, 1) := by
  show rZeroPathStep V0 V1 (rZeroPathStep V0 V1 (base, 1, 1) (μ, true)) (μ, false) = (base, 1, 1)
  unfold rZeroPathStep
  simp only [periodicLatticeStep_forward_backward, groupConj]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp <;> group

/-- **The `[b,-b]` fold is the identity, at the public `rZeroPath` level** — the form SI1 actually
consumes: the raw relative tree-frame transport of a bond immediately followed by its own reverse
is trivial, for arbitrary background and field, not only the zero field. -/
theorem rZeroPath_fold (V0 V1 : PeriodicLinkConfiguration SU2 L)
    (base : PeriodicLatticeSite L) (μ : Fin 3) :
    rZeroPath V0 V1 base [(μ, true), (μ, false)] = 1 := by
  unfold rZeroPath
  rw [rZeroPathStep_fold]

#print axioms periodicLatticeStep_forward_backward
#print axioms rZeroPathStep_fold
#print axioms rZeroPath_fold

/-! ## §4 — CMP98 (78)/(63)'s endpoint tree-gauge average `\overline{R_{0,y}V₁}` -/

/-- **`\overline{R_{0,y}V₁}`, CMP98 (63), literally**: `exp[Σ_{x∈B(y)} L⁻ᵈ log (R_{0,y}V₁)(Γ_{y,x})]`
at `d = 3`, `L = ell` — the SAME `ell⁻³` weight, block set (`blockOf`, `stepBlockOf_one`-equal at
stride 1) and `su2LogExp` chart `Q1Real.rZeroA`/`BlockedBackground.ubarSU2` already use. This is
ONE of the "both endpoint tree-gauge/averaged factors" `𝓜_V` needs; the other is the SAME function
evaluated at `y = c₊`. -/
noncomputable def endpointAvg (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : SU2 :=
  su2Exp (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 V1 y (GammaPath y x)))

/-- **Scale-factor lemma**: `endpointAvg` carries EXACTLY CMP98's `L⁻ᵈ = ell⁻³` prefactor inside
`su2Exp`, not a silently different normalization — pinned by unfolding, the same discipline
`Q1Real.lean`'s own header uses to keep its `ell⁻³`-vs-`ell⁻⁴` tension visible rather than hidden. -/
theorem endpointAvg_eq (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) :
    endpointAvg V0 V1 ell y =
      su2Exp (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 V1 y (GammaPath y x))) :=
  rfl

/-- **Value at zero, the endpoint level**: the trivial field averages to the identity at either
endpoint, for any background and any block size. -/
theorem endpointAvg_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) :
    endpointAvg V0 (trivialU L) ell y = 1 := by
  unfold endpointAvg
  have hterm : ∀ x ∈ blockOf y ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 (trivialU L) y (GammaPath y x)) = (0 : M2) := by
    intro x _
    rw [rZeroPath_trivialU_right, su2Log_one, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, su2Exp_zero]

#print axioms endpointAvg_eq
#print axioms endpointAvg_trivialU_right

/-! ## §5 — CMP98 (63)'s chart-domain guard, named as a predicate

`su2Exp`'s totalisation guard (`SuTwoLogExpCore.su2Exp`'s own `dite`) is transparent — genuinely
equal to `NormedSpace.exp` — exactly when the accumulated sum lands in `SU(2)` under the ambient
exponential. CMP98's own text calls this "a good approximation ... for `V'` close to `1`" (p.28); THIS
file states it as an explicit Prop rather than a silent standing assumption. -/

/-- **CMP98's "one neighborhood of zero" regularity hypothesis, as a named predicate**: the
endpoint chart at `(V0,V1,ell,y)` sits on `su2Exp`'s transparent branch. -/
def EndpointChartDomain (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : Prop :=
  NormedSpace.exp (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 V1 y (GammaPath y x))
      : M2) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- On the chart domain, `endpointAvg`'s underlying matrix genuinely IS the ambient exponential
of CMP98's own bracket — not the totalisation guard's truncated `1` fallback. -/
theorem endpointAvg_coe_eq_of_chartDomain (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) (h : EndpointChartDomain V0 V1 ell y) :
    ((endpointAvg V0 V1 ell y : SU2) : M2) =
      NormedSpace.exp (∑ x ∈ blockOf y ell,
        ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 V1 y (GammaPath y x))) := by
  unfold endpointAvg
  exact su2Exp_of_mem h

/-- The trivial field is unconditionally on the chart domain, at every background/block size —
its bracket is literally `0` (`endpointAvg_trivialU_right`'s own computation), and `exp 0 = 1 ∈
SU(2)` always. -/
theorem endpointChartDomain_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : EndpointChartDomain V0 (trivialU L) ell y := by
  have hterm : ∀ x ∈ blockOf y ell,
      ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 (trivialU L) y (GammaPath y x)) = (0 : M2) := by
    intro x _
    rw [rZeroPath_trivialU_right, su2Log_one, smul_zero]
  unfold EndpointChartDomain
  rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero, NormedSpace.exp_zero]
  exact Submonoid.one_mem _

#print axioms endpointAvg_coe_eq_of_chartDomain
#print axioms endpointChartDomain_trivialU_right

/-! ## §5b — `EndpointChartDomain` is actually VACUOUS, and the genuine source-margin replacement

**Finding, not claimed by the unfixed file:** `EndpointChartDomain` holds UNCONDITIONALLY, for
EVERY `V0 V1 ell y` — not only at the trivial field. `su2Log` always lands in `su2Alg` (the
already-compiled `su2Log_mem_su2Alg`), `su2Alg` is a `ℚ`-SUBMODULE of `M2` so it is closed under
the exact finite sum/rational-scalar combination `endpointAvg`'s bracket is, and `su2Alg`'s
exponential is UNCONDITIONALLY special-unitary (`exp_antiHerm_traceless_mem_special`, no smallness
hypothesis at all). So bare pointwise `exp ∈ SU(2)` membership can never be CMP98's actual
"one neighborhood of zero" regularity hypothesis (p.28): it never excludes anything. This is the
precise sense in which the audited predicate was "only pointwise exp membership, not a branch
neighborhood with source margins." -/

theorem endpointAvg_exponent_mem_su2Alg (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) :
    (∑ x ∈ blockOf y ell, ((ell : ℚ) ^ 3)⁻¹ • su2Log (rZeroPath V0 V1 y (GammaPath y x)))
      ∈ su2Alg :=
  Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (su2Log_mem_su2Alg _))

/-- **`EndpointChartDomain` holds for EVERY `V1`, unconditionally.** Supersedes
`endpointChartDomain_trivialU_right`, which is now a special case. -/
theorem endpointChartDomain_always (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : EndpointChartDomain V0 V1 ell y := by
  unfold EndpointChartDomain
  obtain ⟨htr, hah⟩ := mem_su2Alg.mp (endpointAvg_exponent_mem_su2Alg V0 V1 ell y)
  exact exp_antiHerm_traceless_mem_special hah htr

/-- **The genuine chart/branch predicate, with a real source margin `b`.** CMP98 p.28's actual
hypothesis is that the raw relative tree-frame path values entering the average are sufficiently
CLOSE TO THE IDENTITY (its own worked example threshold is small, of angle type) — a quantified
neighborhood-of-zero condition on each of the `ell^3` per-bond terms, using this project's OWN
established S3 averaging-margin idiom (`BlockingLinkEstimate.frobNorm_blockExponent_le`'s
hypothesis shape), not bare guard membership. Unlike `EndpointChartDomain`, this predicate has real
content: it is FALSE whenever some path value's raw log is not simultaneously bounded by `b`, and
it gives an actual nested-neighborhood (radius) structure (`endpointChartMargin_mono` below). -/
def EndpointChartMargin (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) (b : ℝ) : Prop :=
  ∀ x ∈ blockOf y ell, frobNorm (su2Log (rZeroPath V0 V1 y (GammaPath y x))) ≤ b

/-- Genuine neighborhood structure: a wider radius is implied by a narrower one. Bare pointwise
membership has no such axis at all. -/
theorem endpointChartMargin_mono (V0 V1 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) {b1 b2 : ℝ} (hb : b1 ≤ b2)
    (h : EndpointChartMargin V0 V1 ell y b1) : EndpointChartMargin V0 V1 ell y b2 :=
  fun x hx => le_trans (h x hx) hb

/-- The trivial field sits at margin EXACTLY `0` (the tightest possible radius), for every
background and block size — the margin predicate's own zero-input sanity check, matching
`endpointAvg_trivialU_right`/`endpointChartDomain_trivialU_right` at the sharpest radius. -/
theorem endpointChartMargin_trivialU_right (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (y : PeriodicLatticeSite L) : EndpointChartMargin V0 (trivialU L) ell y 0 := by
  intro x _
  rw [rZeroPath_trivialU_right, su2Log_one]
  exact le_of_eq frobNorm_zero

#print axioms endpointAvg_exponent_mem_su2Alg
#print axioms endpointChartDomain_always
#print axioms endpointChartMargin_mono
#print axioms endpointChartMargin_trivialU_right

/-! ## §6 — CMP98 (89)/(63): the modified relative average `𝓜_V`, assembled -/

/-- `c₊` for a coarse bond `c` of block size `ell` at stride `1`: `ell` forward steps in direction
`c.2` from `c.1`. -/
def cPlus (ell : ℕ) (c : PeriodicLatticeEdge L) : PeriodicLatticeSite L :=
  pathSite c.1 c.2 ell

/-- **`𝓜_V(V₁)_c`, CMP98 (89)/(63), literally**:
`(R_{0,c₋}V₁)⁻¹ · (V̄₁V₀)_c(V̄₀)_c⁻¹ · R̄_{0,c}((R_{0,c₊}V₁))`, where `R̄_{0,c} = R((V̄₀)_c)` (59) is
CONJUGATION by the raw average (15) (`ubarSU2`), applied to the far endpoint factor — exactly (63)'s
placement of `R̄_{0,c}` between the tree-frame ratio and the `c₊` bracket. Fixed `s = 1`
(`Q1Real.lean`'s own scope); `V0` is the prescribed background, `ell` the block size, `V1` the
field being averaged. -/
noncomputable def modifiedAverage (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (V1 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) : SU2 :=
  (endpointAvg V0 V1 ell c.1)⁻¹
    * (ubarSU2 1 ell (configMul V1 V0) c * (ubarSU2 1 ell V0 c)⁻¹)
    * groupConj (ubarSU2 1 ell V0 c) (endpointAvg V0 V1 ell (cPlus ell c))

/-- **Value at zero: `𝓜_V(𝟙) = 𝟙`.** The identity field averages to the identity, for EVERY
background `V0`, block size `ell`, and coarse bond `c` — the group-valued analogue of
`NEXT_PROOF_PACKET.md`'s `𝔑_{V,s,L}(0) = 0`. Genuine content, not `rfl`: it uses
`endpointAvg_trivialU_right` at BOTH endpoints and `configMul_trivialU_left`, not merely
unfolding. -/
theorem modifiedAverage_trivialU (V0 : PeriodicLinkConfiguration SU2 L) (ell : ℕ)
    (c : PeriodicLatticeEdge L) :
    modifiedAverage V0 ell (trivialU L) c = 1 := by
  unfold modifiedAverage
  rw [endpointAvg_trivialU_right, endpointAvg_trivialU_right, configMul_trivialU_left]
  simp [groupConj]

#print axioms modifiedAverage_trivialU

/-! ## §7 — stride/physical-h bookkeeping for `s = 1`: precisely characterized, not attempted here

`cPlus` already fixes stride `s = 1`: it advances by exactly `ell` unit steps (`pathSite c.1 c.2
ell`), matching this file's single-averaging-step scope (`Q1Real.lean`'s own `rZeroA`/`q1RealMain`
use the same `s = 1`). For general stride the far endpoint should be `pathSite c.1 c.2 (s * ell)`
(or `s` iterations of `cPlus`), not attempted here.

No physical lattice spacing `h` appears anywhere in this file, and it cannot yet: `modifiedAverage`
is entirely GROUP-valued (`SU2`), with no tangent/linearization step, whereas the SI1 target's
`(Lh) • q124Principal` is a REAL-LINEAR map on a real vector space of directions. `h` enters only
once a derivative of `modifiedAverage` at `V1 = 1` is taken (turning the `SU2`-valued map into a
map on `su2Alg`/its coordinates); no such derivative is defined in this file. The precise
bookkeeping obligation for the next phase is therefore: (i) differentiate `modifiedAverage` at the
trivial field along `A ↦ su2Exp (t • (h • A))`-type curves (reusing `DerivSeed.lean`'s
`hasDerivAt_su2Exp_coe_smul` at the single-factor level), and (ii) identify the resulting
HOMOGENEOUS coefficient in `h` with `q124Principal`'s own `Lh` normalization at `s = 1`. Neither
step is attempted here; this paragraph is the requested precise characterization, not a fix. -/

end AdalySI1.ModifiedAverageDeriv

/-
Owned SI1 L7 file (compute/m1_si1_step1/l7/). Self-contained against the frozen `AdalyFormal`
package only (`AdalyFormal.Balaban.CovariantOperators`, for `suTwo`/`SuTwo`) — no noloop/prod/step1
file copies needed for this lemma.

## Scope

CHANNEL_EXPANSION.md §7 row L7 ("Named raw leaf extraction") needs each raw log-loop leaf
`ℓ'_x = deriv (fun t => su2Log (loopVar ...)) 0` repackaged as a genuine `SuTwo` element (via
`principalSuTwoLog g := ⟨su2Log g, su2Log_antiHermitian g, su2Log_traceless g⟩`,
`compute/deltak_r66/PrincipalCoeff.lean` / `T1MainSegment.lean` Part 2) before it can be fed to the
`SuTwo`-typed `gOp`/`adOp`/`gInvOp` operators used by the paid `dexp_eq_gOp`/`dexp_eq_gOpM2`
(`compute/m1_si1_step1/DexpRodriguesG.lean`). `su2Log g` is traceless and anti-Hermitian for every
fixed `g` (`su2Log_traceless`/`su2Log_antiHermitian`, already paid, unconditional); what was
missing is that a DERIVATIVE of a `suTwo`-valued curve is again `suTwo`-valued — needed because
`ℓ'_x` is itself a `deriv`, not a `su2Log` value at a fixed point. This file supplies that missing
mechanical bridge, proved directly (not via submodule/closed-set topology, to avoid depending on
unfamiliar Mathlib closedness API): `suTwo`'s two defining equations (`Xᴴ = -X`, `trace X = 0`)
are each preserved by `ℝ`-linear-continuous-map composition (`conjTranspose`, `trace`), so if a
curve `G` satisfies both pointwise for every `t`, so does `deriv G t0`, by uniqueness of `HasDerivAt`
applied to the two (function-level) rewritten sides. This is the SAME proof shape already paid in
`compute/m1_si1_noloop/phi/deps/RawAverageDeriv.lean` (`conjTransposeCLM`/`hasDerivAt_conjTranspose_curve`,
`reTraceLM`/`hasDerivAt_reTrace_curve`), reinstantiated here for the full complex trace instead of
its real part, and combined into the actual submodule-membership statement.

## What this does NOT close

The core L7 split (`ℓ'_x = P_x τ_x + P_x σ_x - N_x J_- 𝓑 φ_{x'} - N_x d`, CHANNEL_EXPANSION.md
(log-4)) still requires identifying `ℓ'_x` with `gInvOp (-(adOp Z_x)) v` for the (4-legs) value
`v` at EVERY block point `x` — this is exactly `compute/m1_si1_step1/l4/RESULT.md`'s named,
still-BLOCKED target for general (non-identity) `W_x` (needs `hunit : IsUnit (gOp (-(adOp Z_x)))`,
measured there at 72 files / 13,310 lines across `deltak_r53`-`deltak_r82`). This file only
supplies the SuTwo-repackaging step, not that bridge.
-/
import AdalyFormal.Balaban.CovariantOperators

set_option autoImplicit false
noncomputable section

open Matrix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace AdalySI1.L7

open AdalyFormal.Balaban.CovariantOperators (suTwo mem_suTwo_iff)

/-- `conjTranspose` is `ℝ`-linear on `M2`, hence differentiates unconditionally. Same shape as
`compute/m1_si1_noloop/phi/deps/RawAverageDeriv.lean`'s `conjTransposeLM`/`conjTransposeCLM`. -/
def conjTransposeLM : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun M := Mᴴ
  map_add' := Matrix.conjTranspose_add
  map_smul' r M := by simp [Matrix.conjTranspose_smul]

noncomputable def conjTransposeCLM : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  conjTransposeLM.toContinuousLinearMap

theorem hasDerivAt_conjTranspose_curve {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {G' : Matrix (Fin 2) (Fin 2) ℂ} (t0 : ℝ) (hG : HasDerivAt G G' t0) :
    HasDerivAt (fun t => (G t)ᴴ) (G')ᴴ t0 :=
  conjTransposeCLM.hasFDerivAt.comp_hasDerivAt t0 hG

/-- `trace` is `ℝ`-linear on `M2` (not just its real part, unlike
`RawAverageDeriv.lean`'s `reTraceLM`), hence differentiates unconditionally. -/
def traceLM : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ where
  toFun M := Matrix.trace M
  map_add' := Matrix.trace_add
  map_smul' r M := by simp [Matrix.trace_smul]

noncomputable def traceCLM : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ := traceLM.toContinuousLinearMap

theorem hasDerivAt_trace_curve {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    {G' : Matrix (Fin 2) (Fin 2) ℂ} (t0 : ℝ) (hG : HasDerivAt G G' t0) :
    HasDerivAt (fun t => Matrix.trace (G t)) (Matrix.trace G') t0 :=
  traceCLM.hasFDerivAt.comp_hasDerivAt t0 hG

/-- **L7 sub-lemma: the derivative of a `suTwo`-valued curve is itself in `suTwo`.** Needed to
repackage each raw log-loop leaf `deriv (fun t => su2Log (...)) 0` as a genuine `SuTwo` element
before it can be fed to the `SuTwo`-typed `gOp`/`adOp`/`gInvOp` operators. -/
theorem mem_suTwo_of_hasDerivAt {G : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {G' : Matrix (Fin 2) (Fin 2) ℂ}
    {t0 : ℝ} (hG : HasDerivAt G G' t0) (hmem : ∀ t, G t ∈ suTwo) : G' ∈ suTwo := by
  have h1 : ∀ t, (G t)ᴴ = -(G t) := fun t => ((mem_suTwo_iff (G t)).1 (hmem t)).1
  have h2 : ∀ t, Matrix.trace (G t) = 0 := fun t => ((mem_suTwo_iff (G t)).1 (hmem t)).2
  have hC := hasDerivAt_conjTranspose_curve t0 hG
  have hCneg : HasDerivAt (fun t => (G t)ᴴ) (-G') t0 :=
    hG.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall h1)
  have hTr := hasDerivAt_trace_curve t0 hG
  have hTr0 : HasDerivAt (fun t => Matrix.trace (G t)) (0 : ℂ) t0 :=
    (hasDerivAt_const t0 (0 : ℂ)).congr_of_eventuallyEq (Filter.Eventually.of_forall h2)
  exact (mem_suTwo_iff G').2 ⟨hC.unique hCneg, hTr.unique hTr0⟩

#print axioms mem_suTwo_of_hasDerivAt

end AdalySI1.L7

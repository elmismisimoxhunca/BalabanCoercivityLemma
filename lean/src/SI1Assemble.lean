/-
Owned SI1 scratch file (compute/m1_si1_deriv/si1/). Imports the frozen `AdalyFormal` package and
this tranche's own already-compiled `IngredientDeriv` (diff/ing-07) read-only.

## Scope of this pass

Both prior specialist passes (`sonnet/ModifiedAverageDeriv.lean`, `diff/IngredientDeriv.lean`)
independently named the SAME unresolved gap as the block on the full boxed SI1 equality:
differentiating `su2Log` along a curve that is a genuine PRODUCT of conjugated exponentials
(what `rZeroPath` actually is along a multi-step path), not merely a single `su2Exp(t•H)`.
`diff`'s own `hasDerivAt_su2Log_su2Exp_smul` is explicitly scoped to the single-exponential case
via the exact-inverse trick (`Bch2.log_exp`) and does not extend to products.

This file closes exactly that shared gap for FORWARD-ONLY paths (the only paths `endpointAvg`
ever calls `rZeroPath` on), using machinery neither prior pass invoked:
`AdalyFormal.Balaban.SuTwoLogExp.su2_exp_ad` (`exp(Ad g X) = g·exp(X)·g⁻¹`, EXACT, no smallness
hypothesis) converts the forward-path product into a literal `Bch2.expProd` of a list of
adjoint-transported generators (no error term at all), and `Bch2.bch2_telescope` (a compiled
quantitative BCH-2 remainder bound neither prior pass discovered) then gives the needed
first-order Taylor bound in `t`, which converts to `HasDerivAt` by a standard quadratic-remainder
argument.

## What this file does NOT reach

It does NOT differentiate `ubarSU2` (a separate, wholly undifferentiated ingredient feeding the
raw-average factor of `modifiedAverage`), does NOT assemble the 4-factor group-product rule for
`modifiedAverage` itself, does NOT differentiate `log_skew` at the OUTER level of `𝔑_{V,s,L}`, and
does NOT compare any of CMP98 (121)-(124)'s five channels against `q124Principal`'s E1/E2/E3/gbar
or its `Lh`/`ell^{-4}` normalization. The full boxed SI1 equality is NOT claimed here.
-/
import IngredientDeriv
import AdalyFormal.Balaban.Bch2
import AdalyFormal.Balaban.BlockingLinkEstimate
import AdalyFormal.Balaban.BlockedGaugeGuardAlgebra

set_option autoImplicit false

open Matrix

namespace AdalySI1.SI1Assemble

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2_exp_ad adMap adMap_apply
  coe_mul coe_inv coe_one mem_su2Alg adMap_mem_su2Alg)
open AdalyFormal.Balaban.Bch2 (IsSu2 expProd expProd_nil expProd_cons bch2_telescope frobSq_smul)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobNorm_nonneg frobSq_nonneg
  frobSq_mul_right_isometry)
open AdalyFormal.Balaban.BlockingLinkEstimate (frobSq_mul_left_isometry)
open AdalySI1.IngredientDeriv (rZeroPath rZeroPathStep dirDeriv groupConj)

variable {L : PeriodicLatticeExtent}

/-! ## §1 — `adMap` is a Frobenius-norm isometry preserving `IsSu2` -/

theorem coe_conjTranspose_eq_inv (g : SU2) : (g : M2)ᴴ * (g : M2) = 1 := by
  have h1 : ((g⁻¹ * g : SU2) : M2) = ((1 : SU2) : M2) := by rw [inv_mul_cancel]
  rwa [coe_mul, coe_inv, coe_one] at h1

theorem adMap_isSu2 {g : SU2} {X : M2} (hX : IsSu2 X) : IsSu2 (adMap g X) := by
  have h := adMap_mem_su2Alg g (mem_su2Alg.mpr ⟨hX.2, hX.1⟩)
  exact ⟨(mem_su2Alg.mp h).2, (mem_su2Alg.mp h).1⟩

theorem frobSq_adMap (g : SU2) (X : M2) : frobSq (adMap g X) = frobSq X := by
  rw [adMap_apply,
    frobSq_mul_right_isometry ((g : M2) * X) (g : M2)ᴴ
      (by rw [Matrix.conjTranspose_conjTranspose]; exact coe_conjTranspose_eq_inv g)]
  exact frobSq_mul_left_isometry (g : M2) X (coe_conjTranspose_eq_inv g)

theorem frobNorm_adMap (g : SU2) (X : M2) : frobNorm (adMap g X) = frobNorm X := by
  unfold frobNorm; rw [frobSq_adMap]

/-! ## §2 — the forward-path product, EXACTLY as an `expProd`, via `su2_exp_ad` -/

/-- The exact list of `t`-scaled adjoint-transported per-bond generators, in the SAME order
`dirDeriv` sums them (mirrors `dirDeriv`'s own recursion). -/
noncomputable def genList (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) :
    PeriodicLatticeSite L → List (Fin 3 × Bool) → SU2 → List M2
  | _, [], _ => []
  | x, s :: rest, transport =>
      (t • adMap transport (A (x, s.1))) ::
        genList t V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))

theorem genList_sum (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) :
    ∀ (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) (transport : SU2),
      (genList t V0 A base steps transport).sum = t • dirDeriv V0 A base steps transport
  | _, [], _ => by simp [genList, dirDeriv]
  | x, s :: rest, transport => by
      show t • adMap transport (A (x, s.1)) +
          (genList t V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))).sum
        = t • dirDeriv V0 A x (s :: rest) transport
      rw [genList_sum t V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))]
      show t • adMap transport (A (x, s.1)) + t • dirDeriv V0 A (periodicLatticeStep x s) rest
          (transport * V0 (x, s.1))
        = t • (adMap transport (A (x, s.1))
            + dirDeriv V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1)))
      rw [smul_add]

theorem genList_isSu2 (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) :
    ∀ (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) (transport : SU2),
      ∀ X ∈ genList t V0 A base steps transport, IsSu2 X
  | _, [], _ => by simp [genList]
  | x, s :: rest, transport => by
      intro X hX
      simp only [genList, List.mem_cons] at hX
      rcases hX with hX | hX
      · subst hX
        have hAsu2 : IsSu2 (A (x, s.1)) := ⟨hah (x, s.1), htr (x, s.1)⟩
        exact ⟨by rw [Matrix.conjTranspose_smul, (adMap_isSu2 hAsu2).1]; simp,
          by rw [Matrix.trace_smul, (adMap_isSu2 hAsu2).2, smul_zero]⟩
      · exact genList_isSu2 t V0 A hah htr (periodicLatticeStep x s) rest
          (transport * V0 (x, s.1)) X hX

/-- Total path length of `A`'s Frobenius norms along `steps`, tracking the CURRENT site at each
step (not the fixed `base`) — the correct recursive accounting `genList`'s own per-step site
threading needs. -/
noncomputable def pathNormSum (A : PeriodicLatticeEdge L → M2) :
    PeriodicLatticeSite L → List (Fin 3 × Bool) → ℝ
  | _, [] => 0
  | x, s :: rest => frobNorm (A (x, s.1)) + pathNormSum A (periodicLatticeStep x s) rest

theorem genList_frobNorm_sum (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) :
    ∀ (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)) (transport : SU2),
      ((genList t V0 A base steps transport).map frobNorm).sum
        = |t| * pathNormSum A base steps
  | _, [], _ => by simp [genList, pathNormSum]
  | x, s :: rest, transport => by
      show frobNorm (t • adMap transport (A (x, s.1))) +
          ((genList t V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))).map
            frobNorm).sum
        = |t| * pathNormSum A x (s :: rest)
      rw [genList_frobNorm_sum t V0 A (periodicLatticeStep x s) rest (transport * V0 (x, s.1))]
      have hsmul : frobNorm (t • adMap transport (A (x, s.1))) =
          |t| * frobNorm (adMap transport (A (x, s.1))) := by
        unfold frobNorm
        rw [frobSq_smul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
      rw [hsmul, frobNorm_adMap]
      show |t| * frobNorm (A (x, s.1)) + |t| * pathNormSum A (periodicLatticeStep x s) rest
        = |t| * (frobNorm (A (x, s.1)) + pathNormSum A (periodicLatticeStep x s) rest)
      ring

/-! ## §3 — the exact identity: the forward-path product IS an `expProd`, via `su2_exp_ad`

Unlike `diff/IngredientDeriv.lean`'s `hasDerivAt_rZeroPath_forward` (which stops at the raw
group-valued `HasDerivAt`), this identity is EXACT for every `t`, not merely a first-order fact
— it uses `su2_exp_ad` (`exp(Ad g X) = g·exp(X)·g⁻¹`, no smallness hypothesis) at every step, so
no error term is introduced by the conjugated-transport structure at all; the only place a
remainder can appear is `bch2_telescope`'s own (already-quantified) BCH-2 estimate on the
resulting plain product. -/

theorem rZeroPath_eq_expProd (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (base : PeriodicLatticeSite L)
    (steps : List (Fin 3 × Bool)) (hfwd : ∀ s ∈ steps, s.2 = true) :
    rZeroPath V0 (fun e => su2Exp (t • A e)) base steps
      = expProd (genList t V0 A base steps 1) := by
  suffices h : ∀ (steps : List (Fin 3 × Bool)), (∀ s ∈ steps, s.2 = true) →
      ∀ (site : PeriodicLatticeSite L) (transport prod : SU2),
        ((steps.foldl (rZeroPathStep V0 (fun e => su2Exp (t • A e))) (site, transport, prod)).2.2)
          = prod * expProd (genList t V0 A site steps transport) by
    have := h steps hfwd base 1 1
    simpa [rZeroPath] using this
  intro steps
  induction steps with
  | nil => intro _ site transport prod; simp [genList, expProd]
  | cons s rest ih =>
    intro hfwd site transport prod
    have hs : s.2 = true := hfwd s (by simp)
    obtain ⟨μ, hμ⟩ : ∃ μ, s = (μ, true) := ⟨s.1, by cases s; simp_all⟩
    subst hμ
    have hstep : rZeroPathStep V0 (fun e => su2Exp (t • A e)) (site, transport, prod) (μ, true)
        = (periodicLatticeStep site (μ, true), transport * V0 (site, μ),
            prod * groupConj transport (su2Exp (t • A (site, μ)))) := by
      simp [rZeroPathStep]
    have hconj : groupConj transport (su2Exp (t • A (site, μ)))
        = su2Exp (t • adMap transport (A (site, μ))) := by
      have hlin : adMap transport (t • A (site, μ)) = t • adMap transport (A (site, μ)) := by
        simp [adMap_apply, Matrix.mul_smul, Matrix.smul_mul]
      rw [← hlin, su2_exp_ad]
      rfl
    rw [List.foldl_cons, hstep, hconj]
    have hrest := ih (fun s' hs' => hfwd s' (List.mem_cons_of_mem _ hs'))
      (periodicLatticeStep site (μ, true)) (transport * V0 (site, μ))
      (prod * su2Exp (t • adMap transport (A (site, μ))))
    rw [hrest]
    show (prod * su2Exp (t • adMap transport (A (site, μ)))) *
        expProd (genList t V0 A (periodicLatticeStep site (μ, true)) rest
          (transport * V0 (site, μ)))
      = prod * expProd ((t • adMap transport (A (site, μ))) ::
          genList t V0 A (periodicLatticeStep site (μ, true)) rest (transport * V0 (site, μ)))
    rw [expProd_cons, mul_assoc]

/-! ## §4 — the closed BCH-2 quadratic-remainder bound for `su2Log ∘ rZeroPath`, forward paths

This is the concrete instance of the shared gap both `sonnet` and `diff` named: differentiating
`su2Log` along a curve that is a genuine PRODUCT of conjugated exponentials (not a single
`su2Exp(t•H)`). It follows the exact identity above composed with the already-compiled
`Bch2.bch2_telescope`, discovered by neither prior pass. -/

theorem frobNorm_su2Log_rZeroPath_sub_le (t : ℝ) (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (base : PeriodicLatticeSite L)
    (steps : List (Fin 3 × Bool)) (hfwd : ∀ s ∈ steps, s.2 = true)
    (hsmall : |t| * pathNormSum A base steps ≤ 1 / 8) :
    frobNorm (su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) base steps)
        - t • dirDeriv V0 A base steps 1)
      ≤ 14 * (|t| * pathNormSum A base steps) ^ 2 := by
  have hEq := rZeroPath_eq_expProd t V0 A base steps hfwd
  have hSum := genList_sum t V0 A base steps 1
  have hNorm := genList_frobNorm_sum t V0 A base steps 1
  have hmem := genList_isSu2 t V0 A hah htr base steps 1
  have hbnd := bch2_telescope (genList t V0 A base steps 1) hmem (by rw [hNorm]; exact hsmall)
  rw [hEq, ← hSum, ← hNorm]
  exact hbnd

#print axioms coe_conjTranspose_eq_inv
#print axioms adMap_isSu2
#print axioms frobSq_adMap
#print axioms frobNorm_adMap
#print axioms genList_sum
#print axioms genList_isSu2
#print axioms genList_frobNorm_sum
#print axioms rZeroPath_eq_expProd
#print axioms frobNorm_su2Log_rZeroPath_sub_le

end AdalySI1.SI1Assemble

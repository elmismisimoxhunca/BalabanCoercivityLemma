/-
Owned SI1-long file (compute/m1_si1_long/wrap/). Imports the frozen `AdalyFormal` package and the
read-only compiled `IngredientDeriv`/`SI1Assemble` tranche, copied byte-identically into this
directory only for `LEAN_PATH` visibility (hashes checked against
`compute/m1_si1_deriv/COORDINATOR_REVIEW.md`'s `518a0c11…`/`1c9e41cc…` sources and
`79d51b7a…`/`6a2a7a29…` oleans). Neither file is edited.

## Scope

Turns `SI1Assemble.frobNorm_su2Log_rZeroPath_sub_le` (an already-compiled quadratic BCH-2
remainder bound for `su2Log ∘ rZeroPath` along forward paths) into a genuine `HasDerivAt` at
`t = 0`, for arbitrary forward paths, arbitrary traceless anti-Hermitian per-bond direction `A`,
and arbitrary `V0`. All the hard analysis (`Bch2.bch2_telescope`, the exact `expProd` identity) is
already done in `SI1Assemble.lean`; what is added here is the standard "quadratic remainder ⇒
`HasDerivAt`" packaging (`IsBigO.trans_isLittleO` against `t ↦ t²`, mirroring Mathlib's own
`hasFDerivAt_ringInverse`), plus a one-directional `linftyOp`-vs-Frobenius norm bound on `M2`
needed to move the `frobNorm`-valued remainder estimate into the ambient `HasDerivAt` topology
already fixed by `IngredientDeriv.lean`'s own `Matrix.linftyOpNormedRing`/
`Matrix.linftyOpNormedAlgebra` choice (Mathlib registers both `linftyOp` and Frobenius as
competing `local instance`s on `Matrix (Fin 2) (Fin 2) ℂ`; neither is a global instance).

## What this file does NOT reach

It does not touch `ubarSU2`, the 4-factor `modifiedAverage` product rule, the outer `log_skew`
derivative, or any CMP98 (121)–(124) vs `q124Principal` comparison. Only the shared
`su2Log ∘ rZeroPath` gap both prior specialist passes named is closed here, now as a real
derivative rather than a remainder bound.
-/
import SI1Assemble

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1.SI1AssembleDeriv

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Exp_zero su2Log_one)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobNorm_nonneg frobSq_nonneg)
open AdalySI1.IngredientDeriv (rZeroPath rZeroPathStep dirDeriv groupConj)
open AdalySI1.SI1Assemble (pathNormSum frobNorm_su2Log_rZeroPath_sub_le)
open Asymptotics

variable {L : PeriodicLatticeExtent}

/-! ## §1 — a one-directional `linftyOp`-vs-Frobenius bound on `M2`, for `2×2` matrices

`hasDerivAt_su2Log_su2Exp_smul` and `hasDerivAt_rZeroPath_forward` (`IngredientDeriv.lean`) already
fixed the ambient `HasDerivAt` topology on `M2` to `Matrix.linftyOpNormedRing`. The BCH-2 remainder
bound is stated in `frobNorm`. This section supplies the (one-directional, all that is needed)
bridge `‖X‖ ≤ 2 · frobNorm X`, proved directly by entrywise `Complex.normSq` algebra — the same
"no Mathlib matrix-norm-instance" style `RMapLipschitz.lean` already uses, so no PiLp/`WithLp`
unfolding is needed on either side. -/

theorem entry_norm_le_frobNorm (A : M2) (i j : Fin 2) : ‖A i j‖ ≤ frobNorm A := by
  have hsq : ‖A i j‖ ^ 2 ≤ frobSq A := by
    rw [← Complex.normSq_eq_norm_sq]
    fin_cases i <;> fin_cases j <;>
      simp [frobSq] <;>
      nlinarith [Complex.normSq_nonneg (A 0 0), Complex.normSq_nonneg (A 0 1),
        Complex.normSq_nonneg (A 1 0), Complex.normSq_nonneg (A 1 1)]
  have h0 : (0 : ℝ) ≤ ‖A i j‖ := norm_nonneg _
  have hs : Real.sqrt (‖A i j‖ ^ 2) ≤ Real.sqrt (frobSq A) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h0, ← frobNorm] at hs

theorem opNorm_le_two_mul_frobNorm (A : M2) : ‖A‖ ≤ 2 * frobNorm A := by
  have hpos : (0:ℝ) ≤ 2 * frobNorm A := mul_nonneg (by norm_num) (frobNorm_nonneg A)
  have hnn : ‖A‖₊ ≤ (2 * frobNorm A).toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le (fun i _ => ?_)
    rw [Fin.sum_univ_two, ← NNReal.coe_le_coe, NNReal.coe_add, coe_nnnorm, coe_nnnorm,
      Real.coe_toNNReal _ hpos]
    have h0 := entry_norm_le_frobNorm A i 0
    have h1 := entry_norm_le_frobNorm A i 1
    linarith
  have h2 := NNReal.coe_le_coe.mpr hnn
  rwa [coe_nnnorm, Real.coe_toNNReal _ hpos] at h2

/-! ## §2 — the forward path collapses to the identity at `t = 0`

Every bond factor becomes `1` (the constant `su2Exp 0`), regardless of `V0` or the direction `A`,
so the fold's product component is `prod` at every step and the whole path collapses to `1`. -/

theorem foldl_snd_snd_of_inv {X Y Z : Type*} {g : (X × Y × Z) → (Fin 3 × Bool) → (X × Y × Z)}
    (hinv : ∀ p s, (g p s).2.2 = p.2.2) :
    ∀ (steps : List (Fin 3 × Bool)) (p : X × Y × Z), (steps.foldl g p).2.2 = p.2.2
  | [], p => rfl
  | s :: rest, p => by
      rw [List.foldl_cons, foldl_snd_snd_of_inv hinv rest (g p s), hinv p s]

theorem rZeroPath_zero_smul_eq_one (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (base : PeriodicLatticeSite L)
    (steps : List (Fin 3 × Bool)) :
    rZeroPath V0 (fun e => su2Exp ((0 : ℝ) • A e)) base steps = 1 := by
  have hconst : (fun e => su2Exp ((0 : ℝ) • A e)) = (fun _ : PeriodicLatticeEdge L => (1 : SU2)) := by
    funext e; rw [zero_smul, su2Exp_zero]
  rw [hconst]
  have hinv : ∀ (p : PeriodicLatticeSite L × SU2 × SU2) (s : Fin 3 × Bool),
      (rZeroPathStep V0 (fun _ : PeriodicLatticeEdge L => (1 : SU2)) p s).2.2 = p.2.2 := by
    intro p s
    simp [rZeroPathStep, groupConj]
  have h := foldl_snd_snd_of_inv hinv steps (base, 1, 1)
  simpa [rZeroPath] using h

/-! ## §3 — a general "quadratic remainder ⇒ `HasDerivAt`" packaging lemma

Mirrors Mathlib's own `hasFDerivAt_ringInverse` (`IsBigO.trans_isLittleO` against `isLittleO_pow_id`
then `hasDerivAt_iff_isLittleO_nhds_zero`), specialised to a `frobNorm`-valued quadratic bound with
the uniform (division-by-zero-free) radius `δ := 1/(8·(S+1))`. -/

theorem hasDerivAt_of_frobNorm_sub_le {f : ℝ → M2} {f' : M2} {S : ℝ} (hS : 0 ≤ S)
    (hf0 : f 0 = 0)
    (hbound : ∀ t : ℝ, |t| * S ≤ 1 / 8 → frobNorm (f t - t • f') ≤ 14 * (|t| * S) ^ 2) :
    HasDerivAt f f' 0 := by
  refine hasDerivAt_iff_isLittleO_nhds_zero.mpr ?_
  have hδpos : (0 : ℝ) < 1 / (8 * (S + 1)) := by positivity
  have hmem : Set.Ioo (-(1 / (8 * (S + 1)))) (1 / (8 * (S + 1))) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) hδpos
  have hO : (fun h : ℝ => f (0 + h) - f 0 - h • f') =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    apply IsBigO.of_bound (2 * 14 * S ^ 2)
    filter_upwards [hmem] with t ht
    have hδ : |t| < 1 / (8 * (S + 1)) := abs_lt.mpr (Set.mem_Ioo.mp ht)
    have hsmall : |t| * S ≤ 1 / 8 := by
      have hlt : |t| * (S + 1) < 1 / (8 * (S + 1)) * (S + 1) :=
        mul_lt_mul_of_pos_right hδ (by linarith)
      have heq : 1 / (8 * (S + 1)) * (S + 1) = 1 / 8 := by
        have hne : (S + 1) ≠ 0 := by positivity
        field_simp
      rw [heq] at hlt
      nlinarith [abs_nonneg t]
    have hb := hbound t hsmall
    have hbridge := opNorm_le_two_mul_frobNorm (f t - t • f')
    have hnormt2 : ‖(t : ℝ) ^ 2‖ = t ^ 2 := by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg t)
    have hsq : (|t| * S) ^ 2 = t ^ 2 * S ^ 2 := by rw [mul_pow, sq_abs]
    rw [zero_add, hf0, sub_zero, hnormt2]
    calc ‖f t - t • f'‖ ≤ 2 * frobNorm (f t - t • f') := hbridge
      _ ≤ 2 * (14 * (|t| * S) ^ 2) := by linarith [hb]
      _ = 2 * 14 * S ^ 2 * t ^ 2 := by rw [hsq]; ring
  exact hO.trans_isLittleO (isLittleO_pow_id (n := 2) (by norm_num))

/-! ## §4 — `pathNormSum` is nonnegative (a sum of `frobNorm`s along the path) -/

theorem pathNormSum_nonneg (A : PeriodicLatticeEdge L → M2) :
    ∀ (base : PeriodicLatticeSite L) (steps : List (Fin 3 × Bool)), 0 ≤ pathNormSum A base steps
  | _, [] => by simp [pathNormSum]
  | x, s :: rest => by
      show 0 ≤ frobNorm (A (x, s.1)) + pathNormSum A (periodicLatticeStep x s) rest
      have h1 := frobNorm_nonneg (A (x, s.1))
      have h2 := pathNormSum_nonneg A (periodicLatticeStep x s) rest
      linarith

/-! ## §5 — the target: a real `HasDerivAt` of `su2Log ∘ rZeroPath`, forward paths, arbitrary `A`,
`V0`

This is the shared gap both `sonnet/ModifiedAverageDeriv.lean` and `diff/IngredientDeriv.lean`
named, now closed as a genuine derivative rather than a remainder bound: `SI1Assemble`'s exact
`expProd` identity plus the compiled `Bch2.bch2_telescope` estimate supply `hbound`; §2 supplies
`hf0`; §3 packages both into `HasDerivAt`. -/

theorem hasDerivAt_su2Log_rZeroPath_forward (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (base : PeriodicLatticeSite L)
    (steps : List (Fin 3 × Bool)) (hfwd : ∀ s ∈ steps, s.2 = true) :
    HasDerivAt (fun t : ℝ => su2Log (rZeroPath V0 (fun e => su2Exp (t • A e)) base steps))
      (dirDeriv V0 A base steps 1) 0 := by
  apply hasDerivAt_of_frobNorm_sub_le (pathNormSum_nonneg A base steps)
  · show su2Log (rZeroPath V0 (fun e => su2Exp ((0 : ℝ) • A e)) base steps) = 0
    rw [rZeroPath_zero_smul_eq_one, su2Log_one]
  · intro t ht
    exact frobNorm_su2Log_rZeroPath_sub_le t V0 A hah htr base steps hfwd ht

#print axioms entry_norm_le_frobNorm
#print axioms opNorm_le_two_mul_frobNorm
#print axioms rZeroPath_zero_smul_eq_one
#print axioms hasDerivAt_of_frobNorm_sub_le
#print axioms pathNormSum_nonneg
#print axioms hasDerivAt_su2Log_rZeroPath_forward

end AdalySI1.SI1AssembleDeriv

/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import GaugeInvClass

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# DOES THE PRINTED PER-CUBE CLASS IMPLY THE GLOBAL ORBIT CLASS?  NO — AND THE OBSTRUCTION IS EXACTLY
# THE WRAPPING HOLONOMY.

`GaugeInvClass.covariant_lemma24_orbit` consumes `GaugeRegular α U = ∃ γ, frobSupBond (U^γ) ≤ α`,
which quantifies ONE GLOBAL gauge. CMP99b (3.35) grants a gauge PER CUBE
(`compute/delta_alpha0/SCOPE.md` §1 transcribes the prefix as `∀□ ∀U ∃u`). The dispatch asked
whether the gauge-invariance transfer makes the global gauge unnecessary.

**It does not, and this file proves it rather than reporting it.** The result is a no-go with a
named witness, plus the exact statement that is missing.

## §0 — WHAT IS PROVED HERE

| statement | declaration |
|---|---|
| the wrapping (Polyakov) holonomy is gauge-COVARIANT, and CONJUGATION-INVARIANT at the center | `wrapHol_gauge`, `wrapHol_centerU_gauge` |
| `GaugeRegular α U` forces every wrapping holonomy within `(L μ + 1)·α` of `1` — a NECESSARY condition, in the campaign's own norm | `wrap_holonomy_le_of_gaugeRegular` |
| the constant center configuration on an ODD torus has wrapping holonomy `−1` | `wrapHol_centerU_odd` |
| **hence it is OUTSIDE the global orbit class whenever `(L μ + 1)·α < 2√2`** | `centerU_odd_not_gaugeRegular` |
| **yet ONE gauge makes it EXACTLY flat on every non-wrapping bond simultaneously** — stronger than any per-cube hypothesis | `centerU_flat_off_wrap` |
| **so the per-cube class does NOT imply the global orbit class** | `perCube_not_implies_global` |
| and the per-cube class is not vacuous the other way: global ⟹ per-cube | `perCubeRegular_of_gaugeRegular` |

## §1 — WHY THIS IS THE RIGHT WITNESS, AND WHAT IT DOES NOT SAY

`AlphaAnalyticity.centerU` (`U ≡ −1`) is the same configuration that `GaugeInvClass` uses to show
the restatement WIDENS the class — on an EVEN torus, where the parity gauge closes up and `centerU`
is globally gauge-equivalent to `1`. On an ODD torus the parity gauge cannot close up, and the
identical configuration becomes the counterexample. **The whole difference between the two cases is
the parity of `L μ + 1`, i.e. a purely topological datum**; nothing local distinguishes them, which
is precisely the point.

This does NOT say the per-cube class is useless, and it does NOT contradict
`compute/gauge_patching/`: that lane proved a DIFFERENT consumer (the source term `‖J(U)‖`) needs no
patching at all, because `J` is a bond-local, gauge-invariant quantity. The covariant Lemma 2.4 is
not bond-local: it sums over the whole torus and its drift bounds are stated at a GLOBAL sup.

**The missing statement, named at the defining declaration.** To close per-cube ⟹ global one needs,
in addition to (3.35), a hypothesis controlling the holonomies of NON-CONTRACTIBLE loops — for the
`wrapHol` of this file, a bound `frobNorm (wrapHol U x μ − 1) ≤ c·α`. That hypothesis is not implied
by (3.35) (this file) and is not printed in CMP99b's (3.35)/(3.36). Bałaban does not need it because
he never forms a global gauge: p.408's Corollary 3.6 localizes every estimate to a domain
`Ω'₀ ⊂ □` inside ONE cube. **The corresponding move for this chain would be a LOCALIZED covariant
Lemma 2.4** — a per-cube floor with per-cube drift constants, summed over a cover. That is a
different theorem from `covariant_lemma24`, whose flat leg (`Lemma24GeneralEll.lemma24_general_ell`)
and whose two drift bounds (`RegularUQChain.coarseDriftEnergy_le`,
`RegularUPerturbation.norm_curlDrift_L2_le_sup`) are all stated globally; it is NOT reachable by
restating a hypothesis, which is the operation this lane is scoped to.

## §2 — DEFINITION CREATED BY THIS FILE, DISCLOSED (OPS-10)

`PerCubeRegular` is new here. It is `compute/gauge_patching/JLocality.CubeGaugeData` with the
entrywise `EB δ` replaced by the Frobenius `frobNorm ≤ α` — i.e. it is the per-cube analogue of
`GaugeRegular` **in `GaugeRegular`'s own norm**, so that the comparison this file makes is between
two classes measured identically and no norm conversion can hide in the gap. The two differ by the
`√2` of `GaugePatching.EBBridge.EB_of_printedNormSq_le`, proved sharp there.
-/

namespace AdalyFormal.Balaban.GaugeInvPerCube

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.RegularUPerturbation (frobSupBond frobSupBond_nonneg
  frobNorm_le_frobSupBond)
open AdalyFormal.Balaban.RegularUQChain (frobNorm_holonomy_sub_one_le)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn GaugeRegular gaugeRegular_of_frobSupBond_le
  periodicPathHolonomy_gauge negOneElem negOneElem_coe negOneElem_mul_self negOneElem_inv
  centerU parityGauge frobNorm_negOne_sub_one frobSupBond_centerU)

variable {L : PeriodicLatticeExtent}

/-! ## §3 — THE CENTER ELEMENT IS CENTRAL (used to strip the conjugating gauge) -/

/-- `−1` is a scalar matrix, hence commutes with every `SU(2)` element. -/
theorem negOneElem_comm (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    g * negOneElem = negOneElem * g := by
  apply Subtype.ext
  show (g : Matrix (Fin 2) (Fin 2) ℂ) * (-1 : Matrix (Fin 2) (Fin 2) ℂ)
    = (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [mul_neg_one, neg_one_mul]

/-- Powers of the center element are central too. -/
theorem negOneElem_pow_comm (k : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    g * negOneElem ^ k = negOneElem ^ k * g := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, negOneElem_comm, ← mul_assoc]

/-- `(−1)^k = −1` for every ODD `k`, from `(−1)² = 1`. -/
theorem negOneElem_pow_odd {k : ℕ} (hk : k % 2 = 1) :
    negOneElem ^ k = (negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  subst hm
  rw [pow_succ, pow_mul, sq, negOneElem_mul_self, one_pow, one_mul]

#print axioms negOneElem_comm
#print axioms negOneElem_pow_comm
#print axioms negOneElem_pow_odd

/-! ## §4 — THE WRAPPING (POLYAKOV) HOLONOMY

The straight closed loop that winds once around direction `μ`. It exists on the torus and on no
finite box; it is the only object in this file that distinguishes the two classes. -/

/-- The straight winding path in direction `μ`: `L μ + 1` forward steps. -/
def wrapPath (L : PeriodicLatticeExtent) (μ : Fin 3) : List (Fin 3 × Bool) :=
  List.replicate (L μ + 1) (μ, true)

/-- **The wrapping holonomy** `W_μ(x) = ∏_{i<L μ+1} U(x + i·e_μ, μ)`, the ordered product of every
link on the straight line through `x` in direction `μ`. -/
def wrapHol (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  periodicPathHolonomy U x (wrapPath L μ)

theorem wrapPath_length (μ : Fin 3) : (wrapPath L μ).length = L μ + 1 := by
  rw [wrapPath, List.length_replicate]

/-- `pathSite` peeled from the LEFT (the tree carries only the right-peeled `pathSite_succ`). -/
theorem pathSite_succ_left (x : PeriodicLatticeSite L) (μ : Fin 3) (k : ℕ) :
    AdalyFormal.Balaban.QOne.pathSite x μ (k + 1)
      = AdalyFormal.Balaban.QOne.pathSite (periodicLatticeShift x μ) μ k :=
  Function.iterate_succ_apply _ k x

/-- `(a + b % n + c) % n = (a + b + c) % n`. -/
theorem add_mod_middle (a b c n : ℕ) : (a + b % n + c) % n = (a + b + c) % n := by
  have h : (a + b % n) % n = (a + b) % n := Nat.add_mod_mod a b n
  calc (a + b % n + c) % n
      = ((a + b % n) % n + c) % n := (Nat.mod_add_mod _ _ _).symm
    _ = ((a + b) % n + c) % n := by rw [h]
    _ = (a + b + c) % n := Nat.mod_add_mod _ _ _

/-- The replicate path's endpoint is the tree's own `QOne.pathSite` (REUSED), so no new iteration
object is introduced. -/
theorem endpoint_replicate (μ : Fin 3) (k : ℕ) (x : PeriodicLatticeSite L) :
    periodicPathEndpoint x (List.replicate k (μ, true))
      = AdalyFormal.Balaban.QOne.pathSite x μ k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      show periodicPathEndpoint (periodicLatticeStep x (μ, true)) (List.replicate k (μ, true))
        = AdalyFormal.Balaban.QOne.pathSite x μ (k + 1)
      have hstep : periodicLatticeStep x (μ, true) = periodicLatticeShift x μ := rfl
      rw [hstep, ih (periodicLatticeShift x μ)]
      exact (Function.iterate_succ_apply _ k x).symm

/-- The `μ`-coordinate of `pathSite x μ k`, on the natural-number representative. Pure `ℕ`
arithmetic; no `ℕ → Fin` coercion appears anywhere in this file. -/
theorem pathSite_val (μ : Fin 3) (k : ℕ) (x : PeriodicLatticeSite L) :
    ((AdalyFormal.Balaban.QOne.pathSite x μ k) μ).val = ((x μ).val + k) % (L μ + 1) := by
  induction k generalizing x with
  | zero =>
      show (x μ).val = ((x μ).val + 0) % (L μ + 1)
      simp only [Nat.add_zero]
      exact (Nat.mod_eq_of_lt (x μ).isLt).symm
  | succ k ih =>
      rw [pathSite_succ_left, ih (periodicLatticeShift x μ),
        periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one', Nat.mod_add_mod, add_mod_middle]
      congr 1
      omega

/-- Off the direction `μ`, `pathSite` does not move. -/
theorem pathSite_off (μ : Fin 3) (k : ℕ) (x : PeriodicLatticeSite L) (ν : Fin 3) (hν : ν ≠ μ) :
    (AdalyFormal.Balaban.QOne.pathSite x μ k) ν = x ν := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [pathSite_succ_left, ih (periodicLatticeShift x μ),
        periodicLatticeShift, Function.update_of_ne hν]

/-- **THE WRAPPING PATH IS CLOSED**: `L μ + 1` forward steps return to the base site. -/
theorem wrapPath_closed (μ : Fin 3) (x : PeriodicLatticeSite L) :
    periodicPathEndpoint x (wrapPath L μ) = x := by
  rw [wrapPath, endpoint_replicate]
  funext ν
  by_cases h : ν = μ
  · subst h
    apply Fin.ext
    rw [pathSite_val, Nat.add_mod_right, Nat.mod_eq_of_lt (x ν).isLt]
  · exact pathSite_off μ (L μ + 1) x ν h

#print axioms wrapPath_length
#print axioms wrapPath
#print axioms wrapHol
#print axioms pathSite_succ_left
#print axioms add_mod_middle
#print axioms endpoint_replicate
#print axioms pathSite_val
#print axioms pathSite_off
#print axioms wrapPath_closed

/-- **THE WRAPPING HOLONOMY IS GAUGE-COVARIANT**: `W_μ(U^γ; x) = γ(x)·W_μ(U; x)·γ(x)⁻¹`. The path
being CLOSED is exactly what turns `periodicPathHolonomy_gauge`'s two different endpoints into a
conjugation. -/
theorem wrapHol_gauge (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (x : PeriodicLatticeSite L) (μ : Fin 3) :
    wrapHol (periodicGaugeTransform γ U) x μ = γ x * wrapHol U x μ * (γ x)⁻¹ := by
  unfold wrapHol
  rw [periodicPathHolonomy_gauge, wrapPath_closed]

/-- **THE NECESSARY CONDITION.** Membership of the GLOBAL orbit class forces every wrapping
holonomy to lie within `(L μ + 1)·α` of the identity, in the campaign's own Frobenius norm.

The proof is `RegularUQChain.frobNorm_holonomy_sub_one_le` (REUSED) applied to the gauged
representative, plus `wrapHol_gauge` to bring the statement back to `U`. -/
theorem wrap_holonomy_le_of_gaugeRegular {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hreg : GaugeRegular α U) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ∃ γ : GaugeFn L,
      frobNorm (((γ x * wrapHol U x μ * (γ x)⁻¹ :
          Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) - 1)
        ≤ ((L μ + 1 : ℕ) : ℝ) * α := by
  obtain ⟨γ, hγ⟩ := hreg
  refine ⟨γ, ?_⟩
  have hb := frobNorm_holonomy_sub_one_le (periodicGaugeTransform γ U) (wrapPath L μ) x
  rw [show periodicPathHolonomy (periodicGaugeTransform γ U) x (wrapPath L μ)
      = wrapHol (periodicGaugeTransform γ U) x μ from rfl, wrapHol_gauge, wrapPath_length] at hb
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_left hγ (by positivity)

#print axioms wrapHol_gauge
#print axioms wrap_holonomy_le_of_gaugeRegular

/-! ## §5 — THE WITNESS: THE CONSTANT CENTER CONFIGURATION ON AN ODD TORUS -/

/-- Every link of `centerU` is `−1`, so the wrapping holonomy is `(−1)^{L μ + 1}`. -/
theorem wrapHol_centerU_pow (x : PeriodicLatticeSite L) (μ : Fin 3) :
    wrapHol (centerU L) x μ = negOneElem ^ (L μ + 1) := by
  unfold wrapHol wrapPath
  generalize (L μ + 1) = k
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    show (if (μ, true).2 then centerU L (x, (μ, true).1)
        else (centerU L (periodicLatticeStep x (μ, true), (μ, true).1))⁻¹)
        * periodicPathHolonomy (centerU L) (periodicLatticeStep x (μ, true))
            (List.replicate k (μ, true))
      = _
    rw [if_pos rfl, ih (periodicLatticeStep x (μ, true))]
    show negOneElem * negOneElem ^ k = negOneElem ^ (k + 1)
    rw [pow_succ, negOneElem_pow_comm]

/-- **THE WRAPPING HOLONOMY OF `U ≡ −1` ON AN ODD TORUS IS `−1`.** -/
theorem wrapHol_centerU_odd {μ : Fin 3} (hodd : (L μ + 1) % 2 = 1)
    (x : PeriodicLatticeSite L) :
    wrapHol (centerU L) x μ = negOneElem := by
  rw [wrapHol_centerU_pow, negOneElem_pow_odd hodd]

/-- The conjugating gauge cancels at the center: `γ(x)·(−1)·γ(x)⁻¹ = −1`. -/
theorem wrapHol_centerU_gauge {μ : Fin 3} (hodd : (L μ + 1) % 2 = 1) (γ : GaugeFn L)
    (x : PeriodicLatticeSite L) :
    γ x * wrapHol (centerU L) x μ * (γ x)⁻¹ = negOneElem := by
  rw [wrapHol_centerU_odd hodd, negOneElem_comm, mul_assoc, mul_inv_cancel, mul_one]

/-- **THE WITNESS IS OUTSIDE THE GLOBAL ORBIT CLASS.** On any torus with `L μ + 1` ODD, the
constant center configuration fails `GaugeRegular α` for every `α` with `(L μ + 1)·α < 2√2`.

Note the CONTRAST with `AlphaAnalyticity.centerU_is_gaugeRegular`, which puts the SAME
configuration in the class at radius `0` when every `L μ + 1` is EVEN. The two are not in tension:
they are the two parities, and nothing local separates them. -/
theorem centerU_odd_not_gaugeRegular {α : ℝ} {μ : Fin 3} (hodd : (L μ + 1) % 2 = 1)
    (hα : ((L μ + 1 : ℕ) : ℝ) * α < 2 * Real.sqrt 2) :
    ¬ GaugeRegular α (centerU L) := by
  intro hreg
  obtain ⟨x⟩ := (inferInstance : Nonempty (PeriodicLatticeSite L))
  obtain ⟨γ, hb⟩ := wrap_holonomy_le_of_gaugeRegular hreg x μ
  rw [wrapHol_centerU_gauge hodd γ x] at hb
  rw [show ((negOneElem : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = -1 from negOneElem_coe, frobNorm_negOne_sub_one] at hb
  linarith

#print axioms wrapHol_centerU_pow
#print axioms wrapHol_centerU_odd
#print axioms wrapHol_centerU_gauge
#print axioms centerU_odd_not_gaugeRegular

/-! ## §6 — YET ONE GAUGE FLATTENS IT EXACTLY OFF THE WRAPPING BONDS -/

/-- A bond WRAPS if its forward step returns the `μ`-coordinate to `0`, i.e. if the coordinate is at
its maximum. Stated on the natural-number representative so it is decidable and box-visible. -/
def Wraps (b : Bond L) : Prop := (b.1 b.2).val + 1 = L b.2 + 1

/-- **ONE GAUGE MAKES `U ≡ −1` EXACTLY `1` ON EVERY NON-WRAPPING BOND, SIMULTANEOUSLY** — on any
torus with every `L μ + 1` ODD and at least `3`.

This is strictly STRONGER than any per-cube hypothesis: a single gauge serves the whole
non-wrapping bond set at once, so a fortiori it serves each cube of any family whose cubes avoid
wrapping bonds. The gauge is `AlphaAnalyticity.parityGauge` (REUSED), which is `(−1)^{|x|}`. -/
theorem centerU_flat_off_wrap (hbig : ∀ μ : Fin 3, 2 ≤ L μ)
    (hodd : ∀ μ : Fin 3, (L μ + 1) % 2 = 1) (b : Bond L) (hb : ¬ Wraps b) :
    periodicGaugeTransform (parityGauge L) (centerU L) b = 1 := by
  obtain ⟨x, μ⟩ := b
  have hlt : (x μ).val + 1 < L μ + 1 := by
    have := (x μ).isLt
    simp only [Wraps] at hb
    omega
  -- the coordinate sum increases by exactly one across a non-wrapping bond, so the parity flips
  have hone : ((1 : Fin (L μ + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by have := hbig μ; omega)
  have hval : ((periodicLatticeShift x μ) μ).val = (x μ).val + 1 := by
    rw [periodicLatticeShift, Function.update_self, Fin.val_add, hone]
    exact Nat.mod_eq_of_lt hlt
  have hoff : ∀ ν : Fin 3, ν ≠ μ → ((periodicLatticeShift x μ) ν).val = (x ν).val := by
    intro ν hν
    rw [periodicLatticeShift, Function.update_of_ne hν]
  have hsplit1 : (∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val)
      = ((periodicLatticeShift x μ) μ).val
        + ∑ ν ∈ Finset.univ.erase μ, ((periodicLatticeShift x μ) ν).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
  have hsplit2 : (∑ ν : Fin 3, (x ν).val)
      = (x μ).val + ∑ ν ∈ Finset.univ.erase μ, (x ν).val :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ μ)).symm
  have heq : (∑ ν ∈ Finset.univ.erase μ, ((periodicLatticeShift x μ) ν).val)
      = ∑ ν ∈ Finset.univ.erase μ, (x ν).val :=
    Finset.sum_congr rfl (fun ν hν => hoff ν (Finset.ne_of_mem_erase hν))
  have hflip : ((∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val) % 2 = 0)
      ↔ ((∑ ν : Fin 3, (x ν).val) % 2 ≠ 0) := by
    rw [hsplit1, hsplit2, heq, hval]; omega
  show parityGauge L x * negOneElem * (parityGauge L (periodicLatticeShift x μ))⁻¹ = 1
  by_cases hpar : (∑ ν : Fin 3, (x ν).val) % 2 = 0
  · have h2 : ((∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val) % 2 = 0) = False := by
      simp only [eq_iff_iff, iff_false]
      exact fun hc => (hflip.mp hc) hpar
    rw [parityGauge, parityGauge, if_pos hpar]
    simp only [h2, if_false]
    rw [negOneElem_inv, one_mul, negOneElem_mul_self]
  · have h2 : (∑ ν : Fin 3, ((periodicLatticeShift x μ) ν).val) % 2 = 0 := hflip.mpr hpar
    rw [parityGauge, parityGauge, if_neg hpar, if_pos h2]
    rw [inv_one, mul_one, negOneElem_mul_self]

#print axioms centerU_flat_off_wrap

/-! ## §7 — THE PER-CUBE CLASS, AND THE NO-GO -/

/-- **`PerCubeRegular α U 𝒞`** — CMP99b (3.35)'s quantifier prefix `∀□ ∃u`, at `GaugeRegular`'s own
Frobenius norm (§2 of the header discloses that this definition is created here). Each cube is
presented as its set of bonds; NOTHING relates the gauges of two cubes, exactly as printed. -/
def PerCubeRegular (α : ℝ) (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (𝒞 : Set (Set (Bond L))) : Prop :=
  ∀ C ∈ 𝒞, ∃ γ : GaugeFn L, ∀ b ∈ C,
    frobNorm (((periodicGaugeTransform γ U) b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α

/-- **GLOBAL ⟹ PER-CUBE, for every cube family** — so the two classes are genuinely comparable and
the no-go below is about the converse only. -/
theorem perCubeRegular_of_gaugeRegular {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    (hreg : GaugeRegular α U) (𝒞 : Set (Set (Bond L))) : PerCubeRegular α U 𝒞 := by
  obtain ⟨γ, hγ⟩ := hreg
  exact fun C _ => ⟨γ, fun b _ => le_trans (frobNorm_le_frobSupBond _ b) hγ⟩

/-- Shrinking the cubes only weakens the hypothesis. -/
theorem perCubeRegular_mono {α : ℝ}
    {U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L}
    {𝒞 𝒞' : Set (Set (Bond L))} (hsub : ∀ C' ∈ 𝒞', ∃ C ∈ 𝒞, C' ⊆ C)
    (h : PerCubeRegular α U 𝒞) : PerCubeRegular α U 𝒞' := by
  intro C' hC'
  obtain ⟨C, hC, hCC⟩ := hsub C' hC'
  obtain ⟨γ, hγ⟩ := h C hC
  exact ⟨γ, fun b hb => hγ b (hCC hb)⟩

/-- **THE NO-GO, AS ONE STATEMENT.**

On any torus whose every extent `L μ + 1` is ODD and at least `3`, the configuration
`U ≡ −1` satisfies

* `PerCubeRegular 0 U 𝒞` at the STRONGEST parameter `α = 0`, for the family `𝒞` consisting of the
  single largest non-wrapping cube — the whole non-wrapping bond set — and hence, by
  `perCubeRegular_mono`, for EVERY family of cubes made of non-wrapping bonds;
* and `¬ GaugeRegular α U` for every `α` with `(L 0 + 1)·α < 2√2`.

**Therefore the printed per-cube class does not imply the global orbit class**, and no amount of
gauge-invariance transfer supplies the missing global gauge: the obstruction
(`wrap_holonomy_le_of_gaugeRegular`) is a gauge INVARIANT that the per-cube data never sees. -/
theorem perCube_not_implies_global {α : ℝ} (hbig : ∀ μ : Fin 3, 2 ≤ L μ)
    (hodd : ∀ μ : Fin 3, (L μ + 1) % 2 = 1)
    (hα : ((L 0 + 1 : ℕ) : ℝ) * α < 2 * Real.sqrt 2) :
    PerCubeRegular 0 (centerU L) {{b : Bond L | ¬ Wraps b}}
    ∧ ¬ GaugeRegular α (centerU L) := by
  refine ⟨?_, centerU_odd_not_gaugeRegular (hodd 0) hα⟩
  intro C hC
  refine ⟨parityGauge L, fun b hb => ?_⟩
  have hb' : ¬ Wraps b := by
    have : C = {b : Bond L | ¬ Wraps b} := hC
    subst this; exact hb
  rw [centerU_flat_off_wrap hbig hodd b hb']
  rw [show ((1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = 1 from rfl,
    sub_self]
  exact le_of_eq AdalyFormal.Balaban.RMapLipschitz.frobNorm_zero

#print axioms Wraps
#print axioms PerCubeRegular
#print axioms perCubeRegular_of_gaugeRegular
#print axioms perCubeRegular_mono
#print axioms perCube_not_implies_global

/-! ## §8 — NON-VACUITY CONTROLS FOR THE NO-GO ITSELF

A no-go proved on an empty hypothesis proves nothing. Three checks. -/

/-- The odd-torus hypothesis is satisfiable: `L μ = 2` for every `μ` gives extents `3`, odd and
`≥ 3`. So `perCube_not_implies_global` is not vacuously hypothesised. -/
theorem odd_torus_exists :
    (∀ μ : Fin 3, 2 ≤ (fun _ : Fin 3 => 2 : PeriodicLatticeExtent) μ)
    ∧ (∀ μ : Fin 3, ((fun _ : Fin 3 => 2 : PeriodicLatticeExtent) μ + 1) % 2 = 1) :=
  ⟨fun _ => le_refl 2, fun _ => by norm_num⟩

/-- The `α`-range in the no-go is a nonempty interval containing the campaign's own threshold
whenever the torus is not enormous: at `L 0 = 2` and `ell ≥ 2`, `3·(1/(186·ell³)) < 2√2`. So the
no-go bites at exactly the hypothesis `covariant_lemma24_orbit_positive` consumes. -/
theorem no_go_covers_campaign_threshold {ell : ℕ} (hell : 0 < ell) :
    (3 : ℝ) * (1 / (186 * (ell : ℝ) ^ 3)) < 2 * Real.sqrt 2 := by
  have h1 : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  have h3 : (1 : ℝ) ≤ (ell : ℝ) ^ 3 := one_le_pow₀ h1
  have hle : 1 / (186 * (ell : ℝ) ^ 3) ≤ 1 / 186 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- The non-wrapping bond set is NOT everything — otherwise §7's per-cube family would be the whole
lattice and the no-go would be an artefact of a degenerate cube. There is a wrapping bond in every
direction. -/
theorem wrapping_bond_exists (μ : Fin 3) :
    ∃ b : Bond L, Wraps b := by
  refine ⟨(Function.update (fun ν => (0 : Fin (L ν + 1))) μ (Fin.last (L μ)), μ), ?_⟩
  show ((Function.update (fun ν => (0 : Fin (L ν + 1))) μ (Fin.last (L μ))) μ).val + 1 = L μ + 1
  rw [Function.update_self]
  rfl

#print axioms odd_torus_exists
#print axioms no_go_covers_campaign_threshold
#print axioms wrapping_bond_exists

end AdalyFormal.Balaban.GaugeInvPerCube

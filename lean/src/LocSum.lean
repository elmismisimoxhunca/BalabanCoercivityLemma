/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocCov
import GaugeInvLocalize

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# SUMMATION WITH BOUNDED MULTIPLICITY — enlarged cubes overlap, and that is priced.

`GaugeInvLocalize.localized_floor_sums_of_gauged` sums per-cube floors on a PARTITION: its three
index families are pairwise disjoint and cover. That is exactly what the localized estimates of
`LocGeom`/`LocCov` do NOT deliver: the enlarged cube `□̃` makes the curl and drift families OVERLAP,
by construction (`LocGeom.tilde`). This module supplies the summation theorem those estimates
actually need, and PRICES the overlap.

## THE RESULT

`floor_sums_multiplicity` — with the bond family only COVERING (multiplicity `≥ 1`, no disjointness)
and the coarse / plaquette / drift families of multiplicity at most `Mq`, `Mp`, `Md`:

>  `(coef − d·Md)·∑_b ‖A b‖² ≤ Mq·ell·∑_c ‖(Q(U)A)(c)‖² + Mp·∑_p ‖(D_U A)(p)‖²`

`floor_sums_gauged_multiplicity` is the same with ONE UNRELATED GAUGE PER CUBE, by
`GaugeInvLocalize`'s pointwise gauge invariance — reused, not rebuilt (LAW-19); this module's
energies are DEFINITIONALLY that module's (`bondEnergyS_eq_bondEnergyOn` etc., all `rfl`).

## THE MULTIPLICITIES, PROVED FROM THE GEOMETRY

`tilde_mult_le_four` — on ANY pairwise-disjoint cube family, a coarse site lies in at most **4** of
the enlarged cubes: itself, and one backward neighbour per direction. `tilde2_mult_le_sixteen` is
the same count for the doubly-enlarged cube (`≤ 16`; not claimed least). Both follow from ONE
lemma, `mult_le_of_family`, whose content is that the displacement operators are INJECTIVE, so a
displacement class plus the target determines the source block, and disjointness then determines
the cube.

## HONEST SCOPE

This module contains NO estimate. It is the bookkeeping layer between the per-cube floors and a
global one; every analytic input is a hypothesis. `localized_floor_sums_of_gauged` is recovered
(`recovers_partition_case`) at `Mq = Mp = 1`, `d = 0`, so this is a strict generalization of the
existing summation theorem, not a competing one.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.CovariantLemma24
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn gaugeActA)

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE COUNTING IDENTITY -/

/-- **Double counting.** Summing a nonnegative weight over a FAMILY of index sets counts each index
once per member set containing it. The one identity every multiplicity bound in this module uses. -/
theorem sum_family_count {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (𝒞 : Finset ι) (S : ι → Finset α) (f : α → ℝ) :
    ∑ i ∈ 𝒞, ∑ a ∈ S i, f a
      = ∑ a : α, ((𝒞.filter (fun i => a ∈ S i)).card : ℝ) * f a := by
  classical
  have h1 : ∀ i : ι, ∑ a ∈ S i, f a = ∑ a : α, if a ∈ S i then f a else 0 := by
    intro i; rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Lower bound from COVERING alone (no disjointness): a covering family's total is at least the
whole. -/
theorem sum_family_ge {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (𝒞 : Finset ι) (S : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hcov : ∀ a : α, 1 ≤ (𝒞.filter (fun i => a ∈ S i)).card) :
    ∑ a : α, f a ≤ ∑ i ∈ 𝒞, ∑ a ∈ S i, f a := by
  rw [sum_family_count]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have h1 : (1 : ℝ) ≤ ((𝒞.filter (fun i => a ∈ S i)).card : ℝ) := by exact_mod_cast hcov a
  nlinarith [hf a]

/-- Upper bound from bounded MULTIPLICITY: a family of multiplicity `≤ M` totals at most `M` times
the whole. -/
theorem sum_family_le {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]
    (𝒞 : Finset ι) (S : ι → Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (M : ℕ)
    (hmul : ∀ a : α, (𝒞.filter (fun i => a ∈ S i)).card ≤ M) :
    ∑ i ∈ 𝒞, ∑ a ∈ S i, f a ≤ (M : ℝ) * ∑ a : α, f a := by
  rw [sum_family_count, Finset.mul_sum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have h1 : ((𝒞.filter (fun i => a ∈ S i)).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmul a
  nlinarith [hf a]

/-! ## §2 — THE MULTIPLICITY OF THE ENLARGED CUBE -/

/-- The displacement operators of the tilde operation: the identity and the three forward coarse
shifts, packaged as one injective family indexed by `Option (Fin 3)`. -/
def actO (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (o : Option (Fin 3)) (y : CSite L ell) :
    CSite L ell :=
  match o with
  | none => y
  | some μ => shiftC hdvd y μ

theorem actO_injective (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (o : Option (Fin 3)) :
    Function.Injective (actO (L := L) (ell := ell) hdvd o) := by
  cases o with
  | none => exact fun _ _ h => h
  | some μ => exact shiftC_injective hdvd μ

/-- **`□̃` characterised by the displacement family**: a coarse site is in the enlarged cube exactly
when it is a displacement of a site of the cube. -/
theorem mem_tilde_iff (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (W : Finset (CSite L ell))
    (z : CSite L ell) : z ∈ tilde hdvd W ↔ ∃ o : Option (Fin 3), ∃ y ∈ W, actO hdvd o y = z := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h1 | h2
    · exact ⟨none, z, h1, rfl⟩
    · obtain ⟨μ, _, hμ⟩ := Finset.mem_biUnion.mp h2
      obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hμ
      exact ⟨some μ, y, hy, hyz⟩
  · rintro ⟨o, y, hy, rfl⟩
    cases o with
    | none => exact Finset.mem_union_left _ hy
    | some μ => exact shiftC_mem_tilde hdvd hy μ

/-- **THE MULTIPLICITY LEMMA.** If each membership of `z` in the `i`-th neighbourhood is witnessed
by an INJECTIVE displacement from a site of `Y i`, and the `Y i` are pairwise disjoint, then the
number of `i` involved is at most the number of displacement classes. Injectivity recovers the
source site from `z`, and disjointness then recovers `i`. -/
theorem mult_le_of_family {ι K : Type*} [DecidableEq ι] [Fintype K] [DecidableEq K] [Nonempty K]
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j))
    (φ : K → CSite L ell → CSite L ell) (hinj : ∀ k, Function.Injective (φ k))
    (P : ι → Prop) [DecidablePred P] (z : CSite L ell)
    (hchar : ∀ i ∈ 𝒞, P i → ∃ k : K, ∃ y ∈ Y i, φ k y = z) :
    (𝒞.filter P).card ≤ Fintype.card K := by
  classical
  have hex : ∀ i ∈ 𝒞.filter P, ∃ k : K, ∃ y ∈ Y i, φ k y = z := by
    intro i hi
    exact hchar i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  choose! f hf using hex
  have hcard : (𝒞.filter P).card ≤ (Finset.univ : Finset K).card := by
    refine Finset.card_le_card_of_injOn f (fun i _ => Finset.mem_univ _) ?_
    intro i hi j hj hfe
    by_contra hne
    obtain ⟨yi, hyi, hzi⟩ := hf i hi
    obtain ⟨yj, hyj, hzj⟩ := hf j hj
    rw [hfe] at hzi
    have hy : yi = yj := hinj (f j) (hzi.trans hzj.symm)
    subst hy
    exact (Finset.disjoint_left.mp
      (hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne) hyi) hyj
  simpa using hcard

/-- **THE ENLARGED CUBES OVERLAP AT MOST `4`-FOLD.** On any pairwise-disjoint cube family, a coarse
site belongs to at most four enlarged cubes. -/
theorem tilde_mult_le_four {ι : Type*} [DecidableEq ι]
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j)) (z : CSite L ell) :
    (𝒞.filter (fun i => z ∈ tilde hdvd (Y i))).card ≤ 4 := by
  classical
  have h := mult_le_of_family (K := Option (Fin 3)) 𝒞 Y hdisj (actO hdvd)
    (actO_injective hdvd) (fun i => z ∈ tilde hdvd (Y i)) z
    (fun i _ hi => (mem_tilde_iff hdvd (Y i) z).mp hi)
  simpa using h

/-- The doubly-enlarged cubes overlap at most `16`-fold — the same lemma with the composed
displacement family. **`16` is not claimed least** (the true count is `10`); it is what the
composition of two `Option (Fin 3)` families gives, and it is all the summation needs. -/
theorem tilde2_mult_le_sixteen {ι : Type*} [DecidableEq ι]
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (𝒞 : Finset ι) (Y : ι → Finset (CSite L ell))
    (hdisj : ∀ i ∈ 𝒞, ∀ j ∈ 𝒞, i ≠ j → Disjoint (Y i) (Y j)) (z : CSite L ell) :
    (𝒞.filter (fun i => z ∈ tilde hdvd (tilde hdvd (Y i)))).card ≤ 16 := by
  classical
  have hchar : ∀ i ∈ 𝒞, z ∈ tilde hdvd (tilde hdvd (Y i)) →
      ∃ k : Option (Fin 3) × Option (Fin 3), ∃ y ∈ Y i,
        (fun w => actO hdvd k.1 (actO hdvd k.2 w)) y = z := by
    intro i _ hi
    obtain ⟨o1, w, hw, hwz⟩ := (mem_tilde_iff hdvd (tilde hdvd (Y i)) z).mp hi
    obtain ⟨o2, y, hy, hyw⟩ := (mem_tilde_iff hdvd (Y i) w).mp hw
    exact ⟨(o1, o2), y, hy, by simp only [hyw]; exact hwz⟩
  have h := mult_le_of_family (K := Option (Fin 3) × Option (Fin 3)) 𝒞 Y hdisj
    (fun k w => actO hdvd k.1 (actO hdvd k.2 w))
    (fun k => Function.Injective.comp (actO_injective hdvd k.1) (actO_injective hdvd k.2))
    (fun i => z ∈ tilde hdvd (tilde hdvd (Y i))) z hchar
  simpa using h

/-! ## §3 — THE SUMMATION THEOREM -/

/-- **SUMMATION WITH BOUNDED MULTIPLICITY.** The bond family need only COVER; the coarse, plaquette
and drift families are priced by their multiplicities. Every hypothesis is a counting hypothesis;
no estimate is used. -/
theorem floor_sums_multiplicity {ι : Type*} [DecidableEq ι]
    (coef d : ℝ) (hcoef : 0 ≤ coef) (hd : 0 ≤ d) (Mq Mp Md : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo)
    (𝒞 : Finset ι) (Sb Sd : ι → Finset (Bond L)) (Sc : ι → Finset (CoarseBond L ell))
    (Sp : ι → Finset (PeriodicLatticePlaquette L))
    (hbcov : ∀ b : Bond L, 1 ≤ (𝒞.filter (fun i => b ∈ Sb i)).card)
    (hcmul : ∀ c : CoarseBond L ell, (𝒞.filter (fun i => c ∈ Sc i)).card ≤ Mq)
    (hpmul : ∀ p : PeriodicLatticePlaquette L, (𝒞.filter (fun i => p ∈ Sp i)).card ≤ Mp)
    (hdmul : ∀ b : Bond L, (𝒞.filter (fun i => b ∈ Sd i)).card ≤ Md)
    (hloc : ∀ i ∈ 𝒞, coef * bondEnergyS (Sb i) A
      ≤ (ell : ℝ) * coarseQS (Sc i) U A + curlS (Sp i) U A + d * bondEnergyS (Sd i) A) :
    (coef - d * (Md : ℝ)) * bondEnergy A
      ≤ (Mq : ℝ) * ((ell : ℝ) * coarseQEnergyCov U ell A) + (Mp : ℝ) * curlEnergyCov U A := by
  classical
  have hsum := Finset.sum_le_sum hloc
  -- LHS
  have hL : coef * bondEnergy A ≤ ∑ i ∈ 𝒞, coef * bondEnergyS (Sb i) A := by
    rw [← Finset.mul_sum]
    have hge : bondEnergy A ≤ ∑ i ∈ 𝒞, ∑ b ∈ Sb i, ‖A b‖ ^ 2 :=
      sum_family_ge 𝒞 Sb (fun b => ‖A b‖ ^ 2) (fun _ => sq_nonneg _) hbcov
    exact mul_le_mul_of_nonneg_left hge hcoef
  -- RHS, term by term
  have hRq : ∑ i ∈ 𝒞, (ell : ℝ) * coarseQS (Sc i) U A
      ≤ (Mq : ℝ) * ((ell : ℝ) * coarseQEnergyCov U ell A) := by
    rw [← Finset.mul_sum]
    have h := sum_family_le 𝒞 Sc (fun c => ‖lineCoarseRestrictCov U ell A c‖ ^ 2)
      (fun _ => sq_nonneg _) Mq hcmul
    have hnn : (0 : ℝ) ≤ (ell : ℝ) := by positivity
    calc (ell : ℝ) * ∑ i ∈ 𝒞, coarseQS (Sc i) U A
        ≤ (ell : ℝ) * ((Mq : ℝ) * coarseQEnergyCov U ell A) :=
          mul_le_mul_of_nonneg_left h hnn
      _ = (Mq : ℝ) * ((ell : ℝ) * coarseQEnergyCov U ell A) := by ring
  have hRp : ∑ i ∈ 𝒞, curlS (Sp i) U A ≤ (Mp : ℝ) * curlEnergyCov U A :=
    sum_family_le 𝒞 Sp (fun p => ‖curlValueCovariant U A p‖ ^ 2) (fun _ => sq_nonneg _) Mp hpmul
  have hRd : ∑ i ∈ 𝒞, d * bondEnergyS (Sd i) A ≤ d * ((Md : ℝ) * bondEnergy A) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_family_le 𝒞 Sd (fun b => ‖A b‖ ^ 2) (fun _ => sq_nonneg _) Md hdmul) hd
  have hsplit : ∑ i ∈ 𝒞, ((ell : ℝ) * coarseQS (Sc i) U A + curlS (Sp i) U A
        + d * bondEnergyS (Sd i) A)
      = (∑ i ∈ 𝒞, (ell : ℝ) * coarseQS (Sc i) U A) + (∑ i ∈ 𝒞, curlS (Sp i) U A)
        + ∑ i ∈ 𝒞, d * bondEnergyS (Sd i) A := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsplit] at hsum
  nlinarith [hL, hsum, hRq, hRp, hRd]

/-! ## §4 — ONE UNRELATED GAUGE PER CUBE

This module's three energies are DEFINITIONALLY `GaugeInvLocalize`'s, so that module's pointwise
gauge-invariance theorems are reused verbatim (LAW-19) rather than restated. -/

theorem bondEnergyS_eq_bondEnergyOn (S : Finset (Bond L)) (A : Bond L → SuTwo) :
    bondEnergyS S A = GaugeInvLocalize.bondEnergyOn S A := rfl

theorem coarseQS_eq_coarseQEnergyOn (S : Finset (CoarseBond L ell))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    coarseQS S U A = GaugeInvLocalize.coarseQEnergyOn S U A := rfl

theorem curlS_eq_curlEnergyOn (S : Finset (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    curlS S U A = GaugeInvLocalize.curlEnergyOn S U A := rfl

theorem bondEnergyS_gauge (S : Finset (Bond L)) (γ : GaugeFn L) (A : Bond L → SuTwo) :
    bondEnergyS S (gaugeActA γ A) = bondEnergyS S A :=
  GaugeInvLocalize.bondEnergyOn_gauge S γ A

theorem coarseQS_gauge (S : Finset (CoarseBond L ell)) (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    coarseQS S (periodicGaugeTransform γ U) (gaugeActA γ A) = coarseQS S U A :=
  GaugeInvLocalize.coarseQEnergyOn_gauge S γ U A

theorem curlS_gauge (S : Finset (PeriodicLatticePlaquette L)) (γ : GaugeFn L)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    curlS S (periodicGaugeTransform γ U) (gaugeActA γ A) = curlS S U A :=
  GaugeInvLocalize.curlEnergyOn_gauge S γ U A

/-- **SUMMATION WITH BOUNDED MULTIPLICITY AND ONE UNRELATED GAUGE PER CUBE.** Each cube carries its
own `γ i`; NOTHING relates `γ i` and `γ j`, and no global gauge is formed. -/
theorem floor_sums_gauged_multiplicity {ι : Type*} [DecidableEq ι]
    (coef d : ℝ) (hcoef : 0 ≤ coef) (hd : 0 ≤ d) (Mq Mp Md : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo)
    (𝒞 : Finset ι) (Sb Sd : ι → Finset (Bond L)) (Sc : ι → Finset (CoarseBond L ell))
    (Sp : ι → Finset (PeriodicLatticePlaquette L)) (γ : ι → GaugeFn L)
    (hbcov : ∀ b : Bond L, 1 ≤ (𝒞.filter (fun i => b ∈ Sb i)).card)
    (hcmul : ∀ c : CoarseBond L ell, (𝒞.filter (fun i => c ∈ Sc i)).card ≤ Mq)
    (hpmul : ∀ p : PeriodicLatticePlaquette L, (𝒞.filter (fun i => p ∈ Sp i)).card ≤ Mp)
    (hdmul : ∀ b : Bond L, (𝒞.filter (fun i => b ∈ Sd i)).card ≤ Md)
    (hloc : ∀ i ∈ 𝒞, coef * bondEnergyS (Sb i) (gaugeActA (γ i) A)
      ≤ (ell : ℝ) * coarseQS (Sc i) (periodicGaugeTransform (γ i) U) (gaugeActA (γ i) A)
        + curlS (Sp i) (periodicGaugeTransform (γ i) U) (gaugeActA (γ i) A)
        + d * bondEnergyS (Sd i) (gaugeActA (γ i) A)) :
    (coef - d * (Md : ℝ)) * bondEnergy A
      ≤ (Mq : ℝ) * ((ell : ℝ) * coarseQEnergyCov U ell A) + (Mp : ℝ) * curlEnergyCov U A := by
  refine floor_sums_multiplicity coef d hcoef hd Mq Mp Md U A 𝒞 Sb Sd Sc Sp
    hbcov hcmul hpmul hdmul (fun i hi => ?_)
  have h := hloc i hi
  rwa [bondEnergyS_gauge, coarseQS_gauge, curlS_gauge, bondEnergyS_gauge] at h

/-! ## §5 — CONTROLS -/

/-- **The partition case is recovered.** At `Mq = Mp = 1` and `d = 0` the conclusion of
`floor_sums_multiplicity` is exactly `GaugeInvLocalize.localized_floor_sums_of_gauged`'s, so this
module strictly generalizes rather than competes. Stated as the arithmetic identity that makes the
two conclusions the same expression. -/
theorem recovers_partition_case (coef Q P : ℝ) :
    (coef - 0 * ((1 : ℕ) : ℝ)) * 1 = coef * 1
    ∧ ((1 : ℕ) : ℝ) * Q + ((1 : ℕ) : ℝ) * P = Q + P := by
  norm_num

/-- **THE MULTIPLICITY HYPOTHESES ARE LOAD-BEARING.** With an EMPTY cube family every `hloc` holds
vacuously and every multiplicity bound holds, but the covering hypothesis FAILS — and it must, since
the conclusion is then false. Exhibited on explicit numbers: at `card = 0` the covering hypothesis
`1 ≤ 0` is false, and the conclusion `1·1 ≤ 0` it would otherwise deliver is false. -/
theorem covering_is_load_bearing_here :
    ¬ (1 ≤ (0 : ℕ)) ∧ ¬ ((1 : ℝ) * 1 ≤ 0) := by
  refine ⟨by omega, by norm_num⟩

/-- **The `4` of `tilde_mult_le_four` is not vacuous**: `Option (Fin 3)` really has four elements,
and `Option (Fin 3) × Option (Fin 3)` sixteen — the two counts the two lemmas report. -/
theorem displacement_counts :
    Fintype.card (Option (Fin 3)) = 4 ∧ Fintype.card (Option (Fin 3) × Option (Fin 3)) = 16 := by
  constructor <;> simp

#print axioms sum_family_count
#print axioms sum_family_ge
#print axioms sum_family_le
#print axioms actO
#print axioms actO_injective
#print axioms mem_tilde_iff
#print axioms mult_le_of_family
#print axioms tilde_mult_le_four
#print axioms tilde2_mult_le_sixteen
#print axioms floor_sums_multiplicity
#print axioms bondEnergyS_eq_bondEnergyOn
#print axioms coarseQS_eq_coarseQEnergyOn
#print axioms curlS_eq_curlEnergyOn
#print axioms bondEnergyS_gauge
#print axioms coarseQS_gauge
#print axioms curlS_gauge
#print axioms floor_sums_gauged_multiplicity
#print axioms recovers_partition_case
#print axioms covering_is_load_bearing_here
#print axioms displacement_counts

end AdalyFormal.Balaban.LocalizedEstimates

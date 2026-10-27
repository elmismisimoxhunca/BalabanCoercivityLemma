/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import LocDrift
import CovLemma24

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# THE LOCALIZED COVARIANT CMP96 LEMMA 2.4 — the per-cube floor.

`CovLemma24.covariant_lemma24` is the global covariant floor. This module runs its EXACT argument
— `transfer_abstract` fed by the flat leg and the two drifts — with every sum restricted to one
cube, using `LocGeom.local_lemma24_flat` for the flat leg and `LocDrift`'s two localized drifts.

## THE RESULT

`local_covariant_lemma24`, for every `ell ≥ 2`, compatible torus, EVERY background `U`, every
`(2.121)`-admissible `𝔰𝔲(2)` field `A`, every cube `Y`, and every `α` bounding the holonomy
deviations on the cube's own bonds:

>  `(1/360)·ell⁻⁵ · ∑_{b ∈ bondsOn Y} ‖A b‖²
>       ≤ ell·∑_{c ∈ coarseOn Y} ‖(Q(U)A)(c)‖² + ∑_{p ∈ plaqsOn (tilde Y)} ‖(D_U A)(p)‖²
>         + (64·α₁² + 32·α²)·∑_{b ∈ bondsOn (tilde Y)} ‖A b‖²`

with `α₁ = frobSupBond U` (global) and `α` local. **Every constant is the global theorem's**:
`64 = ell·(64/ell)` from `RegularUQChain.coarseDriftEnergy_le`, `32 = (4√2)²` from
`RegularUPerturbation.norm_curlDrift_L2_le`, and `64 + 32 = 96` is `covariant_lemma24`'s own
coefficient. Nothing is refitted.

At `Y = univ` — where `tilde univ = univ` and every localized energy is its global counterpart —
this IS `covariant_lemma24` (`local_covariant_lemma24_univ`), so the localization is a genuine
strengthening.

## THE ONE THING THAT IS NOT LOCAL, NAMED AT ITS DEFINING DECLARATION

`α₁ = frobSupBond U` is the GLOBAL sup. It enters through exactly one place —
`LocDrift.local_coarseDrift_le`, i.e. `RegularUQChain.coarseDriftEnergy_le` — and the reason is
stated precisely in §4: `LineIntegralCovariant.lineCoarseRestrictCov` reads `U` through
`Q1Real.periodicPathHolonomy U c₋ (Q1Real.transportPath c₋ x μ i)`, and this lane does not prove
that the bonds that holonomy visits lie in `bondsOn (tilde Y)`. **That containment is TRUE** — the
sites `Q1Real.GammaPath` visits stay inside the block `B(c₋)` (all its steps are FORWARD and each
coordinate travels from `y_ρ` to `x_ρ < y_ρ + ell`) and the trailing `straightSegment` advances at
most `ell − 1` further steps, which is exactly `LocDrift.pathSite_mem_block_or_next`. What is
missing is only the Lean statement that `periodicPathHolonomy` depends on `U` solely through the
bonds it visits. It is named `holonomy_locality` in §4 with its exact type, is NOT assumed anywhere
in this file, and NOTHING in this module is stated conditionally on it.
-/

namespace AdalyFormal.Balaban.LocalizedEstimates

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.CoarseCurl
open GeomScratch
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCov_trivialU)
open AdalyFormal.Balaban.RegularUPerturbation
open AdalyFormal.Balaban.RegularUQChain
open AdalyFormal.Balaban.SuTwoGeomU1
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovU1Reduction
open AdalyFormal.Balaban.CovariantLemma24

variable {L : PeriodicLatticeExtent} {ell : ℕ}

/-! ## §1 — THE THREE LOCALIZED `𝔰𝔲(2)` ENERGIES -/

/-- `∑_{b ∈ S} ‖A b‖²`. -/
noncomputable def bondEnergyS (S : Finset (Bond L)) (A : Bond L → SuTwo) : ℝ :=
  ∑ b ∈ S, ‖A b‖ ^ 2

/-- `∑_{c ∈ S} ‖(Q(U)A)(c)‖²`. -/
noncomputable def coarseQS (S : Finset (CoarseBond L ell))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ c ∈ S, ‖lineCoarseRestrictCov U ell A c‖ ^ 2

/-- `∑_{p ∈ S} ‖(D_U A)(p)‖²`. -/
noncomputable def curlS (S : Finset (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) : ℝ :=
  ∑ p ∈ S, ‖curlValueCovariant U A p‖ ^ 2

theorem bondEnergyS_nonneg (S : Finset (Bond L)) (A : Bond L → SuTwo) : 0 ≤ bondEnergyS S A :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem coarseQS_nonneg (S : Finset (CoarseBond L ell))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    0 ≤ coarseQS S U A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem curlS_nonneg (S : Finset (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (A : Bond L → SuTwo) :
    0 ≤ curlS S U A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem bondEnergyS_mono {S T : Finset (Bond L)} (h : S ⊆ T) (A : Bond L → SuTwo) :
    bondEnergyS S A ≤ bondEnergyS T A :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

/-! ### The `univ` pins — the localized energies ARE the global ones there. -/

theorem bondEnergyS_univ (A : Bond L → SuTwo) :
    bondEnergyS (Finset.univ : Finset (Bond L)) A = bondEnergy A := rfl

theorem coarseQS_univ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    coarseQS (Finset.univ : Finset (CoarseBond L ell)) U A = coarseQEnergyCov U ell A := rfl

theorem curlS_univ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) :
    curlS (Finset.univ : Finset (PeriodicLatticePlaquette L)) U A = curlEnergyCov U A := rfl

/-! ## §2 — THE FIBRE DECOMPOSITION, RESTRICTED

`CovLemma24` §2's three decompositions with `Finset.univ` replaced by an arbitrary index set. Every
proof is `Finset.sum_comm` plus the SAME pointwise identity, so nothing new is assumed: the
restriction is free because the decomposition is POINTWISE in the index. -/

theorem bondEnergyS_eq_sum_comp (S : Finset (Bond L)) (A : Bond L → SuTwo) :
    bondEnergyS S A = ∑ i : Fin 3, bondEnergyR S (suComp i A) := by
  unfold bondEnergyS bondEnergyR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suComp_apply, sq])

theorem curlS_trivialU_eq_sum (S : Finset (PeriodicLatticePlaquette L)) (A : Bond L → SuTwo) :
    curlS S (trivialU L) A = ∑ i : Fin 3, curlEnergyR S (suComp i A) := by
  unfold curlS curlEnergyR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [curlValueCovariant_trivialU_eq, normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suCoordLM_flatCurlValue, sq])

theorem coarseQS_trivialU_eq_sum (S : Finset (CoarseBond L ell)) (A : Bond L → SuTwo) :
    coarseQS S (trivialU L) A = ∑ i : Fin 3, coarseQEnergyR S (suComp i A) := by
  unfold coarseQS coarseQEnergyR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [lineCoarseRestrictCov_trivialU, normSq_eq_hsInner, hsInner_eq_sum_coord]
  exact Finset.sum_congr rfl (fun i _ => by rw [suCoordLM_lineCoarseRestrictSuTwo, sq])

/-! ## §3 — THE LOCALIZED FLAT `𝔰𝔲(2)` LEG -/

/-- **The localized flat leg on the `𝔰𝔲(2)` fibre.** `LocGeom.local_lemma24_flat` applied to each of
the three real components, exactly as `CovLemma24.suTwo_lemma24_flat` does globally. -/
theorem local_suTwo_flat (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) (Y : Finset (CSite L ell)) :
    (1 / 180) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A
      ≤ (ell : ℝ) * coarseQS (coarseOn Y) (trivialU L) A
        + curlS (plaqsOn (tilde hdvd Y)) (trivialU L) A := by
  rw [bondEnergyS_eq_sum_comp, coarseQS_trivialU_eq_sum, curlS_trivialU_eq_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact local_lemma24_flat hell2 hstrict hdvd (suComp i A)
    (suComp_mem_admissible ell i A hadm) Y

/-! ## §4 — THE TWO DRIFTS AS THE TRANSFER CONSUMES THEM -/

/-- The flat coarse energy on the cube is at most twice the covariant one plus twice the drift. -/
theorem local_coarseQ_flat_le (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (Y : Finset (CSite L ell)) :
    coarseQS (coarseOn Y) (trivialU L) A
      ≤ 2 * coarseQS (coarseOn Y) U A
        + 2 * ((64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A) := by
  have hpt : coarseQS (coarseOn Y) (trivialU L) A
      ≤ 2 * coarseQS (coarseOn Y) U A
        + 2 * ∑ c ∈ coarseOn Y,
            ‖lineCoarseRestrictCov (trivialU L) ell A c - lineCoarseRestrictCov U ell A c‖ ^ 2 := by
    unfold coarseQS
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ =>
      sq_le_two_add_two (lineCoarseRestrictCov (trivialU L) ell A c)
        (lineCoarseRestrictCov U ell A c))
  have hd := local_coarseDrift_le hell hdvd U A Y
  unfold bondEnergyS
  linarith [hpt, hd]

/-- The flat curl energy on the enlarged cube is at most twice the covariant one plus twice the
curl drift — and the curl drift's `α` is the cube's OWN. -/
theorem local_curl_flat_le (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (α : ℝ) (hα0 : 0 ≤ α) (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn (tilde hdvd Y),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    curlS (plaqsOn (tilde hdvd Y)) (trivialU L) A
      ≤ 2 * curlS (plaqsOn (tilde hdvd Y)) U A
        + 2 * (32 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A) := by
  have hpt : curlS (plaqsOn (tilde hdvd Y)) (trivialU L) A
      ≤ 2 * curlS (plaqsOn (tilde hdvd Y)) U A
        + 2 * ∑ p ∈ plaqsOn (tilde hdvd Y), ‖curlDrift U A p‖ ^ 2 := by
    unfold curlS
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun p _ => ?_)
    have hd : curlValueCovariant (trivialU L) A p - curlValueCovariant U A p
        = - curlDrift U A p := by
      have h : curlDrift U A p = curlValueCovariant U A p - curlValueCovariant (trivialU L) A p :=
        rfl
      rw [h]; abel
    have h := sq_le_two_add_two (curlValueCovariant (trivialU L) A p) (curlValueCovariant U A p)
    rwa [hd, norm_neg] at h
  have hd := local_curlDrift_le hell2 hdvd U A α hα0 (tilde hdvd Y) hα
  unfold bondEnergyS
  linarith [hpt, hd]

/-! ## §5 — THE LOCALIZED COVARIANT LEMMA 2.4 -/

/-- **THE LOCALIZED COVARIANT CMP96 LEMMA 2.4.**

Every constant is `covariant_lemma24`'s. The floor is read on the cube `Y`; the covariant curl and
the two drifts are read on the enlarged cube. -/
theorem local_covariant_lemma24 (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) (α : ℝ) (hα0 : 0 ≤ α)
    (Y : Finset (CSite L ell))
    (hα : ∀ b ∈ bondsOn (tilde hdvd Y),
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A
      ≤ (ell : ℝ) * coarseQS (coarseOn Y) U A + curlS (plaqsOn (tilde hdvd Y)) U A
        + (64 * frobSupBond U ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A
           + 32 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A) := by
  have hell : 0 < ell := by omega
  have ht : (0 : ℝ) ≤ (ell : ℝ) := by positivity
  have hne : (ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have hfloor := local_suTwo_flat hell2 hstrict hdvd A hadm Y
  have hQ := local_coarseQ_flat_le hell hdvd U A Y
  have hP := local_curl_flat_le hell2 hdvd U A α hα0 Y hα
  have hmain := transfer_abstract (t := (ell : ℝ)) (gam := (1 / 180) * (1 / (ell : ℝ) ^ 5))
    (N := bondEnergyS (bondsOn Y) A)
    (Qf := coarseQS (coarseOn Y) (trivialU L) A)
    (Pf := curlS (plaqsOn (tilde hdvd Y)) (trivialU L) A)
    (Qc := coarseQS (coarseOn Y) U A)
    (Pc := curlS (plaqsOn (tilde hdvd Y)) U A)
    (dQ := (64 / (ell : ℝ)) * frobSupBond U ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A)
    (dP := 32 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A)
    ht hfloor hQ hP
  have hid : (ell : ℝ) * ((64 / (ell : ℝ)) * frobSupBond U ^ 2
        * bondEnergyS (bondsOn (tilde hdvd Y)) A)
      = 64 * frobSupBond U ^ 2 * bondEnergyS (bondsOn (tilde hdvd Y)) A := by
    field_simp
  have hgam : ((1 / 180) * (1 / (ell : ℝ) ^ 5)) / 2 * bondEnergyS (bondsOn Y) A
      = (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A := by ring
  rw [hid, hgam] at hmain
  linarith [hmain]

/-- **THE PER-CUBE FLOOR IN ONE SMALLNESS PARAMETER.** If `α` also dominates the global sup, the two
drift coefficients merge into `covariant_lemma24`'s own `96 = 64 + 32`, and the statement is the
global one with the index sets localized:

`(1/360)·ell⁻⁵·E(Y) − 96·α²·E(tilde (tilde Y)) ≤ ell·Q(Y) + P(tilde Y)`. -/
theorem local_covariant_lemma24_uniform (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) (α : ℝ) (hα0 : 0 ≤ α)
    (hsup : frobSupBond U ≤ α) (Y : Finset (CSite L ell)) :
    (1 / 360) * (1 / (ell : ℝ) ^ 5) * bondEnergyS (bondsOn Y) A
        - 96 * α ^ 2 * bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A
      ≤ (ell : ℝ) * coarseQS (coarseOn Y) U A + curlS (plaqsOn (tilde hdvd Y)) U A := by
  have hαall : ∀ b : Bond L,
      RMapLipschitz.frobNorm ((U b : Matrix (Fin 2) (Fin 2) ℂ) - 1) ≤ α :=
    fun b => le_trans (frobNorm_le_frobSupBond U b) hsup
  have hmain := local_covariant_lemma24 hell2 hstrict hdvd U A hadm α hα0 Y
    (fun b _ => hαall b)
  have hsq : frobSupBond U ^ 2 ≤ α ^ 2 := by
    have h0 := frobSupBond_nonneg U
    nlinarith [hsup, h0]
  have hE : bondEnergyS (bondsOn (tilde hdvd Y)) A
      ≤ bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A :=
    bondEnergyS_mono (Finset.biUnion_subset_biUnion_of_subset_left _
      (subset_tilde hdvd (tilde hdvd Y))) A
  have hEnn : 0 ≤ bondEnergyS (bondsOn (tilde hdvd (tilde hdvd Y))) A := bondEnergyS_nonneg _ _
  nlinarith [hmain, hsq, hE, hEnn, bondEnergyS_nonneg (bondsOn (tilde hdvd Y)) A]

/-- **THE `Y = univ` PIN.** At the full cube the localized covariant lemma IS
`CovLemma24.covariant_lemma24`: same constant `96`, same `α₁ = frobSupBond U`, same three energies.
So nothing has been weakened, rescaled or renamed in the localization. -/
theorem local_covariant_lemma24_univ (hell2 : 2 ≤ ell)
    (hstrict : ∀ ν : Fin 3, ell < L ν + 1) (hdvd : ∀ ν : Fin 3, ell ∣ (L ν + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (A : Bond L → SuTwo) (hadm : SuAdmissible L ell A) :
    ((1 / 360) * (1 / (ell : ℝ) ^ 5) - 96 * frobSupBond U ^ 2) * bondEnergy A
      ≤ (ell : ℝ) * coarseQEnergyCov U ell A + curlEnergyCov U A := by
  have hell : 0 < ell := by omega
  have h := local_covariant_lemma24_uniform hell2 hstrict hdvd U A hadm (frobSupBond U)
    (frobSupBond_nonneg U) le_rfl (Finset.univ : Finset (CSite L ell))
  rw [tilde_univ hdvd, tilde_univ hdvd, bondsOn_univ hell hdvd, plaqsOn_univ hell hdvd,
    coarseOn_univ] at h
  rw [bondEnergyS_univ, coarseQS_univ, curlS_univ] at h
  nlinarith [h]

/-! ## §6 — THE ONE MISSING LOCALITY, NAMED AT ITS TYPE (NOT ASSUMED)

Nothing below is used by anything above. `holonomy_locality_statement` is the EXACT proposition
whose proof would replace `frobSupBond U` by the cube's own `α` in `local_coarseDrift_le`, and
hence in `local_covariant_lemma24`. It is stated as a `Prop`-valued definition — a target, NOT a
postulate and NOT a hypothesis of any theorem in this file. -/

/-- **THE MISSING LOCALITY, as a target.** `Q1Real.periodicPathHolonomy U z steps` should depend on
`U` only through the bonds the walk `steps` visits from `z`. Stated here in the only form this
chain needs: for the coarse-graining transport path of a coarse bond of the cube `Y`, cutting `U`
to `bondsOn (tilde Y)` must not change the holonomy.

Were this proved, `LocDrift.lineCoarseRestrictCov_cutA` would extend from `A` to `U`, and
`local_coarseDrift_le`'s `frobSupBond U` would become `α` by the same `frobSupBond_linkCut_le` step
the curl drift already uses. -/
def holonomy_locality_statement (L : PeriodicLatticeExtent) (ell : ℕ)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) : Prop :=
  ∀ (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Y : Finset (CSite L ell)) (c : CoarseBond L ell), c ∈ coarseOn Y →
    ∀ x ∈ blockOf c.1.1 ell, ∀ i ∈ Finset.range ell,
      periodicPathHolonomy U c.1.1
          (AdalyFormal.Balaban.Q1Real.transportPath c.1.1 x c.2 i)
        = periodicPathHolonomy (linkCut (bondsOn (tilde hdvd Y)) U)
            c.1.1 (AdalyFormal.Balaban.Q1Real.transportPath c.1.1 x c.2 i)

#print axioms bondEnergyS
#print axioms bondEnergyS_nonneg
#print axioms coarseQS_nonneg
#print axioms curlS_nonneg
#print axioms bondEnergyS_mono
#print axioms coarseQS
#print axioms curlS
#print axioms bondEnergyS_univ
#print axioms coarseQS_univ
#print axioms curlS_univ
#print axioms bondEnergyS_eq_sum_comp
#print axioms curlS_trivialU_eq_sum
#print axioms coarseQS_trivialU_eq_sum
#print axioms local_suTwo_flat
#print axioms local_coarseQ_flat_le
#print axioms local_curl_flat_le
#print axioms local_covariant_lemma24
#print axioms local_covariant_lemma24_uniform
#print axioms local_covariant_lemma24_univ
#print axioms holonomy_locality_statement

end AdalyFormal.Balaban.LocalizedEstimates

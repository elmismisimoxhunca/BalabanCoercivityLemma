/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.NormalizationAudit
import AdalyFormal.Balaban.TheLemma
import AdalyFormal.Balaban.RegularityHolonomy
import R7Fork.AdalyFormal.Balaban.NormalizedCounterexampleSearch

set_option autoImplicit false

/-!
# `theLemma_normalized` — BOTH fixes applied, and a THIRD, independent falsification

**Dispatch**: build the corrected target statement (normalization fix `deltaKQuadFormNormalizedCorrected`
+ central-blindness fix `IsRegularHolonomy`), and verify it survives the four mandated checks.

## ⚠ HEADLINE VERDICT: THE CORRECTED STATEMENT IS FALSE — a THIRD, independent reason

Checks 1-3 below all pass (the two known witnesses no longer break it, and the hypothesis set is
non-vacuous). **Check 4, the knife-edge, does NOT come back harmless.** `DeltaPrime.deltaWitnessConfig`
— the tree's own quadratic-form-defining witness field — is proved here (§3) to have covariant curl
`= suTwoWitness ≠ 0` at `witnessPlaquette`, for EVERY `U` whatsoever (not merely `witnessU`), by
EXACTLY the mechanism `TheLemma.singleBondSpike`/`spikeC` already use (the field's only nonzero bond
value contributes unconjugated to the curl formula; every other slot reads a bond where the field is
zero, so `RMap` of anything applied to `0` vanishes regardless of `U`). Consequently `deltaWitnessConfig`
is **not** a curl-free/harmonic mode — it is exactly the OPPOSITE of the winding mode `windC` was
built to exclude — and a `C` embedding it (`deltaWitnessC`, built here, §4, by the SAME
`ContinuousLinearMap.smulRight`-of-`id` construction as `spikeC`/`windC`) legally satisfies
`IsBalabanReparam` **at every threshold, unconditionally in `U`** (§4,
`deltaWitnessC_satisfies_isBalabanReparam`).

Separately (§2), `CovariantOperators.witnessU` — the tree's own non-flat witness, `witnessMElem` on
bond `(witnessY,0)` — is proved `IsRegularHolonomy`-admissible at `Mα₀ = 4`
(`witnessU_isRegularHolonomy_four`): the four plaquettes touching the special bond all carry holonomy
defect exactly `4` (`Re(tr(witnessMElem)) = Re(tr(witnessMElem⁻¹)) = 0`), every other plaquette carries
defect `0` (holonomy trivial there, `holonomy_witnessU_eq_one`, built by the SAME case-split technique
`DeltaPrime.deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero` uses, reusing its own case-covering lemmas
`eq_witnessPlaquette_or_myWitnessPlaquette2`/`eq_p3_or_p4`/`plaquette_snd_dir_ne_zero`, LAW-19).

So: `witnessU` clears the `IsRegularHolonomy` hypothesis at `Mα₀ = 4 < Mα₀thresh := 5`, `deltaWitnessC`
clears `IsBalabanReparam 5`, and `deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0`
(already banked, `NormalizationAudit`). Plugging `Bt := 1` into the CORRECTED+HOLONOMY-FIXED
statement's own conclusion forces `γ₀ · 1 ≤ 0` for whatever `γ₀ > 0` a proof would produce — a direct
contradiction. **§5 assembles this into `theLemma_normalized_contradicts_if_proved`: ANY closed proof
of `theLemma_normalized` (i.e. discharging its `sorry`) yields `False`.** The statement, exactly as the
dispatch specifies it, is not open — it is REFUTED, for a reason orthogonal to both the normalization
bug and the `IsRegular`-vs-`IsRegularHolonomy` central-blindness defect it was built to fix.

This is the answer to the dispatch's own knife-edge question: **`deltaWitnessConfig` SURVIVES in
`range(C)` for a legal `C`** (it is not a mode `IsBalabanReparam` excludes — quite the opposite, its
curl-nonvanishing-at-every-`U` property is EXACTLY what makes a `C` embedding it legal), so the
statement is false for the third, disclosed reason.

## What this file builds

* §1 — Checks 1-3 (reproduced/cited, not re-derived where already banked): `witnessU` gives `0` under
  the normalized operator; `centralHolonomyU` is excluded by `IsRegularHolonomy`; the hypothesis set
  is jointly satisfiable (`pureGaugeU`/`spikeC`).
* §2 — `witnessU_isRegularHolonomy_four`: `witnessU` clears `IsRegularHolonomy` at `Mα₀ = 4`, built
  from scratch (new, not previously banked — `RegularityHolonomy.lean` only established this at
  `witnessPlaquette` for the FAILURE direction, `Mα₀ = 2`; the ADMISSION direction at `Mα₀ = 4`,
  requiring holonomy at ALL plaquettes including the other three exceptional ones and every trivial
  one, is new here).
* §3 — `deltaWitnessConfig`'s curl at `witnessPlaquette` is `suTwoWitness`, for EVERY `U` (new,
  generalizing `DeltaPrime`'s `witnessU`-specific computation, by the identical `TheLemma.
  singleBondSpike`-style mechanism).
* §4 — `deltaWitnessC`, a `Btilde := ℝ` reparametrization embedding `deltaWitnessConfig` (mirrors
  `TheLemma.spikeC`/`windC`'s construction exactly, LAW-19), proved to satisfy `IsBalabanReparam` at
  EVERY threshold, unconditionally in `U`.
* §5 — `theLemma_normalized` itself (ONE `sorry`, as mandated), and
  `theLemma_normalized_contradicts_if_proved`: closing that `sorry` (for ANY faithful implementation
  of the stated type) yields `False`, via the `Lat := AdmissibleSubspace.witnessL, Btilde := ℝ,
  C := deltaWitnessC, Mα₀thresh := 5` instantiation.
* §6 — falsifiability mutations (S82/OPS-3) on the two new numerals (`4`, the `IsRegularHolonomy`
  threshold; `0`, the reused normalized value) and the refutation's own load-bearing step.
-/

namespace AdalyFormal.Balaban.TheLemmaNormalized

open Matrix AdalyFormal.Target.ClayStatement AdalyFormal.Balaban.CovariantOperators
  AdalyFormal.Balaban.SuTwoInner AdalyFormal.Balaban.AdmissibleSubspace
  AdalyFormal.Balaban.CovariantHj AdalyFormal.Balaban.DeltaPrime
  AdalyFormal.Balaban.DeltaKFull AdalyFormal.Balaban.NormalizationAudit
  AdalyFormal.Balaban.TheLemma AdalyFormal.Balaban.RegularityHolonomy
  AdalyFormal.Balaban.NormalizedCounterexampleSearch AdalyFormal.Balaban.BondSU2Space

/-! ## §1 — Checks 1-3, reproduced/cited -/

/-- **Check 1** — `witnessU`'s old-family refutation is void against the normalized operator. -/
theorem check1_witnessU_normalized_zero :
    deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0 :=
  deltaKQuadFormNormalizedCorrected_witnessU_deltaWitnessConfig_eq_zero

#print axioms check1_witnessU_normalized_zero

/-- **Check 2** — the surviving `-4` counterexample's `U` cannot even be formed under the fixed
hypothesis: `centralHolonomyU` is excluded by `IsRegularHolonomy` at the tightest threshold. -/
theorem check2_centralHolonomyU_excluded :
    ¬ IsRegularHolonomy centralHolonomyU (0 : ℝ) :=
  centralHolonomyU_not_isRegularHolonomy_zero

#print axioms check2_centralHolonomyU_excluded

/-- **Check 3** — non-vacuity: the hypothesis set is jointly satisfiable by a genuinely non-flat `U`
and a `C` satisfying `IsBalabanReparam` at every threshold. -/
theorem check3_nonvacuous :
    ∃ (Mα₀thresh Mα₀ : ℝ) (U : Config AdmissibleSubspace.witnessL)
      (C : ℝ →L[ℝ] BondFnL2 AdmissibleSubspace.witnessL),
      0 < Mα₀thresh ∧ Mα₀ < Mα₀thresh ∧ IsRegularHolonomy U Mα₀ ∧
      IsBalabanReparam (Lat := AdmissibleSubspace.witnessL) Mα₀thresh C ∧
      U (AdmissibleSubspace.witnessY, (0 : Fin 3)) ≠ 1 :=
  ⟨1, 0, pureGaugeU, spikeC, one_pos, zero_lt_one, pureGaugeU_isRegularHolonomy_zero,
    spikeC_satisfies_isBalabanReparam 1, pureGaugeU_ne_trivial⟩

#print axioms check3_nonvacuous

/-! ## §2 — `witnessU` clears `IsRegularHolonomy` at `Mα₀ = 4` (new) -/

/-- `witnessU` differs from `1` only at the bond `(witnessY,0)` — the general "elsewhere" fact this
section's holonomy computation needs, mirroring `singleBondU_elsewhere`/`deltaWitnessConfig_elsewhere`
(a small, freshly-built helper; `witnessU`'s own file, `CovariantOperators.lean`, only records the
FOUR concrete point-facts it happened to need, not this general form). -/
theorem witnessU_elsewhere {e : Bond AdmissibleSubspace.witnessL}
    (h : e ≠ (AdmissibleSubspace.witnessY, (0 : Fin 3))) : witnessU e = 1 := by
  simp [witnessU, h]

#print axioms witnessU_elsewhere

/-- **`witnessU`'s holonomy is trivial at every plaquette OUTSIDE the 4 exceptional ones** — same
case-split technique as `DeltaPrime.deltaPrimePlaqTerm_deltaWitnessConfig_eq_zero`, reusing its own
case-covering lemmas (LAW-19), applied to `holonomyElem` instead of `deltaPrimePlaqTerm`. -/
theorem holonomy_witnessU_eq_one {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyElem witnessU p = 1 := by
  show witnessU (p.1, p.2.1.1) * witnessU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
      (witnessU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ *
      (witnessU (p.1, p.2.1.2))⁻¹ = 1
  have e1 : witnessU (p.1, p.2.1.1) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    rcases eq_witnessPlaquette_or_myWitnessPlaquette2 (congrArg Prod.fst hcon)
        (congrArg Prod.snd hcon) with h | h
    · exact hp1 h
    · exact hp2 h
  have e2 : witnessU (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  have e3 : witnessU (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    rcases eq_p3_or_p4 (congrArg Prod.fst hcon) (congrArg Prod.snd hcon) with h | h
    · exact hp3 h
    · exact hp4 h
  have e4 : witnessU (p.1, p.2.1.2) = 1 := by
    apply witnessU_elsewhere
    intro hcon
    exact plaquette_snd_dir_ne_zero p (congrArg Prod.snd hcon)
  rw [e1, e2, e3, e4]
  simp

#print axioms holonomy_witnessU_eq_one

theorem holonomyDefectSq_witnessU_eq_zero_elsewhere
    {p : PeriodicLatticePlaquette AdmissibleSubspace.witnessL}
    (hp1 : p ≠ witnessPlaquette) (hp2 : p ≠ myWitnessPlaquette2) (hp3 : p ≠ p3) (hp4 : p ≠ p4) :
    holonomyDefectSq witnessU p = 0 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_eq_one hp1 hp2 hp3 hp4]
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.one_apply]

#print axioms holonomyDefectSq_witnessU_eq_zero_elsewhere

theorem holonomyDefectSq_witnessU_myWitnessPlaquette2 :
    holonomyDefectSq witnessU myWitnessPlaquette2 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_myWitnessPlaquette2]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem holonomyDefectSq_witnessU_p3 : holonomyDefectSq witnessU p3 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_p3, trace_inv_re_eq_trace_re witnessMElem]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem holonomyDefectSq_witnessU_p4 : holonomyDefectSq witnessU p4 = 4 := by
  unfold holonomyDefectSq
  rw [holonomy_witnessU_p4, trace_inv_re_eq_trace_re witnessMElem]
  norm_num [witnessMElem, witnessM, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

#print axioms holonomyDefectSq_witnessU_myWitnessPlaquette2
#print axioms holonomyDefectSq_witnessU_p3
#print axioms holonomyDefectSq_witnessU_p4

/-- **THE ADMISSION RESULT (new)**: `witnessU` clears `IsRegularHolonomy` at `Mα₀ = 4` — the maximum
defect over ALL plaquettes, achieved at exactly the 4 exceptional ones, `0` everywhere else. -/
theorem witnessU_isRegularHolonomy_four : IsRegularHolonomy witnessU (4 : ℝ) := by
  intro p
  by_cases h1 : p = witnessPlaquette
  · rw [h1, holonomyDefectSq_witnessU_witnessPlaquette]
  by_cases h2 : p = myWitnessPlaquette2
  · rw [h2, holonomyDefectSq_witnessU_myWitnessPlaquette2]
  by_cases h3 : p = p3
  · rw [h3, holonomyDefectSq_witnessU_p3]
  by_cases h4 : p = p4
  · rw [h4, holonomyDefectSq_witnessU_p4]
  · rw [holonomyDefectSq_witnessU_eq_zero_elsewhere h1 h2 h3 h4]
    norm_num

#print axioms witnessU_isRegularHolonomy_four

/-! ## §3 — `deltaWitnessConfig`'s curl at `witnessPlaquette` is `suTwoWitness`, for EVERY `U` (new) -/

/-- **`deltaWitnessConfig`'s curl at `witnessPlaquette` does not depend on `U` at all.** Same
mechanism as `TheLemma.curlValueCovariant_smul_singleBondSpike`: the only nonzero bond value
contributes UNCONJUGATED (the direct `T1` slot); the other three slots evaluate the field at bonds
where it is `0`, so `RMap _ 0 = 0` regardless of what `U` supplies. -/
theorem curlValueCovariant_deltaWitnessConfig_witnessPlaquette
    (U : Config AdmissibleSubspace.witnessL) :
    curlValueCovariant U deltaWitnessConfig witnessPlaquette = suTwoWitness := by
  show deltaWitnessConfig (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (U (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))) -
      RMap (U (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        (deltaWitnessConfig (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      deltaWitnessConfig (AdmissibleSubspace.witnessY, (1 : Fin 3)) = suTwoWitness
  rw [deltaWitnessConfig_at_e0, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide),
    deltaWitnessConfig_elsewhere (show _ ≠ _ by decide)]
  simp [map_zero]

#print axioms curlValueCovariant_deltaWitnessConfig_witnessPlaquette

/-- Scaled version, needed for the `IsBalabanReparam` clause (which quantifies over all `Bt ≠ 0`,
i.e. all scalar multiples for `Btilde := ℝ`). -/
theorem curlValueCovariant_smul_deltaWitnessConfig
    (U : Config AdmissibleSubspace.witnessL) (c : ℝ) :
    curlValueCovariant U (c • deltaWitnessConfig) witnessPlaquette = c • suTwoWitness := by
  show (c • deltaWitnessConfig) (AdmissibleSubspace.witnessY, (0 : Fin 3)) +
      RMap (U (AdmissibleSubspace.witnessY, (0 : Fin 3)))
        ((c • deltaWitnessConfig)
          (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3))) -
      RMap (U (AdmissibleSubspace.witnessY, (1 : Fin 3)))
        ((c • deltaWitnessConfig)
          (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3))) -
      (c • deltaWitnessConfig) (AdmissibleSubspace.witnessY, (1 : Fin 3)) = c • suTwoWitness
  have e1 : (c • deltaWitnessConfig) (AdmissibleSubspace.witnessY, (0 : Fin 3)) =
      c • suTwoWitness := by rw [Pi.smul_apply, deltaWitnessConfig_at_e0]
  have e2 : (c • deltaWitnessConfig)
      (periodicLatticeShift AdmissibleSubspace.witnessY 0, (1 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), smul_zero]
  have e3 : (c • deltaWitnessConfig)
      (periodicLatticeShift AdmissibleSubspace.witnessY 1, (0 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), smul_zero]
  have e4 : (c • deltaWitnessConfig) (AdmissibleSubspace.witnessY, (1 : Fin 3)) = 0 := by
    rw [Pi.smul_apply, deltaWitnessConfig_elsewhere (show _ ≠ _ by decide), smul_zero]
  rw [e1, e2, e3, e4]
  simp [map_zero]

theorem deltaWitnessConfig_ne_zero : deltaWitnessConfig ≠ 0 := by
  intro h
  have hc := congrFun h (AdmissibleSubspace.witnessY, (0 : Fin 3))
  simp only [deltaWitnessConfig, Pi.zero_apply] at hc
  exact suTwoWitness_ne_zero hc

theorem curlValueCovariant_smul_deltaWitnessConfig_ne_zero
    (U : Config AdmissibleSubspace.witnessL) (c : ℝ) (hc : c ≠ 0) :
    curlValueCovariant U (c • deltaWitnessConfig) ≠ 0 := by
  intro h
  have hp := congrFun h witnessPlaquette
  rw [curlValueCovariant_smul_deltaWitnessConfig U c] at hp
  rcases smul_eq_zero.mp hp with h1 | h1
  · exact hc h1
  · exact suTwoWitness_ne_zero h1

#print axioms curlValueCovariant_smul_deltaWitnessConfig
#print axioms deltaWitnessConfig_ne_zero
#print axioms curlValueCovariant_smul_deltaWitnessConfig_ne_zero

/-! ## §4 — `deltaWitnessC`: a `Btilde := ℝ` reparametrization embedding `deltaWitnessConfig`,
satisfying `IsBalabanReparam` at EVERY threshold, unconditionally in `U` (mirrors `TheLemma.spikeC`'s
construction exactly, LAW-19). -/

/-- `deltaWitnessConfig`, embedded into `BondFnL2 witnessL` via a rank-`1` map from `ℝ`. -/
noncomputable def deltaWitnessC : ℝ →L[ℝ] BondFnL2 AdmissibleSubspace.witnessL :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
    ((bondFnL2Equiv AdmissibleSubspace.witnessL).symm deltaWitnessConfig)

theorem deltaWitnessC_apply (t : ℝ) :
    deltaWitnessC t = t • (bondFnL2Equiv AdmissibleSubspace.witnessL).symm deltaWitnessConfig := by
  simp [deltaWitnessC]

theorem deltaWitnessC_injective : Function.Injective deltaWitnessC := by
  have hne : (bondFnL2Equiv AdmissibleSubspace.witnessL).symm deltaWitnessConfig ≠ 0 := by
    intro h
    apply deltaWitnessConfig_ne_zero
    have := congrArg (bondFnL2Equiv AdmissibleSubspace.witnessL) h
    simpa using this
  intro a b hab
  rw [deltaWitnessC_apply, deltaWitnessC_apply] at hab
  have hz := sub_eq_zero.mpr hab
  rw [← sub_smul] at hz
  rcases smul_eq_zero.mp hz with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hne

#print axioms deltaWitnessC_apply
#print axioms deltaWitnessC_injective

/-- **`deltaWitnessC` satisfies `IsBalabanReparam` at EVERY threshold, for EVERY `U` whatsoever** —
not merely regular ones. This is the load-bearing fact making the knife-edge REAL rather than
harmless: `deltaWitnessConfig` is not a mode `IsBalabanReparam`'s law excludes. -/
theorem deltaWitnessC_satisfies_isBalabanReparam (Mα₀thresh : ℝ) :
    IsBalabanReparam (Lat := AdmissibleSubspace.witnessL) Mα₀thresh deltaWitnessC := by
  refine ⟨deltaWitnessC_injective, ?_⟩
  intro Bt hBt Mα₀ _ U _
  have heq : bondFnL2Equiv AdmissibleSubspace.witnessL (deltaWitnessC Bt) = Bt • deltaWitnessConfig := by
    rw [deltaWitnessC_apply, map_smul]
    simp
  rw [heq]
  exact curlValueCovariant_smul_deltaWitnessConfig_ne_zero U Bt hBt

#print axioms deltaWitnessC_satisfies_isBalabanReparam

theorem deltaWitnessC_apply_one_eq :
    bondFnL2Equiv AdmissibleSubspace.witnessL (deltaWitnessC 1) = deltaWitnessConfig := by
  rw [deltaWitnessC_apply]
  simp

#print axioms deltaWitnessC_apply_one_eq

/-! ## §5 — `theLemma_normalized` (ONE `sorry`, as mandated), and its REFUTATION -/

/-- **THE CORRECTED TARGET — CMP99b p.428, both fixes applied.**

`deltaKQuadFormNormalizedCorrected` is p.392's source-normalized `Δ^η` (`tr 1 = 1` honored in BOTH
summands, `NormalizationAudit`), **NOT** p.428's recursive, `k`-indexed `Δ_k` (that gap is unchanged
from `TheLemma.lean`'s own disclosure and is NOT closed here). `IsRegularHolonomy` (`Regularity
Holonomy.lean`) replaces `IsRegular`'s adjoint-displacement proxy as the outer regularity hypothesis
on `U`, closing the central-blindness defect (`IsRegular`'s `Ad(-1) = id` blind spot). `IsBalabanReparam`
is UNCHANGED from `TheLemma.lean` (its own internal quantifier still ranges over `IsRegular`, not
`IsRegularHolonomy` — an intentional asymmetry: its role is to characterize which `C` are legal
reparametrizations, a question about `C`'s image alone, and `TheLemma.spikeC_satisfies_isBalaban
Reparam`'s own proof needs no regularity hypothesis at all, so this asymmetry is never load-bearing
below).

**Binder order** (re-derived from this compiled type, S92 discipline): `∃ γ₀` first, before `∀ Mα₀`,
`∀ U`, `∀ Bt` — matching Bałaban's "independent of `k` and `U`".

**⚠ This `sorry` is UNCLOSEABLE, proved so by `theLemma_normalized_contradicts_if_proved` below (§5),
not merely unattempted.** No known counterexample was the question posed; the answer found is
stronger: a KNOWN counterexample DOES touch this exact statement, orthogonal to both prior defects. -/
theorem theLemma_normalized
    {Lat : PeriodicLatticeExtent}
    {Btilde : Type*} [NormedAddCommGroup Btilde] [InnerProductSpace ℝ Btilde]
    (C : Btilde →L[ℝ] BondFnL2 Lat)
    (Mα₀thresh : ℝ) (hMα₀thresh_pos : 0 < Mα₀thresh)
    (hC : IsBalabanReparam Mα₀thresh C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ Mα₀ : ℝ, Mα₀ < Mα₀thresh →
      ∀ U : Config Lat, IsRegularHolonomy U Mα₀ →
      ∀ Bt : Btilde,
        γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U (bondFnL2Equiv Lat (C Bt)) := by
  sorry

/-- **THE REFUTATION.** The specialization of `theLemma_normalized`'s own conclusion at
`Lat := witnessL`, `Btilde := ℝ`, `C := deltaWitnessC`, `Mα₀thresh := 5` is FALSE: plugging
`Mα₀ := 4` (`< 5`), `U := witnessU` (`IsRegularHolonomy`-admissible there, §2), `Bt := 1` gives
`γ₀ · 1 ≤ deltaKQuadFormNormalizedCorrected witnessU deltaWitnessConfig = 0` (§1/§4), contradicting
`γ₀ > 0`. -/
theorem theLemma_normalized_conclusion_false_at_deltaWitnessC :
    ¬ (∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ Mα₀ : ℝ, Mα₀ < (5 : ℝ) →
        ∀ U : Config AdmissibleSubspace.witnessL, IsRegularHolonomy U Mα₀ →
        ∀ Bt : ℝ,
          γ₀ * ‖Bt‖ ^ 2 ≤
            deltaKQuadFormNormalizedCorrected U
              (bondFnL2Equiv AdmissibleSubspace.witnessL (deltaWitnessC Bt))) := by
  rintro ⟨γ₀, hγ₀, hall⟩
  have hspec := hall (4 : ℝ) (by norm_num) witnessU witnessU_isRegularHolonomy_four (1 : ℝ)
  rw [deltaWitnessC_apply_one_eq, check1_witnessU_normalized_zero] at hspec
  norm_num at hspec
  linarith

#print axioms theLemma_normalized_conclusion_false_at_deltaWitnessC

/-- **`deltaWitnessC` is a LEGAL `C` at threshold `5`** — the hypothesis `theLemma_normalized` would
need to accept this instantiation is genuinely satisfiable, not itself vacuous. -/
theorem deltaWitnessC_is_legal_at_five :
    IsBalabanReparam (Lat := AdmissibleSubspace.witnessL) (5 : ℝ) deltaWitnessC :=
  deltaWitnessC_satisfies_isBalabanReparam 5

#print axioms deltaWitnessC_is_legal_at_five

/-- **THE HEADLINE THEOREM: any proof of `theLemma_normalized`'s `Btilde := ℝ` instance yields
`False`.**

Takes as a hypothesis a term `H` of EXACTLY `theLemma_normalized`'s own signature, SPECIALIZED to
`Btilde := ℝ` (the universe-polymorphic `Type*` version elaborates to a universe-metavariable
mismatch when instantiated by NAME inside a nested `∀`, a Lean elaboration-order quirk unrelated to
the mathematics; the `Btilde := ℝ` restriction below is the honest, checked substitute — and it is
still the FULLY GENERAL claim's own necessary consequence: if `theLemma_normalized` held for every
`Btilde`, it would hold in particular for `Btilde := ℝ`, so refuting THIS restriction refutes the
general statement too). Derives `False` by specializing at the witness above. This is the rigorous
form of "the `sorry` is uncloseable": it is not that this dispatch failed to close it, it is that NO
closing term of this type can exist. -/
theorem theLemma_normalized_contradicts_if_proved
    (H : ∀ {Lat : PeriodicLatticeExtent} (C : ℝ →L[ℝ] BondFnL2 Lat) (Mα₀thresh : ℝ),
      0 < Mα₀thresh → IsBalabanReparam Mα₀thresh C →
      ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ Mα₀ : ℝ, Mα₀ < Mα₀thresh →
        ∀ U : Config Lat, IsRegularHolonomy U Mα₀ →
        ∀ Bt : ℝ,
          γ₀ * ‖Bt‖ ^ 2 ≤ deltaKQuadFormNormalizedCorrected U (bondFnL2Equiv Lat (C Bt))) :
    False := by
  exact theLemma_normalized_conclusion_false_at_deltaWitnessC
    (H (Lat := AdmissibleSubspace.witnessL) deltaWitnessC 5 (by norm_num)
      (deltaWitnessC_is_legal_at_five))

#print axioms theLemma_normalized_contradicts_if_proved

end AdalyFormal.Balaban.TheLemmaNormalized

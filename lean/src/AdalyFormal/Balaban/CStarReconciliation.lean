/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.PerturbationRoute
import AdalyFormal.Balaban.CStarLevelCorrected
import AdalyFormal.Balaban.ThirdLevelSandwich
import AdalyFormal.Balaban.AlphaAnalyticity

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `CStarReconciliation.lean` — the three unreconciled CMP99b p.428 statements, related in the kernel

Lane record: `compute/cstar_reconciliation/`.

## The three statements this module relates

**(a) the PENALTY form** — `PerturbationRoute.coercive_on_VSrc_perturbed`:
`(γ* − 320α₀)·‖A‖² ≤ ⟨A, Δ_k(U)A⟩ + ⟨A, P_Ax A⟩` for every fine `A` whose coarse datum lies in
`VRestrictedRoute.VSrc`, the source's own three clauses.

**(b) the REFUTATION** — `CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted`: the naive
`C`-sandwiched target is identically `0` at every `γ > 0` and every `U`, with the named conflation
`[CSTAR-LEVEL-MISMATCH]` and residual `[CSTAR-SCHUR-GAP]`.

**(c) the PRINTED statement** — `corpus/pages/CMP99b_p428.md` (`verification_status: adjudicated`,
render sha256 `128b1172e7090661d2c2ead70d9514244567c17a43c709ff87b18603b3012d54`):
`(3.156)`'s form "*is considered on the subspace `{B : B=0 on Λᶜ, B=0 on ⋃_{y∈Λ'} Ax(y), Q₁B=0}`*",
which "*we can parametrize ... using part of the variables `B`, which we denote by `B̃` ... we have
`B = C B̃`, where `C` is a linear operator*", and `C*Δ_kC` "*is defined by a positive definite
operator `C*Δ_kC` with a lower bound `γ₀ > 0` independent of `k` and `U`*".

## What is PROVED here

**1. `C` IS A PARAMETRIZATION IN p.428's SENSE (§2).** The tree had only `range C ⊆ ker Q₁`. Here:
`fullC` is the IDENTITY on `ker Q₁(U)` (`fullC_eq_self_of_mem_kerQ`), hence a linear PROJECTION
(`fullC_idem`); it is SURJECTIVE onto `ker Q₁(U)` from fields supported on the free set `Λ̃`
(`fullC_surjective_onto_kerQ`, section `dropAll`); it is INJECTIVE there
(`fullC_injective_on_free`); and the two non-vacuous clauses of the (3.156) subspace are EXACTLY
`range C` on axial free data (`subspace156_eq_range_C`, an `iff`). The only new input is that a
one-sided inverse of `coeffDc` is two-sided on the finite-dimensional fibre (`linv_of_rinv`), so
every existing consumer's `hinv` suffices.

**2. THE PENALTY TERM IS IDENTICALLY ZERO ON `range C` (§3).** `pAx_fullC_eq_zero`. Hence
(a)'s penalty form and the bare `C*Δ_kC` form COINCIDE there (`penalty_eq_bare_on_range`), for
every functional. This is the answer to "equivalent / stronger / incomparable" at the FORM level:
the penalty form is weaker in general (`P_Ax ≥ 0`) and the SAME on `range C`.

**3. A TRUE `C`-SANDWICH COERCIVITY (§5).** `cStarDeltaK_sandwich`:

  `(γ* − 320α₀) · bondEnergy B̃  ≤  ⟨B̃, C*Δ_kC B̃⟩`,
  `Δ_k = NormalizationAudit.deltaKQuadFormNormalizedCorrected U = ‖D_U·‖² + Δ'`,
  `C = fullC (trivialU L) 2 (dinvC (trivialU L) 2)`,

for every torus with `4 ∣ L μ + 1`, every `α₀` with `γ* − 320α₀ ≥ 0`, every `U` with
`frobSupBond U ≤ α₀`, and every `B̃` axial-gauge and supported on `Λ̃`. No extent appears in the
constant. §6 exhibits it with BOTH SIDES STRICTLY POSITIVE at a nonzero free field on `witL7`.

**4. THE RECONCILIATION WITH (b) (§6b).** `two_deltas_separate`: at ONE field, ONE `C`, ONE level,
ONE background, the Schur-typed `cStarDeltaKCForm` is `0` while the assembled
`deltaKQuadFormNormalizedCorrected` is `> 0`. The collapse is a property of the SCHUR TYPING — a
minimised energy is a function of the class modulo the constraint subspace, hence annihilates
`range C` — and not of `C`, the subspace or the field. (b) and (3) are both true and do not meet.

**5. THE DOOR AND `C` ARE ORDERED (§6c).** `range_C_subset_door_domain` (the containment that
discharges §5's hypothesis) and `cRestriction_strictly_stronger` (a fine field in the door's domain
outside `range C`, built from `VSrc_nontrivial` and the flat `Q`'s section). So `H₁(V)`/`VSrc` is
NOT "the tree's `C`": the `C`-restriction is strictly the stronger of the two.

## ⚠ HONEST SCOPE — read before quoting anything above

* **`Δ_k` here is the tree's ASSEMBLED lattice operator**, not the Schur complement, and not
  CMP99b's `(QG₁Q*)^{-1} − a`. `PerturbationRoute` §11a records that the external identification of
  either family with p.428's `Δ_k` is not formalisable — `Δ_k` occurs on no other page of that
  paper. Inherited, not repaired here.
* **`C` is built with the FLAT transport** (`trivialU`), because the domain hypothesis of
  `coercive_on_VSrc_perturbed` is phrased with the flat `Q` (`VRestrictedRoute` §0's own reading of
  clause (c3)). `Δ_k` carries the curved `U`. The covariant-`C` version is the named delta
  `CovariantCLandsInFlatKernel` (§8), discharged only at `U = 1`.
* **`J = 0`** throughout: (3.156)'s source term `−2⟨H₁D̃⁽²⁾(B),J⟩` is absent — the standing residual
  of `DeltaKSuTwoAssembly` §3.
* **Clause (c1) of the subspace is VACUOUS** on the periodic torus (`region_clause_vacuous_on_torus`
  states it as a theorem rather than a caveat). Two clauses are live, not three.
* **THE CONSTANT IS NONPOSITIVE ABOVE THE THRESHOLD** and the headline then asserts nothing:
  `sandwich_content_free_above_threshold` at `α₀ = 10⁻¹⁸`. The positive side is `α₀ = 10⁻²⁰`.
* **The BACKWARD transfer holds only with an EXTENT-DEPENDENT constant.** `[CSTAR-UPPER-BRIDGE]`
  (`IsUpperBridge`, §8) is CLOSED in §9 (`isUpperBridge_holds`) at `κ = 1 + |bonds|·ell⁶`, giving
  the unconditional per-lattice descent `restricted_of_sandwich_unconditional` with constant `γ/κ`.
  Because `κ` grows with the volume this does NOT reproduce p.428's `k`-independent claim; ~~the
  sharp `κ = 1 + ell³` needs the read-multiplicity count `[CSTAR-UPPER-BRIDGE-SHARP]`, stated in
  §9 and not proved.~~ **[S75 STRIKE 2026-08-02, install lane `compute/conjunct_install/`:
  `[CSTAR-UPPER-BRIDGE-SHARP]` IS PROVED, in `Balaban/SharpUpperBridge.lean`
  (`isUpperBridge_sharp`, and `R1d_holds : GoalRegister.R1d_SharpUpperBridge`), with the
  volume-free descent at `Balaban.SharpUpperBridge.restricted_of_sandwich_sharp` /
  `coercivity_volume_free`. Two further corrections THIS module owes, both from the R1d lane's F1
  finding: (a) the read-multiplicity count was ALREADY IN THIS TREE when the struck sentence was
  written — `RegularUQChain.sum_coarse_Sblk_eq` and `QCLMNorm.multiplicity_exact`, in modules this
  one does not import; (b) what remained genuinely missing was the ASSEMBLY (local Cauchy–Schwarz
  against `c`'s own read set + summing over the DROPPED bonds only), not the count. The crude
  `κ = 1 + |bonds|·ell⁶` bound of §9 stands as written and is not retracted;
  `SharpUpperBridge.sharp_lt_crude` proves the new constant is strictly smaller on every torus
  with more than one coarse bond.]** The FORWARD direction (§4, §5) needs nothing extra and loses
  no constant.
* **ONE LEVEL, `ell = 2`** for the composition; `[CSTAR-LEVEL-MISMATCH]`'s two-block-side repair
  lives in `CStarLevelCorrected`/`ThirdLevel*` and is not re-derived here.
* **NOT FULL3D, NOT the mass gap.** No `k`-recursion is run; the uniformity claimed is that the
  constant contains no extent, exactly as in `PerturbationRoute` §1.

`#print axioms` on every declaration below: `{propext, Classical.choice, Quot.sound}` — no `sorry`,
no `native_decide`, no new `axiom`.
-/

namespace AdalyFormal.Balaban.CStarReconciliation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf CoarseLattice mem_CoarseLattice
  staircasePath)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictCov lineCoarseRestrictCovLM
  lineCoarseRestrictCovLM_apply)
open AdalyFormal.Balaban.ReparamCSuTwo (restFunctional coeffDc constraintFunctional
  constraintFunctional_apply dropZero dropZero_apply)
open AdalyFormal.Balaban.ReparamCDisjoint (ReadsBond droppedBondLast droppedBondLast_not_reads
  lineCoarseRestrictCov_congr)
open AdalyFormal.Balaban.FullReparamC (IsDropped fullC fullCLM fullC_free fullC_dropped
  fullC_mem_kerQ fullC_axialGauge solvedValue dinvC dinvC_hinv isDropped_droppedBondLast
  droppedBondLast_injective freeBond freeBond_not_dropped freeBond_not_mem_staircase
  originSite_coarse)
open AdalyFormal.Balaban.AxialCoercivity (pAx pAx_nonneg pAx_eq_zero_of_vanishing_on_Ax)
open AdalyFormal.Balaban.AxialContour (Ax mem_Ax)
open AdalyFormal.Balaban.NormalizationAudit (deltaKQuadFormNormalizedCorrected)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.Balaban.CStarDeltaKCCoercive (bondEnergy_le_fullC)

variable {L : PeriodicLatticeExtent}

/-! ## §0 — bookkeeping on `bondEnergy` -/

theorem bondEnergy_nonneg' (A : Bond L → SuTwo) : 0 ≤ bondEnergy A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem bondEnergy_zero : bondEnergy (0 : Bond L → SuTwo) = 0 := by
  unfold bondEnergy; simp

/-- The energy of a single-bond field is strictly positive whenever the value is nonzero. -/
theorem bondEnergy_single_pos (b : Bond L) {w : SuTwo} (hw : w ≠ 0) :
    0 < bondEnergy (Pi.single b w : Bond L → SuTwo) := by
  have hle : ‖(Pi.single b w : Bond L → SuTwo) b‖ ^ 2
      ≤ ∑ e : Bond L, ‖(Pi.single b w : Bond L → SuTwo) e‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun e : Bond L => ‖(Pi.single b w : Bond L → SuTwo) e‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
  have hpos : (0 : ℝ) < ‖(Pi.single b w : Bond L → SuTwo) b‖ ^ 2 := by
    rw [Pi.single_eq_same]
    have : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    positivity
  unfold bondEnergy
  linarith

/-! ## §1 — `dropAll`: the (3.157) free coordinates as a retraction

`Λ̃ = Λ \ (⋃ Ax(y) ∪ ⋃ B(c)∩c)` is the free index set of CMP99b p.428. `dropAll ell` zeroes exactly
the eliminated variables `B(c)∩c = droppedBondLast ell c`, so `dropAll ell B` is the canonical free
representative of `B`. -/

/-- Zero out EVERY eliminated (3.157) variable. -/
noncomputable def dropAll (ell : ℕ) (B : Bond L → SuTwo) : Bond L → SuTwo :=
  fun b => @ite _ (IsDropped ell b) (Classical.dec _) 0 (B b)

theorem dropAll_of_dropped {ell : ℕ} (B : Bond L → SuTwo) {b : Bond L} (h : IsDropped ell b) :
    dropAll ell B b = 0 := by
  show (@ite _ (IsDropped ell b) (Classical.dec _) 0 (B b)) = 0
  rw [if_pos h]

theorem dropAll_of_free {ell : ℕ} (B : Bond L → SuTwo) {b : Bond L} (h : ¬ IsDropped ell b) :
    dropAll ell B b = B b := by
  show (@ite _ (IsDropped ell b) (Classical.dec _) 0 (B b)) = B b
  rw [if_neg h]

/-- `dropAll` produces a field satisfying the `hdrop` hypothesis of the energy bridge. -/
theorem dropAll_hdrop {ell : ℕ} (B : Bond L → SuTwo) (c : CoarseBond L ell) :
    dropAll ell B (droppedBondLast ell c) = 0 :=
  dropAll_of_dropped B (isDropped_droppedBondLast c)

/-- Dropping components can only lower the energy. -/
theorem bondEnergy_dropAll_le {ell : ℕ} (B : Bond L → SuTwo) :
    bondEnergy (dropAll ell B) ≤ bondEnergy B := by
  unfold bondEnergy
  refine Finset.sum_le_sum (fun b _ => ?_)
  by_cases h : IsDropped ell b
  · rw [dropAll_of_dropped B h, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
  · rw [dropAll_of_free B h]

/-! ## §2 — `C` IS A PARAMETRIZATION, not merely a map INTO the constraint locus

p.428 says of the subspace `{B : B = 0 on Λᶜ, B = 0 on ⋃_{y∈Λ'} Ax(y), Q₁B = 0}`:
"*We can parametrize this subspace ... using part of the variables `B`, which we denote by `B̃` ...
we have `B = C B̃`*". That is TWO properties: `range C ⊆ V` (the tree has it —
`fullC_mem_kerQ`, `fullC_axialGauge`) and `range C ⊇ V` (**nowhere in the tree before this
module**). §2 supplies the second, and with it the exact bijection. -/

/-- **The left inverse comes free.** `SuTwo` is finite dimensional, so a one-sided inverse of an
endomorphism is two-sided. This lets every consumer keep the tree's existing `hinv`
(`coeffDc ∘ Dinv = id`) and still get `Dinv ∘ coeffDc = id`. -/
theorem linv_of_rinv {f g : SuTwo →ₗ[ℝ] SuTwo} (h : f.comp g = LinearMap.id) :
    g.comp f = LinearMap.id := by
  have h' : f * g = 1 := h
  exact mul_eq_one_comm.mp h'

/-- **The exact linear split of the constraint at `c`**: the part not involving the eliminated
variable, plus the coefficient of the eliminated variable. Stated for an ARBITRARY field (the tree
had it only at `reparamCSuTwo`'s own image). -/
theorem constraintFunctional_split
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ell : ℕ)
    (c : CoarseBond L ell) (b₀ : Bond L) (B : Bond L → SuTwo) :
    constraintFunctional U ell c B
      = restFunctional U ell c b₀ B + coeffDc U ell c b₀ (B b₀) := by
  have hsplit : B = dropZero b₀ B + Pi.single b₀ (B b₀) := by
    funext b
    rw [Pi.add_apply, dropZero_apply, Pi.single_apply]
    by_cases h : b = b₀ <;> simp [h]
  calc constraintFunctional U ell c B
      = constraintFunctional U ell c (dropZero b₀ B + Pi.single b₀ (B b₀)) := by rw [← hsplit]
    _ = constraintFunctional U ell c (dropZero b₀ B)
          + constraintFunctional U ell c (Pi.single b₀ (B b₀)) := by rw [map_add]
    _ = restFunctional U ell c b₀ B + coeffDc U ell c b₀ (B b₀) := rfl

/-- **`C` IS THE IDENTITY ON THE CONSTRAINT LOCUS.** If `Q₁(U)B = 0` at every coarse bond then
`C B = B`. Hence `range C ⊇ ker Q₁(U)`, and `C` is a linear PROJECTION onto `ker Q₁(U)`. -/
theorem fullC_eq_self_of_mem_kerQ {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinvL : ∀ c : CoarseBond L ell,
      (Dinv c).comp (coeffDc U ell c (droppedBondLast ell c)) = LinearMap.id)
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    fullC U ell Dinv B = B := by
  funext b
  by_cases h : IsDropped ell b
  · obtain ⟨c, rfl⟩ := h
    rw [fullC_dropped hell hdvd U Dinv B c]
    have hsplit := constraintFunctional_split U ell c (droppedBondLast ell c) B
    have hzero : constraintFunctional U ell c B = 0 := by
      rw [constraintFunctional_apply]; exact hB c
    rw [hzero] at hsplit
    have hrest : restFunctional U ell c (droppedBondLast ell c) B
        = -(coeffDc U ell c (droppedBondLast ell c) (B (droppedBondLast ell c))) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hsplit.symm
    show -(Dinv c (restFunctional U ell c (droppedBondLast ell c) B)) = _
    rw [hrest, map_neg, neg_neg]
    exact LinearMap.congr_fun (hinvL c) (B (droppedBondLast ell c))
  · exact fullC_free U Dinv B h

/-- Same, with the tree's own RIGHT-inverse hypothesis `hinv`. -/
theorem fullC_eq_self_of_mem_kerQ' {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    fullC U ell Dinv B = B :=
  fullC_eq_self_of_mem_kerQ hell hdvd U Dinv (fun c => linv_of_rinv (hinv c)) B hB

/-- **`C` IS IDEMPOTENT** — a projection onto `ker Q₁(U)`. -/
theorem fullC_idem {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) :
    fullC U ell Dinv (fullC U ell Dinv B) = fullC U ell Dinv B :=
  fullC_eq_self_of_mem_kerQ' hell hdvd U Dinv hinv _ (fullC_mem_kerQ hell hdvd U Dinv hinv B)

/-- **`C` does not see the eliminated variables**: `C (dropAll B) = C B`.
The value on `c`'s own dropped bond is built from `rest_c`, which reads only bonds `c` READS, and
`c` reads no OTHER coarse bond's dropped bond (`droppedBondLast_not_reads`). -/
theorem fullC_dropAll {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (B : Bond L → SuTwo) :
    fullC U ell Dinv (dropAll ell B) = fullC U ell Dinv B := by
  funext b
  by_cases h : IsDropped ell b
  · obtain ⟨c, rfl⟩ := h
    have hrest : restFunctional U ell c (droppedBondLast ell c) (dropAll ell B)
        = restFunctional U ell c (droppedBondLast ell c) B := by
      unfold restFunctional
      simp only [LinearMap.comp_apply, constraintFunctional_apply]
      refine lineCoarseRestrictCov_congr U ell _ _ c (fun e he => ?_)
      rw [dropZero_apply, dropZero_apply]
      by_cases hee : e = droppedBondLast ell c
      · rw [if_pos hee, if_pos hee]
      · rw [if_neg hee, if_neg hee]
        refine dropAll_of_free B ?_
        rintro ⟨c', rfl⟩
        have hne : c ≠ c' := by rintro rfl; exact hee rfl
        exact droppedBondLast_not_reads hell hdvd c c' hne he
    rw [fullC_dropped hell hdvd U Dinv _ c, fullC_dropped hell hdvd U Dinv _ c,
      solvedValue, solvedValue, hrest]
  · rw [fullC_free U Dinv _ h, fullC_free U Dinv _ h, dropAll_of_free B h]

/-- **THE PARAMETRIZATION, SURJECTIVE HALF.** Every element of the constraint locus is `C B̃` for a
`B̃` supported on the (3.157) free set `Λ̃` — namely `B̃ = dropAll B`. Together with
`fullC_mem_kerQ` this is `range (C ∘ dropAll) = ker Q₁(U)` exactly. -/
theorem fullC_surjective_onto_kerQ {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    (∀ c : CoarseBond L ell, dropAll ell B (droppedBondLast ell c) = 0)
      ∧ fullC U ell Dinv (dropAll ell B) = B := by
  refine ⟨dropAll_hdrop B, ?_⟩
  rw [fullC_dropAll hell hdvd U Dinv B]
  exact fullC_eq_self_of_mem_kerQ' hell hdvd U Dinv hinv B hB

/-- **THE PARAMETRIZATION, INJECTIVE HALF.** On fields supported on the free set `Λ̃`, `C` is
injective. So `C : {B̃ supported on Λ̃} → ker Q₁(U)` is a linear BIJECTION — exactly p.428's
"`B = C B̃`, `C` a linear operator, identity on almost all bonds". -/
theorem fullC_injective_on_free {ell : ℕ}
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (B₁ B₂ : Bond L → SuTwo)
    (h₁ : ∀ c : CoarseBond L ell, B₁ (droppedBondLast ell c) = 0)
    (h₂ : ∀ c : CoarseBond L ell, B₂ (droppedBondLast ell c) = 0)
    (heq : fullC U ell Dinv B₁ = fullC U ell Dinv B₂) : B₁ = B₂ := by
  funext b
  by_cases h : IsDropped ell b
  · obtain ⟨c, rfl⟩ := h
    rw [h₁ c, h₂ c]
  · have e₁ := fullC_free U Dinv B₁ h
    have e₂ := fullC_free U Dinv B₂ h
    rw [← e₁, ← e₂, heq]

/-- **THE AXIAL CLAUSE IS ALSO EXACTLY PARAMETRIZED.** If `B` lies in the (3.156) subspace — the
constraint locus AND the axial locus — then its free representative `dropAll B` is axial too, so
`B` is `C` of an axial free field. (`fullC_axialGauge` is the converse inclusion.) -/
theorem dropAll_axial {ell : ℕ} (B : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, B e = 0) :
    ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, dropAll ell B e = 0 := by
  intro y' hy' x hx e he
  by_cases h : IsDropped ell e
  · exact dropAll_of_dropped B h
  · rw [dropAll_of_free B h]; exact hax y' hy' x hx e he

/-- **THE (3.156) SUBSPACE IS EXACTLY `range C` restricted to axial free data.**
Both inclusions in one statement, at the two clauses that are not vacuous on a torus. -/
theorem subspace156_eq_range_C {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (B : Bond L → SuTwo) :
    ((∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0)
        ∧ (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
            ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
            ∀ e ∈ staircasePath y' x, B e = 0))
      ↔ ∃ Btil : Bond L → SuTwo,
          (∀ c : CoarseBond L ell, Btil (droppedBondLast ell c) = 0)
          ∧ (∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
              ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
              ∀ e ∈ staircasePath y' x, Btil e = 0)
          ∧ fullC U ell Dinv Btil = B := by
  constructor
  · rintro ⟨hQ, hax⟩
    exact ⟨dropAll ell B, dropAll_hdrop B, dropAll_axial B hax,
      (fullC_surjective_onto_kerQ hell hdvd U Dinv hinv B hQ).2⟩
  · rintro ⟨Btil, _, hax, rfl⟩
    exact ⟨fullC_mem_kerQ hell hdvd U Dinv hinv Btil,
      fullC_axialGauge hell hdvd U Dinv Btil hax⟩

/-! ## §3 — THE PENALTY TERM VANISHES ON `range C`

`PerturbationRoute`'s headline is the PENALTY form `⟨u,Δu⟩ + ⟨u,P_Ax u⟩`; p.428's printed object is
the bare `C*Δ_kC`. §3 settles the relation: on `range C` (with axial free data) the two forms are
EQUAL, because `P_Ax` is identically `0` there. Off `range C` the penalty form is strictly larger
(§3b, a must-fire control). So the penalty form is a WEAKER statement in general and the SAME
statement on `range C`; it is not incomparable. -/

/-- **`P_Ax ∘ C = 0` on axial free data.** -/
theorem pAx_fullC_eq_zero {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (Btil : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, Btil e = 0) :
    pAx (fullC U ell Dinv Btil) (CoarseLattice L ell) ell = 0 := by
  refine pAx_eq_zero_of_vanishing_on_Ax _ _ _ (fun y hy b hb => ?_)
  obtain ⟨x, hx, _, hbs⟩ := mem_Ax.1 hb
  exact fullC_axialGauge hell hdvd U Dinv Btil hax y hy x hx b hbs

/-- **The penalty form and the bare form COINCIDE on `range C`**, for EVERY functional `q`. -/
theorem penalty_eq_bare_on_range {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo)) (q : (Bond L → SuTwo) → ℝ)
    (Btil : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L ell →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' ell →
      ∀ e ∈ staircasePath y' x, Btil e = 0) :
    q (fullC U ell Dinv Btil) + pAx (fullC U ell Dinv Btil) (CoarseLattice L ell) ell
      = q (fullC U ell Dinv Btil) := by
  rw [pAx_fullC_eq_zero hell hdvd U Dinv Btil hax, add_zero]

/-! ## §4 — the ABSTRACT transfer, both directions, with the missing ingredient isolated -/

/-- **FORWARD TRANSFER (restricted ⟹ sandwich).** A coercivity on the constraint locus transfers to
the `C`-sandwich in the free coordinates WITH THE SAME CONSTANT, given only
(i) `range C` inside the locus and (ii) the energy bridge. Both hold for `fullC`. -/
theorem sandwich_of_restricted {W : Type*} (q : (Bond L → SuTwo) → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (C : W → (Bond L → SuTwo)) (V : (Bond L → SuTwo) → Prop)
    (hrange : ∀ w : W, V (C w))
    (hres : ∀ B : Bond L → SuTwo, V B → γ * bondEnergy B ≤ q B)
    (en : W → ℝ) (hbridge : ∀ w : W, en w ≤ bondEnergy (C w)) (w : W) :
    γ * en w ≤ q (C w) :=
  le_trans (mul_le_mul_of_nonneg_left (hbridge w) hγ) (hres (C w) (hrange w))

/-- **BACKWARD TRANSFER (sandwich ⟹ restricted).** Requires, in addition to surjectivity, the
UPPER energy bridge `bondEnergy B ≤ κ · bondEnergy (free part of B)` — the control of the eliminated
variables by the free ones. That inequality is `[CSTAR-UPPER-BRIDGE]` (§8). -/
theorem restricted_of_sandwich (q : (Bond L → SuTwo) → ℝ) (γ κ : ℝ) (hκ : 0 < κ)
    (C : (Bond L → SuTwo) → (Bond L → SuTwo)) (V : (Bond L → SuTwo) → Prop)
    (sect : (Bond L → SuTwo) → (Bond L → SuTwo))
    (hsect : ∀ B, V B → C (sect B) = B)
    (hsand : ∀ w, γ * bondEnergy w ≤ q (C w))
    (hupper : ∀ B, V B → bondEnergy B ≤ κ * bondEnergy (sect B))
    (hγ : 0 ≤ γ) (B : Bond L → SuTwo) (hB : V B) :
    (γ / κ) * bondEnergy B ≤ q B := by
  have h1 : γ * bondEnergy (sect B) ≤ q B := by
    have := hsand (sect B); rwa [hsect B hB] at this
  have h2 : bondEnergy B ≤ κ * bondEnergy (sect B) := hupper B hB
  have h3 : (γ / κ) * bondEnergy B ≤ (γ / κ) * (κ * bondEnergy (sect B)) :=
    mul_le_mul_of_nonneg_left h2 (div_nonneg hγ (le_of_lt hκ))
  have h4 : (γ / κ) * (κ * bondEnergy (sect B)) = γ * bondEnergy (sect B) := by
    field_simp
  linarith

/-! ## §5 — THE COMPOSITION: a TRUE `C*Δ_kC` coercivity in the free (3.157) coordinates

`PerturbationRoute.coercive_on_VSrc_perturbed` is the tree's `k`-uniform positive: for every fine
field `A` whose coarse datum lies in the source's subspace `VSrc`,

  `(γ* − 320α₀)·‖A‖² ≤ ⟨A, Δ_k(U)A⟩ + ⟨A, P_Ax A⟩`.

Two facts turn it into p.428's printed shape:

* `range C ⊆ ker Q₁`, and `VSrc` HOLDS AT THE ZERO COARSE DATUM (`VSrc_zero`), so the domain
  hypothesis is discharged automatically on `range C` — the reparametrization was built to satisfy
  exactly the constraint the domain asks about;
* the penalty term VANISHES on `range C` (§3), so what remains is the BARE `⟨B̃, C*Δ_kC B̃⟩`.

The result is `γ₀·bondEnergy B̃ ≤ ⟨B̃, C*Δ_kC B̃⟩` with `γ₀ = γ* − 320α₀` — the (3.157) inequality
with the constant `k`-independent (nothing in it mentions the extent).

**SCOPE, stated here and not only in the module header.**
* `Δ_k` is `NormalizationAudit.deltaKQuadFormNormalizedCorrected U = ‖D_U·‖² + Δ'`, the tree's
  assembled lattice operator — NOT the Schur complement `deltaKSuTwoForm` that
  `CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` refutes. §6 proves those are different
  objects at one and the same field, which is the whole reconciliation.
* `C` is built with the FLAT transport `trivialU L`, because the domain hypothesis of
  `coercive_on_VSrc_perturbed` is phrased with the flat `Q` (`VRestrictedRoute` §0's own reading of
  clause (c3)). `Δ_k` carries the curved `U`. The covariant-`C` version of the same composition is
  not available until the domain hypothesis is restated covariantly; that is a delta, named in §8.
* The constant is `≤ 0` for `α₀ ≥ γ*/320`; the headline is therefore stated with an explicit
  nonnegativity hypothesis, and §7c exhibits both sides of the threshold. -/

/-- **THE PENALTY-FREE FORM ON `range C`.** Same constant, the `P_Ax` term proved absent rather
than dropped. Stated at the transported energy `bondEnergy (C B̃)`; no hypothesis on the sign of the
constant is needed here. -/
theorem cStarDeltaK_bound_transported (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (Btil : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' 2 →
      ∀ e ∈ staircasePath y' x, Btil e = 0) :
    AdalyFormal.Balaban.PerturbationRoute.gammaZero alpha0
        * bondEnergy (fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil)
      ≤ deltaKQuadFormNormalizedCorrected U
          (fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil) := by
  have hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1) :=
    AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4
  set A := fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil with hA
  have hQ : lineCoarseRestrictCov (trivialU L) 2 A = (fun _ => 0) := by
    funext c
    exact fullC_mem_kerQ (by norm_num) hdvd2 (trivialU L) (dinvC (trivialU L) 2)
      (dinvC_hinv (by norm_num) hdvd2 (trivialU L)) Btil c
  have hV : AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4
      (lineCoarseRestrictCov (trivialU L) 2 A) := by
    rw [hQ]
    exact AdalyFormal.Balaban.VRestrictedRoute.VSrc_zero hdvd4
  have hmain := AdalyFormal.Balaban.PerturbationRoute.coercive_on_VSrc_perturbed hdvd4 halpha U
    hsup A hV
  have hpen : pAx A (CoarseLattice L 2) 2 = 0 :=
    pAx_fullC_eq_zero (by norm_num) hdvd2 (trivialU L) (dinvC (trivialU L) 2) Btil hax
  rw [hpen, add_zero] at hmain
  exact hmain

/-- **THE HEADLINE — p.428's PRINTED FORM `⟨B̃, C*Δ_kC B̃⟩ ≥ γ₀‖B̃‖²` ON OUR CARRIERS, deltas
named** (billing narrowed 2026-08-02 per the Sol gate's Q6: the operator is OUR assembled Δ_k —
the paper defines its own nowhere — with flat C, J = 0, one level; "p.428's" unqualified
overclaimed). Kimi-gate strengthening recorded: the identity `pAx ∘ C = pAx` holds for EVERY
field (probe compiled in-lane), so the vanishing below is exactly "input is axial", consistent
with Sol's non-axial counterexample.

For every torus with `4 ∣ L μ + 1`, every `α₀ ≥ 0` below the threshold, every background `U` with
`frobSupBond U ≤ α₀`, and every free field `B̃` that is axial-gauge and vanishes on every eliminated
bond (i.e. `B̃` is supported on `Λ̃`):

  `(γ* − 320α₀) · bondEnergy B̃ ≤ ⟨B̃, C*Δ_kC B̃⟩`.

Nothing in the statement mentions the extent, so the constant is uniform over the level tower —
which is what "independent of `k` and `U`" asks for on p.428. Read §5's SCOPE before quoting. -/
theorem cStarDeltaK_sandwich (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    {alpha0 : ℝ} (halpha : 0 ≤ alpha0)
    (hgamma : 0 ≤ AdalyFormal.Balaban.PerturbationRoute.gammaZero alpha0)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (hsup : frobSupBond U ≤ alpha0) (Btil : Bond L → SuTwo)
    (hax : ∀ y' : PeriodicLatticeSite L, y' ∈ CoarseLattice L 2 →
      ∀ x : PeriodicLatticeSite L, x ∈ blockOf y' 2 →
      ∀ e ∈ staircasePath y' x, Btil e = 0)
    (hdrop : ∀ c : CoarseBond L 2, Btil (droppedBondLast 2 c) = 0) :
    AdalyFormal.Balaban.PerturbationRoute.gammaZero alpha0 * bondEnergy Btil
      ≤ deltaKQuadFormNormalizedCorrected U
          (fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil) := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hgamma)
    (cStarDeltaK_bound_transported hdvd4 halpha U hsup Btil hax)
  exact bondEnergy_le_fullC (trivialU L) (dinvC (trivialU L) 2) Btil hdrop

/-! ## §6 — NON-VACUITY, at an explicit nonzero free field

The free (3.157) coordinate `B̃` supported on a single bond of `Λ̃` — the bond
`FullReparamC.freeBond 2 y`, proved there to be neither eliminated (`freeBond_not_dropped`) nor on
any axial staircase (`freeBond_not_mem_staircase`). On `witL7` (`L μ = 7`, so `4 ∣ 8`) it satisfies
both hypotheses of §5's headline and has strictly positive energy. -/

/-- The origin coarse site of `witL7`. -/
def witY : PeriodicLatticeSite AdalyFormal.Balaban.ThirdLevelWitness.witL7 := fun _ => 0

/-- **THE FREE-COORDINATE WITNESS.** Supported on one bond of `Λ̃`. -/
noncomputable def witBtil : Bond AdalyFormal.Balaban.ThirdLevelWitness.witL7 → SuTwo :=
  Pi.single (freeBond 2 witY) suTwoWitness

theorem witL7_two : ∀ μ : Fin 3, (2 : ℕ) ∣ (AdalyFormal.Balaban.ThirdLevelWitness.witL7 μ + 1) :=
  AdalyFormal.Balaban.ThirdLevelWitness.witL7_two_dvd

theorem witY_coarse : witY ∈ CoarseLattice AdalyFormal.Balaban.ThirdLevelWitness.witL7 2 :=
  originSite_coarse

/-- `witBtil` is axial-gauge — the supporting bond lies on no staircase. -/
theorem witBtil_axial :
    ∀ y' : PeriodicLatticeSite AdalyFormal.Balaban.ThirdLevelWitness.witL7,
      y' ∈ CoarseLattice AdalyFormal.Balaban.ThirdLevelWitness.witL7 2 →
      ∀ x : PeriodicLatticeSite AdalyFormal.Balaban.ThirdLevelWitness.witL7,
        x ∈ blockOf y' 2 → ∀ e ∈ staircasePath y' x, witBtil e = 0 := by
  intro y' hy' x hx e he
  have hne : e ≠ freeBond 2 witY := by
    rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) witL7_two witY witY_coarse y' hy' x hx he
  exact Pi.single_eq_of_ne hne _

/-- `witBtil` vanishes on every eliminated bond — it is genuinely supported on `Λ̃`. -/
theorem witBtil_hdrop :
    ∀ c : CoarseBond AdalyFormal.Balaban.ThirdLevelWitness.witL7 2,
      witBtil (droppedBondLast 2 c) = 0 := by
  intro c
  have hne : droppedBondLast 2 c ≠ freeBond 2 witY := by
    intro heq
    exact freeBond_not_dropped (by norm_num) witL7_two witY witY_coarse ⟨c, heq.symm⟩
  exact Pi.single_eq_of_ne hne _

theorem witBtil_energy_pos : 0 < bondEnergy witBtil :=
  bondEnergy_single_pos _ suTwoWitness_ne_zero

/-- **THE HEADLINE IS INHABITED, WITH BOTH SIDES STRICTLY POSITIVE.** At `α₀ = 10⁻²⁰` (where
`γ₀ > 0`, `PerturbationRoute.gammaZero_pos_at_1e_neg_20`), at `U = 1` on `witL7`:

  `0 < γ₀ · bondEnergy B̃ ≤ ⟨B̃, C*Δ_kC B̃⟩`.

So the `C`-sandwich value is proved STRICTLY POSITIVE at a nonzero free field — the exact quantity
`cStarDeltaKC_coercivity_refuted` proves is identically `0` for the Schur-complement typing. -/
theorem cStarDeltaK_sandwich_nonvacuous :
    0 < AdalyFormal.Balaban.PerturbationRoute.gammaZero (1 / 10 ^ 20) * bondEnergy witBtil
      ∧ AdalyFormal.Balaban.PerturbationRoute.gammaZero (1 / 10 ^ 20) * bondEnergy witBtil
        ≤ deltaKQuadFormNormalizedCorrected
            (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
            (fullC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2
              (dinvC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2) witBtil) := by
  have hgpos : 0 < AdalyFormal.Balaban.PerturbationRoute.gammaZero (1 / 10 ^ 20) :=
    AdalyFormal.Balaban.PerturbationRoute.gammaZero_pos_at_1e_neg_20
  have hsup : frobSupBond (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
      ≤ (1 / 10 ^ 20 : ℝ) := by
    rw [AdalyFormal.Balaban.RegularUDomainWitness.frobSupBond_trivialU]
    norm_num
  refine ⟨mul_pos hgpos witBtil_energy_pos, ?_⟩
  exact cStarDeltaK_sandwich AdalyFormal.Balaban.ThirdLevelWitness.witL7_four_dvd
    (by norm_num) (le_of_lt hgpos) _ hsup witBtil witBtil_axial witBtil_hdrop

/-- **The sandwich value is strictly positive at the witness.** -/
theorem cStarDeltaK_sandwich_pos :
    0 < deltaKQuadFormNormalizedCorrected
        (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
        (fullC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2
          (dinvC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2) witBtil) :=
  lt_of_lt_of_le cStarDeltaK_sandwich_nonvacuous.1 cStarDeltaK_sandwich_nonvacuous.2

/-! ## §6b — THE RECONCILIATION WITH THE REFUTATION, AT ONE AND THE SAME FIELD

`CStarDeltaKCCoercive.cStarDeltaKC_coercivity_refuted` proves the `C`-sandwich is identically `0`
for EVERY `γ > 0`; §5 proves a strictly positive lower bound for the `C`-sandwich. Both are true and
they do not conflict, because the two `Δ`'s are DIFFERENT OBJECTS:

* the refuted one is `CStarDeltaKCCompose.cStarDeltaKCForm`, whose leading term is the SCHUR
  COMPLEMENT `deltaJQuadFormCovFaithful` — a minimised energy over the constraint subspace `V`,
  hence a function of the class of `B` modulo `V`, hence identically zero on `V ⊇ range C`;
* the one bounded below here is `NormalizationAudit.deltaKQuadFormNormalizedCorrected
  = ‖D_U·‖² + Δ'`, the assembled lattice operator, which is NOT a minimised energy and does NOT
  annihilate `V`.

`two_deltas_separate` exhibits both at the SAME field, the SAME `C`, the SAME level and the SAME
background: one is `0`, the other is `> 0`. That is the whole of `[CSTAR-LEVEL-MISMATCH]` seen from
the operator side — the collapse is a property of the SCHUR TYPING, not of `C`, not of the
subspace, and not of the field. -/

/-- **THE TWO `Δ`'s, SEPARATED AT ONE FIELD.** -/
theorem two_deltas_separate (a : ℝ)
    [(AdalyFormal.Balaban.CovariantHjMinimizer.deltaKernelImageCovH
      (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv
        AdalyFormal.Balaban.ThirdLevelWitness.witL7)).HasOrthogonalProjection]
    [(AdalyFormal.Balaban.CovariantHjFaithful.curlImageCovHFaithful 2
      (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv
        AdalyFormal.Balaban.ThirdLevelWitness.witL7)
      (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)).HasOrthogonalProjection] :
    AdalyFormal.Balaban.CStarDeltaKCCompose.cStarDeltaKCForm a 2
        (AdalyFormal.Balaban.CovariantHjMinimizer.oneLevelUniv
          AdalyFormal.Balaban.ThirdLevelWitness.witL7)
        (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
        (fullCLM (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2
          (dinvC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2)) witBtil = 0
      ∧ 0 < deltaKQuadFormNormalizedCorrected
          (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7)
          (fullC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2
            (dinvC (trivialU AdalyFormal.Balaban.ThirdLevelWitness.witL7) 2) witBtil) := by
  refine ⟨?_, cStarDeltaK_sandwich_pos⟩
  exact AdalyFormal.Balaban.CStarDeltaKCCoercive.cStarDeltaKCForm_fullC_eq_zero_oneLevelUniv a
    (by norm_num) witL7_two _ _
    (dinvC_hinv (by norm_num) witL7_two _) witBtil

/-! ## §6c — THE DOOR AND `C` ARE ORDERED, NOT EQUAL

`OnRangeCoercivity`/`VRestrictedRoute`'s door restricts the CONSUMER to fine fields whose coarse
datum lies in `VSrc`. p.428's `C` restricts to fields whose coarse datum is `0`. The first
containment is proved (`range_C_subset_door_domain` — this is exactly what discharges §5's domain
hypothesis); the reverse FAILS, and not for a bookkeeping reason: `VSrc` carries a NONZERO coarse
field (`VRestrictedRoute.VSrc_nontrivial`) and the flat `Q` has a section
(`FullySupplied.lineCoarseRestrictSuTwo_suTwoLift`), so a fine field with nonzero coarse datum IN
`VSrc` exists and is outside `range C`.

**So the `C`-sandwich statement is STRICTLY STRONGER as a domain restriction** — it asserts the
bound on strictly fewer fields than the door does. It is NOT the same statement as the door's, and
it is NOT incomparable with it: the two are ordered, and this is the order. -/

/-- **`range C` sits inside the door's domain.** Every `C B̃` has coarse datum `0`, and `0 ∈ VSrc`. -/
theorem range_C_subset_door_domain (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1))
    (Btil : Bond L → SuTwo) :
    AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4
      (lineCoarseRestrictCov (trivialU L) 2
        (fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil)) := by
  have hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1) :=
    AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4
  have hQ : lineCoarseRestrictCov (trivialU L) 2
      (fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil) = (fun _ => 0) := by
    funext c
    exact fullC_mem_kerQ (by norm_num) hdvd2 (trivialU L) (dinvC (trivialU L) 2)
      (dinvC_hinv (by norm_num) hdvd2 (trivialU L)) Btil c
  rw [hQ]
  exact AdalyFormal.Balaban.VRestrictedRoute.VSrc_zero hdvd4

/-- **THE STRICTNESS.** A fine field in the door's domain that is NOT in `range C`. -/
theorem cRestriction_strictly_stronger (hdvd4 : ∀ μ : Fin 3, (4 : ℕ) ∣ (L μ + 1)) :
    ∃ A : Bond L → SuTwo,
      AdalyFormal.Balaban.VRestrictedRoute.VSrc hdvd4
          (lineCoarseRestrictCov (trivialU L) 2 A)
        ∧ ∀ Btil : Bond L → SuTwo,
            fullC (trivialU L) 2 (dinvC (trivialU L) 2) Btil ≠ A := by
  have hdvd2 : ∀ μ : Fin 3, (2 : ℕ) ∣ (L μ + 1) :=
    AdalyFormal.Balaban.VRestrictedRoute.two_dvd_of_four hdvd4
  obtain ⟨F, hF, hFne⟩ := AdalyFormal.Balaban.VRestrictedRoute.VSrc_nontrivial hdvd4
  refine ⟨AdalyFormal.Balaban.FullySupplied.suTwoLift 2 F, ?_, ?_⟩
  · have hQA : lineCoarseRestrictCov (trivialU L) 2
        (AdalyFormal.Balaban.FullySupplied.suTwoLift 2 F) = F := by
      funext b
      rw [AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU]
      exact AdalyFormal.Balaban.FullySupplied.lineCoarseRestrictSuTwo_suTwoLift
        (by norm_num) hdvd2 F b
    rw [hQA]; exact hF
  · intro Btil heq
    refine hFne ?_
    funext b
    have hker := fullC_mem_kerQ (by norm_num) hdvd2 (trivialU L) (dinvC (trivialU L) 2)
      (dinvC_hinv (by norm_num) hdvd2 (trivialU L)) Btil b
    rw [heq, AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictCov_trivialU,
      AdalyFormal.Balaban.FullySupplied.lineCoarseRestrictSuTwo_suTwoLift
        (by norm_num) hdvd2 F b] at hker
    exact hker

/-! ## §7 — WHO CHOOSES EACH PARAMETER, and where the statement loses content

* `L` — universally quantified, constrained only by `4 ∣ L μ + 1`. Inhabited (`witL7`).
* `α₀` — chosen by the CONSUMER. The constant `γ₀(α₀) = γ* − 320α₀` is **nonpositive** for
  `α₀ ≥ γ*/320`, and there the headline is content-free: its left side is `≤ 0` while the right
  side is a value of the assembled quadratic form. `sandwich_content_free_above_threshold` states
  exactly that, at `α₀ = 10⁻¹⁸`, so the degeneracy is on the record as a theorem rather than a
  caveat. `PerturbationRoute.gammaZero_pos_at_1e_neg_20` is the other side.
* `U` — universally quantified subject to `frobSupBond U ≤ α₀`. At small `α₀` this is a genuine
  smallness restriction; the flat `U = 1` satisfies it for every `α₀ ≥ 0`.
* `Dinv` — NOT free: pinned to the canonical `dinvC`, whose right-inverse property is discharged
  unconditionally (`dinvC_hinv`).
* `B̃` — universally quantified subject to the two `Λ̃`-support hypotheses. Inhabited by a nonzero
  field with strictly positive energy (§6), so the headline is not a statement about `{0}`. -/

/-- **THE DEGENERATE POINT, EXHIBITED.** Above the threshold the headline's left-hand side is
nonpositive for EVERY free field, so it asserts nothing there. -/
theorem sandwich_content_free_above_threshold (Btil : Bond L → SuTwo) :
    AdalyFormal.Balaban.PerturbationRoute.gammaZero (1 / 10 ^ 18) * bondEnergy Btil ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg
    AdalyFormal.Balaban.PerturbationRoute.gammaZero_nonpos_at_1e_neg_18 (bondEnergy_nonneg' Btil)

/-! ## §8 — THE HONEST DELTAS, as named `Prop`s (S84)

What p.428's `C` requires that this tree does not yet carry. Each is a `def : Prop`, UNPROVED and
so marked; each is stated so that a proof of it immediately buys a named consequence, so none of
them is decorative. -/

/-- **`[CSTAR-UPPER-BRIDGE]`** — the eliminated variables are controlled by the free ones on the
constraint locus. This is the one missing ingredient of the BACKWARD transfer: with it, p.428's
change of variables is a norm equivalence and the `C`-sandwich bound and the restricted bound are
the same statement up to the factor `κ`. ~~Not proved here.~~ (STALE, corrected 2026-08-02 per
the Sol gate: §9's `isUpperBridge_holds` PROVES it at the crude `κ = 1 + |bonds|·ell⁶`; ~~the sharp
`1 + ell³` remains the named residual.~~ **[S75 2026-08-02, install lane: the sharp `1 + ell³` is
PROVED — `Balaban.SharpUpperBridge.isUpperBridge_sharp`, for every `0 < ell` with
`∀ μ, ell ∣ L μ + 1`, at every background `U`.]**) The forward direction (§4, §5) does not need
it. -/
def IsUpperBridge (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (κ : ℝ) : Prop :=
  ∀ B : Bond L → SuTwo, (∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) →
    bondEnergy B ≤ κ * bondEnergy (dropAll ell B)

/-- **What `[CSTAR-UPPER-BRIDGE]` buys, stated as a theorem so the delta is load-bearing.** Given
the bridge, a `C`-sandwich coercivity in the free coordinates DESCENDS to a coercivity on the
constraint locus, with constant `γ/κ`. -/
theorem restricted_of_sandwich_at_fullC {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    {κ : ℝ} (hκ : 0 < κ) (hbridge : IsUpperBridge ell U κ)
    (q : (Bond L → SuTwo) → ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hsand : ∀ Btil : Bond L → SuTwo, γ * bondEnergy Btil ≤ q (fullC U ell Dinv Btil))
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    (γ / κ) * bondEnergy B ≤ q B :=
  restricted_of_sandwich q γ κ hκ (fullC U ell Dinv)
    (fun B => ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0)
    (dropAll ell)
    (fun B hB => (fullC_surjective_onto_kerQ hell hdvd U Dinv hinv B hB).2)
    hsand hbridge hγ B hB

/-- **`[CSTAR-REGION]`** — p.428's clause (c1), "`B = 0` on `Λᶜ`", with `Λ` a genuine proper
subregion of the lattice. -/
def IsRegionSupported (region : Finset (Bond L)) (B : Bond L → SuTwo) : Prop :=
  ∀ b : Bond L, b ∉ region → B b = 0

/-- **Clause (c1) is VACUOUS on this carrier** — the periodic torus has no `Λᶜ`. Proved rather
than asserted, so no reader counts three live clauses where two are live. -/
theorem region_clause_vacuous_on_torus (B : Bond L → SuTwo) :
    IsRegionSupported (Finset.univ : Finset (Bond L)) B :=
  fun b hb => absurd (Finset.mem_univ b) hb

/-- **`[CSTAR-C-COVARIANT]`** — the composition of §5 uses the FLAT `C` (built from
`trivialU`) because the domain hypothesis of `coercive_on_VSrc_perturbed` is phrased with the flat
`Q`. This `Prop` is the missing statement: the covariant reparametrization also lands in the flat
constraint locus. It is FALSE in general for a curved `U` (the transports do not cancel), which is
why the delta is a delta and not a plumbing gap; the honest general-`U` form carries an `O(α₀)`
remainder, exactly as `[STOKES-COMM-U]` records for the neighbouring identity. -/
def CovariantCLandsInFlatKernel (ell : ℕ)
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) : Prop :=
  ∀ Btil : Bond L → SuTwo, ∀ c : CoarseBond L ell,
    lineCoarseRestrictCov (trivialU L) ell (fullC U ell (dinvC U ell) Btil) c = 0

/-- At `U = 1` the delta is discharged trivially — a must-not-fire control showing
`CovariantCLandsInFlatKernel` is not an empty `Prop`. -/
theorem covariantCLandsInFlatKernel_at_trivial {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    CovariantCLandsInFlatKernel ell (trivialU L) :=
  fun Btil c => fullC_mem_kerQ hell hdvd (trivialU L) (dinvC (trivialU L) ell)
    (dinvC_hinv hell hdvd (trivialU L)) Btil c

/-! ## §9 — `[CSTAR-UPPER-BRIDGE]` CLOSED, at an EXTENT-DEPENDENT constant

§8 named the missing ingredient of the backward transfer and stated it as a `Prop`. It is closed
here rather than left named: `isUpperBridge_holds` proves `IsUpperBridge ell U κ` for EVERY `ell > 0`,
EVERY compatible torus and EVERY background `U`, with

  `κ = 1 + (card of the bond set) · ell⁶`.

Mechanism, no analysis beyond the triangle inequality: `Q_ell` is a genuine AVERAGE — `ell⁴` terms
against the prefactor `1/ell⁴` — and `RMap` is an isometry (`AlphaAnalyticity.norm_RMap`), so
`‖Q_ell f‖ ≤ max_b ‖f b‖ ≤ √(bondEnergy f)` pointwise (§9a). On the constraint locus `C` is the
identity (§2) and does not see the eliminated variables (`fullC_dropAll`), so each eliminated value
is `−Dinv_c(rest_c(dropAll B))` with `‖Dinv_c v‖ = ell³‖v‖`, giving
`‖B(b₀ c)‖² ≤ ell⁶ · bondEnergy (dropAll B)` (§9b). Summing the termwise bound over all bonds gives
§9c.

**⚠ THE CONSTANT IS NOT EXTENT-FREE, AND THAT IS THE POINT.** p.428 asks for `γ₀ > 0` "*independent
of `k` and `U`*"; a backward transfer through THIS `κ` yields `γ/κ` with `κ` growing like the
volume, so it does NOT deliver a uniform descent. What is closed here is the EXISTENCE of the
bridge, i.e. that the change of variables is a norm equivalence on each fixed lattice; what remains
open is the SHARP constant. The sharp bound `κ = 1 + ell³` follows from the read-multiplicity count
"each fine bond is read by at most `ell` coarse bonds" — the crude step replaced here is
`‖f b‖² ≤ bondEnergy f` used once per bond instead of once per read. ~~That count is not proved here;
it is the residual `[CSTAR-UPPER-BRIDGE-SHARP]`, and it is a counting statement about
`ReadsBond`, not an analytic one.~~

**[S75 STRIKE 2026-08-02, install lane `compute/conjunct_install/`. THE RESIDUAL IS CLOSED, and
the struck sentence was wrong on BOTH of its factual assertions — recorded because the error is
the reusable part.**
* *"That count is not proved here"* — it was not proved in THIS module, but it WAS already proved
  elsewhere in this tree when the sentence was written: `RegularUQChain.sum_coarse_Sblk_eq` (as an
  EQUALITY) and, independently routed, `QCLMNorm.multiplicity_exact`. This module imports neither.
  A de-correlated gate (`compute/kimi_cstar/VERDICT.md`) independently affirmed the ingredient was
  absent. Both were wrong; the reuse grep was never run before the residual was filed.
* *"it is a counting statement about `ReadsBond`, not an analytic one"* — the count was the part
  already in hand. What was actually missing was the ASSEMBLY: running `norm_dropped_le`'s
  derivation against the LOCAL Cauchy–Schwarz bound (`ell⁶ · ell⁻⁴ = ell²` against `c`'s own read
  set) and summing over the DROPPED bonds only, indexed by `c : CoarseBond L ell` rather than over
  all `|Bond L|` bonds.

The proof is `Balaban/SharpUpperBridge.lean`: `norm_sq_dropped_le_sharp`,
`bondEnergy_le_dropAll_add_dropped`, `isUpperBridge_sharp`. What "sharp" does and does not mean
there: `1 + ell³` is ACHIEVED and sits above a PROVED floor of `1` (`bridge_const_ge_one`, for
`2 ≤ ell`); it is NOT proved least. At `ell = 1` there is no floor at all and that is a theorem
(`isUpperBridge_one_free`).]** -/

/-- Zeroing one component lowers the energy. -/
theorem bondEnergy_dropZero_le (b₀ : Bond L) (B : Bond L → SuTwo) :
    bondEnergy (dropZero b₀ B) ≤ bondEnergy B := by
  unfold bondEnergy
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [dropZero_apply]
  by_cases h : b = b₀
  · rw [if_pos h, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _
  · rw [if_neg h]

/-- Every bond value is bounded by the square root of the total energy. -/
theorem norm_le_sqrt_bondEnergy (B : Bond L → SuTwo) (b : Bond L) :
    ‖B b‖ ≤ Real.sqrt (bondEnergy B) := by
  have hsq : ‖B b‖ ^ 2 ≤ bondEnergy B :=
    Finset.single_le_sum (f := fun e : Bond L => ‖B e‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

/-! ### §9a — `Q_ell` is an average: a pointwise sup bound -/

/-- **`‖(Q_ell f)(c)‖ ≤ √(bondEnergy f)`**, for every background, every compatible torus and every
coarse bond. The `ell⁴` summands each have norm `≤ √(bondEnergy f)` (`RMap` is an isometry) against
the prefactor `1/ell⁴`. -/
theorem norm_lineCoarseRestrictCov_le {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (f : Bond L → SuTwo) (c : CoarseBond L ell) :
    ‖lineCoarseRestrictCov U ell f c‖ ≤ Real.sqrt (bondEnergy f) := by
  have hcard : (blockOf c.1.1 ell).card = ell ^ 3 :=
    AdalyFormal.Balaban.BlockedGauge.card_blockOf hell hdvd c.1.2
  have hellR : (0 : ℝ) < (ell : ℝ) := Nat.cast_pos.mpr hell
  -- each inner term is bounded
  have hterm : ∀ x ∈ blockOf c.1.1 ell,
      ‖AdalyFormal.Balaban.Q1Real.rZeroA U c.1.1 x f c.2 ell‖
        ≤ (ell : ℝ) * Real.sqrt (bondEnergy f) := by
    intro x _
    unfold AdalyFormal.Balaban.Q1Real.rZeroA
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ (Real.sqrt (bondEnergy f)) ?_) ?_
    · intro i _
      rw [AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
      exact norm_le_sqrt_bondEnergy f _
    · rw [Finset.card_range, nsmul_eq_mul]
  -- assemble
  have hsum : ‖∑ x ∈ blockOf c.1.1 ell, AdalyFormal.Balaban.Q1Real.rZeroA U c.1.1 x f c.2 ell‖
      ≤ (ell : ℝ) ^ 3 * ((ell : ℝ) * Real.sqrt (bondEnergy f)) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans
      (Finset.sum_le_card_nsmul _ _ ((ell : ℝ) * Real.sqrt (bondEnergy f)) hterm) ?_
    rw [hcard, nsmul_eq_mul, Nat.cast_pow]
  unfold lineCoarseRestrictCov
  rw [norm_smul]
  have habs : ‖(1 / (ell : ℝ) ^ 4 : ℝ)‖ = 1 / (ell : ℝ) ^ 4 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [habs]
  have hpref : (0 : ℝ) ≤ 1 / (ell : ℝ) ^ 4 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hpref) (le_of_eq ?_)
  have hne : ((ell : ℝ)) ≠ 0 := ne_of_gt hellR
  field_simp

/-! ### §9b — the eliminated value, bounded -/

/-- **`‖B(b₀ c)‖ ≤ ell³ · √(bondEnergy (dropAll B))`** on the constraint locus. -/
theorem norm_dropped_le {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0)
    (c : CoarseBond L ell) :
    ‖B (droppedBondLast ell c)‖ ≤ (ell : ℝ) ^ 3 * Real.sqrt (bondEnergy (dropAll ell B)) := by
  have hself : fullC U ell (dinvC U ell) B = B :=
    fullC_eq_self_of_mem_kerQ' hell hdvd U (dinvC U ell) (dinvC_hinv hell hdvd U) B hB
  have hval : B (droppedBondLast ell c)
      = -(dinvC U ell c (restFunctional U ell c (droppedBondLast ell c) (dropAll ell B))) := by
    conv_lhs => rw [← hself, ← fullC_dropAll hell hdvd U (dinvC U ell) B]
    rw [fullC_dropped hell hdvd U (dinvC U ell) _ c]
    rfl
  have hrest : ‖restFunctional U ell c (droppedBondLast ell c) (dropAll ell B)‖
      ≤ Real.sqrt (bondEnergy (dropAll ell B)) := by
    have hEq : restFunctional U ell c (droppedBondLast ell c) (dropAll ell B)
        = lineCoarseRestrictCov U ell
            (dropZero (droppedBondLast ell c) (dropAll ell B)) c := rfl
    rw [hEq]
    refine le_trans (norm_lineCoarseRestrictCov_le hell hdvd U _ c) ?_
    exact Real.sqrt_le_sqrt (bondEnergy_dropZero_le _ _)
  have hDinv : ∀ v : SuTwo, ‖dinvC U ell c v‖ = (ell : ℝ) ^ 3 * ‖v‖ := by
    intro v
    show ‖(((ell : ℝ) ^ 3) • AdalyFormal.Balaban.CovariantOperators.RMap
      (AdalyFormal.Balaban.FullReparamC.dropTransport U ell c)⁻¹) v‖ = _
    rw [LinearMap.smul_apply, norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hval, norm_neg, hDinv]
  exact mul_le_mul_of_nonneg_left hrest (by positivity)

/-! ### §9c — the bridge -/

/-- The bridge constant: `1 + |bonds| · ell⁶`. Extent-DEPENDENT — see §9's warning. -/
noncomputable def upperBridgeConst (L : PeriodicLatticeExtent) (ell : ℕ) : ℝ :=
  1 + (Fintype.card (Bond L) : ℝ) * (ell : ℝ) ^ 6

theorem upperBridgeConst_pos (L : PeriodicLatticeExtent) (ell : ℕ) :
    0 < upperBridgeConst L ell := by
  unfold upperBridgeConst
  have : (0 : ℝ) ≤ (Fintype.card (Bond L) : ℝ) * (ell : ℝ) ^ 6 := by positivity
  linarith

/-- **`[CSTAR-UPPER-BRIDGE]` HOLDS**, for every `ell > 0`, every compatible torus and every
background, at `κ = upperBridgeConst`. -/
theorem isUpperBridge_holds {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) :
    IsUpperBridge ell U (upperBridgeConst L ell) := by
  intro B hB
  have hEnn : 0 ≤ bondEnergy (dropAll ell B) := bondEnergy_nonneg' _
  have hpt : ∀ b : Bond L,
      ‖B b‖ ^ 2 ≤ ‖dropAll ell B b‖ ^ 2 + (ell : ℝ) ^ 6 * bondEnergy (dropAll ell B) := by
    intro b
    by_cases h : IsDropped ell b
    · obtain ⟨c, rfl⟩ := h
      have hb := norm_dropped_le hell hdvd U B hB c
      have h0 : (0 : ℝ) ≤ ‖B (droppedBondLast ell c)‖ := norm_nonneg _
      have hsq : ‖B (droppedBondLast ell c)‖ ^ 2
          ≤ ((ell : ℝ) ^ 3 * Real.sqrt (bondEnergy (dropAll ell B))) ^ 2 := by
        nlinarith [hb, h0]
      have hsq2 : ((ell : ℝ) ^ 3 * Real.sqrt (bondEnergy (dropAll ell B))) ^ 2
          = (ell : ℝ) ^ 6 * bondEnergy (dropAll ell B) := by
        rw [mul_pow, Real.sq_sqrt hEnn]; ring
      rw [hsq2] at hsq
      have hz : (0 : ℝ) ≤ ‖dropAll ell B (droppedBondLast ell c)‖ ^ 2 := sq_nonneg _
      linarith
    · rw [dropAll_of_free B h]
      have hz : (0 : ℝ) ≤ (ell : ℝ) ^ 6 * bondEnergy (dropAll ell B) := by positivity
      linarith
  have hsum : bondEnergy B
      ≤ bondEnergy (dropAll ell B)
        + (Fintype.card (Bond L) : ℝ) * ((ell : ℝ) ^ 6 * bondEnergy (dropAll ell B)) := by
    have h2 : bondEnergy B
        ≤ ∑ b : Bond L,
            (‖dropAll ell B b‖ ^ 2 + (ell : ℝ) ^ 6 * bondEnergy (dropAll ell B)) := by
      exact Finset.sum_le_sum (fun b _ => hpt b)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    exact h2
  have hconst : upperBridgeConst L ell * bondEnergy (dropAll ell B)
      = bondEnergy (dropAll ell B)
        + (Fintype.card (Bond L) : ℝ) * ((ell : ℝ) ^ 6 * bondEnergy (dropAll ell B)) := by
    unfold upperBridgeConst; ring
  rw [hconst]
  exact hsum

/-- **THE BACKWARD TRANSFER, UNCONDITIONAL ON EACH LATTICE.** With §9's bridge discharged, a
`C`-sandwich coercivity in the free coordinates DESCENDS to a coercivity on the (3.156) constraint
locus, with constant `γ / (1 + |bonds|·ell⁶)`. Together with `sandwich_of_restricted` this closes
the loop: on a FIXED lattice the two statements are equivalent up to that factor.

**The factor is the whole story.** It grows with the volume, so THIS theorem does NOT deliver
p.428's `k`-independent descent; ~~`[CSTAR-UPPER-BRIDGE-SHARP]` (§9) is what would.~~
**[S75 2026-08-02, install lane: `[CSTAR-UPPER-BRIDGE-SHARP]` is PROVED and the extent-free
descent EXISTS — `Balaban.SharpUpperBridge.restricted_of_sandwich_sharp` is this same statement
with `κ = 1 + ell³`, and `SharpUpperBridge.coercivity_volume_free` carries it to the (3.156)
constraint locus at general `ell` with no extent in the constant. THIS declaration is unchanged
and its constant is still volume-dependent; the sentence is struck because "what would" implies
nothing does.]** -/
theorem restricted_of_sandwich_unconditional {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (Dinv : CoarseBond L ell → (SuTwo →ₗ[ℝ] SuTwo))
    (hinv : ∀ c : CoarseBond L ell,
      (coeffDc U ell c (droppedBondLast ell c)).comp (Dinv c) = LinearMap.id)
    (q : (Bond L → SuTwo) → ℝ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hsand : ∀ Btil : Bond L → SuTwo, γ * bondEnergy Btil ≤ q (fullC U ell Dinv Btil))
    (B : Bond L → SuTwo) (hB : ∀ c : CoarseBond L ell, lineCoarseRestrictCov U ell B c = 0) :
    (γ / upperBridgeConst L ell) * bondEnergy B ≤ q B :=
  restricted_of_sandwich_at_fullC hell hdvd U Dinv hinv (upperBridgeConst_pos L ell)
    (isUpperBridge_holds hell hdvd U) q hγ hsand B hB

/-! ### §9d — TAG COMPLETENESS: `#print axioms` on EVERY declaration of this module

The nested validator (OPS-11) measured a coverage gap of 13 declarations on the first pass. Closed
here: every `theorem` and every `def` below carries a print, including the three `Prop`-valued
definitions and the four data definitions, so the file's own output is the complete audit. -/

#print axioms bondEnergy_nonneg'
#print axioms bondEnergy_zero
#print axioms dropAll
#print axioms dropAll_of_dropped
#print axioms dropAll_of_free
#print axioms witY
#print axioms witBtil
#print axioms witL7_two
#print axioms witY_coarse
#print axioms IsUpperBridge
#print axioms IsRegionSupported
#print axioms CovariantCLandsInFlatKernel
#print axioms upperBridgeConst
#print axioms bondEnergy_dropZero_le
#print axioms norm_le_sqrt_bondEnergy
#print axioms norm_lineCoarseRestrictCov_le
#print axioms norm_dropped_le
#print axioms upperBridgeConst_pos
#print axioms isUpperBridge_holds
#print axioms restricted_of_sandwich_unconditional
#print axioms bondEnergy_single_pos
#print axioms dropAll_hdrop
#print axioms bondEnergy_dropAll_le
#print axioms linv_of_rinv
#print axioms constraintFunctional_split
#print axioms fullC_eq_self_of_mem_kerQ
#print axioms fullC_eq_self_of_mem_kerQ'
#print axioms fullC_idem
#print axioms fullC_dropAll
#print axioms fullC_surjective_onto_kerQ
#print axioms fullC_injective_on_free
#print axioms dropAll_axial
#print axioms subspace156_eq_range_C
#print axioms pAx_fullC_eq_zero
#print axioms penalty_eq_bare_on_range
#print axioms sandwich_of_restricted
#print axioms restricted_of_sandwich
#print axioms cStarDeltaK_bound_transported
#print axioms cStarDeltaK_sandwich
#print axioms witBtil_axial
#print axioms witBtil_hdrop
#print axioms witBtil_energy_pos
#print axioms cStarDeltaK_sandwich_nonvacuous
#print axioms cStarDeltaK_sandwich_pos
#print axioms two_deltas_separate
#print axioms range_C_subset_door_domain
#print axioms cRestriction_strictly_stronger
#print axioms sandwich_content_free_above_threshold
#print axioms restricted_of_sandwich_at_fullC
#print axioms region_clause_vacuous_on_torus
#print axioms covariantCLandsInFlatKernel_at_trivial

end AdalyFormal.Balaban.CStarReconciliation

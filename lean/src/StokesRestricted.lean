/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.VariationalProjectorH1
import StokesOneSided

set_option autoImplicit false

/-!
# `[STOKES-COMM-U]` — THE NEAR-CIRCULARITY IS AN ARTIFACT OF THE DOMAIN

## The recorded resistance point

`Balaban/ThirdLevelSchurGap.lean` §4 records `[STOKES-COMM-U]`'s stop as follows: the general-`U`
Stokes error is reachable only in the form `O(α₁·√bondEnergy(A)) = O(α₁·‖A‖)`; converting it to
`O(α₁·‖D_U A‖)` is a **reverse Poincaré on the fibre**, itself a coercivity statement — so the proof
of the coercivity floor would consume a coercivity statement. That is the "near-circularity".

`StokesOneSided.lean` §4 sharpened the price: the conversion is exactly a **Poincaré inequality with
mean**, `‖A‖² ≤ K₁‖dA‖² + K₂‖QA‖²`, and `not_meanPoincare_of_kernel` proves that inequality FALSE for
every `K₁, K₂` as soon as `ker d ∩ ker Q ≠ 0`.

## What this file proves

**The cycle is route-specific, and the route is the QUANTIFIER, not the mathematics.**

`Gamma1ChainMap.interp_energy_of_chain` STATES its chain hypothesis as `∀ A : Hs`, but its proof
(lines 60–64) instantiates it at exactly one point, `A := solutionOperator D B`; and its own consumer
`gamma_floor_from_interp_and_poincare` needs it only for `B` in `range C₀`.  So the fact actually
consumed by the floor is a bound on `A` ranging over `range (solutionOperator D)`, never over `Hs`.

On that smaller domain three things happen, and each is proved below.

* **§2 — the obstruction of `StokesOneSided` §4 CANNOT BE INSTANTIATED.**  `ker Q ∩ range H₁ = 0`:
  if `A = H₁B` and `Q A = 0` then `B = Q A = 0` and hence `A = H₁ 0 = 0`.  The hypothesis of
  `not_meanPoincare_of_kernel` — a NONZERO vector killed by both `d` and `Q` — has no instance among
  minimizers, for ANY `d` whatsoever.  This is not "the obstruction is hard to meet"; it is
  `no_kernel_witness_among_minimizers`, a theorem that it is unmeetable.

* **§3 — the conversion the cycle was about is FREE on that domain, and it is not a Poincaré
  inequality at all.**  `meanPoincare_at_minimizer` proves `‖A‖² ≤ 0·‖dA‖² + ‖H₁‖²‖B‖²` — with
  `K₁ = 0`.  The proof is `ContinuousLinearMap.le_opNorm`: `solutionOperator D` is a **bounded
  operator by type** (`VariationalProjectorH1.solutionOperator : K →L[ℝ] H`, definition
  `G_star ∘ Q* ∘ (QG_starQ*)⁻¹`).  No reverse Poincaré, no coercivity, no smallness.

* **§4/§5 — consequently the floor follows from the RAW drift bound**, the `‖A‖`-measured one the
  tree can already produce, with no reverse Poincaré anywhere in the derivation:
  `gamma_floor_at_minimizer` gives `(γ_P − 2κ²)/(2σ₀²)` with `κ = c·‖H₁‖`.
  **INPUT BILLING (added 2026-08-12, S75 propagation of the strike inside `perturbed_chain_at_minimizer`).**
  "No reverse Poincaré" is not "no input beyond boundedness": §4 and §5 BOTH consume the datum's
  exact-interpolation field `interpolates D B : Q(H₁B) = B` in addition to boundedness of `H₁`.  That
  field is packaged data in the abstract statements here and is DISCHARGED at the constructed datum
  `compute/g1_datum/stage/G1Datum.lean:318`.  The full billing is inside
  `perturbed_chain_at_minimizer`'s docstring; read it before quoting §4/§5's inputs anywhere.

## WHAT THIS DOES **NOT** DO — read before consuming

Breaking the cycle is not closing the lemma.  `κ = c·‖H₁‖` and the floor is positive only when
`2κ² < γ_P` (§5, a proved dichotomy, not a decoration).  So the residual is now a **quantitative**
one: an UPPER bound on `‖H₁‖ = ‖G_star Q* (QG_starQ*)⁻¹‖`, uniform in `k` and `L`, against
`γ_P = (1/180)·ℓ⁻⁵`.  §6 proves this is a bound on `(QG_starQ*)⁻¹` from ABOVE, i.e. the `hG2`-shaped
input, which `Gamma1Reduction` §6 proves is a DIFFERENT fact from `γ₁` — opposite-direction bounds on
the same composite, neither implying the other.  **That is why the result is a break and not a
relabelling: the input needed sits on the opposite side of the operator from the conclusion, so
consuming it cannot be circular.**  It is nonetheless UNPROVED, and nothing here asserts a value for
`‖H₁‖`, for `c`, or for the resulting `γ₀`.

§7 gives the sharp refutation criterion on the restricted domain, and proves the criterion is
EMPTY wherever an exact chain map holds (so `U = 1` is consistent, as it must be).
§8 carries witnesses, including the free-parameter audit: `‖H₁‖` cannot be `0` (`§8`), so the
statement cannot be emptied by degenerating the operator whose norm carries the error.

Nothing here is installed in `formal/`; nothing enters `Spine.lean`'s import cone.
-/

namespace AdalyFormal.StokesCommu.Restricted

open AdalyFormal.Balaban.VariationalProjectorH1
open AdalyFormal.StokesCommu.OneSided

variable {Hs Ks P₁ P₂ : Type*} [NormedAddCommGroup Hs] [InnerProductSpace ℝ Hs]
  [NormedAddCommGroup Ks] [InnerProductSpace ℝ Ks]
  [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
  [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]

/-! ## §1 — the minimizer family, and its one defining property -/

/-- `Q A = 0` forces `A = 0` **among minimizers**.  `interpolates` says `Q(H₁B) = B`, so the coarse
field is recoverable from the fine one; a minimizer therefore cannot hide in `ker Q`. -/
theorem eq_zero_of_minimizer_of_Q_eq_zero (D : BalabanCovarianceData Hs Ks) (B : Ks)
    (h : D.Q (solutionOperator D B) = 0) : solutionOperator D B = 0 := by
  have hB : B = 0 := (interpolates D B).symm.trans h
  rw [hB, map_zero]

/-- **§2 — THE OBSTRUCTION IS UNMEETABLE ON THE CONSUMER'S DOMAIN.**  `StokesOneSided`'s
`not_meanPoincare_of_kernel` refutes the Poincaré-with-mean from a NONZERO `A₀` with `d A₀ = 0` and
`Q A₀ = 0`.  Among minimizers no such `A₀` exists — and note the statement is **independent of `d`**:
whatever the fine coboundary is, the second half of the obstruction's hypothesis already fails. -/
theorem no_kernel_witness_among_minimizers (D : BalabanCovarianceData Hs Ks) (B : Ks)
    (hne : solutionOperator D B ≠ 0) : D.Q (solutionOperator D B) ≠ 0 :=
  fun h => hne (eq_zero_of_minimizer_of_Q_eq_zero D B h)

/-! ## §3 — THE CONVERSION IS FREE: `K₁ = 0`, and the constant is an operator norm -/

/-- **THE CIRCULARITY-BREAKING FACT.**  The Poincaré-with-mean that `[STOKES-COMM-U]`'s conversion
needs holds on the minimizer family with `K₁ = 0` and `K₂ = ‖H₁‖²`, and its proof is
`ContinuousLinearMap.le_opNorm` — boundedness of `solutionOperator`, which is true BY TYPE.  It is
not a Poincaré inequality, not a coercivity statement, and carries no smallness hypothesis. -/
theorem meanPoincare_at_minimizer (D : BalabanCovarianceData Hs Ks) (d : Hs →L[ℝ] P₁) (B : Ks) :
    ‖solutionOperator D B‖ ^ 2
      ≤ 0 * ‖d (solutionOperator D B)‖ ^ 2 + ‖solutionOperator D‖ ^ 2 * ‖B‖ ^ 2 := by
  have hop : ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖B‖ :=
    (solutionOperator D).le_opNorm B
  have h0 : (0 : ℝ) ≤ ‖solutionOperator D B‖ := norm_nonneg _
  nlinarith [hop, h0]

/-! ## §4 — THE PERTURBED CHAIN BOUND, DERIVED FROM THE RAW DRIFT BOUND -/

/-- **THE BREAK, STATED AS THE STEP THE TREE COULD NOT TAKE.**  `hraw` is the general-`U` bound the
drift estimates deliver: the error measured against `‖A‖` (`√bondEnergy`), which is precisely the
form `[STOKES-COMM-U]` records as unusable.  Evaluated at the minimizer it becomes an error measured
against `‖B‖`, with coefficient `c·‖H₁‖`.

~~`The only input is boundedness of H₁.`~~  **STRUCK 2026-08-12 (S75, retained struck), SUPERSEDED
by the two paragraphs below.**  Convicted by the Sol secondary gate, `compute/sol_gate_stokes/VERDICT.md`
§3 / claim set (b).  The struck sentence is FALSE as a statement about THIS theorem: the proof's
first step is `hQA : D.Q (solutionOperator D B) = B := interpolates D B` (below), so the abstract
theorem also consumes EXACT INTERPOLATION `Q H₁ = id`.  Sol's failing input, which boundedness alone
does not exclude: on `Hs = Ks = ℝ` take `H₁ := 0`, `Q := 0`, `d := 0`, `d₁ := id`, `σ₀ = c = 0`,
`B := 1`.  Every operator there is bounded and `hraw` holds (`‖d₁(Q A)‖ = 0 ≤ 0` for all `A`), while
the conclusion reads `‖d₁ B‖ = 1 ≤ 0`.  What blocks that input is the datum's right-inverse field,
not boundedness.

**THE INPUTS, BILLED CORRECTLY.**  (i) boundedness of `H₁`, true BY TYPE
(`solutionOperator D : Ks →L[ℝ] Hs`), used as `le_opNorm`; AND (ii) the EXACT-INTERPOLATION FIELD of
the covariance datum — `interpolates D B : D.Q (solutionOperator D B) = B`
(`AdalyFormal/Balaban/VariationalProjectorH1.lean:204`), which is a two-line unpacking of the
`BalabanCovarianceData` structure fields `Comp_eq` (`:182`) and `Comp_CompInv` (`:187`).  In the
ABSTRACT statement those two fields are PACKAGED AS INPUT DATA; they are not derived from
self-adjointness, positivity or boundedness.

**AT THE CONSTRUCTED DATUM, (ii) IS DISCHARGED RATHER THAN ASSUMED.**  `compute/g1_datum/` builds a
`BalabanCovarianceData` for the tree's real operators: `g1Data`
(`compute/g1_datum/stage/G1Datum.lean:318`) is `CovDataCtor.build`
(`compute/g1_datum/dep/CovDataCtor.lean:143`), and there the `Comp_CompInv` field is `invOf_right _ _`
— constructed from `GinvH_selfAdjoint`, `GinvH_posDef` and `QH_surjective` (`G1Datum.lean:297`, the
last-layer lift landing INSIDE the admissible subspace), all three theorems, none of them an
interpolation assumption.  `CovDataCtor.build_interpolates` (`:173`) is the resulting interpolation
statement carrying no undischarged field.  So the chain INSTANTIATED at `g1Data` consumes no
interpolation assumption; what it does consume there is boundedness of `H₁` (by type) together with
`g1Data`'s own lattice hypotheses `2 ≤ ell`, `∀ ν, ell < L ν + 1`, `∀ ν, ell ∣ (L ν + 1)`, `0 < a`.
The struck sentence named neither (ii) nor those hypotheses, and it was written about the abstract
theorem, where (ii) is genuinely an input.

Note the quantifier: `hraw` is `∀ A`, because that is what the drift estimate gives; the CONCLUSION
is at the minimizer, because that is all the consumer instantiates. -/
theorem perturbed_chain_at_minimizer (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (σ₀ c : ℝ) (hc : 0 ≤ c)
    (hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖) (B : Ks) :
    ‖d₁ B‖ ≤ σ₀ * ‖d (solutionOperator D B)‖ + (c * ‖solutionOperator D‖) * ‖B‖ := by
  have hQA : D.Q (solutionOperator D B) = B := interpolates D B
  have h := hraw (solutionOperator D B)
  rw [hQA] at h
  have hop : ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖B‖ :=
    (solutionOperator D).le_opNorm B
  nlinarith [h, hop, hc]

/-! ## §5 — THE FLOOR, WITH NO REVERSE POINCARÉ ANYWHERE IN ITS DERIVATION -/

/-- **THE ASSEMBLED FLOOR AT THE MINIMIZER.**  From the RAW (`‖A‖`-measured) drift bound, the
coarse Poincaré inequality, and curl-domination of `Kop`, with `κ := c·‖H₁‖`:

  `((γ_P − 2κ²)/(2σ₀²))·‖B‖² ≤ ⟪H₁B, Kop H₁B⟫`.

This is exactly the shape of `Gamma1Reduction.gamma_floor_from_interp_and_poincare`'s `hinterp`
(which is itself already minimizer-only), so it composes with that lane without widening.

**INPUT LIST COMPLETED 2026-08-12 (S75 propagation of the strike in `perturbed_chain_at_minimizer`).**
The three-item list in the first sentence is INCOMPLETE as written: this proof's first step is
`hQA : D.Q (solutionOperator D B) = B := interpolates D B`, and `hQA` is used three further times
below, so a FOURTH input is the datum's exact-interpolation field.  Nothing in the list is withdrawn;
the omission is repaired.  See `perturbed_chain_at_minimizer` for the full billing and for the
discharge of that field at the constructed datum. -/
theorem gamma_floor_at_minimizer (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (Kop : Hs →L[ℝ] Hs) (σ₀ c γP : ℝ)
    (hσ₀ : 0 < σ₀) (hc : 0 ≤ c)
    (hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖)
    (hpoin : ∀ B : Ks, γP * ‖B‖ ^ 2 ≤ ‖d₁ B‖ ^ 2)
    (hK : ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (B : Ks) :
    ((γP - 2 * (c * ‖solutionOperator D‖) ^ 2) / (2 * σ₀ ^ 2)) * ‖B‖ ^ 2
      ≤ (inner ℝ (solutionOperator D B) (Kop (solutionOperator D B)) : ℝ) := by
  have hQA : D.Q (solutionOperator D B) = B := interpolates D B
  have hκ : (0 : ℝ) ≤ c * ‖solutionOperator D‖ := mul_nonneg hc (norm_nonneg _)
  have key := gamma_floor_of_perturbed_chain D.Q d d₁ Kop σ₀ (c * ‖solutionOperator D‖) γP hσ₀ hκ
      (solutionOperator D B)
      (by rw [hQA]; exact perturbed_chain_at_minimizer D d d₁ σ₀ c hc hraw B)
      (by rw [hQA]; exact hpoin B)
      (hK (solutionOperator D B))
  rwa [hQA] at key

/-- **THE DICHOTOMY.**  The floor of §5 is positive exactly when `2κ² < γ_P`, and NONPOSITIVE as soon
as that fails — so the smallness condition is a real hypothesis, not decoration.  Both directions are
`StokesOneSided`'s, reused rather than rebuilt (LAW-19). -/
theorem floor_pos_iff_small (D : BalabanCovarianceData Hs Ks) (σ₀ c γP : ℝ) (hσ₀ : 0 < σ₀) :
    (2 * (c * ‖solutionOperator D‖) ^ 2 < γP →
        0 < (γP - 2 * (c * ‖solutionOperator D‖) ^ 2) / (2 * σ₀ ^ 2)) ∧
      (γP ≤ 2 * (c * ‖solutionOperator D‖) ^ 2 →
        (γP - 2 * (c * ‖solutionOperator D‖) ^ 2) / (2 * σ₀ ^ 2) ≤ 0) :=
  ⟨fun h => absorbed_constant_pos σ₀ (c * ‖solutionOperator D‖) γP hσ₀ h,
   fun h => absorbed_constant_nonpos σ₀ (c * ‖solutionOperator D‖) γP hσ₀ h⟩

/-! ## §6 — WHERE THE RESIDUAL NOW LIVES, AND WHY IT IS NOT THE SAME FACT AS `γ₁` -/

/-- **THE RESIDUAL, FACTORED.**  `‖H₁‖ ≤ ‖G_star‖·‖Q*‖·‖(QG_starQ*)⁻¹‖` — from the DEFINITION
`solutionOperator = Gstar ∘ Qstar ∘ CompInv`, so the smallness condition of §5 reduces to an
UPPER bound on `CompInv`, with the other two factors carried explicitly. -/
theorem norm_solutionOperator_le (D : BalabanCovarianceData Hs Ks) :
    ‖solutionOperator D‖ ≤ ‖D.Gstar‖ * (‖D.Qstar‖ * ‖D.CompInv‖) := by
  refine le_trans (ContinuousLinearMap.opNorm_comp_le D.Gstar (D.Qstar.comp D.CompInv)) ?_
  exact mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.opNorm_comp_le D.Qstar D.CompInv) (norm_nonneg _)

/-- **THE DIRECTION AUDIT, PROVED.**  What §5 needs from the composite is an UPPER bound on
`CompInv`; what `γ₁` asserts is a LOWER bound on `CompInv − a`.  Here is the mechanical reason they
cannot be the same fact: an upper bound of the form `‖CompInv y‖ ≤ M‖y‖` is CONSISTENT with a
positive lower bound (both hold for `CompInv = id`, `M = 1`, floor `1`), so assuming the former
cannot prove the latter false — and conversely a lower bound alone constrains nothing above.
This is the statement-level form of `Gamma1Reduction` §6's `comp_lower_holds_while_gamma_fails`. -/
theorem upper_and_lower_are_compatible :
    ∃ (T : ℝ →L[ℝ] ℝ), (∀ y : ℝ, ‖T y‖ ≤ 1 * ‖y‖) ∧ (∀ y : ℝ, 1 * ‖y‖ ^ 2 ≤ inner ℝ y (T y)) := by
  refine ⟨ContinuousLinearMap.id ℝ ℝ, fun y => by simp, fun y => ?_⟩
  simp only [ContinuousLinearMap.id_apply, one_mul]
  rw [real_inner_self_eq_norm_sq]

/-! ## §7 — THE SHARP REFUTATION CRITERION ON THE RESTRICTED DOMAIN -/

/-- **THE RESTRICTED CRITERION.**  What refutes the bound the consumer actually needs is not any old
Stokes defect, but a defect AT A MINIMIZER: a coarse field `B₀` whose cheapest interpolation has
vanishing fine curl while `B₀` itself has nonzero coarse curl.  Then no `σ` works. -/
theorem not_onesided_at_minimizers_of_defect (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (B₀ : Ks)
    (h0 : d (solutionOperator D B₀) = 0) (hne : d₁ B₀ ≠ 0) (σ : ℝ) :
    ¬ (∀ B : Ks, ‖d₁ B‖ ≤ σ * ‖d (solutionOperator D B)‖) := by
  intro h
  have hb := h B₀
  rw [h0, norm_zero, mul_zero] at hb
  exact hne (norm_le_zero_iff.mp hb)

/-- **THE CRITERION IS EMPTY WHEREVER AN EXACT CHAIN MAP HOLDS.**  So `U = 1` (`stokes_flat`) is
consistent with §7, as it must be: there the defect set is provably empty, which is exactly why the
flat case never needed any of this machinery. -/
theorem no_minimizer_defect_of_chain (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (S : P₁ →L[ℝ] P₂)
    (hchain : ∀ A : Hs, d₁ (D.Q A) = S (d A)) (B₀ : Ks)
    (h0 : d (solutionOperator D B₀) = 0) : d₁ B₀ = 0 := by
  have hQA : D.Q (solutionOperator D B₀) = B₀ := interpolates D B₀
  have h := hchain (solutionOperator D B₀)
  rw [hQA, h0, map_zero] at h
  exact h

/-! ## §8 — WITNESSES AND THE FREE-PARAMETER AUDIT -/

/-- **THE STATEMENT CANNOT BE EMPTIED BY DEGENERATING `H₁`.**  A reader may ask whether §5 is
vacuous through `‖H₁‖ = 0` (which would make `κ = 0` and the smallness free).  It is not: for any
nonzero coarse field, `1 ≤ ‖Q‖·‖H₁‖`.  So `H₁ = 0` forces the coarse space to be trivial, where
there is nothing to prove.  This is the "who chooses the parameter, and can that chooser empty the
statement" audit, discharged as a theorem rather than asserted. -/
theorem one_le_norm_Q_mul_norm_solutionOperator (D : BalabanCovarianceData Hs Ks) (B : Ks)
    (hB : B ≠ 0) : 1 ≤ ‖D.Q‖ * ‖solutionOperator D‖ := by
  have hQA : D.Q (solutionOperator D B) = B := interpolates D B
  have h1 : ‖B‖ ≤ ‖D.Q‖ * ‖solutionOperator D B‖ := by
    -- NOT `rw [← hQA]`: that rewrites the `B` inside `solutionOperator D B` too.
    have hle := D.Q.le_opNorm (solutionOperator D B)
    rwa [hQA] at hle
  have h2 : ‖solutionOperator D B‖ ≤ ‖solutionOperator D‖ * ‖B‖ :=
    (solutionOperator D).le_opNorm B
  have hBpos : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hQnn : (0 : ℝ) ≤ ‖D.Q‖ := norm_nonneg _
  nlinarith [h1, h2, hBpos, hQnn]

/-- The identity data on `ℝ`: every operator is `id`.  A genuine `BalabanCovarianceData`, used below
as the inhabitant. -/
noncomputable def wData : BalabanCovarianceData ℝ ℝ where
  Ginv := ContinuousLinearMap.id ℝ ℝ
  Gstar := ContinuousLinearMap.id ℝ ℝ
  Ginv_Gstar := fun _ => rfl
  Gstar_Ginv := fun _ => rfl
  Ginv_selfAdjoint := fun _ _ => rfl
  Ginv_posSemidef := fun x => real_inner_self_nonneg
  Q := ContinuousLinearMap.id ℝ ℝ
  Qstar := ContinuousLinearMap.id ℝ ℝ
  Q_Qstar_adjoint := fun _ _ => rfl
  Comp := ContinuousLinearMap.id ℝ ℝ
  Comp_eq := fun _ => rfl
  CompInv := ContinuousLinearMap.id ℝ ℝ
  Comp_CompInv := fun _ => rfl
  CompInv_Comp := fun _ => rfl

/-- **INHABITANT.**  On `wData`, `H₁ = id`, so `‖H₁‖ ≥ 1`: the error coefficient `κ = c‖H₁‖` of §5 is
genuinely of size `c`, not silently zero.  Together with `one_le_norm_Q_mul_norm_solutionOperator`
this closes the free-parameter audit on `‖H₁‖`. -/
theorem witness_norm_solutionOperator_ge_one : 1 ≤ ‖solutionOperator wData‖ := by
  have h := one_le_norm_Q_mul_norm_solutionOperator wData (1 : ℝ) one_ne_zero
  have hQ : ‖wData.Q‖ ≤ 1 := by
    show ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hnn : (0 : ℝ) ≤ ‖solutionOperator wData‖ := norm_nonneg _
  nlinarith [h, hQ, hnn]

/-- **NON-INHABITANT of §7's criterion, i.e. the criterion is not vacuously unsatisfiable.**  With
`d = 0` and `d₁ = id` on `wData`, the minimizer defect EXISTS at `B₀ = 1`, and §7 refutes the
restricted one-sided bound for every `σ`.  So §7 has real content: the restricted domain does not by
itself rescue the bound — §3–§5 are needed, and they route around it rather than through it. -/
theorem witness_restricted_defect_exists (σ : ℝ) :
    ¬ (∀ B : ℝ, ‖(ContinuousLinearMap.id ℝ ℝ) B‖
        ≤ σ * ‖(0 : ℝ →L[ℝ] ℝ) (solutionOperator wData B)‖) := by
  refine not_onesided_at_minimizers_of_defect wData (0 : ℝ →L[ℝ] ℝ)
    (ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) (by simp) ?_ σ
  simp

/-- **JUNK SUBSTITUTION (S82) on the load-bearing hypothesis.**  Substituting a structurally invalid
`B = 0` collapses §5's conclusion to `0 ≤ ⟪H₁0, Kop H₁0⟫`, i.e. `0 ≤ 0`.  Recorded so that the
`B = 0` instance is never mistaken for content; `witness_norm_solutionOperator_ge_one` supplies the
non-degenerate point. -/
theorem junk_B_zero (D : BalabanCovarianceData Hs Ks) (σ₀ c γP : ℝ) :
    ((γP - 2 * (c * ‖solutionOperator D‖) ^ 2) / (2 * σ₀ ^ 2)) * ‖(0 : Ks)‖ ^ 2 = 0 := by
  simp

/-! ### §8b — THE TWO `FIRED-BAD` MUSTNOT CONTROLS, DISCHARGED AS THEOREMS (added 2026-08-12)

`MUTATION_RESULTS.tsv` row `C3` and `MUTATION_RESULTS2.tsv` row `C5` are MUSTNOT controls that
FIRED: each weakens a conclusion and the module then fails to compile.  Both re-ran identically in
the repair pass, so the readings are stable and are not flakiness.  A MUSTNOT control that fires
leaves an ambiguity the battery cannot settle by itself — is the mutant caught because it is FALSE,
or only because the proof script no longer goes through?  The two theorems below settle it inside
the kernel: each states the EXACT mutated conclusion and proves it from the unmutated theorem.  So
both firings are PROOFSTRUCT (the proofs are `nlinarith` calls whose hint sets are tuned to the
literal goal), and neither mutant is a false statement.  Nothing above is weakened; these are
additional consequences. -/

/-- **`C3`'s MUTANT IS A THEOREM.**  `MUTATION_RESULTS.tsv:C3` subtracts `1000` from §5's floor
coefficient — a genuine weakening, since `‖B‖² ≥ 0` — and the module stops compiling.  Here is that
exact statement, proved from `gamma_floor_at_minimizer`. -/
theorem gamma_floor_at_minimizer_weakened (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (Kop : Hs →L[ℝ] Hs) (σ₀ c γP : ℝ)
    (hσ₀ : 0 < σ₀) (hc : 0 ≤ c)
    (hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖)
    (hpoin : ∀ B : Ks, γP * ‖B‖ ^ 2 ≤ ‖d₁ B‖ ^ 2)
    (hK : ∀ A : Hs, ‖d A‖ ^ 2 ≤ (inner ℝ A (Kop A) : ℝ)) (B : Ks) :
    ((γP - 2 * (c * ‖solutionOperator D‖) ^ 2) / (2 * σ₀ ^ 2) - 1000) * ‖B‖ ^ 2
      ≤ (inner ℝ (solutionOperator D B) (Kop (solutionOperator D B)) : ℝ) := by
  have h := gamma_floor_at_minimizer D d d₁ Kop σ₀ c γP hσ₀ hc hraw hpoin hK B
  have hB : (0 : ℝ) ≤ ‖B‖ ^ 2 := sq_nonneg _
  nlinarith [h, hB]

/-- **`C5`'s MUTANT IS A THEOREM.**  `MUTATION_RESULTS2.tsv:C5` adds `1` to §4's error coefficient —
a genuine weakening, since `‖B‖ ≥ 0` — and the module stops compiling.  Here is that exact
statement, proved from `perturbed_chain_at_minimizer`. -/
theorem perturbed_chain_at_minimizer_weakened (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (σ₀ c : ℝ) (hc : 0 ≤ c)
    (hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + c * ‖A‖) (B : Ks) :
    ‖d₁ B‖ ≤ σ₀ * ‖d (solutionOperator D B)‖ + (c * ‖solutionOperator D‖ + 1) * ‖B‖ := by
  have h := perturbed_chain_at_minimizer D d d₁ σ₀ c hc hraw B
  have hB : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
  nlinarith [h, hB]

/-- **JUNK SUBSTITUTION (S82), the operator side.**  With `c = 0` the perturbed bound of §4
degenerates to the exact one-sided bound — so §4 is not silently assuming its own conclusion: at
`c = 0` there is no error to convert, and the theorem says exactly that. -/
theorem junk_c_zero (D : BalabanCovarianceData Hs Ks)
    (d : Hs →L[ℝ] P₁) (d₁ : Ks →L[ℝ] P₂) (σ₀ : ℝ)
    (hraw : ∀ A : Hs, ‖d₁ (D.Q A)‖ ≤ σ₀ * ‖d A‖ + 0 * ‖A‖) (B : Ks) :
    ‖d₁ B‖ ≤ σ₀ * ‖d (solutionOperator D B)‖ + 0 * ‖B‖ := by
  have h := perturbed_chain_at_minimizer D d d₁ σ₀ 0 le_rfl hraw B
  simpa using h

#print axioms eq_zero_of_minimizer_of_Q_eq_zero
#print axioms no_kernel_witness_among_minimizers
#print axioms meanPoincare_at_minimizer
#print axioms perturbed_chain_at_minimizer
#print axioms gamma_floor_at_minimizer
#print axioms floor_pos_iff_small
#print axioms norm_solutionOperator_le
#print axioms upper_and_lower_are_compatible
#print axioms not_onesided_at_minimizers_of_defect
#print axioms no_minimizer_defect_of_chain
#print axioms one_le_norm_Q_mul_norm_solutionOperator
#print axioms witness_norm_solutionOperator_ge_one
#print axioms witness_restricted_defect_exists
#print axioms junk_B_zero
#print axioms junk_c_zero
#print axioms gamma_floor_at_minimizer_weakened
#print axioms perturbed_chain_at_minimizer_weakened
-- TAG COMPLETION 2026-08-12 (repair pass): `wData` was declared but untagged (16 declared /
-- 15 tagged).
#print axioms wData

end AdalyFormal.StokesCommu.Restricted

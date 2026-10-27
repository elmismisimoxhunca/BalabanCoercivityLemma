/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.QcEquation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false

/-!
# `Claim18Repaired.lean` — Claim 18 with EVERY operator supplied, `d` and `L` TIED, and the
# transfer bound reduced to ONE equation on ONE named object

## What this module repairs, and what it does NOT do

`Spine.claim18_exists` (2026-07-27 carrier form) reads

```
∃ (C2 : Hfine →L[ℝ] Hfine) (Qc : Hfine →L[ℝ] H) (Qc_inv : H →L[ℝ] Hfine),
  Balaban.Claim18Carrier.Clauses L d Ccorr α₀ C2 Qc Qc_inv
```

with `L : ℝ`, `d : ℕ`, `Ccorr α₀ : ℝ` all FREE binders of the theorem and `Hfine`, `H` abstract.
Three defects are already established elsewhere and are NOT re-derived here:

1. `compute/claim18_carrier/carrier_attacks.lean`'s `carrier_clauses_land_by_linear_algebra` —
   the bundle is satisfiable at EVERY carrier pair with a dimension drop, by pure linear algebra.
2. `QcEquation.suppliedClauses_iff` — pinning `𝒬_c` by equation relocates the whole freedom onto
   `C⁽²⁾`; three conditions on `C⁽²⁾` alone remain.
3. `d` is bound with no hypothesis, and `Lreal` with only `1 ≤ Lreal`.

This module removes the *remaining* freedom that can be removed without inventing an object:

* **`𝒬_c` and `𝒬_c⁻¹` are SUPPLIED** — `QcEquation.qcOp` / `QcEquation.qcSection` (LAW-19 reuse,
  nothing rebuilt).
* **`d` is TIED to the lattice**: `latticeDim := Fintype.card (Fin 3)`, and `Fin 3` is literally
  the direction index of `PeriodicLatticeExtent = Fin 3 → ℕ` and of `Bond L = Site × Fin 3`. It is
  not a numeral chosen to make something come out; it is read off the carrier.
* **`Lreal` is TIED to the block scale** `ell`, the same `ell` that indexes `CoarseBondSpace L ell`.
* **`Ccorr` and `α₀` are GONE.** Clause 3 becomes the unconditional `‖𝒬_c‖ ≤ 1`
  (`QcEquation.qcOp_opNorm_le_one`), which is CMP98 p.36 (126)'s bound at zero background field and
  is a THEOREM about the supplied operator. There is therefore no `α₀ = 0` point at which the
  statement can be false, because there is no `α₀`.
* **`C⁽²⁾` is UNIVERSALLY quantified, at its SOURCE-FAITHFUL TYPE**, and is the only operator the
  statement still ranges over. It is not existentially bound: `TiedClauses L ell C2` is a predicate
  ON a given `C2`, and §4's `tiedClauses_iff` says exactly which `C2` satisfy it.

## The retyping of `C⁽²⁾`, and why it is the source's type and the tree's is not

CMP102-UV printed p.260 (`corpus/pages/CMP102-UV_p260.md`, VERBATIM block, the paragraph under
eq. (17)) prints:

> "There exists a unique solution `\tilde{D}` of this equation for `A` sufficiently small, and it
> is an analytic function of `A` with a Taylor expansion beginning with second order terms.
> Denoting the terms by `\tilde{D}^{(2)}(A)`, we have
> `Q\tilde{D}^{(2)}(A,c) = C^{(2)}(A,c)` …"

(Quoted in the corpus page's own LaTeX, character for character, rather than in a Unicode
re-rendering — a nested validator flagged that an earlier draft silently inserted a space between
`Q` and `\tilde{D}` that the source does not print. The page carries
`verification_status: single-read`, so per LAW-11's 2026-07-20 correction this is a STRONG LEAD and
not adjudicated ground truth; the page's own ANNOTATION lists the fine→coarse domain reading as one
of the three findings needing a second, de-correlated read.)

and the same page pins the domains: the average's output is indexed by a COARSE bond `c`
(`(QA)(c)`), its input `A` lives on the FINE bonds. Reading the two displayed arguments:

* `D̃⁽²⁾(A)` is a FINE field — it is a `D̃`, and `D̃(A,b,c)` is indexed by a fine bond `b`;
* `C⁽²⁾(A,c)` is a COARSE field — indexed by `c`;
* `Q\tilde{D}^{(2)}(A,c) = C^{(2)}(A,c)` therefore forces `C⁽²⁾ : fine → coarse` and `D̃⁽²⁾ : fine → fine`,
  with `D̃⁽²⁾ = 𝒬_c⁻¹ ∘ C⁽²⁾` (the section is exactly the "linear operator on `𝔤` acting on
  `C⁽²⁾(A,c)`" the same paragraph announces).

`Spine`/`Claim18Carrier` type `C2 : Hfine →L[ℝ] Hfine` and `Dtilde2 := C2 ∘L Qc_inv : H →L[ℝ] Hfine`
— a map whose DOMAIN is the coarse space. That is a different object: the source's `D̃⁽²⁾` eats a
fine configuration `A`. At the tree's typing the source's own equation `Q D̃⁽²⁾ = C⁽²⁾` cannot even
be written down (`qcOp ∘L (C2 ∘L qcSection)` is coarse → coarse, `C2` is fine → fine). At the typing
used here it is a THEOREM, `transfer_satisfies_source_equation`, and it is proved from
`QcEquation.qc_comp_section` alone. This is reported as a FACT about two encodings; it is not a
verdict on the spine, and nothing in `Spine.lean`'s `Gap2Output` is edited by this module.

## The measurement this module is built on

`qcSection` is a SCALED ISOMETRY with an exactly computed constant:
`‖𝒬_c⁻¹ F‖ = ell² ‖F‖` (§2, `qcSection_norm`). The count behind it: `lastLayerLift` places
`ell · F(c)` on every fine bond `(x, μ)` whose block corner is `c`'s corner and whose `μ`-offset
inside the block is `ell − 1`; there are `ell²` such sites in an `ell³` block, so
`‖lift F‖² = ell² · (ell)² · ‖F‖² = ell⁴ ‖F‖²`.

Consequently `‖𝒬_c⁻¹ ∘ C⁽²⁾‖ = ell² ‖C⁽²⁾‖` EXACTLY (§3), and Bałaban's constant at the tied
parameters is `ell^{d−1} = ell²` — the same number. So:

**Claim 18, with `𝒬_c`, `𝒬_c⁻¹` supplied and `d`, `L` tied, is EXACTLY `‖C⁽²⁾‖ = 1`.**

That is `tiedClauses_iff`. It is a genuine constraint (an operator can fail it — §5) and it is a
genuine reduction (a two-object product bound collapses to a one-object normalization), and it is
also the exact statement of what is still missing: this tree does not define `C⁽²⁾`, so it cannot
decide whether the intended object has norm `1`.

## Clause independence — DISCLOSED, because two clauses are redundant

An S82 garbage-substitution audit of the STATEMENT (not of a certificate) was run against
`TiedClausesAt`, and it found two of the seven clauses redundant. Recorded here rather than left
for a prosecutor to find:

* **Clause 2** (`Function.Injective (qcSection L ell)`) is implied by **clause 1** alone, for ANY
  pair of maps satisfying clause 1's equation — a left-invertible map is injective. It consumes no
  hypothesis beyond clause 1.
* **Clause 7** (`transfer L ell C2 ≠ 0`) is implied by **clauses 2 and 5** together (`1 ≤ ‖C2‖`
  forces `C2 ≠ 0`; injectivity of the section then forces `qcSection (C2 v) ≠ 0` for some `v`),
  again for any maps satisfying those clauses. (`tiedClausesAt_iff` happens to derive it by the
  different route of `transfer_opNorm`'s exact formula; the redundancy is there either way.)
* Clauses **1, 3, 4, 5, 6 are independent**: each is falsified by its own substitution — clause 1
  by any non-left-inverse pair, clause 3 by any operator of norm `> 1`, clause 4 by any injective
  substitute for `𝒬_c` (`ell = 1` is exactly that, `tied_empty_at_ell_one`), clauses 5/6 by any
  `C2` of the wrong norm (`tied_rejects_expansive`, `tied_with_bound_ell_is_empty`).

Both redundant clauses are RETAINED, because they are the clauses `Claim18Carrier.Clauses` carries
and dropping them would make the comparison between the two statements less direct — but they are
not evidence of anything, and no count in this module treats them as independent checks.

## Controls (§5), both directions

* MUST-FIRE. `untied_bound_admits_every_operator`: with `Lreal` and `d` left FREE — the binders
  `Spine.claim18_exists` actually has — the transfer bound is satisfiable for EVERY `C2`, however
  large its norm, by choosing `Lreal := ‖transfer‖ + 2`, `d := 2`. `tied_rejects_expansive`: the
  tied statement rejects every `C2` with `1 < ‖C2‖`. `control_pair` exhibits ONE operator that the
  untied bound admits and the tied bundle refuses.
* MUST-NOT-FIRE. `tied_satisfiable`: the tied bundle is inhabited (by the normalized supplied
  average), so it has not been over-constrained into vacuity.
* DEGENERATE POINTS. `tied_empty_at_ell_one` (`ell = 1`: the average is injective, clause 4 fails);
  `no_tiling_at_ell_zero` (`ell = 0` is not a tileable block scale at all); `d` and `Lreal` no
  longer exist as free binders; `Ccorr`/`α₀` no longer exist. `nat_sub_truncation_at_d_zero` and
  `rpow_at_d_zero_ne_one` exhibit the ℕ-subtraction trap the registry note recorded, side by side.

## §7 — the number is SECTION-DEPENDENT, and the source's own support gives a DIFFERENT one

The collapse above uses `QcEquation.qcSection`, which is an exact right inverse but is NOT supported
where the source says `\tilde{D}` is supported. §7 builds the `b₀(c)`-supported section instead —
`b0Section`, weight `ell³` on the single bond of `B(c)` contained in `c` — and proves it is ALSO an
exact right inverse of the same faithful average (`qc_comp_b0Section`), so the comparison is between
two admissible choices and not against a straw object. Measured there:

* `b0Section_norm` — `‖𝒬_c⁻¹_{b₀} F‖ = ell³ ‖F‖`; `section_norm_ratio` — the two sections differ by
  exactly a factor `ell`.
* `b0_bound_forces_C2_le_inv_ell` — at the `b₀` section, Bałaban's `‖D̃⁽²⁾‖ ≤ ell^{d−1}` reads
  `‖C⁽²⁾‖ ≤ 1/ell`, not `‖C⁽²⁾‖ ≤ 1`.
* `b0_tied_bundle_is_empty` — that is INCOMPATIBLE with the anti-shrink floor `1 ≤ ‖C⁽²⁾‖` for every
  `2 ≤ ell`, so the bundle at the `b₀` section is EMPTY.

Which clause loses is stated and not smoothed: the floor `1 ≤ ‖C⁽²⁾‖` is the CAMPAIGN's addition
(introduced to block the zero witness), the bound is BAŁABAN's. This module does not decide between
them — it measures that they conflict at the source-faithful section, and routes that to
statement-prosecution.

§4b's `claim18_bound_forces_C2_bound_any_section` is the section-INDEPENDENT residue of all this:
for ANY right inverse, Claim 18's bound forces `‖C⁽²⁾‖ ≤ ell²·‖𝒬_c‖`, hence `≤ √ell`
(`claim18_bound_forces_C2_sqrt_bound`). That much survives no matter which section is right.
-/

namespace AdalyFormal.Balaban.Claim18Repaired

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.LatticeOperators
open AdalyFormal.Balaban.LineIntegralAveraging
open AdalyFormal.Balaban.QcEquation
open AdalyFormal.Balaban.PoincareBridge
open ContinuousLinearMap

variable {L : PeriodicLatticeExtent}

/-! ## §1 — the fibre count: `ell²` last-layer sites per block, per direction -/

/-- Exactly one residue class in `Fin ell` is the last one. -/
theorem sum_fin_ite_last {ell : ℕ} (hell : 0 < ell) (C : ℝ) :
    (∑ a : Fin ell, if a.val = ell - 1 then C else 0) = C := by
  classical
  rw [Finset.sum_eq_single (⟨ell - 1, by omega⟩ : Fin ell)]
  · simp
  · intro b _ hb
    have hbv : b.val ≠ ell - 1 := fun h => hb (Fin.ext h)
    simp [hbv]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The cube slice count.** Fixing one of the three cube coordinates to its last value leaves
`ell²` cube points. Stated as a weighted sum so it plugs straight into the norm computation. -/
theorem sum_cube_slice {ell : ℕ} (hell : 0 < ell) (μ : Fin 3) (C : ℝ) :
    (∑ p : Cube ell, if cubeIdx p μ = ell - 1 then C else 0) = (ell : ℝ) ^ 2 * C := by
  classical
  have hcard : ((Fintype.card (Fin ell) : ℕ) : ℝ) = (ell : ℝ) := by
    rw [Fintype.card_fin]
  have hcases : ∀ ν : Fin 3, ν = 0 ∨ ν = 1 ∨ ν = 2 := by decide
  -- the two constant-sum steps, isolated so each case is three rewrites
  have hconstFin : ∀ (c : ℝ), (∑ _a : Fin ell, c) = (ell : ℝ) * c := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  have hconstProd : ∀ (c : ℝ), (∑ _q : Fin ell × Fin ell, c) = (ell : ℝ) ^ 2 * c := by
    intro c
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  rcases hcases μ with rfl | rfl | rfl
  · simp only [cubeIdx_zero]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun a _ => hconstProd (if a.val = ell - 1 then C else 0))]
    rw [← Finset.mul_sum, sum_fin_ite_last hell]
  · simp only [cubeIdx_one]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ _a : Fin ell,
        (∑ q : Fin ell × Fin ell, if q.1.val = ell - 1 then C else 0)
          = (ell : ℝ) * C := by
      intro _
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_congr rfl (fun b _ => hconstFin (if b.val = ell - 1 then C else 0))]
      rw [← Finset.mul_sum, sum_fin_ite_last hell]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), hconstFin]
    ring
  · simp only [cubeIdx_two]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ _a : Fin ell,
        (∑ q : Fin ell × Fin ell, if q.2.val = ell - 1 then C else 0)
          = (ell : ℝ) * C := by
      intro _
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_congr rfl (fun _b _ => sum_fin_ite_last (ell := ell) hell C)]
      rw [hconstFin]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), hconstFin]
    ring

/-- **The block count, in the coordinates the lift actually uses.** Inside the block of a coarse
corner `y`, the fine sites whose `μ`-coordinate has residue `ell − 1` number exactly `ell²`. -/
theorem sum_block_lastLayer {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) (C : ℝ) :
    (∑ x ∈ blockOf y ell, if (x μ).val % ell = ell - 1 then C else 0) = (ell : ℝ) ^ 2 * C := by
  classical
  have hfit := coarseLattice_fits hdvd hy
  rw [sum_block_eq_cube hfit]
  have hy0 := (mem_CoarseLattice.mp hy) μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy0
  have hcong : ∀ p : Cube ell,
      (if ((chart y ell p) μ).val % ell = ell - 1 then C else 0)
        = (if cubeIdx p μ = ell - 1 then C else 0) := by
    intro p
    have h1 : ((chart y ell p) μ).val = (y μ).val + cubeIdx p μ := chart_val hfit p μ
    have h2 : ((y μ).val + cubeIdx p μ) % ell = cubeIdx p μ := by
      rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (cubeIdx_lt p μ)]
    have hP : (((chart y ell p) μ).val % ell = ell - 1) ↔ (cubeIdx p μ = ell - 1) := by
      rw [h1, h2]
    exact if_congr hP rfl rfl
  rw [Finset.sum_congr rfl (fun p _ => hcong p)]
  exact sum_cube_slice hell μ C

/-- Exactly one residue class in `Fin ell` is the first one. -/
theorem sum_fin_ite_zero {ell : ℕ} (hell : 0 < ell) (C : ℝ) :
    (∑ a : Fin ell, if a.val = 0 then C else 0) = C := by
  classical
  rw [Finset.sum_eq_single (⟨0, hell⟩ : Fin ell)]
  · simp
  · intro b _ hb
    have hbv : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [hbv]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A sum over the cube of a product of one-coordinate factors factorises. Used three times below
(once per direction), so the direction case split happens ONCE, here at the level of the algebra,
instead of once per lemma. -/
theorem sum_cube_factor {ell : ℕ} (A B D : Fin ell → ℝ) :
    (∑ p : Cube ell, A p.1 * B p.2.1 * D p.2.2)
      = (∑ a : Fin ell, A a) * (∑ b : Fin ell, B b) * (∑ c : Fin ell, D c) := by
  classical
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a : Fin ell,
      (∑ q : Fin ell × Fin ell, A a * B q.1 * D q.2)
        = A a * ((∑ b : Fin ell, B b) * (∑ c : Fin ell, D c)) := by
    intro a
    rw [Fintype.sum_prod_type]
    have h2 : ∀ b : Fin ell,
        (∑ c : Fin ell, A a * B b * D c) = A a * B b * (∑ c : Fin ell, D c) :=
      fun b => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul]
  ring

/-- The `ell` cube points ON the coarse axis through the corner, in direction `μ`. -/
theorem sum_cube_axis {ell : ℕ} (hell : 0 < ell) (μ : Fin 3) (C : ℝ) :
    (∑ p : Cube ell, if (∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) then C else 0)
      = (ell : ℝ) * C := by
  classical
  have hcases : ∀ ν : Fin 3, ν = 0 ∨ ν = 1 ∨ ν = 2 := by decide
  have hone : (∑ _a : Fin ell, (1 : ℝ)) = (ell : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, mul_one]
  have hind : (∑ a : Fin ell, if a.val = 0 then (1 : ℝ) else 0) = 1 := sum_fin_ite_zero hell 1
  have hindC : (∑ a : Fin ell, (if a.val = 0 then (1 : ℝ) else 0) * C) = C := by
    rw [← Finset.sum_mul, hind, one_mul]
  have hconstC : (∑ _a : Fin ell, C) = (ell : ℝ) * C := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  rcases hcases μ with rfl | rfl | rfl
  · have hfac : ∀ p : Cube ell,
        (if (∀ ν : Fin 3, ν ≠ (0 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (1 : ℝ) * (if p.2.1.val = 0 then (1 : ℝ) else 0)
              * ((if p.2.2.val = 0 then (1 : ℝ) else 0) * C) := by
      intro p
      have hP : (∀ ν : Fin 3, ν ≠ (0 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.2.1.val = 0 ∧ p.2.2.val = 0) := by
        constructor
        · intro h
          exact ⟨by rw [← cubeIdx_one]; exact h 1 (by decide),
                 by rw [← cubeIdx_two]; exact h 2 (by decide)⟩
        · rintro ⟨h1, h2⟩ ν hν
          rcases hcases ν with rfl | rfl | rfl
          · exact absurd rfl hν
          · rw [cubeIdx_one]; exact h1
          · rw [cubeIdx_two]; exact h2
      rw [if_congr hP rfl rfl]
      by_cases h1 : p.2.1.val = 0 <;> by_cases h2 : p.2.2.val = 0 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun _ : Fin ell => (1 : ℝ))) (B := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0))
        (D := fun c : Fin ell => (if c.val = 0 then (1 : ℝ) else 0) * C),
      hone, hind, hindC]
    ring
  · have hfac : ∀ p : Cube ell,
        (if (∀ ν : Fin 3, ν ≠ (1 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (if p.1.val = 0 then (1 : ℝ) else 0) * (1 : ℝ)
              * ((if p.2.2.val = 0 then (1 : ℝ) else 0) * C) := by
      intro p
      have hP : (∀ ν : Fin 3, ν ≠ (1 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.1.val = 0 ∧ p.2.2.val = 0) := by
        constructor
        · intro h
          exact ⟨by rw [← cubeIdx_zero]; exact h 0 (by decide),
                 by rw [← cubeIdx_two]; exact h 2 (by decide)⟩
        · rintro ⟨h1, h2⟩ ν hν
          rcases hcases ν with rfl | rfl | rfl
          · rw [cubeIdx_zero]; exact h1
          · exact absurd rfl hν
          · rw [cubeIdx_two]; exact h2
      rw [if_congr hP rfl rfl]
      by_cases h1 : p.1.val = 0 <;> by_cases h2 : p.2.2.val = 0 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0)) (B := (fun _ : Fin ell => (1 : ℝ)))
        (D := fun c : Fin ell => (if c.val = 0 then (1 : ℝ) else 0) * C),
      hone, hind, hindC]
    ring
  · have hfac : ∀ p : Cube ell,
        (if (∀ ν : Fin 3, ν ≠ (2 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (if p.1.val = 0 then (1 : ℝ) else 0)
              * (if p.2.1.val = 0 then (1 : ℝ) else 0) * C := by
      intro p
      have hP : (∀ ν : Fin 3, ν ≠ (2 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.1.val = 0 ∧ p.2.1.val = 0) := by
        constructor
        · intro h
          exact ⟨by rw [← cubeIdx_zero]; exact h 0 (by decide),
                 by rw [← cubeIdx_one]; exact h 1 (by decide)⟩
        · rintro ⟨h1, h2⟩ ν hν
          rcases hcases ν with rfl | rfl | rfl
          · rw [cubeIdx_zero]; exact h1
          · rw [cubeIdx_one]; exact h2
          · exact absurd rfl hν
      rw [if_congr hP rfl rfl]
      by_cases h1 : p.1.val = 0 <;> by_cases h2 : p.2.1.val = 0 <;> simp [h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0)) (B := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0)) (D := fun _ : Fin ell => C),
      hind, hconstC]
    ring

/-- **Exactly ONE `b₀` cube point per block per direction**: last layer in `μ`, zero offset in the
other two. -/
theorem sum_cube_b0 {ell : ℕ} (hell : 0 < ell) (μ : Fin 3) (C : ℝ) :
    (∑ p : Cube ell,
        if (cubeIdx p μ = ell - 1 ∧ ∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) then C else 0) = C := by
  classical
  have hcases : ∀ ν : Fin 3, ν = 0 ∨ ν = 1 ∨ ν = 2 := by decide
  have hindL : (∑ a : Fin ell, if a.val = ell - 1 then (1 : ℝ) else 0) = 1 :=
    sum_fin_ite_last hell 1
  have hind : (∑ a : Fin ell, if a.val = 0 then (1 : ℝ) else 0) = 1 := sum_fin_ite_zero hell 1
  have hindC : (∑ a : Fin ell, (if a.val = 0 then (1 : ℝ) else 0) * C) = C := by
    rw [← Finset.sum_mul, hind, one_mul]
  have hindLC : (∑ a : Fin ell, (if a.val = ell - 1 then (1 : ℝ) else 0) * C) = C := by
    rw [← Finset.sum_mul, hindL, one_mul]
  rcases hcases μ with rfl | rfl | rfl
  · have hfac : ∀ p : Cube ell,
        (if (cubeIdx p (0 : Fin 3) = ell - 1 ∧
              ∀ ν : Fin 3, ν ≠ (0 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (if p.1.val = ell - 1 then (1 : ℝ) else 0)
              * (if p.2.1.val = 0 then (1 : ℝ) else 0)
              * ((if p.2.2.val = 0 then (1 : ℝ) else 0) * C) := by
      intro p
      have hP : (cubeIdx p (0 : Fin 3) = ell - 1 ∧
            ∀ ν : Fin 3, ν ≠ (0 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.1.val = ell - 1 ∧ p.2.1.val = 0 ∧ p.2.2.val = 0) := by
        constructor
        · rintro ⟨h0, h⟩
          exact ⟨by rw [← cubeIdx_zero]; exact h0,
                 by rw [← cubeIdx_one]; exact h 1 (by decide),
                 by rw [← cubeIdx_two]; exact h 2 (by decide)⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨by rw [cubeIdx_zero]; exact h0, fun ν hν => ?_⟩
          rcases hcases ν with rfl | rfl | rfl
          · exact absurd rfl hν
          · rw [cubeIdx_one]; exact h1
          · rw [cubeIdx_two]; exact h2
      rw [if_congr hP rfl rfl]
      by_cases h0 : p.1.val = ell - 1 <;> by_cases h1 : p.2.1.val = 0 <;>
        by_cases h2 : p.2.2.val = 0 <;> simp [h0, h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun a : Fin ell => if a.val = ell - 1 then (1 : ℝ) else 0)) (B := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0))
        (D := fun c : Fin ell => (if c.val = 0 then (1 : ℝ) else 0) * C),
      hindL, hind, hindC]
    ring
  · have hfac : ∀ p : Cube ell,
        (if (cubeIdx p (1 : Fin 3) = ell - 1 ∧
              ∀ ν : Fin 3, ν ≠ (1 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (if p.1.val = 0 then (1 : ℝ) else 0)
              * (if p.2.1.val = ell - 1 then (1 : ℝ) else 0)
              * ((if p.2.2.val = 0 then (1 : ℝ) else 0) * C) := by
      intro p
      have hP : (cubeIdx p (1 : Fin 3) = ell - 1 ∧
            ∀ ν : Fin 3, ν ≠ (1 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.1.val = 0 ∧ p.2.1.val = ell - 1 ∧ p.2.2.val = 0) := by
        constructor
        · rintro ⟨h0, h⟩
          exact ⟨by rw [← cubeIdx_zero]; exact h 0 (by decide),
                 by rw [← cubeIdx_one]; exact h0,
                 by rw [← cubeIdx_two]; exact h 2 (by decide)⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨by rw [cubeIdx_one]; exact h1, fun ν hν => ?_⟩
          rcases hcases ν with rfl | rfl | rfl
          · rw [cubeIdx_zero]; exact h0
          · exact absurd rfl hν
          · rw [cubeIdx_two]; exact h2
      rw [if_congr hP rfl rfl]
      by_cases h0 : p.1.val = 0 <;> by_cases h1 : p.2.1.val = ell - 1 <;>
        by_cases h2 : p.2.2.val = 0 <;> simp [h0, h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0)) (B := (fun a : Fin ell => if a.val = ell - 1 then (1 : ℝ) else 0))
        (D := fun c : Fin ell => (if c.val = 0 then (1 : ℝ) else 0) * C),
      hind, hindL, hindC]
    ring
  · have hfac : ∀ p : Cube ell,
        (if (cubeIdx p (2 : Fin 3) = ell - 1 ∧
              ∀ ν : Fin 3, ν ≠ (2 : Fin 3) → cubeIdx p ν = 0) then C else 0)
          = (if p.1.val = 0 then (1 : ℝ) else 0)
              * (if p.2.1.val = 0 then (1 : ℝ) else 0)
              * ((if p.2.2.val = ell - 1 then (1 : ℝ) else 0) * C) := by
      intro p
      have hP : (cubeIdx p (2 : Fin 3) = ell - 1 ∧
            ∀ ν : Fin 3, ν ≠ (2 : Fin 3) → cubeIdx p ν = 0)
          ↔ (p.1.val = 0 ∧ p.2.1.val = 0 ∧ p.2.2.val = ell - 1) := by
        constructor
        · rintro ⟨h0, h⟩
          exact ⟨by rw [← cubeIdx_zero]; exact h 0 (by decide),
                 by rw [← cubeIdx_one]; exact h 1 (by decide),
                 by rw [← cubeIdx_two]; exact h0⟩
        · rintro ⟨h0, h1, h2⟩
          refine ⟨by rw [cubeIdx_two]; exact h2, fun ν hν => ?_⟩
          rcases hcases ν with rfl | rfl | rfl
          · rw [cubeIdx_zero]; exact h0
          · rw [cubeIdx_one]; exact h1
          · exact absurd rfl hν
      rw [if_congr hP rfl rfl]
      by_cases h0 : p.1.val = 0 <;> by_cases h1 : p.2.1.val = 0 <;>
        by_cases h2 : p.2.2.val = ell - 1 <;> simp [h0, h1, h2]
    rw [Finset.sum_congr rfl (fun p _ => hfac p),
      sum_cube_factor (A := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0)) (B := (fun a : Fin ell => if a.val = 0 then (1 : ℝ) else 0))
        (D := fun c : Fin ell => (if c.val = ell - 1 then (1 : ℝ) else 0) * C),
      hind, hindLC]
    ring

/-! ## §2 — `𝒬_c⁻¹` is a SCALED ISOMETRY with constant `ell²` -/

/-- The coordinate form of the section's squared norm: `∑_b (lift f b)² = ell⁴ ∑_c (f c)²`. -/
theorem lastLayerLift_sumSq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (f : CoarseBond L ell → ℝ) :
    (∑ b : Bond L, (lastLayerLift ell f b) ^ 2)
      = (ell : ℝ) ^ 4 * ∑ c : CoarseBond L ell, (f c) ^ 2 := by
  classical
  -- the proof-free reading of `f` at a site, so `Finset.sum_coe_sort` applies
  set g : PeriodicLatticeSite L → Fin 3 → ℝ :=
    fun y μ => if h : y ∈ CoarseLattice L ell then f (⟨y, h⟩, μ) else 0 with hg
  have hsets : @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
        (instFintypeCoarseSite L ell)
      = @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
        (Finset.Subtype.fintype (CoarseLattice L ell)) := by
    ext x; simp
  -- per direction
  have key : ∀ μ : Fin 3,
      (∑ x : PeriodicLatticeSite L, (lastLayerLift ell f (x, μ)) ^ 2)
        = (ell : ℝ) ^ 4 * ∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (f (yc, μ)) ^ 2 := by
    intro μ
    have hsq : ∀ x : PeriodicLatticeSite L,
        (lastLayerLift ell f (x, μ)) ^ 2
          = if (x μ).val % ell = ell - 1 then
              ((ell : ℝ) * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0 := by
      intro x
      unfold lastLayerLift
      split_ifs with h
      · rfl
      · ring
    rw [Finset.sum_congr rfl (fun x _ => hsq x)]
    rw [AdalyFormal.Balaban.PoincareBridge.sum_eq_blocks ell hell hdvd]
    have hblk : ∀ y ∈ CoarseLattice L ell,
        (∑ x ∈ blockOf y ell, if (x μ).val % ell = ell - 1 then
            ((ell : ℝ) * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0)
          = (ell : ℝ) ^ 4 * (g y μ) ^ 2 := by
      intro y hy
      have hpt : ∀ x ∈ blockOf y ell,
          (if (x μ).val % ell = ell - 1 then
              ((ell : ℝ) * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0)
            = (if (x μ).val % ell = ell - 1 then ((ell : ℝ) * g y μ) ^ 2 else 0) := by
        intro x hx
        have hc : (⟨blockCorner ell x, blockCorner_mem x⟩ :
            {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) = ⟨y, hy⟩ :=
          Subtype.ext (blockCorner_of_mem_blockOf hy hx)
        rw [hc]
        have : g y μ = f (⟨y, hy⟩, μ) := by rw [hg]; exact dif_pos hy
        rw [this]
      rw [Finset.sum_congr rfl hpt, sum_block_lastLayer hell hdvd hy μ]
      ring
    rw [Finset.sum_congr rfl hblk]
    have hcoe : (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          (ell : ℝ) ^ 4 * (f (yc, μ)) ^ 2)
        = ∑ y ∈ CoarseLattice L ell, (ell : ℝ) ^ 4 * (g y μ) ^ 2 := by
      have hstep : (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (ell : ℝ) ^ 4 * (f (yc, μ)) ^ 2)
          = ∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (ell : ℝ) ^ 4 * (g (yc : PeriodicLatticeSite L) μ) ^ 2 := by
        refine Finset.sum_congr rfl (fun yc _ => ?_)
        have : g (yc : PeriodicLatticeSite L) μ = f (yc, μ) := by
          rw [hg]; exact dif_pos yc.2
        rw [this]
      rw [hstep]
      exact (Finset.sum_congr hsets (fun _ _ => rfl)).trans
        (Finset.sum_coe_sort (CoarseLattice L ell)
          (fun y => (ell : ℝ) ^ 4 * (g y μ) ^ 2))
    rw [← hcoe, ← Finset.mul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun μ _ => key μ), ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- **`‖𝒬_c⁻¹ F‖ = ell² ‖F‖`** — the supplied section is a scaled isometry, with the constant
computed, not assumed. -/
theorem qcSection_norm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBondSpace L ell) :
    ‖qcSection L ell F‖ = (ell : ℝ) ^ 2 * ‖F‖ := by
  have hnn : (0 : ℝ) ≤ (ell : ℝ) ^ 2 * ‖F‖ := by positivity
  have h1 : ‖qcSection L ell F‖ ^ 2 = ((ell : ℝ) ^ 2 * ‖F‖) ^ 2 := by
    rw [bondSpace_norm_sq]
    have hval : ∀ b : Bond L,
        bondEquiv L (qcSection L ell F) b = lastLayerLift ell (coarseBondEquiv L ell F) b :=
      fun b => congrFun (qcSection_apply L ell F) b
    rw [Finset.sum_congr rfl (fun b _ => by rw [hval b])]
    rw [lastLayerLift_sumSq hell hdvd, ← coarseBondSpace_norm_sq]
    ring
  calc ‖qcSection L ell F‖ = Real.sqrt (‖qcSection L ell F‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (((ell : ℝ) ^ 2 * ‖F‖) ^ 2) := by rw [h1]
    _ = (ell : ℝ) ^ 2 * ‖F‖ := Real.sqrt_sq hnn

/-- **THE CONSTANT `ell²` IS NOT DECORATION — the same statement with `ell` in its place is FALSE.**
`qcSection_norm` is an equality, so it can fail; this exhibits an input at which the mutated
constant does fail, for every tileable lattice with `2 ≤ ell`. (OPS-3: "I made it fail", not "I can
see it would fail".) -/
theorem qcSection_norm_constant_sharp {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ F : CoarseBondSpace L ell, F ≠ 0 ∧ ‖qcSection L ell F‖ ≠ (ell : ℝ) * ‖F‖ := by
  have hell : 0 < ell := by omega
  have hne := qcSection_ne_zero (L := L) hell hdvd
  have hex : ∃ F : CoarseBondSpace L ell, qcSection L ell F ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (ContinuousLinearMap.ext hc)
  obtain ⟨F, hF⟩ := hex
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, map_zero] at hF
    exact hF rfl
  refine ⟨F, hF0, ?_⟩
  rw [qcSection_norm hell hdvd F]
  have hnF : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hl : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  intro hcontra
  have h1 : ((ell : ℝ) ^ 2 - (ell : ℝ)) * ‖F‖ = 0 := by linear_combination hcontra
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have hprod : (2 : ℝ) * (ell : ℝ) ≤ (ell : ℝ) * (ell : ℝ) :=
      mul_le_mul_of_nonneg_right hl (by linarith)
    nlinarith [hl, hprod]
  · exact absurd h2 (ne_of_gt hnF)

/-! ## §3 — `D̃⁽²⁾ := 𝒬_c⁻¹ ∘ C⁽²⁾`, at the source's type, and its exact operator norm -/

/-- **`D̃⁽²⁾`, at the source's type.** `C⁽²⁾ : fine → coarse`, `D̃⁽²⁾ = 𝒬_c⁻¹ ∘ C⁽²⁾ : fine → fine`
— CMP102-UV p.260, the paragraph under (17). -/
noncomputable def transfer (L : PeriodicLatticeExtent) (ell : ℕ)
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) : BondSpace L →L[ℝ] BondSpace L :=
  qcSection L ell ∘L C2

/-- **THE SOURCE'S OWN EQUATION, `Q\tilde{D}^{(2)}(A,c) = C^{(2)}(A,c)`, as a theorem.** It is not imposed as
a clause and not assumed: it follows from `QcEquation.qc_comp_section` alone. At the
`C2 : Hfine →L[ℝ] Hfine` typing used by `Spine`/`Claim18Carrier` this equation is not statable. -/
theorem transfer_satisfies_source_equation {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    qcOp L ell ∘L transfer L ell C2 = C2 := by
  rw [transfer, ← ContinuousLinearMap.comp_assoc, qc_comp_section hell hdvd,
    ContinuousLinearMap.id_comp]

/-- Pointwise: the transfer scales `C⁽²⁾`'s values by exactly `ell²`. -/
theorem transfer_apply_norm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) (v : BondSpace L) :
    ‖transfer L ell C2 v‖ = (ell : ℝ) ^ 2 * ‖C2 v‖ :=
  qcSection_norm hell hdvd (C2 v)

/-- **`‖D̃⁽²⁾‖ = ell² ‖C⁽²⁾‖`, EXACTLY.** Not submultiplicativity (an inequality that could be
slack): the section is a scaled isometry, so the composition's norm is determined. -/
theorem transfer_opNorm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    ‖transfer L ell C2‖ = (ell : ℝ) ^ 2 * ‖C2‖ := by
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  have hsq : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [transfer_apply_norm hell hdvd, mul_assoc]
    exact mul_le_mul_of_nonneg_left (C2.le_opNorm v) (le_of_lt hsq)
  · have hC : ‖C2‖ ≤ ‖transfer L ell C2‖ / (ell : ℝ) ^ 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have h := (transfer L ell C2).le_opNorm v
      rw [transfer_apply_norm hell hdvd] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
      nlinarith [norm_nonneg v, norm_nonneg (C2 v)]
    rw [← le_div_iff₀' hsq]
    exact hC

/-! ## §4 — THE REPAIRED STATEMENT, and exactly what it says -/

/-- **`d`, TIED.** Not a numeral: the number of coordinate directions of the carrier the statement
is about. `PeriodicLatticeExtent = Fin 3 → ℕ` and `Bond L = PeriodicLatticeSite L × Fin 3`, so this
`Fin 3` is the lattice's own direction index. -/
def latticeDim : ℕ := Fintype.card (Fin 3)

theorem latticeDim_eq_three : latticeDim = 3 := by simp [latticeDim]

/-- Bałaban's constant `L^{d−1}` at the TIED parameters (`L := ell`, `d := latticeDim`), written
with the REAL exponent (`Real.rpow`) so that ℕ-subtraction cannot truncate it. -/
noncomputable def transferBound (ell : ℕ) : ℝ := (ell : ℝ) ^ ((latticeDim : ℝ) - 1)

theorem transferBound_eq (ell : ℕ) : transferBound ell = (ell : ℝ) ^ 2 := by
  have h : ((latticeDim : ℝ) - 1) = ((2 : ℕ) : ℝ) := by
    rw [latticeDim_eq_three]; norm_num
  rw [transferBound, h, Real.rpow_natCast]

/-- **THE REPAIRED CLAIM 18, with its transfer bound left as a PARAMETER `bnd`.** Written this way
so that the bound's VALUE can be mutated against ONE text (§5's `tied_with_bound_ell_is_empty` /
`tied_with_bound_ell_cubed_admits_expansive`) instead of against a second copy of the clause list.
`TiedClauses` below is this predicate at Bałaban's own constant. -/
def TiedClausesAt (L : PeriodicLatticeExtent) (ell : ℕ) (bnd : ℝ)
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) : Prop :=
  -- 1. the averaging equation
  (qcOp L ell ∘L qcSection L ell = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell))
  ∧ -- 2. the section is injective
  Function.Injective (qcSection L ell)
  ∧ -- 3. CMP98 p.36 (126) at zero background field: the average does not expand
  ‖qcOp L ell‖ ≤ 1
  ∧ -- 4. genuine coarsening: the average kills a nonzero fluctuation
  ¬ Function.Injective (qcOp L ell)
  ∧ -- 5. anti-shrink floor on `C⁽²⁾`
  1 ≤ ‖C2‖
  ∧ -- 6. THE TRANSFER BOUND
  ‖transfer L ell C2‖ ≤ bnd
  ∧ -- 7. the transfer is nondegenerate
  transfer L ell C2 ≠ 0

/-- **THE REPAIRED CLAIM 18.** Every operator is supplied except `C⁽²⁾`, which is a PARAMETER, not
an existential. `d` and `L` are tied to the carrier. `Ccorr` and `α₀` do not appear. -/
def TiedClauses (L : PeriodicLatticeExtent) (ell : ℕ)
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) : Prop :=
  TiedClausesAt L ell (transferBound ell) C2

/-- The clause bundle at an arbitrary bound is EXACTLY a two-sided pinch on `‖C⁽²⁾‖`, because the
supplied section is a scaled isometry. Everything in §4/§5 is a corollary of this one line. -/
theorem tiedClausesAt_iff {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (bnd : ℝ) (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    TiedClausesAt L ell bnd C2 ↔ (1 ≤ ‖C2‖ ∧ (ell : ℝ) ^ 2 * ‖C2‖ ≤ bnd) := by
  have hell : 0 < ell := by omega
  have hsq : (0 : ℝ) < (ell : ℝ) ^ 2 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  have hnorm := transfer_opNorm (L := L) hell hdvd C2
  constructor
  · rintro ⟨-, -, -, -, hfloor, hbnd, -⟩
    rw [hnorm] at hbnd
    exact ⟨hfloor, hbnd⟩
  · rintro ⟨hfloor, hbnd⟩
    refine ⟨qc_comp_section hell hdvd, qcSection_injective hell hdvd,
      qcOp_opNorm_le_one hell hdvd, qcOp_not_injective hell2 hdvd, hfloor, ?_, ?_⟩
    · rw [hnorm]; exact hbnd
    · intro hz
      have h0 : (ell : ℝ) ^ 2 * ‖C2‖ = 0 := by rw [← hnorm, hz, norm_zero]
      nlinarith [hfloor, hsq]

/-- **WHAT THE REPAIRED STATEMENT SAYS, exactly: `‖C⁽²⁾‖ = 1`.** Clauses 1–4 are theorems about the
supplied operators; clauses 5 and 6 are the two halves of a single equation, because the section is
a scaled isometry with the same constant `ell²` that Bałaban's `L^{d−1}` becomes at `d = 3`; clause
7 follows. This is the whole content of Claim 18 once `𝒬_c`, `𝒬_c⁻¹`, `d` and `L` are pinned. -/
theorem tiedClauses_iff {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    TiedClauses L ell C2 ↔ ‖C2‖ = 1 := by
  have hell : 0 < ell := by omega
  have hsq : (0 : ℝ) < (ell : ℝ) ^ 2 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  rw [TiedClauses, tiedClausesAt_iff hell2 hdvd, transferBound_eq]
  constructor
  · rintro ⟨hfloor, hbnd⟩
    nlinarith
  · intro h1
    exact ⟨le_of_eq h1.symm, by rw [h1, mul_one]⟩

/-! ## §4b — THE COLLAPSE IS NOT AN ARTEFACT OF *THIS* SECTION

`tiedClauses_iff` uses `QcEquation.qcSection` specifically, and §7 of the report records that this
section is NOT supported on the source's `b₀(c)`. The obvious objection is that the collapse to a
bound on `‖C⁽²⁾‖` might be an artefact of that choice. It is not: the same conclusion follows from
Claim 18's bound at **any** right inverse whatsoever, with a constant that depends only on `‖𝒬_c‖`
— because `C⁽²⁾ = 𝒬_c ∘ (𝒬_c⁻¹ ∘ C⁽²⁾)` whenever `𝒬_c ∘ 𝒬_c⁻¹ = id`. -/

/-- **SECTION-INDEPENDENT.** For ANY right inverse `S` of the supplied average, Claim 18's transfer
bound forces an upper bound on `‖C⁽²⁾‖`. No property of `S` beyond being a right inverse is used. -/
theorem claim18_bound_forces_C2_bound_any_section {ell : ℕ}
    (S : CoarseBondSpace L ell →L[ℝ] BondSpace L)
    (hS : qcOp L ell ∘L S = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell)
    (hbnd : ‖S ∘L C2‖ ≤ (ell : ℝ) ^ 2) :
    ‖C2‖ ≤ (ell : ℝ) ^ 2 * ‖qcOp L ell‖ := by
  have h1 : qcOp L ell ∘L (S ∘L C2) = C2 := by
    rw [← ContinuousLinearMap.comp_assoc, hS, ContinuousLinearMap.id_comp]
  calc ‖C2‖ = ‖qcOp L ell ∘L (S ∘L C2)‖ := by rw [h1]
    _ ≤ ‖qcOp L ell‖ * ‖S ∘L C2‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖qcOp L ell‖ * (ell : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
    _ = (ell : ℝ) ^ 2 * ‖qcOp L ell‖ := by ring

/-- The same with the tree's own bound on `‖𝒬_c‖` substituted: at ANY right inverse, Claim 18
forces `‖C⁽²⁾‖ ≤ ell² · √(ell^{-3}) = √ell`. Weaker than `tiedClauses_iff`'s `‖C⁽²⁾‖ = 1`, and
that is the point — the strong form is what the SUPPLIED section buys, and this is what survives
without it. -/
theorem claim18_bound_forces_C2_sqrt_bound {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (S : CoarseBondSpace L ell →L[ℝ] BondSpace L)
    (hS : qcOp L ell ∘L S = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell)
    (hbnd : ‖S ∘L C2‖ ≤ (ell : ℝ) ^ 2) :
    ‖C2‖ ≤ (ell : ℝ) ^ 2 * Real.sqrt (1 / (ell : ℝ) ^ 3) := by
  refine le_trans (claim18_bound_forces_C2_bound_any_section S hS C2 hbnd) ?_
  exact mul_le_mul_of_nonneg_left (qcOp_opNorm_le_sqrt hell hdvd) (by positivity)

/-- **EVERY right inverse of the supplied average has operator norm at least `ell^{3/2}`** — so no
choice of section can make `‖𝒬_c⁻¹‖` small, and the supplied one (`ell²`) is within a factor
`√ell` of the best possible. A section-independent floor, from `‖𝒬_c ∘ S‖ = ‖id‖ = 1`. -/
theorem right_inverse_opNorm_lower_bound {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (S : CoarseBondSpace L ell →L[ℝ] BondSpace L)
    (hS : qcOp L ell ∘L S = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell)) :
    1 ≤ ‖qcOp L ell‖ * ‖S‖ := by
  have hone : ‖(qcOp L ell) ∘L S‖ ≤ ‖qcOp L ell‖ * ‖S‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  rw [hS] at hone
  have hid : (1 : ℝ) ≤ ‖ContinuousLinearMap.id ℝ (CoarseBondSpace L ell)‖ := by
    have hne := qcSection_ne_zero (L := L) hell hdvd
    have hex : ∃ F : CoarseBondSpace L ell, qcSection L ell F ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (ContinuousLinearMap.ext hc)
    obtain ⟨F, hF⟩ := hex
    have hF0 : F ≠ 0 := by
      intro h
      rw [h, map_zero] at hF
      exact hF rfl
    have hnF : 0 < ‖F‖ := norm_pos_iff.mpr hF0
    have := (ContinuousLinearMap.id ℝ (CoarseBondSpace L ell)).le_opNorm F
    simp only [ContinuousLinearMap.id_apply] at this
    nlinarith [hnF, this]
  linarith

/-! ## §5 — CONTROLS, both directions -/

/-- **MUST-FIRE, half 1: the FREE `Lreal`/`d` binders make the transfer bound empty.** With `Lreal`
and `d` quantified as `Spine.claim18_exists` quantifies them, EVERY operator satisfies the bound,
no matter how large its norm. This is a measurement of the defect the tie removes. -/
theorem untied_bound_admits_every_operator {ell : ℕ}
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    ∃ (Lreal : ℝ) (d : ℕ), 1 < Lreal ∧
      ‖transfer L ell C2‖ ≤ Lreal ^ ((d : ℝ) - 1) := by
  refine ⟨‖transfer L ell C2‖ + 2, 2, by linarith [norm_nonneg (transfer L ell C2)], ?_⟩
  have h : (((2 : ℕ) : ℝ) - 1) = (1 : ℝ) := by norm_num
  rw [h, Real.rpow_one]
  linarith

/-- **MUST-FIRE, half 2: the TIED statement rejects what the untied bound admits.** -/
theorem tied_rejects_expansive {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) (h : 1 < ‖C2‖) :
    ¬ TiedClauses L ell C2 := by
  intro hT
  have := (tiedClauses_iff hell2 hdvd C2).mp hT
  linarith

/-- The normalized supplied average — a norm-`1` operator of the source's type, built from an
operator this tree already has. It is NOT `C⁽²⁾`; it exists only to inhabit the statement. -/
noncomputable def unitWitness (L : PeriodicLatticeExtent) (ell : ℕ) :
    BondSpace L →L[ℝ] CoarseBondSpace L ell :=
  (‖qcOp L ell‖)⁻¹ • qcOp L ell

theorem unitWitness_norm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖unitWitness L ell‖ = 1 := by
  have hne : qcOp L ell ≠ 0 := qcOp_ne_zero hell hdvd
  have hpos : 0 < ‖qcOp L ell‖ := norm_pos_iff.mpr hne
  rw [unitWitness, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_cancel₀ (ne_of_gt hpos)]

/-- **MUST-NOT-FIRE: the repaired statement is NOT vacuous.** It is inhabited, so the tie did not
over-constrain it into emptiness. -/
theorem tied_satisfiable {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell, TiedClauses L ell C2 :=
  ⟨unitWitness L ell,
    (tiedClauses_iff hell2 hdvd _).mpr (unitWitness_norm (by omega) hdvd)⟩

/-- **THE CONTROL PAIR, on ONE operator.** `2 • unitWitness` has norm `2`: the UNTIED bound admits
it, the TIED bundle refuses it. A single exhibit showing the repair changed what is asserted. -/
theorem control_pair {ell : ℕ} (hell2 : 2 ≤ ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell,
      (∃ (Lreal : ℝ) (d : ℕ), 1 < Lreal ∧ ‖transfer L ell C2‖ ≤ Lreal ^ ((d : ℝ) - 1))
        ∧ ¬ TiedClauses L ell C2 := by
  refine ⟨(2 : ℝ) • unitWitness L ell, untied_bound_admits_every_operator _, ?_⟩
  refine tied_rejects_expansive hell2 hdvd _ ?_
  rw [norm_smul, Real.norm_eq_abs, unitWitness_norm (by omega) hdvd]
  norm_num

/-- **BOUND MUTATION, DOWN: replace `ell^{d−1} = ell²` by `ell` and the bundle goes EMPTY.**
So the bound's VALUE is load-bearing on the tight side: it is not a number that could be shrunk
without changing what is asserted. -/
theorem tied_with_bound_ell_is_empty {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell, TiedClausesAt L ell (ell : ℝ) C2 := by
  rintro ⟨C2, hT⟩
  obtain ⟨hfloor, hbnd⟩ := (tiedClausesAt_iff hell2 hdvd _ C2).mp hT
  have hl : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  nlinarith

/-- **BOUND MUTATION, UP: replace it by `ell³` and the bundle starts admitting `‖C⁽²⁾‖ = ell`.**
So the bound's value is load-bearing on the loose side too. Together with the previous theorem this
is the mutation pair for clause 6's constant: both directions fire, and the count is 2/2. -/
theorem tied_with_bound_ell_cubed_admits_expansive {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell,
      ‖C2‖ = (ell : ℝ) ∧ TiedClausesAt L ell ((ell : ℝ) ^ 3) C2 := by
  have hell : 0 < ell := by omega
  have hl : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  refine ⟨(ell : ℝ) • unitWitness L ell, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, unitWitness_norm hell hdvd, mul_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ell : ℝ))]
  · refine (tiedClausesAt_iff hell2 hdvd _ _).mpr ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, unitWitness_norm hell hdvd, mul_one,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ell : ℝ))]
      linarith
    · rw [norm_smul, Real.norm_eq_abs, unitWitness_norm hell hdvd, mul_one,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ell : ℝ))]
      ring_nf
      linarith [le_refl ((ell : ℝ) ^ 3)]

/-! ## §6 — DEGENERATE-POINT AUDIT: every numeric binder, checked -/

/-- `ell = 0` is not a block scale at all: no periodic extent is divisible by it. -/
theorem no_tiling_at_ell_zero (hdvd : ∀ μ : Fin 3, (0 : ℕ) ∣ (L μ + 1)) : False := by
  have h := hdvd 0
  rw [Nat.zero_dvd] at h
  omega

/-- `ell = 1` — the degenerate block side — EMPTIES the repaired bundle: the average is injective
there, so clause 4 fails. (Reuses `QcEquation.qcOp_one_injective`, LAW-19.) -/
theorem tied_empty_at_ell_one :
    ¬ ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L 1, TiedClauses L 1 C2 := by
  rintro ⟨C2, -, -, -, hni, -⟩
  exact hni (qcOp_one_injective)

/-- **THE ℕ-SUBTRACTION TRAP, exhibited.** `formal/S91_REGISTRY.tsv`'s own note records that
`claim18_exists`'s clause-5 exponent was ℕ-truncated: at `d = 0`, `L^(d−1)` reads `L^0 = 1`. -/
theorem nat_sub_truncation_at_d_zero (ell : ℕ) : ((ell : ℝ)) ^ ((0 : ℕ) - 1) = 1 := by
  norm_num

/-- …and the honest REAL exponent at the same point is `1/ell ≠ 1`. The two readings of the SAME
notation disagree, which is why `transferBound` is defined with `Real.rpow`. -/
theorem rpow_at_d_zero_ne_one (ell : ℕ) (hell2 : 2 ≤ ell) :
    ((ell : ℝ)) ^ ((0 : ℝ) - 1) ≠ 1 := by
  have hpos : (0 : ℝ) < (ell : ℝ) := by
    have : (0 : ℕ) < ell := by omega
    exact_mod_cast this
  have h2 : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  have hval : ((ell : ℝ)) ^ ((0 : ℝ) - 1) = ((ell : ℝ))⁻¹ := by
    rw [zero_sub, Real.rpow_neg_one]
  rw [hval]
  intro h
  have : (ell : ℝ) = 1 := by
    field_simp at h
    linarith [h]
  linarith

/-- **The repaired bundle has NO `α₀` and NO `Ccorr` binder**, so the point at which the
single-carrier predecessor was proved false cannot be reached. Recorded as the statement that
clause 3 holds unconditionally, i.e. at zero background field, with nothing to choose. -/
theorem clause3_unconditional {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ‖qcOp L ell‖ ≤ 1 :=
  qcOp_opNorm_le_one hell hdvd

/-! ## §7 — THE SOURCE'S OWN SUPPORT: the `b₀(c)` section, BUILT and MEASURED

`QcEquation.qcSection` is an exact right inverse, but it is NOT supported where CMP102-UV p.260
says `D̃` is supported: *"We assume that `\tilde{D}(A,b,c)=0` for all `b\neq b_0(c)`"*, with `b₀(c)` the
SINGLE bond of `B(c)` contained in `c`. `lastLayerLift` spreads over all `ell²` bonds of `B(c)`.
Since Claim 18 multiplies `‖𝒬_c⁻¹‖`, the choice changes the number, so this section builds the
`b₀`-supported right inverse rather than leaving the difference as a remark. -/

/-- **`b₀(c)` as a predicate on fine bonds.** For `c = (y, μ)`: last layer in direction `μ` AND on
the coarse axis through the corner (every transverse coordinate a multiple of `ell`). That is the
unique fine bond of `B(c)` contained in `c`. -/
def IsB0 (ell : ℕ) (b : Bond L) : Prop :=
  (b.1 b.2).val % ell = ell - 1 ∧ ∀ ν : Fin 3, ν ≠ b.2 → (b.1 ν).val % ell = 0

instance decIsB0 (ell : ℕ) (b : Bond L) : Decidable (IsB0 ell b) := by
  unfold IsB0; infer_instance

/-- **Exactly ONE `b₀` site per block per direction.** The `b₀` twin of `sum_block_lastLayer`
(which counts `ell²`); the ratio `ell²` between the two counts is where the two sections' operator
norms diverge. -/
theorem sum_block_b0 {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    {y : PeriodicLatticeSite L} (hy : y ∈ CoarseLattice L ell) (μ : Fin 3) (C : ℝ) :
    (∑ x ∈ blockOf y ell, if IsB0 (L := L) ell (x, μ) then C else 0) = C := by
  classical
  have hfit := coarseLattice_fits hdvd hy
  rw [sum_block_eq_cube hfit]
  have hres : ∀ (p : Cube ell) (ν : Fin 3),
      ((chart y ell p) ν).val % ell = cubeIdx p ν := by
    intro p ν
    obtain ⟨kk, hkk⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ν)
    rw [chart_val hfit p ν, hkk, Nat.mul_add_mod, Nat.mod_eq_of_lt (cubeIdx_lt p ν)]
  have hcong : ∀ p : Cube ell,
      (if IsB0 (L := L) ell (chart y ell p, μ) then C else 0)
        = (if (cubeIdx p μ = ell - 1 ∧ ∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) then C else 0) := by
    intro p
    have hP : IsB0 (L := L) ell (chart y ell p, μ)
        ↔ (cubeIdx p μ = ell - 1 ∧ ∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) := by
      unfold IsB0
      simp only []
      constructor
      · rintro ⟨h0, h⟩
        exact ⟨by rw [← hres p μ]; exact h0, fun ν hν => by rw [← hres p ν]; exact h ν hν⟩
      · rintro ⟨h0, h⟩
        exact ⟨by rw [hres p μ]; exact h0, fun ν hν => by rw [hres p ν]; exact h ν hν⟩
    exact if_congr hP rfl rfl
  rw [Finset.sum_congr rfl (fun p _ => hcong p)]
  exact sum_cube_b0 hell μ C

/-- **The `b₀`-supported lift.** Weight `ell³` on the single bond, forced (not chosen) by the
right-inverse requirement below: the block average reads that bond from `ell` of its `ell³` sites,
against the `1/ell⁴` normalisation. -/
noncomputable def b0Lift (ell : ℕ) (f : CoarseBond L ell → ℝ) (b : Bond L) : ℝ :=
  if IsB0 ell b then
    (ell : ℝ) ^ 3 * f (⟨blockCorner ell b.1, blockCorner_mem b.1⟩, b.2) else 0

theorem b0Lift_add (ell : ℕ) (f g : CoarseBond L ell → ℝ) (b : Bond L) :
    b0Lift ell (f + g) b = b0Lift ell f b + b0Lift ell g b := by
  unfold b0Lift; split_ifs with h
  · simp only [Pi.add_apply]; ring
  · ring

theorem b0Lift_smul (ell : ℕ) (c : ℝ) (f : CoarseBond L ell → ℝ) (b : Bond L) :
    b0Lift ell (c • f) b = c * b0Lift ell f b := by
  unfold b0Lift; split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul]; ring
  · ring

/-- The `b₀` line integral: `ell³ f(y,μ)` on the `ell` axis sites of the block, `0` on the rest. -/
theorem lineIntegralValue_b0Lift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) {y : PeriodicLatticeSite L}
    (hy : y ∈ CoarseLattice L ell) {x : PeriodicLatticeSite L} (hx : x ∈ blockOf y ell)
    (μ : Fin 3) (f : CoarseBond L ell → ℝ) :
    lineIntegralValue ell (b0Lift ell f) x μ =
      if (∀ ν : Fin 3, ν ≠ μ → (x ν).val % ell = 0) then (ell : ℝ) ^ 3 * f (⟨y, hy⟩, μ) else 0 := by
  classical
  set i : ℕ := (x μ).val - (y μ).val with hi_def
  have hbμ := (mem_blockOf.mp hx) μ
  have hy0 : (y μ).val % ell = 0 := (mem_CoarseLattice.mp hy) μ
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy0
  have hi_lt : i < ell := by omega
  have hxval : (x μ).val = ell * k + i := by omega
  have hfit : (y μ).val + ell ≤ L μ + 1 := coarseLattice_mem_fits hdvd hy μ
  have hres : ∀ j : ℕ, ((pathStep x μ j) μ).val % ell = (i + j) % ell := by
    intro j
    rw [pathStep_apply_self_val, Nat.mod_mod_of_dvd _ (hdvd μ), hxval]
    conv_lhs => rw [show ell * k + i + j = ell * k + (i + j) by ring]
    rw [Nat.mul_add_mod]
  -- the transverse coordinates never move along the path
  have htr : ∀ (j : ℕ) (ν : Fin 3), ν ≠ μ → ((pathStep x μ j) ν).val = (x ν).val := by
    intro j ν hν
    rw [pathStep_apply_ne x μ ν j hν]
  have hjstar : ell - 1 - i < ell := by omega
  rw [lineIntegralValue]
  by_cases haxis : ∀ ν : Fin 3, ν ≠ μ → (x ν).val % ell = 0
  · rw [if_pos haxis]
    rw [Finset.sum_eq_single (ell - 1 - i)]
    · have hcondμ : ((pathStep x μ (ell - 1 - i)) μ).val % ell = ell - 1 := by
        rw [hres]; exact (residue_hit_iff hell hi_lt hjstar).mpr rfl
      have hcond : IsB0 (L := L) ell (pathStep x μ (ell - 1 - i), μ) := by
        refine ⟨hcondμ, fun ν hν => ?_⟩
        rw [htr _ ν hν]; exact haxis ν hν
      simp only [b0Lift, iterate_eq_pathStep]
      rw [if_pos hcond]
      congr 2
      refine Prod.ext_iff.mpr ⟨?_, rfl⟩
      apply Subtype.ext
      funext ν
      apply Fin.ext
      rw [blockCorner_val]
      by_cases hν : ν = μ
      · subst hν
        have hvv : ((pathStep x ν (ell - 1 - i)) ν).val = ell * k + (ell - 1) := by
          rw [pathStep_apply_self_val, hxval,
            show ell * k + i + (ell - 1 - i) = ell * k + (ell - 1) by omega]
          exact Nat.mod_eq_of_lt (by omega)
        have hvm : ((pathStep x ν (ell - 1 - i)) ν).val % ell = ell - 1 := by
          rw [hres]; exact (residue_hit_iff hell hi_lt hjstar).mpr rfl
        show ((pathStep x ν (ell - 1 - i)) ν).val -
            ((pathStep x ν (ell - 1 - i)) ν).val % ell = (y ν).val
        omega
      · rw [pathStep_apply_ne x μ ν _ hν]
        have := congrArg (fun z : PeriodicLatticeSite L => (z ν).val)
          (blockCorner_of_mem_blockOf hy hx)
        simpa [blockCorner_val] using this
    · intro j hjmem hjne
      rw [Finset.mem_range] at hjmem
      have hcondμ : ¬ ((pathStep x μ j) μ).val % ell = ell - 1 := by
        rw [hres]; intro hc; exact hjne ((residue_hit_iff hell hi_lt hjmem).mp hc)
      have hcond : ¬ IsB0 (L := L) ell (pathStep x μ j, μ) := fun h => hcondμ h.1
      simp only [b0Lift, iterate_eq_pathStep]
      rw [if_neg hcond]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hjstar) hnot
  · rw [if_neg haxis]
    refine Finset.sum_eq_zero fun j _ => ?_
    push_neg at haxis
    obtain ⟨ν, hν, hνval⟩ := haxis
    have hcond : ¬ IsB0 (L := L) ell (pathStep x μ j, μ) := by
      intro h
      exact hνval (by rw [← htr j ν hν]; exact h.2 ν hν)
    simp only [b0Lift, iterate_eq_pathStep]
    rw [if_neg hcond]

/-- **THE `b₀` SECTION EQUATION**: the `b₀`-supported lift with weight `ell³` is an EXACT right
inverse of the same faithful average. So `qcSection` is not the only one, and the weight `ell³` is
forced by this identity, not chosen. -/
theorem lineCoarseRestrict_b0Lift {ell : ℕ} (hell : 0 < ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) (f : CoarseBond L ell → ℝ) (b : CoarseBond L ell) :
    lineCoarseRestrict ell (b0Lift ell f) b = f b := by
  classical
  obtain ⟨⟨y, hy⟩, μ⟩ := b
  have hfit := coarseLattice_fits hdvd hy
  rw [lineCoarseRestrict]
  rw [Finset.sum_congr rfl (fun x hx => lineIntegralValue_b0Lift hell hdvd hy hx μ f)]
  -- the axis sites of the block: exactly `ell` of them
  rw [sum_block_eq_cube hfit]
  have hcong : ∀ p : Cube ell,
      (if (∀ ν : Fin 3, ν ≠ μ → ((chart y ell p) ν).val % ell = 0) then
          (ell : ℝ) ^ 3 * f (⟨y, hy⟩, μ) else 0)
        = (if (∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) then
          (ell : ℝ) ^ 3 * f (⟨y, hy⟩, μ) else 0) := by
    intro p
    have hP : (∀ ν : Fin 3, ν ≠ μ → ((chart y ell p) ν).val % ell = 0)
        ↔ (∀ ν : Fin 3, ν ≠ μ → cubeIdx p ν = 0) := by
      constructor <;> intro h ν hν
      · have hres : ((chart y ell p) ν).val % ell = cubeIdx p ν := by
          obtain ⟨kk, hkk⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ν)
          rw [chart_val hfit p ν, hkk, Nat.mul_add_mod,
            Nat.mod_eq_of_lt (cubeIdx_lt p ν)]
        rw [← hres]; exact h ν hν
      · have hres : ((chart y ell p) ν).val % ell = cubeIdx p ν := by
          obtain ⟨kk, hkk⟩ := Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hy) ν)
          rw [chart_val hfit p ν, hkk, Nat.mul_add_mod,
            Nat.mod_eq_of_lt (cubeIdx_lt p ν)]
        rw [hres]; exact h ν hν
    exact if_congr hP rfl rfl
  rw [Finset.sum_congr rfl (fun p _ => hcong p), sum_cube_axis hell μ _]
  have hne : (ell : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  field_simp

/-- The `b₀` fine bonds are ONE per coarse bond: the squared-norm identity. -/
theorem b0Lift_sumSq {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (f : CoarseBond L ell → ℝ) :
    (∑ b : Bond L, (b0Lift ell f b) ^ 2)
      = (ell : ℝ) ^ 6 * ∑ c : CoarseBond L ell, (f c) ^ 2 := by
  classical
  set g : PeriodicLatticeSite L → Fin 3 → ℝ :=
    fun y μ => if h : y ∈ CoarseLattice L ell then f (⟨y, h⟩, μ) else 0 with hg
  have hsets : @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
        (instFintypeCoarseSite L ell)
      = @Finset.univ {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}
        (Finset.Subtype.fintype (CoarseLattice L ell)) := by
    ext x; simp
  have key : ∀ μ : Fin 3,
      (∑ x : PeriodicLatticeSite L, (b0Lift ell f (x, μ)) ^ 2)
        = (ell : ℝ) ^ 6 * ∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (f (yc, μ)) ^ 2 := by
    intro μ
    have hsq : ∀ x : PeriodicLatticeSite L,
        (b0Lift ell f (x, μ)) ^ 2
          = if IsB0 (L := L) ell (x, μ) then
              ((ell : ℝ) ^ 3 * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0 := by
      intro x
      unfold b0Lift
      split_ifs with h
      · rfl
      · ring
    rw [Finset.sum_congr rfl (fun x _ => hsq x)]
    rw [AdalyFormal.Balaban.PoincareBridge.sum_eq_blocks ell hell hdvd]
    have hblk : ∀ y ∈ CoarseLattice L ell,
        (∑ x ∈ blockOf y ell, if IsB0 (L := L) ell (x, μ) then
            ((ell : ℝ) ^ 3 * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0)
          = (ell : ℝ) ^ 6 * (g y μ) ^ 2 := by
      intro y hy
      have hfit := coarseLattice_fits hdvd hy
      have hpt : ∀ x ∈ blockOf y ell,
          (if IsB0 (L := L) ell (x, μ) then
              ((ell : ℝ) ^ 3 * f (⟨blockCorner ell x, blockCorner_mem x⟩, μ)) ^ 2 else 0)
            = (if IsB0 (L := L) ell (x, μ) then ((ell : ℝ) ^ 3 * g y μ) ^ 2 else 0) := by
        intro x hx
        have hc : (⟨blockCorner ell x, blockCorner_mem x⟩ :
            {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell}) = ⟨y, hy⟩ :=
          Subtype.ext (blockCorner_of_mem_blockOf hy hx)
        rw [hc]
        have hgy : g y μ = f (⟨y, hy⟩, μ) := by rw [hg]; exact dif_pos hy
        rw [hgy]
      rw [Finset.sum_congr rfl hpt, sum_block_b0 hell hdvd hy μ]
      ring
    rw [Finset.sum_congr rfl hblk]
    have hcoe : (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
          (ell : ℝ) ^ 6 * (f (yc, μ)) ^ 2)
        = ∑ y ∈ CoarseLattice L ell, (ell : ℝ) ^ 6 * (g y μ) ^ 2 := by
      have hstep : (∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (ell : ℝ) ^ 6 * (f (yc, μ)) ^ 2)
          = ∑ yc : {y : PeriodicLatticeSite L // y ∈ CoarseLattice L ell},
            (ell : ℝ) ^ 6 * (g (yc : PeriodicLatticeSite L) μ) ^ 2 := by
        refine Finset.sum_congr rfl (fun yc _ => ?_)
        have : g (yc : PeriodicLatticeSite L) μ = f (yc, μ) := by rw [hg]; exact dif_pos yc.2
        rw [this]
      rw [hstep]
      exact (Finset.sum_congr hsets (fun _ _ => rfl)).trans
        (Finset.sum_coe_sort (CoarseLattice L ell)
          (fun y => (ell : ℝ) ^ 6 * (g y μ) ^ 2))
    rw [← hcoe, ← Finset.mul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun μ _ => key μ), ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

/-! ### §7b — the `b₀` section as an operator, its norm, and the number Claim 18 reduces to there -/

/-- The `b₀` lift as a `LinearMap` on raw function spaces. -/
noncomputable def b0LiftLM (L : PeriodicLatticeExtent) (ell : ℕ) :
    (CoarseBond L ell → ℝ) →ₗ[ℝ] (Bond L → ℝ) where
  toFun f := b0Lift ell f
  map_add' f g := funext fun b => b0Lift_add ell f g b
  map_smul' c f := funext fun b => b0Lift_smul ell c f b

noncomputable def b0LiftLMH (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseBondSpace L ell →ₗ[ℝ] BondSpace L :=
  (bondEquiv L).symm.toLinearMap.comp
    ((b0LiftLM L ell).comp (coarseBondEquiv L ell).toLinearMap)

/-- **The `b₀`-supported section as a `ContinuousLinearMap`** — the source-faithful `𝒬_c⁻¹`. -/
noncomputable def b0Section (L : PeriodicLatticeExtent) (ell : ℕ) :
    CoarseBondSpace L ell →L[ℝ] BondSpace L :=
  LinearMap.toContinuousLinearMap (b0LiftLMH L ell)

theorem b0Section_apply (L : PeriodicLatticeExtent) (ell : ℕ) (F : CoarseBondSpace L ell) :
    bondEquiv L (b0Section L ell F) = b0Lift ell (coarseBondEquiv L ell F) := rfl

/-- **The `b₀` section IS an exact right inverse of the same faithful average** — so it is a
legitimate `𝒬_c⁻¹`, not a straw object, and the comparison below is between two admissible
choices. -/
theorem qc_comp_b0Section {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    qcOp L ell ∘L b0Section L ell = ContinuousLinearMap.id ℝ (CoarseBondSpace L ell) := by
  refine ContinuousLinearMap.ext fun F => ?_
  apply (coarseBondEquiv L ell).injective
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply, qcOp_apply, b0Section_apply]
  funext b
  exact lineCoarseRestrict_b0Lift hell hdvd _ b

/-- **`‖𝒬_c⁻¹_{b₀} F‖ = ell³ ‖F‖`** — the source-faithful section is also a scaled isometry, but
with constant `ell³`, a factor `ell` LARGER than the tree's `qcSection`. -/
theorem b0Section_norm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBondSpace L ell) :
    ‖b0Section L ell F‖ = (ell : ℝ) ^ 3 * ‖F‖ := by
  have hnn : (0 : ℝ) ≤ (ell : ℝ) ^ 3 * ‖F‖ := by positivity
  have h1 : ‖b0Section L ell F‖ ^ 2 = ((ell : ℝ) ^ 3 * ‖F‖) ^ 2 := by
    rw [bondSpace_norm_sq]
    have hval : ∀ b : Bond L,
        bondEquiv L (b0Section L ell F) b = b0Lift ell (coarseBondEquiv L ell F) b :=
      fun b => congrFun (b0Section_apply L ell F) b
    rw [Finset.sum_congr rfl (fun b _ => by rw [hval b])]
    rw [b0Lift_sumSq hell hdvd, ← coarseBondSpace_norm_sq]
    ring
  calc ‖b0Section L ell F‖ = Real.sqrt (‖b0Section L ell F‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (((ell : ℝ) ^ 3 * ‖F‖) ^ 2) := by rw [h1]
    _ = (ell : ℝ) ^ 3 * ‖F‖ := Real.sqrt_sq hnn

theorem b0_transfer_opNorm {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell) :
    ‖b0Section L ell ∘L C2‖ = (ell : ℝ) ^ 3 * ‖C2‖ := by
  have hcube : (0 : ℝ) < (ell : ℝ) ^ 3 := by
    have : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
    positivity
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply, b0Section_norm hell hdvd, mul_assoc]
    exact mul_le_mul_of_nonneg_left (C2.le_opNorm v) (le_of_lt hcube)
  · have hC : ‖C2‖ ≤ ‖b0Section L ell ∘L C2‖ / (ell : ℝ) ^ 3 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have h := (b0Section L ell ∘L C2).le_opNorm v
      rw [ContinuousLinearMap.coe_comp', Function.comp_apply, b0Section_norm hell hdvd] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hcube]
      nlinarith [norm_nonneg v, norm_nonneg (C2 v)]
    rw [← le_div_iff₀' hcube]
    exact hC

/-- **THE NUMBER IS SECTION-DEPENDENT, AND AT THE SOURCE'S OWN SUPPORT THE CAMPAIGN'S FLOOR CLAUSE
CONTRADICTS BAŁABAN'S BOUND.** At `𝒬_c⁻¹ := b0Section` the transfer bound `‖D̃⁽²⁾‖ ≤ ell^{d−1}`
reads `‖C⁽²⁾‖ ≤ 1/ell`, which is incompatible with the anti-shrink floor `1 ≤ ‖C⁽²⁾‖` for every
`2 ≤ ell`. Note WHICH clause loses: the floor is the CAMPAIGN's addition (introduced to block the
zero witness), not Bałaban's; the bound is Bałaban's. This is reported, not resolved. -/
theorem b0_tied_bundle_is_empty {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1)) :
    ¬ ∃ C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell,
        1 ≤ ‖C2‖ ∧ ‖b0Section L ell ∘L C2‖ ≤ (ell : ℝ) ^ 2 := by
  rintro ⟨C2, hfloor, hbnd⟩
  have hell : 0 < ell := by omega
  have hl : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell2
  rw [b0_transfer_opNorm hell hdvd] at hbnd
  have hcube_nn : (0 : ℝ) ≤ (ell : ℝ) ^ 3 := by positivity
  have h1 : (ell : ℝ) ^ 3 * 1 ≤ (ell : ℝ) ^ 3 * ‖C2‖ :=
    mul_le_mul_of_nonneg_left hfloor hcube_nn
  have h2 : (ell : ℝ) ^ 2 * 1 < (ell : ℝ) ^ 2 * (ell : ℝ) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  rw [mul_one] at h1 h2
  have h3 : (ell : ℝ) ^ 2 * (ell : ℝ) = (ell : ℝ) ^ 3 := by ring
  rw [h3] at h2
  linarith

/-- The same fact stated positively, so the surviving content at the `b₀` section is on the record
as a number: Bałaban's bound there is `‖C⁽²⁾‖ ≤ 1/ell`. -/
theorem b0_bound_forces_C2_le_inv_ell {ell : ℕ} (hell2 : 2 ≤ ell)
    (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (C2 : BondSpace L →L[ℝ] CoarseBondSpace L ell)
    (hbnd : ‖b0Section L ell ∘L C2‖ ≤ (ell : ℝ) ^ 2) :
    ‖C2‖ ≤ 1 / (ell : ℝ) := by
  have hell : 0 < ell := by omega
  have hpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hell
  rw [b0_transfer_opNorm hell hdvd] at hbnd
  rw [le_div_iff₀ hpos]
  have hsq : (0 : ℝ) < (ell : ℝ) ^ 2 := by positivity
  have h : (ell : ℝ) ^ 2 * (‖C2‖ * (ell : ℝ)) ≤ (ell : ℝ) ^ 2 * 1 := by
    rw [show (ell : ℝ) ^ 2 * (‖C2‖ * (ell : ℝ)) = (ell : ℝ) ^ 3 * ‖C2‖ by ring, mul_one]
    exact hbnd
  exact le_of_mul_le_mul_left h hsq

/-- **The two admissible sections differ by exactly a factor `ell` in operator norm** — the whole
of the divergence, on one line. -/
theorem section_norm_ratio {ell : ℕ} (hell : 0 < ell) (hdvd : ∀ μ : Fin 3, ell ∣ (L μ + 1))
    (F : CoarseBondSpace L ell) :
    ‖b0Section L ell F‖ = (ell : ℝ) * ‖qcSection L ell F‖ := by
  rw [b0Section_norm hell hdvd, qcSection_norm hell hdvd]
  ring

#print axioms b0Lift_add
#print axioms b0Lift_smul
#print axioms b0Section_apply
#print axioms sum_fin_ite_last
#print axioms sum_fin_ite_zero
#print axioms sum_cube_factor
#print axioms sum_cube_axis
#print axioms sum_cube_b0
#print axioms sum_block_b0
#print axioms lineIntegralValue_b0Lift
#print axioms lineCoarseRestrict_b0Lift
#print axioms b0Lift_sumSq
#print axioms qc_comp_b0Section
#print axioms b0Section_norm
#print axioms b0_transfer_opNorm
#print axioms b0_tied_bundle_is_empty
#print axioms b0_bound_forces_C2_le_inv_ell
#print axioms section_norm_ratio
#print axioms transfer_apply_norm
#print axioms latticeDim_eq_three
#print axioms transferBound_eq
#print axioms unitWitness_norm
#print axioms nat_sub_truncation_at_d_zero
#print axioms clause3_unconditional
#print axioms claim18_bound_forces_C2_bound_any_section
#print axioms claim18_bound_forces_C2_sqrt_bound
#print axioms right_inverse_opNorm_lower_bound
#print axioms sum_cube_slice
#print axioms sum_block_lastLayer
#print axioms lastLayerLift_sumSq
#print axioms qcSection_norm
#print axioms qcSection_norm_constant_sharp
#print axioms tiedClausesAt_iff
#print axioms tied_with_bound_ell_is_empty
#print axioms tied_with_bound_ell_cubed_admits_expansive
#print axioms transfer_satisfies_source_equation
#print axioms transfer_opNorm
#print axioms tiedClauses_iff
#print axioms untied_bound_admits_every_operator
#print axioms tied_rejects_expansive
#print axioms tied_satisfiable
#print axioms control_pair
#print axioms no_tiling_at_ell_zero
#print axioms tied_empty_at_ell_one
#print axioms rpow_at_d_zero_ne_one

end AdalyFormal.Balaban.Claim18Repaired

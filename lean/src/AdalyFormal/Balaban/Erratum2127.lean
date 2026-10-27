/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import AdalyFormal.Balaban.DiscreteNeumannPoincare

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# ERRATUM 2 — the printed justification of CMP96 `(2.127)` is FALSE from `L = 10`

Bałaban, *Propagators for Lattice Gauge Theories in a Background Field* (CMP 1996 = `[4]`),
printed p.245.  This file replaces a PYTHON-ONLY claim (`compute/lemma24_general_ell/PROGRESS.md`
lines 28/45, repeated in the docstring of `AdalyFormal.Balaban.Lemma24GeneralEll` lines 59/72) by a
kernel-checked theorem.

## §0. Source, VERBATIM from the page image (LAW-11)

`compute/lemma24_general_ell/zoom_2126.png`, `zoom_sentence_2126_2127.png`, `zoom_2127.png`
(600 dpi renders of CMP96 PDF page 23 = printed p.245; page offset 222,
`corpus/tools/page_offsets.json`, `constant_verified: true`).

`(2.126)` [TRANSCRIBED from the page image]:

> `L^{-d} Σ_{p⊂B(c)}|(∂₁B)(p)|² + |(Q₁B)(c)|² ≧ ⅓( L^{-d} Σ_{b⊂Δ'}|(∂B_μ)(b)|²`
> `  + L^{-2}|Σ_{x∈Δ'} L^{-(d-1)}B_μ(x)|² ) − L^{-d}Σ_{b⊂B(c₋)}|B(b)|² − L^{-d}Σ_{b⊂B(c₊)}|B(b)|².`

the sentence immediately following `(2.126)` [TRANSCRIBED from the page image]:

> "The terms in parentheses on the right-hand side can be written as
> `L^{-2}⟨B, (Δ_{Δ'}^{L^{-1},N} + Q'*_{Δ'} Q'_{Δ'}) B⟩`, where the operators are defined on a
> `d−1`-dimensional lattice.  **This quadratic form is bounded from below by
> `L^{-d-1} Σ_{x∈Δ'}|B_μ(x)|²`,** hence"

`(2.127)` [TRANSCRIBED from the page image] then replaces the parenthesis by
`L^{-d-1} Σ_{b∈B(c)}|B(b)|²` (the crossing bonds `b ∈ B(c)` are exactly the bonds `(x,μ)`,
`x ∈ Δ'`, so `Σ_{b∈B(c)}|B(b)|² = Σ_{x∈Δ'}|B_μ(x)|²`).

The bold-faced sentence is the *justification* of the `(2.126) → (2.127)` step.  It is ASSERTED,
with no proof and no citation, on that page (LAW-12: Bałaban defers proofs in place).

## §1. What this file proves [ASSEMBLED]

Write, for the `(d−1)`-dimensional face `Δ'` of side `L`,
`G := Σ_{b⊂Δ'}|(∂B_μ)(b)|²` (the bond sum **as displayed**, plain nearest-neighbour differences,
free/Neumann boundary), `T := Σ_{x∈Δ'}|B_μ(x)|²`, `m := L^{-(d-1)} Σ_{x∈Δ'} B_μ(x)`.  The printed
justification is the assertion

>   `P := L^{-d}·G + L^{-2}·m²  ≥  L^{-(d+1)}·T`.        (†)

* `printed_iff_poincare_general` — for EVERY `d = e+1 ≥ 1`, `(†)` is EXACTLY equivalent to the
  cross-sectional Poincaré inequality `Var ≤ L·G`, `Var := T − L^{e}·m²`.  The rank-one (`Q'*Q'`)
  term cancels IDENTICALLY; this is why the printed exponent is `−(d+1)` and it is `d`-independent.
* `printed_2127_holds_of_le_nine` — for `2 ≤ L ≤ 9` and **every** field on the `d=3` face, `(†)`
  HOLDS.  Proof: eight exact rational sum-of-squares certificates (`var1_le_two` … `var1_le_nine`,
  `ring`-checked) give the sharp-enough 1-D Neumann Poincaré constant `L`, lifted to the 2-D face
  by `var2_le_of_var1_le` (ANOVA; a constant-generic version of the tree's `var2_le_crude`).
* `printed_2127_fails_of_ten_le` — for **every** `L ≥ 10` there is an explicit rational field on
  the `d=3` face for which `(†)` FAILS.  Three explicit witnesses: `w10` (`L = 10`), `w11`
  (`L = 11`), and the linear field `i ↦ i` (`L ≥ 12`).
* `corrected_2127_general` / `corrected_2127` — the CORRECTED form: with the exponent lowered by
  one, `P ≥ L^{-(d+2)}·T` holds for EVERY `L ≥ 1` and every field.  This is exactly the exponent
  that `AdalyFormal.Balaban.Lemma24GeneralEll` (`Lemma24ConclusionCorrected`, `ell^{-5} = ell^{-(d+2)}`
  at `d=3`) already carries.
* `erratum_2127` — the three combined: **10 is exactly the threshold.**

## §2. Two findings about the campaign's own prior prose [ASSEMBLED, reported not fixed]

1. **The explicit witness quoted in `Lemma24GeneralEll.lean:73` and
   `compute/lemma24_general_ell/PROGRESS.md:45` — "`f(x) = x_ν` (linear across the face) has
   `V/G = L(L+1)/12 ≫ L`" — does NOT refute the printed step at `L = 10` or `L = 11`.**
   `L(L+1)/12 > L ⟺ L ≥ 12`; at `L = 10` it gives `55/6 = 9.1666… < 10` and at `L = 11` exactly
   `11`, not `> 11`.  The THRESHOLD `L = 10` in that prose is correct (it comes from the sharp
   Neumann eigenvalue `λ₁ = 2(1−cos(π/L))`, not from the linear field), but the exhibited witness
   does not reach it.  `linear_ratio` and `linear_not_witness_ten_eleven` below prove BOTH halves
   of this correction in the kernel; `w10`/`w11` supply the witnesses that were missing.
2. **`AdalyFormal.Balaban.CrossSectionPositivity`'s module docstring says `Var ≤ L·G` is
   "FALSE for `L ≥ 16`".**  That understates the defect: it is false from `L = 10`
   (`printed_2127_fails_of_ten_le` gives an explicit counterexample at every `L ≥ 10`).
   Not edited here (write-scope discipline); reported.

Neither finding is fixed in place by this file — this lane's write scope is `compute/erratum_2127/`.

## §3. Scope / what is NOT claimed

* The failure is of the printed justification **under the literal reading of the displayed sum**
  `Σ_{b⊂Δ'}|(∂B_μ)(b)|²` as the plain nearest-neighbour bond-difference sum on the face.
  `CrossSectionPositivity`'s module docstring documents that p.245's displays are mutually
  inconsistent across normalization conventions (`c = 1` vs `L^{-1}` vs `L^{-2}`);
  `printed_scaled_iff_poincare` below makes that dependence explicit and quantitative — the printed
  bound with the displayed gradient sum rescaled by `κ` is equivalent to `Var ≤ κ·L·G`, so any
  reading with `κ ≥ L` restores it (that is the tree's already-proved
  `cross_section_2127_operator_bound`).  **What this file settles is that the literal reading
  `κ = 1` fails, and fails from exactly `L = 10`.**
* Nothing here bears on `(2.126)` itself, on `(2.123)`–`(2.125)`, or on the covariant (general
  background `U`) version of `(2.127)`.
* The face is the `d = 3` case (`(d−1) = 2`) for the counterexample and the positive range;
  `printed_iff_poincare_general` and `corrected_2127_general` are `d`-generic.

## §4. L12 / S91 note

`printed_2127_fails_of_ten_le` and `erratum_2127` conclude with `∃`.  The existential is the
CONTENT (a counterexample), not free data handed to the prover: the witnesses are the explicit
named fields `colLift w10`, `colLift w11`, `colLift linearField`, and
`printed_2127_fails_explicit_*` state the failure for those named fields WITHOUT any existential.
Registry rows for `formal/S91_REGISTRY.tsv` are staged in `compute/erratum_2127/S91_ROWS.tsv`
(this lane may not write `formal/`).
-/

namespace AdalyFormal.Balaban.Erratum2127

open Finset
open AdalyFormal.Balaban.DiscretePoincare
open AdalyFormal.Balaban.DiscreteNeumannPoincare
open AdalyFormal.Balaban.CrossSectionPositivity

/-! ## §5. The printed assertion, and its exact `d`-generic reduction. -/

/-- The 1-D variance on `range n`, mean subtracted. -/
noncomputable def var1 (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, (g i - (∑ k ∈ range n, g k) / (n : ℝ)) ^ 2

/-- **The printed justification of `(2.127)`, `d`-generically and in the abstract.**
`d = e + 1`, face `Δ'` of `L^e` sites, `G` the displayed bond sum, `m` the face mean, `T` the face
sum of squares: the asserted bound is `G/L^(e+1) + m²/L² ≥ T/L^(e+2)`. -/
def PrintedAbstract (e : ℕ) (L G m T : ℝ) : Prop :=
  G / L ^ (e + 1) + m ^ 2 / L ^ 2 ≥ T / L ^ (e + 2)

/-- **THE EXACT REDUCTION, for EVERY `d = e+1`.** Given the variance decomposition
`T = Var + L^e·m²` (`L^e = |Δ'|`), the printed bound is equivalent to `Var ≤ L·G`.  The rank-one
`Q'*_{Δ'}Q'_{Δ'}` term cancels IDENTICALLY — which is why the printed exponent is exactly
`L^{-(d+1)}`.  [CORRECTED 2026-08-08 per Sol gate: the algebraic REDUCTION is `d`-independent
(this declaration is generic in `e`); the DEFECT is not — at `d = 1` (`e = 0`) the face has one
site, gradient and variance vanish, and the printed bound holds trivially for every `L`.  The
threshold theorems below are proved at `d = 3`; no dimension-generic failure is claimed.] -/
theorem printed_iff_poincare_general (e : ℕ) (L G m T Var : ℝ) (hL : 0 < L)
    (hdec : T = Var + L ^ e * m ^ 2) :
    PrintedAbstract e L G m T ↔ Var ≤ L * G := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hpow : (0 : ℝ) < L ^ (e + 2) := by positivity
  have hid : (G / L ^ (e + 1) + m ^ 2 / L ^ 2) - T / L ^ (e + 2)
      = (L * G - Var) / L ^ (e + 2) := by
    rw [hdec]
    field_simp
    ring
  rw [PrintedAbstract, ge_iff_le, ← sub_nonneg, hid, le_div_iff₀ hpow, zero_mul, sub_nonneg]

/-- **The normalization dependence, made explicit and quantitative.** If the displayed gradient sum
is read as `κ·G` (`κ = 1` is the literal plain-difference reading; the tree's already-proved
`cross_section_2127_operator_bound` is the `κ = L` reading), then the printed bound is equivalent to
`Var ≤ κ·L·G`. -/
theorem printed_scaled_iff_poincare (e : ℕ) (L G m T Var κ : ℝ) (hL : 0 < L)
    (hdec : T = Var + L ^ e * m ^ 2) :
    PrintedAbstract e L (κ * G) m T ↔ Var ≤ κ * (L * G) := by
  have h := printed_iff_poincare_general e L (κ * G) m T Var hL hdec
  rw [h]
  constructor
  · intro hh; linarith
  · intro hh; linarith

/-- **The CORRECTED exponent, `d`-generically.** Lowering the printed exponent by one power of `L`
makes the bound TRUE for every `L ≥ 1`, given only the (unconditional, mesh-uniform) Poincaré
inequality `Var ≤ L²·G`. -/
theorem corrected_2127_general (e : ℕ) (L G m T Var : ℝ) (hL : 1 ≤ L)
    (hdec : T = Var + L ^ e * m ^ 2) (hpoin : Var ≤ L ^ 2 * G) :
    G / L ^ (e + 1) + m ^ 2 / L ^ 2 ≥ T / L ^ (e + 3) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hpow : (0 : ℝ) < L ^ (e + 3) := by positivity
  have hLe : (0 : ℝ) < L ^ e := by positivity
  have hid : (G / L ^ (e + 1) + m ^ 2 / L ^ 2) - T / L ^ (e + 3)
      = (L ^ 2 * G - Var) / L ^ (e + 3) + m ^ 2 * (1 / L ^ 2 - 1 / L ^ 3) := by
    rw [hdec]
    field_simp
    ring
  have h1 : (0 : ℝ) ≤ (L ^ 2 * G - Var) / L ^ (e + 3) := by
    apply div_nonneg (by linarith) (le_of_lt hpow)
  have h2 : (0 : ℝ) ≤ m ^ 2 * (1 / L ^ 2 - 1 / L ^ 3) := by
    apply mul_nonneg (sq_nonneg m)
    have h3 : (1 : ℝ) / L ^ 3 ≤ 1 / L ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_pos hL0 2]
    linarith
  rw [ge_iff_le, ← sub_nonneg, hid]
  linarith

/-! ## §6. The eight exact rational SOS certificates: `var1 L g ≤ L · dirichletEnergy L g`,
`L = 2 … 9`.

Each is the `ring`-checked identity
`L·(L·E₁(g) − Var₁(g)) = Σ_k d_k · (linear form in g)²` with `d_k > 0` rational, in
reflection-adapted coordinates (`compute/erratum_2127/gen_sos.py`; the generator SIGNS NOTHING —
the identity is re-established by the kernel here).  `L·λ₁(L) ≥ 1` fails from `L = 10`, so no such
certificate exists for `L ≥ 10` — and §7 exhibits the counterexamples. -/

theorem var1_le_two (g : ℕ → ℝ) : var1 2 g ≤ 2 * dirichletEnergy 2 g := by
  have key : (2 : ℝ) * (2 * dirichletEnergy 2 g - var1 2 g) =
      (3 / 1) * ((1) * ((-1) * g 0 + g 1)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((1 : ℝ) * ((-1) * g 0 + g 1))]

theorem var1_le_three (g : ℕ → ℝ) : var1 3 g ≤ 3 * dirichletEnergy 3 g := by
  have key : (3 : ℝ) * (3 * dirichletEnergy 3 g - var1 3 g) =
      (4 / 1) * ((2) * ((-1) * g 0 + g 1) + (-1) * ((-1) * g 0 + g 2)) ^ 2
      + (3 / 1) * ((1) * ((-1) * g 0 + g 2)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((2 : ℝ) * ((-1) * g 0 + g 1) + (-1) * ((-1) * g 0 + g 2)),
    sq_nonneg ((1 : ℝ) * ((-1) * g 0 + g 2))]

theorem var1_le_four (g : ℕ → ℝ) : var1 4 g ≤ 4 * dirichletEnergy 4 g := by
  have key : (4 : ℝ) * (4 * dirichletEnergy 4 g - var1 4 g) =
      (2 / 3) * ((3) * (g 0 + (-1) * g 3) + (-4) * (g 1 + (-1) * g 2)) ^ 2
      + (34 / 3) * ((1) * (g 1 + (-1) * g 2)) ^ 2
      + (7 / 1) * ((1) * ((-1) * g 0 + g 1 + g 2 + (-1) * g 3)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((3 : ℝ) * (g 0 + (-1) * g 3) + (-4) * (g 1 + (-1) * g 2)),
    sq_nonneg ((1 : ℝ) * (g 1 + (-1) * g 2)),
    sq_nonneg ((1 : ℝ) * ((-1) * g 0 + g 1 + g 2 + (-1) * g 3))]

theorem var1_le_five (g : ℕ → ℝ) : var1 5 g ≤ 5 * dirichletEnergy 5 g := by
  have key : (5 : ℝ) * (5 * dirichletEnergy 5 g - var1 5 g) =
      (5 / 8) * ((4) * (g 0 + (-1) * g 4) + (-5) * (g 1 + (-1) * g 3)) ^ 2
      + (55 / 8) * ((1) * (g 1 + (-1) * g 3)) ^ 2
      + (1 / 44) * ((22) * (g 0 + (-2) * g 2 + g 4) + (-23) * (g 1 + (-2) * g 2 + g 3)) ^ 2
      + (505 / 44) * ((1) * (g 1 + (-2) * g 2 + g 3)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((4 : ℝ) * (g 0 + (-1) * g 4) + (-5) * (g 1 + (-1) * g 3)),
    sq_nonneg ((1 : ℝ) * (g 1 + (-1) * g 3)),
    sq_nonneg ((22 : ℝ) * (g 0 + (-2) * g 2 + g 4) + (-23) * (g 1 + (-2) * g 2 + g 3)),
    sq_nonneg ((1 : ℝ) * (g 1 + (-2) * g 2 + g 3))]

theorem var1_le_six (g : ℕ → ℝ) : var1 6 g ≤ 6 * dirichletEnergy 6 g := by
  have key : (6 : ℝ) * (6 * dirichletEnergy 6 g - var1 6 g) =
      (3 / 5) * ((5) * (g 0 + (-1) * g 5) + (-6) * (g 1 + (-1) * g 4)) ^ 2
      + (3 / 95) * ((19) * (g 1 + (-1) * g 4) + (-30) * (g 2 + (-1) * g 3)) ^ 2
      + (429 / 19) * ((1) * (g 2 + (-1) * g 3)) ^ 2
      + (17 / 2) * ((2) * ((-1) * g 0 + g 1 + g 4 + (-1) * g 5)
          + (-1) * ((-1) * g 0 + g 2 + g 3 + (-1) * g 5)) ^ 2
      + (15 / 2) * ((1) * ((-1) * g 0 + g 2 + g 3 + (-1) * g 5)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((5 : ℝ) * (g 0 + (-1) * g 5) + (-6) * (g 1 + (-1) * g 4)),
    sq_nonneg ((19 : ℝ) * (g 1 + (-1) * g 4) + (-30) * (g 2 + (-1) * g 3)),
    sq_nonneg ((1 : ℝ) * (g 2 + (-1) * g 3)),
    sq_nonneg ((2 : ℝ) * ((-1) * g 0 + g 1 + g 4 + (-1) * g 5)
      + (-1) * ((-1) * g 0 + g 2 + g 3 + (-1) * g 5)),
    sq_nonneg ((1 : ℝ) * ((-1) * g 0 + g 2 + g 3 + (-1) * g 5))]

theorem var1_le_seven (g : ℕ → ℝ) : var1 7 g ≤ 7 * dirichletEnergy 7 g := by
  have key : (7 : ℝ) * (7 * dirichletEnergy 7 g - var1 7 g) =
      (7 / 12) * ((6) * (g 0 + (-1) * g 6) + (-7) * (g 1 + (-1) * g 5)) ^ 2
      + (7 / 348) * ((29) * (g 1 + (-1) * g 5) + (-42) * (g 2 + (-1) * g 4)) ^ 2
      + (581 / 58) * ((1) * (g 2 + (-1) * g 4)) ^ 2
      + (1 / 88) * ((44) * (g 0 + (-2) * g 3 + g 6) + (-47) * (g 1 + (-2) * g 3 + g 5)
          + (2) * (g 2 + (-2) * g 3 + g 4)) ^ 2
      + (7 / 23672) * ((269) * (g 1 + (-2) * g 3 + g 5) + (-282) * (g 2 + (-2) * g 3 + g 4)) ^ 2
      + (12341 / 538) * ((1) * (g 2 + (-2) * g 3 + g 4)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((6 : ℝ) * (g 0 + (-1) * g 6) + (-7) * (g 1 + (-1) * g 5)),
    sq_nonneg ((29 : ℝ) * (g 1 + (-1) * g 5) + (-42) * (g 2 + (-1) * g 4)),
    sq_nonneg ((1 : ℝ) * (g 2 + (-1) * g 4)),
    sq_nonneg ((44 : ℝ) * (g 0 + (-2) * g 3 + g 6) + (-47) * (g 1 + (-2) * g 3 + g 5)
      + (2) * (g 2 + (-2) * g 3 + g 4)),
    sq_nonneg ((269 : ℝ) * (g 1 + (-2) * g 3 + g 5) + (-282) * (g 2 + (-2) * g 3 + g 4)),
    sq_nonneg ((1 : ℝ) * (g 2 + (-2) * g 3 + g 4))]

theorem var1_le_eight (g : ℕ → ℝ) : var1 8 g ≤ 8 * dirichletEnergy 8 g := by
  have key : (8 : ℝ) * (8 * dirichletEnergy 8 g - var1 8 g) =
      (4 / 7) * ((7) * (g 0 + (-1) * g 7) + (-8) * (g 1 + (-1) * g 6)) ^ 2
      + (4 / 287) * ((41) * (g 1 + (-1) * g 6) + (-56) * (g 2 + (-1) * g 5)) ^ 2
      + (4 / 6847) * ((167) * (g 2 + (-1) * g 5) + (-328) * (g 3 + (-1) * g 4)) ^ 2
      + (4868 / 167) * ((1) * (g 3 + (-1) * g 4)) ^ 2
      + (1 / 61) * ((61) * ((-1) * g 0 + g 1 + g 6 + (-1) * g 7)
          + (-31) * ((-1) * g 0 + g 2 + g 5 + (-1) * g 7)
          + (1) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7)) ^ 2
      + (30 / 1403) * ((46) * ((-1) * g 0 + g 2 + g 5 + (-1) * g 7)
          + (-31) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7)) ^ 2
      + (194 / 23) * ((1) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((7 : ℝ) * (g 0 + (-1) * g 7) + (-8) * (g 1 + (-1) * g 6)),
    sq_nonneg ((41 : ℝ) * (g 1 + (-1) * g 6) + (-56) * (g 2 + (-1) * g 5)),
    sq_nonneg ((167 : ℝ) * (g 2 + (-1) * g 5) + (-328) * (g 3 + (-1) * g 4)),
    sq_nonneg ((1 : ℝ) * (g 3 + (-1) * g 4)),
    sq_nonneg ((61 : ℝ) * ((-1) * g 0 + g 1 + g 6 + (-1) * g 7)
      + (-31) * ((-1) * g 0 + g 2 + g 5 + (-1) * g 7)
      + (1) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7)),
    sq_nonneg ((46 : ℝ) * ((-1) * g 0 + g 2 + g 5 + (-1) * g 7)
      + (-31) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7)),
    sq_nonneg ((1 : ℝ) * ((-1) * g 0 + g 3 + g 4 + (-1) * g 7))]

theorem var1_le_nine (g : ℕ → ℝ) : var1 9 g ≤ 9 * dirichletEnergy 9 g := by
  have key : (9 : ℝ) * (9 * dirichletEnergy 9 g - var1 9 g) =
      (9 / 16) * ((8) * (g 0 + (-1) * g 8) + (-9) * (g 1 + (-1) * g 7)) ^ 2
      + (9 / 880) * ((55) * (g 1 + (-1) * g 7) + (-72) * (g 2 + (-1) * g 6)) ^ 2
      + (9 / 31570) * ((287) * (g 2 + (-1) * g 6) + (-495) * (g 3 + (-1) * g 5)) ^ 2
      + (1908 / 287) * ((1) * (g 3 + (-1) * g 5)) ^ 2
      + (1 / 148) * ((74) * (g 0 + (-2) * g 4 + g 8) + (-79) * (g 1 + (-2) * g 4 + g 7)
          + (2) * (g 2 + (-2) * g 4 + g 6) + (2) * (g 3 + (-2) * g 4 + g 5)) ^ 2
      + (9 / 85988) * ((581) * (g 1 + (-2) * g 4 + g 7) + (-632) * (g 2 + (-2) * g 4 + g 6)
          + (34) * (g 3 + (-2) * g 4 + g 5)) ^ 2
      + (3 / 1783670) * ((4605) * (g 2 + (-2) * g 4 + g 6)
          + (-4813) * (g 3 + (-2) * g 4 + g 5)) ^ 2
      + (58929 / 1535) * ((1) * (g 3 + (-2) * g 4 + g 5)) ^ 2 := by
    simp only [var1, dirichletEnergy]
    norm_num [Finset.sum_range_succ]
    ring
  nlinarith [sq_nonneg ((8 : ℝ) * (g 0 + (-1) * g 8) + (-9) * (g 1 + (-1) * g 7)),
    sq_nonneg ((55 : ℝ) * (g 1 + (-1) * g 7) + (-72) * (g 2 + (-1) * g 6)),
    sq_nonneg ((287 : ℝ) * (g 2 + (-1) * g 6) + (-495) * (g 3 + (-1) * g 5)),
    sq_nonneg ((1 : ℝ) * (g 3 + (-1) * g 5)),
    sq_nonneg ((74 : ℝ) * (g 0 + (-2) * g 4 + g 8) + (-79) * (g 1 + (-2) * g 4 + g 7)
      + (2) * (g 2 + (-2) * g 4 + g 6) + (2) * (g 3 + (-2) * g 4 + g 5)),
    sq_nonneg ((581 : ℝ) * (g 1 + (-2) * g 4 + g 7) + (-632) * (g 2 + (-2) * g 4 + g 6)
      + (34) * (g 3 + (-2) * g 4 + g 5)),
    sq_nonneg ((4605 : ℝ) * (g 2 + (-2) * g 4 + g 6) + (-4813) * (g 3 + (-2) * g 4 + g 5)),
    sq_nonneg ((1 : ℝ) * (g 3 + (-2) * g 4 + g 5))]

/-! ## §7. ANOVA lift with a GENERIC constant. -/

/-- **Constant-generic 2-D lift of a 1-D Neumann Poincaré inequality.**  If `var1 n g ≤ C·E₁(g)`
for every 1-D field, then `var2 n f ≤ C·gradEnergy2 n f` for every field on the `n×n` face.
Same ANOVA argument as `DiscreteNeumannPoincare.var2_le_crude` (LAW-19: that proof, with its
concrete constant `n(n−1)/2` abstracted to an arbitrary `C ≥ 0` — the argument never uses the
value of the constant, only `0 ≤ C`). -/
theorem var2_le_of_var1_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h1 : ∀ g : ℕ → ℝ, var1 n g ≤ C * dirichletEnergy n g) (f : ℕ → ℕ → ℝ) :
    var2 n f ≤ C * gradEnergy2 n f := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [var2, gradEnergy2, horEnergy, verEnergy]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
  rw [var2]
  set m : ℝ := sum2 n f / (n : ℝ) ^ 2 with hm
  set r : ℕ → ℝ := fun i => (∑ j ∈ range n, f i j) / (n : ℝ) with hr
  have hper : ∀ i ∈ range n, ∑ j ∈ range n, (f i j - m) ^ 2
      = (∑ j ∈ range n, (f i j - r i) ^ 2) + (n : ℝ) * (r i - m) ^ 2 := by
    intro i _
    have hrow : ∑ j ∈ range n, (f i j - r i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      simp only [hr]
      field_simp
      ring
    calc ∑ j ∈ range n, (f i j - m) ^ 2
        = ∑ j ∈ range n,
            ((f i j - r i) ^ 2 + 2 * (r i - m) * (f i j - r i) + (r i - m) ^ 2) := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ j ∈ range n, (f i j - r i) ^ 2)
            + 2 * (r i - m) * (∑ j ∈ range n, (f i j - r i)) + (n : ℝ) * (r i - m) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, card_range, nsmul_eq_mul]
      _ = (∑ j ∈ range n, (f i j - r i) ^ 2) + (n : ℝ) * (r i - m) ^ 2 := by
          rw [hrow]; ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
  have hA : (∑ i ∈ range n, ∑ j ∈ range n, (f i j - r i) ^ 2) ≤ C * horEnergy n f := by
    rw [horEnergy, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := h1 (fun j => f i j)
    rw [var1] at h
    simp only [hr]
    exact h
  have hB : (∑ i ∈ range n, (n : ℝ) * (r i - m) ^ 2) ≤ C * verEnergy n f := by
    have hrsum : ∑ i ∈ range n, r i = sum2 n f / (n : ℝ) := by
      simp only [hr]
      rw [← Finset.sum_div, sum2]
    have hm_r : (∑ i ∈ range n, r i) / (n : ℝ) = m := by
      rw [hrsum, hm, pow_two, div_div]
    have hvar_r : ∑ i ∈ range n, (r i - m) ^ 2 ≤ C * dirichletEnergy n r := by
      have h2 := h1 r
      rw [var1, hm_r] at h2
      exact h2
    have hDEr : dirichletEnergy n r ≤ verEnergy n f / (n : ℝ) := by
      have hpt : ∀ i ∈ range (n - 1), (r (i + 1) - r i) ^ 2
          ≤ (1 / (n : ℝ)) * ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 := by
        intro i _
        have hdiff : r (i + 1) - r i
            = (∑ j ∈ range n, (f (i + 1) j - f i j)) / (n : ℝ) := by
          simp only [hr]
          rw [Finset.sum_sub_distrib, sub_div]
        rw [hdiff, div_pow]
        have hCS := sq_sum_le_card_mul_sum_sq (s := range n)
          (f := fun j => f (i + 1) j - f i j)
        rw [card_range] at hCS
        have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
        rw [div_le_iff₀ hn2]
        have hrw : (1 / (n : ℝ)) * (∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2) * (n : ℝ) ^ 2
            = (n : ℝ) * (∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2) := by
          field_simp
        rw [hrw]; exact hCS
      calc dirichletEnergy n r
          = ∑ i ∈ range (n - 1), (r (i + 1) - r i) ^ 2 := by rw [dirichletEnergy]
        _ ≤ ∑ i ∈ range (n - 1), (1 / (n : ℝ)) * ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 :=
            Finset.sum_le_sum hpt
        _ = (1 / (n : ℝ)) * ∑ i ∈ range (n - 1), ∑ j ∈ range n, (f (i + 1) j - f i j) ^ 2 := by
            rw [Finset.mul_sum]
        _ = (1 / (n : ℝ)) * verEnergy n f := by
            rw [verEnergy]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _; rw [dirichletEnergy]
        _ = verEnergy n f / (n : ℝ) := by ring
    rw [← Finset.mul_sum]
    have hstep1 : (n : ℝ) * ∑ i ∈ range n, (r i - m) ^ 2
        ≤ (n : ℝ) * (C * dirichletEnergy n r) :=
      mul_le_mul_of_nonneg_left hvar_r (le_of_lt hnpos)
    have hstep2 : (n : ℝ) * (C * dirichletEnergy n r)
        ≤ (n : ℝ) * (C * (verEnergy n f / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDEr hC) (le_of_lt hnpos)
    have hfinal : (n : ℝ) * (C * (verEnergy n f / (n : ℝ))) = C * verEnergy n f := by
      field_simp
    linarith [hstep1, hstep2, hfinal.le, hfinal.ge]
  rw [gradEnergy2, mul_add]
  linarith [hA, hB]

/-! ## §8. Column lift: a 1-D field, extended constantly along the other face direction. -/

/-- Extend a 1-D field `g` to the `n×n` face constantly in the first index. -/
def colLift (g : ℕ → ℝ) : ℕ → ℕ → ℝ := fun _ j => g j

theorem sum2_colLift (n : ℕ) (g : ℕ → ℝ) :
    sum2 n (colLift g) = (n : ℝ) * ∑ j ∈ range n, g j := by
  simp [sum2, colLift, Finset.sum_const, card_range, nsmul_eq_mul]

theorem var2_colLift (n : ℕ) (g : ℕ → ℝ) :
    var2 n (colLift g) = (n : ℝ) * var1 n g := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [var2, var1]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmean : sum2 n (colLift g) / (n : ℝ) ^ 2 = (∑ k ∈ range n, g k) / (n : ℝ) := by
    rw [sum2_colLift, pow_two, ← div_div, mul_div_assoc, mul_comm, mul_div_assoc,
      div_self hn, mul_one]
  rw [var2, var1, hmean]
  rw [Finset.sum_congr rfl (fun i _ => rfl)]
  simp only [colLift]
  rw [Finset.sum_const, card_range, nsmul_eq_mul]

theorem gradEnergy2_colLift (n : ℕ) (g : ℕ → ℝ) :
    gradEnergy2 n (colLift g) = (n : ℝ) * dirichletEnergy n g := by
  have hhor : horEnergy n (colLift g) = (n : ℝ) * dirichletEnergy n g := by
    simp [horEnergy, colLift, Finset.sum_const, card_range, nsmul_eq_mul]
  have hver : verEnergy n (colLift g) = 0 := by
    simp [verEnergy, colLift, dirichletEnergy]
  rw [gradEnergy2, hhor, hver, add_zero]

/-! ## §9. The three explicit counterexample fields. -/

/-- Witness at `L = 10`: the rounded first Neumann mode `x ↦ 1000·cos(π(x+½)/10)`.
`var1 = 5000652`, `E₁ = 489500`, ratio `= 5000652/489500 = 10.2158… > 10`. -/
noncomputable def w10 : ℕ → ℝ
  | 0 => 988
  | 1 => 891
  | 2 => 707
  | 3 => 454
  | 4 => 156
  | 5 => -156
  | 6 => -454
  | 7 => -707
  | 8 => -891
  | 9 => -988
  | _ => 0

/-- Witness at `L = 11`: the rounded first Neumann mode `x ↦ 1000·cos(π(x+½)/11)`.
`var1 = 5503882`, `E₁ = 445892`, ratio `= 12.3435… > 11`. -/
noncomputable def w11 : ℕ → ℝ
  | 0 => 990
  | 1 => 910
  | 2 => 756
  | 3 => 541
  | 4 => 282
  | 5 => 0
  | 6 => -282
  | 7 => -541
  | 8 => -756
  | 9 => -910
  | 10 => -990
  | _ => 0

/-- The linear field `i ↦ i` — the witness quoted in the campaign's prior prose.  It works for
`L ≥ 12` and, as `linear_not_witness_ten_eleven` shows, NOT at `L = 10, 11`. -/
noncomputable def linearField : ℕ → ℝ := fun i => (i : ℝ)

theorem w10_witness : (10 : ℝ) * dirichletEnergy 10 w10 < var1 10 w10 := by
  have hE : dirichletEnergy 10 w10 = 489500 := by
    simp only [dirichletEnergy]
    norm_num [Finset.sum_range_succ, w10]
  have hV : var1 10 w10 = 5000652 := by
    simp only [var1]
    norm_num [Finset.sum_range_succ, w10]
  rw [hE, hV]; norm_num

theorem w11_witness : (11 : ℝ) * dirichletEnergy 11 w11 < var1 11 w11 := by
  have hE : dirichletEnergy 11 w11 = 445892 := by
    simp only [dirichletEnergy]
    norm_num [Finset.sum_range_succ, w11]
  have hV : var1 11 w11 = 5503882 := by
    simp only [var1]
    norm_num [Finset.sum_range_succ, w11]
  rw [hE, hV]; norm_num

/-! ### The linear field in closed form. -/

theorem sum_range_cast (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem sum_range_cast_sq (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem dirichlet_linear (n : ℕ) (hn : 1 ≤ n) :
    dirichletEnergy n linearField = (n : ℝ) - 1 := by
  rw [dirichletEnergy]
  have hpt : ∀ i ∈ range (n - 1), (linearField (i + 1) - linearField i) ^ 2 = 1 := by
    intro i _; simp only [linearField]; push_cast; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, card_range, nsmul_eq_mul, mul_one,
    Nat.cast_sub hn, Nat.cast_one]

theorem var1_linear (n : ℕ) (hn : 1 ≤ n) :
    var1 n linearField = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) + 1) / 12 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hexp : var1 n linearField
      = (∑ i ∈ range n, (linearField i) ^ 2)
        - (∑ k ∈ range n, linearField k) ^ 2 / (n : ℝ) := by
    rw [var1]
    have hpt : ∀ i ∈ range n,
        (linearField i - (∑ k ∈ range n, linearField k) / (n : ℝ)) ^ 2
        = (linearField i) ^ 2
          - 2 * ((∑ k ∈ range n, linearField k) / (n : ℝ)) * linearField i
          + ((∑ k ∈ range n, linearField k) / (n : ℝ)) ^ 2 := by
      intro i _; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  rw [hexp]
  simp only [linearField]
  rw [sum_range_cast, sum_range_cast_sq]
  field_simp
  ring

/-- **The linear field's exact Rayleigh ratio: `var1 / E₁ = L(L+1)/12`.** -/
theorem linear_ratio (n : ℕ) (hn : 2 ≤ n) :
    var1 n linearField = ((n : ℝ) * ((n : ℝ) + 1) / 12) * dirichletEnergy n linearField := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  rw [var1_linear n h1, dirichlet_linear n h1]
  ring

/-- **The linear field refutes the printed step exactly from `L = 12`.** -/
theorem linear_witness (n : ℕ) (hn : 12 ≤ n) :
    (n : ℝ) * dirichletEnergy n linearField < var1 n linearField := by
  have h1 : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
  have hnR : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [var1_linear n h1, dirichlet_linear n h1]
  have hp1 : (0 : ℝ) < (n : ℝ) := by linarith
  have hp2 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hp3 : (0 : ℝ) < (n : ℝ) - 11 := by linarith
  nlinarith [mul_pos (mul_pos hp1 hp2) hp3]

/-- **FINDING 1 (correction to the campaign's own prose).**  The linear field — the witness quoted
in `Lemma24GeneralEll.lean:73` and `compute/lemma24_general_ell/PROGRESS.md:45` — does NOT refute
the printed step at `L = 10` or `L = 11`: at `L = 10` its ratio is `55/6 < 10`, and at `L = 11` it
is exactly `11`, not `> 11`. -/
theorem linear_not_witness_ten_eleven :
    ¬ ((10 : ℝ) * dirichletEnergy 10 linearField < var1 10 linearField)
    ∧ ¬ ((11 : ℝ) * dirichletEnergy 11 linearField < var1 11 linearField) := by
  constructor
  · rw [var1_linear 10 (by norm_num), dirichlet_linear 10 (by norm_num)]; norm_num
  · rw [var1_linear 11 (by norm_num), dirichlet_linear 11 (by norm_num)]; norm_num

/-! ## §10. The printed bound on the `d = 3` face, and the erratum. -/

/-- **The printed justification of `(2.127)` at `d = 3`, LITERAL reading**, as a statement about a
field `f` on the `L×L` face: `G/L³ + (Σf/L²)²/L² ≥ (Σf²)/L⁴`, with `G = gradEnergy2` the displayed
plain nearest-neighbour bond sum. -/
def Printed2127 (L : ℕ) (f : ℕ → ℕ → ℝ) : Prop :=
  gradEnergy2 L f / (L : ℝ) ^ 3 + (sum2 L f / (L : ℝ) ^ 2) ^ 2 / (L : ℝ) ^ 2
    ≥ sumSq2 L f / (L : ℝ) ^ 4

/-- **The corrected form** — the same inequality with the exponent lowered by one power of `L`. -/
def Corrected2127 (L : ℕ) (f : ℕ → ℕ → ℝ) : Prop :=
  gradEnergy2 L f / (L : ℝ) ^ 3 + (sum2 L f / (L : ℝ) ^ 2) ^ 2 / (L : ℝ) ^ 2
    ≥ sumSq2 L f / (L : ℝ) ^ 5

/-- The `d = 3` face instance of the exact reduction: the printed bound holds for `f` iff
`var2 L f ≤ L·gradEnergy2 L f`. -/
theorem printed_iff_var2 (L : ℕ) (hL : 1 ≤ L) (f : ℕ → ℕ → ℝ) :
    Printed2127 L f ↔ var2 L f ≤ (L : ℝ) * gradEnergy2 L f := by
  have hpos : 0 < L := hL
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hpos
  set f' : ℕ × ℕ → ℝ := fun p => f p.1 p.2 with hf'
  set s : Finset (ℕ × ℕ) := (range L) ×ˢ (range L) with hs_def
  have hcardnat : s.card = L * L := by rw [hs_def, Finset.card_product, card_range]
  have hcard : (s.card : ℝ) = (L : ℝ) ^ 2 := by rw [hcardnat, Nat.cast_mul, ← pow_two]
  have hs : s.Nonempty :=
    ⟨(0, 0), by rw [hs_def, Finset.mem_product]; exact ⟨mem_range.mpr hpos, mem_range.mpr hpos⟩⟩
  have hsum : ∑ p ∈ s, f' p = sum2 L f := by rw [hs_def, Finset.sum_product]; rfl
  have hsumsq : ∑ p ∈ s, (f' p) ^ 2 = sumSq2 L f := by rw [hs_def, Finset.sum_product]; rfl
  have hvar : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2 = var2 L f := by
    rw [hsum, hcardnat, Nat.cast_mul, ← pow_two, hs_def, Finset.sum_product, var2]
  have key := cross_section_2127_iff_poincare s f' hs (L : ℝ) (gradEnergy2 L f) hLR hcard
  rw [hvar] at key
  rw [hsum, hsumsq] at key
  exact key

/-- **PART (i) — the printed justification HOLDS for `2 ≤ L ≤ 9`.**  Every field on the `L×L` face
satisfies the bound asserted on p.245. -/
theorem printed_2127_holds_of_le_nine (L : ℕ) (hL2 : 2 ≤ L) (hL9 : L ≤ 9) (f : ℕ → ℕ → ℝ) :
    Printed2127 L f := by
  have h1 : (1 : ℕ) ≤ L := le_trans (by norm_num) hL2
  rw [printed_iff_var2 L h1]
  have hC : (0 : ℝ) ≤ (L : ℝ) := by positivity
  refine var2_le_of_var1_le L (L : ℝ) hC ?_ f
  interval_cases L
  · exact fun g => by simpa using var1_le_two g
  · exact fun g => by simpa using var1_le_three g
  · exact fun g => by simpa using var1_le_four g
  · exact fun g => by simpa using var1_le_five g
  · exact fun g => by simpa using var1_le_six g
  · exact fun g => by simpa using var1_le_seven g
  · exact fun g => by simpa using var1_le_eight g
  · exact fun g => by simpa using var1_le_nine g

/-- Transfer of a 1-D counterexample to the face. -/
theorem printed_fails_of_var1 (L : ℕ) (hL : 1 ≤ L) (g : ℕ → ℝ)
    (hg : (L : ℝ) * dirichletEnergy L g < var1 L g) :
    ¬ Printed2127 L (colLift g) := by
  rw [printed_iff_var2 L hL]
  rw [var2_colLift, gradEnergy2_colLift]
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  intro hcon
  nlinarith [hcon, hLR, hg]

theorem printed_2127_fails_explicit_ten : ¬ Printed2127 10 (colLift w10) :=
  printed_fails_of_var1 10 (by norm_num) w10 (by simpa using w10_witness)

theorem printed_2127_fails_explicit_eleven : ¬ Printed2127 11 (colLift w11) :=
  printed_fails_of_var1 11 (by norm_num) w11 (by simpa using w11_witness)

theorem printed_2127_fails_explicit_linear (L : ℕ) (hL : 12 ≤ L) :
    ¬ Printed2127 L (colLift linearField) :=
  printed_fails_of_var1 L (le_trans (by norm_num) hL) linearField (linear_witness L hL)

/-- **PART (ii) — the printed justification FAILS for EVERY `L ≥ 10`**, with an explicit rational
counterexample field on the `L×L` face. -/
theorem printed_2127_fails_of_ten_le (L : ℕ) (hL : 10 ≤ L) :
    ∃ f : ℕ → ℕ → ℝ, ¬ Printed2127 L f := by
  rcases eq_or_lt_of_le hL with h | h10
  · exact ⟨colLift w10, by rw [← h]; exact printed_2127_fails_explicit_ten⟩
  · have h11 : 11 ≤ L := h10
    rcases eq_or_lt_of_le h11 with h' | h11'
    · exact ⟨colLift w11, by rw [← h']; exact printed_2127_fails_explicit_eleven⟩
    · exact ⟨colLift linearField, printed_2127_fails_explicit_linear L h11'⟩

/-- **PART (iii) — the CORRECTED bound holds for every `L ≥ 1` and every field.**  The exponent is
`L^{-(d+2)} = L^{-5}` at `d = 3` — exactly the exponent
`AdalyFormal.Balaban.Lemma24GeneralEll.Lemma24ConclusionCorrected` carries. -/
theorem corrected_2127 (L : ℕ) (hL : 1 ≤ L) (f : ℕ → ℕ → ℝ) : Corrected2127 L f := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
  have hdec : sumSq2 L f = var2 L f + (L : ℝ) ^ 2 * (sum2 L f / (L : ℝ) ^ 2) ^ 2 := by
    set f' : ℕ × ℕ → ℝ := fun p => f p.1 p.2 with hf'
    set s : Finset (ℕ × ℕ) := (range L) ×ˢ (range L) with hs_def
    have hpos : 0 < L := hL
    have hcardnat : s.card = L * L := by rw [hs_def, Finset.card_product, card_range]
    have hcard : (s.card : ℝ) = (L : ℝ) ^ 2 := by rw [hcardnat, Nat.cast_mul, ← pow_two]
    have hs : s.Nonempty :=
      ⟨(0, 0), by rw [hs_def, Finset.mem_product]; exact ⟨mem_range.mpr hpos, mem_range.mpr hpos⟩⟩
    have hsum : ∑ p ∈ s, f' p = sum2 L f := by rw [hs_def, Finset.sum_product]; rfl
    have hsumsq : ∑ p ∈ s, (f' p) ^ 2 = sumSq2 L f := by rw [hs_def, Finset.sum_product]; rfl
    have hvar : ∑ x ∈ s, (f' x - (∑ y ∈ s, f' y) / (s.card : ℝ)) ^ 2 = var2 L f := by
      rw [hsum, hcardnat, Nat.cast_mul, ← pow_two, hs_def, Finset.sum_product, var2]
    have hsplit := sq_sum_split s f' hs
    rw [hsumsq, hvar, hsum, hcard] at hsplit
    exact hsplit
  have hpoin : var2 L f ≤ (L : ℝ) ^ 2 * gradEnergy2 L f := var2_le_nsq L f
  have := corrected_2127_general 2 (L : ℝ) (gradEnergy2 L f) (sum2 L f / (L : ℝ) ^ 2)
    (sumSq2 L f) (var2 L f) hL1 hdec hpoin
  simpa [Corrected2127] using this

/-! ## §12. SHARPNESS / FALSIFIABILITY — the boundary proved from BOTH sides in the kernel.

These are the "mutants" of the threshold `10` and of the exponents, discharged as THEOREMS rather
than as compile-failures: each states that the mutated claim is FALSE.  (Compile-failure mutants
of the SOS identities and of the abstract reduction are additionally run from
`compute/erratum_2127/mut/`; see `MUTATION_RESULTS.tsv`.) -/

/-- The witness field is not the zero field (no degenerate/vacuous counterexample). -/
theorem w10_ne_zero : colLift w10 0 0 ≠ 0 := by
  simp only [colLift]
  norm_num [w10]

theorem w11_ne_zero : colLift w11 0 0 ≠ 0 := by
  simp only [colLift]
  norm_num [w11]

theorem linearField_ne_zero : colLift linearField 0 1 ≠ 0 := by
  simp only [colLift, linearField]
  norm_num

/-- **Mutant `L ≤ 9 ↦ L ≤ 10` in the positive part is FALSE.**  There is no 1-D Poincaré constant
`10` at `L = 10`: `w10` refutes it. -/
theorem no_var1_le_ten : ¬ (∀ g : ℕ → ℝ, var1 10 g ≤ 10 * dirichletEnergy 10 g) := by
  intro h
  have := h w10
  have h2 := w10_witness
  linarith

/-- Same at `L = 11`. -/
theorem no_var1_le_eleven : ¬ (∀ g : ℕ → ℝ, var1 11 g ≤ 11 * dirichletEnergy 11 g) := by
  intro h
  have := h w11
  have h2 := w11_witness
  linarith

/-- **The threshold is sharp, LOWER side:** at `L = 9` the printed bound holds for EVERY field. -/
theorem threshold_sharp_below : ∀ f : ℕ → ℕ → ℝ, Printed2127 9 f :=
  fun f => printed_2127_holds_of_le_nine 9 (by norm_num) (by norm_num) f

/-- **The threshold is sharp, UPPER side:** at `L = 10` it already fails. -/
theorem threshold_sharp_at : ¬ (∀ f : ℕ → ℕ → ℝ, Printed2127 10 f) :=
  fun h => printed_2127_fails_explicit_ten (h _)

/-- **Mutant `10 ↦ 9` in the negative part is FALSE:** there is NO counterexample at `L = 9`. -/
theorem no_counterexample_at_nine : ¬ (∃ f : ℕ → ℕ → ℝ, ¬ Printed2127 9 f) := by
  rintro ⟨f, hf⟩
  exact hf (threshold_sharp_below f)

/-- **Mutant on the CORRECTED exponent: `L^{-(d+2)} ↦ L^{-(d+1)}` (i.e. the printed exponent) is
FALSE** — the corrected statement cannot be strengthened back to the printed one, at any `L ≥ 10`.
(`Corrected2127` with `L^5` replaced by `L^4` IS `Printed2127`.) -/
theorem corrected_exponent_cannot_be_printed_exponent (L : ℕ) (hL : 10 ≤ L) :
    ¬ (∀ f : ℕ → ℕ → ℝ,
      gradEnergy2 L f / (L : ℝ) ^ 3 + (sum2 L f / (L : ℝ) ^ 2) ^ 2 / (L : ℝ) ^ 2
        ≥ sumSq2 L f / (L : ℝ) ^ 4) := by
  intro h
  obtain ⟨f, hf⟩ := printed_2127_fails_of_ten_le L hL
  exact hf (h f)

/-! ## §11. The erratum, as one theorem. -/

/-- **ERRATUM 2 (CMP96 p.245, the sentence between `(2.126)` and `(2.127)`).**

Under the literal reading of the displayed bond sum `Σ_{b⊂Δ'}|(∂B_μ)(b)|²` (plain nearest-neighbour
differences on the `(d−1)`-dimensional face, `d = 3`):

1. the printed bound `L^{-d}G + L^{-2}m² ≥ L^{-(d+1)}T` HOLDS for every field when `2 ≤ L ≤ 9`;
2. it FAILS, with an explicit rational counterexample field, for EVERY `L ≥ 10`;
3. the CORRECTED bound `L^{-d}G + L^{-2}m² ≥ L^{-(d+2)}T` holds for every `L ≥ 1` and every field.

So `L = 10` is exactly the threshold, and the printed exponent is off by one power of `L`. -/
theorem erratum_2127 :
    (∀ L : ℕ, 2 ≤ L → L ≤ 9 → ∀ f : ℕ → ℕ → ℝ, Printed2127 L f)
    ∧ (∀ L : ℕ, 10 ≤ L → ∃ f : ℕ → ℕ → ℝ, ¬ Printed2127 L f)
    ∧ (∀ L : ℕ, 1 ≤ L → ∀ f : ℕ → ℕ → ℝ, Corrected2127 L f) :=
  ⟨printed_2127_holds_of_le_nine, printed_2127_fails_of_ten_le, corrected_2127⟩

#print axioms sum2_colLift
#print axioms sum_range_cast
#print axioms sum_range_cast_sq
#print axioms dirichlet_linear
#print axioms var1_linear
#print axioms printed_fails_of_var1
#print axioms printed_iff_poincare_general
#print axioms printed_scaled_iff_poincare
#print axioms corrected_2127_general
#print axioms var1_le_two
#print axioms var1_le_three
#print axioms var1_le_four
#print axioms var1_le_five
#print axioms var1_le_six
#print axioms var1_le_seven
#print axioms var1_le_eight
#print axioms var1_le_nine
#print axioms var2_le_of_var1_le
#print axioms var2_colLift
#print axioms gradEnergy2_colLift
#print axioms w10_witness
#print axioms w11_witness
#print axioms linear_ratio
#print axioms linear_witness
#print axioms linear_not_witness_ten_eleven
#print axioms printed_iff_var2
#print axioms printed_2127_holds_of_le_nine
#print axioms printed_2127_fails_explicit_ten
#print axioms printed_2127_fails_explicit_eleven
#print axioms printed_2127_fails_explicit_linear
#print axioms printed_2127_fails_of_ten_le
#print axioms corrected_2127
#print axioms w10_ne_zero
#print axioms w11_ne_zero
#print axioms linearField_ne_zero
#print axioms no_var1_le_ten
#print axioms no_var1_le_eleven
#print axioms threshold_sharp_below
#print axioms threshold_sharp_at
#print axioms no_counterexample_at_nine
#print axioms corrected_exponent_cannot_be_printed_exponent
#print axioms erratum_2127

end AdalyFormal.Balaban.Erratum2127

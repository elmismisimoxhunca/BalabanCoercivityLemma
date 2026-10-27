# Prosecution — s2-class-implication

Prosecutor: second model family (this thread). Target: the uncompiled draft
[ClassImplication.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s2-class-implication/ClassImplication.lean)
and its note [s2-class-implication.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/s2-class-implication.md),
item S-2 of `paper/OPEN_ITEMS.md`. Mandate: refute if possible — wrong quantifier order, dropped
hypothesis, both-endpoint/touching swap, even-ell/odd-ell mix-up, diagnostic called a theorem,
`sorry` or edits outside `AHP/`.

**Verdict: NOT REFUTED.** No mathematical defect found. The draft stands as what it says it is:
an uncompiled, self-consistent draft whose statements match the frozen definitions and whose
claimed implications are direction-correct. Two non-mathematical hazards and the disclosed
vacuity gap are recorded below (F-1, F-2, F-3). `compiled` stays `false`; nothing here is a
theorem of the project tree.

No Lean, lake, or elan was run (machine limit; no oleans). All checks below are by reading.

## What was checked against the frozen tree

| Draft object | Frozen definition read | Match |
|---|---|---|
| `TouchBond`, `CubeBond.toTouch` | `CubeBond` = both endpoints, `ZStatementP428.lean:145` | yes |
| `cornerA..D`, `boundary_is_square` | `periodicPlaquetteBoundaryEdges`, `ClayStatement.lean:1295`: `{(x,μ), (shift x μ,ν), (shift x ν,μ), (x,ν)}` with `μ = p.2.1.1 < ν = p.2.1.2` (`PeriodicPlaquetteDirections`, line 1265) | yes, all four edges and corner identifications correct, including the `shift_comm` swap on edge CD |
| `coord_shift_ne`, `cornerD_comm` | `shift_ne`/`shift_comm`, `ZR8Class.lean:52,87` | yes, signatures and implicit argument order match |
| `mem_siteBox_iff` | `siteBox`, `ZStatementP428.lean:122` | yes (`Iff.rfl`-defeq) |
| `cubeAnte_iff_plaqIn` | `plaqIn`, `ZR2Ops2.lean:74` | yes, `plaqIn` is literally `CubeBond` on all four boundary bonds |
| `CoversPlaqTouch` | `CoversPlaqOm0c`, `ZR6A.lean:27` | yes, exact substitution of `TouchBond` for both `CubeBond` occurrences (antecedent and consequent); both share `IsClassCube ell M c k` at the same `c` |
| `CoversOm0c` has no `CubeBond` | `ZR2A.lean:107` | confirmed, sites only |
| `CurlReadsTouch`, `PerCubeRegularTouch` | `CurlReads` `ZR2A.lean:35`, `PerCubeRegular2` `ZR2A.lean:47` | yes: every `CubeBond` hypothesis (clause 1, both hypotheses of clause 2, and `CurlReads` at `shiftBack x ν` and at `x` in clause 3) widened to the touching form; bounds, quantifier order, `∃ g A` placement unchanged |
| `ClassCoupledTouch`, `ClassCoupledCorner` | `ClassCoupled` = `CoversOm0p ∧ PerCubeRegular2` = `(CoversOm0c ∧ CoversPlaqOm0c) ∧ PerCubeRegular2`, `ZR6A.lean:124,33` | yes; the single shared factor `c` is kept in all three conjuncts |
| `CoercG8AtTouch/Corner` | `CoercG8At`, `ZT5A.lean:89` | yes: `TorusOK → ∀ S, Admissible → ∀ Lam, LambdaOK2 → ∀ U, class → InstIneq`, same `η = (ell^k)⁻¹` |
| `P428Core8AtTouch/Corner`, `P428Genuine8Touch/Corner`, `P428Target8Touch/Corner` | `P428Core8At` `ZT5A.lean:170`, `SidePow6` `:200`, `P428Genuine8` `:229`, `P428Target8` `:291` | yes: identical quantifier order (`ell ≥ 2`, `a > 0`, then `m₀`, `R₀`, then `a₀`, `γ₀` before `k ≥ 1, Lu, α₀`), factor `12` and smallness `(12:ℝ) * M * α₀ ≤ a₀` kept, inner `(by omega)` for `0 < ell` kept |
| conclusion | `InstIneq`, `ZT5A.lean:56` | unchanged, still the frozen `plaqIn` operators — and the draft says so |

## The mathematics, re-checked by hand

1. **The non-trivial step is `touchCover_cubeBond`, and it is sound.** A `siteBox z s` is a
   product of per-coordinate arcs. If all four boundary edges of a unit plaquette are
   `TouchBond` of the box, the corner set in the box is a vertex cover of the 4-cycle
   A–B–D–C–A; `opposite_of_touch` (a correct `Classical.em` case split) gives an opposite
   pair `{A,D}` or `{B,C}`. The fill lemmas then need **no arc arithmetic**: corner B agrees
   with corner A in every coordinate except `d1`, where it agrees with corner D (since
   `D = shift B d2` and `d1 ≠ d2`, `shift_ne`), and likewise for C and for the antidiagonal
   case. Coordinate arcs are trivially closed under substituting an equal coordinate. The
   argument is valid as written.
2. **`CoversPlaqTouch.toFrozen` direction is correct.** A frozen antecedent plaquette
   (`CubeBond` on four bonds) is a touching antecedent plaquette; the witness's
   `IsClassCube` gives `sites = siteBox z (c * bigSide M ell j)` via `DescribedAt`
   (`ZStatementP428.lean:131`), so step 1 upgrades the consequent to `CubeBond`. The
   unique-index clause of `IsClassCube` is carried through unchanged (same `hc` reused);
   nothing dropped. The summary's "the antecedent grows and the consequent weakens, so this
   is not a rewrite" is an accurate description, and the geometry is exactly what repairs it.
3. **`PerCubeRegularTouch.toFrozen` needs no geometry** — `CubeBond → TouchBond` pointwise,
   including inside `CurlReads`. Correct.
4. **`ClassCoupledCorner → ClassCoupledTouch → ClassCoupled`** is correct:
   all-four-bonds-touch implies one corner in `Ω₀` (edge AB suffices,
   `plaqCorner_of_allTouch`), so the corner clause is the stronger antecedent. The corner
   clause is the CMP 102 p.277 "at least one corner" reading; the draft says so and does not
   claim the four-bonds-touch interpolation is printed.
5. **Headline transport**: `targetTouch_of_frozen` and `targetCorner_of_touch` unpack and
   repack the existential blocks without reordering anything; the class hypothesis is the
   only change. Checked line by line against `ZT5A.lean`.

## Specific refutation probes, all negative

- **Quantifier order**: none changed (table above; `P428Target8Touch` is `P428Target8` with
  `P428Genuine8` → `P428Genuine8Touch`, nothing else).
- **Dropped hypothesis**: none. `CoversOm0c`, `TorusOK`, `Admissible`, `LambdaOK2`,
  `SidePow6`, factor 12, smallness, `η = ell^-k` all kept; `Λ` untouched (`OnLambdaT`,
  `CRowIn`, `OnLambdaTildeIn` are the frozen touching readings already).
- **Both-endpoint/touching swap**: the draft keeps `CubeBond` exactly where the frozen
  statement has it (nowhere in the conclusion; `InstIneq` still sums over `plaqIn`), and
  widens to `TouchBond` only inside the class hypotheses. No swap found.
- **Even-ell fact reused as odd-ell**: no parity-dependent step exists in this file (the
  vertex-cover/fill argument is parity-free). Not applicable.
- **Diagnostic called a theorem**: no. The file header and the note both say uncompiled
  draft, not a Lake root, not a project theorem; the draft JSON's `compiled: false` is
  accurate. The summary sentence "Touching regularity implies the frozen bounds" describes
  the *drafted* `PerCubeRegularTouch.toFrozen`, labelled as such.
- **`sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/`extern`**: none in
  the file (the only hits are the docstring listing the forbidden words).
- **Edits outside `AHP/`**: none. `git status --porcelain` shows only untracked `.bb/` and
  `AHP/`. Frozen modules, `lean/lakefile.toml`, `lean/Check*.lean`, `expected/`, `paper/`,
  `notes/statement_sheet.tex` untouched. The file lives outside `lean/` and is not a Lake
  root; imports (`ZT5A`, `ZR2Ops2`, `ZR8Class`) are existing modules.

## Findings (non-refuting)

- **F-1 (integration hazard, not a defect of this draft): cross-draft name clash.** The S-1
  draft (`AHP/attempts/s1-touching/Touching.lean`, namespace `AdalyFormal.AHP.S1Touching`)
  already defines `TouchBond`, `plaqCorner`, `CoversPlaqCorner`, `CurlReadsTouch`,
  `PerCubeRegularTouch`, `touchCover_cubeBond` with the *same* content, and — confusingly —
  defines `ClassCoupledTouch` to mean what S-2 calls `ClassCoupledCorner`
  (`CoversOm0c ∧ CoversPlaqCorner ∧ PerCubeRegularTouch`). S-2's `ClassCoupledTouch`
  (with `CoversPlaqTouch`, the four-bonds-touch interpolation) is a *different*, weaker
  class. The namespaces keep both files consistent separately, but if either is ever moved
  into `lean/`, the shared names must be reconciled and the two `ClassCoupledTouch` meanings
  disambiguated. S-2 does not cite S-1's identical lemmas.
- **F-2 (unverifiable here): elaboration risk in the geometry section.** Several steps are
  plausible but not guaranteed without a compiler: `rw [TouchBond, hAB] at h` (relies on
  `rw` unfolding a plain `def` via equation lemmas and matching pair projections up to
  reducible defeq), `simp [periodicPlaquetteBoundaryEdges, ...]` closing Finset membership
  for a `by classical` def (depends on the let-inlined equation lemma), `rcases hc.1.2.1
  with ⟨z, _, rfl⟩` substituting `sites` under dependent hypotheses, and anonymous
  constructors/`obtain` through the def chain `P428Genuine8 → P428Core8 → P428Core8At → ∃`.
  On paper each is standard; a failed elaboration would leave the chain unproved, and this
  machine cannot check it (no oleans, 16 GB limit). This is inherent to the "uncompiled
  draft" status the draft itself declares, not a hidden claim.
- **F-3 (disclosed, worth restating sharply): vacuity.** The draft claims no non-vacuity.
  If the S-1 draft's (equally uncompiled) obstruction argument is right, `CoversPlaqCorner`
  fails on every tower with a proper nonempty `Ω₀`, so `P428Target8Corner`'s content may be
  concentrated on `Ω₀ = ∅` and the full torus. `P428Target8Touch` is unaffected by that
  particular obstruction but is a strict weakening of the frozen headline (stronger class
  hypothesis, same conclusion), so its independent content is limited to being a stepping
  stone to the corner form. The middle class `CoversPlaqTouch` is an interpolation with no
  print motivation; the same "all four bonds touch Ω₀" clause is refuted *as an operator
  reading* in the tree (`not_P428Target8LiteralBoth`), and the draft correctly keeps it only
  as a coverage hypothesis and keeps the operators at `plaqIn`.

## Bottom line

I could not refute the draft. Its statements match the frozen definitions it names, the
implication directions are the right ones for S-2 (frozen class ⊇ touching class, hence
`P428Target8 → P428Target8Touch → P428Target8Corner`), the one genuinely geometric lemma is
sound, and the disclosures (uncompiled, no converse, no non-vacuity, `InstIneq` unchanged)
are accurate. It remains an uncompiled draft under `AHP/attempts/s2-class-implication/`:
before any use, it needs a compile on a machine with the mathlib oleans, a forbidden-token
scan of the compiled file, and resolution of F-1 against the S-1 draft.

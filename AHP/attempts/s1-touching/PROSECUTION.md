# PROSECUTION — s1-touching (second model family)

Target: `AHP/attempts/s1-touching/Touching.lean`, `AHP/notes/s1-touching.md`, draft outcome `reduced`, `compiled: false`.

Method: reading only. No `lean`/`lake`/`elan` was run (machine limit; no oleans on this box). Every claim below is a reading of the draft against the frozen sources in `lean/src/`. Frozen files read for this prosecution: `ZStatementP428.lean` (BlockClosed, Admissible, siteBox, DescribedAt, IsClassCube, CubeBond, CRowIn, TorusOK), `ZR2A.lean` (PerCubeRegular2, CurlReads, ddA, CoversOm0c, OnLambdaT), `ZR6A.lean` (CoversPlaqOm0c, CoversOm0p, ClassCoupled), `ZT5A.lean` (InstIneq, CoercG8At, P428Core8At, SidePow6, P428Genuine8, P428Target8), `ZR2Ops2.lean` (plaqIn, Delta), `ZLocOps.lean` (deltaKLocCLM), `ZLocJ.lean` (JSU2Loc), `ZXR2Ops3.lean` (bondsOm0), `ZR8Class.lean` (shift_ne, shift_comm, shift_sameBlock, classBond_bothIn), `ZR8Geo.lean` (admissible_mono), `AdalyFormal/Target/ClayStatement.lean` (periodicLatticeShift, periodicPlaquetteBoundaryEdges, PeriodicLatticeSite), `AdalyFormal/Balaban/AdmissibleSubspace.lean` (Bond).

## Process checks (pass)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/`extern` in code; the only token hits are the disclaimer sentence in the module docstring.
- `git status --porcelain` shows only untracked `.bb/` and `AHP/`; no tracked file modified. Frozen modules, `paper/`, `notes/statement_sheet.tex` (rows 5 and 7), `lean/lakefile.toml`, `expected/` untouched. No Lake root added.
- `compiled: false` is stated in the JSON and in the note. The note does not call anything a project theorem. This is honored.

## Statement-level audit (passes; the construction is faithful)

Checked against the frozen types, item by item:

- **Quantifier order.** `P428Target8Touching` reproduces `P428Target8` (ZT5A:291) exactly: `∀ ell ≥ 2, ∀ a > 0, ∃ m₀ ≥ 1, ∀ m ≥ m₀, ∃ R₀, ∀ R ≥ R₀, P428Genuine8· ell (ell^m) R _ a`. `P428Core8AtTouch` reproduces `P428Core8At` (ZT5A:170): `∃ a₀ > 0, ∃ γ₀ > 0, ∀ k ≥ 1, ∀ Lu α₀, 0 < α₀ → (c)Mα₀ ≤ a₀ → CoercG8At·`. `CoercG8AtTouch` reproduces `CoercG8At` (ZT5A:89) hypothesis-for-hypothesis (TorusOK → Admissible → LambdaOK2 → U), changing only `ClassCoupled` → `ClassCoupledTouch` and adding the set-equality conjunct to the conclusion. No hypothesis dropped; the class hypothesis is strengthened, so the implication direction is the safe one.
- **Touching vs both-endpoint directions.** `CubeBond` (ZStatementP428:145) is both-endpoints; `TouchBond` is one-endpoint; `CubeBond.toTouch` is the correct direction. In `PerCubeRegularTouch.toFrozen` the frozen (weaker-hypothesis) statement is proved from the touch (stronger-hypothesis) one by mapping `CubeBond → TouchBond` on the hypotheses — correct: the touch class is a *subclass* of the frozen class, which is exactly what S-2 predicted and what the implication needs. The curl clause mirrors `CurlReads` (ZR2A:40) bond-for-bond, in order.
- **plaqIn.** ZR2Ops2:74: `p ∈ plaqIn S ↔ ∀ e ∈ boundary p, e.1 ∈ S ∧ shift e.1 e.2 ∈ S`, i.e. `CubeBond S` on all four boundary bonds — the draft's reading ("all four corners") is exact, and the frozen `CoversPlaqOm0c` (ZR6A:27) hypothesis is literally that predicate, so `corner_of_cubeBond_om hp` is well-typed.
- **Λ already touching.** Verified: `OnLambdaT` (ZR2A:119) and `CRowIn` (ZStatementP428:211) and `bondsOm0` (ZXR2Ops3:26) are all at-least-one-endpoint. The draft leaves Λ alone, correctly.
- **Class cubes lie in Ω₀.** The crux lemma `class_sites_subset_om0` navigates `hc.1.2.2.1` = `DescribedAt`'s clause `sites ⊆ towerBj S j ∪ towerBj S (j+1)` (ZStatementP428:131-140) and finishes with `admissible_mono` (ZR8Geo:175: `∀ j, S.Om j ⊆ S.Om 0`, from the decreasing-tower conjunct). This is exactly the frozen `classBond_bothIn` (ZR8Class:31) argument; the navigation is right.
- **Admissible conjunct positions.** `block_div` uses `hS.2.2.1` (divisibility), `block_closed_om0` uses `hS.2.2.2.1` (BlockClosed at `bigSide M ell 0 = M`). Correct against the six-conjunct def (ZStatementP428:73).
- **Helper lemmas exist with the used signatures**: `StatementLaneR8.shift_ne` (ZR8Class:52), `shift_comm` (ZR8Class:87, gives `cornerD_comm` with `μ := d2, ν := d1`), `shift_sameBlock` (ZR8Class:59), `admissible_mono` (ZR8Geo). `deltaKLocCLM U P` (ZLocOps:181) and `JSU2Loc η P U` (ZLocJ:71) match the two `_congr` lemmas. `siteBox` (ZStatementP428:122) is verbatim the coordinatewise condition, so `mem_siteBox_iff` by `rfl` is believable, and the product-set fill argument is valid.
- **No even-ell/odd-ell reuse.** Parity is never used; `M ≥ 2` comes from `M = ell^m, m ≥ 1, ell ≥ 2` (`M_ge_two_of_pow`), available in the headline since `m₀ ≥ 1`.
- **No diagnostic called a theorem.** The outcome is `reduced`, not `proved`; the note is explicit that nothing was compiled.

## Mathematics of the skeleton (sound, with one consequence the summary understates)

The reduction argument is correct on paper:

1. `CoversPlaqCorner` + `Admissible` + `M ≥ 2` force `Ω₀ ∈ {∅, univ}` (`saturated_of_coversCorner`). The exit-edge construction (`exists_exit`, forward-distance induction) and the bad-plaquette construction (`bad_plaq_of_exit`) are geometrically correct: from `z ∈ Ω₀`, `shift z μ ∉ Ω₀`, the block-closure move to `w = faceSite z ν` (ν ⊥ μ, `(w ν).val` a multiple of `M`, needs `M ≥ 2` via `not_dvd_block_start`) yields a unit plaquette with corner `w ∈ Ω₀` and the opposite bond `(shift w μ, ν)` with both endpoints out of `Ω₀`. Since class cubes sit inside `Ω₀`, no class cube touches that bond (`not_touch_class_of_noEnd`). Correct.
2. The vertex-cover argument (`opposite_of_touch`: a vertex cover of a 4-cycle contains an opposite pair) is true, and the fill step (`siteBox_fill_of_diagonal`/`_antidiagonal`) is valid because `siteBox` membership is coordinatewise. Hence `CoversPlaqCorner → CoversPlaqOm0c` and `ClassCoupledTouch → ClassCoupled`. Correct directions.
3. On `∅` and `univ`, `plaqCorner = plaqIn` (all four sub-lemmas are right), so on the touching class the frozen `plaqIn`-operators are the one-corner operators.

**The consequence the summary understates (F5):** saturation means the touching hypothesis class contains *no tower with a proper nonempty `Ω₀`*. The reason is already in the frozen `DescribedAt`: class cubes are confined to `B^j ∪ B^{j+1} ⊆ Ω₀`, so a cube can never touch a bond that leaves `Ω₀`, and a proper block-closed `Ω₀` always has a one-corner plaquette whose opposite bond is fully outside. So the consistent touching reading's coverage clause is *unsatisfiable on every domain the paper's coverage results are about* (the witness towers all have proper nonempty `Ω₀`). The implication `P428Target8 → P428Target8Touching` is therefore vacuous outside the trivial domains. The note discloses the saturation fact itself ("forces `Ω₀` empty or the whole torus") but the JSON summary's "the frozen `InstIneq` is the touching inequality" should carry the qualifier: *on a class that excludes every proper-domain tower*. For S-1 this is the real content: the touching convention does not merely agree with the frozen one — it collapses the class. This must be said plainly before the item is presented as settled-by-reduction.

## Defects in the proof script (the file as written would not elaborate)

The draft is honestly labelled uncompiled, so these are not misrepresentations — but they mean the file is a proof *sketch*, and the JSON sentence "The draft shows `P428Target8 → P428Target8Touching`" overstates: the draft *writes a proof-shaped text* that, by inspection, fails at least twice.

- **F1 (script error, `opposite_of_touch`).** After `by_contra h; push_neg at h`, `h.1` has type `cornerA p ∈ sites → cornerD p ∉ sites` (mathlib `push_neg` rewrites `¬(P ∧ Q)` with `not_and`, giving an implication, not a disjunction). The next line `rcases h.1 with hA | hD` destructures that implication as if it were an `Or`. This is a type error. (Fix: `rcases not_and_or.mp h.1 with hA | hD`, or `by_cases`.) The lemma's *statement* is true; the script is wrong.
- **F2 (script error, `touchCover_cubeBond`).** The goal is `CubeBond (siteBox z s) e`, with `CubeBond` a plain `def`. `rw [h1]` with `h1 : e.1 = cornerA p` finds no `e.1` in the folded goal (rewrite does not unfold the def), and even unfolded, after rewriting `e.1` the pattern of `h2 : periodicLatticeShift e.1 e.2 = cornerB p` is stale. Both `rw [h1, h2]` steps fail as written. (Fix: `refine ⟨?_, ?_⟩` after `show`, or `h1 ▸ hall.1`-style term proofs.)
- **F3 (high risk, `bad_plaq_of_exit`).** `refine not_plaqIn_of_endpoint_out ?_ (Or.inl hwμ_out)` leaves the bond direction as a metavariable (`?e := (wμ, ?m)`); the remaining membership goal `(wμ, ?m) ∈ periodicPlaquetteBoundaryEdges …` is then handed to `simp`, which cannot instantiate goal metavariables. Likely stuck. (Fix: pass `(e := (wμ, ν))` explicitly.)
- **F4 (unverified elaboration risks).** (a) `simp [periodicPlaquetteBoundaryEdges]` membership goals: the frozen def's body is a `by classical; exact {…}` block (ClayStatement:1295), so unfolding may leave decidable-instance cruft that the membership simp set does not close. (b) `fwdDist_shift`'s `simpa using hstep` needs `Fin.val (x μ + 1)` normalized to `((x μ).val + 1) % (L μ + 1)`; the draft never invokes `Fin.val_add_one`, so the `simpa` is speculative. (c) `Set.ne_univ_iff_exists_not_mem` is used but occurs nowhere in the tree; its name is unverified against the pinned mathlib.

None of F1–F4 indicates a *mathematical* gap; all are repairable. But until repaired and compiled, the correct status is: **the reduction is a paper argument, not a proof script that works**.

## Other findings

- **F6 (prose presented as checked fact).** The summary's "The slab counterexamples `not_P428Target8Literal` and `not_P428Target8LiteralBoth` stay outside this class" is supported only by prose. The file contains the general lemma (`not_CoversPlaqCorner_of_proper`) but never instantiates it on the D1 lane's `SlabNv` tower — that would need the slab's `Admissible`, its proper-nonempty `Ω₀` (`SlabNv_bdpt`), and `U_θ`'s regularity under `TouchBond`, none of which is imported or cited in the file. The prose argument itself is sound (class-cube sites ⊆ Ω₀, so a `TouchBond` of a class cube meets Ω₀, where `U_θ = 1`; the slab's `Ω₀` is a proper nonempty block union, so `CoversPlaqCorner` fails), and the note correctly says the D1 refutations "are not refutations of operators and class together". But it is an argument, not a Lean fact.
- **F7 (admitted gap, correctly disclosed).** The operator-agreement step is delivered as a set equality plus two congr lemmas (`deltaKLocCLM_congr`, `JSU2Loc_congr`) that the headline proof never uses. There is no `InstIneqTouch` and no rewriting of `gparams`/`genForm`/`G1invS`. Propositionally this is one `subst` away (any construction from equal sets is equal, `Classical.choose` included), so this is a presentational gap, not a mathematical one; the note says so. Both congr lemmas are dead code as the file stands.
- **F8 (minor).** `hwν_in` in `bad_plaq_of_exit` is unused (the plaquette only needs the corner `w`, not `shift w ν`). Dead code, linter noise only.

## What was NOT found

No wrong quantifier order, no dropped hypothesis, no both-endpoint/touching swap in the wrong direction, no even-ell lemma reused at odd ell, no diagnostic presented as a theorem, no `sorry`-class token, no edit outside `AHP/`, no Lake root added, no prose copied from the external repository.

## Verdict

- The *construction* (definitions, quantifier order, class direction) is faithful to the frozen statement and to CMP 102 p.277 as transcribed in S-1.
- The *reduction argument* is mathematically sound, and its key enabler (class cubes ⊆ Ω₀) is already a frozen theorem (`classBond_bothIn`).
- The *Lean file* is not a working proof script: F1 and F2 are definite elaboration failures, F3 likely, F4 unverified. "reduced" must be read as "reduced on paper"; no compile on this box could succeed as written, and nothing here may be cited as a Lean artifact.
- The summary must add the F5 qualifier: the touching coverage clause collapses the class to `Ω₀ ∈ {∅, univ}`; the frozen theorem decides the touching reading only on trivial domains, and S-1's interesting case (proper `Ω₀`) is not "the two forms agree" but "the touching class is empty of such towers".
- `compiled: false` stays; statement-sheet rows 5 and 7 stay open; the item should stay under `AHP/attempts/` until F1–F4 are fixed and a build gate (elsewhere, within memory limits) has run.

# Prosecution — two-domain

Prosecutor: second model family (this thread). Target: the uncompiled lane package
`extras/two_domain/` (`LOG.md`, `READING.md`, `SCOPE.md`, `STATEMENT.md`, `src/TD1.lean`–`TD7.lean`),
its review card [REVIEW.md](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/two-domain/REVIEW.md)
and note [two-domain.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/two-domain.md), in the
light of [SOL_VERDICT.md](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/two-domain/SOL_VERDICT.md)
(reject, grade 2). Item: `paper/OPEN_ITEMS.md` R-a2, still-open part (2), the literal two-domain
transfer. Mandate: refute if possible — wrong quantifier order, dropped hypothesis, class or
bond-convention swap, threshold sleight, vacuous witness, diagnostic called a theorem, forbidden
tokens, edits outside `AHP/`. One constraint from Sol's verdict: the card's projection-defect
objection was refuted by Sol; it is not repeated here.

**Verdict: NOT REFUTED.** No mathematical defect found in the lane's sources at the level a
reading can reach. The types of the six headlines match the frozen definitions they name, the
reductions are direction-correct, and the one genuinely geometric argument (`cover_cut` with the
cut/glue at level 0) is sound as written. This is not an adoption: the package is outside the
build, its gate record is absent, and nothing was compiled. `compiled` stays `false`; no
declaration of `extras/two_domain/` is a theorem of the project tree.

No `lean`, `lake`, `elan`, or `REPRODUCE.sh` was run (16 GB, no swap, no oleans). No file was
copied into `lean/src`. `git status --porcelain` shows only untracked `.bb/` and `AHP/`.

## Sol's rejected objection: independently confirmed false, not repeated

Sol's verdict refutes the card's "Reading defect" (the claim that `regBody_glue` at `TD1.lean:162`
projects `CurlReads` onto the wrong site). I re-derived the count from the frozen definitions and
confirm Sol, exactly:

- `ZR2A.lean:35`: `CurlReads W x ν μ` is `C1 ∧ (C2 ∧ (C3 ∧ C4))` with
  `C2 = CubeBond W (x, μ)`; `ZStatementP428.lean:145`: `CubeBond sites b := b.1 ∈ sites ∧ …`.
- In `regBody_glue`, `hcr ν0 hν0 : CurlReads W (shiftBack x ν0) ν0 μ ∧ CurlReads W x ν0 μ`.
  Hence `(hcr ν0 hν0).2.2.1 = C2 = CubeBond W (x, μ)` and `.2.2.1.1 = (x ∈ W)`, with
  `W = D ∪ E`. The `rcases … with hx | hx` then splits `x ∈ D` or `x ∈ E`, which is exactly what
  `hs2 μ x hx hcr` / `ht2 μ x hx hcr` consume.
- The card's proposed replacement `(hcr ν0 hν0).2.1.1` would select `C1.1`, membership of
  `shift x ν0`, not of `x`. It must not be applied.

So: the card's "Reading defect" section and its must-not-write item 9, and the note's "union
proof text does not match `CurlReads`" section, are withdrawn by Sol and are not part of this
prosecution. The dependency chain `regBody_glue → cover_cut → famTwoDom_union →
twodom_union_instance_inequality` stands as *uncompiled but not shown defective*. Symmetrically,
nothing here certifies that chain: the refutation of a false objection is not an elaboration.

## What was checked against the frozen tree

| Lane object | Frozen definition read | Match |
|---|---|---|
| `TwoDomFamP` (TD2) | `FamTorusLayerP`, `THL6.lean:73` | yes: identical binders and existential block, with exactly one insertion — `∀ Sc, (∀ j ≥ 1, Sc.Om j = S.Om j) → S.Om 0 ⊆ Sc.Om 0 →` between `AdmSplitNB … S` and `∀ Lam …`; class hypothesis `ClassCoupledP Cl … Sc`, conclusion `InstAtWD … S` |
| `TwoDomCapP`, `classCoupledCap_of_two` (TD3) | `ClassCoupledCap`, `L0C2.lean:136`; `FamTorusCapLayer`, `THL6.lean` | yes; third clause is `RegBodyH … (sites ∩ S.Om 0)`, fed by `regBody_mono_sites` (`UNI_Joint.lean:32`) along `sites ∩ S.Om 0 ⊆ sites ∩ Sc.Om 0` |
| `descAt0_of_described`, `descAlt_congr` (TD3) | `DescribedAt0`, `P4L4.lean:141`; `DescribedAtAlt`, `L0C2.lean:25` | yes: `DescribedAt0` reads only `Om 1`, `Om 2` (the p. 408 `B⁰ := T₁ \ Ω₁`), so only `hag` is needed; the witness need not lie in `S.Om 0` |
| `cover_cut`, `famTwoDom_union` (TD2) | `UnionAt`, `IsClassUnion`, `RegBodyH`, `isClassUnion_of_unionAt`, `UNI_Base.lean:40,47,72,216`; `unionClass`, `IsClassCubeP`, `ClassCoupledP`, `UNI_Tor.lean:31,34,37,42` | yes; `unionClass` ignores the factor, so `hc3 f C j hCF hCl` typechecks by defeq; `isClassUnion_of_unionAt h1 …` takes the nesting field of `AdmSplitNB` (`THL6.lean:36`) as written |
| `famTwoDom_box` (TD3) | cap route via `famTorusLayerCap`, `THL6.lean` | yes (see F-4: the constants are the cap's, not `famTorusLayer_box`'s) |
| `mixedTwoDom`, `totalTwoDom` (TD4) | `ClassCoupledΦ`, `classCoupledΦ_single`, `MX_Orig.lean:22,31`; `perCubeRegular2_iff`, `UNI_Base.lean:97` | yes |
| `Target8TwoDom`, `target8TwoDom` (TD4) | `AdmNoBase`, `THL2.lean:23`; `SidePow6`, `ZT5A.lean:200`; `target8Layer`, `THL6.lean` | yes: `∃ m₀, ∀ m ≥ m₀, ∃ R₀, ∀ R ≥ R₀` order kept; factor 12; `InstIneq` only; the `AdmNoBase → AdmSplitNB` repack `⟨h1,h2,h3,h4, h5 0 (zero_le _), fun j _ hj => h5 j hj⟩` matches the six-field definition field by field |
| `regBody_glue`, `glue_side`, `far_block_exists`, `pdist_block_le` (TD1) | `CurlReads`, `ddA`, `curlA`, `ZR2A.lean:29,35,40`; `CubeBond`, `ZStatementP428.lean:145`; `pcd`, `pdist`, `siteBox`; `L0C.bd`, `L0C.exists_step`, `L0C1.lean:84,101`; `ZR8Geo` `pdist_*` | yes; `exists_step`'s conclusion shape `∃ y', y' ∈ siteBox z s ∧ pdist y y' ≤ 1 ∧ bd z x₀ y' < bd z x₀ y` is what TD1 consumes |
| `plain_cut_fails`, `slabT`, `slabT_two` (TD6) | slab tower of lane `nonvac_c` (`slab3`, `nvcP0`…, `om0_mem`, `bj0/1/2`), `NVC*` via `THL3` | yes; index-0 statement only |
| `regBody_of_M1_union`, `classCoupledU_of_M1`, `famF` (TD6) | `M1Regular`, `M1B.lean:69`; `bstrat`, `le_bstrat_of_mem`, `M1A.lean:34,144`; `unionAt_of_described` (namespace `UNI.Total`), `UNI_Red.lean:48` | yes; mirrors the compiled `perCube_of_M1` (`M1B.lean:91`) with `IsClassCube` replaced by `UnionAt` |
| `two_nonvac_core`, `twodom_nonvac_regime`, `twodom_instance_inequality`, `twodom_union_instance_inequality` (TD5) | `ufield_M1Regular`, `M1B.lean:304`; `spike`, `Ufield`, `plaq_spike`, `Ug_ne_one`, `spike_not_pure_gauge`, `ZR2B4/ZR2B5` (namespace `StatementLane2`); `InstIneq`, `InstAtWD`, `ZT5A.lean:56,64` | yes; the witness block mirrors the compiled `THL3.lean:150–173` / `NVC7.lean` block nearly verbatim, including `Ug_ne_one hηc0 hηc1` (two-argument form, `ZR2B5.lean:17`) and `hmain.2 Bt h8 h9` with `OnLambdaTildeIn` before `OnLambdaT`, the frozen argument order |
| `TD7` gates module | — | prints and `run_cmd` scripts only; no new mathematics; see F-2 |

## The mathematics, re-checked by hand

1. **Cap (`classCoupledCap_of_two`, `famTwoDom_cap`).** `DescribedAtAlt` never mentions `Om 0`,
   so `descAlt_congr` rewrites it between `Sc` and `S` using only level-≥1 agreement. Coverage of
   the smaller domain follows from `S.Om 0 ⊆ Sc.Om 0`; the regularity clause is monotone in the
   intersected domain. Then `famTorusLayerCap` on `S`. This is monotonicity, not a cut — sound.
2. **Box (`famTwoDom_box`).** Does not call the union glue. It filters `F` to `IsClassCube`
   members, turns level-0 `DescribedAt … Sc … 0` into `DescribedAt0 … S` (needs only `hag`;
   the p. 408 descriptor does not see `Om 0`), builds `ClassCoupledCap` on `S` with regularity
   restricted from the whole box to `sites ∩ S.Om 0`, and calls `famTorusLayerCap`. A level-0
   box of `Sc` may leave `S.Om 0`; the cap class is exactly the class that tolerates that.
   Sound — and note what it does *not* do (F-3): it never proves that the cut of a box meets
   `B⁰(S)`.
3. **Union (`cover_cut`, `famTwoDom_union`).** At level `j ≥ 1` the cube is kept (tower strata
   agree). At level 0 the cube is cut to `S.Om 0`; if the cut meets `B⁰(S)` it is the `S`-class
   union as it stands. If it misses `B⁰(S)` it lies in `S.Om 1`; then `far_block_exists`
   (discrete IVT along unit steps inside `siteBox z (L 0 + L 1 + L 2 + 3)`, using the strict
   collar with `3M+1 ≤ R₀·M`, i.e. `R₀ ≥ 4`) produces `v ∈ S.Om 0` at distance `≥ 3M+1` from
   `S.Om 1`; `pdist_block_le` (`pdist u v + 3 ≤ 3M` inside one aligned `M`-block) lifts that to
   separation `≥ 4` between the cut and `blockOf M v`; coverage of `Sc` supplies a level-0 cube
   containing `v`, hence the whole block (`BlockClosed`), whose regularity restricts to the
   block; `regBody_glue` (single gauge, single `A`, piecewise by bond start; stencils of radius
   ≤ 3 cannot connect the pieces) glues at factor `max f fu`, which still occurs in `F` by
   `max_choice`. The new family `F'` inherits factors `≥ 10` and smallness from `F`. The
   threshold is `max R₁ 4` with `4 ≤ R₀` used only for `cover_cut`. Every step checked against
   the frozen shapes; the arithmetic closes with margin to spare. Sound as written.
4. **Mixed, total, frozen.** `mixedTwoDom` rebuilds a box family from `ClassCoupledΦ` and calls
   `famTwoDom_box`; `totalTwoDom` is the singleton via `classCoupledΦ_single`;
   `target8TwoDom` takes `SidePow6` from `target8Layer` and applies `totalTwoDom` at `c = 12`,
   `Rs = fun _ => R`, returning only the `InstIneq` conjunct. No quantifier moved, nothing
   dropped.
5. **Witness (`twodom_instance_inequality`, `twodom_union_instance_inequality`).** Depth
   `k = 2`, one radial slab of radius `R` inside one of radius `Rb > R`, the curved spike `U` of
   the compiled `THL3`/`NVC7` witness, `ClassCoupled` on `Sc` from the M1 regime
   (`ufield_M1Regular`, `perCube_of_M1`), `LambdaOK2` at the *larger* radius `Rb` (headline
   requires only `RL ≥ R₀`), one positive-energy `Bt`. The union instance adds
   `ClassCoupledP unionClass (famF c) Sc` via `classCoupledU_of_M1` (every factor-`c` union
   regular in the M1 regime) and contains the cut-missing cube of `plain_cut_fails`. Existential
   throughout; no overreach found in the statements.

## Specific refutation probes, all negative

- **Quantifier order**: `TwoDomFamP`/`TwoDomCapP`/`MixedTwoDom`/`TotalTwoDom` are the frozen
  family/cap/mixed/total binder sequences with the `Sc` block inserted in one place
  (after `S`, before `Lam`); `Target8TwoDom` keeps the `target8Layer` order. No reordering found.
- **Dropped hypothesis**: none. Factors `≥ 10`, smallness `f·ℓ^m·α₀ ≤ a₀`, `TorusOK`,
  `AdmSplitNB` with its six clauses, `LambdaOK2` at `RL ≥ R₀`, coverage and regularity of the
  class — all present in every form. `AdmSplitNB` is *not* required of `Sc` (that is the point
  of the statement, and it is disclosed, not hidden).
- **Class swap**: box, cap, union, mixed, total each use the frozen predicate they name
  (`boxClass`, `ClassCoupledCap`, `unionClass`, `ClassCoupledΦ`, `ClassCoupled`); the
  union-class cap is correctly *not* asserted anywhere.
- **Bond convention**: `CubeBond` (both endpoints) is used uniformly, including inside the
  coverage clauses after cutting (`famTwoDom_union`'s plaquette clause rebuilds both endpoints
  of every boundary edge inside `Q` from `hp` and `hcb`). No touching/one-endpoint slip.
- **Threshold sleight**: `max R₁ 4` appears only in `famTwoDom_union`, is passed to
  `famTorusLayer_union` as `R₁ ≤ R₀` via `le_trans (le_max_left _ _)`, and `4 ≤ R₀` via
  `le_max_right`. Box/cap/mixed/total/target8 do not take the max. No hidden weakening.
- **Vacuity**: the witness inhabits the fixed-factor and union-family hypotheses with
  `Om 0 (S) ⊊ Om 0 (Sc)`, a curved non-pure-gauge `U`, and a positive-energy competitor. The
  two-domain statements are not vacuously true on the empty shell (the shell is inhabited).
- **Diagnostic called a theorem**: no. But see F-1: the lane's *own prose* (SCOPE/STATEMENT)
  does call the package "PROVED (Lean)"/"kernel-checked"/"CLOSED"; that self-report is not a
  measurement of this package and must not travel.
- **Forbidden tokens**: my own scan of `TD1`–`TD7` found no `sorry`, `admit`, `native_decide`,
  `unsafe`, `implemented_by`, or `extern`. `axiom` occurs only in `#print axioms` commands and a
  TD7 comment — commands and comments, not declarations, and unexecuted here.
- **Isolation**: `lean/lakefile.toml` and `REPRODUCE.sh` do not mention the lane; `lean/src`
  contains no `TD*` module; imports (`THL6`, `THL3`, `TD1`–`TD6`, `Lean`) are existing modules.
  The transitive closure reaches every frozen name used (`THL6 → THL5 → L0C2 → L0C1 → P4L4`,
  `UNI_Joint`; `UNI_Red`; `MX_*` via `MX_F`; `NVC7` via `THL3`), checked by reading import
  lines only.

## Findings (non-refuting)

- **F-1 (evidence gap, controlling): the gates are not in the package.** `gate_record/` is
  absent (HANDOFF.md: the last gate record was not committed). `LOG.md`'s two byte-identical
  builds, `leanchecker` exits, 1,029-root census, 16 failing mutants, and per-headline axiom
  prints are unattributed-historical reports here. `SCOPE.md`'s "PROVED (Lean)"/"CLOSED" and
  `STATEMENT.md`'s "kernel-checked" are the lane's summary of those reports. None of it is a
  measurement of the seven files present.
- **F-2 (TD7 comment/script mismatch, confirmed in source).** TD7's header says the census
  covers `THL1`–`THL8`; the script selects module names starting with `TD` and excludes `TD7`.
  The comment is wrong; the reported `roots=1029` counts TD-lane constants, not the thin-layer
  modules.
- **F-3 (the box meeting clause is asserted, not formalized).** `READING.md` §3.1 and
  `SCOPE.md` state that for boxes the cut `C ∩ S.Om 0` meets `B⁰(S)` whenever nonempty, citing
  `path_exists_T`. No declaration in `TD1`–`TD7` proves any form of this; the token
  `path_exists` occurs only in `READING.md` prose. The box headline is engineered to avoid the
  clause (`DescribedAt0` does not see `Om 0`; regularity is intersected). The assertion may well
  be true (`path_exists_T` exists in the frozen `THL5` replay), but it is not a result of this
  package and must not be cited as one.
- **F-4 ("same constants" is inaccurate for four of six forms, sharpened).** `STATEMENT.md`'s
  answer paragraph says the two-domain forms hold "with the same constants as the corresponding
  one-domain statements". As a reading of the *proofs*: the union form reuses
  `famTorusLayer_union`'s package with `R₁ ↦ max R₁ 4` (same `m₁, a₀, γ₀`); the cap form reuses
  `famTorusLayerCap`'s package. But `famTwoDom_box` is built from `famTorusLayerCap`, **not**
  from `famTorusLayer_box`, and `mixedTwoDom`, `totalTwoDom`, `target8TwoDom` inherit the cap
  package through it. So "the box/mixed/total/target8 two-domain forms have the constants of
  `famTorusLayer_box`/`mixedLayer`/`totalLayer`/`target8Layer`" is not established by these
  proofs — they carry the cap package's constants. Since all constants are existential, the
  statements are unaffected; the prose claim about proofs is what must not travel.
- **F-5 (unverifiable here: elaboration risk).** Several steps are standard-looking but not
  guaranteed without a compiler: `unionClass`'s factor-ignoring defeq in `hc3` applications;
  `(fun _ => R) j` beta-redexes under `le_rfl`; `0 < M` passed where `1 ≤ M` is expected
  (`ufield_M1Regular`; defeq for `ℕ`); `obtain rfl : ju = 0` by contradiction;
  `if_pos`/`if_neg` through `Set` membership decidability under `classical` in `regBody_glue`;
  `simp [periodicPlaquetteBoundaryEdges]` for the first boundary edge; `rw [← hSc1]` under a
  negated membership. Mitigations: TD5's witness block is nearly verbatim the compiled
  `THL3`/`NVC7` block, and the `unfold spike; split_ifs; rw [abs_of_pos …]` pattern has
  compiled precedent in `ZR2B11.lean`. Risk remains until a build.
- **F-6 (disclosed limits, restated because they bound every reuse).** The witness is two
  nested *radial* slabs at `k = 2` with the M1-regime family `famF c`; no non-radial layer, no
  general family, no every-`k`. No form holds below its existential `R₁`; the union form's `4`
  is a proof artifact, not shown sharp and not a binder. `target8TwoDom` drops `WellDefG`. The
  class hypothesis constrains `U` on the shell `Sc.Om 0 \ S.Om 0`; the quadratic form is
  `gparams` of `S`. No union-class cap is stated.
- **F-7 (witness `LambdaOK2` radius).** The witness's `LambdaOK2` is at the *larger* radius
  `Rb`, while `S`'s level-0 radius is `R`; this satisfies the headline (`RL ≥ R₀`) but a paper
  sentence must not describe the witness's Λ-collar as being at the operator radius.

## What must not be written in the paper

1. That any `extras/two_domain` declaration is a theorem of this repository, or that its axioms
   are `propext`, `Classical.choice`, `Quot.sound`. No build or axiom print was run in this
   package; the `#print axioms` lines are unexecuted commands; `gate_record/` is absent.
2. That prosecution or Sol adopted the lane. Sol *rejected the review card* (grade 2) for a
   false projection objection; this prosecution could not refute the sources and certifies
   nothing. `OPEN_ITEMS.md` R-a2 and the `thin-two-domain` paragraph of `paper.tex` still say
   the literal two-domain transfer is not proved. Those sentences stand.
3. That pp. 394/396 force the two-domain reading. One letter `Ω₀` is used on both pages; the
   one-domain reading remains the paper's adopted reading.
4. That `target8TwoDom` is `P428Target8` or `Target8Layer`. It has no `WellDefG` conjunct,
   uses `AdmNoBase` at one radius, and inherits `SidePow6` from `target8Layer`.
5. "Same constants" as equality of numbers — and, sharpened (F-4): that the box/mixed/total/
   target8 forms carry the constants of `famTorusLayer_box`/`mixedLayer`/`totalLayer`/
   `target8Layer`. The proofs give them `famTorusLayerCap`'s package. Only the union form
   reuses its one-domain counterpart's package, with `R₁` raised to `max R₁ 4`.
6. Anything below `R₁`, an explicit `R₁`, the union form for `R₀ < 4`, or sharpness of `4`.
   No negative theorem and no mutant log is in this package.
7. That the plain cut of a disconnected union is a class union of the operator domain, or that
   `plain_cut_fails` is a theorem, or that the cut fails at every index. It is an uncompiled,
   index-0, two-slab example.
8. That this lane proves the box meeting clause (F-3): the claim appears only in prose; no
   `TD*` declaration states it. Likewise that `famTwoDom_box` is the cap theorem: hypothesis
   boxes on `Sc`, route cap on `S`, and a box of `Sc` may leave `S.Om 0`.
9. ~~That `famTwoDom_union` mismatches `CurlReads`.~~ Struck by Sol's verdict; independently
   confirmed false here (the projection selects `x ∈ D ∪ E`). Equally forbidden: that the union
   text is *verified* — it is uncompiled.
10. That `Sc` may differ from `S` at some level `j ≥ 1`, or that `S.Om 0` need not sit inside
    `Sc.Om 0`. The headlines assume the opposite.
11. That the headlines assume a radial `≤ RM` class domain. Only the witness builds one radial
    slab inside another.
12. That the witness covers every configuration, every `k`, a non-radial layer, or a general
    union family. `famF` is the M1 regime; `k = 2`; radial slabs.
13. That a union-class cap (level-0 unions allowed to leave `Ω₀`) is proved. It is not stated.
14. That `CubeBond` matches CMP 96 (both endpoints here; at least one there), that the distance
    is non-periodic, that the dimension is not 3, the group not `SU(2)`, or `η ≠ ℓ⁻ᵏ`. All
    inherited and unchanged. The formal `a₀` is not the source's `a₁`.
15. That regularity is required only on the operator domain. The class hypothesis sees the
    shell; the form is `gparams` of `S`.
16. "No condition on the family remains." Factors `≥ 10` and the smallness bound remain.
17. `SCOPE.md`'s "CLOSED"/"PROVED (Lean)", `STATEMENT.md`'s "kernel-checked" and its draft
    paper sentence, and the `notes/statement_sheet.tex` row (line 185) that already names
    `target8TwoDom`, `famTwoDom_union`, `famTwoDom_box`, `famTwoDom_cap`. That row is a sheet
    entry, not a build claim; the paper does not copy a lane's self-report.
18. That `LOG.md`'s gates (two byte-identical builds, `leanchecker` exit 0, 1,029-root census,
    16 failing mutants, per-headline axiom prints) are measurements of this package. The
    artifacts are absent (F-1).
19. That `TD7`'s census covers `THL1`–`THL8` (its comment). The script counts `TD*`-prefixed
    modules excluding `TD7` (F-2).

## Bottom line

I could not refute the lane. Sol's rejection of the review card is correct and is respected: the
projection objection is dead and is not repeated. On the remaining substance, the six headline
types match the frozen definitions, the four reduction routes (cap monotonicity; box-via-cap;
union cut-and-glue; mixed/total/frozen by family surgery) are direction-correct and their key
steps check out against the frozen predicates line by line, and the witness is a faithful reuse
of the compiled `THL3`/`NVC7` non-vacuity block. What stands between this package and any paper
sentence is not a found mathematical error but the missing gates: no build, no axiom print, no
`gate_record/`, and the lane's own prose overclaiming its status (F-1, F-3, F-4). Before any
use: copy the modules into a Lake root on a machine with the mathlib oleans, build, run the
`#print axioms` and census of `TD7`, correct the `TD7` census comment, reconcile
`STATEMENT.md`'s constants sentence with F-4, and re-run both review gates. Until then,
`compiled` is `false`, nothing here is a theorem of the project tree, and the paper's
`thin-two-domain` sentence is unchanged.

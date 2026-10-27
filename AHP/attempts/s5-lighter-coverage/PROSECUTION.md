# Prosecution of s5-lighter-coverage

Verdict: **QUALIFIED — the headline mechanism is refuted on paper; the arithmetic skeleton is
verified; the negative answer to S-5 survives only in a weaker form.**

The draft ([LighterCoverage.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s5-lighter-coverage/LighterCoverage.lean),
[note](/home/sebastian/BalabanCoercivityLemma/AHP/notes/s5-lighter-coverage.md)) answers S-5
(`paper/OPEN_ITEMS.md` line 334: does the frozen proof work with regularity only on side-`M`
cubes containing a bond of the active set?) with: "Yes — the frozen proof needs a fine plaquette
the lighter side-`M` hypothesis does not cover." The coverage-gap claim, which is the stated
reason, does not follow from the frozen definitions and is false under the active-set reading the
harvested note itself proposes. What survives is the strictly weaker statement that the frozen
proof *term* cannot be replayed against the lighter hypothesis, because `plaq_small_class` needs a
factor-`c` class cube with its index, not a side-`M` gauge. No Lean was run; `compiled` stays
false; nothing here is a theorem of the project tree.

## 1. What was verified against the frozen tree (all by reading; no build)

* `rhoT` copy. `LighterCoverage.rhoT` is clause-for-clause `rhoT` of `lean/src/ZR8Read.lean`
  (`rhoT ell 0 = 0`, `rhoT ell (l+1) = rhoT ell l + 4 * (ell ^ l * ell)`). The draft's disclosure
  that this is a copy, not the declaration, and not definitionally equal, is accurate.
* Ball radius. `readRadius ell l = 4 * (ell ^ l * ell) + 2 * rhoT ell l` is exactly the radius in
  `read_region` (`lean/src/CJ4.lean`: `Ball e.1 (4 * (ell ^ l * ell) + 2 * rhoT ell l)`), and the
  same expression is the `hR` ball of `loop_small`/`regRow_of_plaq` (`lean/src/CJ3.lean`).
* The call chain. `classRows_read` (`CJ4`) does apply `plaq_small_class` at every `z` of that ball
  and every `ν μ` (the `intro z hz ν μ; have := plaq_small_class … (read_region … z hz) ν μ` step),
  and `plaq_small_class` (`CJ3`) obtains its cube from `hU.1.2 p hp`, i.e. `CoversPlaqOm0c` inside
  `ClassCoupled` (`lean/src/ZR6A.lean`: `ClassCoupled = CoversOm0p ∧ PerCubeRegular2`,
  `CoversOm0p = CoversOm0c ∧ CoversPlaqOm0c`), with the index gain `m - 1 ≤ i` from
  `cube_index_ge`. The bound `(4π+4) a / (ell²)^(m-1)` matches the note's "(ell²)^{m-1} in the
  denominator".
* Level choice. `ReadRow` (`lean/src/CJ2.lean:223`) is
  `l < j ∧ e.1 ∈ CoarseLattice L (ell ^ (l+1)) ∧ pdist b.1 e.1 ≤ rhoT ell j - rhoT ell (l+1)`.
  With `M = ell^m`, `j = m+1`, `l = m`: `l < j` holds, the `pdist` bound is `rhoT j - rhoT j = 0`,
  and `b ∈ bondsLam (m+1)` makes `b.1` `ell^(m+1)`-aligned (`bondsLam_facts`, `CJ4`), so
  `e = (b.1, μ)` is a legitimate `ReadRow`. The headline permits it: `P428Target8`
  (`ZStatementP428.lean`) fixes `M = ell^m` with `m ≥ m₀` and then `P428Core8At` (`ZT5A.lean:171`)
  quantifies `∀ k, 1 ≤ k`, so `k = m+1` is allowed. Factor `c = 12 ≥ 2` (`core6_is_c12`, ZT5A).
* The three arithmetic lemmas, hand-checked (uncompiled, as disclosed):
  `4 * ell^(l+1) ≤ readRadius ell l` is the first summand; `ell^m < readRadius ell m` for
  `ell ≥ 2` since `readRadius ≥ 4 ell^(m+1) = 4 ell·ell^m ≥ 8 ell^m > ell^m`;
  `readRadius 2 1 = 32` (`rhoT 2 1 = 8`, `16 + 16`) against block side `2`;
  `no_side_containing_bond_and_far`: `a ≤ 0` forces `a = 0`, then `s < 0 + s` is false;
  `class_side_gt_block`: `M < c·M ≤ c·(M·ell^i)` for `c ≥ 2`, `M ≥ 1`, `ell ≥ 1`.
  `bigSide M ell i = M * ell^i` and `siteBox z (f * bigSide M ell i)` in `DescribedAt` match the
  docstring citations (`ZStatementP428.lean:51,122,131`).
* `bothIn_classBond` / `plaq_of_bothIn` (`ZR8Class.lean:136,169`) and `plaq_common_gauge`
  (`ZR6A.lean`) are as the note describes; the note is right that the `plaq_of_bothIn` plaquette
  (inside the bond's own `M`-block) is not the gap.

## 2. The refutation: the headline ranges over the wrong quantifier

The lighter clause (HARVEST.md line 23: "Let `Q ⊂ Ω_k` be a cube of side `M` that contains a bond
of `B⁺`. For **every such** `Q` there is a gauge …") gauges *every* side-`M` cube containing *any*
active bond. The draft's exhibited fact is only:

> no side-`M` block contains both the unit bond `b` and the offset-`M` site.

That is the right arithmetic lemma for the wrong statement. Non-coverage of the plaquette requires
ranging over **all** active bonds of **all** levels, and the draft does not. Two concrete
counter-scenarios:

**Scenario A — the active set is the `Ω_0` bonds (`bondsOm0`, ZXR2Ops3.lean:27).** This is the
reading the harvested note itself flags as the relevant one ("It could replace ours if our active
bond set (Omega_0 bonds under the touching mask) is what is covered", HARVEST.md:23). The offset-`M`
plaquette's four corners lie in `Ball z 2 ⊆ Ω_m ⊆ Ω_0` (`read_region`, `om_anti`), so its own four
bonds are active, and for `M ≥ 2` some side-`M` cube contains the whole unit plaquette. Coverage
**holds**. The draft's own note concedes exactly this in "What the lighter clause is not" — yet the
headline and the JSON summary state the gap unconditionally. The headline is false under this
reading.

**Scenario B — the active set is `⋃_j bondsLam j`, and `b` sits in the second disjunct.**
`bondsLam (m+1)` (ZXR2Ops3.lean:43) allows `b.1 ∉ Lam (m+1)` with only
`coarseShift b.1 (ell^(m+1)) b.2 ∈ Lam (m+1)`. Then nothing in `Admissible` forces `b.1 ∈ Ω_(m+1)`
(the collar bounds distances from `Ω_(m+2)`, not from `Ω_(m+1)`), and `z = b.1 + M·e_1` can lie in
`Ω_m \ Ω_(m+1)`: the collar of the shifted endpoint gives
`pdist y0 z ≤ ell^(m+1) + M ≤ R·M·ell^m`, so `z ∈ Ω_m`. Since `z` is `ell^m`-aligned
(`b.1` is `ell^(m+1)`-aligned, `M = ell^m`), `geomOf`'s
`Lam m = {x | ell^m ∣ x, x ∈ Ω_m, x ∉ Ω_(m+1)}` (ZXR2Wire1.lean:24) gives `z ∈ Lam m`. If the
`ell^m`-block of `z` in direction `ν` also avoids `Ω_(m+1)`, the plaquette's own bond `(z, ν)` is in
`bondsLam m` — **active** — and `siteBox z M` contains the plaquette. Coverage holds again.

The gap does hold under extra geometry (e.g. `b.1 ∈ Lam (m+1)` with `Ω_(m+1)` a union of
`M·ell^(m+1)` grid blocks: then `z ∈ Ω_(m+1)`, every `ell^m`-aligned site within coordinate
distance `< M` of `z` lies in `Ω_(m+1)`, every `Lam m` site is at coordinate distance `≥ M` — and
distance exactly `M` already kills side-`M` containment, since sites `0..M` are `M+1` points; level
`≥ m+1` active sites differ from `z` by `≥ M` in coordinate 1; level `< m` bonds exclude endpoints
in `Ω_(j'+1) ∋ z`). But the draft proves none of this. Its "Yes" is not a consequence of the
frozen definitions; it is one disjunct of an unanalysed case split.

## 3. What survives

The defensible content, all supported by the frozen sources:

1. The frozen proof term consumes fine plaquettes at every site of the read ball, whose radius
   `4·ell^(m+1) + 2·rhoT ell m` strictly exceeds `M = ell^m` at level `l = m`; the ladder plaquettes
   of `loop_small` step with stride `ell^l = M`, so offset-`M` sites are genuinely used, not just
   quantified over.
2. No side-`M` cube contains both the row bond `b` and such a site (verified arithmetic).
3. A factor-`c ≥ 2` class cube has side `c·M·ell^i > M`; the headline factor is `12`. A side-`M`
   gauged cube is never a class cube.
4. Therefore the frozen proof **term** cannot be replayed under the lighter hypothesis:
   `plaq_small_class` needs `CoversPlaqOm0c` at factor `c` and the cube index `i ≥ m-1` for the
   `(ell²)^-(m-1)` gain that the estimate chain spends (`classRows_read`'s
   `q0 = (4π+4)a/(ell²)^(j-2)`, `pow_ratio_le` with `l` up to `j-1`; `ClassSmall` only covers
   `ell^6`, so without the index gain the chain breaks at `l > 3`). A side-`M` gauge supplies
   neither the cube type nor the index. This is the note's own "What the lighter clause is not"
   remark — and unlike the coverage gap, it is reading-independent: it holds whether or not the
   plaquettes are gauged.

So the correct S-5 record is: *the frozen proof as written does not go through under the lighter
hypothesis (class-cube type and index lost); whether the lighter hypothesis covers the needed
plaquettes is undecided (it does under the `bondsOm0` reading); the coercivity inequality under the
lighter hypothesis is untouched.* The draft's stronger claim — an exhibited plaquette the lighter
hypothesis does not cover — should be withdrawn or re-graded to the conditional statement of
section 2's last paragraph.

## 4. Minor holes (do not change the verdict)

* Non-vacuity: no `b ∈ bondsLam (m+1)` is exhibited on any admissible tower; on the known witness
  towers such bonds exist, but the draft does not cite one.
* Wrap-around: `pdist b.1 z = M` needs `M < L_1 + 1`; fine on `scaleUp ell (m+1) Lu`
  (`scaleUp_big` gives `2·ell^(m+1) < L_1 + 1`), but unwritten.
* `pdist x y = 0 ⇒ x = y` is explicitly disclaimed — honest, but it is the step that puts the ball
  at `b.1`.
* Uncompiled: `Nat.mul_le_mul_right`'s argument order has drifted across Mathlib revisions; the
  file imports current Mathlib unpinned by the project. Risk noted, not checked.
* The `bondsLam` records are unit-edge records `(y, μ)` denoting coarse bonds `[y, y+ell^j e_μ]`;
  under a coarse-segment reading of "bond", a level-`m` active bond already spans `ell^m = M`, so no
  side-`M` cube contains it — the draft never fixes which reading of "bond" the lighter clause uses.

## 5. Compliance

* Writes: only `AHP/attempts/s5-lighter-coverage/` and `AHP/notes/s5-lighter-coverage.md` (draft);
  this file adds `AHP/attempts/s5-lighter-coverage/PROSECUTION.md`. `git status --porcelain` shows
  only `AHP/` and `.bb/` untracked; no frozen file, lakefile, `expected/`, `paper/`, or
  `notes/statement_sheet.tex` was touched.
* Forbidden-token scan of the draft: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/
  `implemented_by`/`extern` in code (the only grep hits are the word "external" in prose).
* No `lean`/`lake`/`elan` run, no mathlib download, no `rm`, no commit. `compiled` is false.
  Nothing here or in the draft is a theorem of the project tree.

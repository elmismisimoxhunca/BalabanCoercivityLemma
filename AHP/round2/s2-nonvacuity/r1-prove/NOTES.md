# S-2 non-vacuity — round 1, positive direction

## Result

**Closed the exact pinned `GoalPos1` (four-bond class).**

Main declaration:
`AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved`,
[Attempt.lean:293](Attempt.lean#L293).
Its type is exactly `AdalyFormal.AHP.Round2.S2Nonvacuity.GoalPos1`, with no
additional hypotheses. The corner positive and negative goals are not proved
in this attempt.

Final compilation: **exit 0**, no errors or warnings.
[Compiler log](Attempt.lean.log), [exit record](Attempt.lean.exit).

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All **40** dependency records are subsets of that permitted set: the 14
pinned definitions, two copied sanity implications, six new theorems, and
18 directly reused frozen witness definitions/helpers. Every local theorem
has its own print; the main print also covers transitive dependencies.

## Construction and reduction

The useful existing proof was the frozen slab construction in
`lean/src/D1Final.lean:139–168`, together with the cap/flat-field proof pattern
in `AHP/fidelity/s1-touching/lean/ShellComparison.lean:116–169`.
No AHP file is imported, and no shell definition replaces the pinned class.

1. **New geometry reduction** — `four_touch_cubeBond_of_transverse`
   (`Attempt.lean:185`). In an ordered plaquette, its second direction is
   nonzero. On a domain invariant under nonzero-direction shifts, its two
   parallel edges have equivalent endpoint membership. Four-edge touching
   therefore places all four vertices inside. Unfolding the actual frozen
   boundary finset gives `CubeBond` for every boundary edge. This argument
   also handles periodic wrap and degenerate extents; no coordinate-size
   approximation or parity assumption is used.
2. **Apply to the actual slab** — `slabNv_transverse` (`:221`) uses frozen
   `SlabNv`, `om0_mem` (`lean/src/NV1.lean:28`) and `shift_ne`
   (`lean/src/ZR8Class.lean:52`). Slab membership depends only on coordinate
   zero. `slabNv_coversFour` (`:230`) then transfers the already proved
   frozen plaquette coverage to exactly `CoversPlaqFour`, retaining the same
   `IsClassCube` witness. General towers are not assumed to have this property.
3. **Flat touching regularity** — `perCubeRegularTouch_one` (`:240`) uses
   gauge one and matrix field zero, checking all three strict bounds and
   the actual `ddA` expression. Positivity of the bounds is proved, not
   replaced by non-strict inequalities or zero smallness.
4. **Complete instance** — `properFourAt_two` (`:268`) proves
   `ProperFourAt 2 m R a₀` for **every** `m ≥ 1`, `R ≥ 18`, and `a₀ > 0`.
   It sets:
   - `M = 2^m`, `k = 2`, `Lu = nvLu M R`;
   - `S = SlabNv 2 M R`, `Lam = LamN M R`, `U = fun _ => 1`;
   - `α₀ = a₀ / (12 * M)`, positive with exact cap `12 * M * α₀ = a₀`;
   - `Bt = BseedNv 2 hM`.
   Actual torus compatibility, admissibility, Lambda compatibility,
   nonempty/proper base domain and factor-12 site/plaquette coverage come
   from the frozen slab theorems. `BseedNv_props`
   (`lean/src/NV6.lean:203`) supplies both exact test-space predicates,
   positive `bondEnergy`, and nonzeroness. No test field or coverage premise
   is left for a caller to provide.
5. **Cofinality** — `goalPos1_proved` (`:293`) chooses `ell = 2`,
   `m = max 1 mLower`, then `R = max RLower 18`, before receiving the cap.
   Thus this is the pinned threshold-order family, not an isolated small
   witness or a radius chosen after seeing the cap.

## Verification and provenance

Direct imports: `ZT5A`, `D1Final`, `ZR8Class`, all frozen `lean/src` modules.
The eight touching definitions, `ProperFourAt`, `ProperCornerAt`, and all
four goal definitions were copied from the pin **character-for-character**.
The pinned two sanity implications were retained unchanged as well.

Reproducible source/log audit:

```sh
python3 AHP/round2/s2-nonvacuity/r1-prove/audit.py > AHP/round2/s2-nonvacuity/r1-prove/AUDIT.json
```

[AUDIT.json](AUDIT.json) records exact text matches for all 14 definitions,
source and pin hashes, import restrictions, clean forbidden-token scan,
main type, exit 0, print completeness, and each dependency set.

Source SHA-256:
`2e2d384afeab5a5fa1a0249c7e3960eef91078888b071463bf0228538cc07f8a`.
Pin SHA-256 (unchanged):
`826f93c754d1c78a13e8ee7a832fc3041b36cd9cbe4628cde3a7475d752909f9`.

Each Lean invocation was serial, using exactly:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean.log 2>&1
echo $? > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean.exit
```

Three compilations were run. The first had one elaboration error: an extra
argument in the application of `not_lt_zero`; it is preserved in
`compile-1.log`/`compile-1.exit` and is **not acceptance evidence**. Removing
that extra argument gave exit 0. The final run also printed the imported
frozen helpers and the exact main type, and again exited 0. No numerical
simulation, build, update, reproduction run, commit, push, or removal was
performed. All writes stayed in this `r1-prove/` directory; pre-existing
shared-checkout changes were left untouched.

## Stopping boundary / remaining questions

There is **no obstacle to the pinned positive four-bond goal**: it is proved.
Work stopped after the successful final compilation and source/log audit.
Independent verification remains the next workflow stage.

This closes the item's four-bond proper-domain non-vacuity branch as pinned;
it does not identify that class with Balaban's printed class. In particular,
this proof says nothing positive about `ClassCoupledCorner`, does not prove
corner saturation, does not give changed-operator coercivity, does not settle
S-1 or S-3, and does not supply non-flat richness. It uses the explicitly
permitted `ell = 2` case, not the separate odd-`ell > 11` source convention.
The explicit radius bound 18 is a sufficient bound for this witness family,
not a necessary or sharp threshold for general towers.

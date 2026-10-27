# Sol review — sg-guarded

## Verdict

**ADOPT WITH DISCLOSURES — grade 2, after the prose corrections made in this review.** Adopt the corrected residual note, not a resolution of the guarded headline and not a certified Lean artifact. The originally submitted note is not acceptable unchanged.

`compiled: false`. `frozenFilesEdited: false`.

Read `HANDOFF.md`, `paper/OPEN_ITEMS.md`, the complete `PencilPin.lean` draft, the note, and the prosecution. Checked the central claims against the actual frozen definitions and proof bodies, not their headers alone. Grade 2 means this source-level comparison; it does not mean a rebuild, a printed-page fidelity audit, or completion of every review owed to the historical residual lane.

## Source checks

| Claim | Frozen source inspected | Finding |
|---|---|---|
| Ginv-only guarded headline | `lean/src/D2Cons.lean`, definitions `InstIneqSG`, `CoercG8AtSG`, `P428Target8SG` | The guard is `IsUnit Ginv`; the conclusion is the inequality, not an unconditional unit assertion. Thresholds are eventual in both m and R. |
| Exact residual reduction | `lean/src/DrEquiv.lean:35–118`, `GShape`, `CPen`, `GuardPencilT`, `residualT_iff_pencilT`, `P428Target8SG_iff_pencilT` | Matches the draft's main reduction. `CPen` uses the correction of localised data. `GShape_imp` enlarges thresholds and shrinks smallness, so this is not an equivalence preserving the same chosen constants. |
| Pencil identity | `lean/src/DrRed1.lean:33–69` | Requires admissibility, positive ell, the collar, literal Ginv a unit, and localised `WellDefAt`. It does not assume literal G1inv a unit. Added the geometric qualifications explicitly to the note. |
| Full guard is different | `lean/src/GdGap.lean`, `WellDefAt`, `InstIneqSG2`, `P428Target8SG2`; `lean/src/SolR345Audit.lean:68` | `WellDefAt` includes literal G1inv being a unit. `full_guard_literal` concludes SG2, not SG. Do not read it as the missing transfer. |
| Exterior-only pin | `lean/src/D1Path.lean:25–78`; `lean/src/DrPath1.lean:29–70`; `lean/src/DrPath2.lean:54–96`; `lean/src/DrPath3.lean:31–93`; `lean/src/ZT6B.lean:32–61` | Agreement off bonds with neither endpoint in Omega0 preserves localised data and transports an existing class hypothesis. Literal Ginv varies by the displayed all-plaquette shift; the pencil identity along the path is conditional on localised well-definedness and literal Ginv being a unit. Exterior freedom does not construct a class start or a separating path. |
| Refutation certificate | `lean/src/DrFamily2.lean:36–99`; `lean/src/DrBracket2.lean:20–37`; `lean/src/D1IVT.lean:86` | Cofinal scale/smallness quantifiers plus the path sign and unit hypotheses suffice for refutation. They are not supplied by this draft. No converse from arbitrary headline failure to that path certificate is established here. |
| Margin | `lean/src/DrMargin.lean:33–62` | A positive coercivity constant above the correction norm suffices; a pencil failure under that coercivity hypothesis forces c at most the correction norm. This says nothing about an invertible but noncoercive carrier. |
| Known configurations | `lean/src/GdR5b.lean:81–156`; `lean/src/GdR6a.lean:40–118`; `lean/src/GdR6b.lean:40–110` | Near-zero non-vacuity is on the stated depth-two slab and has an existential radius. The pi result compares literal and localised Ginv forms, without proving units at pi. A zero correction cannot separate the roots; the base-flat hypothesis concerns base points, not all bonds touching Omega0. |

## Prosecution findings and corrections

**F1 upheld and fixed in `AHP/notes/sg-guarded.md`.** A single bad point at one scale does not refute an eventual headline. The corrected pin requires fixed ell and a, then every lower m threshold, some larger m, every lower R threshold, some larger R, every positive smallness threshold, and a bad configuration satisfying every remaining premise. In particular the R witness must be chosen before the universal smallness threshold. Merely saying “arbitrarily large scales” would not by itself specify that order.

**Additional qualification to F1:** the prosecution and an older `OPEN_ITEMS` sentence describe `SepPathFamily2` as the negation. Only its *cofinal quantifier prefix* matches the required obstruction shape. Its continuous exterior-path, interval-unit, and endpoint-sign requirements are additional sufficient conditions. The source gives `SepPathFamily2 → not GuardResidualT`, not an equivalence. The corrected note now makes this distinction. The frozen text and paper were not edited.

**F2 upheld and fixed.** `domination_fails_pi` provides one vector with negative literal Ginv form and nonnegative localised Ginv form. Their difference therefore has a negative direction. That declaration alone is not a statement about corrected G1inv operators. `G1inv_diff_eq` additionally requires both well-definedness hypotheses; they must not be silently assumed at pi. The note now states only the direct Ginv comparison and does not infer singularity from a negative direction.

**F3 upheld and fixed.** The bracket citation now separately identifies `D1IVT.lean:86` and `DrBracket2.lean:20`.

Also replaced “the class is free” by preservation of membership from an in-class start, and labelled the linear-algebra section as uncompiled records. No change to `PencilPin.lean` or `PROSECUTION.md`.

## Independent mathematical check of the draft

The scalar carrier is multiplication by 2-t and the pencil by 1-t. Hence the carrier is a unit at t=1 and fails only at t=2, whereas the corrected operator fails at t=1. Both are units for t<1. The sign assertions at t=0 and t=3 are correct. This disproves only a bare linear-algebra transfer. It supplies none of the lattice, class, scale, or test-field data.

For the margin argument, Cauchy–Schwarz and the operator bound give

\[
\langle x,(A-D)x\rangle \ge (c-\lVert D\rVert)\lVert x\rVert^2.
\]

If c exceeds the correction norm, this implies injectivity and, in finite dimension, bijectivity and an operator unit. The stated contrapositive is correct. The zero-correction observation is immediate. No mathematical error was found in these elementary arguments.

This is not a check of tactic acceptance or of pinned Mathlib APIs. The prosecution's elaboration concerns remain unverified. No compiler or reproduction command was run, no dependencies downloaded, and no compiled output was created. A later permitted rebuild and dependency check remain prerequisites to promoting the draft declarations to project results. Adoption here relies on the independently readable elementary arguments and existing frozen reduction, not on assuming that the draft elaborates.

## What remains open

`P428Target8SG selAll selAll` is neither proved nor refuted by this work. Missing is a source-specific eventual unit-transfer proof, or a cofinal family of genuine smallness-qualified counterexamples. An inhabited `SepPathFamily2` would suffice for the latter; this draft does not inhabit it. The full guard, the pi sign diagnostic, and a near-flat interval do not close the Ginv-only guard.

Do not describe this review as a complete fresh gate of the historical residual lane, a decision of the printed lemma, or a theorem of the project tree. Do not equate a single-torus counterexample with a negation of the headline.

## Permitted later paper sentence

The Ginv-guarded all-plaquette statement remains undecided: its frozen reduction is the eventual implication from invertibility of literal Ginv to invertibility of literal Ginv minus the localised correction; neither the scalar obstruction nor a bad point at a single scale refutes that headline.

## Files changed in this review

- `AHP/notes/sg-guarded.md`: corrected F1–F3, the sufficient-certificate distinction, and omitted qualifications.
- `AHP/attempts/sg-guarded/SOL_VERDICT.md`: this review.

The paper, frozen modules, build configuration, checks, and expected outputs were not edited. No deletion, commit, push, or outward action was performed.

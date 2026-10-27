# S-2 odd, attack round 1

## Result

**Both pinned goals hold.** Fresh compilation of `Attempt.lean` through the required serial wrapper completed with exit **0**, no warnings and no errors.

| Declaration in `AdalyFormal.AHP.Round7.S2Odd` | Line | Result |
|---|---:|---|
| `properFourAt_every_ell` | 413 | Every ell ≥ 2, m ≥ 1, R ≥ 18, and positive cap satisfies the unchanged `ProperFourAt` |
| `goal2_proved` | 443 | Exactly `Goal2`, no extra hypotheses |
| `goal1_proved` | 455 | Exactly the primary `Goal1`, no extra hypotheses |
| `odd_gt_eleven_cofinal` | 462 | Explicit restriction to odd ell > 11 |

The primary cofinal choices are `m = max 1 mLower` and `R = max RLower 18`. The radius is chosen **before** the cap. There is no parity restriction. The sufficient bound 18 is not asserted to be sharp or an analytic coercivity threshold.

## Provenance and pin integrity

The pin directory already supplied a complete candidate in `../pin/Proof.lean`. This attempt reuses that proof verbatim, adding only nine dependency-print commands for directly used frozen helpers. It does not claim a newly discovered proof independent of that candidate.

The entire **12,259-byte** `../pin/Statement.lean` occurs unchanged at byte offset **32** in `Attempt.lean`. The only preceding content is the required import header:

```lean
import D1Final
import ZR8Class

```

Lean requires these imports before the pin's commands. No goal, definition, proof or comment within the pin was altered. The original round-two pin is its unchanged first 10,509 bytes. Historical comments about open round-two goals are retained, not endorsed as current status.

The four round-two helpers are copied verbatim from `AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean`: `four_touch_cubeBond_of_transverse`, `slabNv_transverse`, `slabNv_coversFour`, and `perCubeRegularTouch_one`. There are no AHP imports. Direct imports are frozen `D1Final`, `ZR8Class`, and `ZT5A`.

## Witness audit

Set \(M=\ell^m\). The construction uses:

- depth \(k=2\), unit torus `nvLu M R`, and fine torus `scaleUp ell 2 (nvLu M R)`;
- tower `SlabNv ell M R` and unit-domain `LamN M R`;
- flat background \(U=1\), gauges \(g=1\), and matrix fields \(A=0\);
- \(\alpha_0=a_0/(12M)>0\), satisfying the cap with equality;
- the genuine free-bond field `BseedNv ell hM`.

The general-ell geometry is the family used in frozen `D1PGen.lean`. The proof uses geometry and test-field results, not that file's spectral or refutation theorem:

1. `slabGeo_inst`, `scaleUp_nv`, and `slab3_admissible` give actual admissibility. Divisibility is \(\ell\mid\ell^m\) for \(m\ge1\); evenness is never used.
2. `nv_widths` and `slab3_coversp` supply actual **factor-12** site and inside-plaquette coverage. These are proved, not assumed in the final theorem.
3. On this transverse-invariant slab, four touching edges imply that all four edges have both endpoints inside. `slabNv_coversFour` transfers the existing coverage to the required common-cube touching coverage. This is a property of this family, not a selector identity on every domain.
4. `SlabNv_bdpt` gives an inside point with an outside forward neighbor, proving both nonemptiness and properness.
5. `torusOK_nv` and `lambdaOK2_nv` give the exact torus and Lambda predicates.
6. `perCubeRegularTouch_one` satisfies all three strict regularity bounds with positive right sides. The smallness parameter is not zero.
7. `BseedNv_props` gives **both** `OnLambdaTildeIn` and `OnLambdaT`, nonzeroness and strictly positive `bondEnergy`.

The separate general-factor theorem `NonVacC.headline_regime_nonvacuousC` was inspected but is not used as a shortcut: it proves membership in the frozen class, not the touching class required here. The specialized round-two `properFourAt_two` is not invoked.

## Verification

Command run directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round7/s2-odd/r1/Attempt.lean
```

Evidence: `Attempt.lean.log`, `Attempt.lean.exit`, and `CHECKS.json` in this directory. No timeout or relaunch occurred.

All **46** dependency records are present and use only permitted axioms; every one of the **28** local declarations has a print. The main records are:

```text
'AdalyFormal.AHP.Round7.S2Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.AHP.Round7.S2Odd.goal2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The log's `#check` output also confirms the exact types `Goal1` and `Goal2` without additional premises. A read-only audit verified pin/helper byte identity, source-before-log/exit ordering, imports, print coverage, and a clean full-source forbidden-token scan.

- Attempt SHA256: `000f5c6e860d67172468f2fa762344fd17de9586943ecc9c3b9c4659723ee835`
- Log SHA256: `f671f4866cc7c562f5338fffb1e3b4c85c484e04077dd8ab4fa6023dc091bf74`
- Pin SHA256: `fcba7f81a4d1e8f358d2bae1c7627f017919795b2bf3de257c39b3d68afaca41`

This is a fresh builder replay using ready frozen oleans. The workflow's independent verifier has not yet run on this attempt; no whole-project rebuild is claimed.

## Scope and remaining questions

There is **no obstacle to either pinned goal**. This settles proper-domain non-vacuity of `ClassCoupledFour` at every blocking factor, including odd factors above eleven.

It does not identify this class with Balaban's printed class, prove non-flat richness or all-depth witnesses, alter the corner-class saturation result, settle odd sites-only coverage, compare boundary operators, prove any inverse exists, or settle the guarded all-plaquette headline. The witness remains flat and depth two, with the frozen finite periodic three-dimensional SU(2), block/collar/Lambda/test-field conventions, common factor 12, and added coverage. Natural radii are not restricted to powers of ell. No source-page image was independently reread; the supplied pin's source-reading qualifications remain.

Only `AHP/round7/s2-odd/r1/` was written in this turn. No protected file or earlier round was edited; no numerical job, direct Lake invocation, reproduction script, build, dependency update, commit, push or removal was run.

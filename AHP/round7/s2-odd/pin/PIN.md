# Round 7 / S-2: proper four-bond domains at every blocking factor

**Status:** both new goals are well-formed and proved in a builder-compiled file. Independent verification remains for the workflow's verifier. This is non-vacuity of the specified formal class, not identification with Balaban's printed class.

- Pin: [Statement.lean](Statement.lean), new namespace `AdalyFormal.AHP.Round7.S2Odd`.
- Proof: [Proof.lean](Proof.lean).
- Evidence: [Statement log](Statement.lean.log), [Statement exit](Statement.lean.exit), [Proof log](Proof.lean.log), [Proof exit](Proof.lean.exit), [CHECKS.json](CHECKS.json).

## Goals and exact quantifier order

| Goal | Pin line | Plain meaning |
|---|---:|---|
| `Goal1` | 249 | **For every** blocking factor \(\ell\ge2\), there are proper nonempty four-bond-class instances cofinally in \(m\), then cofinally in \(R\), admitting every positive cap and a nonzero admissible test field. |
| `Goal2` | 257 | The stronger construction works for **every** \(\ell\ge2\), **every** \(m\ge1\), **every** \(R\ge18\), and **every** positive cap. |

The primary goal has the order

\[
\forall\ell\ge2\;\forall m_{\rm lower}\;\exists m\ge\max(1,m_{\rm lower})\;
\forall R_{\rm lower}\;\exists R\ge R_{\rm lower}\;
\forall a_0>0,\quad\mathrm{ProperFourAt}(\ell,m,R,a_0).
\]

In particular, \(R\) is chosen **before** the cap. The proof takes
\(m=\max(1,m_{\rm lower})\) and \(R=\max(R_{\rm lower},18)\).
The bound 18 is a sufficient construction bound, not an asserted sharp bound or a value of the coercivity theorem's unknown threshold.

`ProperFourAt` is the **unchanged round-two definition**, not a relaxed or newly assumed witness predicate. It requires, jointly:

1. \(M=\ell^m\), a depth \(k\ge1\), and a unit-torus extent `Lu`;
2. `TorusOK ell M Lu`;
3. a fine-lattice tower `S : Tower (scaleUp ell k Lu)` satisfying `Admissible ell M R k S`;
4. `LambdaOK2 ell M R k S Lam`;
5. `(S.Om 0).Nonempty` and `S.Om 0 ≠ Set.univ`;
6. \(0<\alpha_0\) and \(12M\alpha_0\le a_0\);
7. `ClassCoupledFour ell M 12 k S α₀ ((ell : ℝ)^k)⁻¹ U`, including actual site coverage, actual common-cube four-touch-bond plaquette coverage, and all three touching-regularity bounds;
8. `Bt : Bond Lu → SuTwo` satisfying **both** `OnLambdaTildeIn Lam ell Bt` and `OnLambdaT Lam Bt`, with `Bt ≠ 0` and `0 < bondEnergy Bt`.

The two field predicates are the actual premises of frozen `InstIneq` (`lean/src/ZT5A.lean:56`). The field is the independent input \(\widetilde B\), not \(C\widetilde B\); no extra `Q1 Bt = 0` constraint is substituted. No inequality, inverse existence, or positivity of an operator is assumed or concluded. The mass parameter does not occur in this non-vacuity predicate.

## What is strengthened

Round two's `GoalPos1` began with **there exists** one \(\ell\ge2\). Its proof `goalPos1_proved` used `properFourAt_two`, fixing \(\ell=k=2\). The new `Goal1` instead begins with **for every** \(\ell\ge2\), while preserving the entire inner witness predicate and cofinal/cap ordering.

Thus it covers every odd \(\ell\ge3\), including the later odd \(L>11\) convention in OPEN_ITEMS S-4. It is not a renaming of the old existential statement. The compiled `goal1_implies_round2` gives the implication to the old target. `odd_gt_eleven_cofinal` exports the odd-\(L>11\) restriction explicitly. Its oddness hypothesis is unnecessary precisely because the main theorem covers both parities.

The old pin is preserved as the first **10,509 bytes** of `Statement.lean`, byte-for-byte, including its historical comments, old four goals, and logical incompatibility proofs. Those old comments describe the original pin stage; they are not current claims that all four old goals remain open. Only `Goal1` and `Goal2` in the round-seven namespace are this track's new targets. This track does not reopen the separate corner-class branch.

## Actual proof and witness

`Proof.lean` contains the complete round-seven pin unchanged, preceded only by two additional frozen imports. It copies the four needed round-two helper proofs verbatim:

- `four_touch_cubeBond_of_transverse`;
- `slabNv_transverse`;
- `slabNv_coversFour`;
- `perCubeRegularTouch_one`.

The new assembly `properFourAt_every_ell` generalizes `properFourAt_two`; it never invokes that specialized theorem. Its construction is:

| Object | Choice |
|---|---|
| Depth | \(k=2\), independently of \(\ell\) |
| Unit torus | `nvLu M R`: side \(M(6R+2)\) in each direction |
| Fine torus | `scaleUp ell 2 (nvLu M R)`: side \(M\ell^2(6R+2)\) |
| Tower | `SlabNv ell M R` |
| Lambda | `LamN M R`, the slab \(3RM\le y_0<3RM+M\) |
| Background | \(U=1\) everywhere |
| Class gauges/matrix fields | \(g=1\), \(A=0\) on every class cube |
| Smallness | \(\alpha_0=a_0/(12M)>0\), with \(12M\alpha_0=a_0\) |
| Test field | `BseedNv ell hM`, the genuine free-bond seed of `NV6` |

There is no parity assumption on \(\ell\) or \(M\). The divisibility requirement is supplied by \(\ell\mid\ell^m\) for \(m\ge1\).

Proof mechanism:

- `slabGeo_inst`, `nv_widths`, `scaleUp_nv`, `slab3_admissible`, and `slab3_coversp` provide the frozen geometry and **factor-12** coverage for general \(\ell\).
- The base slab is invariant in transverse directions. On this slab, if all four plaquette edges touch the domain, all their endpoints lie inside it. Frozen inside-plaquette coverage therefore supplies a class cube whose bonds also satisfy the touching condition. This is a proved property of this family, **not** a global equivalence of selectors on arbitrary domains.
- `SlabNv_bdpt` supplies an inside point whose forward neighbor is outside, proving both nonemptiness and properness.
- `torusOK_nv`, `lambdaOK2_nv`, and `BseedNv_props` supply compatibility and the genuine positive-energy nonzero test field.
- The copied flat-regularity proof satisfies each strict bound with positive right-hand side. The class parameter is never set to zero.

Useful frozen locations inspected: `D1PGen.lean:24–71` (the general-ell literal family), `D1Final.lean:75–111` (slab and boundary point), `NV7.lean:27` (factor-12 widths), `NV6.lean:56,185,203` (torus, Lambda, seed), and `NVC7.lean:219` (the separate general-factor non-vacuity lane). The NVC result is about the frozen class; it was not silently treated as touching-class membership. No spectral crossing or coercivity theorem is used by the new assembly.

### Settling declarations

All names below are in `AdalyFormal.AHP.Round7.S2Odd`.

| Declaration | Proof line | Type/result |
|---|---:|---|
| `properFourAt_every_ell` | 413 | General-ell pointwise witness for every \(m\ge1,R\ge18,a_0>0\) |
| `goal2_proved` | 443 | `Goal2` |
| `goal1_proved` | 455 | `Goal1` |
| `odd_gt_eleven_cofinal` | 462 | Explicit odd-\(\ell>11\) cofinal corollary |

Each of these prints exactly `[propext, Classical.choice, Quot.sound]`. In particular:

```text
'AdalyFormal.AHP.Round7.S2Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.AHP.Round7.S2Odd.goal2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Departures from Balaban's print and retained readings

These disclosures inherit the round-two pin and the supplied HANDOFF/OPEN_ITEMS readings, with the blocking-factor limitation updated. No source-page image was independently re-read here; in particular the CMP102 p.277 touching quotation and CMP109 p.251 odd-scale quotation remain supplied reading evidence.

1. **Different purpose.** Properness, nonemptiness, positive-energy tests and cofinal witness quantifiers are audit requirements, not the printed p.428 lower-bound theorem. Class inhabitation alone neither proves nor refutes that theorem.
2. **Dimension/group/lattice specialization.** Retain the finite periodic three-dimensional SU(2) setting, modular wrap, rectangular extent representation by side minus one, unit/fine `scaleUp` dictionary, and mesh \(\eta=\ell^{-k}\). `TorusOK` divisibility and strict-size conditions are formal compatibility conventions, not an unrestricted group/dimension theorem.
3. **Scale ranges and ordering.** Retain natural \(\ell\ge2\), \(M=\ell^m\), \(m\ge1\), \(k\ge1\). Unlike the old witness, the new result includes the later odd \(L>11\) convention, but also allows other scales. Radii are natural numbers, not restricted to powers of \(L\) as on p.408. The cofinal ordering and sufficient bound 18 belong to this construction; no identification of printed uniform constants or sharp thresholds is asserted.
4. **Tower/base geometry.** Retain periodic \(\ell^1\) distance, aligned half-open block tilings, empty padding above depth, strict collars, and the exact p.396 block-collar base law. This is reading A of the fine lattice in its own units, not reading B, the arbitrary p.394 thinner layer, or a two-domain construction. The witness has depth two, not arbitrary depth.
5. **Cube family/factor.** Retain frozen `IsClassCube`: aligned product boxes with side \(12M\ell^j\), two-stratum containment and unique index. Selecting a single common factor 12 and product boxes is a restriction of the print's per-cube \(O(1)\ge10\)/union-of-big-block language. Neither non-box unions, per-cube factors, the altered p.408 zero-level class, nor its third-enlargement clause is added.
6. **Touching regularity and stencils.** Use at-least-one-endpoint `TouchBond` rather than frozen both-endpoint `CubeBond` in every regularity bound and stencil guard, exactly as in the copied definitions. This implements the bond part of the supplied CMP102 convention, not the larger read-bond shell. Derivative bounds apply when all displayed stencil bonds touch the cube; the source boundary prescription is not uniquely identified. Gauge/matrix functions are global functions quantified separately for each cube, with constraints only on its selected bonds.
7. **Additional coverage; four-touch is not one-corner.** Site coverage and common-cube plaquette coverage are extra formal hypotheses, not consequences asserted from the printed regularity conditions. `CoversPlaqFour` requires all four edges to touch the domain, then all four to touch one frozen class cube. This differs from the print's at-least-one-corner selector. The copied corner class retains an even stronger antecedent and is a different class. No reversal of the earlier corner-saturation result follows.
8. **Norms, differential expression and cap.** Keep full-matrix Frobenius norm in class bounds, with the disclosed \(\sqrt2\) difference from the trace-normalized norm; the actual frozen `ddA` curl expression; strict inverse-mesh powers 1, 2 and 3; and explicit \(12M\alpha_0\le a_0\). Test energy uses the frozen `SuTwo` norm. This does not establish a new printed norm/normalization dictionary.
9. **Lambda and free variables.** Keep frozen `LambdaOK2`, its unit-lattice collar and block-sum condition, touching support, axial staircase, selected coarse rows and dropped-bond conventions. These are the existing support/constraint reading, not a fresh correspondence proof for pp.427–428. The nonzero test excludes empty-Lambda vacuity.
10. **No operator or inverse conclusion.** The pin does not alter or compare Delta, J, C, eta/tau-star, or any covariance. The surrounding frozen instance uses inside-plaquette localization and its existing inverse conventions; they are not repaired by a class-existence theorem. This result says nothing new about the guarded all-plaquette question, the odd sites-only coverage cell, a corner-operator counterexample, or existence of every printed inverse.
11. **Flatness and family limits.** The witness uses \(U=1\), a depth-two slab and a single free-bond test. No non-flat richness theorem, all-depth witness family, all-tower classification or uniform analytic lower bound is claimed. The general-ell curved witnesses in NV/NVC concern the frozen class and are not claimed here for the touching class.

## Compilation and audit

Both invocations ran directly through the required wrapper:

```sh
AHP/round3/lean1.sh AHP/round7/s2-odd/pin/Statement.lean
AHP/round3/lean1.sh AHP/round7/s2-odd/pin/Proof.lean
```

Both have exit **0**, zero warnings and zero errors. `Statement.lean` has 18 dependency records and `Proof.lean` 37; every list is a subset of the permitted three axioms. The full-source forbidden-token scan is clean. Direct imports are frozen `ZT5A` for the pin and frozen `D1Final`, `ZR8Class`, `ZT5A` for the proof. There are no AHP imports.

Byte checks confirm the original pin prefix, the complete new pin inside the proof, and the four verbatim copied helper proofs. Source/log hashes and source-before-log/exit ordering are recorded in `CHECKS.json`.

- `Statement.lean` SHA256: `fcba7f81a4d1e8f358d2bae1c7627f017919795b2bf3de257c39b3d68afaca41`.
- `Proof.lean` SHA256: `8bf18d38c55dae67f9dc17284c78b7ead3d435876249562ab531d81c6b4867e6`.

These are builder compilations using ready frozen oleans, not an independent replay or a whole-project rebuild. No numerical experiment, direct Lake invocation, build, dependency update, reproduction script, commit, push or removal was run. Writes are confined to `AHP/round7/s2-odd/pin/`; protected files and earlier rounds were not edited.

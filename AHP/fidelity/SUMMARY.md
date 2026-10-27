# Statement-fidelity Stage A — plain-language summary

## Status and evidence

This is a consolidation of the files already on disk, not a fresh numerical or formal verification. Numbers below are recorded experimental results, not proofs. This pass ran no numerical scripts, Lean, Lake or `REPRODUCE.sh` and made no changes to protected sources or the statement sheet.

Six target directories have decisions. `guarded` has a design and numerical output but **no DECISION.md**, so it is not ready for Stage B. The supplied workflow array also has a null `sheet-variants` entry; its existing on-disk decision supplies the accepted plan instead. The [Stage-B work list](STAGE_B.md) follows decisions only and waits for the current reproduction gate to pass.

The main outcome is narrower than closing all six audit items: coverage row 6 is stale; several exact comparisons are ready to try compiling; one proposed normalisation counterexample was rejected; the full touching and guarded questions remain open. The reading-only target is a completed qualified record, not a blanket statement that the printed and frozen forms agree.

## 1. Touching bonds and corner plaquettes — S-1

**What was tested.** On tori of side 4, 6 and 8, the design compared plaquettes wholly inside a domain with plaquettes having at least one corner in it. It also proposed a stronger “shell” regularity class that controls every bond read by those corner plaquettes, including some bonds with neither endpoint in the domain. Tests included slabs, selector geometry, diagonal backgrounds and noncommuting small-link backgrounds.

**What the numbers showed.** The old exterior-link example gave raw Delta Rayleigh value -4 for corner and all-plaquette selection, but 0 for inside selection. The shell sees links that endpoint-only regularity misses. On the tested proper slabs and cube, no change of the site set reproduces corner selection as inside selection. A diagonal example within phase cap pi/2 had minimum about -2.94; the tighter constrained regime did not produce such a negative example. Noncommuting small-link examples had negative raw Delta values too, but did not separate the readings after the incomplete gauge comparison.

One reported eigenmode decomposition needed repair: the raw minimum about -0.223 belongs with curl contribution about +0.019 and Delta-prime contribution about -0.242. The +0.024/-0.281 pair belongs to a different configuration with raw minimum about -0.257. The decision corrected the attribution using the saved attack measurements.

**Decision and open work.** Advance seven structural comparisons and a flat proper-domain hypothesis-family witness. The shell is stronger than the printed endpoint rule and keeps frozen coverage. Negative raw Delta is not a refutation of the actual gauge-fixed form. Neither fully consistent touching coercivity nor shell coercivity is settled, and inequality of selectors rules out only that particular identification route. Statement-sheet rows 5 and 7 stay open.

Sources: [decision](s1-touching/DECISION.md), [design and corrected evidence](s1-touching/SPEC.md), `s1-touching/numerics/results.json`, `s1-touching/numerics/attack_check.json`.

## 2. Class inclusion — S-2

**What was tested.** Geometry scans asked whether a product box that touches all four edges of a plaquette contains all those edges in the frozen both-endpoint sense. Separate scans tested proposed four-touch and corner-coverage conditions on proper domains. These were set calculations, not operator calculations or full admissible-class witnesses.

**What the numbers showed.** Box comparisons on sides 1 through 8 had zero failures in either direction. Side 8 alone had 1,603,584 touch-cover instances. A product domain on side 8 had 108 inside/four-touch plaquettes but 300 corner plaquettes. An L-shaped two-block domain had 14 four-touch versus 12 inside plaquettes; its exhibited extra square had no covering product box. All 254 proper nonempty side-2 subsets and all 462 sampled side-3 entries failed the proposed corner coverage. The 462 entries are not necessarily distinct, and this is not a general saturation proof.

**Decision and open work.** Advance ten conditional geometry, regularity, class and headline comparisons. Both proposed headlines keep the frozen inside-plaquette operators. Their implication chain does not establish that either class has a proper nonempty admissible-domain instance with nontrivial test fields. That non-vacuity remains a blocker for substantive variant acceptance. The corner variant looks especially restrictive in the finite tests. Testing odd torus sizes does not test the source's odd blocking-factor regime above 11. No inclusion for the new S-1 shell class is supplied by these names.

Sources: [decision](s2-inclusion/DECISION.md), `s2-inclusion/numerics/decision_geometry.json`, `s2-inclusion/numerics/decision_attack.json`.

## 3. Coverage row — already settled in OPEN_ITEMS B1

**What was checked.** This item compared statement-sheet row 6 with the existing source declarations and B1. Integer scripts checked witness extents and their scaling; no operator, inverse or coercivity form was simulated.

**What the numbers showed.** The recorded 36-point scalar checks reproduced exactly. The listed unit/fine side pairs were 30/120, 120/480 and 264/1056. These exceed the side-8 numerical limit, so the existing witness was not silently replaced by a smaller torus. The arithmetic does not itself establish class membership or a violating field.

**Decision and open work.** The sentence saying the coverage-free granting-existence body is undecided is stale. Existing source results give failure of that body for every natural cube factor at least 10, every blocking factor at least 2 and every positive mass parameter. Keeping both coverage clauses gives the corresponding positive body. At blocking factor 2, the both-coverage constant-family body holds while the sites-only body fails. The negative result uses the actual well-definedness guard, not merely a junk inverse.

Stage B should compile three exact re-exports and inspect their axioms. [ROW6.md](coverage-row/ROW6.md) contains the proposed correction; the real statement sheet has not been edited. Whether the printed sentence implies coverage remains reading-only. Odd-scale sites-only cases and the remaining even-scale cases in OPEN_ITEMS M are not resolved by this correction.

Sources: [decision](coverage-row/DECISION.md), [replacement row](coverage-row/ROW6.md), `coverage-row/numerics/extent_check.out.txt`.

## 4. Eta and the top-level embedding — S-3

**What was tested.** A small rational matrix model compared three proposed coefficient recipes for the first term. It used nonzero second jets at levels zero and one and tested whether one scalar could reconcile the resulting forms for all model fields.

**What the numbers showed.** For two test fields, the frozen/printed ratio pairs were 56/57 versus 48/53 for plainH, 14/13 versus 4/3 for draft, and 7/6 versus 3/2 for linearEta. Thus the unrestricted stand-in model did not have a common ratio. A uniformBody control gave ratio 1. Removing the level-zero second jet made the plainH control give ratio 1 as well. The decision's exact recheck recorded 38 passing checks.

**Why this is not an accepted counterexample.** The actual wired level-zero second jet is zero, and its level-zero linear map is the identity. The model's nonzero level-zero jets therefore cannot arise from the genuine operators. Positive definite matrices and exact arithmetic do not repair that mismatch. The model also lacked the printed admissible test subspace and a background-derived source.

**Decision and open work.** Reject `NoScalar.lean` as a fidelity-counterexample plan. Instead compile the actual zero-level jet identities and the depth-one plainH/uniformBody coefficient equality. S-3 still needs a full units dictionary and comparison using genuine operators, adjoints, pairings, the top-level embedding, the mass subtraction, the nonlinear source term and the energy norm. These three local comparisons do not establish that dictionary.

Sources: [decision](s3-normalisation/DECISION.md), `s3-normalisation/numerics/out/results.json`, `s3-normalisation/numerics/decision_check.txt`.

## 5. Guarded all-plaquette reading — NOT READY

**What was tested.** The available, not yet decision-approved design studied raw Delta on side-3 and side-4 tori with a small proper domain, exterior-link paths and an interior bond defect. It did not assemble the actual guarded carrier `Ginv`, its gauge/mass terms, or the actual correction `Delta2`.

**What the recorded design reports.** At the flat background, the raw operator had kernel dimensions 87 and 198. Exterior changes produced negative directions while a kernel survived. On the flat-interior path the actual local source and correction vanish, so a common singularity would not separate the carrier from its corrected pencil. The one-bond defect moved the inside operator by about 0.634 in operator norm at defect size 0.2. That is a change of Delta, not a measurement of Delta2. No invertible actual carrier with a singular corrected pencil was produced.

**Decision and open work.** There is no `guarded/DECISION.md`; these are preliminary design reports, not accepted targets. The design's proposed intermediate crossing declarations are deliberately excluded from the decision-only Stage-B list. Obtain an adjudicated decision first. Small-torus raw-operator scans cannot decide `P428Target8SG`, its true guard, class membership, or the required threshold quantifiers. The stronger full-guard result already in the repository does not settle this weaker-guard question.

Sources: [unadjudicated design](guarded/SPEC.md), `guarded/numerics/crossing_results.json`; authoritative existing limits: OPEN_ITEMS K–N.

## 6. Statement-sheet questions

### Testable variants

**What was tested.** Strict versus non-strict collars; two meanings of the base-domain lattice; scaling from unit sites to fine sites; global versus per-patch gauge choice; the norm factor; and abstract threshold order.

**What the numbers showed, with the decision's corrections.**

- A side-8 example gave base-domain sizes 448 and 512 under the two readings, with minimum outside distance 3 for the smaller one. All 255 nonempty unions of side-4 blocks filled the torus under the tested reading-B enlargement. This does not hold for arbitrary nonempty site sets.
- A geometry-only collar example attained distance 2 exactly, so it passed the non-strict predicate and failed the strict one. It used `M = 1`, outside the actual headline regime. Depth-one sample sweeps found no strict/non-strict mismatch.
- Embedded distance checks had zero mismatches. The original collar-inequality test had no true cases; the repaired test had 3,648 true and 448 false pairs, still with zero mismatches.
- Correctly applying `TorusOK` to the unit side leaves no depth-at-least-two headline instance with fine side at most 8. The purported single small fit in the attack confused fine and unit sides. The selected formal lower bound is 16.
- All 16 central-subgroup gauges on a four-cycle failed to flatten it globally, while each tested arc flattened separately. This is not an exhaustive SU(2) gauge search or separation of the actual regularity classes, which permit small nonzero fields.
- Entrywise Pauli checks gave full Frobenius squared norm 2 versus normalized squared norm 1, with the same factor on seven coordinate samples.
- The bounded threshold toy separated two quantifier patterns. It did not establish non-implication between actual analytic headlines.

**Decision and open work.** Advance six comparison files: collars, conditional reading B, explicit distance scaling, global-to-per-cube inclusion with flat regularity, left-hand norm re-expression, and Total's existing implication plus an unbounded arithmetic toy. There is no new non-strict coercivity assertion, proper-domain reading-B analytic witness, strict global-class separation or source-uniformity verdict. The norm comparison changes only the lower-bound norm and rescales its constant; it does not close S-3.

Sources: [decision](sheet-variants/DECISION.md), `sheet-variants/numerics/decision_attack_results.txt`, `sheet-variants/numerics/decision_results.txt`. The decision overrides misleading labels retained in the attack output.

### Reading-only Q8, Q10 and Q11

**What was tested.** Small stand-in matrices checked the shapes of masked inverses, gauge fixing and inverse/constraint compositions. A side-4 support model checked touching bonds and solutions on selected dropped-bond rows. These were not the genuine one-step jet assembly.

**What the numbers showed.** The site-mass recurrence matched 21 exact rational pairs. Masked-inverse residuals were about 9e-16 and the Delta-pi quadratic identity residual about 1e-13. The abstract inverse-chain quadratic check was within 6e-14. Weighted and unweighted masses differed by at least 2.57. The support example had 12 both-endpoint bonds, 24 touching-only bonds and six dropped bonds, all touching-only. Joint constraint solving had residual below 6e-17; freezing other dropped variables could leave a residual at least 0.45. In the singular constraint-matrix branch, the construction became the identity and the remaining constraint had size 2.57.

**Decision and open work.** Retain a qualified reading record, with no new Stage-B declaration targets. General-spacing weights differ by eta; a same-space scalar inverse calculation does not justify exchanging compression and inversion. `Cop` solves only selected rows under the required bijectivity assumption, not every coarse constraint unconditionally. The matrix tests establish neither source intent nor genuine operator realization. Citation repairs in the design and script comments remain outstanding before reuse. Optional checks of existing declarations would not turn this reading record into a fidelity certificate.

Sources: [decision](sheet-reading/DECISION.md), `sheet-reading/numerics/results.json`.

## Next step

After the current reproduction gate passes, execute the ten-file, 39-declaration list in [STAGE_B.md](STAGE_B.md), keeping successful comparisons distinct from unresolved analytic and source-reading questions. Obtain the missing guarded decision before assigning that target any Lean work. No claim in this summary substitutes numerical agreement for compilation and the required axiom checks.

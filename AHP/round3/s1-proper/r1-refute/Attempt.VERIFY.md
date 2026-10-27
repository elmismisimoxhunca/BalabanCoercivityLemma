# Independent verification — S-1 proper, round 1 refutation

## Verdict: `closes-goal` (exact formal pin only)

The independently compiled theorem is

```lean
Round3.S1Proper.goalNeg1_proved : Round3.S1Proper.GoalNeg1
```

at `Attempt.lean:354` and the identical `Attempt.verify.lean:354`.
`GoalNeg1` is exactly `¬ GoalPos1`, and `GoalPos1` is `P428TouchFour`.
This closes the **unguarded, four-bond-class, corner-Delta/corner-J formal
headline** negatively. It does **not** establish that Balaban's printed lemma,
an existence-presupposing version, or an invertibility-guarded version is false.

## Independent evidence

The attempt was not edited. I copied it byte-for-byte and compiled only the copy:

```sh
cp AHP/round3/s1-proper/r1-refute/Attempt.lean AHP/round3/s1-proper/r1-refute/Attempt.verify.lean
AHP/round3/lean1.sh AHP/round3/s1-proper/r1-refute/Attempt.verify.lean
python3 AHP/round3/s1-proper/r1-refute/verify_audit.py
```

The first foreground wrapper invocation was interrupted while queued, with no
exit record; it is not success evidence. The subsequent invocation ran in the
persistent terminal `term_tejz7yp7mf`, waited for the shared lock, and exited 0.
The terminal is now exited, not running. Some client wait calls timed out; they
did not stop that persistent compilation. No direct Lean/Lake invocation, build,
reproduction run or dependency update was made.

Evidence files, all beside this report:

- `Attempt.verify.lean` — independently compiled, byte-identical source.
- `Attempt.verify.lean.log` — complete independent compiler output.
- `Attempt.verify.lean.exit` — **0**.
- `Attempt.verify.audit.json` — independent source/log audit, **pass: true**.
- `verify_audit.py` — reproducible source/log checker; no numerical model.

| Contract check | Result |
|---|---|
| (1) Independent exit 0 | **PASS**, no errors or warnings |
| (2) Exact main type | **PASS**: `theorem goalNeg1_proved : GoalNeg1 := by`, in `Round3.S1Proper`, without extra premises |
| (2) Copied definitions | **PASS**, all 10 pin definitions match after whitespace normalization; the entire shared options/open/namespace/variable/definition/check block is actually byte-identical |
| (3) All dependency prints permitted | **PASS**, 44 records for 44 commands; every set is a subset of `propext`, `Classical.choice`, `Quot.sound` |
| (4) Forbidden constructs | **PASS**, zero forbidden whole-word tokens even before removing comments; no opaque replacement |
| (5) Faithfulness | **Qualified**: matches the explicit round-3 item, with the source limitations below; CMP102 p.277 could not be independently image-checked |

The ten unchanged definitions are `plaqCorner`, `TouchBond`, `CoversPlaqFour`,
`CurlReadsTouch`, `PerCubeRegularTouch`, `ClassCoupledFour`, `selCorner`,
`P428TouchFour`, `GoalPos1`, and `GoalNeg1`. Their implicit extent context is
unchanged. `autoImplicit false` is retained. There are no additional theorem
parameters or local hypotheses on the main declaration. The three coverage
helpers beginning at line 240 are also byte-identical to the corresponding
block of `AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean:185–236`.

All 23 local declarations have their own dependency print. Direct imports are
only `D1Lit`, `D2Lit`, and `GdPlaq`, resolving to frozen files under `lean/src`;
there are no AHP imports or local replacements for the actual operators.
The main dependency record is:

```text
'Round3.S1Proper.goalNeg1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Hashes measured after independent compilation:

| File | SHA-256 |
|---|---|
| `Attempt.lean` and `Attempt.verify.lean` | `a114b3d28b83d02b8d38df0f26cfac3d1485bb4cb72bdcd0150bd392e79a0280` |
| `../pin/Statement.lean` | `dff1d868790779a2def248238b348234402a065760bdb0d0c9b675136fe7cf9f` |
| `Attempt.verify.lean.log` | `fb72117ac68c0ad97b024c2bcc461adea36b2e07cd1faf9e8b3e090137849b40` |

## What the proof actually establishes

I read the current proof, pin and PIN.md, the required handoff/status reports,
the relevant round-2 pins and proof passages, and the actual frozen selected
form and collapse mechanism in `lean/src/D1Lit.lean:39–101`,
`D1Main.lean:141–151`, and `D1Collapse.lean:57–89`.

1. `Attempt.verify.lean:142–225` proves that every omitted corner plaquette has
   all four field values zero on a touching-supported field. The **operator
   application** of corner Delta therefore equals all-plaquette Delta there.
   The frozen W support theorem propagates this through the actual W sandwich
   and Dirichlet compression, giving equality of the actual carriers. This is
   not equality with the frozen inside selector, unrestricted Delta equality,
   J equality, or a generic full-form comparison.
2. Lines 240–335 supply actual four-bond coverage on the slab and all three
   strict touching-regularity bounds along the exterior path. The path is one
   on every endpoint-touching link; each local gauge and logarithm can be one
   and zero respectively. Thus every positive smallness cap is respected,
   despite arbitrary exterior-link phases. This does not silently assume a
   bound on far links of a corner plaquette.
3. Lines 338–350 transfer the genuine all-plaquette carrier non-unit crossing
   to the corner carrier, not merely a negative raw-Delta pairing.
4. Lines 354–407 refute the full quantifier order: fix blocking factor 2 and
   mass parameter 1; choose the proposed lower exponent itself; choose
   `R = max R0 18` before receiving the cap and coercivity constant; then build
   the covered depth-two slab, compatible torus/Lambda, positive capped alpha,
   exterior-path background and genuine positive-energy `BseedNv`. Both test
   predicates are supplied. The boundary-point witness certifies a nonempty
   proper base even though properness is not a premise of the headline.
5. The final application is `not_InstIneqS_of_not_unit` with **both selectors
   `selCorner`**. The totalized full form collapses to the nonpositive mass
   subtraction; the positive-energy right-hand comparison fails for every
   positive coercivity constant. No unsupported numerical claim is used.

The refutation uses two-adjacent-corner boundary squares, not a one-corner
family. The item recommends investigating one-corner squares but does not
require that geometry. This is not a mismatch with the pinned goal.

## Printed-page audit and faithfulness concerns

### Pages actually inspected

I viewed readable resized images, saved in `verify-pages/`, of:

- CMP99 pp.392, 393, 394, 396, 408, 421, 428, from the corresponding
  `sources/corpus/renders/CMP99b_p*-*.png` files;
- CMP99 p.409 and CMP109 p.251 from the already saved renders under
  `AHP/round2/s1-touching/r1-prove/verify-pages/`;
- CMP96 p.224 from
  `sources/compute/domain_sequence_spec/renders/CMP96_p224-02.png`.

The saved source images exceeded the image reader's size limit; PyMuPDF was
used only to produce smaller readable copies under this item. No mathematical
numerical script was run or relied upon.

**Missing independent source check:** CMP102 p.277 is not present in the local
source collection or the advertised `notes/external_ymx/p102-01.png` location.
The quotation is recorded in `paper/OPEN_ITEMS.md:S-1` and
`notes/external_ymx/HARVEST.md:9`. External bibliographic lookup identified
Balaban, *The variational problem and background fields in renormalization
group method for lattice gauge theories*, CMP 102 (1985), 277–309,
DOI `10.1007/BF01229381`. Attempts to retrieve the publisher/Euclid PDF returned
HTML rather than a usable PDF. Those failed downloads were removed. I do not
claim to have viewed p.277. Its one-corner quotation remains inherited evidence;
CMP96 p.224 independently confirms the at-least-one-endpoint bond convention,
not the plaquette clause.

### Limits of the pin relative to the printed assertion

No discrepancy was found between the **explicit round-3 item** and its pin.
The following prevent treating formal closure as unrestricted source fidelity:

1. **Inverse existence is the decisive limitation.** CMP99 pp.421/428 use actual
   inverses, including (3.129) and (3.156). The pin retains totalized inverses
   without any existence premise or conclusion. This counterexample deliberately
   reaches a non-unit carrier. It does not defeat a guarded or
   existence-presupposing printed statement, nor supply an invertible
   negative-energy configuration.
2. **Corner selection does not settle boundary semantics.** CMP99 p.392 displays
   torus sums in (3.10)/(3.11); p.394 applies Dirichlet boundary conditions and
   emphasizes dependence only on the restricted background. The pin chooses
   corner plaquettes but keeps their full frozen background products, which
   can read far links outside the endpoint-touching set. Endpoint/corner set
   identification alone does not prove that this is the printed boundary
   operator. The exterior-path mechanism exposes precisely this distinction.
3. **Coverage is added and has a different antecedent from the selector.**
   `CoversOm0c` plus common-cube four-touch-edge coverage is not printed in
   (3.35)/(3.36). A selected square with one inside corner, or two adjacent
   inside corners, need not satisfy the four-edge antecedent. The p.396
   outside-domain sentence does not imply either coverage clause. Replacing
   this by common-cube corner coverage would change the question and exclude
   the proper-domain slab by the round-2 collapse theorem.
4. **Class/stencil interpretation remains qualified.** Endpoint-touching bonds
   agree with CMP96 p.224, and per-cube existential gauges agree with the
   grammar of p.396. But requiring every read bond to touch before imposing
   difference/curl bounds is an interpretation of “on the cube.” It does not
   bound all far edges read by every corner square. No common global gauge or
   compatibility among the cube gauges is asserted.
5. **Cube geometry and factor.** The pin uses aligned periodic product boxes,
   the frozen two-stratum/index conditions, and common factor 12. CMP99 p.396
   describes unions of several big blocks with cube-attached O(1) at least 10;
   p.409 chooses 12 in its application. These pages do not alone identify the
   complete factor-12 box class with the printed class. Non-box unions and
   per-cube factors are not included.
6. **Domain and lattice conventions.** Finite periodic rectangular three-
   dimensional SU(2) geometry, periodic l1 distance, half-open block alignment,
   padding above depth, and the fine/unit coordinate dictionary remain frozen.
   The pin takes the exact p.396 base layer under reading A. CMP99 p.394 also
   permits a thinner layer; no two-domain construction is substituted.
7. **p.408 clauses are not all premises.** The altered level-zero domain and
   third-enlargement alternative on p.408 are not imposed. The pin allows
   natural radii rather than only powers of the blocking factor. Its explicit
   proof-local lower bounds are derived by choosing large radii, not new
   headline premises.
8. **Blocking-factor range matters to this refutation.** The pin allows every
   natural blocking factor at least two. CMP109 p.251 explicitly takes odd
   L greater than 11. The present contradiction fixes L=2 and therefore gives
   no refutation in that narrower convention. Whether that later convention
   is intended for the earlier CMP99 assertion is not decided here.
9. **Uniformity is an explicit reading.** The pin fixes thresholds/constants in
   the frozen order, with the radius threshold after the exponent and the
   positive cap/coercivity constant after the radius but before geometry,
   depth and fields. CMP99 p.428 explicitly says independent of k and U;
   the complete elaborated quantifier order is not printed there.
10. **Norms and differential expressions.** The class retains full Frobenius
    norm while test energy uses the trace-normalized SU(2) norm; p.392
    explicitly normalizes the trace. The actual frozen curl-adjoint-curl
    expression is kept for (3.36), with its guarded local stencils. No new
    pointwise norm/differential dictionary is proved here.
11. **Averaging, constraints and normalization are inherited, not identified
    anew.** Genuine W, Q/jets, weighted mass, site operators, corrected inverse,
    multilevel covariance, C, selected dropped/axial constraints and touching
    test support are retained. CMP99 p.428's constrained field and one-variable
    description of C do not by themselves certify the frozen joint solution
    and singular fallback. Explicit eta/tau-star and all other summands remain;
    the round-2 inside-selector first-term result does not establish the whole
    changed-corner printed dictionary.
12. **“Proper” is a motivation, not a headline restriction.** The pin quantifies
    all admissible towers, rather than asserting the inequality only on proper
    nonempty bases. This is as requested. The actual refutation nevertheless
    uses a proper nonempty base; it is not an empty-domain artifact.

Thus all four formal acceptance checks pass, with a partial independent
printed-page audit and the limitations above. The safe conclusion is:
**the explicitly pinned unguarded four-bond touching-class headline with corner
Delta and J is false under the frozen totalized-inverse conventions.**

## Scope of writes

Only files below `AHP/round3/s1-proper/r1-refute/` were deliberately written:
the verification copy/log/exit, independent audit script/JSON/log, page-image
copies and this report. The builder attempt, pin and original builder records
were not changed. No protected file, other AHP item, commit or push was touched.

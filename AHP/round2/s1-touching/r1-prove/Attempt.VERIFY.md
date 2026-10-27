# Independent verification — S-1 touching, round 1, prove

## Verdict

**`closes-goal`: `Round2.S1.GoalPos2`, exactly as pinned.** Checks (1)–(4) all pass. This is **not closure of the unmodified printed S-1 question**: the added common-cube coverage excludes every proper nonempty base domain. The proof establishes this exclusion rather than hiding it.

Source-fidelity review found the material departures below. **The requested page-image review is incomplete at CMP102 p.277:** that image is absent from the checkout and attempted public retrieval did not supply it. I independently read the other cited page images listed below; I do not label the inherited CMP102 quotation independently verified. This limitation does not change the formal verdict, whose requested acceptance conditions are (1)–(4).

## 1. Independent compilation: PASS

I compiled the unchanged attempt, not the pin, with:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s1-touching/r1-prove/Attempt.lean > ../AHP/round2/s1-touching/r1-prove/Attempt.verify.log 2>&1
echo $? > ../AHP/round2/s1-touching/r1-prove/Attempt.verify.exit
```

`Attempt.verify.exit`: **0**. `Attempt.verify.log`: **84 lines**, no errors or warnings, 12 type checks and 72 dependency records. No other Lean file was compiled. No `lake build`, `lake update`, or `REPRODUCE.sh` was run. The builder's log and exit record remain untouched.

## 2. Exact goal and copied definitions: PASS

The declaration at `Attempt.lean:689` is:

```lean
theorem goalPos2_proved : GoalPos2 :=
  ⟨touchCoverageCollapse_proved, touchConsistent_iff_extreme⟩
```

The independent compiler prints at `Attempt.verify.log:34`:

```text
Round2.S1.goalPos2_proved : GoalPos2
```

Within this namespace `GoalPos2` is exactly `Round2.S1.GoalPos2`, copied from `../pin/Statement.lean:134–135` to `Attempt.lean:138–139`:

```lean
def GoalPos2 : Prop :=
  TouchCoverageCollapse ∧ (P428TouchConsistent ↔ P428Target8Extreme)
```

There are no extra theorem parameters, hidden section assumptions, replacement propositions, local notation changes, or shadow definitions. The only surrounding implicit variable is the same lattice variable from the pin; the printed closed theorem type has no lattice argument.

`verify_audit.py` mechanically compared **all 22 pinned definitions**, including every goal wrapper and the unused shell definitions. Every declaration is byte-identical, which is stronger than character identity after whitespace normalization. It also checked the **entire copied namespace prefix**, including the variable context, comments and pin checks/prints, for byte identity. The four additional definitions `cornerA`–`cornerD` are not in the pin; each is byte-identical to its Stage-B S-2 source in `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`. Per-definition names and source/attempt line numbers are recorded in `Attempt.verify.audit.json`.

All eight imports resolve under `lean/src/`: `ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, `D1Lit`, `ZR8Class`, `RI6`, and `AdalyFormal.Balaban.U1AnchorPoincare`. No AHP import is used.

## 3. Dependency checks: PASS

All **72/72** dependency records contain only subsets of `propext`, `Classical.choice`, `Quot.sound`; empty dependencies are allowed. Every one of the **67 local declarations** has a record, together with five frozen helpers. No dependency print is missing.

Main record, `Attempt.verify.log:45`:

```text
'Round2.S1.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Also independently confirmed: `goalPos1_proved : GoalPos1` (`Attempt.lean:575`, log line 33), with the same permitted three dependencies (log line 84). This is the coverage-repaired primary headline, not the shell fallback.

## 4. Forbidden constructs: PASS

A raw whole-source token scan of `Attempt.lean`, including comments and strings, found **zero** occurrences of the forbidden tokens `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. The permitted command `#print axioms` is not a hit for singular `axiom`. Source inspection found ordinary definitions and theorem proofs, no substitute operators, new assumptions, metaprogrammatic declaration injection, or imported AHP modules.

The audit script is a text/log check, not a numerical model. It performs no Lean execution and does not modify the attempt or pin. Reproduce it from the workspace root with:

```sh
python3 AHP/round2/s1-touching/r1-prove/verify_audit.py
```

## Proof-content audit

I read the complete attempt and the pin, rather than relying on the builder's report.

- `Attempt.lean:420–449`: a product box touching all four boundary edges contains all four corners. The diagonal/antidiagonal proof handles wrapped coordinate boxes.
- `Attempt.lean:472–512`: every frozen class cube in a nested tower lies in the base; corner coverage therefore forces `plaqCorner (S.Om 0) = plaqIn (S.Om 0)`.
- `Attempt.lean:452–470,514–522`: class inclusion transfers both coverage clauses and all three regularity clauses, with the same per-cube gauge and matrix field. Neither the difference guards nor the backward/forward curl guards are omitted.
- `Attempt.lean:527–557`: equality propagates through **both** selected operators, `dataS`, `G1invS`, and the full `GenS.genFormS`, including the inverse, mass term and nonlinear J term. `lean/src/D1Lit.lean:39–101,138` confirms these are the genuine frozen selector-parametrized operators and instance inequality; no raw-Delta surrogate is used.
- `Attempt.lean:579–630`: selector equality forces shift-invariant membership; frozen `U1AnchorPoincare.eq_of_shiftInvariant` yields empty/full collapse. The proved nested-tower version is stronger than the pin's headline-geometry obligation, not weaker.
- `Attempt.lean:656–686`: the implication from the extreme frozen headline to the touching headline uses collapse, class inclusion and full-form equality. The opposite implication deliberately ignores its touching-headline premise and restricts the already-proved `RI6.p428Target8`, as `PIN.md` expressly permits. This is a logical equivalence of true headline propositions, **not** reverse class inclusion or equality of admissible configurations/constants in both directions.
- `Attempt.lean:560–576`: the separate primary proof reuses the frozen quantifier order and thresholds without adding a room, flatness, invertibility or fixed-depth premise.

## 5. Source faithfulness: material departures remain

### Pages actually read in this verification

I read `PIN.md` completely and independently viewed these printed pages:

| Printed page | Local evidence | Relevant content |
|---|---|---|
| CMP99 p.392 | `sources/corpus/renders/CMP99b_p392-04.png` | Normalized trace; (3.10) sums over torus plaquettes; (3.11) pairs over torus bonds; mesh factors appear explicitly. |
| CMP99 p.393 | `sources/corpus/renders/CMP99b_p393-05.png` | Nested domains; composite averaging; Dirichlet introduction; weighted mass form (3.16). |
| CMP99 p.394 | `sources/corpus/renders/CMP99b_p394-06.png` | Dirichlet compression and inverse; permits the RM layer or a thinner block layer; states boundary operators depend on U restricted to the domain. |
| CMP99 p.396 | `sources/corpus/renders/CMP99b_p396-08.png` | Cube-attached size O(1), at least 10; union of several big blocks; unique stratum index; per-cube gauge and (3.35)–(3.36); no constraints outside the domain. |
| CMP99 p.408 | `sources/corpus/renders/CMP99b_p408-20.png` | Corollary 3.6 hypotheses; altered zero-level set for the random-walk cover; R and M taken as powers of L; third-enlargement clause. |
| CMP99 p.409 | PDF page 21 of `sources/compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf` | Choice 12 and the local cube-containment/application discussion. |
| CMP99 p.428 | `sources/corpus/renders/CMP99b_p428-40.png` | (3.156), support/constraint construction, and positive bound independent of k and U under (3.35)–(3.36) and small M alpha. |
| CMP109 p.251 | PDF page 3 of `sources/compute/balaban_su2_papers/balaban_CMP109_1987_RGapproach_I.pdf` | Odd positive L greater than 11; continuum torus and lattice definitions; site/bond/plaquette identification by intersection. |

Readable resized/rendered copies are in `verify-pages/`. Printed page numbers were checked on the images. These are evidence images, not new mathematical computations.

**Missing page:** CMP102 p.277, the principal endpoint/corner quotation. `notes/external_ymx/HARVEST.md` refers to `p102-01.png`, but that file and the CMP102 PDF are absent here. Public searches identified Balaban's article, DOI `10.1007/BF01229381`; attempted Michigan and Springer retrieval returned HTML or access errors, not its scan. The unusable download and blank rendering were deleted. I rely only on the explicitly inherited quotation for that page, not an asserted fresh image check. CMP109 p.251 corroborates an intersection convention but is not a replacement for reading CMP102 p.277.

### Why this pin does not settle the original item

1. **Unprinted coverage is decisive.** `Statement.lean:45–48` requires every one-corner plaquette to have all four boundary bonds touching **one common frozen class cube**. Neither the inherited CMP102 quotation nor the inspected p.396 class wording supplies this requirement. Site coverage is also retained as an extra hypothesis. The now-proved collapse (`Attempt.lean:622–630`) eliminates **every proper nonempty base**, precisely where touching and inside conventions have a boundary to compare. Thus this is a successful reduction of an explicitly repaired formal class, not evidence that Balaban's ordinary domains collapse or that his original class satisfies the inequality.
2. **Boxes and factor choices matter.** The pin uses aligned periodic product boxes and one global factor 12. The p.396 wording describes cubes as unions of several big blocks with cube-specific size O(1), while p.409 chooses 12 in a local construction. Product structure is load-bearing in the proof. No theorem here transfers the collapse or headline to arbitrary block unions, varying factors, or the altered zero-level class.
3. **The boundary-operator reading is not identified with the print.** Corner selection for both Delta and J is faithful to the pin's interpretation, but is not the unrestricted sum displayed on p.392. Relating it to p.394's Dirichlet prescription and dependence on the restricted configuration still needs an operator dictionary. The proof avoids that issue by establishing selector equality only on the coverage-collapsed class.
4. **Regularity boundary stencils remain an interpretation.** Touching replaces both-endpoint guards in all three bounds, correctly. However, the existential global extensions of the per-cube gauge/logarithm, and evaluation of derivative/curl-of-curl bounds only when all their read bonds pass guards, are formal treatments of “on the cube”; the source quotation alone does not establish these choices.
5. **Geometry and ranges stay specialized.** Dimension three, SU(2), finite periodic rectangular lattices, divisibility, periodic l1 distance, half-open aligned blocks, padding, and reading A remain. The exact base layer does not implement p.394's thinner-layer option. The p.408 third-enlargement requirement is not added. All natural ell at least 2 and natural R above a threshold differ from the later odd-L restriction and the p.408 power-of-L radius convention. Whether those later conventions are intended globally is not settled by the proof.
6. **Other statement-fidelity questions are inherited, not discharged.** The radius threshold depends on m in the frozen order; normalization uses the frozen Frobenius class bounds, trace-normalized energy and curl-of-curl; the complete Q/jet/C/support dictionary remains unproved here. In particular, `D1Lit.lean:88–94` retains the explicit eta/tau-star first term, absent as such in displayed (3.156). S-3 is not solved by selector equality. Lambda, dropped-bond constraints, the common collar radius and empty Lambda remain the frozen choices.
7. **No printed-inverse existence certificate.** The same totalized inverse and singular constraint fallback remain, with no added well-definedness guard or existence conclusion. Equality of these formal operators is not identification with every existence-presupposing printed inverse.
8. **No proper-domain or shell closure.** `GoalPos3` is copied but not proved. The shell's `ReadBond` bounds include edges with neither endpoint in a cube and thus strengthen the endpoint convention; its non-collapsing coverage is a different class. No nonzero-test witness for the surviving extreme class, general non-flat richness theorem, or proper-domain changed-operator coercivity theorem is supplied by this attempt.

Accordingly: **accept the exact pinned reduction and the separately printed primary proof; keep unmodified S-1, the shell fallback, and the outstanding source dictionary open.** The limitation is in the pin's connection to the requested printed reading, not a failure to prove the pin.

## Hashes and write scope

- `Attempt.lean`: `d45e27d564812a3b7679b3efdaad008ba833a74604dac5dc66cf32fd78bc5d40`
- `../pin/Statement.lean`: `0ad24d3129dc87c72d1fdc8281a9f7f08a66526a17ef2a697431b8ad8be5ea7c`
- `Attempt.verify.log`: `153aef38bce2a0d463ab46fd1907e808a32d11075111d53410026def37385b40`
- `Attempt.verify.exit`: `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`

The attempt hash measured before and after verification is unchanged. Only verification artifacts under `AHP/round2/s1-touching/r1-prove/` were written. No protected source, pin, builder report/log, other AHP directory, git commit, or push was changed/performed. No numerical experiment was run; prior Stage-A numerics were inspected as background only and are not evidence for this acceptance.

# Independent verification — S-2 non-vacuity, round 1 positive attempt

**Verdict: `closes-goal` — the exact pinned four-bond `GoalPos1`, not printed-statement fidelity.**

The attempt was not edited. I independently recompiled it, checked the current source against the pin and Stage-B definitions, read the proof, and checked the fresh dependency output. All four mandatory correctness checks pass. No mismatch with this round's four-bond non-vacuity request was found. The broader printed-class limitations are listed below and remain substantive.

## 1. Independent compilation

Executed once, serially, using the already prepared frozen oleans:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.verify.log 2>&1
echo $? > /home/sebastian/BalabanCoercivityLemma/AHP/round2/s2-nonvacuity/r1-prove/Attempt.verify.exit
```

- [Fresh exit record](Attempt.verify.exit): **0**.
- [Fresh compiler output](Attempt.verify.log): **no warnings or errors**.
- **40 dependency records**, including multiline records and the empty dependency list for `nvLu`; every list is a subset of `propext`, `Classical.choice`, `Quot.sound`.
- All 40 source `#print axioms` commands have corresponding records; all local theorems are printed.
- Main record:

```text
'AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is independent compilation evidence, not reuse of `Attempt.lean.log`, `AUDIT.json`, or the supplied attempt report. No whole-project build, update, or reproduction script was run.

## 2. Exact statement and copied definitions

`Attempt.lean:293` declares, with no parameters or extra hypotheses:

```lean
theorem goalPos1_proved : GoalPos1 := by
```

The fresh compiler confirms:

```text
AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved : GoalPos1
```

Here `GoalPos1` is exactly `AdalyFormal.AHP.Round2.S2Nonvacuity.GoalPos1`, defined at `Attempt.lean:136`, copied from `../pin/Statement.lean:133`. There is one local namespace, no local notation or alternate goal definition, and no ambient hypothesis that weakens the declaration. The pre-definition options, namespace, opened namespaces, and implicit extent variable are identical to the pin. The additional frozen imports introduce the witness helpers, not a replacement goal.

All **14 definitions** match the pin character-for-character as declaration text, even before whitespace normalization:

| Definition | Pin line | Attempt line | Exact / whitespace-normalized match |
|---|---:|---:|---|
| `TouchBond` | 41 | 44 | pass / pass |
| `CoversPlaqFour` | 44 | 47 | pass / pass |
| `plaqCorner` | 49 | 52 | pass / pass |
| `CoversPlaqCorner` | 54 | 57 | pass / pass |
| `CurlReadsTouch` | 59 | 62 | pass / pass |
| `PerCubeRegularTouch` | 64 | 67 | pass / pass |
| `ClassCoupledFour` | 84 | 87 | pass / pass |
| `ClassCoupledCorner` | 87 | 90 | pass / pass |
| `ProperFourAt` | 98 | 101 | pass / pass |
| `ProperCornerAt` | 113 | 116 | pass / pass |
| `GoalPos1` | 133 | 136 | pass / pass |
| `GoalNeg1` | 142 | 145 | pass / pass |
| `GoalPos2` | 153 | 156 | pass / pass |
| `GoalNeg2` | 161 | 164 | pass / pass |

The first eight also match their actual Stage-B originals in `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean` exactly. Frozen definitions such as `Admissible`, `IsClassCube`, `LambdaOK2`, and the input-space predicates are used directly, not replaced with local stand-ins.

Independent audit: [verify_audit.py](verify_audit.py), [Attempt.verify.audit.json](Attempt.verify.audit.json). The script checks the declaration texts, context, source/log main-type evidence, direct imports, dependency records, forbidden tokens, and fresh exit code. It is a textual audit, not a numerical operator model or a substitute for Lean's elaboration.

Hashes of the files independently checked:

- Attempt: `2e2d384afeab5a5fa1a0249c7e3960eef91078888b071463bf0228538cc07f8a`.
- Pin: `826f93c754d1c78a13e8ee7a832fc3041b36cd9cbe4628cde3a7475d752909f9`.

## 3. Safety and proof substance

Full raw-source token scan: **no hits** for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. Reading the complete attempt found no alternate elaborator command, placeholder definition, or concealed hypothesis. The direct imports are exactly `ZT5A`, `D1Final`, `ZR8Class`, each present under frozen `lean/src/`; there are no AHP imports. The main dependency print also covers its transitive proof dependencies.

The proof supplies the actual non-vacuity obligations rather than assuming them:

1. `four_touch_cubeBond_of_transverse` (`Attempt.lean:185`) proves that on a transverse-invariant site set, touching all four edges forces all four vertices inside. The ordered plaquette's second direction is nonzero; membership is invariant under that shift. The argument uses the actual periodic boundary edges and shift commutation, not a Euclidean surrogate.
2. `slabNv_transverse` (`:221`) checks that property for frozen `SlabNv`. `slabNv_coversFour` (`:230`) then transfers the frozen coverage witness, with exactly the same class cube, to the pinned four-bond coverage. This is a slab argument, not a claim for arbitrary towers.
3. `perCubeRegularTouch_one` (`:240`) supplies gauge one and matrix field zero, proves positivity of every strict bound, and evaluates the actual `ddA`; no zero cap or weakened inequality is used.
4. `properFourAt_two` (`:268`) supplies a complete instance for every \(m\ge1\), \(R\ge18\), and positive cap. It uses \(\ell=k=2\), \(M=2^m\), frozen `nvLu`, `SlabNv`, `LamN`, flat background, and \(\alpha_0=a_0/(12M)>0\). The cap holds with equality. Frozen geometry supplies admissibility, torus compatibility, Lambda compatibility, actual factor-12 coverage, and a boundary point proving nonempty proper base domain.
5. The final conjunct uses `BseedNv_props` (`lean/src/NV6.lean:203`) to supply a nonzero field of positive energy satisfying **both** `OnLambdaTildeIn` and `OnLambdaT`. These are precisely the two input predicates in `InstIneq` (`lean/src/ZT5A.lean:56`); empty-Lambda or zero-test-field vacuity is not used.
6. `goalPos1_proved` (`:293`) chooses \(m=\max(1,m_{\rm lower})\), then \(R=\max(R_{\rm lower},18)\), **before** receiving the cap. It therefore meets the pinned cofinal quantifier order. The missing mass symbol in the pin is harmless for this non-vacuity request: taking \(a=1\), its outer assumptions supply frozen `SidePow6` (`ZT5A.lean:200`).

## 4. Faithfulness audit and limitations

Read `../pin/PIN.md`, `HANDOFF.md`, the requested `OPEN_ITEMS.md` sections B, K–N, R, S, the Stage-B results, and the S-2 specification/attack/decision and Lean comparison. Read the five cited adjudicated transcriptions and **independently viewed all five printed pages** from the supplied source PDF:

- [CMP99 p.393](verify-pages/CMP99b_p393.png): nested domains, strata, Dirichlet domain, scale-dependent quadratic form.
- [CMP99 p.396](verify-pages/CMP99b_p396.png): class cubes, unique index, base block collar, per-cube gauge and bounds (3.35)–(3.36).
- [CMP99 p.408](verify-pages/CMP99b_p408.png): powers-of-\(L\) scales, altered level-zero set, local-domain construction and third-enlargement clause.
- [CMP99 p.427](verify-pages/CMP99b_p427.png): unit-lattice Lambda and collar, constrained Gaussian expression.
- [CMP99 p.428](verify-pages/CMP99b_p428.png): constrained \(B\) versus free \(\widetilde B\), reconstruction \(B=C\widetilde B\), and the lower-bound assertion.

Images were rendered locally from `sources/compute/balaban_su2_papers/balaban_CMP99_1985_propagators_backgroundfield.pdf`; its SHA-256 is `39f8033b35838c7bdd14f97c7fb1edb0b35d4190b8b88f31d19d12a72d542861`, matching the transcription provenance. The CMP102 p.277 source is absent locally; its endpoint/corner convention was checked against the supplied quotation in `OPEN_ITEMS.md` S-1, **not independently against that page image**.

### Does the pin say what this item asks?

**Yes, for the explicitly selected four-bond non-vacuity branch.** It demands actual proper nonempty admissible-domain membership, factor 12, positive capped smallness, Lambda, and a genuine nonzero admissible input field at cofinal scales. The workflow item explicitly allows this branch to close the item and treats the corner branch separately. No additional omission blocking that narrow conclusion was found.

It does **not** resolve the original printed-class question. The following are the ways it is narrower than, or departs from, that broader reading:

1. **Four-touch is not one-corner.** `CoversPlaqFour` selects plaquettes whose every boundary edge touches the base domain. It does not select every plaquette with one corner there. Thus a four-bond witness cannot be promoted to a `ClassCoupledCorner` witness or to the fully consistent CMP102 convention. Neither corner positive nor corner saturation is proved here.
2. **Coverage is additional.** Site coverage and coverage by one class cube are explicit formal hypotheses, not clauses established by the p.396 regularity paragraph. The proof genuinely constructs them, but does not derive their printed legitimacy.
3. **Restricted cube family and boundary prescription.** The pin keeps aligned product boxes, one common factor 12, the unique stratum index, and frozen base law. Page 396 describes a cube as a union of big blocks with its own \(O(1)\ge10\) size. Membership in the fixed formal family does not identify all printed families. Touching finite-difference and curl-read guards are chosen prescriptions; the print only says the bounds hold on the cube. No shell, arbitrary block union, altered p.408 zero-level class, or third-enlargement clause is incorporated.
4. **Scale generality is limited.** `GoalPos1` needs one blocking factor and cofinal exponents/radii, not all blocking factors or all sufficiently large values. This attempt uses \(\ell=2\); it therefore says nothing about the separate odd-\(L>11\) convention noted in S-4. The pin permits natural radii instead of requiring powers of \(L\) as p.408 does. The stronger helper here works at every natural \(R\ge18\), so powers of 2 can also be selected, but no odd-blocking-factor result follows.
5. **Frozen geometry and specialization remain.** Dimension three, SU(2), periodic distance/wrap, aligned half-open tiling, padding above depth, and reading A for the fine-lattice/base-domain interpretation are retained conventions. There is no thinner-layer or two-domain correspondence theorem in this attempt.
6. **Non-vacuity is not coercivity or inverse existence.** Page 428 asserts a uniform positive bound for the reconstructed field, not just existence of a free input. The pin contains no quadratic-form comparison or inverse-existence conclusion. Using \(\widetilde B\) rather than imposing \(Q_1\widetilde B=0\) is correct for the frozen input space, but the frozen dropped-row/axial/support correspondence to the printed \(C\widetilde B\) is not newly established.
7. **Flat background suffices only for existence.** The witness is flat at fixed depth two, not a non-flat-richness result or an all-depth family. This is explicitly permitted by the pin and suffices for the requested existential non-vacuity; it does not address the arbitrary-background analytic assertion on p.428.
8. **Norm and operator fidelity remain separate.** The pin retains the full Frobenius class-bound convention, strict mesh powers, explicit \(12M\alpha_0\le a_0\) cap, and frozen input energy. It does not compare touching/corner operators with frozen `plaqIn`, normalize the eta/tau-star first term, or resolve the guarded all-plaquette statement.

These limitations are consistent with the pin's disclosures; they are not grounds for rejecting a proof of its exact formal goal. They do prevent reporting this verification as closure of S-1, full S-2 printed fidelity, S-3, or the guarded headline.

## 5. Final disposition and write scope

**Accept:** `AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved` closes the exact pinned `GoalPos1`. The former independent non-vacuity hold for the formal four-bond class is discharged at the stated scope. The radius bound 18 is sufficient for this witness family, not asserted necessary or sharp.

**Still open here:** corner-class disposition, printed-class identification, odd-blocking-factor/non-flat generalizations, changed-operator coercivity and the other fidelity items.

This verifier wrote only `Attempt.verify.log`, `Attempt.verify.exit`, `verify_audit.py`, `Attempt.verify.audit.json`, the five source-page renders under `verify-pages/`, and this report, all under `AHP/round2/s2-nonvacuity/r1-prove/`. The attempt, pin, original builder evidence, frozen sources, sheet, paper, and Lake configuration were not edited. No numerical simulation, deletion, commit, push, or deployment was performed.

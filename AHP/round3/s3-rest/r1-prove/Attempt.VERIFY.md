# Independent verification — S-3 rest, round 1, prove

## Verdict: `closes-goal` — **GoalPos2 only, with source-fidelity qualifications**

The attempt passes all four formal acceptance checks. It proves the exact normalized-constraint pin, not merely the previous first-term goal. This is not an unconditional certification of Balaban's printed operators, covariance, or coercivity headline.

- Main declaration: `AdalyFormal.Round3.S3Rest.goalPos2_proved : AdalyFormal.Round3.S3Rest.GoalPos2`.
- Source and identical verification copy: `Attempt.lean:1268` / `Attempt.verify.lean:1268`.
- Pin: `../pin/Statement.lean:457–461`.
- Stronger result: `restComparison_normalized`, `Attempt.lean:1252–1265`, needs only the pinned inverse guard, not the configuration predicate.
- `GoalPos1` (raw constraint) is **not proved by this attempt**. Its relationship to the normalized branch is not supplied as an additional theorem here.

## 1. Independent compilation — PASS

The attempt was not edited. From the workspace root I ran:

```sh
cp AHP/round3/s3-rest/r1-prove/Attempt.lean AHP/round3/s3-rest/r1-prove/Attempt.verify.lean
cmp AHP/round3/s3-rest/r1-prove/Attempt.lean AHP/round3/s3-rest/r1-prove/Attempt.verify.lean
AHP/round3/lean1.sh AHP/round3/s3-rest/r1-prove/Attempt.verify.lean
```

The shared-lock wrapper completed with **exit 0**. Independent evidence is `Attempt.verify.lean.log` and `Attempt.verify.lean.exit`, not the builder's log. The independent log has **0 errors, 28 nonfatal warnings, and 143 dependency records**. The warnings concern deprecated lemmas, unused simp arguments, and unused/unreachable tactics; none is a proof failure.

No direct Lean/Lake/build/reproduction/update command was run. No numerical experiment was run.

## 2. Exact type and copied definitions — PASS

The entire 26,607-byte pin is a **byte-identical prefix** of the 61,934-byte attempt and verification copy. This is stronger than equality after whitespace normalization: all pinned definitions, goals, quantifiers, guards, source comments and logical helpers are unchanged.

The main declaration is literally:

```lean
theorem goalPos2_proved : GoalPos2 := by
  intro r P _ hI
  exact restComparison_normalized P r hI
```

It is inside `namespace AdalyFormal.Round3.S3Rest`, with no ambient section variables, replacement goal, local notation, or additional theorem premise. There is exactly one declaration of this qualified main name. `GoalPos2` resolves to the pin's local definition, which says:

```lean
∀ r : Reading, ∀ P : IngrBParams,
  AdmissibleConfiguration P → InversesExist P r →
    RestComparison P r .normalizedConstraint
```

Thus the successfully elaborated theorem has exactly the pinned type, not a strengthened antecedent or an existential substitute. `RestComparison` at pin lines 434–444 includes the mass subtraction, final nonlinear subtraction, whole form, independent-field energy, C, and equivalence of the full instance inequalities for every real gamma. `gammaScale` at line 420 is literally 1, and a is unchanged.

Additional independent text checks:

- Sole import: frozen `ZT5A`; no AHP import.
- The reused round-two dictionary from `abbrev Fine` through `InversesExist` matches the round-two pin after whitespace normalization.
- Round-two `r1-prove/Attempt.lean:359–820` is copied byte-for-byte; its old positive goals are not substituted for this goal.
- All **143 explicit local declarations** are uniquely named and have corresponding dependency prints.

These checks and hashes are reproducible with `python3 AHP/round3/s3-rest/r1-prove/verify_audit.py`; results are in `Attempt.verify.audit.json`. This is an independent source/log audit, not the builder's `audit.py` and not an operator simulation.

## 3. Dependencies — PASS

All **143/143** requested `#print axioms` records are present in the independent log, including multiline records. Every list is a subset of `propext`, `Classical.choice`, `Quot.sound`; no unexpected or missing record was found.

```text
'AdalyFormal.Round3.S3Rest.restComparison_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.S3Rest.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Forbidden constructs — PASS

A whole-token scan of the **raw, unstripped attempt/copy** found none of `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. Scanning raw text also checks comments and attribute text rather than potentially hiding operative attributes. The audited source uses genuine frozen primitives and ordinary proofs, not local stand-ins or extra trusted declarations. This is an audit of the attempt and its printed dependency closure, not a claim to have rescanned/rebuilt the entire repository.

## 5. Proof and faithfulness audit

### What the proof actually establishes

I read the required handoff/open-item sections, Stage-B and round-two results, both S-3 pins, the round-two judgement/proof, and the new proof. I also inspected frozen `ZXR2Unit2.lean:39–145`, `ZXR2Wire2.lean:35–91`, `ZXG3A.lean:35–58`, and `ZT5A.lean:56–61` against the relevant copied definitions.

The new proof does the substantive remaining work:

1. Lines 1100–1115 identify the normalized trace/unit pairing, separate mass subtraction and independent-field energy.
2. Lines 1117–1160 identify the genuine normalized first jet, matching second coefficient, coupled matrix/lift, Dtilde and C. Lines 1128–1140 explicitly handle both the bijective and singular branches of the frozen inverse; no new corridor guard is hidden in the theorem.
3. Lines 1163–1219 identify physical H1 using the **full multilevel inverse**, and use top spacing one for both linked H/C conventions.
4. Lines 1221–1233 cancel the physical J factor against the fine pairing and identify the entire final nonlinear term, including factor 2.
5. Lines 1235–1265 combine these with the copied first-term identity and transfer the unchanged independent-field domain through the inequality.

This proves equality for all B, so it does not exploit an empty test subspace or the configuration assumptions. It does not, however, prove that the inverse guards have admissible inhabitants.

### Printed-page checks

I read the source transcriptions for CMP99b pp.392–394, 396, 408, 419–428, at the displayed equations and surrounding text. I directly inspected these page images:

- Round-two `pin/renders/p392.png`, `p393.png`, `p394.png`, `p419.png`, `p420.png`, `p421.png`, `p422.png`, `p428.png`.
- Round-three `pin/renders/CMP109_p267.png`.
- `verify-renders/CMP99b_p427.png`, rendered in this permitted directory from PDF page 39 of the repository's CMP99b PDF using the already-installed PyMuPDF (longest side 1900 pixels).

The images support the normalization choices: normalized trace on p.392; the argument and linear/remainder factors in (3.14); constant bond mass a in (3.16), as distinct from the site recursion (3.24); physical H/H1 and linked C conventions on pp.420–422; unit-lattice B on p.427; all three summands in (3.156) and energy of the independent variable in the lower-bound claim following (3.158). There is no external eta or tau in the displayed (3.156). The first-term proof supplies their encoded interpretation rather than reading them into the display.

CMP109 p.267 visibly gives the raw constraint `L Qtilde B' + Ctilde(B')`, `L Qtilde h = I`, `Dtilde^(2) = Ctilde^(2)` **before applying h**, and the lifted term `H1 h Ctilde^(2)` in (2.11), followed by an explicit reference to (3.156). Dividing both constraint and remainder by ell is therefore a defensible linked normalization, not an independently chosen power for one summand.

### Ways this pin falls short of unrestricted item/source fidelity

These are scope qualifications, not failures of checks 1–4:

1. **The missing CMP99b formula is supplied by a later source.** CMP99b p.427 only calls Dtilde a quadratic polynomial with similar properties restricted to unit blocks. It does not uniquely specify the pin's coefficients. CMP109 p.267 supplies strong evidence for the lifted-remainder reading, but its back-reference expressly says the delta-function gauge-fixing term is replaced by an exponential one. The pin does not prove transfer of that later construction to every earlier domain/gauge setting. A CMP99b-only identification remains a reading question.
2. **Coupled solve versus printed local solve.** Pin lines 364–374 use `rhoD * Q * iotaD` and its coupled inverse on the retained dropped set. CMP99b p.428 describes solving each equation for one bond; CMP109 p.267 writes a pointwise coefficient h(c), supported on b0, and an identity on the full coarse lattice. Equality with the frozen coupled lift does not prove this decoupling, locality, or global right-inverse property.
3. **The printed constrained subspace is not identified.** `PrintedInstIneq` at line 414 copies the frozen independent-field conditions. The pin does not prove that C parametrizes exactly all fields with printed Lambda support, axial zeroes and **global** Q1 kernel. Those conditions appear separately in `AdmissibleB`, but are not a positive-goal parametrization theorem. An all-B form identity is useful and avoids a false constraint premise; it does not by itself certify the source's Gaussian change of variables or (3.157)–(3.158).
4. **Totalized corridor inverse.** Positive `GoalPos2` deliberately has no `CorridorInversesExist` hypothesis; its inherited inverse guard does not include H0. At singular H0, the equality compares two zero-fallback extensions, not a printed inverse or a solution of the constraint. On the additional nonsingular regime the comparison still applies, but inverse existence, positivity and guarded non-vacuity are not proved here.
5. **Retained boundary/class/geometry departures.** The physical-unit dictionary retains inside-plaquette Delta/J, both-endpoint cube regularity, added site/inside-plaquette coverage, touching bond/Lambda carriers, fixed factor-12 boxes, aligned half-open tiling, periodic l1 geometry, natural radii, empty padding, and the p.396 base-domain choice. It specializes to finite three-dimensional SU(2), the stated chart, positive ell-powers M and R at least 18. It neither repairs S-1/S-2 nor establishes that these selectors/class are the literal print; source power/odd-L conventions are not recovered by this theorem.
6. **Shared analytic primitives.** Both sides use the genuine frozen componentwise averaging jets and blocked background. That excludes arbitrary matrices or free second jets, but their complete analytic/source identification and control of derivative totalizations are not proved by this normalization comparison.
7. **Conditional algebra, not a new threshold theorem.** No smallness hypothesis is shown to imply the inverse guards. No positive depth/background-uniform coercivity constant, threshold, covariance or Gaussian integral theorem is newly proved. The equivalence is conditional at each instance, for every gamma, with uniform rescaling 1 and unchanged a. Calling it the “(3.157) instance inequality” is shorthand: (3.157) itself is a Gaussian identity, while the lower-bound assertion follows (3.158).
8. **One unit-constraint branch only.** Both p.421 H/C conventions are quantified, but this artifact closes only the normalized unit-constraint branch. It is not a proof of the separate raw-constraint `GoalPos1` or an exhaustion of all historical readings.

Accordingly, the accepted wording is: **Under the unchanged pinned inverse guards and retained source conventions, the normalized unit constraint gives exact agreement of the remaining summands, C, independent-field energy, whole form and full instance inequality, with c=1 and unchanged a, for both linked H/C conventions.**

## Evidence hashes and write scope

| Artifact | SHA-256 |
|---|---|
| `../pin/Statement.lean` | `799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b` |
| `Attempt.lean` and `Attempt.verify.lean` | `9aa7238ddbff572aea7b0f0394eb22325280451f46087ec6e99da0f3518ae6a2` |
| `Attempt.verify.lean.log` | `25c714d0d87a315a0db64008db860dd9e285898afc45cda2a6975579c9f7c678` |
| `Attempt.verify.lean.exit` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |

Only independent verification artifacts under `AHP/round3/s3-rest/r1-prove/` were written. The original attempt, its original evidence, the pin, round-two files, frozen Lean tree, manuscript and other workers' files were not edited. No commit or push was made.

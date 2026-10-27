# Independent verification — assembly R2 / P2Goal

## Verdict

**Compilation, provenance, axioms, and the stated mathematical progress: PASS.**

**Strict requested main-declaration/target gate: FAIL for the submitted `mainDeclaration`.** `AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine` proves an unconditional whole-kernel crossing theorem, but its type is neither `GoalNeg2`, an unconditional sufficient cofinal premise with a compiled bridge to `GoalNeg2`, nor one of the exact P1–P3 propositions. Its crossing conclusion still needs detection (P3) to reach the final goal. This is a declaration-selection issue, not a failed proof or an undisclosed physical hypothesis.

The same verified file **does prove exact P2**, via `AdalyFormal.Round13.Assembly.R2.p2 : AdalyFormal.Round13.Assembly.R1.P2` (line 11049). Selecting that declaration would satisfy the permitted P1–P3 target gate. No source repair is needed for that narrower claim. P1 is integrated; **P3 and unconditional GoalNeg2 remain open**.

## Fresh compilation

Copied `P2Goal.lean` byte-for-byte to `P2Goal.verify.lean`, then executed exactly once:

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r2/P2Goal.verify.lean
```

- Long timeout: 3600 seconds; command returned without timeout or relaunch.
- `P2Goal.verify.lean.exit`: **0**.
- `P2Goal.verify.lean.log`: no errors, 11 nonfatal linter/deprecation warnings.
- 12 requested `#print axioms` commands matched 12 fresh dependency records, in order. Every record contains only `propext`, `Classical.choice`, `Quot.sound`.
- Original, verification copy, and `AHP/round13/shared/assembly/R2_P2Goal.lean` are byte-identical (11120 lines).
- SHA-256 of each source: `da1b94df5c82e075316f3a90cba1086643e9174f19ed7963c850e975952334ef`.
- Imports: only `DrEquiv` and `DrPath3`.

No `lake build`, historical recompilation, or modification of the submitted certificate was performed.

## Exact theorem and quantifier audit

Fresh `#check @...` output confirms that `rightStar_kernelLine` (line 11050), using the source's original opens, has precisely:

```lean
∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →
  0 < vacEdge q R (rightStar hq R) ∧
  vacEdge q R (rightStar hq R) < Real.pi/2 ∧
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    Module.finrank ℝ (vacA q R (rightStar hq R) 1
      (vacEdge q R (rightStar hq R))).ker = 2
```

There are no additional implicit section hypotheses. `KernelLine` is the original whole-carrier statement: a nonzero canonical-crossing kernel vector, the quarter-gauge square identity, and containment of **every** kernel vector in the real span of that vector and its quarter-gauge rotation. It is not a restricted-sector kernel assertion.

The nested cofinal assertion is a **separate theorem**, `cofinal_rightStar_kernelLine` (line 11061), also checked in the fresh log:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  0 < vacEdge (2^j) R (rightStar (by positivity) R) ∧
  vacEdge (2^j) R (rightStar (by positivity) R) < Real.pi/2 ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    Module.finrank ℝ (vacA (2^j) R (rightStar (by positivity) R) 1
      (vacEdge (2^j) R (rightStar (by positivity) R))).ker = 2
```

The proof chooses `j = j₀` and `R = 2*(R₀+18)`. Quantifier order is preserved. Neither crossing theorem asserts detection.

The conditional final-goal claim is also a **separate theorem**. Fresh elaborated output is exactly:

```lean
AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3 :
  AdalyFormal.Round13.Assembly.R1.P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2

AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3 :
  AdalyFormal.Round13.Assembly.R2.CofinalP3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2
```

Thus P3 is the sole hypothesis of `goalNeg2_of_P3`; P1, P2, regularity, continuity, positive start, and gauge facts are not remaining hypotheses. The fresh file also checks the original `CofinalAnyPathNoResponseCancellation → GoalNeg2` bridge. These conditional implications do not establish their premises.

## Provenance and statement fidelity

Read-only checks were rerun against actual current files, rather than trusting `AUDIT.json`:

- All **763** named declaration chunks in the verification copy match their manifest source line ranges and SHA-256 hashes exactly. Coverage is complete: no extra or duplicate parsed declaration names, and every manifest body equals the corresponding copied declaration body, not merely some substring.
- Sources: 503 chunks from `assembly/r1/RepairedJoin.lean`; 186 from `shared/assembly/R1_P1Spine.lean`; 2 from `GoalAppendix.lean.txt`; 63 from `shared/positivity/R2_P2.lean`; 9 from `P2Appendix.lean.txt`.
- All **30** declarations shared with `AHP/round3/guarded/pin/Statement.lean` match verbatim, including the selectors, physical data/form definitions, guarded target, and `GoalPos2`/`GoalNeg2`. In particular, `GoalNeg2 := ¬ GoalPos2` and `GoalPos2 := P428Target8SG selAll selAll` are unchanged.
- `vacA`, `vacEdge`, `KernelLine`, `CurlDetected`, `NoResponseCancellation`, and `CofinalAnyPathNoResponseCancellation` also match their original declarations in `AHP/round10/shared/assembly/R4_ResponseHull.lean` verbatim.
- P1, P2, P3, `CofinalP2P3`, and its response-noncancellation bridge match the R1 spine verbatim.
- The bodies of P1–P3 match the three exact physical statements in `AHP/round12/shared/GAPS.md`, normalizing whitespace only and omitting the Markdown explanatory comments. In particular, P2 includes every actual nonzero carrier field with zero central charged coordinate, on the entire open interval, for every positive q and even R ≥ 18.

## Forbidden mechanisms

No forbidden-token occurrence was found in the raw verification source for `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque` (whole tokens). A comment/string-masked executable scan additionally found no `sorryAx`, `ofReduceBool`, `trustCompiler`, custom macro/elaborator/initialization commands, or `#eval`/`#reduce`. Options are resource, pretty-printing, auto-implicit, or linter settings; no trust bypass was found.

## Acceptance boundary

Accept the mathematical progress and exact P2 proof. Do **not** accept the selected main declaration as one of the explicitly permitted final/physical target types, and do not mark GoalNeg2 closed. The minimal metadata correction is `mainDeclaration = AdalyFormal.Round13.Assembly.R2.p2`, with a P2 closure claim and the crossing/conditional-goal results listed as additional verified consequences.

Only the requested verification copy, its compiler-generated `.log`/`.exit`, and this report were created by this verification. Historical and submitted source files were not edited.

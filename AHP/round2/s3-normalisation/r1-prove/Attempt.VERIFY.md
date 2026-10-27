# Independent verification — S-3, round 1, prove

**Verdict: `closes-goal`.** The unchanged attempt proves the exact pinned `AdalyFormal.Round2.S3Pin.GoalPos1`. Its second positive goal also passes. This is closure of the pinned, guarded first-summand comparison, not certification of the whole printed coercivity statement or every obligation in OPEN_ITEMS S-3.

## 1. Independent compilation

Executed on 2026-10-21 from the existing frozen project:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s3-normalisation/r1-prove/Attempt.lean > ../AHP/round2/s3-normalisation/r1-prove/Attempt.verify.log 2>&1
rc=$?
echo "$rc" > ../AHP/round2/s3-normalisation/r1-prove/Attempt.verify.exit
```

**Independent exit: 0.** The complete log has **59 axiom records, 27 nonfatal warnings, and no errors**. All records contain exactly `propext`, `Classical.choice`, `Quot.sound`. These are newly measured results, not copied from the attempt report.

Infrastructure history: an initial streamed command ended while waiting for a heavy slot, without producing an exit record. A subsequent persistent-terminal run was interrupted by a daemon disconnect, also without a Lean exit record; its partial output is retained as `Attempt.verify.interrupted.log`. Neither was counted as a successful or completed Lean run. The final retry completed normally in a persistent terminal, with both terminal process exit 0 and the explicit `.verify.exit` file containing 0. The complete final `.verify.log` supersedes the interrupted evidence.

No build, reproduction script, dependency update, numerical operator experiment, commit, or push was run. The attempt and pin were not edited.

## 2. Exact statement and definition identity

| Check | Independent result |
|---|---|
| Main declaration | `AdalyFormal.Round2.S3Pin.goalPos1_proved`, `Attempt.lean:822` |
| Explicit declaration type | Exactly `GoalPos1` in namespace `AdalyFormal.Round2.S3Pin` |
| Pinned goal | `pin/Statement.lean:283–286`, copied unchanged at the same lines in the attempt |
| Copied definitions | **All match**: the entire 16,414-byte, 357-line pin is a byte-identical prefix of the attempt, stronger than whitespace-normalized equality |
| Context | No enclosing `variable` declarations, local goal aliases, replacement notation, or extra theorem hypotheses; the appended proof reopens the same namespace |
| Imports | Sole import `ZT5A`, a frozen module; no AHP import |
| Additional result | `goalPos2_proved : GoalPos2`, `Attempt.lean:831`, also compiled and audited |

The exact primary proposition remains:

```lean
∀ P : IngrBParams, AdmissibleConfiguration P → InversesExist P .plainH →
  ∀ B : UnitB P, AdmissibleB P B →
    GenP.firstTerm P B = PrintedFirstTerm P .plainH B
```

The type check here is the successful recompilation of the explicitly typed declaration, together with a source/context audit establishing that its `GoalPos1` resolves to the unchanged pin. No standalone elaborated-type dump was generated, and none is claimed. The goal is not merely a similar inequality, an implication with extra hypotheses, or a depth-one specialization.

The proof at line 822 invokes the stronger `firstTerm_eq_printed` at line 816: it needs only the pinned inverse guard, not `AdmissibleConfiguration` or `AdmissibleB`. In particular, the proof does not derive a contradiction from the configuration/test predicates to make the result vacuous. This observation is not an independent inhabitation theorem for the inverse guards.

The two reused generic inverse lemmas at lines 374–383 were also checked against `lean/src/NsCvOS4.lean:16–18,35–40`; their declaration/proof text is unchanged apart from the enclosing namespace and added explanatory comments.

## 3. Dependencies and forbidden constructs

The final log contains, verbatim:

```text
'AdalyFormal.Round2.S3Pin.goalPos1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round2.S3Pin.goalPos2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All **59/59** source `#print axioms` commands have matching log records; none is missing or unexpected. All **44/44** appended declarations have prints. Every record uses only the permitted three axioms.

A whole-file, raw-text word-token scan of `Attempt.lean` found **zero** occurrences of `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, or `opaque`. Thus no comment/string stripping is needed to obtain a clean scan. Manual review also found no added metaprogram, custom elaborator, unchecked evaluator, or kernel-check-disabling option. The resource options only raise elaboration limits. This is an audit of this attempt and its reported theorem dependencies, not a new raw-source audit of every imported module.

Reproducible static checker: `VerifyAudit.py`; measured output: `Attempt.verify.audit.json`. The checker is a text/log audit, not a numerical operator model. Its initial parser missed the trailing apostrophe in `inverse_smul'`; correcting the record-name parser produced the full 59-record accounting above. No Lean source was changed to fix that verifier-side issue.

## 4. Proof mechanism checked

The appended argument does the substantive normalization work rather than defining the printed answer to equal the frozen answer:

- Lines 443–460 compare the padded Dirichlet inverses on their supported solutions. They do **not** incorrectly scale the identity padding outside the domain.
- Lines 475–499 account for both rescaled inputs of the genuine quadratic jet. The plain-H coefficient is uniformly eta times the frozen coefficient at every level.
- Lines 533–664 compare Q, its weighted adjoint, the mass, G, H, and the actual background-derived J.
- Lines 674–720 identify the quadratic form and symmetric G1 inverse, using the frozen symmetric-form specification rather than substituting an arbitrary matrix.
- Lines 722–757 compare the full multilevel constraint inverse with the level metric still present.
- Lines 760–813 prove the explicit insertion equals tau-star without a full-support assumption.
- Lines 502–531 and 827–831 handle the two linked H/C conventions, including their guards, so the alternative representation is not silently substituted for the primary one.

Writing \(W_F=\operatorname{diag}((\ell^j\eta)^3)\), the decisive relations are

\[
N_{\mathrm{phys}}=\eta^{-1}N_{\mathrm{body}}W_F,
\qquad
W_F N_{\mathrm{phys}}^{-1}f=\eta N_{\mathrm{body}}^{-1}f.
\]

The physical pairing therefore produces the frozen external eta; the separately proved insertion identity accounts for tau-star. The inverse is always taken on the whole multilevel space before evaluating it on the inserted unit field. There is no inverse-of-compression/compression-of-inverse interchange.

## 5. Printed-source faithfulness and remaining scope

Read `HANDOFF.md`, the requested OPEN_ITEMS sections, the Stage-B report, the earlier S-3 design/attack/decision and structural comparison, and the current pin/attempt notes and definitions. Read the corpus page transcriptions for pp.392–396 and 419–428. Directly inspected the pin's page images for pp.392,393,394,419,420,421,422,428, including all the requested equation loci. Page/line citations below refer to `sources/corpus/pages/CMP99b_pNNN.md`; the equation numbers identify the image loci independently.

### Supported normalization reading

I found **no new scale contradiction in the supported first-term reading**:

- p.392 (3.8), (3.10), (3.11): inverse-mesh differences, normalized trace and the fine volume factor are present.
- p.393:28, (3.14): the argument really is \(C_j(U,L^j\eta A)\). Its quadratic argument rescaling cannot be omitted. With the raw quadratic coefficient, this gives \(C_j^{(2)}(A)=\ell^{-2j}\mathrm{raw}_j(A)\).
- p.421:28 explicitly offers plain H with \(L^j\eta C_j^{(2)}(A)\), or the linked dimensionless-H representation. The pin tracks both changes together. This corrects the superseded Stage-A `eta² raw` plain-H recipe, rather than confirming its claimed counterexample.
- p.394 (3.24) uses recursive site coefficients; p.393 (3.16) uses constant a for the bond mass. The pin distinguishes them.
- p.419 (3.119), p.420 (3.122)/(3.126), and p.421 (3.128)/(3.129) support the inverse-chain assembly being compared.
- p.422:92, (3.136), has the level factor with exponent d+1. It corroborates the level-volume/extra-C-factor bookkeeping, not an independent factor to insert a second time.
- p.428:32–43, (3.156)/(3.157), has neither an external eta nor tau. The top-level insertion and weighted inverse comparison explain their frozen counterparts under the pinned dictionary; (3.157) does not license inverting a top compression.

### Ways the pin is narrower than broader printed-fidelity claims

1. **Only the first summand is the target.** OPEN_ITEMS S-3 also asks for common units of the mass subtraction, final nonlinear J term, and `bondEnergy`. `GoalPos1` contains none of those comparisons. The mass and J identities *inside the G1 construction* are not a comparison of the other summands of (3.156). Closure here must not be reported as full term-by-term S-3 closure.
2. **Inverse existence is assumed, not obtained from printed small-field regularity.** `InversesExist` at pin line 273 guards both versions of every inverse used by this construction. Neither a threshold theorem nor positivity nor a nonempty guarded example is part of the positive goal. The print's analytic existence assertions, e.g. pp.395,423,428, are not established by this algebraic identity.
3. **The localization convention is retained, not resolved.** `PrintedDelta` and `PrintedJ` retain `plaqIn`, while bonds use the frozen touching selectors. The print's plaquette sums and Dirichlet prose do not themselves identify that mixed convention. Calling this side “Printed” means the pinned scale reading on the frozen S-1 localization, not a theorem about fully consistent touching operators.
4. **The class/geometry is still the encoded specialization.** Dimension 3, SU(2), finite periodic rectangular tori, aligned half-open blocks, periodic l1 distance, natural radii, padding, factor-12 boxes and the frozen coverage clauses are retained. The p.394 thinner operator-domain option is not independently treated; the p.396 per-cube class is not proved identical to `ClassCoupled`. R at least 18 is an encoded regime, not a printed optimal threshold. The stronger proof's independence from class assumptions does not identify those conventions with the source.
5. **Primitive source identification remains inherited.** The pin shares `QfullOf`, `D2B`, the background tower and componentwise jets with the frozen implementation. Equations (3.13)–(3.15) refer to nonlinear averaging primitives from another paper. This proof checks scaling of those implemented primitives, not a new theorem identifying every primitive with the printed analytic averaging map on the full printed class. In particular, `ZXR2Sector.lean:66–68,92–94` gives bridges to whole-composite jets under a regular-tower hypothesis; the pin does not newly discharge such source-identification obligations.
6. **Pairing and field-coordinate conventions are fixed interpretations.** The level metric, physical numerical field coordinates in the skew-Hermitian chart, and top-level insertion are explicitly pinned. The source supports this dictionary, but the formal theorem compares these definitions rather than proving a proposition about printed notation. The general-support insertion theorem establishes the adjoint of the encoded extraction; it does not independently translate all geometric bond-domain conventions.
7. **No C-parametrization or covariance theorem follows here.** The source after (3.156) imposes support, axial and global Q1 constraints and then uses C in (3.157). The pin includes a chosen realization of that subspace but no theorem identifying every frozen `Cop` output with it or reconstructing the Gaussian covariance. The stronger all-B first-term equality removes the need for those constraints *for this equality*, not for the rest of the printed coercivity argument.

These are disclosed scope boundaries, not failures of conditions (1)–(4). For the round-two request specifically restricted to the supported first-term normalization, the exact equality with scalar 1 is established. For the broader OPEN_ITEMS S-3 checklist, the other-term and inherited source-fidelity obligations remain.

## 6. Artifact identity and final disposition

- Pin SHA-256: `9133de3969b6a26d2f6c373d4bb56c1d0ce6d545bd161b69a851e6af2416962c`.
- Attempt SHA-256, unchanged from the first static check through the completed recompile: `67908d7b3f5a0b882fdbf32376f130e800709d78e1747b43ad6cfaa116d5aa47`.
- Complete independent log SHA-256: `5c6c392d4679225a0cbaf8165cd390e9c92b79bbb2bfb93f332214d998622d99`.

Only verification artifacts under `AHP/round2/s3-normalisation/r1-prove/` were written: this report, the independent log/exit, the retained interrupted log, and the static audit script/JSON. Protected sources, manuscript files, the pin, and the attempt remain untouched by this verifier.

**Accept `goalPos1_proved : GoalPos1`, and also `goalPos2_proved : GoalPos2`, at exactly the scoped meaning above.**

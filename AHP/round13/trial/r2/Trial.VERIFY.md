# Independent verification — trial R2

**PASS: exact P1, with the complete cofinal path/trial handoff.** This is not a proof of P2, P3, response noncancellation, or `GoalNeg2`.

## Fresh compilation

Copied `AHP/round13/trial/r2/Trial.lean` without alteration to `AHP/round13/trial/r2/Trial.verify.lean`, then ran exactly once:

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round13/trial/r2/Trial.verify.lean
```

- Fresh `Trial.verify.lean.exit`: **0**.
- Fresh log: no errors; six harmless linter warnings (two unused simp arguments and four proposition-binder-name warnings).
- No timeout, relaunch, or `lake build` occurred.
- All 2,387 lines of the verification copy, local source, and `AHP/round13/shared/trial/R2_Trial.lean` are byte-identical.
- Source SHA-256: `01279668c4d8cc5c5c42e41963a9857fb2f8e69f1b195c88872e197211c86db8`.
- Fresh verification-log SHA-256: `64b3f7405696ea2e6aa4c6fafddbfaced55002358766fa364cc874eef4fab5b4`.

## Exact type and absence of extra hypotheses

At lines 2335–2340, `AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi` has the explicit compiled type:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

Its type text equals the first physical proposition (P1) in `AHP/round12/shared/GAPS.md`, under “Exact remaining physical statements for one consistently RIGHT star”, after whitespace removal. Its proof is the retained `AdalyFormal.Round13.Trial.rightStar_negative_halfpi`.

The appendix namespace has no section variables, included assumptions, instances, or custom notation; `autoImplicit` is false. All earlier parameterized sections/namespaces are closed. The identifiers resolve to the original copied interfaces:

- `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace`;
- `AdalyFormal.Round9.Guarded.Qualitative.vacA`;
- `AdalyFormal.Round12.Noncancel.RightFamily.rightStar`.

There are no extra physical, spectral, numerical, or regularity hypotheses. In particular, `vacA_rightStar` retains the actual all-plaquette `D1Literal.dataS` operator identification, and the inherited `trial_carrier_energy` proves energy `-1/4` for the physical trial, not a replacement matrix.

The pinned `AHP/round3/guarded/pin/Statement.lean` defines `GoalNeg2 := ¬ GoalPos2`, with `GoalPos2 := P428Target8SG selAll selAll`. P1 is distinct from that target and is accepted under the user's explicit P1–P3 alternative. This certificate supplies no P1-alone bridge to `GoalNeg2`, nor claims one.

## Verbatim source checks

Independent read-only byte/hash assertions establish:

1. The first **105,778 bytes / 2,298 lines** equal the independently accepted R1 source, its published source, and its independent verification copy. Their common SHA-256 remains `65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b`.
2. The remaining appendix equals both local `HandoffBody.lean.txt` and published `R2_HandoffBody.lean.txt`, with SHA-256 `c0c9f3c0df0f47ffab1f93b4945e09871e141a7a4a5ca4f9023f6db1441299b7`.
3. All five inherited interface fragments equal their actual source bytes, including declaration bodies and whitespace. Complete source hashes and fragment hashes agree with the inherited manifest:

| Source under `AHP/round12/shared/` | Destination first line | Bytes checked |
|---|---:|---:|
| `noncancel/R2_RightFamily.lean` | 1 | 30,535 |
| `noncancel/R2_Boundary.lean` | 695 | 5,779 |
| `noncancel/R2_Mass.lean` | 830 | 4,126 |
| `noncancel/R2_StarLocal.lean` | 921 | 13,490 |
| `kernel/R2_FirstCrossing.lean` | 1227 | 739 |

4. The operative pin fragment from `PlaqSel` through `dataS_laws` also matches `AHP/round3/guarded/pin/Statement.lean` verbatim (1,800 bytes).

**Nonblocking inherited manifest metadata discrepancy:** the fifth entry's `source_last_line` is 992, but its 739-byte fragment extends through the namespace-closing text on line **993**, excluding that line's trailing newline. An initial inclusive-line-range assertion exposed this discrepancy. Direct comparison using the recorded source start and byte length confirms that the entire fragment, including the closing namespace, is verbatim and has the recorded hash. No definition differs. The inherited manifest was not edited.

No builder audit script was executed: it would overwrite files outside this verification's write scope. Assertions were independently executed in memory.

## Dependencies and forbidden mechanisms

All **201** `#print axioms` commands are accounted for by corresponding records in the fresh log, including multiline lists. Every dependency list is a subset of `{propext, Classical.choice, Quot.sound}`. Records cover all **91** distinct inherited trial declarations and all **six** R2 declarations. The main record is:

```text
'AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Whole-source scanning found none of: `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, `run_tac`, `run_elab`, `elab`, `macro`, `syntax`, or `initialize`. No instance/notation/attribute overrides occur. Options only disable automatic implicit parameters and raise heartbeat/recursion limits. The only import is `DrEquiv`. The log contains no `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler` dependency.

## R2 handoff and scope

The fresh compile checks all six added declarations:

- `trialVector_norm_sq`: actual norm squared `21/16`;
- `trialVector_ne_zero`: nonzero explicit trial;
- `trial_rayleigh`: actual half-pi Rayleigh quotient `-4/21`;
- `rightStar_negative_halfpi`: exact P1;
- `rightStar_physical_halfpi`: path continuity/analyticity/identity start, negative pi endpoint, and explicit half-pi trial facts at any admissible selected indices;
- `cofinal_rightStar_paths_halfpi`: the original nested scale/radius quantifier order, choosing `j = j₀` and `R = 2*(R₀+18)`, with all path clauses and half-pi trial facts at those same indices.

The last theorem does not intersect unrelated cofinal subsequences. Its pi and half-pi vectors need not coincide; their path, scale, and radius do. Its conclusion contains neither `KernelLine` nor `CurlDetected`. The Rayleigh quotient is not asserted to be an eigenvalue or a crossing value.

**Remaining:** P2, P3, whole-kernel line construction, cofinal response noncancellation, and `GoalNeg2` are not established by this certificate. This replay used the existing frozen `DrEquiv` import environment; it did not rebuild imported libraries or verify downstream historical assembly.

Only the requested verification copy and this report were authored. The prescribed wrapper generated the copy's `.log` and `.exit`. Original/shared certificates, builder audits/notes, and R1 verification artifacts were left unchanged.

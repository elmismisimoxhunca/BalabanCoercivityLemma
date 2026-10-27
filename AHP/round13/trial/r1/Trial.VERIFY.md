# Independent verification — trial R1

**PASS: P1 only.** `AdalyFormal.Round13.Trial.rightStar_negative_halfpi` proves the exact first physical statement in `AHP/round12/shared/GAPS.md`, under “Exact remaining physical statements for one consistently RIGHT star”. It is not a proof of `GoalNeg2`.

## Fresh compilation

Copied `Trial.lean` to `Trial.verify.lean` without alterations or appended declarations, then executed once:

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round13/trial/r1/Trial.verify.lean
```

- Fresh `Trial.verify.lean.exit`: **0**.
- Fresh `Trial.verify.lean.log`: no errors; four harmless linter warnings (two unused simp arguments and the names of two proposition binders).
- No timeout, relaunch, or `lake build` was needed.
- The 2,298-line verification copy, original, and `AHP/round13/shared/trial/R1_Trial.lean` are byte-identical.
- Source SHA-256: `65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b`.
- Fresh verification-log SHA-256: `66174f888fa524b06216877ff40e206d3c98c7d1ce7ed8e12a783861f948ed96`.

## Exact type and assumptions

The compiled declaration at lines 2180–2185 has the explicit type:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

Its type text equals P1 in `GAPS.md` after whitespace removal. The declaration has no preceding parameters; its namespace blocks introduce no section variables, included hypotheses, replacement instances, or custom notation. `autoImplicit` is false. The identifiers resolve to:

- `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace`;
- `AdalyFormal.Round9.Guarded.Qualitative.vacA`;
- `AdalyFormal.Round12.Noncancel.RightFamily.rightStar`.

These are the copied historical interfaces, not similarly shaped replacement operators. The witness is `trialVector hq R`; the proof uses `trial_carrier_energy`, which establishes actual carrier energy `-1/4` with only the same three hypotheses. `vacA_rightStar` identifies the operator with the original all-plaquette `D1Literal.dataS` carrier.

The pinned `AHP/round3/guarded/pin/Statement.lean` defines `GoalNeg2` as the negation of `P428Target8SG selAll selAll`. P1 is a distinct, explicitly permitted verification target; this certificate neither asserts nor supplies a P1-alone bridge to that goal. No additional compiled bridge is required for acceptance under the user's P1–P3 alternative.

## Verbatim-copy checks

Independently compared actual source bytes against the verification copy at the recorded source/destination starts, checking both complete source hashes and fragment hashes from `COPIES.json`. All five fragments match verbatim:

| Source under `AHP/round12/shared/` | Destination first line | Bytes checked |
|---|---:|---:|
| `noncancel/R2_RightFamily.lean` (entire file) | 1 | 30,535 |
| `noncancel/R2_Boundary.lean` (without repeated import) | 695 | 5,779 |
| `noncancel/R2_Mass.lean` (without repeated import) | 830 | 4,126 |
| `noncancel/R2_StarLocal.lean` (copied prefix without repeated import) | 921 | 13,490 |
| `kernel/R2_FirstCrossing.lean` (original `TwistSpace` namespace block) | 1227 | 739 |

These checks cover every declaration in the copied interfaces, including their bodies and whitespace. Additionally, the operative pin fragment from `PlaqSel` through `dataS_laws` was compared directly with `AHP/round3/guarded/pin/Statement.lean` and matches verbatim. No builder audit was executed, since it would overwrite `AUDIT.json`; verification used independent read-only assertions.

## Dependencies and forbidden mechanisms

All **195** `#print axioms` commands have corresponding parsed records in the fresh log, including multiline lists. Every list is a subset of `{propext, Classical.choice, Quot.sound}`. All **91** distinct new trial declarations have dependency records. The main record is:

```text
'AdalyFormal.Round13.Trial.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The only import is `DrEquiv`. Whole-source scanning found none of these forbidden tokens/mechanisms: `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, `run_tac`, `run_elab`, `elab`, `macro`, `syntax`, or `initialize`. No notation/attribute/compiler/trust-level alterations occur. The fresh log contains no `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler` dependency. Ordinary kernel-checked `decide` is used, not native evaluation as proof.

## Scope and remaining work

P1 is independently verified. P2, P3, canonical crossing/kernel-line construction, response noncancellation, and the downstream `GoalNeg2` integration are **not established by this certificate**. This verification compiled against the existing frozen `DrEquiv` import environment; it did not rebuild the imported library or repair historical joins.

Only the requested verification copy and this report were authored; the prescribed compiler wrapper generated the copy's `.log` and `.exit` files. Original/shared certificates and builder notes/audits were left unchanged.

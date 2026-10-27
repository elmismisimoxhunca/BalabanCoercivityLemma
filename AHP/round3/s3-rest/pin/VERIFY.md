# S3-rest pin verification

**2026-10-21: compiled successfully, exit 0. Pinning complete; no open goal proved or refuted.**

## Command and evidence

Only the authorized wrapper was used:

```sh
AHP/round3/lean1.sh AHP/round3/s3-rest/pin/Statement.lean
```

The final invocation ran in a persistent BB terminal to survive tool wait timeouts. Its wrapper-produced `Statement.lean.exit` contains `0`, is newer than the source, and its `Statement.lean.log` contains the complete requested output. The terminal has exited; no compilation remains running for this item. An earlier streamed invocation was interrupted without an exit record; it is not counted as evidence. There was also a successful intermediate run before enabling fully qualified axiom names. Only the final current-source log is used below.

No direct build, reproduction, dependency update, or compiler invocation outside the wrapper was run.

## Measured checks

- Source: **575 lines**, sole import **`ZT5A`**.
- **4** new proposition definitions: `GoalPos1`, `GoalPos2`, `GoalNeg1`, `GoalNeg2`.
- **14** `#check` commands.
- **23/23** requested dependency records present; **0 errors, 0 warnings**.
- Every dependency record lists exactly **`propext`, `Classical.choice`, `Quot.sound`**.
- Raw word-token scan of the source found **0** occurrences of the prohibited constructs, including the prohibited implementation attributes and opaque stand-ins.
- The block from `abbrev Fine` through `InversesExist`, including definitions of the actual geometry/test/guard predicates, is **byte-identical** to the corresponding round-two pin block after trimming trailing whitespace at the block boundary. Original namespace retained. No AHP import.
- No numerical script or numerical operator model was run.

The printed goals are definitions of propositions, **not proofs of them**. The only new proved propositions are positivity of the explicit constant 1 and the three negative-contract helpers. In particular:

```text
'AdalyFormal.Round3.S3Rest.GoalNeg1_implies_not_GoalPos1' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round3.S3Rest.GoalNeg2_implies_not_GoalPos2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Actual statement audit

- Positive goals retain exactly `AdmissibleConfiguration` and `InversesExist` from round two. They quantify both linked H/C readings and all depths admitted by that configuration predicate, and include the whole frozen/printed instance equivalence with gamma unchanged.
- Printed mass and energy use the unit pairing, not the fine pairing. The final nonlinear term uses the fine pairing and physical J.
- H1 is rebuilt from the physical G1, Q-adjoint and full constraint inverse; Dtilde is rebuilt from the actual raw unit jet and corridor inverse. It is not defined by rescaling the frozen output being compared.
- The raw and normalized constraint branches scale the linear part and quadratic remainder **together**.
- Negative goals require actual configurations at depth >= 2, nonzero admitted test fields, genuine background-derived jets/source, nonsingular corridor inverses, and unequal nonzero-denominator ratios. The compiled helpers prove they imply the corresponding positive goal's negation.
- `NoGammaMassRepair` is a distinct, stronger requirement: ratio disagreement is not misrepresented as proving aggregate inequality non-equivalence. It changes the actual a parameter everywhere and excludes singular rescaled instances.
- `PIN.md` discloses CMP99b's incomplete Dtilde specification, the independently inspected CMP109 p.267 supplement, all retained geometric/operator conventions, the totalized-extension scope of the stronger positive goals, and the unproved support/global-Q1 and analytic-existence obligations.

## Hashes

```text
799b0124e2075c575d18c83c68af06e8501f6ee50f9d88b57647d8c2deb9ab3b  Statement.lean
c68441f2f42db45e40fa7a39dea3a2120ab1d694264adb86997f36f51a1d4b42  Statement.lean.log
a45478992e10fa4fa01ede73529acb058b44ef90b3e65802aba5f4bab35b5976  renders/CMP109_p267.png
924444cf60b653acf56cd0bc7f9b5bdc78597f97e8f4f53210a49ead2fe66a9b  sources/compute/balaban_su2_papers/balaban_CMP109_1987_RGapproach_I.pdf
```

The PDF is read-only source evidence, not a generated artifact. All created task files are under `AHP/round3/s3-rest/pin/`. Protected files and other workers' files were not edited. No commit or push.

**Remaining work:** prove a new positive goal or construct a genuine strong negative witness; review acceptance of the CMP109-to-CMP99b unit-correction dictionary. Successful pin compilation alone does not close S-3.

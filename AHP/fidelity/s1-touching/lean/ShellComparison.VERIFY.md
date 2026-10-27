# Independent verification — Stage B entry 3 (s1-touching)

**Verdict: accept**, at the structural-comparison scope specified in `DECISION.md`. All seven required declarations pass; none are missing or failed.

## Independent compilation

The coordinator supplied the required fresh reproduction-gate confirmation. The verifier did not run `REPRODUCE.sh` or `lake build` and did not edit `ShellComparison.lean`.

Executed from the existing project:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/fidelity/s1-touching/lean/ShellComparison.lean > ../AHP/fidelity/s1-touching/lean/ShellComparison.verify.log 2>&1
rc=$?
printf '%s\n' "$rc" > ../AHP/fidelity/s1-touching/lean/ShellComparison.verify.exit
```

Independent exit status: **0**. Complete output: `ShellComparison.verify.log`; exit record: `ShellComparison.verify.exit`. The builder's log and exit record were not overwritten.

Verified source SHA-256:

```text
358c72f814cb755a50659c55603b9ef4d6faddfeafc10fddc3d2c388366923b8
```

## Declaration checks

Every name below has the prefix `Fidelity.S1.`. Each required `#print axioms` command is present outside the namespace, in the order prescribed by `STAGE_B.md`, and has its own corresponding output line. Every line lists exactly `propext, Classical.choice, Quot.sound`.

| Declaration | Exact contract signature | Independent axiom check |
|---|---|---|
| `cubeBond_readBond` | pass | pass |
| `perCubeRegularShell_toFrozen` | pass | pass |
| `classCoupledShell_toFrozen` | pass | pass |
| `classCoupledShell_one` | pass | pass |
| `shell_slab_nonvacuous` | pass | pass |
| `readBond_not_touchBond_slab6` | pass | pass |
| `no_plaqIn_eq_plaqCorner_slab6` | pass | pass |

All seven source signatures match their decision code blocks exactly after whitespace normalization, including binder kinds, binder order, hypotheses, qualifications, and conclusions. There are no surrounding section-variable hypotheses or local notation changes. The full source was inspected: no weakened statements, alternate declarations, or shadow definitions were introduced.

The six authorized shell definitions (`TouchBond`, `plaqCorner`, `ReadBond`, `CurlReadsRead`, `PerCubeRegularShell`, `ClassCoupledShell`) match SPEC exactly after whitespace normalization. `L6` and `slab6` match DECISION exactly. Imports, explicit opens, and namespace match the decision. Coverage, cube sites, admissibility, and Lambda predicates are imported rather than redefined. Frozen declarations were located under `lean/src/`, not the obsolete assumed root paths.

A whole-file token scan found none of: `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`. The permitted `#print axioms` commands are not axiom declarations. The file contains no extra proof helpers requiring separate checks; local proof steps are included in the checked theorem dependencies.

The regularity transfer handles pointwise, forward-difference, and all curl guards. The slab theorem proves coverage and proper/nonempty geometry from the frozen slab-family results rather than assuming them. Both selector-separation results use kernel-checked finite geometry, not external numerical output.

## Scope

Accepted: the seven structural comparisons, flat proper-domain hypothesis-family witness, and geometric separators only. The original S-1 reading and shell coercivity remain open. This verification does not certify the printed headline, corner-operator positivity, non-flat richness, or any coercivity implication.

Only verification artifacts under `AHP/fidelity/s1-touching/lean/` were written.

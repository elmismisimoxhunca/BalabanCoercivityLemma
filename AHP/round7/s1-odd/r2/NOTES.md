# S1-odd attack, round 2

## Result

**Both exact pinned goals compile**, for every natural \(\ell\ge2\) and every real \(0<a<4\), hence also for every odd \(\ell>11\) in that mass window.

| Declaration | Location | Type |
|---|---|---|
| `Round7.S1Odd.not_touchFour_every_ell` | `Attempt.lean:422` | Arbitrary fixed-ell, fixed-a slice negation |
| `Round7.S1Odd.goal1_proved` | `Attempt.lean:477` | Exactly `Round7.S1Odd.Goal1` |
| `Round7.S1Odd.goal2_proved` | `Attempt.lean:480` | Exactly `Round7.S1Odd.Goal2` |

There is no additional hypothesis on either goal theorem. In particular this is not just the old headline negation instantiated at ell = 2. The range \(a\ge4\) remains unproved; no sharpness claim is made.

## What changed from round 1

The previous independent replay timed out, leaving no exit evidence; its verdict did not identify a mathematical or elaboration error. This pass therefore copied the complete round-1 source byte-for-byte to the requested `r2/Attempt.lean`, rather than changing a working proof or a pinned goal. It performed a fresh round-2 wrapper compilation with a **2400-second bash timeout budget**, which returned normally. It did not relaunch the interrupted round-1 replay, overwrite its artifacts, or fabricate an exit record.

Only `AHP/round7/s1-odd/r2/` was written. New artifacts are the attempt, wrapper log/exit, `audit.py`, `AUDIT.json`, and these notes. No numerics, deletion, direct Lean/Lake command, build, reproduction script, dependency update, commit, push, protected-tree edit, or terminal was used.

## Pin and copy integrity

- `../pin/Statement.lean` and `../pin/PIN.md` were not changed.
- The entire round-3 pin is still an exact byte prefix of the round-7 pin.
- All 7,926 bytes of the round-7 pin are unchanged in `Attempt.lean`, at byte offset **29**, after the two frozen import lines `import D1Final` and `import GdPlaq`. This retains the previously audited layout: the pin is the first declaration block, **not literally the file's byte-zero prefix**. Lean requires the additional imports before declarations. The pin's own `import D1Lit` remains intact. No AHP module is imported.
- The entire round-3 helper block, from `/-! ## Locality: corner and all selectors` to immediately before `/-- Exact pinned negative goal.`, is copied verbatim.
- `headline_iff_slices` at line 415 is proved by `Iff.rfl`. The source audit also compares the expanded slice body with the old headline after removing only its outer ell/hell/a/positivity binders. All remaining thresholds, side conditions, field hypotheses, class definitions and actual operators are unchanged.
- Every one of the 30 local definitions/theorems has a dependency print. There are also prints for 21 frozen helpers, checking their full dependency cones.

## Mathematical audit

The proof follows the general-ell family behind `lean/src/D1PGen.lean:24`, read through `D1Cons`, `D1Final`, `D1Main`, `NV6` and `NV7`, together with `D1Collapse`. It does not infer the new result from a theorem about a different class.

Given supposed slice thresholds, set \(m=m_0\), \(M=\ell^{m_0}\), and \(R=\max(R_0,18)\). Then \(\ell\mid M\), \(M\ge\ell\), and \(RM\ge17\ell\). The radius is chosen before receiving the positive cap and coercivity constant. The depth-two `SlabNv` has actual admissibility, torus/Lambda compatibility and factor-12 coverage. `SlabNv_bdpt` supplies an inside site with an outside neighbor, so its base is proper and nonempty.

The copied transverse-slab argument upgrades coverage to `CoversPlaqFour`. The exterior path `Uth` is identity on all endpoint-touching bonds, so the zero logarithm gives all three strict touching-regularity bounds for every positive smallness parameter. The copied W-sandwiched, Dirichlet-compressed corner/all-carrier identity transfers the genuine non-unit crossing to the corner carrier. This is not a comparison with the frozen inside selector, nor an identification of every J operator.

Choose \(\alpha_0=\tfrac12\min(a_0/(12M),1)\). It is positive and obeys the exact cap. `BseedNv_props` supplies the genuine constrained competitor and positive energy for symbolic ell, with no parity assumption. At the singular carrier, `not_InstIneqS_of_not_unit` contradicts the complete selected inequality for every positive coercivity constant. The `SidePow6` conjunct is discarded because the analytic conclusion itself contradicts the witness; failure is not obtained from a side-condition obstruction.

The mass window comes from `D1Main.Fth_pi_neg`: the boundary contribution is \(-4\langle X,X\rangle\) and the positive mass contribution is at most \(a\langle X,X\rangle\). The negative endpoint and the intermediate singular configuration are different points. Indefiniteness is not equated with singularity.

## Fresh evidence

Run directly in bash:

```sh
AHP/round3/lean1.sh AHP/round7/s1-odd/r2/Attempt.lean
python3 AHP/round7/s1-odd/r2/audit.py
```

The wrapper returned normally; `Attempt.lean.exit` contains **0** (2026-10-22 14:07:23 UTC). There are **no warnings or errors**, **51 dependency records**, and **no forbidden raw tokens**. Every dependency set is a subset of `propext`, `Classical.choice`, `Quot.sound`. The audit checks source/log/exit freshness, all local prints, exact pin/helper copies, frozen-only imports, and slice-body identity.

```text
'Round7.S1Odd.not_touchFour_every_ell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| Artifact | SHA-256 |
|---|---|
| `Attempt.lean` (identical to round 1) | `ab9a9c0e1ed1592b3791f729652dc7474754897e93ea124d8b708927f6dffb39` |
| `Attempt.lean.log` | `18870a213fc48bd757dc6ed801adc9c62629714a06beca8505ef047635d2ad1b` |
| Unchanged `../pin/Statement.lean` | `0c7cc8458e7d862e549c8e091325d906c3c448fb0ac7f08c9827a62cac9f3e4f` |
| Unchanged `../pin/PIN.md` | `0d1dd9790636dc775075d6161ad9e723bf1cbebfcc55e8675c79a340f9c5b006` |

This is fresh **attack-worker compilation**, not an independent workflow-verifier replay or a whole-project rebuild. The independent round-2 gate remains separate. For that replay, allow enough direct-bash time for both the serial lock queue and compilation (this invocation used a 2400-second timeout budget); a 200-second wall-clock timeout may expire while another worker holds the lock. Never relaunch a timed-out invocation; inspect its own exit record.

## Limits

No mathematical obstacle remains for the exact pinned mass-window goals. This closes the odd-blocking omission only for the **unguarded four-touch-class/corner-operator formal slice**. The carrier is singular, so its ordinary covariance inverse does not exist. The result does not settle inverse-guarded corner readings, `P428Target8SG`, `GuardPencilT`, odd-ell sites-only coverage, shell coercivity, masses at least four, or Balaban's unqualified printed assertion.

Retained conventions include three dimensions, SU(2), finite periodic tori, factor-12 product boxes, added site and common-cube four-touch coverage, per-cube gauges, guarded derivative stencils, the frozen tower/Lambda/support/constraint constructions, exterior-link dependence of corner operators and totalized inverses. The source-page quotations remain inherited reading evidence; this pass did not independently reread page images.

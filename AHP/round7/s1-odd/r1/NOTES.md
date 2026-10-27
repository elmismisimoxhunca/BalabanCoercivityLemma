# S1-odd attack, round 1

## Result

**Both pinned goals are proved**, for the explicitly pinned mass window \(0<a<4\).

- `Attempt.lean:477`: `Round7.S1Odd.goal1_proved : Round7.S1Odd.Goal1`.
- `Attempt.lean:480`: `Round7.S1Odd.goal2_proved : Round7.S1Odd.Goal2`.
- `Attempt.lean:422`: `Round7.S1Odd.not_touchFour_every_ell` proves the slice negation for arbitrary \(\ell\ge2\) and arbitrary \(0<a<4\).

Thus **each** such fixed-\(\ell,a\) slice fails, including each odd \(\ell>11\), not merely the universally quantified headline at \(\ell=2\). No mathematical obstacle remains for these exact goals. The range \(a\ge4\) is not decided; the available endpoint estimate gives the strict window \(a<4\), not its sharpness.

## Reuse and pin integrity

The pin, its `PIN.md`, and an already completed proof under `../proof/Attempt.lean` existed when this attack started. This pass audited and reused that proof rather than claiming a new construction. It created the requested `r1/Attempt.lean`, adding ten dependency prints for direct frozen locality/regularity helpers. No existing pin, earlier proof, or earlier audit was edited.

The complete round-3 pin remains a byte prefix of `../pin/Statement.lean`. The complete round-7 pin is copied unchanged into `Attempt.lean` at line 3. Its only preceding text is the frozen import header:

```lean
import D1Final
import GdPlaq
```

Lean requires those imports before declarations; consequently the pin starts after this 29-byte header, not literally at byte zero. This is the same layout as the supplied proof. All pinned definitions and goals are unchanged, and no AHP module is imported. Direct imports are only frozen `D1Final`, `GdPlaq`, and the pin's `D1Lit`.

The full round-3 helper block from `/-! ## Locality: corner and all selectors` through immediately before `/-- Exact pinned negative goal.` is copied verbatim. Every local definition and helper/main theorem has a dependency print.

`headline_iff_slices` at line 415 is proved by `Iff.rfl`. It identifies the original headline with its universally quantified slices. A separate source check confirms that the slice body removes **only** the outer \(\ell,\mathrm{hell},a,0<a\) binders. It retains `SidePow6`, factor 12, the class and instance, and every threshold and field hypothesis.

## Proof and threshold order

The template is `lean/src/D1PGen.lean:24`, whose imports lead through `D1Cons` to `D1Final`. The proof uses its general-\(\ell\) family directly, not an implication between distinct classes.

1. Assume the fixed-\(\ell,a\) slice. Choose \(m=m_0\), \(M=\ell^{m_0}\), and \(R=\max(R_0,18)\). Then \(\ell\mid M\), \(M\ge\ell\), and \(RM\ge17\ell\). The radius is fixed before the positive cap and coercivity constant are received.
2. Frozen `NV1`/`NV2`/`NV5`/`NV6`/`NV7` give the depth-two `SlabNv ell M R`, torus and Lambda compatibility, admissibility and factor-12 coverage. `SlabNv_bdpt` gives an inside site with an outside neighbor, so the base is proper and nonempty at every blocking factor used.
3. The copied transverse-slab lemma converts the existing slab coverage into the exact `CoversPlaqFour` requirement. This does not identify four-touch coverage with corner coverage on arbitrary domains.
4. Along the genuine exterior path `Uth`, every endpoint-touching link is identity. The copied zero-logarithm proof establishes all three strict `PerCubeRegularTouch` bounds for every positive smallness parameter.
5. The copied corner/all-carrier identity acts on the genuine touching-supported space after W and Dirichlet compression. It is an operator equality, without an inverse premise; it is not an equality with the frozen inside selector or a comparison of all J operators.
6. `D1Main.exists_nonunit_Ginv`, transferred by that identity, supplies a non-unit corner carrier at some \(0\le\theta<\pi\) for every \(0<a<4\). The negative endpoint and intermediate singular configuration are not conflated.
7. Choose \(\alpha_0=\tfrac12\min(a_0/(12M),1)\), giving strict positivity and \(12M\alpha_0\le a_0\), with the actual touching class and coverage.
8. `NV6.BseedNv_props` supplies the genuine admissible independent field with positive energy. `D1Collapse.not_InstIneqS_of_not_unit` contradicts every positive coercivity constant using the **complete** selected form. Its totalized inverse collapse is \(-a\langle B,B\rangle\), with \(B\) the reconstructed field; it is not just a raw-Hessian sign calculation.

The proof discards the supposed `SidePow6` conjunct because the analytic conclusion itself is contradictory; it does not exploit a failing side condition. No parity condition is used. The additional odd-\(\ell\) theorem is a direct restriction of the general theorem.

## Fresh verification

Run directly in bash, with the serial wrapper (no terminal and no direct Lean/Lake invocation):

```sh
AHP/round3/lean1.sh AHP/round7/s1-odd/r1/Attempt.lean
python3 AHP/round7/s1-odd/r1/audit.py
```

- `Attempt.lean.exit`: **0**; no errors or warnings.
- **51** dependency records, all subsets of `propext`, `Classical.choice`, `Quot.sound`.
- **30** locally declared definitions/theorems, each covered by a dependency print.
- No forbidden raw Lean token; no AHP import; unchanged pin and helper copies; exact slice-body check passed.
- Source/log/exit timestamps have the required order.

Decisive records:

```text
'Round7.S1Odd.not_touchFour_every_ell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal1_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'Round7.S1Odd.goal2_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Hashes:

| Artifact | SHA-256 |
|---|---|
| `Attempt.lean` | `ab9a9c0e1ed1592b3791f729652dc7474754897e93ea124d8b708927f6dffb39` |
| `Attempt.lean.log` | `18870a213fc48bd757dc6ed801adc9c62629714a06beca8505ef047635d2ad1b` |
| Unchanged pin | `0c7cc8458e7d862e549c8e091325d906c3c448fb0ac7f08c9827a62cac9f3e4f` |

`AUDIT.json` contains every dependency record, import hashes and copy checks. This is a fresh attack-worker compile and audit, not the separate workflow verifier's replay or a whole-project rebuild.

## Scope and remaining limits

This closes the odd-blocking omission for the **unguarded four-touch-class/corner-operator formal slice**. The counterexample has a non-unit carrier: its ordinary covariance inverse does not exist. It does **not** establish failure with every printed inverse existing, close `P428Target8SG`/`GuardPencilT`, prove a guarded corner refutation, settle odd-ell sites-only coverage in OPEN_ITEMS M, or refute Balaban's unqualified printed assertion.

The retained restrictions include three dimensions, SU(2), finite periodic tori, the frozen tower/Lambda/support/constraint conventions, factor-12 product boxes, added site and common-cube four-touch coverage, per-cube gauges, guarded derivative stencils, the corner operator's exterior-link dependence, and totalized inverses. Only the blocking-factor omission is removed. The later-paper odd-L and touching quotations are inherited reading evidence; page images were not independently reread.

No numerical job was needed. This pass wrote only `AHP/round7/s1-odd/r1/`; it made no protected-tree edits, deletion, commit, push, dependency update, reproduction run, or deployment. The broader durable goal was queried and is absent on this workflow child.

# Assembly R2 — whole KernelLine proved; GoalNeg2 reduced to P3 alone

## Verdict

**P1 and P2 are proved and integrated. The actual right-star crossing has the
original whole-kernel `KernelLine` and real nullity two, at every positive q,
even R≥18, with the nested cofinal quantifiers. P3 and GoalNeg2 remain OPEN.**

The complete final-goal route now compiles in one self-contained source:
`P3 → GoalNeg2`, and the weaker `CofinalP3 → GoalNeg2`. These are conditional
implications, **not** proofs of detection, response noncancellation, or GoalNeg2.

The requested round-10 helper repair was already completed in R1. Its original
single BB-terminal compile is retained and re-audited read-only, **not rerun**.

## Compiled deliverables

| Local source | Publication | Lines | Printed records | Exit |
|---|---|---:|---:|---:|
| **`P2Goal.lean` (final)** | **`AHP/round13/shared/assembly/R2_P2Goal.lean`** | **11120** | **12 each** | **0 / 0** |
| `PhysicalGoal.lean` | `AHP/round13/shared/assembly/R2_PhysicalGoal.lean` | 9626 | 3 each | 0 / 0 |
| `GoalBridge.lean` | intermediate downstream slice, local only | 6702 | 1 | 0 |

Every certificate has `.lean.log` and `.lean.exit`. Each final local/shared pair
is byte-identical and was executed separately through
`bb heavy run -- AHP/round3/lean1.sh <file>`. Only frozen `DrEquiv` and `DrPath3`
are imported. No AHP module is imported as an unbuilt `.olean`. All printed
dependencies are subsets of `{propext, Classical.choice, Quot.sound}`.
Eleven harmless warnings arise in unchanged copied proofs. These are builder
and publication executions, not an independent reviewer acceptance.

`PhysicalGoal` first closed the R1 end-to-end integration gap with exact
`P2 → P3 → GoalNeg2`. After positivity's local P2 file finished cleanly, its
source was checked against the shared publication and copied into `P2Goal`.
Both final assembly executions recheck the actual P2 proof, not just its name.

## 1. Unconditional whole-kernel crossing

Namespace `AdalyFormal.Round13.Assembly.R2`, final file:

```lean
-- :11049
theorem p2 : AdalyFormal.Round13.Assembly.R1.P2 :=
  AdalyFormal.Round13.Positivity.Physical.rightStar_P2

-- :11050
theorem rightStar_kernelLine {q R : ℕ} (hq : 0 < q)
    (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2
```

It invokes the original `CrossingActual.kernelLine_exists_before_halfpi` with
proved P1, proved P2, the R1 actual continuity/strict positive start, and the
right-star quarter gauge. No nonzero kernel witness, chargedness, isolated root,
positivity, simplicity, numerical, or inverse-unit assumption remains.
`KernelLine` describes the **whole actual carrier kernel**, not one character.

`cofinal_rightStar_kernelLine` (:11061) proves the corresponding nested statement:

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

This chooses j=j₀ and R=2*(R₀+18). The stronger all-instance theorem allows
later detection to choose **any** admissible cofinal radius family. There is no
intersection of unrelated cofinal sets. Neither theorem detects the generator.

Literal record:

```text
'AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. Complete final-goal chain, conditional only on detection

The exact elaborated types printed by `#check @...` in both final logs include:

```lean
AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3 :
  AdalyFormal.Round13.Assembly.R1.P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2

AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3 :
  AdalyFormal.Round13.Assembly.R2.CofinalP3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2
```

Locations are :11077 and :11093. There are no hidden section, regularity, P1/P2,
inverse-unit, initial-positivity, or crossing assumptions. The intermediate
`cofinalNoCancellation_of_P3` (:11075) and
`cofinalNoCancellation_of_cofinalP3` (:11089) conclude the **original**
`CofinalAnyPathNoResponseCancellation`, still with the displayed detection input.

The complete source checks the same right-star family, canonical edge and
actual generator through `R2_FirstCrossing`, the direct
`R2_ResponseLine.cofinal_noCancellation_of_curlLine`, the round-10
response/coupling equivalence with proved regularity, and the round-9
arbitrary-path bridge. The final pin retains both all-plaquette selectors and
only the uncorrected-carrier guard. The old giant Color appendix is irrelevant
to this dependency slice.

```text
'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Exact remaining Lean statements

Use the original shared-package opens (`TwistSpace`, `vacA`, `rightStar`,
`rightSite`, `KernelLine`, `CurlDetected`). **No P1 or P2 obligation remains.**
The original P3 is still unproved, verbatim:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The weaker sufficient `AdalyFormal.Round13.Assembly.R2.CofinalP3` (:11078) is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u
```

This is a defined proposition, not an inhabitant. The universal line clause
is no longer potentially empty: `rightStar_kernelLine` produces a generator at
every such pair. The original sufficient existential cofinal family likewise
remains missing:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

Detection R2's exact physical-area dictionary offers another sufficient but
still unproved input (open its `PhysicalArea` and original `DilatedFlux`):

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The exact identity `physicalJetAggregate = (1/2)*areaSum` does not prove this
nonvanishing. A nonzero linear trace, individual determinant, or one charged
line is not sufficient to rule out cancellation of the weighted sum.

## 4. Source and compilation audit

`prune_goal.py --p2` selects a conservative dependency slice from the compiled
R1 repaired join, R1 P1 spine, and R2 P2 publication, then adds the applications
in `GoalAppendix.lean.txt` and `P2Appendix.lean.txt`. **Python is not a proof
oracle:** Lean elaborates and kernel-checks all selected bodies anew.

- `P2Goal_COPIES.json`: **763 verbatim declaration chunks**, source lines/hashes.
- `P2Goal_DEDUP.json`: 372 repeated declarations. Six raw chunks differ only by
  the scoped `open Classical in` and a comment on three repeated definitions;
  their operative bodies are identical. All are audited.
- `AUDIT.json`: six clean compilation artifacts, every printed axiom record,
  forbidden-mechanism scan, source/log hashes, publication identity, 18 exact
  original interfaces, and the explicit final theorem types.
- Fourteen current sibling publication source/log/exit triples were inspected
  read-only. All three sibling R1 NOTES and all three R2 NOTES were read in full.
  P1 independent acceptance is preserved in `trial/r1/Trial.VERIFY.md`.

The retained R1 `RepairedJoin.lean` is re-audited against the original round-10
file and verbatim helpers `half_twice`, `half_average`, `phase_axis_fixed`.
Its requested **single** BB-terminal compile (R1 terminal `term_i4rxw7r37d`)
still has exit 0 and 1186 standard records. R2 did not repeat it or edit any
historical source. Dependency-slicer scope omissions during development were
corrected before the accepted files; no failed extraction is credited.

## 5. Reproduction and scope

```sh
python3 AHP/round13/assembly/r2/prune_goal.py --p2
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r2/P2Goal.lean
# Copy byte-for-byte to shared/assembly/R2_P2Goal.lean and compile separately.
python3 AHP/round13/assembly/r2/audit.py
```

No numerical solve, lake build, REPRODUCE.sh, commit, push, earlier-round edit,
or deletion outside this track was performed. Only own Python cache diagnostics
were removed. The mapped child's durable goal is null; the unrelated inherited
goal was not altered. `AHP/round13/shared/GAPS.md` now records only detection as
the remaining physical input, not a completed GoalNeg2.

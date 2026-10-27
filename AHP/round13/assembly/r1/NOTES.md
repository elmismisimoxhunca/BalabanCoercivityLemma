# Assembly R1 — repaired goal join; complete conditional right-star spine

## Verdict

**GoalNeg2 remains OPEN. P1 is CLOSED by Trial R1 and integrated here; P2/P3
remain OPEN.** This round repairs the historical round-10 compiler failure,
closes the right-star continuity/full positive-start inputs, recompiles the
actual P1 proof in the round-12 spine, and constructs the actual canonical
crossing in `(0,pi/2)` with a nonzero kernel vector. The whole-kernel line and
its detection still need P2/P3. No unconditional cofinal noncancellation or
pinned-goal inhabitant is supplied.

## Certificates

| Local source | Publication | Lines | Axiom records | Exit |
|---|---|---:|---:|---:|
| `RepairedJoin.lean` | retained locally; see repair below | 16844 | 1186 | 0 |
| `Spine.lean` | intermediate, with explicit StartInputs | 3495 | 217 | 0 |
| `StartedSpine.lean` | `AHP/round13/shared/assembly/R1_Spine.lean` | 4481 | 226 each | 0 / 0 |
| **`P1Spine.lean` (latest)** | **`AHP/round13/shared/assembly/R1_P1Spine.lean`** | **6150** | **399 each** | **0 / 0** |

Every file has `.lean.log` and `.lean.exit`. Both published spines are byte-identical
to their local sources and each was compiled separately. All printed axiom sets are subsets
of `{propext, Classical.choice, Quot.sound}`. `AUDIT.json` checks every printed
record, forbidden tokens, 20 verbatim source ranges, the repair insertion,
source/log hashes, the pinned target and six original interfaces shared by
both certificates. These are builder/publication compiles, not independent
reviewer verification (blueprint B). No numerical computation was used.

## 1. Historical round-10 repair: COMPLETE compiler repair, conditional theorem

`build_repair.py` copies `AHP/round10/assembly/r4/Attempt.lean` and inserts the
missing helpers before Color, in their original FreeSource namespace:

- `phase_axis_fixed`, verbatim from dictionary lines 1376–1388;
- `half_twice`, verbatim from dictionary lines 1467–1477;
- `half_average`, verbatim from dictionary lines 1480–1497.

Their required `half_rotation_matrix`, `neutral_of_half_fixed`, and related
background were already present. Namespace openings and three new axiom prints
are included. Removing this insertion yields the original source byte-for-byte;
`REPAIR_COPIES.json` pins the exact source spans/hashes. Historical comments in
the original source were deliberately preserved, not endorsed as current status.

The repaired copy was compiled **once** with lean1.sh inside BB terminal
`term_i4rxw7r37d`, created at environment scope. Command:

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r1/RepairedJoin.lean
```

Exit 0; no memory kill, no compiler errors and no nonstandard dependency records.
The first attempt to create a *thread-scoped terminal* returned HTTP 409 before
opening; there was no process/log/exit and no Lean invocation on that attempt.
The successful environment-scoped terminal printed `ROUND13_REPAIRED_JOIN_DONE=0`
and was closed with `--if-clean` after audit. No large compile ran as a bash child.

The previously broken regularity, flat-constraint and goal joins are now clean
in this round-13 copy. In particular:

```lean
-- RepairedJoin.lean:15900, namespace AdalyFormal.Round10.Assembly.R4
theorem goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (h : CofinalAnyPathNoResponseCancellation) : GoalNeg2
```

Literal record at `RepairedJoin.lean.log:1767` (whitespace joined):

```text
'AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This proves an implication only. The `h` has not been proved. The target is
verbatim the pin's `GoalNeg2 := ¬ P428Target8SG selAll selAll`, via GoalPos2.
Earlier round-10 sources/logs remain untouched and retain their historical failure.

## 2. Actual right-star start inputs: no remaining hypotheses

In namespace `AdalyFormal.Round13.Assembly.R1`, shared spine:

- `rightStar_fixed` (3426): quarter-gauge invariance specialized to the very
  `RightFamily.rightStar` used by the crossing, not a left-star reflection.
- `rightStar_vacA_cont` (4397): the actual full carrier is continuous, from
  frozen `D1Residual.GinvLit_cont` and `vacA_rightStar`.
- `rightStar_vacA_pd_zero` (4414): actual full-carrier strict positivity at zero,
  for every positive q and R≥1. Recompiles the historical flat localized kernel
  proof and its mass/curl/gauge sum, then transfers positivity through the
  actual all-plaquette domination. It is not a charged-block/Schur estimate.
- `startInputs` (4425): discharges BOTH formerly explicit start assumptions.

The final source imports only frozen `DrPath3` and `DrEquiv`. Its historical
proof bodies and operative round-12 definitions are copied verbatim; no AHP
source is imported as an unbuilt module. `START_COPIES.json` and
`SPINE_COPIES.json` record the exact spans. The two initial StartedSpine
failures (missing helper/import, then expensive Pth unfolding) were corrected;
those transient failed-build diagnostics were removed after the clean final
compiles. The final source/log/exit are clean.

## 3. The compiled reductions retain all open physical premises

P1/P2/P3 at shared lines 3392/3397/3405 are definitions of the exact propositions
from round-12 GAPS, NOT theorems asserting them.

```lean
-- shared R1_Spine.lean:4432
theorem cofinalNoCancellation_of_P1_P2_P3 (h1 : P1) (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation

-- :4468
theorem cofinalNoCancellation_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

These earlier implications are retained; the latest P1-integrated versions
below eliminate P1 as a hypothesis. The first uses the all-instance P1/P2/P3 forms. The second only requires the
joint nested cofinal version: for arbitrarily large dyadic j and then arbitrarily
large even R≥18, P1, P2 and P3 all hold at the same pair. No intersection of
unrelated cofinal subsequences is used.

`detected_line_of_physicalInputs` invokes the original FirstCrossing theorem;
it returns `0 < vacEdge < pi/2`, the original whole-kernel `KernelLine`, detection
of that very generator, and full real nullity two. The response arrow is
`ResponseActual.cofinal_noCancellation_of_curlLine`, with no RegularityFacts
hypothesis. The repaired downstream goal arrow already discharges regularity.

Literal shared log record at line 397:

```text
'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalPhysical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The separate repaired and compact certificates have identical original `vacA`,
`vacEdge`, `KernelLine`, `NoResponseCancellation`, `CofinalAnyPathCurlLine` and
`CofinalAnyPathNoResponseCancellation` bodies (audited byte-for-byte).
They certify the two segments of the conditional route. No new monolithic
round-13 P1/P2/P3-to-GoalNeg2 specialization was compiled. In particular, nothing
here can be reported as an unconditional cofinal or pinned-goal proof.

## 3a. Late P1 integration: actual crossing now constructed

`build_p1.py` appends the needed Boundary/Mass/Star/Plaquette and Trial proof
bodies from the clean `shared/trial/R1_Trial.lean`, omitting only repeated
RightFamily/TwistSpace declarations already present in the base. The two
verbatim ranges are hashed in `P1_COPIES.json`. P1Spine and its shared copy both
compile with exit 0 and 399 standard dependency records.

Latest namespace `AdalyFormal.Round13.Assembly.R1`, in `R1_P1Spine.lean`:

| Declaration | Source | Log | Status |
|---|---:|---:|---|
| `p1 : P1` | 6084 | 603 | unconditional, uses Trial R1 |
| `rightStar_crossing_before_halfpi` | 6088 | 604 | unconditional actual crossing/kernel witness |
| `cofinalNoCancellation_of_P2_P3` | 6116 | 607 | conditional on P2 and P3 only |
| `CofinalP2P3` | 6121 | 610 | predicate definition, not an inhabitant |
| `cofinalNoCancellation_of_cofinalP2P3` | 6140 | 614 | conditional joint cofinal reduction |

The unconditional crossing theorem gives `0 < vacEdge < pi/2`, PSD and
nonunitness of the **actual full** carrier at that canonical edge, and an
actual nonzero vector in its kernel. It uses the negative physical trial,
unconditional continuity/positive start, and the non-isolation first-crossing
argument. It asserts no chargedness, no KernelLine, no nullity two and no jet
nonvanishing. Those still need the remaining physical estimates.

The latest reduced premise `CofinalP2P3` chooses j first and R second, then asks
for BOTH interval positivity and same-line-generator detection at that SAME
pair. Its full exact body is in `shared/GAPS.md` section 4. The all-instance
P1 supplies the trial at those indices, so no cofinal-subsequence intersection
is needed. The downstream implication is:

```lean
theorem cofinalNoCancellation_of_cofinalP2P3 (h : CofinalP2P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

Literal printed axiom record (whitespace joined):

```text
'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is still conditional, and its premise is not proved. The separately
compiled repaired GoalNeg2 arrow applies to its conclusion, but we did not
recompile the large repair a second time or invent a complete GoalNeg2 term.

## 4. Exact remaining statements

Using the round-12 shared opens (`TwistSpace`, `vacA`, `rightStar`, `rightSite`,
`KernelLine`, `CurlDetected`), the physical input types are verbatim (P1 now proved; P2/P3 still missing):

```lean
-- P1
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0

-- P2
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

-- P3
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The weaker exact missing family is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

`AHP/round13/shared/GAPS.md` also gives the complete joint cofinal physical-input
body and the sharpened sibling-track leaves. No finite numerical evidence is
promoted to these quantifiers.

## 5. Sibling audit / handoff

Read trial, detection and positivity R1 NOTES in full and checked all eight published
source/log/exit triples independently with this track's audit (no recompile).

- Detection: full flat N unit and unit-free `TopJetDetected → CurlDetected`
  handoff are compiled. Crossing-specific quadratic detection remains open;
  single-color fields and nonzero linear traces do not supply it.
- Positivity: eight distinct actual leaf rows/masses and unconditional localized
  right-star positivity are compiled. Complete raw omitted-plaquette loss at
  central charged zero remains open. The correct mass-relative comparison is
  `A_t ≥ cos(t) B_t`, not a guessed ordinary-norm gap subtraction.
- Trial: **P1 proved** without extra hypotheses. Read the actual carrier join
  and copied its entire needed proof into P1Spine, then compiled local/shared
  copies. This is not acceptance based only on a note or rational surrogate.

## 6. Reproduction (compact work only)

```sh
python3 AHP/round13/assembly/r1/build_spine.py
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r1/Spine.lean
python3 AHP/round13/assembly/r1/build_started.py
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r1/StartedSpine.lean
python3 AHP/round13/assembly/r1/build_p1.py
bb heavy run -- AHP/round3/lean1.sh AHP/round13/assembly/r1/P1Spine.lean
# Publications were copied byte-for-byte and compiled separately.
python3 AHP/round13/assembly/r1/audit.py
```

Do NOT relaunch the large repair compile: its requested single execution is
complete. No lake build, reproduction suite, commit, push, deletion outside this
track's directory, or edits outside assembly/shared were performed, except the
authorized wrapper's shared lock files. Only transient failed-build diagnostics
in this track's own directory were deleted. The inherited unrelated durable goal is absent on this mapped child
(`get_goal` returned null); it was not changed.

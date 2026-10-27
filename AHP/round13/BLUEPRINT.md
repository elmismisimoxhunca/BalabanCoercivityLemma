# Blueprint: the Ginv-only guarded reading — round 13

## Changelog since round 12

- **P1: O → A.** Exact six-bond physical energy is \(-1/4\); P1 and its cofinal handoff have independent exit-0 replays.
- **P2: O → A.** Complete omitted-plaquette control, eight actual leaf masses and localized positivity prove the original full-carrier P2, independently replayed.
- **Whole kernel: now A.** P1/P2 are integrated: the canonical right-star crossing lies in \((0,\pi/2)\), has the original whole-kernel line and real nullity two, including nested cofinal quantifiers.
- **P3: still O.** The flat N-unit prerequisite is closed and the actual top jet equals half a weighted mixed-color area sum. Nonvanishing of that sum is not proved.
- **Round-10 join: C-broken → compiled in the round-13 repaired copy.** Earlier failed sources/logs are unchanged. The complete \(\mathrm{P3}\Rightarrow\mathrm{GoalNeg2}\) bridge is independently replayed, but is conditional.
- Added all 243 individually axiom-audited round-13 declarations (170 A, 73 B) and an explicit index of eight supporting declarations lacking individual axiom prints. **GoalNeg2 remains open.**

## Verdict and audit boundary

**GoalNeg2 remains OPEN. P1 and P2 are proved; P3 is the sole remaining physical input on the right-star route.** Actual whole-kernel construction and the complete conditional P3-to-goal bridge now compile and have independent replays. Neither cofinal noncancellation nor its negation is proved. This is not a completed guarded refutation.

Notation: \(A=G^{-1}_{\mathrm{all}}\), \(B=G^{-1}_{\mathrm{in}}\), \(D=\Delta^{(2)}_{\mathrm{in}}\), \(C=B-D\), and \(\Theta=A-B\). The intended failure is \(\operatorname{IsUnit}(A)\land\neg\operatorname{IsUnit}(A-D)\). The vacuum singularity used to construct the kernel is **not** itself the guarded failure point.

### Status convention

- **A — compiled and independently verified:** a clean exit-0 builder record and an identical declaration body with its own permitted axiom record in an independent reviewer replay (round 9 or round 13). The replay source, log and exit were checked; per-node replay citations are supplied. This certifies the displayed statement, not its suitability as a final workflow target. No fresh compilation was run by this blueprint writer.
- **B — compiled by a builder only:** current source, exit-0 log and its individual standard-axiom record were inspected. A second publication-path execution by the same builder is not an independent reviewer replay. All round-12 certificates are conservatively in this category.
- **C-memory — assembled but uncompiled owing to memory:** the historical status of the long round-10 joins. It is retained in the history, **not** asserted as their current blocker.
- **C-broken — assembled, failed whole-file compilation:** the retained status of the original round-10 sources, whose coordinator run exited 1. The round-13 repaired copy now exits 0 and is credited separately below; no historical failed artifact is relabelled successful.
- **O — open:** no proof of the asserted proposition; a compiled definition of that proposition is not a proof of it.

The companion LaTeX uses one node per named result and attaches the proof marker only to A/B declarations with a checked individual standard-axiom record in a clean exit-0 log. Compiled predicate definitions have definition nodes; separate open assertion nodes have no proof marker. Open physical estimates have no invented theorem names: their Lean annotation points to the existing predicate/operator, explicitly not to a theorem asserting the estimate.

The ledger covers the guarded boundary-response, gap/decay, full-vector/Schur, sign-change, analytic and qualitative routes; the round-10 dictionary/source/jet/hull alternatives; the round-12 star/kernel improvements; and the round-13 physical trial, positivity, detection dictionary and repaired integration. Companion wrappers are catalogued separately to retain the historical implications rather than hide stronger premises behind the preferred path. Dependencies are **named statement/proof inputs at blueprint granularity**, with additional local source references listed; they are not a claimed extraction of Lean's complete kernel-level dependency DAG. Standard Mathlib algebra, topology and finite-dimensional linear algebra, and frozen imported implementation primitives, are the background. A premise occurring in a conditional theorem remains a premise.

Rounds 7 and 11 also contain touching-selector/odd-site and mass-window work for **different, unguarded pins**. They are not edges proving this Ginv-only target. Round-11 scope nodes below record the relevant outcomes without importing them as guarded counterexamples. No old failed extension is silently promoted from an inherited axiom print.

No Lean compilation, build, reproduction script, numerical solve, source repair, commit or push was run for this documentation task. The source/log audit is read-only. Only the two requested blueprint files are authored in the checkout.

## Mathematical spine

The pinned equivalence reduces the question to the eventual implication
\[
 A\text{ unit}\ \Longrightarrow\ A-D\text{ unit}.
\]
Localized well-definedness supplies the exact correction/pencil identity and the genuine localized inverses. In boundary coordinates it is the comparison of \(K_B=I+\Theta B^{-1}\) and \(K_C=I+\Theta C^{-1}\) on \(\operatorname{ran}\Theta\). Absolute smallness of \(D\) does not control \(K_B^{-1}\); a unit guard is not a uniform gap.

The qualitative refutation route chooses \(\ell=2\), \(a=1\), \(k=1\), \(q=2^j\), and an even \(R\ge18\) **before** the small-curvature cap. At a vacuum crossing, a first-order correction definite on the full kernel splits the corrected crossing from the carrier crossing. Negating the free interior profile handles either sign. The fully verified round-9 bridge then supplies arbitrarily small-curvature guarded failures with all class, geometry and positive-energy test obligations.

For a physical profile \(f\), define
\[
 z_u=C^2_0(W_0i_Eu),\qquad r_u(b)=\langle E_3,(i_EH_0z_u)(b)\rangle,
 \qquad F_f(u)=2\sum_{p\in\operatorname{plaqIn}\Omega_0}c_{r_u}(p)c_f(p).
\]
These are actual frozen operators, not reduced numerical matrices. The adaptive choice \(f=r_u\) gives curl-square energy. This detects one vector, not automatically an entire kernel. The exact common-profile condition is
\[
0\notin\overline{\operatorname{conv}}\{g(u):u\in\ker A_0(t_*),\ \|u\|=1\},
\qquad g(u)=2\,\operatorname{curl}_P^*\operatorname{curl}_P r_u.
\]
Round 12 proves that under the original whole-kernel charged-line condition this hull is the singleton \(\{g(u_0)/\|u_0\|^2\}\). Round 13 now proves that whole-kernel line for every positive q and even R at least 18. Actual detection at the same crossing, or its nested cofinal version, is the remaining physical obligation. Nonzero charged fields can have zero jets, and different nonzero unit responses can cancel; both shortcuts have compiled obstructions.

Round 13 closes the two physical estimates that construct this line: the explicit trial has energy \(-1/4\) at half pi, and on the central-charged-zero subspace the full carrier dominates \(\cos(t)\) times the genuinely positive localized carrier for \(0\le t<\pi/2\). The neutral coordinate is retained. This proves P2 without claiming a strict half-pi endpoint bound or a scale-uniform ordinary-norm gap. The kernel is a whole-carrier real plane, not a selected charged Schur eigenspace.

The detection dictionary proves \(\mathrm{physicalJetAggregate}=\tfrac12\,\mathrm{areaSum}\) for that generator, with the actual interior dressing and normalization. It does not prove the weighted sum is nonzero. The numerical crossing angle and tiny tangential jets remain evidence, not certificates.

## Pinned quantifiers and guards

The positive target is `P428Target8SG selAll selAll`, not a touching-selector target. Its exact order (`AHP/round3/guarded/pin/Statement.lean:113`) is
\[
\forall \ell\ge2,\ \forall a>0,\ \exists m_0\ge1,\ \forall m\ge m_0,\ \exists R_0,\ \forall R\ge R_0,
\quad \mathrm{SidePow6}(\ell,\ell^m,a)\ \land\ \exists a_0>0,\ \exists\gamma_0>0,
\]
followed by **all** depths \(k\ge1\), lattice extents and \(\alpha_0>0\) satisfying \(12\ell^m\alpha_0\le a_0\); then every `TorusOK`, `Admissible`, `LambdaOK2`, and `ClassCoupled` instance (with class constant 12 and \(\eta=(\ell^k)^{-1}\)). On each such instance, the sole guard is invertibility of the uncorrected carrier. The conclusion is the coercive inequality for every test satisfying both support conditions. There is no guard on the corrected carrier or corrected constraint inverse.

`GuardPencilT = GShape CPen` (`Statement.lean:133–151`) keeps the same scale/radius/cap order, with a positive-energy competitor and the uncorrected-carrier guard, and asks for invertibility of \(A-D\). The positive equivalence handles the `SidePow6` and coercivity constants; it does not change selectors or interchange the radius and cap. `GoalNeg2` is the logical negation of the entire positive target, not one failed numerical instance.

## Declaration ledger

Each entry gives a plain-mathematics statement, exact Lean name and source line, accepted compilation category, literal axiom record (multiline whitespace joined), and direct named dependencies. Code excerpts are source declaration headers, not fully elaborated `#check` output: section parameters remain inherited from the cited source. All paths are repository-relative. Axioms in every accepted record are a subset of \(\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}\).


### Targets and rounds 2–6

<a id="bp-001"></a>
#### bp-001 — `AdalyFormal.Round2.Guarded.Pin.GoalNeg2`

The target is the negation of the all-plaquette coercive headline with only the uncorrected carrier inverse guarded. Its definition is compiled; no inhabitant is known.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:158`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:20`: `'AdalyFormal.Round2.Guarded.Pin.GoalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:158`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:20`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.GoalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round3/guarded/pin/Statement.lean:157`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def GoalNeg2 : Prop
```

</details>

<a id="bp-002"></a>
#### bp-002 — `AdalyFormal.Round2.Guarded.Pin.GoalNeg1`

The alternative negative target denies that the carrier guard forces the corrected pencil to be invertible, with the original eventual scale/radius/cap order.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:155`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:18`: `'AdalyFormal.Round2.Guarded.Pin.GoalNeg1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:155`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:18`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.GoalNeg1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round3/guarded/pin/Statement.lean:154`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def GoalNeg1 : Prop
```

</details>

<a id="bp-003"></a>
#### bp-003 — `AdalyFormal.Round2.Guarded.Pin.P428Target8SG`

For each blocking factor and positive mass, sufficiently large scales and then radii admit positive smallness and coercivity constants valid for every later depth, torus and admissible configuration whose carrier is a unit.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:113`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:68`: `'AdalyFormal.Round2.Guarded.Pin.P428Target8SG' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:113`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:68`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.P428Target8SG' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.PlaqSel` (`AHP/round3/guarded/pin/Statement.lean:31`); `AdalyFormal.Round2.Guarded.Pin.CoercG8AtSG` (`AHP/round3/guarded/pin/Statement.lean:104`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def P428Target8SG (sD sJ : PlaqSel) : Prop
```

</details>

<a id="bp-004"></a>
#### bp-004 — `AdalyFormal.Round2.Guarded.Pin.GuardPencilT`

The same eventual class must make the pencil \(A-D\) a unit whenever \(A\) is a unit and a positive-energy competitor exists.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:151`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:72`: `'AdalyFormal.Round2.Guarded.Pin.GuardPencilT' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:151`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:72`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.GuardPencilT' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-005](#bp-005) (`AdalyFormal.Round2.Guarded.Pin.CPen`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round3/guarded/pin/Statement.lean:133`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def GuardPencilT : Prop
```

</details>

<a id="bp-005"></a>
#### bp-005 — `AdalyFormal.Round2.Guarded.Pin.CPen`

At one instance the pencil condition is \(\operatorname{IsUnit}(A-D)\), with \(A\) all-plaquette and \(D\) the genuine localized correction.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:145`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:71`: `'AdalyFormal.Round2.Guarded.Pin.CPen' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:145`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:71`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.CPen' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/pin/Statement.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round3/guarded/pin/Statement.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/pin/Statement.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/pin/Statement.lean:62`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CPen : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop
```

</details>

<a id="bp-006"></a>
#### bp-006 — `AdalyFormal.Round2.Guarded.Pin.goalPos2_iff_goalPos1`

The guarded coercive headline is equivalent to the eventual corrected-pencil unit statement, retaining the original selectors and quantifiers.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:178`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:30`: `'AdalyFormal.Round2.Guarded.Pin.goalPos2_iff_goalPos1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:178`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:30`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.goalPos2_iff_goalPos1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round3/guarded/pin/Statement.lean:154`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round3/guarded/pin/Statement.lean:157`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_iff_goalPos1 : GoalPos2 ↔ GoalPos1
```

</details>

<a id="bp-007"></a>
#### bp-007 — `AdalyFormal.Round2.Guarded.Pin.goalNeg1_iff_goalNeg2`

Negating the positive equivalence identifies the two pinned negative goals.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:181`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:31`: `'AdalyFormal.Round2.Guarded.Pin.goalNeg1_iff_goalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:181`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:31`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.goalNeg1_iff_goalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-002](#bp-002) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg1`); [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg1_iff_goalNeg2 : GoalNeg1 ↔ GoalNeg2
```

</details>

<a id="bp-008"></a>
#### bp-008 — `AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure`

A counterexample must fix a permitted blocking factor and positive mass, then supply arbitrarily large scales and radii chosen before every cap, with the full class and competitor data and \(A\) unit but \(A-D\) nonunit.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:189`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:21`: `'AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:189`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:21`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-005](#bp-005) (`AdalyFormal.Round2.Guarded.Pin.CPen`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round3/guarded/pin/Statement.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/pin/Statement.lean:58`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CofinalPencilFailure : Prop
```

</details>

<a id="bp-009"></a>
#### bp-009 — `AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`

A cofinal pencil-failure family contradicts the pinned guarded coercive headline.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:218`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:35`: `'AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:218`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:35`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-008](#bp-008) (`AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure`); [bp-245](#bp-245) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg1`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPencilFailure_implies_goalNeg2 (h : CofinalPencilFailure) : GoalNeg2
```

</details>

<a id="bp-010"></a>
#### bp-010 — `AdalyFormal.Round2.Guarded.R2Prove.response`

For a unit localized carrier \(B\), the boundary response is \(K_B=I+\Theta B^{-1}\) on \(\operatorname{ran}\Theta\), where \(\Theta=A-B\).

- **Source:** `AHP/round3/guarded/pin/Statement.lean:273`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:48`: `'AdalyFormal.Round2.Guarded.R2Prove.response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:273`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:48`, exit `0`; record: `'AdalyFormal.Round2.Guarded.R2Prove.response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
noncomputable def response (Θ B : E →L[ℝ] E) : Θ.range →L[ℝ] Θ.range
```

</details>

<a id="bp-011"></a>
#### bp-011 — `AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`

The boundary shift is exactly the difference of all-plaquette and localized carriers on the touching-bond space.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:290`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:49`: `'AdalyFormal.Round2.Guarded.R2Prove.boundaryShift' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:290`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:49`, exit `0`; record: `'AdalyFormal.Round2.Guarded.R2Prove.boundaryShift' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/pin/Statement.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round3/guarded/pin/Statement.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/pin/Statement.lean:58`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
noncomputable def boundaryShift : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)
```

</details>

<a id="bp-012"></a>
#### bp-012 — `AdalyFormal.Round2.Guarded.R2Prove.localCorrected`

The localized corrected carrier is \(C=B-D\); it is not the all-plaquette corrected carrier.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:293`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:50`: `'AdalyFormal.Round2.Guarded.R2Prove.localCorrected' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:293`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:50`, exit `0`; record: `'AdalyFormal.Round2.Guarded.R2Prove.localCorrected' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/pin/Statement.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/pin/Statement.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/pin/Statement.lean:62`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
noncomputable def localCorrected : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G)
```

</details>

<a id="bp-013"></a>
#### bp-013 — `AdalyFormal.Round2.Guarded.R2Prove.CBoundaryResponse`

The instance condition asks that \(K_C\) be a unit on the actual boundary-shift range.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:299`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:51`: `'AdalyFormal.Round2.Guarded.R2Prove.CBoundaryResponse' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:299`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:51`, exit `0`; record: `'AdalyFormal.Round2.Guarded.R2Prove.CBoundaryResponse' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CBoundaryResponse : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop
```

</details>

<a id="bp-014"></a>
#### bp-014 — `AdalyFormal.Round2.Guarded.R2Prove.CNoBoundaryReturn`

The inverse-propagated correction has zero return \(\Theta C^{-1}DB^{-1}y\) on every boundary-range vector.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:306`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:52`: `'AdalyFormal.Round2.Guarded.R2Prove.CNoBoundaryReturn' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:306`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:52`, exit `0`; record: `'AdalyFormal.Round2.Guarded.R2Prove.CNoBoundaryReturn' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/pin/Statement.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/pin/Statement.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/pin/Statement.lean:62`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CNoBoundaryReturn : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell)
    (_ : Tower (scaleUp ell k Lu)) (_ : LinkCfg (scaleUp ell k Lu))
    (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop
```

</details>

<a id="bp-015"></a>
#### bp-015 — `AdalyFormal.Round2.Guarded.R2Prove.unit_add_iff_response`

If \(B\) is a unit, then \(B+\Theta\) is a unit exactly when \(K_B\) is a unit on the boundary range.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:300`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:41`: `'AdalyFormal.Round2.Guarded.R2Prove.unit_add_iff_response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.R2Prove.unit_of_kernel_zero` (`AHP/round2/guarded/r2-prove/Attempt.lean:268`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem unit_add_iff_response (Θ B : E →L[ℝ] E) (hB : IsUnit B) :
    IsUnit (B + Θ) ↔ IsUnit (response Θ B)
```

</details>

<a id="bp-016"></a>
#### bp-016 — `AdalyFormal.Round2.Guarded.R2Prove.carrier_isUnit_iff_response`

Under the localized base inverse guard, the actual carrier unit condition is equivalent to invertibility of its boundary response.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:459`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:62`: `'AdalyFormal.Round2.Guarded.R2Prove.carrier_isUnit_iff_response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-015](#bp-015) (`AdalyFormal.Round2.Guarded.R2Prove.unit_add_iff_response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round2/guarded/r2-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round2/guarded/r2-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round2/guarded/r2-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.R2Prove.carrier_eq_local_add_shift` (`AHP/round2/guarded/r2-prove/Attempt.lean:422`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem carrier_isUnit_iff_response (hu : IsUnit (dataS selIn selIn P).Ginv) :
    IsUnit (dataS selAll selAll P).Ginv ↔
      IsUnit (response (boundaryShift P) (dataS selIn selIn P).Ginv)
```

</details>

<a id="bp-017"></a>
#### bp-017 — `AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response`

Under the localized corrected inverse guard, the actual corrected pencil unit condition is equivalent to invertibility of the corrected boundary response.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:467`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:65`: `'AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-015](#bp-015) (`AdalyFormal.Round2.Guarded.R2Prove.unit_add_iff_response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round2/guarded/r2-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round2/guarded/r2-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round2/guarded/r2-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round2/guarded/r2-prove/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.Pin.G1invS` (`AHP/round2/guarded/r2-prove/Attempt.lean:69`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round2/guarded/r2-prove/Attempt.lean:417`); `AdalyFormal.Round2.Guarded.R2Prove.pencil_eq_local_add_shift` (`AHP/round2/guarded/r2-prove/Attempt.lean:427`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_iff_response (hu : IsUnit (G1invS selIn selIn P)) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) ↔
      IsUnit (response (boundaryShift P) (localCorrected P))
```

</details>

<a id="bp-018"></a>
#### bp-018 — `AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_of_no_boundary_return`

Genuine localized inverses, the carrier guard and zero boundary return imply the corrected pencil is a unit.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:475`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:68`: `'AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_of_no_boundary_return' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round2/guarded/r2-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round2/guarded/r2-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round2/guarded/r2-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round2/guarded/r2-prove/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.unit_corrected_of_no_return` (`AHP/round2/guarded/r2-prove/Attempt.lean:376`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round2/guarded/r2-prove/Attempt.lean:417`); `AdalyFormal.Round2.Guarded.R2Prove.carrier_eq_local_add_shift` (`AHP/round2/guarded/r2-prove/Attempt.lean:422`); `AdalyFormal.Round2.Guarded.R2Prove.pencil_eq_local_add_shift` (`AHP/round2/guarded/r2-prove/Attempt.lean:427`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_no_boundary_return
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hret : ∀ y : (boundaryShift P).range,
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) = 0) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-019"></a>
#### bp-019 — `AdalyFormal.Round2.Guarded.R2Prove.guarded_failure_forces_boundary_return`

Under the localized inverse guards, a guarded pencil failure forces a nonzero inverse-propagated boundary return.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:496`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:71`: `'AdalyFormal.Round2.Guarded.R2Prove.guarded_failure_forces_boundary_return' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-016](#bp-016) (`AdalyFormal.Round2.Guarded.R2Prove.carrier_isUnit_iff_response`); [bp-017](#bp-017) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round2/guarded/r2-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round2/guarded/r2-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round2/guarded/r2-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round2/guarded/r2-prove/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.response_sub_apply` (`AHP/round2/guarded/r2-prove/Attempt.lean:362`); `AdalyFormal.Round2.Guarded.R2Prove.exists_response_kernel` (`AHP/round2/guarded/r2-prove/Attempt.lean:388`); `AdalyFormal.Round2.Guarded.R2Prove.response_apply_ne_zero` (`AHP/round2/guarded/r2-prove/Attempt.lean:396`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round2/guarded/r2-prove/Attempt.lean:417`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem guarded_failure_forces_boundary_return
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    ∃ y : (boundaryShift P).range, y ≠ 0 ∧
      response (boundaryShift P) (localCorrected P) y = 0 ∧
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) ≠ 0
```

</details>

<a id="bp-020"></a>
#### bp-020 — `AdalyFormal.Round2.Guarded.R2Prove.goalPos1_iff_boundary_response`

The eventual guarded pencil statement is equivalent to the eventual corrected boundary-response statement, using the small-curvature localized bridges.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:542`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:79`: `'AdalyFormal.Round2.Guarded.R2Prove.goalPos1_iff_boundary_response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-017](#bp-017) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response`); [bp-013](#bp-013) (`AdalyFormal.Round2.Guarded.R2Prove.CBoundaryResponse`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round2/guarded/r2-prove/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round2/guarded/r2-prove/Attempt.lean:154`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_iff_boundary_response : GoalPos1 ↔ GShape CBoundaryResponse
```

</details>

<a id="bp-021"></a>
#### bp-021 — `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`

The guarded headline is equivalently the eventual corrected boundary-response unit condition.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:554`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:82`: `'AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-013](#bp-013) (`AdalyFormal.Round2.Guarded.R2Prove.CBoundaryResponse`); [bp-020](#bp-020) (`AdalyFormal.Round2.Guarded.R2Prove.goalPos1_iff_boundary_response`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round2/guarded/r2-prove/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round2/guarded/r2-prove/Attempt.lean:157`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_iff_boundary_response : GoalPos2 ↔ GShape CBoundaryResponse
```

</details>

<a id="bp-022"></a>
#### bp-022 — `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_of_no_boundary_return`

Class-wide vanishing of the boundary return is sufficient for the positive headline; that vanishing hypothesis is not supplied.

- **Source:** `AHP/round2/guarded/r2-prove/Attempt.lean:569`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round2/guarded/r2-prove/Attempt.lean.log:75`: `'AdalyFormal.Round2.Guarded.R2Prove.goalPos2_of_no_boundary_return' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-018](#bp-018) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_of_no_boundary_return`); [bp-014](#bp-014) (`AdalyFormal.Round2.Guarded.R2Prove.CNoBoundaryReturn`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round2/guarded/r2-prove/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round2/guarded/r2-prove/Attempt.lean:157`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_of_no_boundary_return (h : GShape CNoBoundaryReturn) : GoalPos2
```

</details>

<a id="bp-023"></a>
#### bp-023 — `AdalyFormal.Round3.Guarded.R3Prove.no_return_iff_mixed_boundary_source_zero`

With the displayed localized units, zero boundary return is equivalent to vanishing of the actual mixed source/second-jet pairing on boundary-propagated fields.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:826`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:172`: `'AdalyFormal.Round3.Guarded.R3Prove.no_return_iff_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/r3-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/r3-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/r3-prove/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.inverse_sub_apply` (`AHP/round3/guarded/r3-prove/Attempt.lean:428`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round3/guarded/r3-prove/Attempt.lean:495`); `AdalyFormal.Round3.Guarded.R3Prove.shift_zero_iff_range_pairing` (`AHP/round3/guarded/r3-prove/Attempt.lean:725`); `AdalyFormal.Round3.Guarded.R3Prove.mixedJetSource` (`AHP/round3/guarded/r3-prove/Attempt.lean:762`); `AdalyFormal.Round3.Guarded.R3Prove.boundaryShift_symmetric` (`AHP/round3/guarded/r3-prove/Attempt.lean:790`); `AdalyFormal.Round3.Guarded.R3Prove.resolvent_pairing_eq_mixed_jet` (`AHP/round3/guarded/r3-prove/Attempt.lean:804`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem no_return_iff_mixed_boundary_source_zero
    (hW : WellDefAt selIn selIn P) :
    (∀ y : (boundaryShift P).range,
      boundaryShift P (Ring.inverse (localCorrected P)
        ((dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
          (Ring.inverse (dataS selIn selIn P).Ginv y))) = 0) ↔
    (∀ y z : (boundaryShift P).range,
      mixedJetSource P (Ring.inverse (localCorrected P) z)
        (Ring.inverse (dataS selIn selIn P).Ginv y) = 0)
```

</details>

<a id="bp-024"></a>
#### bp-024 — `AdalyFormal.Round3.Guarded.R3Prove.mixed_boundary_zero_iff_diagonal`

Symmetry and polarization reduce the mixed boundary-source vanishing test to its diagonal form.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:858`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:152`: `'AdalyFormal.Round3.Guarded.R3Prove.mixed_boundary_zero_iff_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/r3-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/r3-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/r3-prove/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round3/guarded/r3-prove/Attempt.lean:495`); `AdalyFormal.Round3.Guarded.R3Prove.inverse_pairing` (`AHP/round3/guarded/r3-prove/Attempt.lean:715`); `AdalyFormal.Round3.Guarded.R3Prove.range_pairing_zero_iff_diagonal` (`AHP/round3/guarded/r3-prove/Attempt.lean:741`); `AdalyFormal.Round3.Guarded.R3Prove.mixedJetSource` (`AHP/round3/guarded/r3-prove/Attempt.lean:762`); `AdalyFormal.Round3.Guarded.R3Prove.localCorrected_symmetric` (`AHP/round3/guarded/r3-prove/Attempt.lean:796`); `AdalyFormal.Round3.Guarded.R3Prove.resolvent_pairing_eq_mixed_jet` (`AHP/round3/guarded/r3-prove/Attempt.lean:804`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem mixed_boundary_zero_iff_diagonal
    (hW : WellDefAt selIn selIn P) :
    (∀ y z : (boundaryShift P).range,
      mixedJetSource P (Ring.inverse (localCorrected P) z)
        (Ring.inverse (dataS selIn selIn P).Ginv y) = 0) ↔
    (∀ y : (boundaryShift P).range,
      mixedJetSource P (Ring.inverse (localCorrected P) y)
        (Ring.inverse (dataS selIn selIn P).Ginv y) = 0)
```

</details>

<a id="bp-025"></a>
#### bp-025 — `AdalyFormal.Round3.Guarded.R3Prove.guarded_failure_forces_positive_mixed_source`

A guarded corrected singularity forces a strictly positive mixed source witness under the localized bridge hypotheses.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:922`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:181`: `'AdalyFormal.Round3.Guarded.R3Prove.guarded_failure_forces_positive_mixed_source' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-019](#bp-019) (`AdalyFormal.Round2.Guarded.R2Prove.guarded_failure_forces_boundary_return`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/r3-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round3/guarded/r3-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/r3-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/r3-prove/Attempt.lean:62`); `AdalyFormal.Round3.Guarded.R3Prove.mixedJetSource` (`AHP/round3/guarded/r3-prove/Attempt.lean:762`); `AdalyFormal.Round3.Guarded.R3Prove.correction_pairing` (`AHP/round3/guarded/r3-prove/Attempt.lean:769`); `AdalyFormal.Round3.Guarded.R3Prove.return_norm_sq_eq_mixed_jet` (`AHP/round3/guarded/r3-prove/Attempt.lean:892`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem guarded_failure_forces_positive_mixed_source
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    ∃ y z : (boundaryShift P).range, y ≠ 0 ∧ z ≠ 0 ∧
      response (boundaryShift P) (localCorrected P) y = 0 ∧
      0 < mixedJetSource P (Ring.inverse (localCorrected P) z)
        (Ring.inverse (dataS selIn selIn P).Ginv y)
```

</details>

<a id="bp-026"></a>
#### bp-026 — `AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_mixed_boundary_source_zero`

Uniform mixed boundary-source invisibility would establish the guarded positive headline; this is a conditional positive alternative.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:962`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:185`: `'AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-246](#bp-246) (`AdalyFormal.Round3.Guarded.R3Prove.pencil_isUnit_of_mixed_boundary_source_zero`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round3/guarded/r3-prove/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round3/guarded/r3-prove/Attempt.lean:157`); `AdalyFormal.Round3.Guarded.R3Prove.CMixedBoundarySourceZero` (`AHP/round3/guarded/r3-prove/Attempt.lean:951`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_of_mixed_boundary_source_zero
    (h : GShape CMixedBoundarySourceZero) : GoalPos2
```

</details>

<a id="bp-027"></a>
#### bp-027 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`

The dilated slab tower satisfies all frozen admissibility clauses for positive scale and the stated even-radius hypotheses.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1024`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:133`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1024`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:133`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round3.Guarded.RefuteR2.zero_coord_le_pdist` (`AHP/round4/guarded/refute-r1/Attempt.lean:404`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_fine_size` (`AHP/round4/guarded/refute-r1/Attempt.lean:1001`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_fine_bound` (`AHP/round4/guarded/refute-r1/Attempt.lean:1006`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R)
```

</details>

<a id="bp-028"></a>
#### bp-028 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`

The dilated torus has the exact block-scale compatibility required by the pinned class.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1012`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:132`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_torus' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1012`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:132`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_torus' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_unit_size` (`AHP/round4/guarded/refute-r1/Attempt.lean:997`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_torus {q : ℕ} (hq : 0 < q) (R : ℕ) : TorusOK 2 (2*q) (dilLu q R)
```

</details>

<a id="bp-029"></a>
#### bp-029 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`

The chosen coarse domain satisfies the frozen admissible-test-domain condition.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1111`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:135`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1111`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:135`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round3.Guarded.RefuteR2.zero_coord_le_pdist` (`AHP/round4/guarded/refute-r1/Attempt.lean:404`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round4/guarded/refute-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_unit_size` (`AHP/round4/guarded/refute-r1/Attempt.lean:997`); `AdalyFormal.Round4.Guarded.RefuteR1.dilEmb` (`AHP/round4/guarded/refute-r1/Attempt.lean:1103`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_lambda {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R)
```

</details>

<a id="bp-030"></a>
#### bp-030 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`

The chosen coarse domain admits an actual admissible test field with strictly positive bond energy.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1156`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:138`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1156`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:138`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round4/guarded/refute-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_unit_size` (`AHP/round4/guarded/refute-r1/Attempt.lean:997`); `AdalyFormal.Round4.Guarded.RefuteR1.dilSeed` (`AHP/round4/guarded/refute-r1/Attempt.lean:1149`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round4/guarded/refute-r1/Attempt.lean:1153`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_competitor {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧
      OnLambdaT (dilLam q R) (dilBt hq R) ∧ 0 < bondEnergy (dilBt hq R)
```

</details>

<a id="bp-031"></a>
#### bp-031 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`

Both factor-12 coverage clauses hold for the dilated family; coverage is not a remaining spectral hypothesis.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1342`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:143`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1342`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:143`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_cube_neighborhood` (`AHP/round4/guarded/refute-r1/Attempt.lean:1284`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_shift_zero` (`AHP/round4/guarded/refute-r1/Attempt.lean:1331`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_coverage {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R) :
    CoversOm0p 2 (2*q) 12 1 (dilTower q R)
```

</details>

<a id="bp-032"></a>
#### bp-032 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`

Small interior defect amplitudes satisfy the full per-cube regularity condition for arbitrary exterior links.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1388`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:146`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_regular' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1388`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:146`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_regular' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilPattern` (`AHP/round4/guarded/refute-r1/Attempt.lean:1379`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round4/guarded/refute-r1/Attempt.lean:1383`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α ε : ℝ} (hα : 0 < α)
    (hε : |ε| ≤ α/80) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V)
```

</details>

<a id="bp-033"></a>
#### bp-033 — `AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor`

For every positive cap the dilated family has capped small curvature, all class/geometry conditions and a positive-energy competitor, independently of the exterior field.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1423`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:149`: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1423`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:149`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round4/guarded/refute-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round4/guarded/refute-r1/Attempt.lean:1153`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round4/guarded/refute-r1/Attempt.lean:1383`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU_nonflat` (`AHP/round4/guarded/refute-r1/Attempt.lean:1408`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_in_class_nonflat_competitor {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    {a₀ : ℝ} (ha₀ : 0 < a₀) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    ∃ α ε : ℝ, 0 < α ∧ (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ ∧ 0 < ε ∧ ε < 1 ∧
      TorusOK 2 (2*q) (dilLu q R) ∧ Admissible 2 (2*q) R 1 (dilTower q R) ∧
      LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) ∧
      ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) ∧
      OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧ OnLambdaT (dilLam q R) (dilBt hq R) ∧
      0 < bondEnergy (dilBt hq R) ∧
      ∃ e : Bond (scaleUp 2 1 (dilLu q R)), e.1 ∈ (dilTower q R).Om 0 ∧ dilU q R ε V e ≠ 1
```

</details>

<a id="bp-034"></a>
#### bp-034 — `AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor`

The complete nonspectral witness construction has the required nested scale/radius/cap ordering and genuine interior curvature. It supplies neither spectral unit condition.

- **Source:** `AHP/round4/guarded/refute-r1/Attempt.lean:1599`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/refute-r1/Attempt.lean.log:158`: `'AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1599`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:158`, exit `0`; record: `'AdalyFormal.Round4.Guarded.RefuteR1.cofinal_in_class_curved_competitor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-033](#bp-033) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round4/guarded/refute-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round4/guarded/refute-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round4/guarded/refute-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round4/guarded/refute-r1/Attempt.lean:1153`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round4/guarded/refute-r1/Attempt.lean:1383`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU_curved` (`AHP/round4/guarded/refute-r1/Attempt.lean:1551`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU_not_pure_gauge` (`AHP/round4/guarded/refute-r1/Attempt.lean:1558`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_in_class_curved_competitor :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 17*2 ≤ R*(2^m) ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ)*(2^m : ℕ)*α₀ ≤ a₀)
            (_ : TorusOK 2 (2^m) Lu)
            (S : Tower (scaleUp 2 k Lu)) (_ : Admissible 2 (2^m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 2 (2^m) R k S Lam)
            (U : LinkCfg (scaleUp 2 k Lu))
            (_ : ClassCoupled 2 (2^m) 12 k S α₀ ((2 : ℝ)^k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            (∃ e : Bond (scaleUp 2 k Lu), e.1 ∈ S.Om 0 ∧ U e ≠ 1) ∧
            (∃ p ∈ plaqIn (S.Om 0), periodicPlaquetteHolonomy U p ≠ 1) ∧
            (¬ ∃ g : PeriodicLatticeSite (scaleUp 2 k Lu) → G2,
              periodicGaugeTransform g U = fun _ => (1 : G2))
```

</details>

<a id="bp-035"></a>
#### bp-035 — `AdalyFormal.Round4.Guarded.GapR1.delta2_norm_le_source`

The genuine correction norm is bounded linearly by source smallness under the stated raw-jet and weighted-dressing bounds, with no unjustified quadratic smallness gain.

- **Source:** `AHP/round4/guarded/gap-r1/Check3.lean:412`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/gap-r1/Check3.lean.log:83`: `'AdalyFormal.Round4.Guarded.GapR1.delta2_norm_le_source' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/gap-r1/Check3.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/gap-r1/Check3.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/gap-r1/Check3.lean:62`); `AdalyFormal.Round4.Guarded.GapR1.delta2_norm_le_weighted` (`AHP/round4/guarded/gap-r1/Check3.lean:398`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem delta2_norm_le_source (P : IngrBParams) (hell : 1 ≤ P.ell)
    (L t K2 CW : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) (hK : 0 ≤ K2) (hCW : 0 ≤ CW)
    (hψ : ∀ p, ‖AdalyFormal.DLayer.psiD P p‖ ≤ L * t)
    (hC : ∀ z : BondFnL2 P.Lf, ∑ p, ‖C2fullOf P.G P.U z p‖ ≤
      K2 * wnormSq P.S P.ell P.k z)
    (hW : ∀ x : ↥(bondSupp P.G),
      wnormSq P.S P.ell P.k (Wop P.G P.U P.a (iE P.G x)) ≤
        CW * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) :
    ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ ≤
      (2 * L * K2 * CW) * t
```

</details>

<a id="bp-036"></a>
#### bp-036 — `AdalyFormal.Round4.Guarded.GapR1.pencil_isUnit_of_weighted_boundary_gap`

A localized coercivity margin exceeding the correction and negative boundary-shift bounds forces \(A-D\) to be a unit.

- **Source:** `AHP/round4/guarded/gap-r1/Check3.lean:476`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/gap-r1/Check3.lean.log:86`: `'AdalyFormal.Round4.Guarded.GapR1.pencil_isUnit_of_weighted_boundary_gap' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/gap-r1/Check3.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round4/guarded/gap-r1/Check3.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/gap-r1/Check3.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/gap-r1/Check3.lean:62`); `AdalyFormal.Round4.Guarded.GapR1.pencil_weighted_lower` (`AHP/round4/guarded/gap-r1/Check3.lean:454`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_weighted_boundary_gap (P : IngrBParams) (hell : 1 ≤ P.ell)
    (cw ε β : ℝ) (hgap : ε + β < cw)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (hΘ : ∀ x : ↥(bondSupp P.G),
      -(β * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ≤
        ⟪x, boundaryShift P x⟫) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-037"></a>
#### bp-037 — `AdalyFormal.Round4.Guarded.GapR1.pencil_failure_forces_negative_boundary_energy`

With localized coercivity and a smaller correction, corrected singularity forces a nonzero kernel vector with strictly negative boundary-shift energy.

- **Source:** `AHP/round4/guarded/gap-r1/Check3.lean:505`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/gap-r1/Check3.lean.log:89`: `'AdalyFormal.Round4.Guarded.GapR1.pencil_failure_forces_negative_boundary_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/gap-r1/Check3.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round4/guarded/gap-r1/Check3.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/gap-r1/Check3.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/gap-r1/Check3.lean:62`); `AdalyFormal.Round4.Guarded.GapR1.weighted_norm_pos` (`AHP/round4/guarded/gap-r1/Check3.lean:387`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_failure_forces_negative_boundary_energy
    (P : IngrBParams) (hell : 1 ≤ P.ell) (cw ε : ℝ) (hgap : ε < cw)
    (hB : ∀ x : ↥(bondSupp P.G),
      cw * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf) ≤
        ⟪x, (dataS selIn selIn P).Ginv x⟫)
    (hD : ∀ x : ↥(bondSupp P.G),
      |⟪x, (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x⟫| ≤
        ε * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf))
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))) :
    ∃ x : ↥(bondSupp P.G), x ≠ 0 ∧
      ((dataS selAll selAll P).Ginv -
        (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) x = 0 ∧
      ⟪x, boundaryShift P x⟫ ≤
        -((cw - ε) * wnormSq P.S P.ell P.k (x : BondFnL2 P.Lf)) ∧
      ⟪x, boundaryShift P x⟫ < 0
```

</details>

<a id="bp-038"></a>
#### bp-038 — `AdalyFormal.Round4.Guarded.GapR1.scalar_gap_obstruction`

An exact scalar example has uniformly positive localized carriers and arbitrarily small correction, but an invertible all-carrier with singular corrected pencil. This is not a lattice counterexample.

- **Source:** `AHP/round4/guarded/gap-r1/Check3.lean:550`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/gap-r1/Check3.lean.log:92`: `'AdalyFormal.Round4.Guarded.GapR1.scalar_gap_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem scalar_gap_obstruction (cap : ℝ) (hcap : 0 < cap) :
    ∃ (B D Θ : ℝ), B = 1 ∧ 0 < D ∧ |D| < cap ∧ 3 / 4 ≤ B - D ∧
      Θ ≠ 0 ∧ IsUnit B ∧ IsUnit (B - D) ∧ IsUnit (B + Θ) ∧
      ¬ IsUnit (B + Θ - D) ∧
      0 < |1 + Θ / B| ∧ |1 + Θ / B| < cap ∧ 1 + Θ / (B - D) = 0
```

</details>

<a id="bp-039"></a>
#### bp-039 — `AdalyFormal.Round4.Guarded.GapR1.inverse_response_norm_of_carrier_lower`

A quantitative lower bound for the full carrier, not merely its unit status, controls the inverse boundary response.

- **Source:** `AHP/round4/guarded/gap-r1/Check3.lean:623`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/gap-r1/Check3.lean.log:77`: `'AdalyFormal.Round4.Guarded.GapR1.inverse_response_norm_of_carrier_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.GapR1.response_lower_of_carrier_lower` (`AHP/round4/guarded/gap-r1/Check3.lean:604`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem inverse_response_norm_of_carrier_lower (Θ B : E →L[ℝ] E)
    (hB : IsUnit B) (hK : IsUnit (response Θ B)) (g : ℝ) (hg : 0 < g)
    (hA : ∀ x : E, g * ‖x‖ ≤ ‖(B + Θ) x‖) :
    ‖Ring.inverse (response Θ B)‖ ≤ ‖B‖ / g
```

</details>

<a id="bp-040"></a>
#### bp-040 — `AdalyFormal.Round3.Guarded.R2Prove.correction_kills_jetInputZero`

The actual correction annihilates the subspace whose dressed input is invisible to the quadratic blocking jet.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:621`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:104`: `'AdalyFormal.Round3.Guarded.R2Prove.correction_kills_jetInputZero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/decay-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/decay-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/decay-r1/Attempt.lean:62`); `AdalyFormal.Round3.Guarded.R2Prove.correction_kills_of_jet_translation` (`AHP/round4/guarded/decay-r1/Attempt.lean:551`); `AdalyFormal.Round3.Guarded.R2Prove.jetInputZero` (`AHP/round4/guarded/decay-r1/Attempt.lean:578`); `AdalyFormal.Round3.Guarded.R2Prove.jet_translation_of_jetInputZero` (`AHP/round4/guarded/decay-r1/Attempt.lean:594`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem correction_kills_jetInputZero
    (x : ↥(bondSupp P.G)) (hx : x ∈ jetInputZero P) :
    (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) x = 0
```

</details>

<a id="bp-041"></a>
#### bp-041 — `AdalyFormal.Round4.Guarded.DecayR1.actual_return_norm_le_two_pass`

Observed two-pass propagation bounds control the actual boundary return under the explicit inverse and observation hypotheses.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:842`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:134`: `'AdalyFormal.Round4.Guarded.DecayR1.actual_return_norm_le_two_pass' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-040](#bp-040) (`AdalyFormal.Round3.Guarded.R2Prove.correction_kills_jetInputZero`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/decay-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/decay-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/decay-r1/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round4/guarded/decay-r1/Attempt.lean:463`); `AdalyFormal.Round3.Guarded.R2Prove.jetInputZero` (`AHP/round4/guarded/decay-r1/Attempt.lean:578`); `AdalyFormal.Round4.Guarded.DecayR1.response_sub_norm_le_two_pass` (`AHP/round4/guarded/decay-r1/Attempt.lean:764`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round4/guarded/decay-r1/Attempt.lean:825`); `AdalyFormal.Round4.Guarded.DecayR1.boundaryShift_symmetric` (`AHP/round4/guarded/decay-r1/Attempt.lean:828`); `AdalyFormal.Round4.Guarded.DecayR1.localCorrected_symmetric` (`AHP/round4/guarded/decay-r1/Attempt.lean:834`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem actual_return_norm_le_two_pass
    (hW : WellDefAt selIn selIn P) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    ‖response (boundaryShift P) (localCorrected P) -
      response (boundaryShift P) (dataS selIn selIn P).Ginv‖ ≤
        ‖boundaryShift P‖ *
          ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c
```

</details>

<a id="bp-042"></a>
#### bp-042 — `AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_two_pass_decay`

A sufficiently small inverse-relative boundary return preserves the corrected pencil unit; the required decay is not inferred from localized coercivity.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:860`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:137`: `'AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_two_pass_decay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-016](#bp-016) (`AdalyFormal.Round2.Guarded.R2Prove.carrier_isUnit_iff_response`); [bp-017](#bp-017) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response`); [bp-041](#bp-041) (`AdalyFormal.Round4.Guarded.DecayR1.actual_return_norm_le_two_pass`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/decay-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round4/guarded/decay-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/decay-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/decay-r1/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.DecayR1.response_isUnit_of_absolute_small` (`AHP/round4/guarded/decay-r1/Attempt.lean:810`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round4/guarded/decay-r1/Attempt.lean:825`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_two_pass_decay
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖)
    (hsmall : ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c) < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-043"></a>
#### bp-043 — `AdalyFormal.Round4.Guarded.DecayR1.guarded_failure_requires_amplification`

A guarded failure forces the corresponding inverse-response amplification to reach the obstruction threshold.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:905`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:113`: `'AdalyFormal.Round4.Guarded.DecayR1.guarded_failure_requires_amplification' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-042](#bp-042) (`AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_two_pass_decay`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/decay-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round4/guarded/decay-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/decay-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/decay-r1/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round4/guarded/decay-r1/Attempt.lean:825`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem guarded_failure_requires_amplification
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hbad : ¬ IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbt : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (dataS selIn selIn P).Ginv y)‖ ≤ b * ‖y‖)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    1 ≤ ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * b * c)
```

</details>

<a id="bp-044"></a>
#### bp-044 — `AdalyFormal.Round4.Guarded.DecayR1.goalPos2_of_two_pass_decay`

A class-wide two-pass smallness bound would prove the guarded positive headline; the bound remains an open alternative.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:941`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:117`: `'AdalyFormal.Round4.Guarded.DecayR1.goalPos2_of_two_pass_decay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-042](#bp-042) (`AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_two_pass_decay`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round4/guarded/decay-r1/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round4/guarded/decay-r1/Attempt.lean:157`); `AdalyFormal.Round4.Guarded.DecayR1.CTwoPassSmall` (`AHP/round4/guarded/decay-r1/Attempt.lean:924`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_of_two_pass_decay (h : GShape CTwoPassSmall) : GoalPos2
```

</details>

<a id="bp-045"></a>
#### bp-045 — `AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed`

The actual inverse-relative return is bounded by the observed propagator estimate under the localized and carrier inverse guards.

- **Source:** `AHP/round5/guarded/structural-r1/Attempt.lean:1101`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/structural-r1/Attempt.lean.log:158`: `'AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-040](#bp-040) (`AdalyFormal.Round3.Guarded.R2Prove.correction_kills_jetInputZero`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/structural-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/structural-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/structural-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round5/guarded/structural-r1/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round5/guarded/structural-r1/Attempt.lean:463`); `AdalyFormal.Round2.Guarded.R2Prove.carrier_eq_local_add_shift` (`AHP/round5/guarded/structural-r1/Attempt.lean:468`); `AdalyFormal.Round3.Guarded.R2Prove.jetInputZero` (`AHP/round5/guarded/structural-r1/Attempt.lean:578`); `AdalyFormal.Round4.Guarded.DecayR1.relativeReturn` (`AHP/round5/guarded/structural-r1/Attempt.lean:650`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round5/guarded/structural-r1/Attempt.lean:825`); `AdalyFormal.Round4.Guarded.DecayR1.boundaryShift_symmetric` (`AHP/round5/guarded/structural-r1/Attempt.lean:828`); `AdalyFormal.Round4.Guarded.DecayR2.relativeReturn_norm_le_observed` (`AHP/round5/guarded/structural-r1/Attempt.lean:1028`); `AdalyFormal.Round4.Guarded.DecayR2.observedGuardTransfer` (`AHP/round5/guarded/structural-r1/Attempt.lean:1081`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem actual_relative_return_norm_le_observed (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖) :
    ‖relativeReturn (boundaryShift P) (dataS selIn selIn P).Ginv (localCorrected P)‖ ≤
      ‖observedGuardTransfer P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c
```

</details>

<a id="bp-046"></a>
#### bp-046 — `AdalyFormal.Round4.Guarded.DecayR2.goalPos2_of_observed_guard_decay`

Uniform observed guard-relative decay suffices for the positive headline. It is not established by small absolute boundary tails.

- **Source:** `AHP/round5/guarded/structural-r1/Attempt.lean:1166`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/structural-r1/Attempt.lean.log:147`: `'AdalyFormal.Round4.Guarded.DecayR2.goalPos2_of_observed_guard_decay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-252](#bp-252) (`AdalyFormal.Round4.Guarded.DecayR2.pencil_isUnit_of_observed_guard_decay`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round5/guarded/structural-r1/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round5/guarded/structural-r1/Attempt.lean:157`); `AdalyFormal.Round4.Guarded.DecayR2.CObservedGuardSmall` (`AHP/round5/guarded/structural-r1/Attempt.lean:1152`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_of_observed_guard_decay (h : GShape CObservedGuardSmall) : GoalPos2
```

</details>

<a id="bp-047"></a>
#### bp-047 — `AdalyFormal.Round5.Guarded.IVTR1.guarded_separation_of_kernel_positive`

A continuous symmetric carrier path with a guarded initial interval and positive correction on an endpoint kernel produces an earlier carrier-unit/corrected-nonunit point.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:1666`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:161`: `'AdalyFormal.Round5.Guarded.IVTR1.guarded_separation_of_kernel_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1666`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:161`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR1.guarded_separation_of_kernel_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem guarded_separation_of_kernel_positive
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (hsA : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hsD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (h0 : AdalyFormal.D1Literal.PSD (A 0 - D))
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (A t))
    (v : E) (hker : A T v = 0) (hpositive : 0 < ⟪v, D v⟫) :
    ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ IsUnit (A t) ∧ ¬ IsUnit (A t - D)
```

</details>

<a id="bp-048"></a>
#### bp-048 — `AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path`

Changing only exterior links changes the all-carrier by the dressed difference of exterior plaquette Hessians; the dressing is fixed along that path.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:1798`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:165`: `'AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1798`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:165`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.PlaqSel` (`AHP/round5/guarded/ivt-r2/Attempt.lean:31`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/ivt-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.DeltaS` (`AHP/round5/guarded/ivt-r2/Attempt.lean:40`); `AdalyFormal.Round2.Guarded.Pin.DpiFullS` (`AHP/round5/guarded/ivt-r2/Attempt.lean:43`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/ivt-r2/Attempt.lean:58`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exterior_carrier_path (sJ : PlaqSel) (t : ℝ) :
    (dataS selAll sJ (gparams ell k Lu hell0 S (U t) a Lam)).Ginv =
      (dataS selAll sJ (gparams ell k Lu hell0 S (U 0) a Lam)).Ginv +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop (geomOf ell k S) (U 0) a))).comp (iE (geomOf ell k S)))
```

</details>

<a id="bp-049"></a>
#### bp-049 — `AdalyFormal.Round5.Guarded.IVTR1.twistD_constant`

The genuine localized correction is independent of the exterior twist angle.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:1742`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:174`: `'AdalyFormal.Round5.Guarded.IVTR1.twistD_constant' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1742`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:174`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR1.twistD_constant' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round5/guarded/ivt-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/ivt-r2/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1713`); `AdalyFormal.Round5.Guarded.IVTR1.twist_data_constant` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1734`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ) :
    twistD q R ε a t = twistD q R ε a 0
```

</details>

<a id="bp-050"></a>
#### bp-050 — `AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings`

Cofinal actual positive-kernel crossing data imply the pinned negative goal with all class bookkeeping retained.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:1888`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:180`: `'AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1888`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:180`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round5/guarded/ivt-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/ivt-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round5/guarded/ivt-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1153`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1703`); `AdalyFormal.Round5.Guarded.IVTR1.twist_separation_of_kernel_positive` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1843`); `AdalyFormal.Round5.Guarded.IVTR1.KernelPositiveCrossing` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1878`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_twist_crossings
    (hcross : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ KernelPositiveCrossing q R ε) :
    GoalNeg2
```

</details>

<a id="bp-051"></a>
#### bp-051 — `AdalyFormal.Round5.Guarded.IVTR2.first_carrier_crossing`

Continuity, initial positivity and invertibility, and a negative endpoint yield the first PSD singular carrier point and the preceding full-carrier unit interval.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:1950`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:183`: `'AdalyFormal.Round5.Guarded.IVTR2.first_carrier_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:1950`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:183`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR2.first_carrier_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem first_carrier_crossing
    (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hp0 : PSD (A 0)) (hu0 : IsUnit (A 0))
    (T : ℝ) (hT : 0 < T) (z : E) (hz : ⟪z, A T z⟫ < 0) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ PSD (A t) ∧ ¬ IsUnit (A t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t → PSD (A s) ∧ IsUnit (A s)) ∧
      ∃ v : E, v ≠ 0 ∧ A t v = 0
```

</details>

<a id="bp-052"></a>
#### bp-052 — `AdalyFormal.Round5.Guarded.IVTR2.twistA_pi_negative`

The actual curved twist has a negative carrier direction at angle \(\pi\) under the displayed geometric and mass hypotheses.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:2288`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:206`: `'AdalyFormal.Round5.Guarded.IVTR2.twistA_pi_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2288`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:206`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR2.twistA_pi_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/ivt-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/ivt-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/ivt-r2/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1703`); `AdalyFormal.Round5.Guarded.IVTR1.twistP` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1706`); `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round5/guarded/ivt-r2/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR2.rightSite` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2198`); `AdalyFormal.Round5.Guarded.IVTR2.rightSite_bd` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2203`); `AdalyFormal.Round5.Guarded.IVTR2.twist_delta_pi` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2260`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistA_pi_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε : ℝ) :
    ∃ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪v, twistA q R ε 1 Real.pi v⟫ < 0
```

</details>

<a id="bp-053"></a>
#### bp-053 — `AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_endpoint_signs`

The endpoint/sign crossing hypotheses suffice for a cofinal guarded refutation; they are not all proved for the curved family.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:2099`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:195`: `'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_endpoint_signs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2099`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:195`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_endpoint_signs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-050](#bp-050) (`AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR2.EndpointSignControl` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2079`); `AdalyFormal.Round5.Guarded.IVTR2.kernelPositiveCrossing_of_endpoint_signs` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2088`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_endpoint_signs
    (hsigns : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ EndpointSignControl q R ε) :
    GoalNeg2
```

</details>

<a id="bp-054"></a>
#### bp-054 — `AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control`

Arbitrarily-small-amplitude initial kernel control would refute the headline. In particular the positive correction pairing remains a hypothesis.

- **Source:** `AHP/round5/guarded/ivt-r2/Attempt.lean:2382`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/ivt-r2/Attempt.lean.log:214`: `'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2382`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:214`, exit `0`; record: `'AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_initial_kernel_control' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-053](#bp-053) (`AdalyFormal.Round5.Guarded.IVTR2.goalNeg2_of_endpoint_signs`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR2.InitialKernelControl` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2368`); `AdalyFormal.Round5.Guarded.IVTR2.endpoint_control_of_initial_kernel` (`AHP/round5/guarded/ivt-r2/Attempt.lean:2376`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_initial_kernel_control
    (hcontrol : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ InitialKernelControl q R ε) :
    GoalNeg2
```

</details>

<a id="bp-055"></a>
#### bp-055 — `AdalyFormal.Round5.Guarded.KernelR2.dil_local_data_exterior_independent`

At fixed interior amplitudes the actual localized data and correction do not change when exterior links are retuned.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2442`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:261`: `'AdalyFormal.Round5.Guarded.KernelR2.dil_local_data_exterior_independent' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/kernel-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/kernel-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round5/guarded/kernel-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/kernel-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round5/guarded/kernel-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1383`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_local_data_exterior_independent {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 34 ≤ R * (2*q)) (ε a : ℝ)
    (V V' : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (dilU q R ε V') a (dilLam q R)) =
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (dilU q R ε V) a (dilLam q R))
```

</details>

<a id="bp-056"></a>
#### bp-056 — `AdalyFormal.Round5.Guarded.KernelR1.actual_two_mode_separation`

Exact full-vector two-mode identities and complementary injectivity yield actual carrier-unit/corrected-kernel separation; compressed entries alone do not satisfy the hypotheses.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2326`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:236`: `'AdalyFormal.Round5.Guarded.KernelR1.actual_two_mode_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/kernel-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/kernel-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/kernel-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round5/guarded/kernel-r2/Attempt.lean:62`); `AdalyFormal.Round5.Guarded.KernelR1.two_mode_unit` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2247`); `AdalyFormal.Round5.Guarded.KernelR1.two_mode_kernel` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2277`); `AdalyFormal.Round5.Guarded.KernelR1.ExactModes` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2313`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem actual_two_mode_separation (P : IngrBParams) (h : ExactModes P) :
    IsUnit (dataS selAll selAll P).Ginv ∧
      ∃ z : ↥(bondSupp P.G), z ≠ 0 ∧
        ((dataS selAll selAll P).Ginv -
          (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) z = 0
```

</details>

<a id="bp-057"></a>
#### bp-057 — `AdalyFormal.Round5.Guarded.KernelR1.goalNeg2_of_dil_modes`

A cofinal realization of the full two-mode model would refute the pinned headline; no such physical realization is supplied.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2415`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:249`: `'AdalyFormal.Round5.Guarded.KernelR1.goalNeg2_of_dil_modes' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-249](#bp-249) (`AdalyFormal.Round5.Guarded.KernelR1.cofinalPencilFailure_of_dil_modes`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.KernelR1.DilModeRealisation` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2377`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_dil_modes (h : DilModeRealisation) : GoalNeg2
```

</details>

<a id="bp-058"></a>
#### bp-058 — `AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation`

Exact Schur block identities and both complementary units reconstruct a nonzero full corrected kernel and certify the full carrier unit.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2608`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:270`: `'AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/kernel-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/kernel-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/kernel-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round5/guarded/kernel-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.GapR2.Plane` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1768`); `AdalyFormal.Round4.Guarded.GapR2.block` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1771`); `AdalyFormal.Round4.Guarded.GapR2.block_unit` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1799`); `AdalyFormal.Round5.Guarded.KernelR2.corner22` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2490`); `AdalyFormal.Round5.Guarded.KernelR2.schur` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2496`); `AdalyFormal.Round5.Guarded.KernelR2.liftKernel` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2499`); `AdalyFormal.Round5.Guarded.KernelR2.liftKernel_ne_zero` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2528`); `AdalyFormal.Round5.Guarded.KernelR2.liftKernel_mem_kernel` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2535`); `AdalyFormal.Round5.Guarded.KernelR2.unit_of_schur_unit` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2544`); `AdalyFormal.Round5.Guarded.KernelR2.planeKernel` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2592`); `AdalyFormal.Round5.Guarded.KernelR2.planeKernel_ne_zero` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2594`); `AdalyFormal.Round5.Guarded.KernelR2.planeKernel_killed` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2599`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem actual_schur_separation (P : IngrBParams) (n : ℕ)
    (e : ↥(bondSupp P.G) ≃L[ℝ] (Plane × EuclideanSpace ℝ (Fin n)))
    (t d : ℝ) (ht : t ≠ 0) (hd : d ≠ 0)
    (hA22 : IsUnit (corner22 e (dataS selAll selAll P).Ginv))
    (hC22 : IsUnit (corner22 e ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))))
    (hSA : schur e (dataS selAll selAll P).Ginv = block (t^2) t (1+d))
    (hSC : schur e ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) = block (t^2) t 1) :
    IsUnit (dataS selAll selAll P).Ginv ∧
    let z
```

</details>

<a id="bp-059"></a>
#### bp-059 — `AdalyFormal.Round5.Guarded.KernelR2.goalNeg2_of_dil_schur`

A cofinal physical Schur realization implies the negative goal; the realization remains an open alternative to the crossing route.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2691`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:279`: `'AdalyFormal.Round5.Guarded.KernelR2.goalNeg2_of_dil_schur' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-251](#bp-251) (`AdalyFormal.Round5.Guarded.KernelR2.cofinalPencilFailure_of_dil_schur`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.KernelR2.DilSchurRealisation` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2654`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_dil_schur (h : DilSchurRealisation) : GoalNeg2
```

</details>

<a id="bp-060"></a>
#### bp-060 — `AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry`

Two-site translations act orthogonally on the actual touching-bond carrier and preserve the background and holonomies. This alone is not commutation of the assembled operators.

- **Source:** `AHP/round6/closedform-r1/Attempt.lean:2643`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/closedform-r1/Attempt.lean.log:254`: `'AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_exact_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round6/closedform-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/closedform-r1/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round6/closedform-r1/Attempt.lean:1703`); `AdalyFormal.Round6.Guarded.ClosedFormR1.bondTranslation` (`AHP/round6/closedform-r1/Attempt.lean:2423`); `AdalyFormal.Round6.Guarded.ClosedFormR1.carrierTranslation` (`AHP/round6/closedform-r1/Attempt.lean:2499`); `AdalyFormal.Round6.Guarded.ClosedFormR1.carrierTranslation_apply` (`AHP/round6/closedform-r1/Attempt.lean:2508`); `AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite` (`AHP/round6/closedform-r1/Attempt.lean:2515`); `AdalyFormal.Round6.Guarded.ClosedFormR1.twoSite_zero` (`AHP/round6/closedform-r1/Attempt.lean:2518`); `AdalyFormal.Round6.Guarded.ClosedFormR1.twistU_twoSite` (`AHP/round6/closedform-r1/Attempt.lean:2549`); `AdalyFormal.Round6.Guarded.ClosedFormR1.twist_holonomy_twoSite` (`AHP/round6/closedform-r1/Attempt.lean:2558`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twoSite_exact_symmetry {q : ℕ} (hq : 0 < q) (R : ℕ) (ε t : ℝ)
    (μ : Fin 3) (hμ : μ ≠ 0) :
    ∃ T : ↥(bondSupp (geomOf 2 1 (dilTower q R))) ≃ₗᵢ[ℝ]
        ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      (∀ v : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
        ∀ e : Bond (scaleUp 2 1 (dilLu q R)),
        (T v : BondFnL2 _) e = (v : BondFnL2 _) (bondTranslation (twoSite q R μ) e)) ∧
      (∀ e : Bond (scaleUp 2 1 (dilLu q R)),
        twistU q R ε t (bondTranslation (twoSite q R μ) e) = twistU q R ε t e) ∧
      (∀ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        periodicPlaquetteHolonomy (twistU q R ε t) (p.1 + twoSite q R μ, p.2) =
          periodicPlaquetteHolonomy (twistU q R ε t) p)
```

</details>

<a id="bp-061"></a>
#### bp-061 — `AdalyFormal.Round6.Guarded.LimitsR1.twistD_zero_amplitude`

At zero interior curvature the genuine correction vanishes, independently of the exterior twist.

- **Source:** `AHP/round6/limits-r2/Attempt.lean:2421`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/limits-r2/Attempt.lean.log:217`: `'AdalyFormal.Round6.Guarded.LimitsR1.twistD_zero_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round6/limits-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/limits-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round6/limits-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/limits-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round6/limits-r2/Attempt.lean:1383`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round6/limits-r2/Attempt.lean:1703`); `AdalyFormal.Round5.Guarded.IVTR1.twistP` (`AHP/round6/limits-r2/Attempt.lean:1706`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round6/limits-r2/Attempt.lean:1713`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistD_zero_amplitude {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (h3 : 3 ≤ R * (2*q)) (a t : ℝ) : twistD q R 0 a t = 0
```

</details>

<a id="bp-062"></a>
#### bp-062 — `AdalyFormal.Round6.Guarded.LimitsR1.not_initial_control_zero`

The zero-amplitude family cannot supply the strictly positive correction required by initial kernel control.

- **Source:** `AHP/round6/limits-r2/Attempt.lean:2487`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/limits-r2/Attempt.lean.log:230`: `'AdalyFormal.Round6.Guarded.LimitsR1.not_initial_control_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR2.InitialKernelControl` (`AHP/round6/limits-r2/Attempt.lean:2368`); `AdalyFormal.Round6.Guarded.LimitsR1.vacuum_correction_pairing` (`AHP/round6/limits-r2/Attempt.lean:2445`); `AdalyFormal.Round6.Guarded.LimitsR1.not_initial_control_of_correction_nonpositive` (`AHP/round6/limits-r2/Attempt.lean:2476`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem not_initial_control_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) : ¬ InitialKernelControl q R 0
```

</details>

<a id="bp-063"></a>
#### bp-063 — `AdalyFormal.Round6.Guarded.LimitsR2.twistD_kills_interiorInvisible`

The correction annihilates every field whose dressed input vanishes on all both-endpoint interior bonds.

- **Source:** `AHP/round6/limits-r2/Attempt.lean:2713`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/limits-r2/Attempt.lean.log:261`: `'AdalyFormal.Round6.Guarded.LimitsR2.twistD_kills_interiorInvisible' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round6/limits-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/limits-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round6/limits-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/limits-r2/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round6/limits-r2/Attempt.lean:1703`); `AdalyFormal.Round5.Guarded.IVTR1.twistP` (`AHP/round6/limits-r2/Attempt.lean:1706`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round6/limits-r2/Attempt.lean:1713`); `AdalyFormal.Round3.Guarded.R2Prove.correction_kills_of_jet_translation` (`AHP/round6/limits-r2/Attempt.lean:2580`); `AdalyFormal.Round6.Guarded.LimitsR2.interiorInvisible` (`AHP/round6/limits-r2/Attempt.lean:2700`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistD_kills_interiorInvisible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ)
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hv : v ∈ interiorInvisible q R ε a t) : twistD q R ε a t v = 0
```

</details>

<a id="bp-064"></a>
#### bp-064 — `AdalyFormal.Round6.Guarded.LimitsR2.no_invisible_negative_test`

At a PSD carrier point an invisible vector cannot be a negative corrected test direction.

- **Source:** `AHP/round6/limits-r2/Attempt.lean:2786`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/limits-r2/Attempt.lean.log:276`: `'AdalyFormal.Round6.Guarded.LimitsR2.no_invisible_negative_test' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-049](#bp-049) (`AdalyFormal.Round5.Guarded.IVTR1.twistD_constant`); [bp-063](#bp-063) (`AdalyFormal.Round6.Guarded.LimitsR2.twistD_kills_interiorInvisible`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/limits-r2/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round6/limits-r2/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round6/limits-r2/Attempt.lean:1713`); `AdalyFormal.Round6.Guarded.LimitsR2.interiorInvisible` (`AHP/round6/limits-r2/Attempt.lean:2700`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem no_invisible_negative_test {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q)) (ε a t : ℝ)
    (hpsd : PSD (twistA q R ε a t))
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hv : v ∈ interiorInvisible q R ε a t) :
    0 ≤ ⟪v, (twistA q R ε a t - twistD q R ε a 0) v⟫
```

</details>

<a id="bp-065"></a>
#### bp-065 — `AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero`

Curvature confined to sufficiently separated outer boundary strips has exactly zero correction, even without inverse hypotheses; that placement cannot separate \(A\) from \(A-D\).

- **Source:** `AHP/round6/placement-r1/Attempt.lean:2749`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/placement-r1/Attempt.lean.log:252`: `'AdalyFormal.Round6.Guarded.PlacementR1.boundary_strip_correction_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round6/placement-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/placement-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round6/placement-r1/Attempt.lean:62`); `AdalyFormal.Round3.Guarded.RefuteR2.zero_coord_le_pdist` (`AHP/round6/placement-r1/Attempt.lean:404`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round6/placement-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/placement-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round6/placement-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_fine_size` (`AHP/round6/placement-r1/Attempt.lean:1001`); `AdalyFormal.Round4.Guarded.RefuteR1.dil_fine_bound` (`AHP/round6/placement-r1/Attempt.lean:1006`); `AdalyFormal.Round5.Guarded.IVTR2.maskedU` (`AHP/round6/placement-r1/Attempt.lean:2118`); `AdalyFormal.Round6.Guarded.PlacementR1.correction_zero_of_flat_near_top` (`AHP/round6/placement-r1/Attempt.lean:2423`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem boundary_strip_correction_zero {q R d : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hgap : d+3 ≤ 2*(R*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hf : ∀ e, 4*q+d ≤ (e.1 0).val → (e.1 0).val+d < 12*(R*q)+12*q → f e = 0)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) (a : ℝ) :
    let P
```

</details>

<a id="bp-066"></a>
#### bp-066 — `AdalyFormal.Round6.Guarded.PlacementR1.cofinal_curved_placement_no_separation`

A genuinely curved cofinal boundary-placement family satisfies the class but cannot distinguish the two unit conditions because its correction is zero.

- **Source:** `AHP/round6/placement-r1/Attempt.lean:2691`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/placement-r1/Attempt.lean.log:249`: `'AdalyFormal.Round6.Guarded.PlacementR1.cofinal_curved_placement_no_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-005](#bp-005) (`AdalyFormal.Round2.Guarded.Pin.CPen`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round6/placement-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/placement-r1/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round6/placement-r1/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/placement-r1/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round6/placement-r1/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round6/placement-r1/Attempt.lean:1153`); `AdalyFormal.Round6.Guarded.PlacementR1.placementU` (`AHP/round6/placement-r1/Attempt.lean:2455`); `AdalyFormal.Round6.Guarded.PlacementR1.placement_guard_iff_pencil` (`AHP/round6/placement-r1/Attempt.lean:2511`); `AdalyFormal.Round6.Guarded.PlacementR1.uniform_placement_class_family` (`AHP/round6/placement-r1/Attempt.lean:2654`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_curved_placement_no_separation :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 17*2 ≤ R*(2^m) ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ)*(2^m : ℕ)*α₀ ≤ a₀)
            (_ : TorusOK 2 (2^m) Lu)
            (S : Tower (scaleUp 2 k Lu)) (_ : Admissible 2 (2^m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 2 (2^m) R k S Lam)
            (U : LinkCfg (scaleUp 2 k Lu))
            (_ : ClassCoupled 2 (2^m) 12 k S α₀ ((2 : ℝ)^k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam 2 Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            (∃ e : Bond (scaleUp 2 k Lu), e.1 ∈ S.Om 0 ∧ U e ≠ 1) ∧
            (∃ p ∈ plaqIn (S.Om 0), periodicPlaquetteHolonomy U p ≠ 1) ∧
            (¬ ∃ g : PeriodicLatticeSite (scaleUp 2 k Lu) → G2,
              periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
            ∀ a : ℝ, CPen 2 k Lu (by norm_num) S U a Lam ↔
              IsUnit (dataS selAll selAll (gparams 2 k Lu (by norm_num) S U a Lam)).Ginv
```

</details>

<a id="bp-067"></a>
#### bp-067 — `AdalyFormal.Round6.Guarded.PlacementR2.hybrid_correction_formula`

For a boundary-plus-core hybrid the effective source is the retained core source; the constrained inverse and dressed jet still depend on the modified background. It does not assert that the correction is unchanged.

- **Source:** `AHP/round6/placement-r2/HybridCertificate.lean:2509`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/placement-r2/HybridCertificate.lean.log:249`: `'AdalyFormal.Round6.Guarded.PlacementR2.hybrid_correction_formula' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round6/placement-r2/HybridCertificate.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/placement-r2/HybridCertificate.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round6/placement-r2/HybridCertificate.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round6/placement-r2/HybridCertificate.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/placement-r2/HybridCertificate.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round6/placement-r2/HybridCertificate.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round6/placement-r2/HybridCertificate.lean:1383`); `AdalyFormal.Round6.Guarded.PlacementR2.activeSource` (`AHP/round6/placement-r2/HybridCertificate.lean:2145`); `AdalyFormal.Round6.Guarded.PlacementR2.boundary_modification_correction_formula` (`AHP/round6/placement-r2/HybridCertificate.lean:2313`); `AdalyFormal.Round6.Guarded.PlacementR2.hybridU` (`AHP/round6/placement-r2/HybridCertificate.lean:2358`); `AdalyFormal.Round6.Guarded.PlacementR2.hybridP` (`AHP/round6/placement-r2/HybridCertificate.lean:2362`); `AdalyFormal.Round6.Guarded.PlacementR2.hybrid_agrees_near_top` (`AHP/round6/placement-r2/HybridCertificate.lean:2381`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem hybrid_correction_formula {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (β ε a : ℝ) (V V' : LinkCfg (scaleUp 2 1 (dilLu q R)))
    (v : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    let P
```

</details>

<a id="bp-068"></a>
#### bp-068 — `AdalyFormal.Round6.Guarded.PlacementR2.nonzero_correction_requires_active_source`

A nonzero correction requires an active higher-level source component, not curvature supported solely on linear level-zero rows.

- **Source:** `AHP/round6/placement-r2/HybridCertificate.lean:2190`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/placement-r2/HybridCertificate.lean.log:216`: `'AdalyFormal.Round6.Guarded.PlacementR2.nonzero_correction_requires_active_source' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.PlaqSel` (`AHP/round6/placement-r2/HybridCertificate.lean:31`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round6/placement-r2/HybridCertificate.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round6/placement-r2/HybridCertificate.lean:62`); `AdalyFormal.Round6.Guarded.PlacementR2.activeSource` (`AHP/round6/placement-r2/HybridCertificate.lean:2145`); `AdalyFormal.Round6.Guarded.PlacementR2.correction_uses_active_source` (`AHP/round6/placement-r2/HybridCertificate.lean:2177`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem nonzero_correction_requires_active_source (sD sJ : PlaqSel) (P : IngrBParams)
    (hD : (dataS sD sJ P).Delta2 (dataS_laws sD sJ P) ≠ 0) : activeSource sJ P ≠ 0
```

</details>

### Rounds 8–9: separation, regularity and cofinal bridges

<a id="bp-069"></a>
#### bp-069 — `AdalyFormal.Round8.Guarded.SignFree.separation_of_sign_change`

A continuous symmetric corrected path changing from PSD to a negative direction crosses a nonunit while the carrier stays a unit on the interval. The carrier need not be positive there.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2440`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:217`: `'AdalyFormal.Round8.Guarded.SignFree.separation_of_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2440`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:217`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.separation_of_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem separation_of_sign_change
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (hsA : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hsD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫)
    (t₀ t₁ : ℝ) (h01 : t₀ ≤ t₁)
    (hguard : ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t))
    (h₀ : PSD (A t₀ - D)) (w : E) (h₁ : ⟪w, (A t₁ - D) w⟫ < 0) :
    ∃ t : ℝ, t₀ ≤ t ∧ t < t₁ ∧ IsUnit (A t) ∧ ¬ IsUnit (A t - D)
```

</details>

<a id="bp-070"></a>
#### bp-070 — `AdalyFormal.Round8.Guarded.SignFree.sign_change_of_kernel_positive`

The older positive-kernel crossing assumptions imply the sign-change interval criterion.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2474`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:220`: `'AdalyFormal.Round8.Guarded.SignFree.sign_change_of_kernel_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2474`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:220`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.sign_change_of_kernel_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem sign_change_of_kernel_positive
    (A : ℝ → E →L[ℝ] E) (D : E →L[ℝ] E) (hc : Continuous A)
    (T : ℝ) (hT : 0 < T)
    (hguard : ∀ t, 0 ≤ t → t < T → IsUnit (A t))
    (v : E) (hker : A T v = 0) (hpositive : 0 < ⟪v, D v⟫) :
    ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ < T ∧ (∀ t, 0 ≤ t → t ≤ t₁ → IsUnit (A t)) ∧
      ⟪v, (A t₁ - D) v⟫ < 0
```

</details>

<a id="bp-071"></a>
#### bp-071 — `AdalyFormal.Round8.Guarded.SignFree.unit_of_definite_complements`

A symmetric operator is a unit if it is negative and positive definite on subspaces whose dimensions cover the ambient space.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2531`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:224`: `'AdalyFormal.Round8.Guarded.SignFree.unit_of_definite_complements' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2531`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:224`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.unit_of_definite_complements' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem unit_of_definite_complements (X : E →L[ℝ] E)
    (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, X x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, X x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    IsUnit X
```

</details>

<a id="bp-072"></a>
#### bp-072 — `AdalyFormal.Round8.Guarded.SignFree.pencil_rescaled_antitone`

For a sine/cosine pencil with PSD constant and cosine coefficients, division by \(\sin t\) makes its quadratic forms nonincreasing on \((0,\pi/2]\).

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2604`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:230`: `'AdalyFormal.Round8.Guarded.SignFree.pencil_rescaled_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2604`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:230`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.pencil_rescaled_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_rescaled_antitone (B Θ₀ Θ₁ : E →L[ℝ] E) (hB : PSD B) (hΘ : PSD Θ₀)
    {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (htπ : t ≤ Real.pi/2) (x : E) :
    ⟪x, (B + Real.cos t • Θ₀ + Real.sin t • Θ₁) x⟫ / Real.sin t ≤
      ⟪x, (B + Real.cos s • Θ₀ + Real.sin s • Θ₁) x⟫ / Real.sin s
```

</details>

<a id="bp-073"></a>
#### bp-073 — `AdalyFormal.Round8.Guarded.SignFree.pencil_units_of_certificates`

The rescaled pencil monotonicity and complementary endpoint subspaces certify the carrier unit throughout an interval.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2631`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:233`: `'AdalyFormal.Round8.Guarded.SignFree.pencil_units_of_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2631`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:233`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.pencil_units_of_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-072](#bp-072) (`AdalyFormal.Round8.Guarded.SignFree.pencil_rescaled_antitone`)
- **Additional local source references:** `AdalyFormal.Round8.Guarded.SignFree.units_of_scaled_certificates` (`AHP/round8/guarded-idea/Attempt.lean:2576`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_units_of_certificates (A : ℝ → E →L[ℝ] E) (B Θ₀ Θ₁ : E →L[ℝ] E)
    (hA : ∀ t, A t = B + Real.cos t • Θ₀ + Real.sin t • Θ₁)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hB : PSD B) (hΘ : PSD Θ₀) (t₀ t₁ : ℝ) (h0 : 0 < t₀) (h1 : t₁ ≤ Real.pi/2)
    (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, A t₀ x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, A t₁ x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A t)
```

</details>

<a id="bp-074"></a>
#### bp-074 — `AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`

Some exterior angle has an invertible actual carrier but a noninvertible actual corrected pencil at the chosen interior curvature.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2656`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:236`: `'AdalyFormal.Round8.Guarded.SignFree.TwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2656`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:236`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.TwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round8/guarded-idea/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round8/guarded-idea/Attempt.lean:1713`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def TwistSeparation (q R : ℕ) (ε : ℝ) : Prop
```

</details>

<a id="bp-075"></a>
#### bp-075 — `AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`

An interval of carrier units has corrected form PSD at its left endpoint and negative in some direction at its right endpoint.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2663`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:237`: `'AdalyFormal.Round8.Guarded.SignFree.SignChangeControl' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2663`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:237`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.SignChangeControl' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round8/guarded-idea/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round8/guarded-idea/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round8/guarded-idea/Attempt.lean:1713`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def SignChangeControl (q R : ℕ) (ε : ℝ) : Prop
```

</details>

<a id="bp-076"></a>
#### bp-076 — `AdalyFormal.Round8.Guarded.SignFree.twistSeparation_of_signChange`

The actual twist sign-change data imply actual guarded separation.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2670`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:238`: `'AdalyFormal.Round8.Guarded.SignFree.twistSeparation_of_signChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2670`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:238`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.twistSeparation_of_signChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-049](#bp-049) (`AdalyFormal.Round5.Guarded.IVTR1.twistD_constant`); [bp-069](#bp-069) (`AdalyFormal.Round8.Guarded.SignFree.separation_of_sign_change`); [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`); [bp-075](#bp-075) (`AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round8/guarded-idea/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round8/guarded-idea/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round8/guarded-idea/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round8/guarded-idea/Attempt.lean:62`); `AdalyFormal.Round5.Guarded.IVTR1.twistP` (`AHP/round8/guarded-idea/Attempt.lean:1706`); `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round8/guarded-idea/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round8/guarded-idea/Attempt.lean:1713`); `AdalyFormal.Round5.Guarded.IVTR1.twistA_continuous` (`AHP/round8/guarded-idea/Attempt.lean:1819`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : SignChangeControl q R ε) :
    TwistSeparation q R ε
```

</details>

<a id="bp-077"></a>
#### bp-077 — `AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`

Above every dyadic-scale bound, one can choose a scale with arbitrarily large even radii, each separating below every positive curvature cap.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2846`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:267`: `'AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2846`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:267`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CofinalTwistSeparation : Prop
```

</details>

<a id="bp-078"></a>
#### bp-078 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`

Nested cofinal actual twist separation refutes the pinned carrier-guarded headline; the radius is chosen before the cap.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2856`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:269`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2856`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:269`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`); [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round8/guarded-idea/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round8/guarded-idea/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round8/guarded-idea/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round8/guarded-idea/Attempt.lean:1153`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round8/guarded-idea/Attempt.lean:1703`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalTwistSeparation (h : CofinalTwistSeparation) : GoalNeg2
```

</details>

<a id="bp-079"></a>
#### bp-079 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalSignChange`

Nested cofinal sign-change intervals imply the negative goal through actual separation.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2905`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:278`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalSignChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2905`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:278`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalSignChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-260](#bp-260) (`AdalyFormal.Round8.Guarded.SignFree.cofinalTwistSeparation_of_cofinalSignChange`)
- **Additional local source references:** `AdalyFormal.Round8.Guarded.SignFree.CofinalSignChange` (`AHP/round8/guarded-idea/Attempt.lean:2851`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalSignChange (h : CofinalSignChange) : GoalNeg2
```

</details>

<a id="bp-080"></a>
#### bp-080 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_pencil_certificates`

Cofinal sine/cosine-pencil and subspace certificates suffice for the negative goal; the actual certificate premise is not proved.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2832`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:264`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_pencil_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2832`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:264`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_pencil_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-258](#bp-258) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_sign_change_control`); [bp-259](#bp-259) (`AdalyFormal.Round8.Guarded.SignFree.signChange_of_pencilCertificates`)
- **Additional local source references:** `AdalyFormal.Round8.Guarded.SignFree.PencilCertificates` (`AHP/round8/guarded-idea/Attempt.lean:2811`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_pencil_certificates
    (hcert : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PencilCertificates q R ε) :
    GoalNeg2
```

</details>

<a id="bp-081"></a>
#### bp-081 — `AdalyFormal.Round8.Guarded.SignFree.goalPos1_forces_no_twist_separation`

The positive reading would exclude all such separations below a positive cap at every sufficiently large scale and radius.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2763`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:256`: `'AdalyFormal.Round8.Guarded.SignFree.goalPos1_forces_no_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2763`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:256`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalPos1_forces_no_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`); [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round8/guarded-idea/Attempt.lean:154`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round8/guarded-idea/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round8/guarded-idea/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round8/guarded-idea/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round8/guarded-idea/Attempt.lean:1153`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round8/guarded-idea/Attempt.lean:1703`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_no_twist_separation (h : GoalPos1) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → ¬ TwistSeparation (2^(m-1)) R ε
```

</details>

<a id="bp-082"></a>
#### bp-082 — `AdalyFormal.Round9.Guarded.AnalyticR1.schur_unit_iff`

With the complementary block invertible, full operator invertibility is equivalent to injectivity of its Schur complement on the projected kernel space.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3137`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:293`: `'AdalyFormal.Round9.Guarded.AnalyticR1.schur_unit_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7224`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:686`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.schur_unit_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.schurC` (`AHP/round9/analytic-r2/Attempt.lean:3085`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS` (`AHP/round9/analytic-r2/Attempt.lean:3088`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem schur_unit_iff {P Z : E →L[ℝ] E} (hP : P * P = P) (hC : IsUnit (schurC P Z)) :
    IsUnit Z ↔ ∀ x, P x = x → schurS P Z x = 0 → x = 0
```

</details>

<a id="bp-083"></a>
#### bp-083 — `AdalyFormal.Round9.Guarded.AnalyticR1.vacuum_schur_slope`

At a vacuum kernel the first-order Schur slope equals the compression of the carrier angle derivative.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3247`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:300`: `'AdalyFormal.Round9.Guarded.AnalyticR1.vacuum_schur_slope' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7334`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:693`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.vacuum_schur_slope' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.schurC` (`AHP/round9/analytic-r2/Attempt.lean:3085`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS` (`AHP/round9/analytic-r2/Attempt.lean:3088`); `AdalyFormal.Round9.Guarded.AnalyticR1.tendsto_inverse_of_unit` (`AHP/round9/analytic-r2/Attempt.lean:3219`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurC_continuous` (`AHP/round9/analytic-r2/Attempt.lean:3227`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacuum_schur_slope (P X' : E →L[ℝ] E) (Xv : ℝ → E →L[ℝ] E) (t₀ : ℝ)
    (hder : HasDerivAt Xv X' t₀)
    (hXP : Xv t₀ * P = 0) (hPX : P * Xv t₀ = 0) (hC0 : IsUnit (schurC P (Xv t₀))) :
    Tendsto (fun t => (t - t₀)⁻¹ • schurS P (Xv t)) (𝓝[≠] t₀) (𝓝 (P * X' * P))
```

</details>

<a id="bp-084"></a>
#### bp-084 — `AdalyFormal.Round9.Guarded.AnalyticR1.schur_difference_tendsto`

The rescaled difference between carrier and corrected Schur complements converges to the compressed first-order correction.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3321`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:304`: `'AdalyFormal.Round9.Guarded.AnalyticR1.schur_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7408`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:697`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.schur_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.schurC` (`AHP/round9/analytic-r2/Attempt.lean:3085`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS` (`AHP/round9/analytic-r2/Attempt.lean:3088`); `AdalyFormal.Round9.Guarded.AnalyticR1.tendsto_inverse_of_unit` (`AHP/round9/analytic-r2/Attempt.lean:3219`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurC_continuous` (`AHP/round9/analytic-r2/Attempt.lean:3227`); `AdalyFormal.Round9.Guarded.AnalyticR1.schur_difference_identity` (`AHP/round9/analytic-r2/Attempt.lean:3286`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem schur_difference_tendsto {α : Type*} {l : Filter α} (P : E →L[ℝ] E)
    {Xf Df : α → E →L[ℝ] E} {c : α → ℝ} {X0 D1 : E →L[ℝ] E}
    (hXP : X0 * P = 0) (hPX : P * X0 = 0) (hC0 : IsUnit (schurC P X0))
    (hX : Tendsto Xf l (𝓝 X0)) (hD : Tendsto Df l (𝓝 0))
    (hcD : Tendsto (fun a => c a • Df a) l (𝓝 D1)) :
    Tendsto (fun a => c a • (schurS P (Xf a) - schurS P (Xf a - Df a)) - P * D1 * P) l (𝓝 0)
```

</details>

<a id="bp-085"></a>
#### bp-085 — `AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_kernel`

A transversal vacuum crossing and a first-order correction definite on its entire kernel give guarded separation for every sufficiently small positive curvature, for either sign.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3788`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:314`: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7875`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:707`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-262](#bp-262) (`AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem separation_of_vacuum_kernel
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hne : ∃ v, X 0 t₀ v = 0 ∧ v ≠ 0)
    (hslope : ∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, X 0 t₀ v = 0 → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, X 0 t₀ v = 0 → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε)
```

</details>

<a id="bp-086"></a>
#### bp-086 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalExtSeparation`

Cofinal separation with arbitrary exterior fields implies the pinned negative goal, using the dilated class and competitor construction.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3963`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:343`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalExtSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8050`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:736`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalExtSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round9/analytic-r2/Attempt.lean:1153`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round9/analytic-r2/Attempt.lean:1383`); `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalExtSeparation` (`AHP/round9/analytic-r2/Attempt.lean:3957`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalExtSeparation (h : CofinalExtSeparation) : GoalNeg2
```

</details>

<a id="bp-087"></a>
#### bp-087 — `AdalyFormal.Round9.Guarded.AnalyticR1.extA_joint_tendsto`

Interior continuity of the carrier and dressing, together with the exterior path formula, yields joint curvature-angle continuity.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4448`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:411`: `'AdalyFormal.Round9.Guarded.AnalyticR1.extA_joint_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8535`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:804`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.extA_joint_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-048](#bp-048) (`AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/analytic-r2/Attempt.lean:35`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round9/analytic-r2/Attempt.lean:1383`); `AdalyFormal.Round9.Guarded.AnalyticR1.extA` (`AHP/round9/analytic-r2/Attempt.lean:3942`); `AdalyFormal.Round9.Guarded.AnalyticR1.dilU_agree` (`AHP/round9/analytic-r2/Attempt.lean:4016`); `AdalyFormal.Round9.Guarded.AnalyticR1.contT_deltaKLocCLM` (`AHP/round9/analytic-r2/Attempt.lean:4372`); `AdalyFormal.Round9.Guarded.AnalyticR1.dilU_contFamT` (`AHP/round9/analytic-r2/Attempt.lean:4420`); `AdalyFormal.Round9.Guarded.AnalyticR1.tendsto_clm_comp` (`AHP/round9/analytic-r2/Attempt.lean:4436`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem extA_joint_tendsto {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : AdalyFormal.D1Literal.ContFam V)
    (hA : Tendsto (fun ε : ℝ => extA q R ε (V 0)) (𝓝[>] 0) (𝓝 (extA q R 0 (V 0))))
    (hW : Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε (V 0)) 1) (𝓝[>] 0)
      (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 (V 0)) 1)))
    (t : ℝ) :
    Tendsto (fun p : ℝ × ℝ => extA q R p.1 (V p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t)
      (𝓝 (extA q R 0 (V t)))
```

</details>

<a id="bp-088"></a>
#### bp-088 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_interiorSoft_vacuumLeftSpectral`

Interior soft regularity and cofinal left-twist vacuum spectral coupling imply the negative goal; the spectral premise remains unproved.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4539`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:419`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_interiorSoft_vacuumLeftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8626`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:812`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_interiorSoft_vacuumLeftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-268](#bp-268) (`AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalLeftVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.leftRegularity_of_interior` (`AHP/round9/analytic-r2/Attempt.lean:4514`); `AdalyFormal.Round9.Guarded.AnalyticR1.InteriorSoft` (`AHP/round9/analytic-r2/Attempt.lean:4525`); `AdalyFormal.Round9.Guarded.AnalyticR1.VacuumLeftSpectral` (`AHP/round9/analytic-r2/Attempt.lean:4532`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_interiorSoft_vacuumLeftSpectral (hs : InteriorSoft)
    (hc : VacuumLeftSpectral) : GoalNeg2
```

</details>

<a id="bp-089"></a>
#### bp-089 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP_unit`

The dilated auxiliary Dirichlet operator is a genuine unit under its stated geometric hypotheses.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:5848`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:532`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:9921`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:925`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_LP_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.AnalyticR2.delpA_unit` (`AHP/round9/analytic-r2/Attempt.lean:5107`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_out_site` (`AHP/round9/analytic-r2/Attempt.lean:5841`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_LP_unit (q R : ℕ) (hq : 0 < q) (U : Cfg (scaleUp 2 1 (dilLu q R))) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) U 1)
```

</details>

<a id="bp-090"></a>
#### bp-090 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam_unit`

The gauge Gram operator is a genuine unit at the flat admissible dilated point, enabling the projection regularity formula.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:5859`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:535`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:9932`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:928`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_Gam_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.AnalyticR2.Gam` (`AHP/round9/analytic-r2/Attempt.lean:4917`); `AdalyFormal.Round9.Guarded.AnalyticR2.bgTower_one` (`AHP/round9/analytic-r2/Attempt.lean:5855`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_Gam_unit {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1)
```

</details>

<a id="bp-091"></a>
#### bp-091 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos`

The flat localized carrier is strictly positive on nonzero fields: zero curl, zero constraints and zero gauge-fixing form force the field to vanish.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:6639`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:584`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:10712`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:977`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/analytic-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/analytic-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_kernel` (`AHP/round9/analytic-r2/Attempt.lean:6579`); `AdalyFormal.Round9.Guarded.AnalyticR2.flat_ginv_form_in` (`AHP/round9/analytic-r2/Attempt.lean:6615`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫
```

</details>

<a id="bp-092"></a>
#### bp-092 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit`

Strict positivity makes the flat localized base carrier a genuine unit.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:6743`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:588`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:10816`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:981`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/analytic-r2/Attempt.lean:33`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/analytic-r2/Attempt.lean:5468`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_unit` (`AHP/round9/analytic-r2/Attempt.lean:6695`); `AdalyFormal.Round9.Guarded.AnalyticR2.dilV` (`AHP/round9/analytic-r2/Attempt.lean:6735`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam_dil_zero` (`AHP/round9/analytic-r2/Attempt.lean:6737`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_B0_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv
```

</details>

<a id="bp-093"></a>
#### bp-093 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit`

The full flat constraint matrix \(QGQ^*\) is a genuine unit for the admissible dilated family; this is not a boundary-block inverse.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:6764`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:591`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:10837`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:984`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-092](#bp-092) (`AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_unit`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/analytic-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round9/analytic-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/analytic-r2/Attempt.lean:5468`); `AdalyFormal.Round9.Guarded.AnalyticR2.dilV` (`AHP/round9/analytic-r2/Attempt.lean:6735`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_B0_psd` (`AHP/round9/analytic-r2/Attempt.lean:6748`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_Qs0_inj` (`AHP/round9/analytic-r2/Attempt.lean:6757`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_N0_unit {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Q.comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).G).comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs)
```

</details>

<a id="bp-094"></a>
#### bp-094 — `AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form`

Any first-order correction limit has quadratic form \(2\langle H_0C^2_0(W_0u),J'\rangle\) under the explicit continuity and source-limit hypotheses.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:5588`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:511`: `'AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:9661`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:904`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_apply₂` (`AHP/round9/analytic-r2/Attempt.lean:5384`); `AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_Delta2_div_form` (`AHP/round9/analytic-r2/Attempt.lean:5527`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫
```

</details>

<a id="bp-095"></a>
#### bp-095 — `AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form`

The dilated single-defect correction coefficient equals that actual flat lift/jet/source pairing.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:6904`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:611`: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:10977`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1004`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-094](#bp-094) (`AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/analytic-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/analytic-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round9/analytic-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round9/analytic-r2/Attempt.lean:3851`); `AdalyFormal.Round9.Guarded.AnalyticR1.extD` (`AHP/round9/analytic-r2/Attempt.lean:3947`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/analytic-r2/Attempt.lean:5468`); `AdalyFormal.Round9.Guarded.AnalyticR2.dilV` (`AHP/round9/analytic-r2/Attempt.lean:6735`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam_dil_zero` (`AHP/round9/analytic-r2/Attempt.lean:6737`); `AdalyFormal.Round9.Guarded.AnalyticR2.extD_eq_dataFam` (`AHP/round9/analytic-r2/Attempt.lean:6779`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_H_cont` (`AHP/round9/analytic-r2/Attempt.lean:6853`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_C2_tendsto` (`AHP/round9/analytic-r2/Attempt.lean:6868`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dil_D1_form (hR : 16 ≤ R) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R)
    (hD₁ : Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)) (J' : TwistSpace q R)
    (hJ : Tendsto (fun ε => ε⁻¹ • (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1
      (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J')) (A : TwistSpace q R) :
    ⟪A, D₁ A⟫ = 2 * ⟪(dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).H
      (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
        (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) A))), J'⟫
```

</details>

<a id="bp-096"></a>
#### bp-096 — `AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved`

The single-defect dilated family has the required interior continuity and first-order correction limit for every permitted scale and even radius.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7282`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:646`: `'AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11041`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1011`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.InteriorSoft` (`AHP/round9/analytic-r2/Attempt.lean:4525`); `AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_of_admissible` (`AHP/round9/analytic-r2/Attempt.lean:6938`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem interiorSoft_proved : InteriorSoft
```

</details>

<a id="bp-097"></a>
#### bp-097 — `AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved`

The original twist family satisfies the zero-curvature regularity premise; this is not a spectral nondegeneracy theorem.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7296`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:653`: `'AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11055`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1018`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-087](#bp-087) (`AdalyFormal.Round9.Guarded.AnalyticR1.extA_joint_tendsto`); [bp-096](#bp-096) (`AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round9/analytic-r2/Attempt.lean:3851`); `AdalyFormal.Round9.Guarded.AnalyticR1.ZeroCurvatureRegularity` (`AHP/round9/analytic-r2/Attempt.lean:3856`); `AdalyFormal.Round9.Guarded.AnalyticR1.extD` (`AHP/round9/analytic-r2/Attempt.lean:3947`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem zeroCurvatureRegularity_proved {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, ZeroCurvatureRegularity q R D₁
```

</details>

<a id="bp-098"></a>
#### bp-098 — `AdalyFormal.Round9.Guarded.AnalyticR2.hasDerivAt_extA_vac`

A smooth exterior path has a genuine vacuum carrier angle derivative, equal to the named total derivative.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7522`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:695`: `'AdalyFormal.Round9.Guarded.AnalyticR2.hasDerivAt_extA_vac' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-048](#bp-048) (`AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/analytic-r2/Attempt.lean:35`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round9/analytic-r2/Attempt.lean:1383`); `AdalyFormal.Round9.Guarded.AnalyticR1.extA` (`AHP/round9/analytic-r2/Attempt.lean:3942`); `AdalyFormal.Round9.Guarded.AnalyticR1.dilU_agree` (`AHP/round9/analytic-r2/Attempt.lean:4016`); `AdalyFormal.Round9.Guarded.AnalyticR2.SmoothFam` (`AHP/round9/analytic-r2/Attempt.lean:7075`); `AdalyFormal.Round9.Guarded.AnalyticR2.contDiff_deltaKLocCLM` (`AHP/round9/analytic-r2/Attempt.lean:7234`); `AdalyFormal.Round9.Guarded.AnalyticR2.hasDerivAt_path_formula` (`AHP/round9/analytic-r2/Attempt.lean:7242`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem hasDerivAt_extA_vac {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (hV : SmoothFam (fun t => dilU q R 0 (V t)))
    (t₀ : ℝ) :
    HasDerivAt (fun t => extA q R 0 (V t)) (deriv (fun t => extA q R 0 (V t)) t₀) t₀
```

</details>

<a id="bp-099"></a>
#### bp-099 — `AdalyFormal.Round9.Guarded.AnalyticR2.extA_vac_one_pos`

The vacuum all-plaquette carrier at the trivial exterior field is positive definite, by domination of the localized flat form.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7541`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:696`: `'AdalyFormal.Round9.Guarded.AnalyticR2.extA_vac_one_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/analytic-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/analytic-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/analytic-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/analytic-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round9/analytic-r2/Attempt.lean:1383`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round9/analytic-r2/Attempt.lean:3851`); `AdalyFormal.Round9.Guarded.AnalyticR1.extA` (`AHP/round9/analytic-r2/Attempt.lean:3942`); `AdalyFormal.Round9.Guarded.AnalyticR2.dilU_zero` (`AHP/round9/analytic-r2/Attempt.lean:5830`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_all_pos` (`AHP/round9/analytic-r2/Attempt.lean:7014`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem extA_vac_one_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (v : TwistSpace q R) (hv : v ≠ 0) :
    0 < ⟪v, extA q R 0 1 v⟫
```

</details>

<a id="bp-100"></a>
#### bp-100 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCouplingD`

Cofinal left-twist vacuum kernel transversality and explicit whole-kernel coupling suffice for the negative goal; the coupling is still an input.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7608`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:707`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCouplingD' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-274](#bp-274) (`AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.VacuumLeftCouplingD` (`AHP/round9/analytic-r2/Attempt.lean:7591`); `AdalyFormal.Round9.Guarded.AnalyticR2.vacuumLeftCoupling_of_D` (`AHP/round9/analytic-r2/Attempt.lean:7596`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_vacuumLeftCouplingD (h : VacuumLeftCouplingD) : GoalNeg2
```

</details>

<a id="bp-101"></a>
#### bp-101 — `AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCouplingD`

The corresponding explicit vacuum data for the symmetric twist imply cofinal actual twist separation.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7632`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:719`: `'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCouplingD' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-275](#bp-275) (`AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCouplingD` (`AHP/round9/analytic-r2/Attempt.lean:7616`); `AdalyFormal.Round9.Guarded.AnalyticR2.twistVacuumCoupling_of_D` (`AHP/round9/analytic-r2/Attempt.lean:7621`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_twistVacuumCouplingD (h : CofinalTwistVacuumCouplingD) :
    CofinalTwistSeparation
```

</details>

<a id="bp-102"></a>
#### bp-102 — `AdalyFormal.Round9.Guarded.Qualitative.first_order_separation`

A vacuum PSD boundary approached from positive and negative sides, soft regularity, and a positive first-order correction on the full kernel yield an earlier corrected singularity with positive-definite carrier.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:3729`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:309`: `'AdalyFormal.Round9.Guarded.Qualitative.first_order_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:3729`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:309`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.first_order_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-051](#bp-051) (`AdalyFormal.Round5.Guarded.IVTR2.first_carrier_crossing`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.abs_inner_op_le` (`AHP/round9/qualitative-r2/Attempt.lean:2963`); `AdalyFormal.Round9.Guarded.Qualitative.unit_of_pos` (`AHP/round9/qualitative-r2/Attempt.lean:3463`); `AdalyFormal.Round9.Guarded.Qualitative.psd_of_pos` (`AHP/round9/qualitative-r2/Attempt.lean:3471`); `AdalyFormal.Round9.Guarded.Qualitative.psd_of_pd_before` (`AHP/round9/qualitative-r2/Attempt.lean:3479`); `AdalyFormal.Round9.Guarded.Qualitative.exists_gap_of_psd` (`AHP/round9/qualitative-r2/Attempt.lean:3504`); `AdalyFormal.Round9.Guarded.Qualitative.pos_of_psd_add` (`AHP/round9/qualitative-r2/Attempt.lean:3579`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem first_order_separation
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hcA : ∀ ε, Continuous (A ε)) (ts : ℝ)
    (hjoint : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖A ε s - A 0 t‖ < δ)
    (hbefore : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, A 0 t₀ x⟫)
    (hafter : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w : E, ⟪w, A 0 t₁ w⟫ < 0)
    (c : ℝ) (De : E →L[ℝ] E) (hc : 0 < c)
    (hDe : ∀ u : E, A 0 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hDexp : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖D ε - ε • De‖ ≤ μ * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t : ℝ, IsUnit (A ε t) ∧ ¬ IsUnit (A ε t - D ε)
```

</details>

<a id="bp-103"></a>
#### bp-103 — `AdalyFormal.Round9.Guarded.Qualitative.scalar_on_complex_line`

A symmetric quadratic form commuting with an orthogonal quarter-turn is scalar on the real span of a charged vector and its quarter-turn.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:3363`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:291`: `'AdalyFormal.Round9.Guarded.Qualitative.scalar_on_complex_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:3363`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:291`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.scalar_on_complex_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2
```

</details>

<a id="bp-104"></a>
#### bp-104 — `AdalyFormal.Round9.Guarded.Qualitative.pathD_constant`

The localized correction for a free interior profile is independent of the exterior path parameter.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4038`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:320`: `'AdalyFormal.Round9.Guarded.Qualitative.pathD_constant' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4038`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:320`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.pathD_constant' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.pathD` (`AHP/round9/qualitative-r2/Attempt.lean:3977`); `AdalyFormal.Round9.Guarded.Qualitative.path_data_constant` (`AHP/round9/qualitative-r2/Attempt.lean:4029`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V f ε a t = pathD q R V f ε a 0
```

</details>

<a id="bp-105"></a>
#### bp-105 — `AdalyFormal.Round9.Guarded.Qualitative.pathD_neg`

Negating the interior profile reflects curvature, hence reverses the first-order correction sign.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4515`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:385`: `'AdalyFormal.Round9.Guarded.Qualitative.pathD_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4515`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:385`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.pathD_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/qualitative-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.pathP` (`AHP/round9/qualitative-r2/Attempt.lean:3966`); `AdalyFormal.Round9.Guarded.Qualitative.pathD` (`AHP/round9/qualitative-r2/Attempt.lean:3977`); `AdalyFormal.Round9.Guarded.Qualitative.pathU_neg` (`AHP/round9/qualitative-r2/Attempt.lean:4500`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathD_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V (fun e => -f e) ε a t = pathD q R V f (-ε) a t
```

</details>

<a id="bp-106"></a>
#### bp-106 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathSeparation`

Cofinal separation along some exterior path and bounded interior profile contradicts the headline with the complete masked-class bookkeeping.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4139`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:333`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4139`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:333`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round9/qualitative-r2/Attempt.lean:1153`); `AdalyFormal.Round5.Guarded.IVTR2.masked_regular` (`AHP/round9/qualitative-r2/Attempt.lean:2123`); `AdalyFormal.Round9.Guarded.Qualitative.pathU` (`AHP/round9/qualitative-r2/Attempt.lean:3962`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4131`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalPathSeparation (h : CofinalPathSeparation) : GoalNeg2
```

</details>

<a id="bp-107"></a>
#### bp-107 — `AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_of_coupling`

A definite vacuum coupling of either sign gives small-curvature separation after choosing the profile or its negative.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4600`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:390`: `'AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4600`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:390`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-105](#bp-105) (`AdalyFormal.Round9.Guarded.Qualitative.pathD_neg`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.expansion_of_hasDerivAt` (`AHP/round9/qualitative-r2/Attempt.lean:3437`); `AdalyFormal.Round9.Guarded.Qualitative.metric_of_continuousAt` (`AHP/round9/qualitative-r2/Attempt.lean:3708`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round9/qualitative-r2/Attempt.lean:3971`); `AdalyFormal.Round9.Guarded.Qualitative.pathD` (`AHP/round9/qualitative-r2/Attempt.lean:3977`); `AdalyFormal.Round9.Guarded.Qualitative.pathD_zero` (`AHP/round9/qualitative-r2/Attempt.lean:4054`); `AdalyFormal.Round9.Guarded.Qualitative.PathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4124`); `AdalyFormal.Round9.Guarded.Qualitative.pathA_neg` (`AHP/round9/qualitative-r2/Attempt.lean:4509`); `AdalyFormal.Round9.Guarded.Qualitative.VacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4543`); `AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_pos` (`AHP/round9/qualitative-r2/Attempt.lean:4557`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem eventually_pathSeparation_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : VacuumCoupling q R V f) :
    ∃ f' : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f' e| = |f e|) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f' ε
```

</details>

<a id="bp-108"></a>
#### bp-108 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling`

Cofinal vacuum whole-kernel coupling with soft regularity and free paths/profiles implies the negative goal.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4680`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:399`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4680`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:399`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-106](#bp-106) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathSeparation`); [bp-286](#bp-286) (`AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalVacuumCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4657`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2
```

</details>

<a id="bp-109"></a>
#### bp-109 — `AdalyFormal.Round9.Guarded.QualitativeR2.isUnit_punctured`

For an analytic finite-dimensional operator path with one unit point, nonunit points are isolated near a singular point.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4917`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:420`: `'AdalyFormal.Round9.Guarded.QualitativeR2.isUnit_punctured' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4917`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:420`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.isUnit_punctured' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.gramDet` (`AHP/round9/qualitative-r2/Attempt.lean:4885`); `AdalyFormal.Round9.Guarded.QualitativeR2.isUnit_iff_gramDet` (`AHP/round9/qualitative-r2/Attempt.lean:4898`); `AdalyFormal.Round9.Guarded.QualitativeR2.analyticAt_gramDet` (`AHP/round9/qualitative-r2/Attempt.lean:4904`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem isUnit_punctured {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀)
    {t₀ : ℝ} (hu : IsUnit (A t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s)
```

</details>

<a id="bp-110"></a>
#### bp-110 — `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_spec`

The end of the initial PSD interval is singular, with positive-definite points before and negative directions after, under continuity and isolated-nonunit hypotheses.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:5007`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:421`: `'AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_spec' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:5007`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:421`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_spec' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.pos_of_psd_unit` (`AHP/round9/qualitative-r2/Attempt.lean:4948`); `AdalyFormal.Round9.Guarded.QualitativeR2.psd_of_pd` (`AHP/round9/qualitative-r2/Attempt.lean:4969`); `AdalyFormal.Round9.Guarded.QualitativeR2.eventually_pd` (`AHP/round9/qualitative-r2/Attempt.lean:4976`); `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge` (`AHP/round9/qualitative-r2/Attempt.lean:4999`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem psdEdge_spec (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0)
    (hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s)) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ - η < s ∧ s < psdEdge A t₀ t₁ ∧
        ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0)
```

</details>

<a id="bp-111"></a>
#### bp-111 — `AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`

The canonical crossing angle is the supremal initial PSD interval endpoint for the actual vacuum carrier on \([0,\pi]\).

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:5852`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:518`: `'AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:5852`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:518`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round9/qualitative-r2/Attempt.lean:4481`); `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge` (`AHP/round9/qualitative-r2/Attempt.lean:4999`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ
```

</details>

<a id="bp-112"></a>
#### bp-112 — `AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`

One positive coercivity constant bounds the actual derivative form or its negative on every vector of the full canonical crossing kernel.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6086`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:544`: `'AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6086`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:544`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round9/qualitative-r2/Attempt.lean:4481`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop
```

</details>

<a id="bp-113"></a>
#### bp-113 — `AdalyFormal.Round9.Guarded.QualitativeR2.De_flip`

The constant color flip reverses the correction derivative form and relates forward and backward twist kernels.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6594`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:616`: `'AdalyFormal.Round9.Guarded.QualitativeR2.De_flip' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6594`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:616`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.De_flip' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.QualitativeR2.flipGauge` (`AHP/round9/qualitative-r2/Attempt.lean:6439`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD_flip` (`AHP/round9/qualitative-r2/Attempt.lean:6549`); `AdalyFormal.Round9.Guarded.QualitativeR2.hasDerivAt_quadForm` (`AHP/round9/qualitative-r2/Attempt.lean:6584`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem De_flip {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    ⟪adEL flipGauge (geomOf 2 1 (dilTower q R)) u,
      De (adEL flipGauge (geomOf 2 1 (dilTower q R)) u)⟫ = -⟪u, De u⟫
```

</details>

<a id="bp-114"></a>
#### bp-114 — `AdalyFormal.Round9.Guarded.QualitativeR2.canonicalCoupling_of_U1`

An actual charged whole-kernel line and a nonzero scalar correction pairing imply the canonical whole-kernel coupling.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6945`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:660`: `'AdalyFormal.Round9.Guarded.QualitativeR2.canonicalCoupling_of_U1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6945`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:660`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.canonicalCoupling_of_U1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-103](#bp-103) (`AdalyFormal.Round9.Guarded.Qualitative.scalar_on_complex_line`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-328](#bp-328) (`AdalyFormal.Round9.Guarded.QualitativeR2.De_rot_comm`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round9/qualitative-r2/Attempt.lean:6772`); `AdalyFormal.Round9.Guarded.QualitativeR2.De_symm` (`AHP/round9/qualitative-r2/Attempt.lean:6884`); `AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalU1Line` (`AHP/round9/qualitative-r2/Attempt.lean:6932`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_U1 {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (h : CanonicalU1Line q R De) :
    CanonicalCoupling q R (uthPath q R) De
```

</details>

<a id="bp-115"></a>
#### bp-115 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont`

The actual full constrained localized lift is continuous at flat curvature for every interior profile under the stated admissibility hypotheses.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11538`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1084`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11538`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1084`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-093](#bp-093) (`AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_clm_comp` (`AHP/round9/qualitative-r2/Attempt.lean:9015`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/qualitative-r2/Attempt.lean:9541`); `AdalyFormal.Round9.Guarded.AnalyticR2.continuousAt_H` (`AHP/round9/qualitative-r2/Attempt.lean:9580`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_unit` (`AHP/round9/qualitative-r2/Attempt.lean:10768`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV` (`AHP/round9/qualitative-r2/Attempt.lean:11439`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero` (`AHP/round9/qualitative-r2/Attempt.lean:11472`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_dataFam_zero_eq` (`AHP/round9/qualitative-r2/Attempt.lean:11480`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_Q_cont` (`AHP/round9/qualitative-r2/Attempt.lean:11525`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_carrier_cont` (`AHP/round9/qualitative-r2/Attempt.lean:11530`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem bulk_H_cont {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).H) 0
```

</details>

<a id="bp-116"></a>
#### bp-116 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto`

The actual dressed second blocking jet converges to its flat value for arbitrary interior profiles.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11571`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1085`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11571`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1085`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_clm_apply₂` (`AHP/round9/qualitative-r2/Attempt.lean:9457`); `AdalyFormal.Round9.Guarded.AnalyticR2.tendsto_C2fullOf` (`AHP/round9/qualitative-r2/Attempt.lean:9517`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/qualitative-r2/Attempt.lean:9541`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV` (`AHP/round9/qualitative-r2/Attempt.lean:11439`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV_smooth` (`AHP/round9/qualitative-r2/Attempt.lean:11456`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_reg0` (`AHP/round9/qualitative-r2/Attempt.lean:11508`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_W_cont` (`AHP/round9/qualitative-r2/Attempt.lean:11513`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem bulk_C2_tendsto {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (A : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    Tendsto (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).C2 A) (𝓝 0)
      (𝓝 ((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).C2 A))
```

</details>

<a id="bp-117"></a>
#### bp-117 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`

The named correction derivative is a genuine two-sided curvature derivative, not merely a totalized derivative.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11642`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1099`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11642`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1099`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_hasDerivAt` (`AHP/round9/qualitative-r2/Attempt.lean:11623`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem hasDerivAt_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) 0
```

</details>

<a id="bp-118"></a>
#### bp-118 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv`

All soft regularity hypotheses for the free-profile qualitative route hold with the actual correction derivative.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11653`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1102`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11653`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1102`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-117](#bp-117) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/qualitative-r2/Attempt.lean:35`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.QualitativeR2.InteriorSoft` (`AHP/round9/qualitative-r2/Attempt.lean:6020`); `AdalyFormal.Round9.Guarded.AnalyticR2.dataFam` (`AHP/round9/qualitative-r2/Attempt.lean:9541`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkV` (`AHP/round9/qualitative-r2/Attempt.lean:11439`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_W_cont` (`AHP/round9/qualitative-r2/Attempt.lean:11513`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_carrier_cont` (`AHP/round9/qualitative-r2/Attempt.lean:11530`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem interiorSoft_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.InteriorSoft q R f (corrDeriv q R f)
```

</details>

<a id="bp-119"></a>
#### bp-119 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.twist_vacuum_crossing_all`

Every admissible dilated symmetric twist has the canonical vacuum crossing, without an additional asymptotic scale threshold.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11677`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1109`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.twist_vacuum_crossing_all' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11677`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1109`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.twist_vacuum_crossing_all' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5576`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg` (`AHP/round9/qualitative-r2/Attempt.lean:5579`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_cont` (`AHP/round9/qualitative-r2/Attempt.lean:5582`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5585`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5591`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5594`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_pd_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5810`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uth_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5818`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uthNeg_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5836`); `AdalyFormal.Round9.Guarded.QualitativeR2.VacuumCrossesAt` (`AHP/round9/qualitative-r2/Attempt.lean:5858`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacuum_crossing` (`AHP/round9/qualitative-r2/Attempt.lean:5867`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.flat_loc_unit` (`AHP/round9/qualitative-r2/Attempt.lean:11671`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twist_vacuum_crossing_all {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    QualitativeR2.VacuumCrossesAt q R (uthPath q R) (QualitativeR2.vacEdge q R (uthPath q R)) ∧
    QualitativeR2.VacuumCrossesAt q R (QualitativeR2.uthPathNeg q R)
      (QualitativeR2.vacEdge q R (QualitativeR2.uthPathNeg q R))
```

</details>

<a id="bp-120"></a>
#### bp-120 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling`

At each admissible instance, canonical coupling implies separation for every sufficiently small positive curvature.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11699`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1112`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11699`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1112`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-294](#bp-294) (`AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually`); [bp-118](#bp-118) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.QualitativeR2.twistSoftCoupling_of_fwd` (`AHP/round9/qualitative-r2/Attempt.lean:6646`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.flat_loc_unit` (`AHP/round9/qualitative-r2/Attempt.lean:11671`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_eventually_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R)
    (hc : QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε
```

</details>

<a id="bp-121"></a>
#### bp-121 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_iff`

Cofinal canonical coupling is equivalent to the earlier forward soft-coupling premise because regularity is now proved.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11774`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1133`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11774`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1133`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6652`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11711`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSoftCouplingFwd_iff` (`AHP/round9/qualitative-r2/Attempt.lean:11758`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalCanonicalCoupling_iff :
    CofinalCanonicalCoupling ↔ QualitativeR2.CofinalTwistSoftCouplingFwd
```

</details>

<a id="bp-122"></a>
#### bp-122 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling`

Nested cofinal canonical coupling implies nested cofinal actual twist separation.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11716`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1118`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11716`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1118`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-120](#bp-120) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.twistSeparation_eventually_of_coupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11711`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) :
    CofinalTwistSeparation
```

</details>

<a id="bp-123"></a>
#### bp-123 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling`

The canonical-profile whole-kernel coupling premise suffices for the pinned negative goal, but is not proved.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11729`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1121`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11729`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1121`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-122](#bp-122) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11711`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalCanonicalCoupling (h : CofinalCanonicalCoupling) : GoalNeg2
```

</details>

<a id="bp-124"></a>
#### bp-124 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul`

Scaling an interior profile scales the actual first-order correction by the same real scalar.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11813`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1138`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11813`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1138`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-117](#bp-117) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_smul` (`AHP/round9/qualitative-r2/Attempt.lean:11797`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem corrDeriv_smul {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ) :
    corrDeriv q R (fun e => c * f e) = c • corrDeriv q R f
```

</details>

<a id="bp-125"></a>
#### bp-125 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale`

Every finite physical profile has a positive rescaling satisfying the class amplitude bound.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11875`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1147`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11875`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1147`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_profile_scale {L : PeriodicLatticeExtent} (f : Bond L → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ e, |c * f e| ≤ 1
```

</details>

<a id="bp-126"></a>
#### bp-126 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling`

Nested cofinal existence of some definite interior profile on the canonical twist kernel suffices for the negative goal.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11906`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1156`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11906`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1156`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-299](#bp-299) (`AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling`); [bp-309](#bp-309) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11869`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalAnyProfileCoupling (h : CofinalAnyProfileCoupling) : GoalNeg2
```

</details>

<a id="bp-127"></a>
#### bp-127 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form`

For the canonical defect profile, the derivative quadratic form is exactly the flat constrained-lift/second-jet/source pairing.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11967`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1170`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11967`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1170`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-095](#bp-095) (`AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form`); [bp-117](#bp-117) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round9/qualitative-r2/Attempt.lean:7938`); `AdalyFormal.Round9.Guarded.AnalyticR1.extD` (`AHP/round9/qualitative-r2/Attempt.lean:8034`); `AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11107`); `AdalyFormal.Round9.Guarded.AnalyticR2.IsSourceDerivative` (`AHP/round9/qualitative-r2/Attempt.lean:11112`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_zero` (`AHP/round9/qualitative-r2/Attempt.lean:11616`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulkD_dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:11950`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem corrDeriv_dilMask_form {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (J' : AnalyticR1.TwistSpace q R) (hJ : AnalyticR2.IsSourceDerivative q R J')
    (u : AnalyticR1.TwistSpace q R) :
    ⟪u, corrDeriv q R (dilMask q R) u⟫ = AnalyticR2.vacCoupling q R J' u
```

</details>

<a id="bp-128"></a>
#### bp-128 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`

The cofinal premise allows any continuous analytic exterior path starting at the trivial field and negative at \(\pi\), and some profile definite on its entire canonical kernel.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12077`.
- **Status:** A — compiled and independently verified. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1204`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12077`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1204`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round9/qualitative-r2/Attempt.lean:4481`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round9/qualitative-r2/Attempt.lean:5161`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CofinalAnyPathCoupling : Prop
```

</details>

<a id="bp-129"></a>
#### bp-129 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath`

The free-path derivative-coupling premise supplies the earlier qualitative vacuum-coupling premise after profile scaling.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12085`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1207`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12085`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1207`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-290](#bp-290) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacuumCoupling_of_soft`); [bp-118](#bp-118) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.interiorSoft_corrDeriv`); [bp-124](#bp-124) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_smul`); [bp-308](#bp-308) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul`); [bp-125](#bp-125) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.exists_profile_scale`); [bp-128](#bp-128) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4657`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.flat_loc_unit` (`AHP/round9/qualitative-r2/Attempt.lean:11671`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalVacuumCoupling_of_anyPath (h : CofinalAnyPathCoupling) : CofinalVacuumCoupling
```

</details>

<a id="bp-130"></a>
#### bp-130 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling`

The original free-path cofinal coupling premise implies exactly the pinned negative goal; its explicit premise remains unproved.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12102`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1210`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12102`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1210`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-108](#bp-108) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling`); [bp-128](#bp-128) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`); [bp-129](#bp-129) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalVacuumCoupling_of_anyPath`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalAnyPathCoupling (h : CofinalAnyPathCoupling) : GoalNeg2
```

</details>

<a id="bp-131"></a>
#### bp-131 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_profiles`

The positive reading would force nondefiniteness for every profile at all sufficiently large canonical instances.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11923`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1165`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_profiles' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11923`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1165`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_profiles' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:154`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalAnyProfileCoupling_of_goalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:11909`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_degenerate_profiles (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R f)
```

</details>

<a id="bp-132"></a>
#### bp-132 — `AdalyFormal.Round10.Assembly.nested_cofinal_of_eventual`

Unbounded scale subsequences and a separate eventual even-radius condition at each chosen scale yield the required nested cofinal order.

- **Source:** `AHP/round10/shared/assembly/R1_Cofinal.lean:37`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R1_Cofinal.lean.log:8`: `'AdalyFormal.Round10.Assembly.nested_cofinal_of_eventual' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-319](#bp-319) (`AdalyFormal.Round10.Assembly.cofinal_of_eventual_subsequence`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem nested_cofinal_of_eventual {P : ℕ → ℕ → Prop}
    (j : ℕ → ℕ) (r : ℕ → ℕ → ℕ)
    (hj : ∀ n, n ≤ j n) (hr : ∀ n m, m ≤ r n m)
    (hP : ∀ n, ∀ᶠ m in atTop, P (j n) (r n m)) :
    ∀ j₀ : ℕ, ∃ j' : ℕ, j₀ ≤ j' ∧ ∀ R₀ : ℕ,
      ∃ R : ℕ, R₀ ≤ R ∧ P j' R
```

</details>

<a id="bp-133"></a>
#### bp-133 — `AdalyFormal.Round10.Assembly.eventually_ne_zero_of_normalized_limit`

A nonzero normalized limit forces eventual scalar nonvanishing; no actual coupling limit is supplied by this abstract lemma.

- **Source:** `AHP/round10/shared/assembly/R1_Cofinal.lean:10`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R1_Cofinal.lean.log:1`: `'AdalyFormal.Round10.Assembly.eventually_ne_zero_of_normalized_limit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem eventually_ne_zero_of_normalized_limit {z s : ℕ → ℝ} {K : ℝ}
    (hK : K ≠ 0) (hlim : Tendsto (fun n => z n / s n) atTop (𝓝 K)) :
    ∀ᶠ n in atTop, z n ≠ 0
```

</details>

### Round 10: actual dictionary, detection and response hull

<a id="bp-134"></a>
#### bp-134 — `AdalyFormal.Round10.Dictionary.Actual.corrDeriv_U1`

The actual free-profile correction derivative commutes with every constant diagonal gauge rotation.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1821`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:209`: `'AdalyFormal.Round10.Dictionary.Actual.corrDeriv_U1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:210`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1455`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1518`); `AdalyFormal.Round10.Dictionary.deriv_comm` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1771`); `AdalyFormal.Round10.Dictionary.Actual.bulkD_U1` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1813`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem corrDeriv_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    corrDeriv q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (corrDeriv q R f u)
```

</details>

<a id="bp-135"></a>
#### bp-135 — `AdalyFormal.Round10.Dictionary.Actual.vacuum_kernel_charge_split`

The vacuum kernel splits orthogonally into neutral and charged half-turn eigenspaces; symmetry does not exclude either part.

- **Source:** `AHP/round10/shared/dictionary/R1_Dictionary.lean:1317`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R1_Dictionary.lean.log:117`: `'AdalyFormal.Round10.Dictionary.Actual.vacuum_kernel_charge_split' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:83`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:183`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:189`); `AdalyFormal.Round10.Dictionary.involution_kernel_split` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:335`); `AdalyFormal.Round10.Dictionary.half_carrier_twice` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:588`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:849`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_rot` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:908`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:991`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacuum_kernel_charge_split (q R : ℕ) (t : ℝ) (u : TwistSpace q R)
    (hu : vacA q R (uthPath q R) 1 t u = 0) :
    ∃ up um : TwistSpace q R, u = up + um ∧
      adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) up = up ∧
      adEL (rotGauge (Real.pi / 2)) (geomOf 2 1 (dilTower q R)) um = -um ∧
      ⟪up, um⟫ = 0 ∧ vacA q R (uthPath q R) 1 t up = 0 ∧ vacA q R (uthPath q R) 1 t um = 0
```

</details>

<a id="bp-136"></a>
#### bp-136 — `AdalyFormal.Round10.Dictionary.Translation.deltaK_all_comm`

The undressed all-plaquette Hessian commutes with translations preserving the background. Full dressed blocking and carrier covariance does not follow without further proofs.

- **Source:** `AHP/round10/shared/dictionary/R1_Dictionary.lean:799`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R1_Dictionary.lean.log:69`: `'AdalyFormal.Round10.Dictionary.Translation.deltaK_all_comm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.Translation.bondPullback` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:665`); `AdalyFormal.Round10.Dictionary.Translation.cfgPullback` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:676`); `AdalyFormal.Round10.Dictionary.Translation.deltaK_translate` (`AHP/round10/shared/dictionary/R1_Dictionary.lean:787`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem deltaK_all_comm (a : PeriodicLatticeSite L) (U : LinkCfg L)
    (hU : cfgPullback a U = U) (x : BondFnL2 L) :
    deltaKLocCLM U Set.univ (bondPullback a x) = bondPullback a (deltaKLocCLM U Set.univ x)
```

</details>

<a id="bp-137"></a>
#### bp-137 — `AdalyFormal.Round10.Dictionary.no_canonical_radius_dilation`

Matching both the dilated collar and core lengths to one canonical undilated radius forces \(q=1\); the proposed exact radius-dilation shortcut is invalid.

- **Source:** `AHP/round10/shared/dictionary/R1_Dictionary.lean:472`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R1_Dictionary.lean.log:16`: `'AdalyFormal.Round10.Dictionary.no_canonical_radius_dilation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem no_canonical_radius_dilation {q R R' : ℕ}
    (hc : 2 * R' = 2 * R * q) (hi : 8 * R' + 8 = (8 * R + 8) * q) : q = 1
```

</details>

<a id="bp-138"></a>
#### bp-138 — `AdalyFormal.Round10.Dictionary.PhaseSource.JSU2Loc_phase`

For diagonal phases the frozen localized source is the backward divergence of the sine of the oriented plaquette circulation, on the neutral color axis.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:555`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:43`: `'AdalyFormal.Round10.Dictionary.PhaseSource.JSU2Loc_phase' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.PhaseSource.phase` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:459`); `AdalyFormal.Round10.Dictionary.PhaseSource.hermDiag` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:470`); `AdalyFormal.Round10.Dictionary.PhaseSource.sourceScalar` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:517`); `AdalyFormal.Round10.Dictionary.PhaseSource.JfieldLoc_phase` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:545`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem JSU2Loc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) :
    -(JSU2Loc 1 P (phase f) b) = sourceScalar P f b • pauliE3
```

</details>

<a id="bp-139"></a>
#### bp-139 — `AdalyFormal.Round10.Dictionary.Source.bulkSource_tendsto`

For every physical profile the actual source derivative is the projected divergence-of-circulation stencil, with exterior masking explicitly accounted for.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:985`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:88`: `'AdalyFormal.Round10.Dictionary.Source.bulkSource_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:23`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:48`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkU` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:202`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkP` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:206`); `AdalyFormal.Round10.Dictionary.PhaseSource.sourceField_tendsto` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:628`); `AdalyFormal.Round10.Dictionary.Source.interiorProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:966`); `AdalyFormal.Round10.Dictionary.Source.bulkU_phase` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:971`); `AdalyFormal.Round10.Dictionary.Source.profileSourceStencil` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:980`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem bulkSource_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (dataS selIn selIn (bulkP q R f ε)).J)
      (𝓝[≠] 0) (𝓝 (profileSourceStencil q R f))
```

</details>

<a id="bp-140"></a>
#### bp-140 — `AdalyFormal.Round10.Dictionary.KKT.source_of_certificate`

If physical fields satisfy the displayed full KKT residual and constraint equations, genuine base and constraint inverses identify the propagated source exactly.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:697`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:73`: `'AdalyFormal.Round10.Dictionary.KKT.source_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.KKT.Q_H` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:684`); `AdalyFormal.Round10.Dictionary.KKT.Ginv_H` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:689`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem source_of_certificate (D : BaseDataS E S F) (hL : D.Laws)
    (hB : IsUnit D.Ginv) (hN : IsUnit (N D)) (J x : E) (h : F)
    (hx : D.Q x = 0) (hr : D.Ginv x + D.Qs h = J) :
    ContinuousLinearMap.adjoint D.H J = h
```

</details>

<a id="bp-141"></a>
#### bp-141 — `AdalyFormal.Round10.Dictionary.Source.vacCoupling_neutral_top_sum`

The explicit coupling is twice the physical sum of neutral propagated-source coefficients times second-jet coefficients at level one; level-zero jets vanish.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:910`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:101`: `'AdalyFormal.Round10.Dictionary.Source.vacCoupling_neutral_top_sum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:369`); `AdalyFormal.Round9.Guarded.AnalyticR2.IsSourceDerivative` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:373`); `AdalyFormal.Round10.Dictionary.Source.neutralSource` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:827`); `AdalyFormal.Round10.Dictionary.Source.neutralCoord` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:841`); `AdalyFormal.Round10.Dictionary.Source.vacCoupling_neutral_sum` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:878`); `AdalyFormal.Round10.Dictionary.Source.vacJet` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:896`); `AdalyFormal.Round10.Dictionary.Source.C2_level_zero` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:901`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacCoupling_neutral_top_sum (q R : ℕ) (J' : TwistSpace q R)
    (hJ : IsSourceDerivative q R J') (v : TwistSpace q R) :
    vacCoupling q R J' v = 2 * ∑ p : BIdx (geomOf 2 1 (dilTower q R)) with (p.1 : ℕ) = 1,
      neutralCoord (neutralSource q R J' p) * neutralCoord (vacJet q R v p)
```

</details>

<a id="bp-142"></a>
#### bp-142 — `AdalyFormal.Round10.Dictionary.SourceEnergy.source_sbp`

Exact finite-torus summation by parts identifies source pairing with the localized mixed curl sum, with no boundary term or unspecified normalization.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1133`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:135`: `'AdalyFormal.Round10.Dictionary.SourceEnergy.source_sbp' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.PhaseSource.circulation` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:461`); `AdalyFormal.Round10.Dictionary.PhaseSource.oriented` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:507`); `AdalyFormal.Round10.Dictionary.PhaseSource.scalarDiv` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:514`); `AdalyFormal.Round10.Dictionary.PhaseSource.linearSourceScalar` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:520`); `AdalyFormal.Round10.Dictionary.SourceEnergy.div_sum` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1094`); `AdalyFormal.Round10.Dictionary.SourceEnergy.oriented_curl_point` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1116`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem source_sbp (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b : Bond L, f b * linearSourceScalar P g b) =
      ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p * circulation g p else 0
```

</details>

<a id="bp-143"></a>
#### bp-143 — `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_curl`

For every physical profile and vector, the actual coupling equals twice the selected mixed curl pairing of that profile with the constrained response profile.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1275`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:164`: `'AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_curl' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:369`); `AdalyFormal.Round10.Dictionary.PhaseSource.circulation` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:461`); `AdalyFormal.Round10.Dictionary.Source.profileSourceStencil` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:980`); `AdalyFormal.Round10.Dictionary.SourceEnergy.inner_sourceLinear` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1184`); `AdalyFormal.Round10.Dictionary.FreeSource.circulation_interiorProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1250`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1270`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem profileCoupling_curl (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = 2 *
      ∑ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        if p ∈ plaqIn ((dilTower q R).Om 0) then
          circulation (responseProfile q R u) p * circulation f p else 0
```

</details>

<a id="bp-144"></a>
#### bp-144 — `AdalyFormal.Round10.Dictionary.FreeSource.adaptive_energy`

Choosing the constrained response itself as profile gives twice its localized curl-square energy.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1292`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:167`: `'AdalyFormal.Round10.Dictionary.FreeSource.adaptive_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-143](#bp-143) (`AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_curl`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.SourceEnergy.curlEnergy` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1146`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1270`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem adaptive_energy (q R : ℕ) (u : TwistSpace q R) :
    profileCoupling q R (responseProfile q R u) u =
      2 * curlEnergy (plaqIn ((dilTower q R).Om 0)) (responseProfile q R u)
```

</details>

<a id="bp-145"></a>
#### bp-145 — `AdalyFormal.Round10.Dictionary.FreeSource.adaptive_pos_iff`

This adaptive coupling is strictly positive exactly when the response has a nonzero selected curl.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1307`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:170`: `'AdalyFormal.Round10.Dictionary.FreeSource.adaptive_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-144](#bp-144) (`AdalyFormal.Round10.Dictionary.FreeSource.adaptive_energy`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.SourceEnergy.curlEnergy_pos_iff` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1174`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1270`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1304`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem adaptive_pos_iff (q R : ℕ) (u : TwistSpace q R) :
    0 < profileCoupling q R (responseProfile q R u) u ↔ CurlDetected q R u
```

</details>

<a id="bp-146"></a>
#### bp-146 — `AdalyFormal.Round10.Dictionary.FreeSource.exists_profile_iff_curlDetected`

Some allowed free profile couples nontrivially to a vector if and only if its actual constrained response is curl-detected.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1313`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:171`: `'AdalyFormal.Round10.Dictionary.FreeSource.exists_profile_iff_curlDetected' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-143](#bp-143) (`AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_curl`); [bp-145](#bp-145) (`AdalyFormal.Round10.Dictionary.FreeSource.adaptive_pos_iff`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.PhaseSource.circulation` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:461`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1270`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1304`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_profile_iff_curlDetected (q R : ℕ) (u : TwistSpace q R) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, profileCoupling q R f u ≠ 0) ↔
      CurlDetected q R u
```

</details>

<a id="bp-147"></a>
#### bp-147 — `AdalyFormal.Round10.Dictionary.FreeSource.liftJet_Q`

The full flat constraint unit gives \(Q_0H_0z=z\) for the actual second jet; no compressed inverse is substituted.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:1364`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:183`: `'AdalyFormal.Round10.Dictionary.FreeSource.liftJet_Q' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round9.Guarded.AnalyticR2.flatData` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:366`); `AdalyFormal.Round10.Dictionary.KKT.N` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:681`); `AdalyFormal.Round10.Dictionary.KKT.Q_H` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:684`); `AdalyFormal.Round10.Dictionary.Source.vacJet` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:896`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem liftJet_Q (q R : ℕ) (hN : IsUnit (KKT.N (flatData q R))) (u : TwistSpace q R) :
    (flatData q R).Q ((flatData q R).H (vacJet q R u)) = vacJet q R u
```

</details>

<a id="bp-148"></a>
#### bp-148 — `AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet`

A nonzero physical transverse top-jet aggregate implies localized curl detection, assuming positive scale, radius at least one and the full flat constraint unit.

- **Source:** `AHP/round10/shared/dictionary/R3_JetDetection.lean:2478`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R3_JetDetection.lean.log:341`: `'AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-151](#bp-151) (`AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:331`); `AdalyFormal.Round9.Guarded.AnalyticR2.flatData` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:367`); `AdalyFormal.Round10.Dictionary.KKT.N` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:682`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:1305`); `AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_physicalJet` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:2442`); `AdalyFormal.Round10.Dictionary.JetDetection.topJetDetected_iff` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:2472`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (AdalyFormal.Round10.Dictionary.KKT.N (flatData q R)))
    (u : TwistSpace q R) (hjet : TopJetDetected hq R u) : CurlDetected q R u
```

</details>

<a id="bp-149"></a>
#### bp-149 — `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.sum_Qfull_level_one`

Summing genuine normalized level-one blocking rows over the physical transverse cells gives exactly one eighth of the two adjacent fine-layer fluxes.

- **Source:** `AHP/round10/shared/assembly/R3_JetGlue.lean:2751`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_JetGlue.lean.log:314`: `'AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.sum_Qfull_level_one' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.Flux.coarseFlux` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2306`); `AdalyFormal.Round10.Nonvanishing.TorusFlux.component` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2441`); `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.row` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2668`); `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.sum_Q1jet_row` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2729`); `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.Qfull_level_one` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2738`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem sum_Qfull_level_one (G : TowerGeom L) (hG : G.ell = 2)
    (hy : ny*2 = L 1+1) (hz : nz*2 = L 2+1)
    (p : ℕ) (hp : p+2 ≤ L 0+1) (heven : p%2 = 0)
    (hdiv : ∀ μ, 2 ∣ L μ+1) (A : BondFnL2 L) (φ : SuTwo →ₗ[ℝ] ℝ)
    (idx : Fin ny × Fin nz → BIdx G)
    (hi : ∀ c, ((idx c).1 : ℕ) = 1)
    (hb : ∀ c, (idx c).2.1 = ((row hy hz p hp heven c).1.1,1)) :
    ∑ c : Fin ny × Fin nz, φ (QfullOf G flatCfg A (idx c)) =
      coarseFlux (component (fun e => φ (A e)) 1) p
```

</details>

<a id="bp-150"></a>
#### bp-150 — `AdalyFormal.Round10.Nonvanishing.DilatedFlux.localized_curl_of_jetAggregate`

The actual constraint equation and a nonzero physical aggregate force a nonzero selected plaquette curl by transverse telescoping and a zero collar flux.

- **Source:** `AHP/round10/shared/assembly/R3_JetGlue.lean:3006`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_JetGlue.lean.log:360`: `'AdalyFormal.Round10.Nonvanishing.DilatedFlux.localized_curl_of_jetAggregate' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R3_JetGlue.lean:87`); `AdalyFormal.Round10.Nonvanishing.TorusFlux.plaq01` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2444`); `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.exists_curl_of_constrained_jet` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2767`); `AdalyFormal.Round10.Nonvanishing.PhysicalBlocking.collar_flux_zero` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2807`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.blockCount` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2872`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.blockBase` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2873`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.side_one` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2875`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.side_two` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2879`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.blockBase_even` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2883`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.blockBase_bounds` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2886`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.two_dvd_sides` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2897`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.topIdx` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2903`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.topIdx_level` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2927`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.topIdx_bond` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2930`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.collarIdx` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2947`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.collarIdx_level` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2978`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.collarIdx_bond` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2981`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.plaq01_in` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2985`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.jetAggregate` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3000`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem localized_curl_of_jetAggregate {q R j : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hj : j < blockCount q R) (φ : SuTwo →ₗ[ℝ] ℝ) (A v : BondFnL2 (L q R))
    (hQ : QfullOf (G q R) flatCfg A = C2fullOf (G q R) flatCfg v)
    (hne : jetAggregate hq hj φ v ≠ 0) :
    ∃ p ∈ plaqIn ((dilTower q R).Om 0), curlValue (fun e => φ (A e)) p ≠ 0
```

</details>

<a id="bp-151"></a>
#### bp-151 — `AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected`

Detection means that at least one actual direction-one level-one second-jet aggregate over all physical even transverse cells is nonzero.

- **Source:** `AHP/round10/shared/dictionary/R3_JetDetection.lean:2368`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R3_JetDetection.lean.log:309`: `'AdalyFormal.Round10.Nonvanishing.DilatedFlux.TopJetDetected' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.DilatedFlux.blockCount` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:2211`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.jetAggregate` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:2339`); `AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional` (`AHP/round10/shared/dictionary/R3_JetDetection.lean:2362`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def TopJetDetected {q : ℕ} (hq : 0 < q) (R : ℕ) (u : ↥(bondSupp (G q R))) : Prop
```

</details>

<a id="bp-152"></a>
#### bp-152 — `AdalyFormal.Round10.Assembly.R2.KernelLine`

A nonzero canonical kernel vector is charged under the quarter-turn and its real charged span contains the entire crossing kernel, not just one Fourier sector.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1323`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:134`: `'AdalyFormal.Round10.Assembly.R2.KernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:82`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:149`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:198`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop
```

</details>

<a id="bp-153"></a>
#### bp-153 — `AdalyFormal.Round10.Assembly.R2.corrDeriv_symmetric`

The actual named correction derivative is symmetric, including the totalized-derivative case; actual differentiability is supplied separately.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1314`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:133`: `'AdalyFormal.Round10.Assembly.R2.corrDeriv_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:23`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:48`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:52`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkP` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:190`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:194`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`); `AdalyFormal.Round10.Assembly.R2.deriv_symmetric` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1294`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem corrDeriv_symmetric (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (x y : TwistSpace q R) :
    ⟪corrDeriv q R f x, y⟫ = ⟪x, corrDeriv q R f y⟫
```

</details>

<a id="bp-154"></a>
#### bp-154 — `AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line`

A whole charged kernel line and a nonzero actual derivative pairing give canonical coupling of one sign on the entire kernel.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1334`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:135`: `'AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-103](#bp-103) (`AdalyFormal.Round9.Guarded.Qualitative.scalar_on_complex_line`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-134](#bp-134) (`AdalyFormal.Round10.Dictionary.Actual.corrDeriv_U1`); [bp-153](#bp-153) (`AdalyFormal.Round10.Assembly.R2.corrDeriv_symmetric`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:82`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:198`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_line {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u₀ : TwistSpace q R)
    (hline : KernelLine q R V u₀) (hc : ⟪u₀, corrDeriv q R f u₀⟫ ≠ 0) :
    CanonicalCoupling q R V (corrDeriv q R f)
```

</details>

<a id="bp-155"></a>
#### bp-155 — `AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_dominatedSource`

The finite source-domination certificate and a whole charged kernel line suffice for canonical coupling; their physical hypotheses remain explicit.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1360`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:136`: `'AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_dominatedSource' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-154](#bp-154) (`AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`); `AdalyFormal.Round10.Nonvanishing.BlockSourceData` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:685`); `AdalyFormal.Round10.Nonvanishing.coupling_ne_zero_of_blockSourceData` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:694`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_dominatedSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R)
    (hline : KernelLine q R V u)
    (hsource : Nonvanishing.BlockSourceData ⟪u, corrDeriv q R f u⟫) :
    CanonicalCoupling q R V (corrDeriv q R f)
```

</details>

<a id="bp-156"></a>
#### bp-156 — `AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_kernelSource`

A common coercive first-jet sign on the whole kernel and the source identity suffice without a kernel-line assumption.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1408`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:144`: `'AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_kernelSource' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:149`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`); `AdalyFormal.Round10.Nonvanishing.left` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:516`); `AdalyFormal.Round10.Nonvanishing.sourcePairing` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:523`); `AdalyFormal.Round10.Assembly.R2.signed_source_lower` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1388`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_kernelSource {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (n : ℕ) (a : ℕ → ℝ) (v : TwistSpace q R → ℕ → ℝ)
    (factor δ σ : ℝ) (hf : 0 < factor) (hδ : 0 < δ) (hσ : σ = 1 ∨ σ = -1)
    (ha : a (n+1) = 0)
    (heq : ∀ j < n+1, 6*a j + Nonvanishing.left a j + a (j+1) =
      if j = 0 then (3/2 : ℝ) else 0)
    (hjet : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ∀ j < n+1, |v u j| ≤ |v u 0|)
    (hfirst : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      δ * ‖u‖^2 ≤ σ * v u 0)
    (hform : ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
      ⟪u, corrDeriv q R f u⟫ = factor * Nonvanishing.sourcePairing n a (v u)) :
    CanonicalCoupling q R V (corrDeriv q R f)
```

</details>

<a id="bp-157"></a>
#### bp-157 — `AdalyFormal.Round10.Assembly.R2.exists_profile_coupling_of_sourceFamily`

The exact finite source-family dictionary, a nonzero jet vector and a whole kernel line yield some definite physical profile.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1440`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:124`: `'AdalyFormal.Round10.Assembly.R2.exists_profile_coupling_of_sourceFamily' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-154](#bp-154) (`AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceResponse` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1140`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.exists_actual_coupling_of_source_dictionary` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1210`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_profile_coupling_of_sourceFamily {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ =
      factor * Nonvanishing.FreeProfile.sourceResponse N i b) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i))
```

</details>

<a id="bp-158"></a>
#### bp-158 — `AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_sourceFamily`

Nested cofinal physical source-family data imply the original free-profile coupling premise.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1482`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:129`: `'AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_sourceFamily' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-157](#bp-157) (`AdalyFormal.Round10.Assembly.R2.exists_profile_coupling_of_sourceFamily`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:146`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:420`); `AdalyFormal.Round10.Assembly.R2.CofinalSourceFamily` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1478`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyProfileCoupling_of_sourceFamily (h : CofinalSourceFamily) :
    CofinalAnyProfileCoupling
```

</details>

<a id="bp-159"></a>
#### bp-159 — `AdalyFormal.Round10.Assembly.R3.ProfileRegular`

The regularity package consists precisely of continuity of the actual lift, convergence of the dressed quadratic jet and the genuine correction derivative for a profile.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2135`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:230`: `'AdalyFormal.Round10.Assembly.R3.ProfileRegular' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1455`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1518`); `AdalyFormal.Round10.Assembly.R3.profileData` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:2130`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def ProfileRegular (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop
```

</details>

<a id="bp-160"></a>
#### bp-160 — `AdalyFormal.Round10.Assembly.R3.RegularityFacts`

The package quantifies those actual regularity facts over positive scales, even radii at least eighteen, and every profile.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2141`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:231`: `'AdalyFormal.Round10.Assembly.R3.RegularityFacts' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-159](#bp-159) (`AdalyFormal.Round10.Assembly.R3.ProfileRegular`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def RegularityFacts : Prop
```

</details>

<a id="bp-161"></a>
#### bp-161 — `AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form`

Under the explicit profile regularity package, the original correction derivative form equals the actual physical profile coupling.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2169`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:234`: `'AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-139](#bp-139) (`AdalyFormal.Round10.Dictionary.Source.bulkSource_tendsto`); [bp-094](#bp-094) (`AdalyFormal.Round9.Guarded.AnalyticR2.limit_Delta2_div_form`); [bp-159](#bp-159) (`AdalyFormal.Round10.Assembly.R3.ProfileRegular`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:23`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:48`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:52`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkP` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:206`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.PhaseSource.tendsto_div_of_hasDerivAt_zero` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:622`); `AdalyFormal.Round10.Dictionary.Source.profileSourceStencil` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:980`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1270`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1455`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1518`); `AdalyFormal.Round10.Assembly.R3.profileData` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:2130`); `AdalyFormal.Round10.Assembly.R3.bulkD_zero_source` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:2146`); `AdalyFormal.Round10.Assembly.R3.bulkData_zero` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:2158`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem corrDeriv_profile_form (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hr : ProfileRegular q R f)
    (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u
```

</details>

<a id="bp-162"></a>
#### bp-162 — `AdalyFormal.Round10.Assembly.R3.canonicalCoupling_of_curlDetected`

A curl-detected generator of the whole charged kernel line yields one definite adaptive profile, using the actual derivative identity and regularity.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2188`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:235`: `'AdalyFormal.Round10.Assembly.R3.canonicalCoupling_of_curlDetected' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-145](#bp-145) (`AdalyFormal.Round10.Dictionary.FreeSource.adaptive_pos_iff`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-154](#bp-154) (`AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line`); [bp-159](#bp-159) (`AdalyFormal.Round10.Assembly.R3.ProfileRegular`); [bp-161](#bp-161) (`AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1304`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1518`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_curlDetected {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (hcurl : CurlDetected q R u)
    (hr : ProfileRegular q R (Dictionary.FreeSource.responseProfile q R u)) :
    CanonicalCoupling q R V
      (corrDeriv q R (Dictionary.FreeSource.responseProfile q R u))
```

</details>

<a id="bp-163"></a>
#### bp-163 — `AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`

Above every scale bound choose a dyadic scale with arbitrarily large even radii, valid free paths, and generators simultaneously satisfying whole-kernel line containment and curl detection.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2208`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:239`: `'AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1304`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1426`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1684`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CofinalAnyPathCurlLine : Prop
```

</details>

<a id="bp-164"></a>
#### bp-164 — `AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCoupling_of_curlLine`

Cofinal detected charged kernel lines imply the original free-path coupling premise, with the regularity package explicit.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2226`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:243`: `'AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCoupling_of_curlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-128](#bp-128) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`); [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-162](#bp-162) (`AdalyFormal.Round10.Assembly.R3.canonicalCoupling_of_curlDetected`); [bp-163](#bp-163) (`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`)
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyPathCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalAnyPathCurlLine) :
    CofinalAnyPathCoupling
```

</details>

<a id="bp-165"></a>
#### bp-165 — `AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCurlLine_of_jetLine`

Cofinal nonzero physical top jets on whole charged kernel lines imply cofinal curl-line data, assuming the full flat constraint units.

- **Source:** `AHP/round10/shared/assembly/R3_JetGlue.lean:3163`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_JetGlue.lean.log:382`: `'AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCurlLine_of_jetLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-163](#bp-163) (`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`)
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_physicalJet` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3078`); `AdalyFormal.Round10.Assembly.R3.FlatConstraintUnits` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3131`); `AdalyFormal.Round10.Assembly.R3.CofinalAnyPathJetLine` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3143`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyPathCurlLine_of_jetLine (hN : FlatConstraintUnits)
    (h : CofinalAnyPathJetLine) : CofinalAnyPathCurlLine
```

</details>

<a id="bp-166"></a>
#### bp-166 — `AdalyFormal.Round10.Assembly.R4.responseHull`

The response hull is the closed convex hull of the responses of all unit vectors in the specified real kernel subspace.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2264`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:246`: `'AdalyFormal.Round10.Assembly.R4.responseHull' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def responseHull (K : Submodule ℝ E) (Q : E → F) : Set F
```

</details>

<a id="bp-167"></a>
#### bp-167 — `AdalyFormal.Round10.Assembly.R4.common_coercive_iff_notMem_responseHull`

For a quadratically homogeneous response, one common coercive real functional exists exactly when zero lies outside that closed convex hull.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2317`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:256`: `'AdalyFormal.Round10.Assembly.R4.common_coercive_iff_notMem_responseHull' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-166](#bp-166) (`AdalyFormal.Round10.Assembly.R4.responseHull`)
- **Additional local source references:** `AdalyFormal.Round10.Assembly.R4.separator_of_notMem_responseHull` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2267`); `AdalyFormal.Round10.Assembly.R4.notMem_responseHull_of_separator` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2277`); `AdalyFormal.Round10.Assembly.R4.norm_square_lower_of_unit_lower` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2292`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem common_coercive_iff_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u) :
    (∃ (f : F →L[ℝ] ℝ) (c : ℝ), 0 < c ∧
      ∀ u, u ∈ K → c * ‖u‖ ^ 2 ≤ f (Q u)) ↔
    (0 : F) ∉ responseHull K Q
```

</details>

<a id="bp-168"></a>
#### bp-168 — `AdalyFormal.Round10.Assembly.R4.responseGradient`

The physical response gradient is twice the localized curl adjoint applied to the response curl, in the Euclidean space of all fine bonds.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2375`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:263`: `'AdalyFormal.Round10.Assembly.R4.responseGradient' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:330`); `AdalyFormal.Round10.Dictionary.PhaseSource.linearSourceScalar` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:520`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1264`); `AdalyFormal.Round10.Assembly.R4.ProfileSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2372`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def responseGradient (q R : ℕ) (u : TwistSpace q R) : ProfileSpace q R
```

</details>

<a id="bp-169"></a>
#### bp-169 — `AdalyFormal.Round10.Assembly.R4.profileCoupling_gradient`

Pairing any physical profile with the response gradient equals the actual profile coupling, with exact sign and factor two.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2379`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:264`: `'AdalyFormal.Round10.Assembly.R4.profileCoupling_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-142](#bp-142) (`AdalyFormal.Round10.Dictionary.SourceEnergy.source_sbp`); [bp-143](#bp-143) (`AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_curl`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:330`); `AdalyFormal.Round10.Dictionary.PhaseSource.circulation` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:461`); `AdalyFormal.Round10.Dictionary.PhaseSource.linearSourceScalar` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:520`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1264`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1270`); `AdalyFormal.Round10.Assembly.R4.ProfileSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2372`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem profileCoupling_gradient (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = ⟪(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫
```

</details>

<a id="bp-170"></a>
#### bp-170 — `AdalyFormal.Round10.Assembly.R4.crossingKernel`

The crossing kernel is the kernel of the actual vacuum carrier at its canonical PSD edge.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2423`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:268`: `'AdalyFormal.Round10.Assembly.R4.crossingKernel' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:330`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1426`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def crossingKernel (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R)
```

</details>

<a id="bp-171"></a>
#### bp-171 — `AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`

Zero is excluded from the closed convex hull of the gradients of all unit vectors in that complete crossing kernel.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2428`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:269`: `'AdalyFormal.Round10.Assembly.R4.NoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-166](#bp-166) (`AdalyFormal.Round10.Assembly.R4.responseHull`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-170](#bp-170) (`AdalyFormal.Round10.Assembly.R4.crossingKernel`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round10.Assembly.R4.ProfileSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2372`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop
```

</details>

<a id="bp-172"></a>
#### bp-172 — `AdalyFormal.Round10.Assembly.R4.exists_positive_profile_iff_noCancellation`

A single strictly positive coercive profile on the full crossing kernel exists exactly when the response hull excludes zero.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2432`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:270`: `'AdalyFormal.Round10.Assembly.R4.exists_positive_profile_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-167](#bp-167) (`AdalyFormal.Round10.Assembly.R4.common_coercive_iff_notMem_responseHull`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-169](#bp-169) (`AdalyFormal.Round10.Assembly.R4.profileCoupling_gradient`); [bp-170](#bp-170) (`AdalyFormal.Round10.Assembly.R4.crossingKernel`); [bp-171](#bp-171) (`AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1270`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1426`); `AdalyFormal.Round10.Assembly.R4.ProfileSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2372`); `AdalyFormal.Round10.Assembly.R4.responseGradient_smul` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2415`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_positive_profile_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    (∃ (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ), 0 < c ∧
      ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
        c * ‖u‖ ^ 2 ≤ profileCoupling q R f u) ↔ NoResponseCancellation q R V
```

</details>

<a id="bp-173"></a>
#### bp-173 — `AdalyFormal.Round10.Assembly.R4.exists_canonicalCoupling_iff_noCancellation`

Given actual profile regularity, existence of an original canonical coupling is equivalent to whole-kernel response noncancellation; a negative profile can be sign-reversed.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2463`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:274`: `'AdalyFormal.Round10.Assembly.R4.exists_canonicalCoupling_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-159](#bp-159) (`AdalyFormal.Round10.Assembly.R3.ProfileRegular`); [bp-161](#bp-161) (`AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form`); [bp-171](#bp-171) (`AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`); [bp-172](#bp-172) (`AdalyFormal.Round10.Assembly.R4.exists_positive_profile_iff_noCancellation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1518`); `AdalyFormal.Round10.Assembly.R4.profileCoupling_neg_profile` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2454`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_canonicalCoupling_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hr : ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ,
      CanonicalCoupling q R V (corrDeriv q R f)) ↔ NoResponseCancellation q R V
```

</details>

<a id="bp-174"></a>
#### bp-174 — `AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_iff`

A vector has nonzero actual response gradient exactly when it is curl-detected.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2524`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:280`: `'AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-146](#bp-146) (`AdalyFormal.Round10.Dictionary.FreeSource.exists_profile_iff_curlDetected`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-169](#bp-169) (`AdalyFormal.Round10.Assembly.R4.profileCoupling_gradient`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1304`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem responseGradient_ne_zero_iff (q R : ℕ) (u : TwistSpace q R) :
    responseGradient q R u ≠ 0 ↔ CurlDetected q R u
```

</details>

<a id="bp-175"></a>
#### bp-175 — `AdalyFormal.Round10.Assembly.R4.curlDetected_of_noCancellation`

Whole-kernel noncancellation necessarily detects every nonzero crossing-kernel vector; vectorwise detection alone does not imply the converse.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2537`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:283`: `'AdalyFormal.Round10.Assembly.R4.curlDetected_of_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-171](#bp-171) (`AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`); [bp-174](#bp-174) (`AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_iff`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1304`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1426`); `AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_of_noCancellation` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2484`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem curlDetected_of_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (h : NoResponseCancellation q R V) (u : TwistSpace q R)
    (hu : vacA q R V 1 (vacEdge q R V) u = 0) (hne : u ≠ 0) :
    CurlDetected q R u
```

</details>

<a id="bp-176"></a>
#### bp-176 — `AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`

The preferred open premise adds whole-kernel response-hull noncancellation to the nested dyadic/even-radius valid-path clauses.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2550`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:289`: `'AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-171](#bp-171) (`AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:83`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1426`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1684`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def CofinalAnyPathNoResponseCancellation : Prop
```

</details>

<a id="bp-177"></a>
#### bp-177 — `AdalyFormal.Round10.Assembly.R4.cofinalAnyPathCoupling_iff_noCancellation`

Under the explicit regularity facts, the original free-path coupling premise is equivalent to the preferred cofinal response-hull premise.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2576`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:295`: `'AdalyFormal.Round10.Assembly.R4.cofinalAnyPathCoupling_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-128](#bp-128) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`); [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-173](#bp-173) (`AdalyFormal.Round10.Assembly.R4.exists_canonicalCoupling_iff_noCancellation`); [bp-176](#bp-176) (`AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyPathCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation
```

</details>

<a id="bp-178"></a>
#### bp-178 — `AdalyFormal.Round10.Assembly.R4.cofinalAnyPathNoCancellation_of_curlLine`

The older cofinal charged-line route implies noncancellation using the regularity-based coupling bridge; round twelve provides a direct version without that regularity premise.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2599`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:301`: `'AdalyFormal.Round10.Assembly.R4.cofinalAnyPathNoCancellation_of_curlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-163](#bp-163) (`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`); [bp-164](#bp-164) (`AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCoupling_of_curlLine`); [bp-176](#bp-176) (`AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`); [bp-177](#bp-177) (`AdalyFormal.Round10.Assembly.R4.cofinalAnyPathCoupling_iff_noCancellation`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyPathNoCancellation_of_curlLine (hr : RegularityFacts)
    (h : R3.CofinalAnyPathCurlLine) : CofinalAnyPathNoResponseCancellation
```

</details>

<a id="bp-179"></a>
#### bp-179 — `AdalyFormal.Round10.Assembly.ProfileQuantifiers.every_vector_has_profile`

A concrete U(1)-invariant traceless quadratic pencil detects every nonzero vector with a vector-dependent profile.

- **Source:** `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:34`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean.log:7`: `'AdalyFormal.Round10.Assembly.ProfileQuantifiers.every_vector_has_profile' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Assembly.ProfileQuantifiers.form` (`AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:9`); `AdalyFormal.Round10.Assembly.ProfileQuantifiers.self_profile` (`AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:26`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem every_vector_has_profile (z w : ℂ) (hne : z ≠ 0 ∨ w ≠ 0) :
    ∃ a b c : ℝ, 0 < form a b c z w
```

</details>

<a id="bp-180"></a>
#### bp-180 — `AdalyFormal.Round10.Assembly.ProfileQuantifiers.no_profile_definite`

No single profile in that pencil is definite on the whole space, disproving the exchange of vectorwise and common-profile quantifiers.

- **Source:** `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:47`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean.log:10`: `'AdalyFormal.Round10.Assembly.ProfileQuantifiers.no_profile_definite' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Assembly.ProfileQuantifiers.form` (`AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:9`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem no_profile_definite (a b c : ℝ) :
    ¬ ((∀ z w : ℂ, z ≠ 0 ∨ w ≠ 0 → 0 < form a b c z w) ∨
       (∀ z w : ℂ, z ≠ 0 ∨ w ≠ 0 → form a b c z w < 0))
```

</details>

<a id="bp-181"></a>
#### bp-181 — `AdalyFormal.Round10.Dictionary.ColorResponse.vacJet_chargedPart_component`

Charged projection preserves the neutral component of the actual dressed jet and makes the full projected jet neutral.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:1931`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:276`: `'AdalyFormal.Round10.Dictionary.ColorResponse.vacJet_chargedPart_component' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:330`); `AdalyFormal.Round10.Dictionary.Source.neutralCoord` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:841`); `AdalyFormal.Round10.Dictionary.Source.vacJet` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:896`); `AdalyFormal.Round10.Dictionary.Color.flatJet_charged_neutral` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1779`); `AdalyFormal.Round10.Dictionary.ColorResponse.chargedPart` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1862`); `AdalyFormal.Round10.Dictionary.ColorResponse.chargedPart_neg` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1873`); `AdalyFormal.Round10.Dictionary.ColorResponse.neutralJet_chargedPart` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1919`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacJet_chargedPart_component (q R : ℕ) (u : TwistSpace q R)
    (p : BIdx (geomOf 2 1 (dilTower q R))) :
    vacJet q R (chargedPart (geomOf 2 1 (dilTower q R)) u) p =
      neutralCoord (vacJet q R u p) • pauliE3
```

</details>

<a id="bp-182"></a>
#### bp-182 — `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_chargedPart`

The actual free-profile response depends only on the charged part of the input.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:1993`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:298`: `'AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_chargedPart' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1264`); `AdalyFormal.Round10.Dictionary.Color.quad_add_of_invariant` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1647`); `AdalyFormal.Round10.Dictionary.Color.halfE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1693`); `AdalyFormal.Round10.Dictionary.ColorResponse.chargedPart` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1862`); `AdalyFormal.Round10.Dictionary.ColorResponse.color_decomposition` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1865`); `AdalyFormal.Round10.Dictionary.ColorResponse.neutralPart_fixed` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1868`); `AdalyFormal.Round10.Dictionary.ColorResponse.chargedPart_neg` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1873`); `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_quad` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1958`); `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_rot` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1966`); `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_neutralPart_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1987`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem responseProfile_chargedPart (q R : ℕ) (u : TwistSpace q R) :
    responseProfile q R (chargedPart (geomOf 2 1 (dilTower q R)) u) = responseProfile q R u
```

</details>

<a id="bp-183"></a>
#### bp-183 — `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_mixed`

Between opposite flip eigenspaces the response is purely mixed and scales by the product of their amplitudes; nonzero mixed response is not automatic.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:2027`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:313`: `'AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1264`); `AdalyFormal.Round10.Dictionary.Color.quad_mixed_scaling` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1673`); `AdalyFormal.Round10.Dictionary.Color.flipE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1696`); `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_quad` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1958`); `AdalyFormal.Round10.Dictionary.ColorResponse.responseProfile_flip_eigen_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2013`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem responseProfile_mixed (q R : ℕ) (x y : TwistSpace q R)
    (hx : flipE (geomOf 2 1 (dilTower q R)) x = x)
    (hy : flipE (geomOf 2 1 (dilTower q R)) y = -y) (a b : ℝ) :
    responseProfile q R (a • x + b • y) = (a * b) • responseProfile q R (x + y)
```

</details>

<a id="bp-184"></a>
#### bp-184 — `AdalyFormal.Round10.Dictionary.ColorObstruction.exists_charged_invisible`

For every positive scale there is a nonzero charged physical carrier field with zero full dressed jet and zero coupling to every profile. It is not shown to be a crossing vector.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:2168`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:342`: `'AdalyFormal.Round10.Dictionary.ColorObstruction.exists_charged_invisible' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:86`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:330`); `AdalyFormal.Round10.Dictionary.Source.vacJet` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:896`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1270`); `AdalyFormal.Round10.Dictionary.Color.halfE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1693`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2110`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_ne_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2114`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_charged` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2136`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_jet_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2160`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_all_profiles_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2163`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_charged_invisible {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∃ u : TwistSpace q R, u ≠ 0 ∧ halfE (geomOf 2 1 (dilTower q R)) u = -u ∧
      vacJet q R u = 0 ∧ (∀ f, profileCoupling q R f u = 0)
```

</details>

<a id="bp-185"></a>
#### bp-185 — `AdalyFormal.Round10.Nonvanishing.sourcePairing_lower`

The finite tridiagonal source equations and domination by a nonzero first jet give a pairing at least four nineteenths of that first jet in absolute value.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:629`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:10`: `'AdalyFormal.Round10.Nonvanishing.sourcePairing_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.left` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:516`); `AdalyFormal.Round10.Nonvanishing.sourcePairing` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:523`); `AdalyFormal.Round10.Nonvanishing.sourcePairing_error` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:603`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem sourcePairing_lower (n : ℕ) (a v : ℕ → ℝ) (ha : a (n + 1) = 0)
    (heq : ∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0)
    (hv : ∀ j < n + 1, |v j| ≤ |v 0|) :
    (4 / 19 : ℝ) * |v 0| ≤ |sourcePairing n a v|
```

</details>

<a id="bp-186"></a>
#### bp-186 — `AdalyFormal.Round10.Nonvanishing.recurrence_cofinal_nonzero`

A reversible finite scalar recurrence with one nonzero seed cannot have an eventually zero tail; applying it to the physical moving crossing needs an exact representation.

- **Source:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:45`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean.log:5`: `'AdalyFormal.Round10.Nonvanishing.recurrence_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.recurrence_eq_zero_of_zero_tail` (`AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:29`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem recurrence_cofinal_nonzero {K : Type*} [Field K]
    (d : ℕ) (c u : ℕ → K) (hc : c 0 ≠ 0)
    (hr : ∀ n, u (n + (d + 1)) = ∑ i ∈ range (d + 1), c i * u (n + i))
    (k : ℕ) (hk : u k ≠ 0) : ∀ N, ∃ n, N ≤ n ∧ u n ≠ 0
```

</details>

<a id="bp-187"></a>
#### bp-187 — `AdalyFormal.Round10.Nonvanishing.transfer_cofinal_nonzero`

An injective finite-dimensional transfer map and a nonzero observable seed yield cofinally many nonzero iterates; no physical transfer certificate is supplied.

- **Source:** `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean:53`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean.log:5`: `'AdalyFormal.Round10.Nonvanishing.transfer_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.transfer_eq_zero_of_zero_tail` (`AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean:26`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem transfer_cofinal_nonzero (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (k : ℕ) (hk : L ((T ^ k) x) ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ L ((T ^ n) x) ≠ 0
```

</details>

<a id="bp-188"></a>
#### bp-188 — `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceResponse_pos`

The finite Dirichlet source-family response form is strictly positive for every nonzero finite jet vector, by its fine-lattice energy identity.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1180`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:112`: `'AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceResponse_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.FreeProfile.prev` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:929`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.exists_tri_solution` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:980`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.tridiagonal_response_pos` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1044`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceAmplitude` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1123`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceAmplitude_boundary` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1126`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceAmplitude_equation` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1129`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceResponse` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1140`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.column_pairing` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1148`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem sourceResponse_pos (n : ℕ) (b : ℕ → ℝ) (hb : b n = 0)
    (hne : ∃ j < n, b j ≠ 0) :
    0 < ∑ i ∈ range n, b i * sourceResponse n i b
```

</details>

<a id="bp-189"></a>
#### bp-189 — `AdalyFormal.Round10.Nonvanishing.FreeProfile.exists_coupling_of_source_columns`

Exact source-column equations and a physical nonzero normalization detect some component of every nonzero jet vector; the operator dictionary remains explicit.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1237`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:86`: `'AdalyFormal.Round10.Nonvanishing.FreeProfile.exists_coupling_of_source_columns' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.FreeProfile.prev` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:929`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceRhs` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1118`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.columnWeight` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1135`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.source_columns_separate` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1221`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_coupling_of_source_columns (n : ℕ) (b coupling : ℕ → ℝ)
    (c : ℕ → ℕ → ℝ) (factor : ℝ)
    (hb : b n = 0) (hne : ∃ j < n, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < n, c i n = 0)
    (heq : ∀ i < n, ∀ j < n,
      6*c i j + prev (c i) j + c i (j+1) = sourceRhs i j)
    (hdict : ∀ i < n, coupling i = factor *
      (∑ j ∈ range n, columnWeight (c i) i j * b j)) :
    ∃ i < n, coupling i ≠ 0
```

</details>

<a id="bp-190"></a>
#### bp-190 — `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.moving_root_cofinal_nonzero`

A fixed finite Bezout certificate for the moving crossing and cleared coupling numerator gives nested cofinal scalar nonvanishing.

- **Source:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:186`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean.log:41`: `'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.moving_root_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.geometric_grid_ne_zero_of_seed` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:86`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.coupling_ne_zero_of_bezout` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:151`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.MovingRootCertificate` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:163`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem moving_root_cofinal_nonzero (coupling : ℕ → ℕ → ℝ)
    (d : MovingRootCertificate coupling) :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling (2 ^ j) R ≠ 0
```

</details>

<a id="bp-191"></a>
#### bp-191 — `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.switchingRoot_not_cofinal`

An algebraic crossing equation and one exact nonzero sample do not imply cofinal nonvanishing: a permitted root choice can switch to a common zero.

- **Source:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:286`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean.log:77`: `'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.switchingRoot_not_cofinal' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.switchingRoot` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:258`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.switchingRoot_zero_large_radius` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:279`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem switchingRoot_not_cofinal : ¬ (∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      switchingRoot (2 ^ j) R ≠ 0)
```

</details>

### Round 12: consistent right star and whole-kernel reduction

<a id="bp-192"></a>
#### bp-192 — `AdalyFormal.Round12.Noncancel.Star.pair_completion`

The charged two-leaf form plus two leaf masses is exactly a retained cosine-weighted mass plus one complex square when \(c^2+s^2=1\).

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:33`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:6`: `'AdalyFormal.Round12.Noncancel.Star.pair_completion' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.pairForm` (`AHP/round12/shared/noncancel/R1_Star.lean:12`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pair_completion (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    Complex.normSq y + Complex.normSq z + pairForm c s y z =
      c * (Complex.normSq y + Complex.normSq z) +
        Complex.normSq (y + ((c : ℂ) - (s : ℂ) * Complex.I) * z)
```

</details>

<a id="bp-193"></a>
#### bp-193 — `AdalyFormal.Round12.Noncancel.Star.kernel_line_of_trace`

Strict positivity on the zero fiber of one complex trace, quarter-turn covariance and a nonzero kernel vector force the complete kernel into one charged complex line.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:88`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:11`: `'AdalyFormal.Round12.Noncancel.Star.kernel_line_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.trace_ne_zero` (`AHP/round12/shared/noncancel/R1_Star.lean:68`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernel_line_of_trace (A J : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ u, A (J u) = J (A u))
    (htrace : ∀ u, l (J u) = Complex.I * l u)
    (hp : ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    (u₀ : E) (hu₀ : A u₀ = 0) (hne : u₀ ≠ 0) :
    J (J u₀) = -u₀ ∧
      ∀ u, A u = 0 → u ∈ Submodule.span ℝ {u₀, J u₀}
```

</details>

<a id="bp-194"></a>
#### bp-194 — `AdalyFormal.Round12.Noncancel.Star.starTrial_negative`

The surrogate polynomial trial energy at amplitudes one quarter and one quarter is exactly minus one quarter; identification with the physical half-pi trial is not part of this theorem.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:153`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:15`: `'AdalyFormal.Round12.Noncancel.Star.starTrial_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.starTrialEnergy` (`AHP/round12/shared/noncancel/R1_Star.lean:148`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem starTrial_negative : starTrialEnergy (1/4) (1/4) = -1/4
```

</details>

<a id="bp-195"></a>
#### bp-195 — `AdalyFormal.Round12.Noncancel.Plaquette.frozen_three_form`

With the displayed left-oriented transported atoms and holonomy, the frozen plaquette form equals the explicit charged three-atom form.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:236`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:25`: `'AdalyFormal.Round12.Noncancel.Plaquette.frozen_three_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.tripleForm` (`AHP/round12/shared/noncancel/R1_Star.lean:16`); `AdalyFormal.Round12.Noncancel.Plaquette.chargedMat` (`AHP/round12/shared/noncancel/R1_Star.lean:186`); `AdalyFormal.Round12.Noncancel.Plaquette.realHol` (`AHP/round12/shared/noncancel/R1_Star.lean:187`); `AdalyFormal.Round12.Noncancel.Plaquette.imagHol` (`AHP/round12/shared/noncancel/R1_Star.lean:188`); `AdalyFormal.Round12.Noncancel.Plaquette.chargedMat_add` (`AHP/round12/shared/noncancel/R1_Star.lean:190`); `AdalyFormal.Round12.Noncancel.Plaquette.charged_inner` (`AHP/round12/shared/noncancel/R1_Star.lean:198`); `AdalyFormal.Round12.Noncancel.Plaquette.first_atom` (`AHP/round12/shared/noncancel/R1_Star.lean:206`); `AdalyFormal.Round12.Noncancel.Plaquette.comm_atom` (`AHP/round12/shared/noncancel/R1_Star.lean:213`); `AdalyFormal.Round12.Noncancel.Plaquette.curl_atoms` (`AHP/round12/shared/noncancel/R1_Star.lean:224`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem frozen_three_form
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = chargedMat y) (h4 : a4LM U p A = chargedMat z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z
```

</details>

<a id="bp-196"></a>
#### bp-196 — `AdalyFormal.Round12.Noncancel.Plaquette.frozen_three_form_right`

The separate right-oriented atom convention gives the corresponding exact charged three-atom form; no reflection equivalence is assumed.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:258`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:26`: `'AdalyFormal.Round12.Noncancel.Plaquette.frozen_three_form_right' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.tripleForm` (`AHP/round12/shared/noncancel/R1_Star.lean:16`); `AdalyFormal.Round12.Noncancel.Plaquette.chargedMat` (`AHP/round12/shared/noncancel/R1_Star.lean:186`); `AdalyFormal.Round12.Noncancel.Plaquette.realHol` (`AHP/round12/shared/noncancel/R1_Star.lean:187`); `AdalyFormal.Round12.Noncancel.Plaquette.imagHol` (`AHP/round12/shared/noncancel/R1_Star.lean:188`); `AdalyFormal.Round12.Noncancel.Plaquette.chargedMat_add` (`AHP/round12/shared/noncancel/R1_Star.lean:190`); `AdalyFormal.Round12.Noncancel.Plaquette.charged_inner` (`AHP/round12/shared/noncancel/R1_Star.lean:198`); `AdalyFormal.Round12.Noncancel.Plaquette.first_atom` (`AHP/round12/shared/noncancel/R1_Star.lean:206`); `AdalyFormal.Round12.Noncancel.Plaquette.comm_atom` (`AHP/round12/shared/noncancel/R1_Star.lean:213`); `AdalyFormal.Round12.Noncancel.Plaquette.curl_atoms` (`AHP/round12/shared/noncancel/R1_Star.lean:224`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem frozen_three_form_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z
```

</details>

<a id="bp-197"></a>
#### bp-197 — `AdalyFormal.Round12.Noncancel.Trace.physical_kernel_line`

The abstract trace criterion applies to the actual touching-bond trace and constant-gauge quarter-turn, retaining strict positivity and operator commutation as hypotheses.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:351`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:34`: `'AdalyFormal.Round12.Noncancel.Trace.physical_kernel_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-193](#bp-193) (`AdalyFormal.Round12.Noncancel.Star.kernel_line_of_trace`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Trace.bondTrace` (`AHP/round12/shared/noncancel/R1_Star.lean:319`); `AdalyFormal.Round12.Noncancel.Trace.quarter` (`AHP/round12/shared/noncancel/R1_Star.lean:326`); `AdalyFormal.Round12.Noncancel.Trace.bondTrace_quarter` (`AHP/round12/shared/noncancel/R1_Star.lean:341`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem physical_kernel_line (G : TowerGeom L) (b : Bond L)
    (A : ↥(bondSupp G) →L[ℝ] ↥(bondSupp G))
    (hcomm : ∀ u, A (quarter G u) = quarter G (A u))
    (hp : ∀ u, bondTrace G b u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫)
    (u₀ : ↥(bondSupp G)) (hu₀ : A u₀ = 0) (hne : u₀ ≠ 0) :
    quarter G (quarter G u₀) = -u₀ ∧
      ∀ u, A u = 0 → u ∈ Submodule.span ℝ {u₀, quarter G u₀}
```

</details>

<a id="bp-198"></a>
#### bp-198 — `AdalyFormal.Round12.Noncancel.Path.starPath`

The exterior star twists the four transverse links at one physical site and its two transverse predecessors, leaving all other links trivial.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:434`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:40`: `'AdalyFormal.Round12.Noncancel.Path.starPath' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Path.starLinks` (`AHP/round12/shared/noncancel/R1_Star.lean:429`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L
```

</details>

<a id="bp-199"></a>
#### bp-199 — `AdalyFormal.Round12.Noncancel.Path.star_negative_endpoint`

An admissible right-boundary star has a genuine negative all-plaquette carrier direction at \(\pi\) for the stated mass and room bounds.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:527`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:50`: `'AdalyFormal.Round12.Noncancel.Path.star_negative_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-198](#bp-198) (`AdalyFormal.Round12.Noncancel.Path.starPath`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Path.starPath_interior` (`AHP/round12/shared/noncancel/R1_Star.lean:479`); `AdalyFormal.Round12.Noncancel.Path.star_holonomy1` (`AHP/round12/shared/noncancel/R1_Star.lean:490`); `AdalyFormal.Round12.Noncancel.Path.star_holonomy2` (`AHP/round12/shared/noncancel/R1_Star.lean:505`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem star_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0
```

</details>

<a id="bp-200"></a>
#### bp-200 — `AdalyFormal.Round12.Noncancel.Gauge.starPath_fixed`

The diagonal star background is fixed by every constant diagonal gauge rotation.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:650`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:53`: `'AdalyFormal.Round12.Noncancel.Gauge.starPath_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-198](#bp-198) (`AdalyFormal.Round12.Noncancel.Path.starPath`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Path.starLinks` (`AHP/round12/shared/noncancel/R1_Star.lean:429`); `AdalyFormal.Round12.Noncancel.Gauge.uθ_comm` (`AHP/round12/shared/noncancel/R1_Star.lean:643`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem starPath_fixed {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (starPath x t) = starPath x t
```

</details>

<a id="bp-201"></a>
#### bp-201 — `AdalyFormal.Round12.Noncancel.Gauge.star_all_comm`

The genuine all-plaquette star carrier commutes with those rotations, using frozen gauge covariance.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:660`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:54`: `'AdalyFormal.Round12.Noncancel.Gauge.star_all_comm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-198](#bp-198) (`AdalyFormal.Round12.Noncancel.Path.starPath`); [bp-200](#bp-200) (`AdalyFormal.Round12.Noncancel.Gauge.starPath_fixed`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Gauge.Ginv_all_gauge` (`AHP/round12/shared/noncancel/R1_Star.lean:601`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem star_all_comm {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (t α : ℝ)
    (u : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv
      (adEL (fun _ => uθ α) (geomOf ell k S) u) =
      adEL (fun _ => uθ α) (geomOf ell k S)
        ((dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u)
```

</details>

<a id="bp-202"></a>
#### bp-202 — `AdalyFormal.Round12.Noncancel.Gauge.star_kernel_line`

For the actual star carrier, a nonzero kernel vector and strict zero-trace positivity yield whole-kernel charged-line containment; neither physical hypothesis is proved here.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:673`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:55`: `'AdalyFormal.Round12.Noncancel.Gauge.star_kernel_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-197](#bp-197) (`AdalyFormal.Round12.Noncancel.Trace.physical_kernel_line`); [bp-198](#bp-198) (`AdalyFormal.Round12.Noncancel.Path.starPath`); [bp-201](#bp-201) (`AdalyFormal.Round12.Noncancel.Gauge.star_all_comm`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Trace.bondTrace` (`AHP/round12/shared/noncancel/R1_Star.lean:319`); `AdalyFormal.Round12.Noncancel.Trace.quarter` (`AHP/round12/shared/noncancel/R1_Star.lean:326`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem star_kernel_line {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (x : PeriodicLatticeSite (scaleUp ell k Lu))
    (b : Bond (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu)) (t : ℝ)
    (hp : ∀ u, Trace.bondTrace (geomOf ell k S) b u = 0 → u ≠ 0 →
      0 < ⟪u, (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u⟫)
    (u₀ : ↥(bondSupp (geomOf ell k S)))
    (hu₀ : (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u₀ = 0)
    (hne : u₀ ≠ 0) :
    Trace.quarter (geomOf ell k S) (Trace.quarter (geomOf ell k S) u₀) = -u₀ ∧
      ∀ u, (dataS selAll selAll (gparams ell k Lu hell S (starPath x t) a Lam)).Ginv u = 0 →
        u ∈ Submodule.span ℝ {u₀, Trace.quarter (geomOf ell k S) u₀}
```

</details>

<a id="bp-203"></a>
#### bp-203 — `AdalyFormal.Round12.Noncancel.Boundary.Wop_eq_on_omitted`

The actual dressing equals the input on every edge of every omitted plaquette under the stated admissibility and room hypotheses, without an inverse-unit premise.

- **Source:** `AHP/round12/shared/noncancel/R2_Boundary.lean:50`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Boundary.lean.log:5`: `'AdalyFormal.Round12.Noncancel.Boundary.Wop_eq_on_omitted' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Boundary.Wop_eq_on_collar` (`AHP/round12/shared/noncancel/R2_Boundary.lean:34`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem Wop_eq_on_omitted {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R*M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e
```

</details>

<a id="bp-204"></a>
#### bp-204 — `AdalyFormal.Round12.Noncancel.Boundary.Tfull_sing_zero_near`

A single-bond field sufficiently close to an exterior site has zero actual gauge-fixing contribution under the explicit endpoint-distance bound.

- **Source:** `AHP/round12/shared/noncancel/R2_Boundary.lean:81`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Boundary.lean.log:7`: `'AdalyFormal.Round12.Noncancel.Boundary.Tfull_sing_zero_near' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Boundary.gradAdj_sing_support` (`AHP/round12/shared/noncancel/R2_Boundary.lean:59`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem Tfull_sing_zero_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Tfull (geomOf ell k S) U (sing e X) = 0
```

</details>

<a id="bp-205"></a>
#### bp-205 — `AdalyFormal.Round12.Noncancel.Boundary.Wop_sing_near`

The same single-bond collar geometry makes the actual dressing the identity on that field.

- **Source:** `AHP/round12/shared/noncancel/R2_Boundary.lean:114`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Boundary.lean.log:8`: `'AdalyFormal.Round12.Noncancel.Boundary.Wop_sing_near' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-204](#bp-204) (`AdalyFormal.Round12.Noncancel.Boundary.Tfull_sing_zero_near`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem Wop_sing_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (a : ℝ) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Wop (geomOf ell k S) U a (sing e X) = sing e X
```

</details>

<a id="bp-206"></a>
#### bp-206 — `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat_coordinates`

Every su(2) value decomposes into a real neutral diagonal coordinate and one complex charged coordinate.

- **Source:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean:334`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log:33`: `'AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:322`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem lieMat_coordinates (X : SuTwo) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) =
      lieMat ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1)
```

</details>

<a id="bp-207"></a>
#### bp-207 — `AdalyFormal.Round12.Noncancel.FullPlaquette.frozen_full_three_right`

The actual right-oriented full-color plaquette form is the charged triple form plus the cosine times the square of the sum of neutral coordinates.

- **Source:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean:374`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log:39`: `'AdalyFormal.Round12.Noncancel.FullPlaquette.frozen_full_three_right' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.tripleForm` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:16`); `AdalyFormal.Round12.Noncancel.Plaquette.realHol` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:187`); `AdalyFormal.Round12.Noncancel.Plaquette.imagHol` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:188`); `AdalyFormal.Round12.Noncancel.Plaquette.curl_atoms` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:224`); `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:322`); `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat_add` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:325`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_inner` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:348`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_first_atom` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:355`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_comm_atom` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:362`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem frozen_full_three_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s h k l : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = lieMat h x) (h2 : a2LM p A = lieMat k y)
    (h3 : a3LM p A = lieMat l z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z + c*(h+k+l)^2
```

</details>

<a id="bp-208"></a>
#### bp-208 — `AdalyFormal.Round12.Noncancel.FullPlaquette.frozen_full_three_left`

The separately computed left-oriented frozen formula retains the same essential neutral-square contribution with its own transported atoms.

- **Source:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean:394`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log:42`: `'AdalyFormal.Round12.Noncancel.FullPlaquette.frozen_full_three_left' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.tripleForm` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:16`); `AdalyFormal.Round12.Noncancel.Plaquette.realHol` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:187`); `AdalyFormal.Round12.Noncancel.Plaquette.imagHol` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:188`); `AdalyFormal.Round12.Noncancel.Plaquette.curl_atoms` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:224`); `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:322`); `AdalyFormal.Round12.Noncancel.FullPlaquette.lieMat_add` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:325`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_inner` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:348`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_first_atom` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:355`); `AdalyFormal.Round12.Noncancel.FullPlaquette.full_comm_atom` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:362`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem frozen_full_three_left
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s h k l : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = lieMat h x) (h2 : a2LM p A = 0)
    (h3 : a3LM p A = lieMat k y) (h4 : a4LM U p A = lieMat l z) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z + c*(h+k+l)^2
```

</details>

<a id="bp-209"></a>
#### bp-209 — `AdalyFormal.Round12.Noncancel.FullPlaquette.full_pair_mass_lower`

For nonnegative cosine, the two actual leaf masses plus the full local plaquette form dominate their cosine-weighted mass, retaining neutral terms.

- **Source:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean:415`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log:45`: `'AdalyFormal.Round12.Noncancel.FullPlaquette.full_pair_mass_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.pairForm` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:12`); `AdalyFormal.Round12.Noncancel.Star.pair_mass_lower` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:45`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem full_pair_mass_lower (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    c*(Complex.normSq y+k^2 + (Complex.normSq z+l^2)) ≤
      Complex.normSq y+k^2 + (Complex.normSq z+l^2) +
        pairForm c s y z + c*(h+k+l)^2
```

</details>

<a id="bp-210"></a>
#### bp-210 — `AdalyFormal.Round12.Noncancel.FullPlaquette.full_star_mass_lower`

Summing the local full-color inequalities yields a bound given a nonnegative remainder; it does not identify that remainder with the complete physical carrier.

- **Source:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean:428`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log:48`: `'AdalyFormal.Round12.Noncancel.FullPlaquette.full_star_mass_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-209](#bp-209) (`AdalyFormal.Round12.Noncancel.FullPlaquette.full_pair_mass_lower`)
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.pairForm` (`AHP/round12/shared/noncancel/R2_FullPlaquette.lean:12`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem full_star_mass_lower {ι : Type*} [Fintype ι]
    (c s rest : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hr : 0 ≤ rest)
    (hcs : c^2+s^2=1) (h k l : ι → ℝ) (y z : ι → ℂ) :
    c*(rest+∑ i, (Complex.normSq (y i)+(k i)^2 +
        (Complex.normSq (z i)+(l i)^2))) ≤
      rest+∑ i, (Complex.normSq (y i)+(k i)^2 +
        (Complex.normSq (z i)+(l i)^2) + pairForm c s (y i) (z i) +
          c*(h i+k i+l i)^2)
```

</details>

<a id="bp-211"></a>
#### bp-211 — `AdalyFormal.Round12.Noncancel.Mass.collar_levelZero`

Every touching collar bond whose endpoints avoid the next domain supplies an actual level-zero constraint row.

- **Source:** `AHP/round12/shared/noncancel/R2_Mass.lean:29`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Mass.lean.log:3`: `'AdalyFormal.Round12.Noncancel.Mass.collar_levelZero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem collar_levelZero {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (e : Bond L)
    (ht : e ∈ bondsOm0 (geomOf ell k S))
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    e ∈ bondsLam (geomOf ell k S) 0
```

</details>

<a id="bp-212"></a>
#### bp-212 — `AdalyFormal.Round12.Noncancel.Mass.carrier_leaf_mass_le`

The actual carrier mass dominates the sum over any finite set of distinct level-zero leaves; a leaf mass cannot be counted twice.

- **Source:** `AHP/round12/shared/noncancel/R2_Mass.lean:67`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Mass.lean.log:5`: `'AdalyFormal.Round12.Noncancel.Mass.carrier_leaf_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Mass.leaf_mass_le` (`AHP/round12/shared/noncancel/R2_Mass.lean:41`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem carrier_leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (u : ↥(bondSupp G)) :
    a * ∑ e ∈ leaves, ‖(iE G u) e‖^2 ≤
      ⟪u, pE G (MassFull G a (bondSectorOf G U) (iE G u))⟫
```

</details>

<a id="bp-213"></a>
#### bp-213 — `AdalyFormal.Round12.Noncancel.Mass.mass_split`

The true weighted mass splits into the selected distinct leaf masses plus a nonnegative remainder.

- **Source:** `AHP/round12/shared/noncancel/R2_Mass.lean:76`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_Mass.lean.log:6`: `'AdalyFormal.Round12.Noncancel.Mass.mass_split' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Mass.leaf_mass_le` (`AHP/round12/shared/noncancel/R2_Mass.lean:41`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem mass_split (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    ∃ rest : ℝ, 0 ≤ rest ∧ ⟪A,MassFull G a (bondSectorOf G U) A⟫ =
      rest + a * ∑ e ∈ leaves, ‖A e‖^2
```

</details>

<a id="bp-214"></a>
#### bp-214 — `AdalyFormal.Round12.Noncancel.RightFamily.rightStar`

The canonical right-star family places the four-link star immediately outside the designated right boundary site of the dilated slab.

- **Source:** `AHP/round12/shared/noncancel/R2_RightFamily.lean:607`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_RightFamily.lean.log:19`: `'AdalyFormal.Round12.Noncancel.RightFamily.rightStar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-198](#bp-198) (`AdalyFormal.Round12.Noncancel.Path.starPath`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:298`); `AdalyFormal.Round5.Guarded.IVTR2.rightSite` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:557`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))
```

</details>

<a id="bp-215"></a>
#### bp-215 — `AdalyFormal.Round12.Noncancel.RightFamily.pathU_rightStar`

Exterior masking in the original canonical path definition leaves this precise right-star configuration unchanged.

- **Source:** `AHP/round12/shared/noncancel/R2_RightFamily.lean:627`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_RightFamily.lean.log:26`: `'AdalyFormal.Round12.Noncancel.RightFamily.pathU_rightStar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-214](#bp-214) (`AdalyFormal.Round12.Noncancel.RightFamily.rightStar`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:298`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:301`); `AdalyFormal.Round5.Guarded.IVTR2.maskedU` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:363`); `AdalyFormal.Round9.Guarded.Qualitative.pathU` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:388`); `AdalyFormal.Round12.Noncancel.RightFamily.rightStar_off_exterior` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:620`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (rightStar hq R) f 0 t = rightStar hq R t
```

</details>

<a id="bp-216"></a>
#### bp-216 — `AdalyFormal.Round12.Noncancel.RightFamily.vacA_rightStar`

The original vacuum carrier is exactly the frozen all-plaquette carrier of this right star, resolving the previous family-identification gap.

- **Source:** `AHP/round12/shared/noncancel/R2_RightFamily.lean:647`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_RightFamily.lean.log:28`: `'AdalyFormal.Round12.Noncancel.RightFamily.vacA_rightStar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-214](#bp-214) (`AdalyFormal.Round12.Noncancel.RightFamily.rightStar`); [bp-215](#bp-215) (`AdalyFormal.Round12.Noncancel.RightFamily.pathU_rightStar`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:298`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:301`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:306`); `AdalyFormal.Round9.Guarded.Qualitative.pathP` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:392`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:396`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:407`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacA_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (rightStar hq R) a t =
      (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (rightStar hq R t) a (dilLam q R))).Ginv
```

</details>

<a id="bp-217"></a>
#### bp-217 — `AdalyFormal.Round12.Noncancel.RightFamily.rightStar_negative`

Every positive scale and even radius at least eighteen has a negative vacuum carrier direction at \(\pi\) for this same right star.

- **Source:** `AHP/round12/shared/noncancel/R2_RightFamily.lean:657`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_RightFamily.lean.log:29`: `'AdalyFormal.Round12.Noncancel.RightFamily.rightStar_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-199](#bp-199) (`AdalyFormal.Round12.Noncancel.Path.star_negative_endpoint`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-214](#bp-214) (`AdalyFormal.Round12.Noncancel.RightFamily.rightStar`); [bp-216](#bp-216) (`AdalyFormal.Round12.Noncancel.RightFamily.vacA_rightStar`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:301`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:306`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:407`); `AdalyFormal.Round5.Guarded.IVTR2.rightSite_bd` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:562`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem rightStar_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0
```

</details>

<a id="bp-218"></a>
#### bp-218 — `AdalyFormal.Round12.Noncancel.RightFamily.cofinal_rightStar_paths`

The full nested dyadic/even-radius quantifiers and all valid-path clauses hold for the right stars, but no kernel-line or noncancellation conjunct is included.

- **Source:** `AHP/round12/shared/noncancel/R2_RightFamily.lean:666`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R2_RightFamily.lean.log:32`: `'AdalyFormal.Round12.Noncancel.RightFamily.cofinal_rightStar_paths' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-214](#bp-214) (`AdalyFormal.Round12.Noncancel.RightFamily.rightStar`); [bp-217](#bp-217) (`AdalyFormal.Round12.Noncancel.RightFamily.rightStar_negative`); [bp-216](#bp-216) (`AdalyFormal.Round12.Noncancel.RightFamily.vacA_rightStar`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:16`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:298`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:407`); `AdalyFormal.Round12.Noncancel.RightFamily.rightStar_zero` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:611`); `AdalyFormal.Round12.Noncancel.RightFamily.rightStar_cont` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:614`); `AdalyFormal.Round12.Noncancel.RightFamily.rightStar_an` (`AHP/round12/shared/noncancel/R2_RightFamily.lean:617`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_rightStar_paths :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
        AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
        (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0)
```

</details>

<a id="bp-219"></a>
#### bp-219 — `AdalyFormal.Round12.Kernel.boundary_observable_injective`

Strict positivity on the zero fiber of the boundary observable makes that observable injective on the entire kernel.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1456`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:126`: `'AdalyFormal.Round12.Kernel.boundary_observable_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem boundary_observable_injective {B : Type*} [AddCommGroup B] [Module ℝ B]
    (A : E →L[ℝ] E) (r : E →ₗ[ℝ] B)
    (hpos : ∀ u : E, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
    Function.Injective (r.comp A.ker.subtype)
```

</details>

<a id="bp-220"></a>
#### bp-220 — `AdalyFormal.Round12.Kernel.kernel_eq_charged_span_of_boundary`

Boundary injectivity, quarter-turn covariance and one nonzero kernel vector identify the complete kernel with its charged span.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1500`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:131`: `'AdalyFormal.Round12.Kernel.kernel_eq_charged_span_of_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Kernel.kernel_eq_charged_span` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1435`); `AdalyFormal.Round12.Kernel.kernel_finrank_le_two_of_boundary` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1475`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernel_eq_charged_span_of_boundary [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E) (r : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ x, A (J x) = J (A x))
    (hpos : ∀ x : E, x ≠ 0 → r x = 0 → 0 < ⟪x, A x⟫)
    (u : E) (hu : u ≠ 0) (hAu : A u = 0) (hJJ : J (J u) = -u) :
    A.ker = Submodule.span ℝ ({u, J u} : Set E)
```

</details>

<a id="bp-221"></a>
#### bp-221 — `AdalyFormal.Round12.Kernel.Actual.chargedCoordinate`

The physical observable is the complex off-diagonal entry of the carrier field at one fixed fine bond.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1671`.
- **Status:** B — builder-compiled only. Compiled definition only, not a proof that a defined proposition holds. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:149`: `'AdalyFormal.Round12.Kernel.Actual.chargedCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:80`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:991`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
def chargedCoordinate (q R : ℕ) (b : Bond (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →ₗ[ℝ] ℂ
```

</details>

<a id="bp-222"></a>
#### bp-222 — `AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive`

For the actual canonical crossing, gauge invariance, strict zero-coordinate positivity and a nonzero crossing vector imply the original whole-kernel KernelLine predicate.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1726`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:155`: `'AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-220](#bp-220) (`AdalyFormal.Round12.Kernel.kernel_eq_charged_span_of_boundary`); [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-221](#bp-221) (`AdalyFormal.Round12.Kernel.Actual.chargedCoordinate`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:80`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:83`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:189`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:849`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:991`); `AdalyFormal.Round12.Kernel.charged_of_boundary` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1484`); `AdalyFormal.Round12.Kernel.Actual.vacA_rot_of_fixed` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1679`); `AdalyFormal.Round12.Kernel.Actual.chargedCoordinate_quarter_twice` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1706`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernelLine_of_boundary_positive (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hAu : vacA q R V 1 (vacEdge q R V) u = 0) :
    KernelLine q R V u
```

</details>

<a id="bp-223"></a>
#### bp-223 — `AdalyFormal.Round12.Kernel.Actual.kernelLine_finrank`

The original KernelLine condition has real kernel dimension exactly two.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1753`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:145`: `'AdalyFormal.Round12.Kernel.Actual.kernelLine_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:80`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:83`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:189`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:849`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:991`); `AdalyFormal.Round12.Kernel.charged_span_finrank` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1411`); `AdalyFormal.Round12.Kernel.Actual.vacA_rot_of_fixed` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1679`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernelLine_finrank (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2
```

</details>

<a id="bp-224"></a>
#### bp-224 — `AdalyFormal.Round12.Kernel.Actual.oneColor_not_crossing`

The particular historical one-color invisible field is excluded from a crossing if the observable misses its support and strict zero-fiber positivity holds; not all invisible fields are excluded by this theorem.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1792`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:136`: `'AdalyFormal.Round12.Kernel.Actual.oneColor_not_crossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-221](#bp-221) (`AdalyFormal.Round12.Kernel.Actual.chargedCoordinate`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:80`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:189`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:991`); `AdalyFormal.Round10.Dictionary.ColorObstruction.interiorSite` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1624`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1635`); `AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor_ne_zero` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1639`); `AdalyFormal.Round12.Kernel.Actual.crossing_coordinate_ne_zero` (`AHP/round12/shared/kernel/R1_ActualKernel.lean:1778`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem oneColor_not_crossing {q : ℕ} (hq : 0 < q) (R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hb : b ≠ (AdalyFormal.Round10.Dictionary.ColorObstruction.interiorSite hq R, 0))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫) :
    vacA q R V 1 (vacEdge q R V)
      (AdalyFormal.Round10.Dictionary.ColorObstruction.oneColor hq R) ≠ 0
```

</details>

<a id="bp-225"></a>
#### bp-225 — `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_singular_without_isolation`

Continuity, symmetry, a positive initial form and a negative endpoint already make the canonical PSD edge singular and strictly interior, without isolated-root assumptions.

- **Source:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean:1887`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean.log:158`: `'AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_singular_without_isolation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1559`); `AdalyFormal.Round9.Guarded.QualitativeR2.pos_of_psd_unit` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1834`); `AdalyFormal.Round9.Guarded.QualitativeR2.psd_of_pd` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1855`); `AdalyFormal.Round9.Guarded.QualitativeR2.eventually_pd` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1862`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem psdEdge_singular_without_isolation (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0)
```

</details>

<a id="bp-226"></a>
#### bp-226 — `AdalyFormal.Round12.Kernel.Crossing.psdEdge_same_after_negative`

Once a negative direction has appeared, enlarging the endpoint does not change the initial PSD edge.

- **Source:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean:1981`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean.log:168`: `'AdalyFormal.Round12.Kernel.Crossing.psdEdge_same_after_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1559`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem psdEdge_same_after_negative (A : ℝ → E →L[ℝ] E)
    {a T b : ℝ} (haT : a ≤ T) (hTb : T ≤ b) (w : E) (hw : ⟪w,A T w⟫ < 0) :
    psdEdge A a b = psdEdge A a T
```

</details>

<a id="bp-227"></a>
#### bp-227 — `AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi`

Actual continuity, positive start, quarter-gauge invariance, a negative half-pi trial and full zero-coordinate positivity construct the same canonical edge in \((0,\pi/2)\), an original KernelLine and real nullity two.

- **Source:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean:2032`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_FirstCrossing.lean.log:174`: `'AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-221](#bp-221) (`AdalyFormal.Round12.Kernel.Actual.chargedCoordinate`); [bp-222](#bp-222) (`AdalyFormal.Round12.Kernel.Actual.kernelLine_of_boundary_positive`); [bp-223](#bp-223) (`AdalyFormal.Round12.Kernel.Actual.kernelLine_finrank`); [bp-225](#bp-225) (`AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge_singular_without_isolation`); [bp-226](#bp-226) (`AdalyFormal.Round12.Kernel.Crossing.psdEdge_same_after_negative`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:80`); `AdalyFormal.Round9.Guarded.Qualitative.pathP` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:174`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:189`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:849`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:991`); `AdalyFormal.Round9.Guarded.QualitativeR2.psdEdge` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1559`); `AdalyFormal.Round12.Kernel.Crossing.exists_kernel_of_nonunit` (`AHP/round12/shared/kernel/R2_FirstCrossing.lean:1998`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernelLine_exists_before_halfpi (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hc : Continuous (vacA q R V 1))
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x,vacA q R V 1 0 x⟫)
    (hw : ∃ w, ⟪w,vacA q R V 1 (Real.pi/2) w⟫ < 0)
    (hV : ∀ t, periodicGaugeTransform (rotGauge (Real.pi/4)) (V t) = V t)
    (hp : ∀ t, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace q R,
      x ≠ 0 → chargedCoordinate q R b x = 0 → 0 < ⟪x,vacA q R V 1 t x⟫) :
    0 < vacEdge q R V ∧ vacEdge q R V < Real.pi/2 ∧
      ∃ u : TwistSpace q R, KernelLine q R V u ∧
        Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2
```

</details>

<a id="bp-228"></a>
#### bp-228 — `AdalyFormal.Round12.Kernel.Response.quadratic_on_charged_line`

A quarter-turn-invariant quadratic response is radial on a charged complex line.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:1603`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:214`: `'AdalyFormal.Round12.Kernel.Response.quadratic_on_charged_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem quadratic_on_charged_line (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    Q (a • u + b • J u) = (a^2+b^2) • Q u
```

</details>

<a id="bp-229"></a>
#### bp-229 — `AdalyFormal.Round12.Kernel.ResponseActual.responseGradient_on_line`

On that charged span the actual response gradient scales as the squared norm ratio times the generator gradient.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2003`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:229`: `'AdalyFormal.Round12.Kernel.ResponseActual.responseGradient_on_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-330](#bp-330) (`AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_U1`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-169](#bp-169) (`AdalyFormal.Round10.Assembly.R4.profileCoupling_gradient`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:86`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:210`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1270`); `AdalyFormal.Round12.Kernel.Response.response_eq_norm_ratio` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1640`); `AdalyFormal.Round12.Kernel.ResponseActual.profileCoupling_quad` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1985`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem responseGradient_on_line (q R : ℕ) (u : TwistSpace q R)
    (hu : u ≠ 0)
    (hJu : adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u) = -u)
    (v : TwistSpace q R)
    (hv : v ∈ Submodule.span ℝ {u,
      adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u}) :
    responseGradient q R v = (‖v‖^2 / ‖u‖^2) • responseGradient q R u
```

</details>

<a id="bp-230"></a>
#### bp-230 — `AdalyFormal.Round12.Kernel.ResponseActual.responseHull_singleton`

Under original whole-kernel KernelLine, the hull of all unit responses is exactly the singleton consisting of the generator gradient divided by its squared norm.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2021`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:232`: `'AdalyFormal.Round12.Kernel.ResponseActual.responseHull_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-166](#bp-166) (`AdalyFormal.Round10.Assembly.R4.responseHull`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-170](#bp-170) (`AdalyFormal.Round10.Assembly.R4.crossingKernel`); [bp-229](#bp-229) (`AdalyFormal.Round12.Kernel.ResponseActual.responseGradient_on_line`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:330`); `AdalyFormal.Round10.Assembly.R4.responseGradient_smul` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1887`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem responseHull_singleton (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    responseHull (crossingKernel q R V) (responseGradient q R) =
      {(‖u‖^2)⁻¹ • responseGradient q R u}
```

</details>

<a id="bp-231"></a>
#### bp-231 — `AdalyFormal.Round12.Kernel.ResponseActual.noCancellation_iff_curlDetected_of_kernelLine`

On the complete charged kernel line, response noncancellation is equivalent to curl detection of its generator, with no regularity assumption.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2046`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:235`: `'AdalyFormal.Round12.Kernel.ResponseActual.noCancellation_iff_curlDetected_of_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-168](#bp-168) (`AdalyFormal.Round10.Assembly.R4.responseGradient`); [bp-171](#bp-171) (`AdalyFormal.Round10.Assembly.R4.NoResponseCancellation`); [bp-174](#bp-174) (`AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_iff`); [bp-230](#bp-230) (`AdalyFormal.Round12.Kernel.ResponseActual.responseHull_singleton`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1304`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem noCancellation_iff_curlDetected_of_kernelLine (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    NoResponseCancellation q R V ↔ CurlDetected q R u
```

</details>

<a id="bp-232"></a>
#### bp-232 — `AdalyFormal.Round12.Kernel.ResponseActual.all_kernel_detected_of_generator`

Under KernelLine, detection of the generator detects every nonzero full-kernel vector.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2058`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:238`: `'AdalyFormal.Round12.Kernel.ResponseActual.all_kernel_detected_of_generator' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-174](#bp-174) (`AdalyFormal.Round10.Assembly.R4.responseGradient_ne_zero_iff`); [bp-229](#bp-229) (`AdalyFormal.Round12.Kernel.ResponseActual.responseGradient_on_line`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:330`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1304`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1722`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem all_kernel_detected_of_generator (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (hu : CurlDetected q R u) (v : TwistSpace q R)
    (hv : vacA q R V 1 (vacEdge q R V) v = 0) (hne : v ≠ 0) :
    CurlDetected q R v
```

</details>

<a id="bp-233"></a>
#### bp-233 — `AdalyFormal.Round12.Kernel.ResponseActual.zeroJet_not_crossing_of_detected_line`

A detected complete kernel line excludes every nonzero zero-full-jet field from the crossing, not merely the historical one-color witness.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2072`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:241`: `'AdalyFormal.Round12.Kernel.ResponseActual.zeroJet_not_crossing_of_detected_line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-146](#bp-146) (`AdalyFormal.Round10.Dictionary.FreeSource.exists_profile_iff_curlDetected`); [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-232](#bp-232) (`AdalyFormal.Round12.Kernel.ResponseActual.all_kernel_detected_of_generator`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:83`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:330`); `AdalyFormal.Round9.Guarded.AnalyticR2.flatData` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:366`); `AdalyFormal.Round10.Dictionary.Source.vacJet` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:896`); `AdalyFormal.Round10.Dictionary.Source.profileSourceStencil` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:980`); `AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1304`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round12/shared/kernel/R2_ResponseLine.lean:1722`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem zeroJet_not_crossing_of_detected_line (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (hu : CurlDetected q R u) (v : TwistSpace q R)
    (hne : v ≠ 0) (hz : vacJet q R v = 0) :
    vacA q R V 1 (vacEdge q R V) v ≠ 0
```

</details>

<a id="bp-234"></a>
#### bp-234 — `AdalyFormal.Round12.Kernel.ResponseActual.cofinal_noCancellation_of_curlLine`

The original cofinal free-path curl-line premise directly implies the requested cofinal response-hull premise, without RegularityFacts.

- **Source:** `AHP/round12/shared/kernel/R2_ResponseLine.lean:2087`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R2_ResponseLine.lean.log:244`: `'AdalyFormal.Round12.Kernel.ResponseActual.cofinal_noCancellation_of_curlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-176](#bp-176) (`AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation`); [bp-163](#bp-163) (`AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`); [bp-231](#bp-231) (`AdalyFormal.Round12.Kernel.ResponseActual.noCancellation_iff_curlDetected_of_kernelLine`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_noCancellation_of_curlLine
    (h : CofinalAnyPathCurlLine) : CofinalAnyPathNoResponseCancellation
```

</details>

### Round 11: separate-pin scope, not a guarded proof

<a id="bp-235"></a>
#### bp-235 — `Round11.Refute.window8_closed_proved`

For every blocking factor at least two, the unguarded touching four-bond headline fails for every mass in the closed interval from zero (excluded) to eight. This is a different pin and does not prove carrier-guarded failure.

- **Source:** `AHP/round11/refute-r1/Attempt.lean:910`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round11/refute-r1/Attempt.lean.log:60`: `'Round11.Refute.window8_closed_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `Round11.Refute.not_touchFour_every_ell_le_eight` (`AHP/round11/refute-r1/Attempt.lean:837`); `Round11.Refute.GoalWindow8Closed` (`AHP/round11/refute-r1/Attempt.lean:906`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem window8_closed_proved : GoalWindow8Closed
```

</details>

<a id="bp-236"></a>
#### bp-236 — `Round11.RefuteR2.window_sqrt5_closed_proved`

A wider mixed boundary trial extends that unguarded touching refutation to positive masses at most four times the square root of five, including the endpoint; it does not preserve a carrier-unit guard.

- **Source:** `AHP/round11/refute-r2/Attempt.lean:1086`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round11/refute-r2/Attempt.lean.log:57`: `'Round11.RefuteR2.window_sqrt5_closed_proved' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `Round11.RefuteR2.not_touchFour_every_ell_le_sqrt5` (`AHP/round11/refute-r2/Attempt.lean:1019`); `Round11.RefuteR2.GoalWindowSqrt5Closed` (`AHP/round11/refute-r2/Attempt.lean:1082`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem window_sqrt5_closed_proved : GoalWindowSqrt5Closed
```

</details>

<a id="bp-237"></a>
#### bp-237 — `Round11.LargeA.touch_slice_of_eventual_half_positive`

Uniform localized half-mass positivity would transfer the large-mass touching headline without corner inverse guards. The analytic positivity premise remains unproved and is not the response-hull premise.

- **Source:** `AHP/round11/largea-r2/Attempt.lean:1514`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round11/largea-r2/Attempt.lean.log:123`: `'Round11.LargeA.touch_slice_of_eventual_half_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `Round7.S1Odd.P428TouchFourAt` (`AHP/round11/largea-r2/Attempt.lean:152`); `Round11.LargeA.ClassCoupledFour.toFrozen` (`AHP/round11/largea-r2/Attempt.lean:799`); `Round11.LargeA.touch_instance_of_half_positive` (`AHP/round11/largea-r2/Attempt.lean:1440`); `Round11.LargeA.EventualHalfPositive` (`AHP/round11/largea-r2/Attempt.lean:1497`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem touch_slice_of_eventual_half_positive (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ)
    (ha : 272 ≤ a) (hpos : EventualHalfPositive ell hell a) :
    P428TouchFourAt ell hell a
```

</details>

<a id="bp-238"></a>
#### bp-238 — `Round11.LargeA.base_flat_large_mass_slice`

For mass at least 272 the unguarded touching headline holds on backgrounds flat on every bond based in the interior domain, with arbitrary remaining exterior links. This restricted result does not settle the curved guarded target.

- **Source:** `AHP/round11/largea-r2/Attempt.lean:1601`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round11/largea-r2/Attempt.lean.log:127`: `'Round11.LargeA.base_flat_large_mass_slice' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `Round3.S1Proper.ClassCoupledFour` (`AHP/round11/largea-r2/Attempt.lean:83`); `Round3.S1Proper.selCorner` (`AHP/round11/largea-r2/Attempt.lean:87`); `Round11.LargeA.ClassCoupledFour.toFrozen` (`AHP/round11/largea-r2/Attempt.lean:799`); `Round11.LargeA.touch_instance_of_half_positive` (`AHP/round11/largea-r2/Attempt.lean:1440`); `Round11.LargeA.local_both_psd_of_base_flat` (`AHP/round11/largea-r2/Attempt.lean:1588`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem base_flat_large_mass_slice (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ) (ha : 272 ≤ a) :
  ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    SidePow6 ell (ell ^ m) a ∧
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
        (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ → TorusOK ell (ell ^ m) Lu →
        ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)),
          ClassCoupledFour ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
          (∀ e : Bond (scaleUp ell k Lu), e.1 ∈ S.Om 0 → U e = 1) →
          InstIneqS selCorner selCorner ell k (by omega) a Lu γ₀ S Lam U
```

</details>

### Frozen inverse and collapse bridge

<a id="bp-239"></a>
#### bp-239 — `AdalyFormal.D1Residual.Delta2_lit_eq_loc`

Under the carrier unit, admissibility/room conditions and localized well-definedness, the all-plaquette correction equals the localized correction; the uncorrected all-plaquette constraint unit is transferred in the proof.

- **Source:** `lean/src/DrRed1.lean:36`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/mine/ChecksV3.lean.log:1438`: `'AdalyFormal.D1Residual.Delta2_lit_eq_loc' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-242](#bp-242) (`AdalyFormal.D1Guarded.NG_unit_of_N1`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem Delta2_lit_eq_loc (hu : IsUnit (dataS selAll selAll P).Ginv) (WD : WellDefAt selIn selIn P) :
    (dataS selAll selAll P).Delta2 (dataS_laws selAll selAll P) =
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
```

</details>

<a id="bp-240"></a>
#### bp-240 — `AdalyFormal.D1Residual.G1inv_lit_eq_pencil`

Under those same genuine inverse hypotheses, the corrected all-plaquette carrier is exactly the pencil formed by subtracting the localized correction from the all-plaquette carrier.

- **Source:** `lean/src/DrRed1.lean:52`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/mine/ChecksV3.lean.log:1446`: `'AdalyFormal.D1Residual.G1inv_lit_eq_pencil' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-239](#bp-239) (`AdalyFormal.D1Residual.Delta2_lit_eq_loc`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem G1inv_lit_eq_pencil (hu : IsUnit (dataS selAll selAll P).Ginv) (WD : WellDefAt selIn selIn P) :
    G1invS selAll selAll P = (dataS selAll selAll P).Ginv - (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)
```

</details>

<a id="bp-241"></a>
#### bp-241 — `AdalyFormal.D1Guarded.genFormS_collapse_G1inv`

If the corrected carrier is a nonunit, its totalized inverse and lift vanish and the final form is exactly minus the mass times the squared norm. A positive-energy admissible test therefore contradicts a positive coercive lower bound.

- **Source:** `lean/src/GdGap.lean:56`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/mine/ChecksV3.lean.log:1513`: `'AdalyFormal.D1Guarded.genFormS_collapse_G1inv' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem genFormS_collapse_G1inv (sD sJ : PlaqSel) (P : IngrBParams) (h : ¬ IsUnit (G1invS sD sJ P))
    (B : BondFnL2 P.Lu) :
    GenS.genFormS sD sJ P B = -P.a * ⟪B, B⟫
```

</details>

<a id="bp-242"></a>
#### bp-242 — `AdalyFormal.D1Guarded.NG_unit_of_N1`

A genuine corrected constraint inverse implies the uncorrected constraint matrix is a unit for the same symmetric constrained assembly.

- **Source:** `lean/src/GdGen4.lean:31`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/mine/ChecksV3.lean.log:1587`: `'AdalyFormal.D1Guarded.NG_unit_of_N1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem NG_unit_of_N1 (D : BaseDataS E S F) (hL : D.Laws) {G1inv : E →L[ℝ] E} (hG : D.IsG1inv G1inv)
    (hN1 : IsUnit ((D.Q.comp (D.G1 G1inv)).comp D.Qs)) : IsUnit ((D.Q.comp D.G).comp D.Qs)
```

</details>

### Companion reductions: full bridge ledger

<a id="bp-243"></a>
#### bp-243 — `AdalyFormal.Round2.Guarded.Pin.goalPos1_pin`

The pinned positive target is definitionally the corresponding frozen target, with no selector or quantifier change.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:170`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:27`: `'AdalyFormal.Round2.Guarded.Pin.goalPos1_pin' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:170`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:27`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.goalPos1_pin' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round3/guarded/pin/Statement.lean:154`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_pin : GoalPos1 = AdalyFormal.D1Residual.GuardPencilT
```

</details>

<a id="bp-244"></a>
#### bp-244 — `AdalyFormal.Round2.Guarded.Pin.goalPos2_pin`

The pinned positive target is definitionally the corresponding frozen target, with no selector or quantifier change.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:172`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:28`: `'AdalyFormal.Round2.Guarded.Pin.goalPos2_pin' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:172`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:28`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.goalPos2_pin' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round3/guarded/pin/Statement.lean:157`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_pin : GoalPos2 =
    AdalyFormal.D1Literal.P428Target8SG AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
```

</details>

<a id="bp-245"></a>
#### bp-245 — `AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg1`

A family satisfying every original cofinal scale/radius/cap, class and competitor obligation, with carrier unit and corrected-pencil nonunit, refutes the pinned eventual pencil statement.

- **Source:** `AHP/round3/guarded/pin/Statement.lean:206`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/pin/Statement.lean.log:32`: `'AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:206`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:32`, exit `0`; record: `'AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-002](#bp-002) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg1`); [bp-008](#bp-008) (`AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPencilFailure_implies_goalNeg1 (h : CofinalPencilFailure) : GoalNeg1
```

</details>

<a id="bp-246"></a>
#### bp-246 — `AdalyFormal.Round3.Guarded.R3Prove.pencil_isUnit_of_mixed_boundary_source_zero`

Under its stated geometric and analytic hypotheses, mixed boundary source zero imply pencil is unit. This implication does not supply its input premise.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:909`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:178`: `'AdalyFormal.Round3.Guarded.R3Prove.pencil_isUnit_of_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-018](#bp-018) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_of_no_boundary_return`); [bp-023](#bp-023) (`AdalyFormal.Round3.Guarded.R3Prove.no_return_iff_mixed_boundary_source_zero`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round3/guarded/r3-prove/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round3/guarded/r3-prove/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round3/guarded/r3-prove/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round3/guarded/r3-prove/Attempt.lean:62`); `AdalyFormal.Round3.Guarded.R3Prove.mixedJetSource` (`AHP/round3/guarded/r3-prove/Attempt.lean:762`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_mixed_boundary_source_zero
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (hj : ∀ y z : (boundaryShift P).range,
      mixedJetSource P (Ring.inverse (localCorrected P) z)
        (Ring.inverse (dataS selIn selIn P).Ginv y) = 0) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-247"></a>
#### bp-247 — `AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero`

Under its stated geometric and analytic hypotheses, diagonal mixed boundary source zero imply goal pos2. This implication does not supply its input premise.

- **Source:** `AHP/round3/guarded/r3-prove/Attempt.lean:981`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round3/guarded/r3-prove/Attempt.lean.log:158`: `'AdalyFormal.Round3.Guarded.R3Prove.goalPos2_of_diagonal_mixed_boundary_source_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-024](#bp-024) (`AdalyFormal.Round3.Guarded.R3Prove.mixed_boundary_zero_iff_diagonal`); [bp-246](#bp-246) (`AdalyFormal.Round3.Guarded.R3Prove.pencil_isUnit_of_mixed_boundary_source_zero`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GShape` (`AHP/round3/guarded/r3-prove/Attempt.lean:133`); `AdalyFormal.Round2.Guarded.Pin.GoalPos2` (`AHP/round3/guarded/r3-prove/Attempt.lean:157`); `AdalyFormal.Round3.Guarded.R3Prove.CDiagonalMixedBoundarySourceZero` (`AHP/round3/guarded/r3-prove/Attempt.lean:970`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos2_of_diagonal_mixed_boundary_source_zero
    (h : GShape CDiagonalMixedBoundarySourceZero) : GoalPos2
```

</details>

<a id="bp-248"></a>
#### bp-248 — `AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_weighted_decay`

Under its stated geometric and analytic hypotheses, weighted decay imply pencil is unit. This implication does not supply its input premise.

- **Source:** `AHP/round4/guarded/decay-r1/Attempt.lean:880`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round4/guarded/decay-r1/Attempt.lean.log:140`: `'AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_weighted_decay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-010](#bp-010) (`AdalyFormal.Round2.Guarded.R2Prove.response`); [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-042](#bp-042) (`AdalyFormal.Round4.Guarded.DecayR1.pencil_isUnit_of_two_pass_decay`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round4/guarded/decay-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round4/guarded/decay-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round4/guarded/decay-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round4/guarded/decay-r1/Attempt.lean:62`); `AdalyFormal.Round2.Guarded.R2Prove.localCorrected_eq` (`AHP/round4/guarded/decay-r1/Attempt.lean:463`); `AdalyFormal.Round4.Guarded.DecayR1.weighted_inverse_observation` (`AHP/round4/guarded/decay-r1/Attempt.lean:735`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round4/guarded/decay-r1/Attempt.lean:825`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_weighted_decay
    (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv)
    (TB TC : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G))
    {cB cC dB dC : ℝ} (hcB : 0 < cB) (hcC : 0 < cC)
    (hcoerB : ∀ x, cB * ‖TB x‖ ^ 2 ≤ ⟪TB x, TB ((dataS selIn selIn P).Ginv x)⟫)
    (hcoerC : ∀ x, cC * ‖TC x‖ ^ 2 ≤ ⟪TC x, TC (localCorrected P x)⟫)
    (hsourceB : ∀ y : (boundaryShift P).range, TB y = (y : ↥(bondSupp P.G)))
    (hsourceC : ∀ y : (boundaryShift P).range, TC y = (y : ↥(bondSupp P.G)))
    (hobsB : ∀ x, ‖jetObservation P x‖ ≤ Real.exp (-dB) * ‖TB x‖)
    (hobsC : ∀ x, ‖jetObservation P x‖ ≤ Real.exp (-dC) * ‖TC x‖)
    (hsmall : ‖Ring.inverse (response (boundaryShift P) (dataS selIn selIn P).Ginv)‖ *
      (‖boundaryShift P‖ *
        ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ *
          (Real.exp (-dB) / cB) * (Real.exp (-dC) / cC)) < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-249"></a>
#### bp-249 — `AdalyFormal.Round5.Guarded.KernelR1.cofinalPencilFailure_of_dil_modes`

Under its stated geometric and analytic hypotheses, the exact full two-mode dilated realization imply the complete cofinal pencil-failure certificate. This implication does not supply its input premise.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2387`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:246`: `'AdalyFormal.Round5.Guarded.KernelR1.cofinalPencilFailure_of_dil_modes' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-005](#bp-005) (`AdalyFormal.Round2.Guarded.Pin.CPen`); [bp-008](#bp-008) (`AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure`); [bp-033](#bp-033) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor`); [bp-056](#bp-056) (`AdalyFormal.Round5.Guarded.KernelR1.actual_two_mode_separation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round5/guarded/kernel-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/kernel-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round5/guarded/kernel-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1153`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1383`); `AdalyFormal.Round5.Guarded.KernelR1.dil_class_exterior_independent` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2362`); `AdalyFormal.Round5.Guarded.KernelR1.DilModeRealisation` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2377`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPencilFailure_of_dil_modes (h : DilModeRealisation) : CofinalPencilFailure
```

</details>

<a id="bp-250"></a>
#### bp-250 — `AdalyFormal.Round5.Guarded.KernelR2.separation_of_schur_realisation`

Under its stated geometric and analytic hypotheses, the supplied full-carrier Schur block realization imply separation. This implication does not supply its input premise.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2645`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:272`: `'AdalyFormal.Round5.Guarded.KernelR2.separation_of_schur_realisation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-058](#bp-058) (`AdalyFormal.Round5.Guarded.KernelR2.actual_schur_separation`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/kernel-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/kernel-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/kernel-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round5/guarded/kernel-r2/Attempt.lean:62`); `AdalyFormal.Round5.Guarded.KernelR2.SchurRealisation` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2635`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem separation_of_schur_realisation (P : IngrBParams) (h : SchurRealisation P) :
    IsUnit (dataS selAll selAll P).Ginv ∧
      ∃ z : ↥(bondSupp P.G), z ≠ 0 ∧
        ((dataS selAll selAll P).Ginv -
          (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)) z = 0
```

</details>

<a id="bp-251"></a>
#### bp-251 — `AdalyFormal.Round5.Guarded.KernelR2.cofinalPencilFailure_of_dil_schur`

Under its stated geometric and analytic hypotheses, the exact physical dilated Schur realization imply the complete cofinal pencil-failure certificate. This implication does not supply its input premise.

- **Source:** `AHP/round5/guarded/kernel-r2/Attempt.lean:2663`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/kernel-r2/Attempt.lean.log:276`: `'AdalyFormal.Round5.Guarded.KernelR2.cofinalPencilFailure_of_dil_schur' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-005](#bp-005) (`AdalyFormal.Round2.Guarded.Pin.CPen`); [bp-008](#bp-008) (`AdalyFormal.Round2.Guarded.Pin.CofinalPencilFailure`); [bp-033](#bp-033) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_in_class_nonflat_competitor`); [bp-250](#bp-250) (`AdalyFormal.Round5.Guarded.KernelR2.separation_of_schur_realisation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round5/guarded/kernel-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round5/guarded/kernel-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round5/guarded/kernel-r2/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1153`); `AdalyFormal.Round4.Guarded.RefuteR1.dilU` (`AHP/round5/guarded/kernel-r2/Attempt.lean:1383`); `AdalyFormal.Round5.Guarded.KernelR1.dil_class_exterior_independent` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2362`); `AdalyFormal.Round5.Guarded.KernelR2.DilSchurRealisation` (`AHP/round5/guarded/kernel-r2/Attempt.lean:2654`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPencilFailure_of_dil_schur (h : DilSchurRealisation) : CofinalPencilFailure
```

</details>

<a id="bp-252"></a>
#### bp-252 — `AdalyFormal.Round4.Guarded.DecayR2.pencil_isUnit_of_observed_guard_decay`

Under its stated geometric and analytic hypotheses, observed guard decay imply pencil is unit. This implication does not supply its input premise.

- **Source:** `AHP/round5/guarded/structural-r1/Attempt.lean:1123`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round5/guarded/structural-r1/Attempt.lean.log:161`: `'AdalyFormal.Round4.Guarded.DecayR2.pencil_isUnit_of_observed_guard_decay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-011](#bp-011) (`AdalyFormal.Round2.Guarded.R2Prove.boundaryShift`); [bp-012](#bp-012) (`AdalyFormal.Round2.Guarded.R2Prove.localCorrected`); [bp-016](#bp-016) (`AdalyFormal.Round2.Guarded.R2Prove.carrier_isUnit_iff_response`); [bp-017](#bp-017) (`AdalyFormal.Round2.Guarded.R2Prove.pencil_isUnit_iff_response`); [bp-045](#bp-045) (`AdalyFormal.Round4.Guarded.DecayR2.actual_relative_return_norm_le_observed`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round5/guarded/structural-r1/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round5/guarded/structural-r1/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round5/guarded/structural-r1/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round5/guarded/structural-r1/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.DecayR1.jetObservation` (`AHP/round5/guarded/structural-r1/Attempt.lean:825`); `AdalyFormal.Round4.Guarded.DecayR2.response_unit_of_relative_small` (`AHP/round5/guarded/structural-r1/Attempt.lean:1069`); `AdalyFormal.Round4.Guarded.DecayR2.observedGuardTransfer` (`AHP/round5/guarded/structural-r1/Attempt.lean:1081`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pencil_isUnit_of_observed_guard_decay (hW : WellDefAt selIn selIn P)
    (hu : IsUnit (dataS selAll selAll P).Ginv) {c : ℝ} (hc : 0 ≤ c)
    (hct : ∀ y : (boundaryShift P).range,
      ‖jetObservation P (Ring.inverse (localCorrected P) y)‖ ≤ c * ‖y‖)
    (hsmall : ‖observedGuardTransfer P‖ *
      ‖(dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P)‖ * c < 1) :
    IsUnit ((dataS selAll selAll P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P))
```

</details>

<a id="bp-253"></a>
#### bp-253 — `AdalyFormal.Round6.Guarded.PlacementR2.cofinal_hybrid_class_family`

The curved hybrid family satisfies the complete cofinal class and competitor obligations with radius before cap, without a spectral separation conclusion.

- **Source:** `AHP/round6/placement-r2/HybridCertificate.lean:2536`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round6/placement-r2/HybridCertificate.lean.log:255`: `'AdalyFormal.Round6.Guarded.PlacementR2.cofinal_hybrid_class_family' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round6/placement-r2/HybridCertificate.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round6/placement-r2/HybridCertificate.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round6/placement-r2/HybridCertificate.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round6/placement-r2/HybridCertificate.lean:1153`); `AdalyFormal.Round6.Guarded.PlacementR2.hybridU` (`AHP/round6/placement-r2/HybridCertificate.lean:2358`); `AdalyFormal.Round6.Guarded.PlacementR2.uniform_hybrid_class_family` (`AHP/round6/placement-r2/HybridCertificate.lean:2459`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_hybrid_class_family :
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∃ q : ℕ, 0 < q ∧ 2^m = 2*q ∧
        ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ 17*2 ≤ R*(2^m) ∧
          ∀ a₀ : ℝ, 0 < a₀ → ∃ α δ : ℝ,
            0 < α ∧ (12 : ℝ)*(2^m : ℕ)*α ≤ a₀ ∧ 0 < δ ∧ δ < 1 ∧
            TorusOK 2 (2^m) (dilLu q R) ∧ Admissible 2 (2^m) R 1 (dilTower q R) ∧
            LambdaOK2 2 (2^m) R 1 (dilTower q R) (dilLam q R) ∧
            ∃ Bt : Bond (dilLu q R) → SuTwo,
              OnLambdaTildeIn (dilLam q R) 2 Bt ∧ OnLambdaT (dilLam q R) Bt ∧
              0 < bondEnergy Bt ∧
              ∀ ε : ℝ, |ε| ≤ δ → ∀ V : LinkCfg (scaleUp 2 1 (dilLu q R)),
                ClassCoupled 2 (2^m) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (hybridU q R δ ε V) ∧
                ∃ p ∈ plaqIn ((dilTower q R).Om 0),
                  periodicPlaquetteHolonomy (hybridU q R δ ε V) p ≠ 1
```

</details>

<a id="bp-254"></a>
#### bp-254 — `AdalyFormal.Round8.Guarded.SignFree.signChange_of_kernelPositiveCrossing`

Under its stated geometric and analytic hypotheses, a guarded carrier crossing with positive kernel correction imply a carrier-unit interval on which the corrected form changes sign. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2686`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:241`: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_kernelPositiveCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2686`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:241`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_kernelPositiveCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-070](#bp-070) (`AdalyFormal.Round8.Guarded.SignFree.sign_change_of_kernel_positive`); [bp-075](#bp-075) (`AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round8/guarded-idea/Attempt.lean:1709`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round8/guarded-idea/Attempt.lean:1713`); `AdalyFormal.Round5.Guarded.IVTR1.twistA_continuous` (`AHP/round8/guarded-idea/Attempt.lean:1819`); `AdalyFormal.Round5.Guarded.IVTR1.KernelPositiveCrossing` (`AHP/round8/guarded-idea/Attempt.lean:1878`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem signChange_of_kernelPositiveCrossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : KernelPositiveCrossing q R ε) :
    SignChangeControl q R ε
```

</details>

<a id="bp-255"></a>
#### bp-255 — `AdalyFormal.Round8.Guarded.SignFree.signChange_of_initialKernelControl`

Under its stated geometric and analytic hypotheses, initial positive carrier and corrected forms with positive correction on the first crossing kernel imply a carrier-unit interval on which the corrected form changes sign. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2694`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:244`: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_initialKernelControl' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2694`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:244`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_initialKernelControl' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-075](#bp-075) (`AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`); [bp-254](#bp-254) (`AdalyFormal.Round8.Guarded.SignFree.signChange_of_kernelPositiveCrossing`)
- **Additional local source references:** `AdalyFormal.Round5.Guarded.IVTR2.kernelPositiveCrossing_of_endpoint_signs` (`AHP/round8/guarded-idea/Attempt.lean:2088`); `AdalyFormal.Round5.Guarded.IVTR2.InitialKernelControl` (`AHP/round8/guarded-idea/Attempt.lean:2368`); `AdalyFormal.Round5.Guarded.IVTR2.endpoint_control_of_initial_kernel` (`AHP/round8/guarded-idea/Attempt.lean:2376`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem signChange_of_initialKernelControl {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {ε : ℝ} (h : InitialKernelControl q R ε) :
    SignChangeControl q R ε
```

</details>

<a id="bp-256"></a>
#### bp-256 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_twist_separation`

Under its stated geometric and analytic hypotheses, actual twist separation below every cap imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2704`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:247`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2704`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:247`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-009](#bp-009) (`AdalyFormal.Round2.Guarded.Pin.cofinalPencilFailure_implies_goalNeg2`); [bp-028](#bp-028) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_torus`); [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-029](#bp-029) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_lambda`); [bp-030](#bp-030) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_competitor`); [bp-031](#bp-031) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_coverage`); [bp-032](#bp-032) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_regular`); [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round8/guarded-idea/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round8/guarded-idea/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round8/guarded-idea/Attempt.lean:994`); `AdalyFormal.Round4.Guarded.RefuteR1.dilBt` (`AHP/round8/guarded-idea/Attempt.lean:1153`); `AdalyFormal.Round5.Guarded.IVTR1.twistU` (`AHP/round8/guarded-idea/Attempt.lean:1703`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg2
```

</details>

<a id="bp-257"></a>
#### bp-257 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg1_of_twist_separation`

Under its stated geometric and analytic hypotheses, actual twist separation below every cap imply the equivalent negative pencil headline. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2741`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:250`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg1_of_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2741`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:250`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg1_of_twist_separation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-002](#bp-002) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg1`); [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`); [bp-256](#bp-256) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_twist_separation`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg1_of_twist_separation
    (hsep : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation q R ε) :
    GoalNeg1
```

</details>

<a id="bp-258"></a>
#### bp-258 — `AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_sign_change_control`

Under its stated geometric and analytic hypotheses, actual sign-change intervals below every cap imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2750`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:253`: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_sign_change_control' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2750`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:253`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_sign_change_control' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-075](#bp-075) (`AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`); [bp-076](#bp-076) (`AdalyFormal.Round8.Guarded.SignFree.twistSeparation_of_signChange`); [bp-256](#bp-256) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_twist_separation`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_sign_change_control
    (hcontrol : ∀ q : ℕ, 0 < q → ∀ R : ℕ, 2 ∣ R → 18 ≤ R →
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ SignChangeControl q R ε) :
    GoalNeg2
```

</details>

<a id="bp-259"></a>
#### bp-259 — `AdalyFormal.Round8.Guarded.SignFree.signChange_of_pencilCertificates`

Under its stated geometric and analytic hypotheses, sine/cosine pencil and complementary subspace certificates imply a carrier-unit interval on which the corrected form changes sign. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2823`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:261`: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_pencilCertificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2823`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:261`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.signChange_of_pencilCertificates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-073](#bp-073) (`AdalyFormal.Round8.Guarded.SignFree.pencil_units_of_certificates`); [bp-075](#bp-075) (`AdalyFormal.Round8.Guarded.SignFree.SignChangeControl`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round8/guarded-idea/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round8/guarded-idea/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round8/guarded-idea/Attempt.lean:62`); `AdalyFormal.Round5.Guarded.IVTR1.twistP` (`AHP/round8/guarded-idea/Attempt.lean:1706`); `AdalyFormal.Round5.Guarded.IVTR1.twistA` (`AHP/round8/guarded-idea/Attempt.lean:1709`); `AdalyFormal.Round8.Guarded.SignFree.PencilCertificates` (`AHP/round8/guarded-idea/Attempt.lean:2811`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem signChange_of_pencilCertificates {q R : ℕ} {ε : ℝ} (h : PencilCertificates q R ε) :
    SignChangeControl q R ε
```

</details>

<a id="bp-260"></a>
#### bp-260 — `AdalyFormal.Round8.Guarded.SignFree.cofinalTwistSeparation_of_cofinalSignChange`

Under its stated geometric and analytic hypotheses, nested cofinal sign-change intervals imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round8/guarded-idea/Attempt.lean:2894`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round8/guarded-idea/Attempt.lean.log:275`: `'AdalyFormal.Round8.Guarded.SignFree.cofinalTwistSeparation_of_cofinalSignChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:2894`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:275`, exit `0`; record: `'AdalyFormal.Round8.Guarded.SignFree.cofinalTwistSeparation_of_cofinalSignChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-076](#bp-076) (`AdalyFormal.Round8.Guarded.SignFree.twistSeparation_of_signChange`); [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round8.Guarded.SignFree.CofinalSignChange` (`AHP/round8/guarded-idea/Attempt.lean:2851`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalSignChange (h : CofinalSignChange) :
    CofinalTwistSeparation
```

</details>

<a id="bp-261"></a>
#### bp-261 — `AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data_pos`

Under its stated geometric and analytic hypotheses, vacuum data pos imply separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3462`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:308`: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7549`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:701`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data_pos' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-082](#bp-082) (`AdalyFormal.Round9.Guarded.AnalyticR1.schur_unit_iff`); [bp-083](#bp-083) (`AdalyFormal.Round9.Guarded.AnalyticR1.vacuum_schur_slope`); [bp-084](#bp-084) (`AdalyFormal.Round9.Guarded.AnalyticR1.schur_difference_tendsto`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.exists_coercive_on_range` (`AHP/round9/analytic-r2/Attempt.lean:3039`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurC` (`AHP/round9/analytic-r2/Attempt.lean:3085`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS` (`AHP/round9/analytic-r2/Attempt.lean:3088`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS_symm` (`AHP/round9/analytic-r2/Attempt.lean:3104`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS_left` (`AHP/round9/analytic-r2/Attempt.lean:3124`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurS_right` (`AHP/round9/analytic-r2/Attempt.lean:3130`); `AdalyFormal.Round9.Guarded.AnalyticR1.schurC_continuous` (`AHP/round9/analytic-r2/Attempt.lean:3227`); `AdalyFormal.Round9.Guarded.AnalyticR1.tendsto_schurS` (`AHP/round9/analytic-r2/Attempt.lean:3231`); `AdalyFormal.Round9.Guarded.AnalyticR1.quad_le_norm` (`AHP/round9/analytic-r2/Attempt.lean:3241`); `AdalyFormal.Round9.Guarded.AnalyticR1.core_separation` (`AHP/round9/analytic-r2/Attempt.lean:3376`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem separation_of_vacuum_data_pos
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hpos : ∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε)
```

</details>

<a id="bp-262"></a>
#### bp-262 — `AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data`

Under its stated geometric and analytic hypotheses, vacuum data imply separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3709`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:311`: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7796`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:704`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-261](#bp-261) (`AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_data_pos`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem separation_of_vacuum_data
    (X : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hPs : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hXs : ∀ ε t x y, ⟪X ε t x, y⟫ = ⟪x, X ε t y⟫)
    (hDs : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hXc : ∀ ε, Continuous (X ε))
    (t₀ η₀ : ℝ) (hη₀ : 0 < η₀)
    (hjoint : ∀ t, |t - t₀| < η₀ →
      Tendsto (fun p : ℝ × ℝ => X p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 t) (𝓝 (X 0 t)))
    (X' : E →L[ℝ] E) (hder : HasDerivAt (X 0) X' t₀)
    (D₁ : E →L[ℝ] E) (hD : Tendsto (fun ε : ℝ => ε⁻¹ • D ε) (𝓝[>] 0) (𝓝 D₁))
    (hXP : X 0 t₀ * P = 0) (hker : ∀ x, X 0 t₀ x = 0 → P x = x)
    (w : E) (hwP : P w = w) (hw0 : w ≠ 0)
    (hslope : ∀ v, P v = v → v ≠ 0 → ⟪v, X' v⟫ < 0)
    (hsign : (∀ v, P v = v → v ≠ 0 → ⟪v, D₁ v⟫ < 0) ∨
      (∀ v, P v = v → v ≠ 0 → 0 < ⟪v, D₁ v⟫)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ t : ℝ, IsUnit (X ε t) ∧ ¬ IsUnit (X ε t - D ε)
```

</details>

<a id="bp-263"></a>
#### bp-263 — `AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal vacuum nondegeneracy imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3903`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:329`: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:7990`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:722`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.eventually_twistSeparation_of_vacuum` (`AHP/round9/analytic-r2/Attempt.lean:3878`); `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalVacuumNondegeneracy` (`AHP/round9/analytic-r2/Attempt.lean:3899`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation
```

</details>

<a id="bp-264"></a>
#### bp-264 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal vacuum nondegeneracy imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:3919`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:332`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8006`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:725`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-263](#bp-263) (`AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalVacuumNondegeneracy` (`AHP/round9/analytic-r2/Attempt.lean:3899`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) : GoalNeg2
```

</details>

<a id="bp-265"></a>
#### bp-265 — `AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalTwistSeparation`

Under its stated geometric and analytic hypotheses, nested cofinal actual twist separation imply nested cofinal separation with arbitrary exterior fields. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4005`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:352`: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8092`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:745`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalTwistSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalExtSeparation` (`AHP/round9/analytic-r2/Attempt.lean:3957`); `AdalyFormal.Round9.Guarded.AnalyticR1.extSeparation_of_twistSeparation` (`AHP/round9/analytic-r2/Attempt.lean:4000`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalExtSeparation_of_cofinalTwistSeparation (h : CofinalTwistSeparation) :
    CofinalExtSeparation
```

</details>

<a id="bp-266"></a>
#### bp-266 — `AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalPathVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal free-path vacuum nondegeneracy imply nested cofinal separation with arbitrary exterior fields. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4124`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:368`: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8211`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:761`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalExtSeparation` (`AHP/round9/analytic-r2/Attempt.lean:3957`); `AdalyFormal.Round9.Guarded.AnalyticR1.eventually_extSeparation_of_pathVacuum` (`AHP/round9/analytic-r2/Attempt.lean:4099`); `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalPathVacuum` (`AHP/round9/analytic-r2/Attempt.lean:4120`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalExtSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalExtSeparation
```

</details>

<a id="bp-267"></a>
#### bp-267 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalPathVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal free-path vacuum nondegeneracy imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4138`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:371`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8225`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:764`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-086](#bp-086) (`AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalExtSeparation`); [bp-266](#bp-266) (`AdalyFormal.Round9.Guarded.AnalyticR1.cofinalExtSeparation_of_cofinalPathVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalPathVacuum` (`AHP/round9/analytic-r2/Attempt.lean:4120`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2
```

</details>

<a id="bp-268"></a>
#### bp-268 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalLeftVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal left-twist vacuum nondegeneracy imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4170`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:380`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalLeftVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8257`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:773`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalLeftVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-267](#bp-267) (`AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalPathVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.leftTwist` (`AHP/round9/analytic-r2/Attempt.lean:4147`); `AdalyFormal.Round9.Guarded.AnalyticR1.leftTwist_cont` (`AHP/round9/analytic-r2/Attempt.lean:4151`); `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalLeftVacuum` (`AHP/round9/analytic-r2/Attempt.lean:4165`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalLeftVacuum (h : CofinalLeftVacuum) : GoalNeg2
```

</details>

<a id="bp-269"></a>
#### bp-269 — `AdalyFormal.Round9.Guarded.AnalyticR1.cofinalLeftVacuum_of_soft_spectral`

Under its stated geometric and analytic hypotheses, the stated interior regularity and spectral inputs imply nested cofinal left-twist vacuum nondegeneracy. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4192`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:385`: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalLeftVacuum_of_soft_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8279`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:778`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalLeftVacuum_of_soft_spectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.CofinalLeftVacuum` (`AHP/round9/analytic-r2/Attempt.lean:4165`); `AdalyFormal.Round9.Guarded.AnalyticR1.LeftSoft` (`AHP/round9/analytic-r2/Attempt.lean:4181`); `AdalyFormal.Round9.Guarded.AnalyticR1.LeftSpectral` (`AHP/round9/analytic-r2/Attempt.lean:4187`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalLeftVacuum_of_soft_spectral (hs : LeftSoft) (hc : LeftSpectral) :
    CofinalLeftVacuum
```

</details>

<a id="bp-270"></a>
#### bp-270 — `AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_leftSoft_leftSpectral`

Under its stated geometric and analytic hypotheses, interior regularity and left-twist vacuum spectral coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:4203`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:388`: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_leftSoft_leftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:8290`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:781`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_leftSoft_leftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-268](#bp-268) (`AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalLeftVacuum`); [bp-269](#bp-269) (`AdalyFormal.Round9.Guarded.AnalyticR1.cofinalLeftVacuum_of_soft_spectral`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.LeftSoft` (`AHP/round9/analytic-r2/Attempt.lean:4181`); `AdalyFormal.Round9.Guarded.AnalyticR1.LeftSpectral` (`AHP/round9/analytic-r2/Attempt.lean:4187`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_leftSoft_leftSpectral (hs : LeftSoft) (hc : LeftSpectral) : GoalNeg2
```

</details>

<a id="bp-271"></a>
#### bp-271 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral`

Under its stated geometric and analytic hypotheses, left-twist vacuum spectral coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7287`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:647`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11046`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1012`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-088](#bp-088) (`AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_interiorSoft_vacuumLeftSpectral`); [bp-096](#bp-096) (`AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR1.VacuumLeftSpectral` (`AHP/round9/analytic-r2/Attempt.lean:4532`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_vacuumLeftSpectral (hc : VacuumLeftSpectral) : GoalNeg2
```

</details>

<a id="bp-272"></a>
#### bp-272 — `AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing`

Under its stated geometric and analytic hypotheses, symmetric-twist vacuum crossing data imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7320`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:659`: `'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11079`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1024`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-263](#bp-263) (`AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum`); [bp-097](#bp-097) (`AdalyFormal.Round9.Guarded.AnalyticR2.zeroCurvatureRegularity_proved`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCrossing` (`AHP/round9/analytic-r2/Attempt.lean:7312`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) :
    CofinalTwistSeparation
```

</details>

<a id="bp-273"></a>
#### bp-273 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCrossing`

Under its stated geometric and analytic hypotheses, symmetric-twist vacuum crossing data imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7330`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:662`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11089`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1027`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCrossing' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-272](#bp-272) (`AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCrossing` (`AHP/round9/analytic-r2/Attempt.lean:7312`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_twistVacuumCrossing (h : CofinalTwistVacuumCrossing) : GoalNeg2
```

</details>

<a id="bp-274"></a>
#### bp-274 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling`

Under its stated geometric and analytic hypotheses, left-twist explicit flat source/jet coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7397`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:679`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11156`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1044`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-271](#bp-271) (`AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftSpectral`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.VacuumLeftCoupling` (`AHP/round9/analytic-r2/Attempt.lean:7368`); `AdalyFormal.Round9.Guarded.AnalyticR2.vacuumLeftSpectral_of_coupling` (`AHP/round9/analytic-r2/Attempt.lean:7386`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_vacuumLeftCoupling (h : VacuumLeftCoupling) : GoalNeg2
```

</details>

<a id="bp-275"></a>
#### bp-275 — `AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling`

Under its stated geometric and analytic hypotheses, symmetric-twist explicit vacuum coupling imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7408`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:685`: `'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11167`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1050`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-272](#bp-272) (`AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCrossing`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/analytic-r2/Attempt.lean:989`); `AdalyFormal.Round5.Guarded.IVTR1.twistD` (`AHP/round9/analytic-r2/Attempt.lean:1713`); `AdalyFormal.Round9.Guarded.AnalyticR1.extD` (`AHP/round9/analytic-r2/Attempt.lean:3947`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_J_tendsto` (`AHP/round9/analytic-r2/Attempt.lean:6877`); `AdalyFormal.Round9.Guarded.AnalyticR2.pathCrossing_of_couplingCrossing` (`AHP/round9/analytic-r2/Attempt.lean:7373`); `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCoupling` (`AHP/round9/analytic-r2/Attempt.lean:7401`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) :
    CofinalTwistSeparation
```

</details>

<a id="bp-276"></a>
#### bp-276 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCoupling`

Under its stated geometric and analytic hypotheses, symmetric-twist explicit vacuum coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7427`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:688`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11186`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1053`, exit `0`; record: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-275](#bp-275) (`AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCoupling` (`AHP/round9/analytic-r2/Attempt.lean:7401`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_twistVacuumCoupling (h : CofinalTwistVacuumCoupling) : GoalNeg2
```

</details>

<a id="bp-277"></a>
#### bp-277 — `AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCouplingD`

Under its stated geometric and analytic hypotheses, symmetric-twist vacuum coupling with the actual angle derivative imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/analytic-r2/Attempt.lean:7636`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round9/analytic-r2/Attempt.lean.log:722`: `'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_twistVacuumCouplingD' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-101](#bp-101) (`AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCouplingD`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.AnalyticR2.CofinalTwistVacuumCouplingD` (`AHP/round9/analytic-r2/Attempt.lean:7616`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_twistVacuumCouplingD (h : CofinalTwistVacuumCouplingD) : GoalNeg2
```

</details>

<a id="bp-278"></a>
#### bp-278 — `AdalyFormal.Round9.Guarded.Qualitative.pathSeparation_of_signChange`

Under its stated geometric and analytic hypotheses, a carrier-unit interval on which the corrected form changes sign imply path separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4187`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:337`: `'AdalyFormal.Round9.Guarded.Qualitative.pathSeparation_of_signChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4187`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:337`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.pathSeparation_of_signChange' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-069](#bp-069) (`AdalyFormal.Round8.Guarded.SignFree.separation_of_sign_change`); [bp-104](#bp-104) (`AdalyFormal.Round9.Guarded.Qualitative.pathD_constant`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/qualitative-r2/Attempt.lean:35`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/qualitative-r2/Attempt.lean:58`); `AdalyFormal.Round2.Guarded.Pin.dataS_laws` (`AHP/round9/qualitative-r2/Attempt.lean:62`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.pathP` (`AHP/round9/qualitative-r2/Attempt.lean:3966`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round9/qualitative-r2/Attempt.lean:3971`); `AdalyFormal.Round9.Guarded.Qualitative.pathD` (`AHP/round9/qualitative-r2/Attempt.lean:3977`); `AdalyFormal.Round9.Guarded.Qualitative.pathA_continuous` (`AHP/round9/qualitative-r2/Attempt.lean:4004`); `AdalyFormal.Round9.Guarded.Qualitative.PathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4124`); `AdalyFormal.Round9.Guarded.Qualitative.PathSignChange` (`AHP/round9/qualitative-r2/Attempt.lean:4179`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ} {ε : ℝ}
    (h : PathSignChange q R V f ε) : PathSeparation q R V f ε
```

</details>

<a id="bp-279"></a>
#### bp-279 — `AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalPathVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal free-path vacuum nondegeneracy imply nested cofinal separation with free paths and bounded profiles. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4257`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:347`: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4257`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:347`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-278](#bp-278) (`AdalyFormal.Round9.Guarded.Qualitative.pathSeparation_of_signChange`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4131`); `AdalyFormal.Round9.Guarded.Qualitative.pathSignChange_of_vacuum` (`AHP/round9/qualitative-r2/Attempt.lean:4230`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathVacuum` (`AHP/round9/qualitative-r2/Attempt.lean:4251`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPathSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalPathSeparation
```

</details>

<a id="bp-280"></a>
#### bp-280 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal free-path vacuum nondegeneracy imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4277`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:350`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4277`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:350`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-106](#bp-106) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathSeparation`); [bp-279](#bp-279) (`AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalPathVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathVacuum` (`AHP/round9/qualitative-r2/Attempt.lean:4251`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2
```

</details>

<a id="bp-281"></a>
#### bp-281 — `AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_vacuum_degeneracy`

The positive guarded reading forces the displayed eventual absence of the relevant full-kernel coupling; this is a necessary condition, not a proof of that reading.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4288`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:356`: `'AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_vacuum_degeneracy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4288`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:356`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_vacuum_degeneracy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:154`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.PathVacuumNondegeneracy` (`AHP/round9/qualitative-r2/Attempt.lean:4213`); `AdalyFormal.Round9.Guarded.Qualitative.not_cofinalPathVacuum_of_goalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:4281`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_vacuum_degeneracy (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ PathVacuumNondegeneracy (2^j) R V f
```

</details>

<a id="bp-282"></a>
#### bp-282 — `AdalyFormal.Round9.Guarded.Qualitative.cofinalPathVacuum_of_cofinalVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal vacuum nondegeneracy imply nested cofinal free-path vacuum nondegeneracy. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4320`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:363`: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathVacuum_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4320`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:363`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathVacuum_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask_bound` (`AHP/round9/qualitative-r2/Attempt.lean:4089`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathVacuum` (`AHP/round9/qualitative-r2/Attempt.lean:4251`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumNondegeneracy` (`AHP/round9/qualitative-r2/Attempt.lean:4316`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPathVacuum_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalPathVacuum
```

</details>

<a id="bp-283"></a>
#### bp-283 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumNondegeneracy`

Under its stated geometric and analytic hypotheses, nested cofinal vacuum nondegeneracy imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4329`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:366`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumNondegeneracy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4329`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:366`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumNondegeneracy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-280](#bp-280) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuum`); [bp-282](#bp-282) (`AdalyFormal.Round9.Guarded.Qualitative.cofinalPathVacuum_of_cofinalVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumNondegeneracy` (`AHP/round9/qualitative-r2/Attempt.lean:4316`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalVacuumNondegeneracy (h : CofinalVacuumNondegeneracy) : GoalNeg2
```

</details>

<a id="bp-284"></a>
#### bp-284 — `AdalyFormal.Round9.Guarded.Qualitative.cofinalTwistSeparation_of_cofinalVacuum`

Under its stated geometric and analytic hypotheses, nested cofinal vacuum nondegeneracy imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4333`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:369`: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalTwistSeparation_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4333`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:369`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalTwistSeparation_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-278](#bp-278) (`AdalyFormal.Round9.Guarded.Qualitative.pathSeparation_of_signChange`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.Qualitative.twistA_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4101`); `AdalyFormal.Round9.Guarded.Qualitative.twistD_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4106`); `AdalyFormal.Round9.Guarded.Qualitative.pathSignChange_of_vacuum` (`AHP/round9/qualitative-r2/Attempt.lean:4230`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumNondegeneracy` (`AHP/round9/qualitative-r2/Attempt.lean:4316`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation
```

</details>

<a id="bp-285"></a>
#### bp-285 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuumU1`

Under its stated geometric and analytic hypotheses, nested cofinal charged-line vacuum data imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4407`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:377`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuumU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4407`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:377`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuumU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-280](#bp-280) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalPathVacuum`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.pathVacuum_of_U1` (`AHP/round9/qualitative-r2/Attempt.lean:4375`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathVacuumU1` (`AHP/round9/qualitative-r2/Attempt.lean:4401`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalPathVacuumU1 (h : CofinalPathVacuumU1) : GoalNeg2
```

</details>

<a id="bp-286"></a>
#### bp-286 — `AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalVacuumCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal qualitative vacuum coupling imply nested cofinal separation with free paths and bounded profiles. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4663`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:396`: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4663`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:396`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalPathSeparation_of_cofinalVacuumCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-107](#bp-107) (`AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_of_coupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalPathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4131`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4657`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPathSeparation_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) :
    CofinalPathSeparation
```

</details>

<a id="bp-287"></a>
#### bp-287 — `AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_no_vacuum_coupling`

The positive guarded reading forces the displayed eventual absence of the relevant full-kernel coupling; this is a necessary condition, not a proof of that reading.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4690`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:405`: `'AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_no_vacuum_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4690`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:405`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalPos1_forces_no_vacuum_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:154`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round9.Guarded.Qualitative.VacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4543`); `AdalyFormal.Round9.Guarded.Qualitative.not_cofinalVacuumCoupling_of_goalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:4684`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_no_vacuum_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ VacuumCoupling (2^j) R V f
```

</details>

<a id="bp-288"></a>
#### bp-288 — `AdalyFormal.Round9.Guarded.Qualitative.cofinalVacuumCoupling_of_defectLine`

Under its stated geometric and analytic hypotheses, coupling for the fixed defect-line family imply nested cofinal qualitative vacuum coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4719`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:411`: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalVacuumCoupling_of_defectLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4719`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:411`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.cofinalVacuumCoupling_of_defectLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask_bound` (`AHP/round9/qualitative-r2/Attempt.lean:4089`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4657`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalDefectLineCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4715`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalVacuumCoupling_of_defectLine (h : CofinalDefectLineCoupling) :
    CofinalVacuumCoupling
```

</details>

<a id="bp-289"></a>
#### bp-289 — `AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalDefectLineCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal coupling for the fixed defect line imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:4728`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:414`: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalDefectLineCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:4728`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:414`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalDefectLineCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-108](#bp-108) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling`); [bp-288](#bp-288) (`AdalyFormal.Round9.Guarded.Qualitative.cofinalVacuumCoupling_of_defectLine`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.CofinalDefectLineCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4715`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalDefectLineCoupling (h : CofinalDefectLineCoupling) : GoalNeg2
```

</details>

<a id="bp-290"></a>
#### bp-290 — `AdalyFormal.Round9.Guarded.QualitativeR2.vacuumCoupling_of_soft`

Under its stated geometric and analytic hypotheses, the explicit soft regularity and kernel-coupling hypotheses imply vacuum coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6102`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:548`: `'AdalyFormal.Round9.Guarded.QualitativeR2.vacuumCoupling_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6102`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:548`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.vacuumCoupling_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`); [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/qualitative-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round9/qualitative-r2/Attempt.lean:4481`); `AdalyFormal.Round9.Guarded.Qualitative.VacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4543`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round9/qualitative-r2/Attempt.lean:5161`); `AdalyFormal.Round9.Guarded.QualitativeR2.flatP` (`AHP/round9/qualitative-r2/Attempt.lean:5748`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_pd_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5810`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacuum_crossing` (`AHP/round9/qualitative-r2/Attempt.lean:5867`); `AdalyFormal.Round9.Guarded.QualitativeR2.InteriorSoft` (`AHP/round9/qualitative-r2/Attempt.lean:6020`); `AdalyFormal.Round9.Guarded.QualitativeR2.joint_of_soft` (`AHP/round9/qualitative-r2/Attempt.lean:6060`); `AdalyFormal.Round9.Guarded.QualitativeR2.deriv_of_soft` (`AHP/round9/qualitative-r2/Attempt.lean:6076`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem vacuumCoupling_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCoupling q R V De) : VacuumCoupling q R V f
```

</details>

<a id="bp-291"></a>
#### bp-291 — `AdalyFormal.Round9.Guarded.QualitativeR2.pathSeparation_eventually_of_soft`

Under its stated geometric and analytic hypotheses, the explicit soft regularity and kernel-coupling hypotheses imply path separation eventually. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6119`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:551`: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathSeparation_eventually_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6119`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:551`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathSeparation_eventually_of_soft' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-111](#bp-111) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacEdge`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/qualitative-r2/Attempt.lean:58`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.Qualitative.expansion_of_hasDerivAt` (`AHP/round9/qualitative-r2/Attempt.lean:3437`); `AdalyFormal.Round9.Guarded.Qualitative.metric_of_continuousAt` (`AHP/round9/qualitative-r2/Attempt.lean:3708`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round9/qualitative-r2/Attempt.lean:3971`); `AdalyFormal.Round9.Guarded.Qualitative.pathD` (`AHP/round9/qualitative-r2/Attempt.lean:3977`); `AdalyFormal.Round9.Guarded.Qualitative.pathD_zero` (`AHP/round9/qualitative-r2/Attempt.lean:4054`); `AdalyFormal.Round9.Guarded.Qualitative.PathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4124`); `AdalyFormal.Round9.Guarded.Qualitative.vacA` (`AHP/round9/qualitative-r2/Attempt.lean:4481`); `AdalyFormal.Round9.Guarded.Qualitative.eventually_pathSeparation_pos` (`AHP/round9/qualitative-r2/Attempt.lean:4557`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round9/qualitative-r2/Attempt.lean:5161`); `AdalyFormal.Round9.Guarded.QualitativeR2.flatP` (`AHP/round9/qualitative-r2/Attempt.lean:5748`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_pd_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5810`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacuum_crossing` (`AHP/round9/qualitative-r2/Attempt.lean:5867`); `AdalyFormal.Round9.Guarded.QualitativeR2.InteriorSoft` (`AHP/round9/qualitative-r2/Attempt.lean:6020`); `AdalyFormal.Round9.Guarded.QualitativeR2.joint_of_soft` (`AHP/round9/qualitative-r2/Attempt.lean:6060`); `AdalyFormal.Round9.Guarded.QualitativeR2.deriv_of_soft` (`AHP/round9/qualitative-r2/Attempt.lean:6076`); `AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCouplingPos` (`AHP/round9/qualitative-r2/Attempt.lean:6095`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathSeparation_eventually_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hVc : AdalyFormal.D1Literal.ContFam V) (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCouplingPos q R V De) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε
```

</details>

<a id="bp-292"></a>
#### bp-292 — `AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uth`

Under its stated geometric and analytic hypotheses, the canonical forward twist path imply twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6148`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:554`: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uth' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6148`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:554`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uth' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.Qualitative.twistA_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4101`); `AdalyFormal.Round9.Guarded.Qualitative.twistD_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4106`); `AdalyFormal.Round9.Guarded.Qualitative.PathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4124`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_of_uth {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPath q R) (dilMask q R) ε) : TwistSeparation q R ε
```

</details>

<a id="bp-293"></a>
#### bp-293 — `AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uthNeg`

Under its stated geometric and analytic hypotheses, the canonical backward twist path imply twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6157`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:557`: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uthNeg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6157`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:557`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uthNeg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.Qualitative.twistA_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4101`); `AdalyFormal.Round9.Guarded.Qualitative.twistD_eq_path` (`AHP/round9/qualitative-r2/Attempt.lean:4106`); `AdalyFormal.Round9.Guarded.Qualitative.PathSeparation` (`AHP/round9/qualitative-r2/Attempt.lean:4124`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg` (`AHP/round9/qualitative-r2/Attempt.lean:5579`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_of_uthNeg {q R : ℕ} {ε : ℝ}
    (h : PathSeparation q R (uthPathNeg q R) (dilMask q R) ε) : TwistSeparation q R ε
```

</details>

<a id="bp-294"></a>
#### bp-294 — `AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually`

The stated soft coupling inputs yield actual twist separation at every sufficiently small positive curvature, transferring the sign by the backward path when needed.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6175`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:561`: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6175`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:561`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`); [bp-291](#bp-291) (`AdalyFormal.Round9.Guarded.QualitativeR2.pathSeparation_eventually_of_soft`); [bp-292](#bp-292) (`AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uth`); [bp-293](#bp-293) (`AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_of_uthNeg`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selIn` (`AHP/round9/qualitative-r2/Attempt.lean:33`); `AdalyFormal.Round2.Guarded.Pin.dataS` (`AHP/round9/qualitative-r2/Attempt.lean:58`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5576`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_cont` (`AHP/round9/qualitative-r2/Attempt.lean:5582`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5585`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5591`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5594`); `AdalyFormal.Round9.Guarded.QualitativeR2.flatP` (`AHP/round9/qualitative-r2/Attempt.lean:5748`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uth_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5818`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uthNeg_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5836`); `AdalyFormal.Round9.Guarded.QualitativeR2.TwistSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6170`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_eventually {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) (h : TwistSoftCoupling q R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation q R ε
```

</details>

<a id="bp-295"></a>
#### bp-295 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal forward/backward soft twist coupling imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6197`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:567`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6197`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:567`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-294](#bp-294) (`AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.flat_loc_unit_eventually` (`AHP/round9/qualitative-r2/Attempt.lean:5759`); `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6189`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) :
    CofinalTwistSeparation
```

</details>

<a id="bp-296"></a>
#### bp-296 — `AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal forward/backward soft twist coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6213`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:570`: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6213`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:570`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-295](#bp-295) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6189`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalTwistSoftCoupling (h : CofinalTwistSoftCoupling) : GoalNeg2
```

</details>

<a id="bp-297"></a>
#### bp-297 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalPathSoftCoupling_of_twist`

Under its stated geometric and analytic hypotheses, twist imply nested cofinal soft coupling for free paths. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6242`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:583`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalPathSoftCoupling_of_twist' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6242`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:583`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalPathSoftCoupling_of_twist' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6189`); `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalPathSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6231`); `AdalyFormal.Round9.Guarded.QualitativeR2.pathSoftCoupling_of_twist` (`AHP/round9/qualitative-r2/Attempt.lean:6235`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPathSoftCoupling_of_twist (h : CofinalTwistSoftCoupling) :
    CofinalPathSoftCoupling
```

</details>

<a id="bp-298"></a>
#### bp-298 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalVacuumCoupling_of_cofinalPathSoftCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal soft coupling for free paths imply nested cofinal qualitative vacuum coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6250`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:586`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalVacuumCoupling_of_cofinalPathSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6250`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:586`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalVacuumCoupling_of_cofinalPathSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-290](#bp-290) (`AdalyFormal.Round9.Guarded.QualitativeR2.vacuumCoupling_of_soft`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.Qualitative.CofinalVacuumCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:4657`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5576`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg` (`AHP/round9/qualitative-r2/Attempt.lean:5579`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_cont` (`AHP/round9/qualitative-r2/Attempt.lean:5582`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5585`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5591`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPathNeg_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5594`); `AdalyFormal.Round9.Guarded.QualitativeR2.flat_loc_unit_eventually` (`AHP/round9/qualitative-r2/Attempt.lean:5759`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uth_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5818`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uthNeg_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5836`); `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalPathSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6231`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalVacuumCoupling_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) :
    CofinalVacuumCoupling
```

</details>

<a id="bp-299"></a>
#### bp-299 — `AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal soft coupling for free paths imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6271`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:589`: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6271`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:589`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalPathSoftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-108](#bp-108) (`AdalyFormal.Round9.Guarded.Qualitative.goalNeg2_of_cofinalVacuumCoupling`); [bp-298](#bp-298) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalVacuumCoupling_of_cofinalPathSoftCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalPathSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6231`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalPathSoftCoupling (h : CofinalPathSoftCoupling) : GoalNeg2
```

</details>

<a id="bp-300"></a>
#### bp-300 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSoftCoupling_of_fwd`

Under its stated geometric and analytic hypotheses, forward coupling transferred by the exact gauge flip imply nested cofinal forward/backward soft twist coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6656`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:627`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSoftCoupling_of_fwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6656`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:627`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSoftCoupling_of_fwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6189`); `AdalyFormal.Round9.Guarded.QualitativeR2.twistSoftCoupling_of_fwd` (`AHP/round9/qualitative-r2/Attempt.lean:6646`); `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6652`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSoftCoupling_of_fwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSoftCoupling
```

</details>

<a id="bp-301"></a>
#### bp-301 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd`

Under its stated geometric and analytic hypotheses, nested cofinal forward soft twist coupling imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6665`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:630`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6665`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:630`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-295](#bp-295) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCoupling`); [bp-300](#bp-300) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSoftCoupling_of_fwd`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6652`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) :
    CofinalTwistSeparation
```

</details>

<a id="bp-302"></a>
#### bp-302 — `AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCouplingFwd`

Under its stated geometric and analytic hypotheses, nested cofinal forward soft twist coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6669`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:633`: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCouplingFwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6669`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:633`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftCouplingFwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-301](#bp-301) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6652`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalTwistSoftCouplingFwd (h : CofinalTwistSoftCouplingFwd) : GoalNeg2
```

</details>

<a id="bp-303"></a>
#### bp-303 — `AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually_of_fwd`

Under its stated geometric and analytic hypotheses, forward coupling transferred by the exact gauge flip imply twist separation eventually. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6678`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:639`: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually_of_fwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6678`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:639`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually_of_fwd' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-074](#bp-074) (`AdalyFormal.Round8.Guarded.SignFree.TwistSeparation`); [bp-294](#bp-294) (`AdalyFormal.Round9.Guarded.QualitativeR2.twistSeparation_eventually`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.flat_loc_unit_eventually` (`AHP/round9/qualitative-r2/Attempt.lean:5759`); `AdalyFormal.Round9.Guarded.QualitativeR2.TwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6642`); `AdalyFormal.Round9.Guarded.QualitativeR2.twistSoftCoupling_of_fwd` (`AHP/round9/qualitative-r2/Attempt.lean:6646`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem twistSeparation_eventually_of_fwd :
    ∃ j₁ : ℕ, ∀ j : ℕ, j₁ ≤ j → ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → 2 ∣ R → 18 ≤ R →
      TwistSoftCouplingFwd (2^j) R →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → TwistSeparation (2^j) R ε
```

</details>

<a id="bp-304"></a>
#### bp-304 — `AdalyFormal.Round9.Guarded.QualitativeR2.goalPos1_forces_no_softCoupling`

The positive guarded reading forces the displayed eventual absence of the relevant full-kernel coupling; this is a necessary condition, not a proof of that reading.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6692`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:642`: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalPos1_forces_no_softCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6692`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:642`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalPos1_forces_no_softCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:154`); `AdalyFormal.Round9.Guarded.QualitativeR2.TwistSoftCouplingFwd` (`AHP/round9/qualitative-r2/Attempt.lean:6642`); `AdalyFormal.Round9.Guarded.QualitativeR2.not_cofinalTwistSoftCouplingFwd_of_goalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:6672`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_no_softCoupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ TwistSoftCouplingFwd (2^j) R
```

</details>

<a id="bp-305"></a>
#### bp-305 — `AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftU1`

Under its stated geometric and analytic hypotheses, nested cofinal charged-line soft twist coupling imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6982`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:668`: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6982`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:668`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-301](#bp-301) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.twistSoftCouplingFwd_of_U1` (`AHP/round9/qualitative-r2/Attempt.lean:6975`); `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftU1` (`AHP/round9/qualitative-r2/Attempt.lean:6979`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) :
    CofinalTwistSeparation
```

</details>

<a id="bp-306"></a>
#### bp-306 — `AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftU1`

Under its stated geometric and analytic hypotheses, nested cofinal charged-line soft twist coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6990`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:671`: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6990`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:671`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.goalNeg2_of_cofinalTwistSoftU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-078](#bp-078) (`AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation`); [bp-305](#bp-305) (`AdalyFormal.Round9.Guarded.QualitativeR2.cofinalTwistSeparation_of_cofinalTwistSoftU1`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalTwistSoftU1` (`AHP/round9/qualitative-r2/Attempt.lean:6979`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalTwistSoftU1 (h : CofinalTwistSoftU1) : GoalNeg2
```

</details>

<a id="bp-307"></a>
#### bp-307 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_coupling`

The positive guarded reading forces the displayed eventual absence of the relevant full-kernel coupling; this is a necessary condition, not a proof of that reading.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11737`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1127`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11737`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1127`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalPos1_forces_degenerate_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.GoalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:154`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.not_cofinalCanonicalCoupling_of_goalPos1` (`AHP/round9/qualitative-r2/Attempt.lean:11732`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalPos1_forces_degenerate_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ¬ QualitativeR2.CanonicalCoupling (2^j) R (uthPath (2^j) R)
        (corrDeriv (2^j) R (dilMask (2^j) R))
```

</details>

<a id="bp-308"></a>
#### bp-308 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul`

A positive rescaling of the profile derivative preserves definite whole-kernel coupling, rescaling its positive margin.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11835`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1141`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11835`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1141`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_smul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_smul {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    {c : ℝ} (hc : c ≠ 0) (h : QualitativeR2.CanonicalCoupling q R V De) :
    QualitativeR2.CanonicalCoupling q R V (c • De)
```

</details>

<a id="bp-309"></a>
#### bp-309 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile`

Under its stated geometric and analytic hypotheses, arbitrary-profile coupling on the canonical path imply nested cofinal soft coupling for free paths. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11897`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1153`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11897`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1153`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalPathSoftCoupling_of_anyProfile' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.CofinalPathSoftCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:6231`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11869`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.pathSoftCoupling_of_profile` (`AHP/round9/qualitative-r2/Attempt.lean:11887`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalPathSoftCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    QualitativeR2.CofinalPathSoftCoupling
```

</details>

<a id="bp-310"></a>
#### bp-310 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyProfileCoupling_of_canonical`

Under its stated geometric and analytic hypotheses, canonical-profile coupling imply nested cofinal canonical-path coupling with free profiles. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11912`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1162`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyProfileCoupling_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11912`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1162`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyProfileCoupling_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11711`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11869`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyProfileCoupling_of_canonical (h : CofinalCanonicalCoupling) :
    CofinalAnyProfileCoupling
```

</details>

<a id="bp-311"></a>
#### bp-311 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit`

Under its stated geometric and analytic hypotheses, the explicit flat constrained source/jet coupling imply canonical coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:11997`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1176`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:11997`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1176`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-127](#bp-127) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_J_tendsto` (`AHP/round9/qualitative-r2/Attempt.lean:10950`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11989`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_explicit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitCoupling q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R))
```

</details>

<a id="bp-312"></a>
#### bp-312 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit`

Under its stated geometric and analytic hypotheses, the explicit flat constrained source/jet coupling imply nested cofinal canonical-profile coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12011`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1182`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12011`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1182`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-311](#bp-311) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicit`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalCanonicalCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11711`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:12007`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalCanonicalCoupling_of_explicit (h : CofinalExplicitCoupling) :
    CofinalCanonicalCoupling
```

</details>

<a id="bp-313"></a>
#### bp-313 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal explicit flat source/jet coupling imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12019`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1185`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12019`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1185`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-122](#bp-122) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling`); [bp-312](#bp-312) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:12007`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) :
    CofinalTwistSeparation
```

</details>

<a id="bp-314"></a>
#### bp-314 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitCoupling`

Under its stated geometric and analytic hypotheses, nested cofinal explicit flat source/jet coupling imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12023`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1188`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12023`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1188`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-123](#bp-123) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling`); [bp-312](#bp-312) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalCanonicalCoupling_of_explicit`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:12007`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalExplicitCoupling (h : CofinalExplicitCoupling) : GoalNeg2
```

</details>

<a id="bp-315"></a>
#### bp-315 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1`

Under its stated geometric and analytic hypotheses, the explicit nonzero scalar coupling on the complete charged kernel line imply canonical coupling. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12040`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1192`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12040`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1192`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-114](#bp-114) (`AdalyFormal.Round9.Guarded.QualitativeR2.canonicalCoupling_of_U1`); [bp-117](#bp-117) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`); [bp-127](#bp-127) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv_dilMask_form`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.dilMask` (`AHP/round9/qualitative-r2/Attempt.lean:4086`); `AdalyFormal.Round9.Guarded.AnalyticR2.dil_J_tendsto` (`AHP/round9/qualitative-r2/Attempt.lean:10950`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round9/qualitative-r2/Attempt.lean:11638`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.ExplicitU1` (`AHP/round9/qualitative-r2/Attempt.lean:12029`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem canonicalCoupling_of_explicitU1 {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (h : ExplicitU1 q R) :
    QualitativeR2.CanonicalCoupling q R (uthPath q R) (corrDeriv q R (dilMask q R))
```

</details>

<a id="bp-316"></a>
#### bp-316 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitU1`

Under its stated geometric and analytic hypotheses, nested cofinal explicit coupling on a charged kernel line imply the pinned negative guarded headline. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12053`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1198`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12053`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1198`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalExplicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-001](#bp-001) (`AdalyFormal.Round2.Guarded.Pin.GoalNeg2`); [bp-123](#bp-123) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling`); [bp-315](#bp-315) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitU1` (`AHP/round9/qualitative-r2/Attempt.lean:12050`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem goalNeg2_of_cofinalExplicitU1 (h : CofinalExplicitU1) : GoalNeg2
```

</details>

<a id="bp-317"></a>
#### bp-317 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitU1`

Under its stated geometric and analytic hypotheses, nested cofinal explicit coupling on a charged kernel line imply nested cofinal actual twist separation. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12061`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1201`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12061`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1201`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalExplicitU1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-077](#bp-077) (`AdalyFormal.Round8.Guarded.SignFree.CofinalTwistSeparation`); [bp-122](#bp-122) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalTwistSeparation_of_cofinalCanonicalCoupling`); [bp-315](#bp-315) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.canonicalCoupling_of_explicitU1`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitU1` (`AHP/round9/qualitative-r2/Attempt.lean:12050`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalTwistSeparation_of_cofinalExplicitU1 (h : CofinalExplicitU1) :
    CofinalTwistSeparation
```

</details>

<a id="bp-318"></a>
#### bp-318 — `AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyPathCoupling_of_anyProfile`

Under its stated geometric and analytic hypotheses, arbitrary-profile coupling on the canonical path imply nested cofinal coupling with free path and profile. This implication does not supply its input premise.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:12109`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:1216`: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyPathCoupling_of_anyProfile' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:12109`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:1216`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.cofinalAnyPathCoupling_of_anyProfile' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-128](#bp-128) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyPathCoupling`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round9/qualitative-r2/Attempt.lean:4078`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath_cont` (`AHP/round9/qualitative-r2/Attempt.lean:4081`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5576`); `AdalyFormal.Round9.Guarded.QualitativeR2.uthPath_zero` (`AHP/round9/qualitative-r2/Attempt.lean:5591`); `AdalyFormal.Round9.Guarded.QualitativeR2.vacA_uth_pi_negative` (`AHP/round9/qualitative-r2/Attempt.lean:5818`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round9/qualitative-r2/Attempt.lean:11869`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyPathCoupling_of_anyProfile (h : CofinalAnyProfileCoupling) :
    CofinalAnyPathCoupling
```

</details>

<a id="bp-319"></a>
#### bp-319 — `AdalyFormal.Round10.Assembly.cofinal_of_eventual_subsequence`

Under its stated geometric and analytic hypotheses, eventual subsequence imply cofinal. This implication does not supply its input premise.

- **Source:** `AHP/round10/shared/assembly/R1_Cofinal.lean:22`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R1_Cofinal.lean.log:4`: `'AdalyFormal.Round10.Assembly.cofinal_of_eventual_subsequence' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinal_of_eventual_subsequence {P : ℕ → Prop} {r : ℕ → ℕ}
    (hr : ∀ n, n ≤ r n) (hP : ∀ᶠ n in atTop, P (r n)) :
    ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ P R
```

</details>

<a id="bp-320"></a>
#### bp-320 — `AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_dominatedSource`

Under its stated geometric and analytic hypotheses, nested cofinal full-kernel lines with exact source domination imply nested cofinal canonical-path coupling with free profiles. This implication does not supply its input premise.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1377`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:140`: `'AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_dominatedSource' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-155](#bp-155) (`AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_dominatedSource`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:146`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:420`); `AdalyFormal.Round10.Assembly.R2.CofinalDominatedSource` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1370`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyProfileCoupling_of_dominatedSource (h : CofinalDominatedSource) :
    CofinalAnyProfileCoupling
```

</details>

<a id="bp-321"></a>
#### bp-321 — `AdalyFormal.Round10.Assembly.R3.cofinalAnyProfileCoupling_of_curlLine`

Under its stated geometric and analytic hypotheses, detected whole charged kernel lines imply nested cofinal canonical-path coupling with free profiles. This implication does not supply its input premise.

- **Source:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2216`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log:240`: `'AdalyFormal.Round10.Assembly.R3.cofinalAnyProfileCoupling_of_curlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-162](#bp-162) (`AdalyFormal.Round10.Assembly.R3.canonicalCoupling_of_curlDetected`)
- **Additional local source references:** `AdalyFormal.Round10.Dictionary.FreeSource.responseProfile` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1264`); `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1422`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:1712`); `AdalyFormal.Round10.Assembly.R3.CofinalCurlLine` (`AHP/round10/shared/assembly/R3_EnergyGlue.lean:2200`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyProfileCoupling_of_curlLine (hr : RegularityFacts) (h : CofinalCurlLine) :
    CofinalAnyProfileCoupling
```

</details>

<a id="bp-322"></a>
#### bp-322 — `AdalyFormal.Round10.Assembly.R3.cofinalCurlLine_of_jetLine`

Under its stated geometric and analytic hypotheses, nonzero physical top jets on whole charged kernel lines imply nested cofinal canonical-path detected kernel lines. This implication does not supply its input premise.

- **Source:** `AHP/round10/shared/assembly/R3_JetGlue.lean:3153`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R3_JetGlue.lean.log:381`: `'AdalyFormal.Round10.Assembly.R3.cofinalCurlLine_of_jetLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Assembly.R3.CofinalCurlLine` (`AHP/round10/shared/assembly/R3_JetGlue.lean:2201`); `AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_physicalJet` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3078`); `AdalyFormal.Round10.Assembly.R3.FlatConstraintUnits` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3131`); `AdalyFormal.Round10.Assembly.R3.CofinalJetLine` (`AHP/round10/shared/assembly/R3_JetGlue.lean:3136`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalCurlLine_of_jetLine (hN : FlatConstraintUnits) (h : CofinalJetLine) :
    CofinalCurlLine
```

</details>

<a id="bp-323"></a>
#### bp-323 — `AdalyFormal.Round10.Assembly.R4.cofinalAnyProfileCoupling_iff_noCancellation`

The two displayed cofinal formulations are equivalent under the stated regularity hypotheses, with the nested scale/radius quantifiers unchanged.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2558`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:292`: `'AdalyFormal.Round10.Assembly.R4.cofinalAnyProfileCoupling_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-173](#bp-173) (`AdalyFormal.Round10.Assembly.R4.exists_canonicalCoupling_iff_noCancellation`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.uthPath` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1422`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:1712`); `AdalyFormal.Round10.Assembly.R4.CofinalNoResponseCancellation` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2545`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalAnyProfileCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyProfileCoupling ↔ CofinalNoResponseCancellation
```

</details>

<a id="bp-324"></a>
#### bp-324 — `AdalyFormal.Round10.Assembly.R4.cofinalNoCancellation_of_curlLine`

Under its stated geometric and analytic hypotheses, detected whole charged kernel lines imply cofinal canonical-path hull noncancellation. This implication does not supply its input premise.

- **Source:** `AHP/round10/shared/assembly/R4_ResponseHull.lean:2594`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R4_ResponseHull.lean.log:298`: `'AdalyFormal.Round10.Assembly.R4.cofinalNoCancellation_of_curlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-160](#bp-160) (`AdalyFormal.Round10.Assembly.R3.RegularityFacts`); [bp-321](#bp-321) (`AdalyFormal.Round10.Assembly.R3.cofinalAnyProfileCoupling_of_curlLine`); [bp-323](#bp-323) (`AdalyFormal.Round10.Assembly.R4.cofinalAnyProfileCoupling_iff_noCancellation`)
- **Additional local source references:** `AdalyFormal.Round10.Assembly.R3.CofinalCurlLine` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2200`); `AdalyFormal.Round10.Assembly.R4.CofinalNoResponseCancellation` (`AHP/round10/shared/assembly/R4_ResponseHull.lean:2545`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem cofinalNoCancellation_of_curlLine (hr : RegularityFacts)
    (h : R3.CofinalCurlLine) : CofinalNoResponseCancellation
```

</details>

### Additional unconditional inputs and conditional subreductions

<a id="bp-325"></a>
#### bp-325 — `AdalyFormal.Round9.Guarded.Qualitative.perturbative_sign_change`

Joint first-order scalar action on the vacuum kernel, a complementary gap and a nonzero correction coefficient give sign-change interval control for either correction sign.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:3101`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:288`: `'AdalyFormal.Round9.Guarded.Qualitative.perturbative_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:3101`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:288`, exit `0`; record: `'AdalyFormal.Round9.Guarded.Qualitative.perturbative_sign_change' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-071](#bp-071) (`AdalyFormal.Round8.Guarded.SignFree.unit_of_definite_complements`)
- **Additional local source references:** `AdalyFormal.Round9.Guarded.Qualitative.block_pos` (`AHP/round9/qualitative-r2/Attempt.lean:2970`); `AdalyFormal.Round9.Guarded.Qualitative.perp_lower` (`AHP/round9/qualitative-r2/Attempt.lean:3030`); `AdalyFormal.Round9.Guarded.Qualitative.cross_upper` (`AHP/round9/qualitative-r2/Attempt.lean:3047`); `AdalyFormal.Round9.Guarded.Qualitative.kernel_form_bounds` (`AHP/round9/qualitative-r2/Attempt.lean:3065`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem perturbative_sign_change
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (ts : ℝ) (K : Submodule ℝ E) (g σ α c : ℝ) (At Ae De : E →L[ℝ] E)
    (hker : ∀ u ∈ K, A 0 ts u = 0)
    (hg : 0 < g) (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A 0 ts y⟫)
    (hne : ∃ u ∈ K, u ≠ 0)
    (hσ : σ < 0) (hc : c ≠ 0)
    (hAt : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2)
    (hAe : ∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2)
    (hDe : ∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2)
    (hAexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖A ε (ts + τ) - A 0 ts - τ • At - ε • Ae‖ ≤ η * (|ε| + |τ|))
    (hDexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r →
      ‖D ε - ε • De‖ ≤ η * |ε|) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧ (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A ε t)) ∧
        PSD (A ε t₀ - D ε) ∧ ∃ w : E, ⟪w, (A ε t₁ - D ε) w⟫ < 0
```

</details>

<a id="bp-326"></a>
#### bp-326 — `AdalyFormal.Round9.Guarded.QualitativeR2.pathA_anR`

The actual carrier along an analytic exterior path is real analytic in the angle, through the frozen plaquette formula.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:5601`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:491`: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathA_anR' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:5601`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:491`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathA_anR' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-048](#bp-048) (`AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/qualitative-r2/Attempt.lean:35`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.Qualitative.pathU` (`AHP/round9/qualitative-r2/Attempt.lean:3962`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round9/qualitative-r2/Attempt.lean:3971`); `AdalyFormal.Round9.Guarded.Qualitative.path_agrees` (`AHP/round9/qualitative-r2/Attempt.lean:3982`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnR` (`AHP/round9/qualitative-r2/Attempt.lean:4794`); `AdalyFormal.Round9.Guarded.QualitativeR2.anR_const` (`AHP/round9/qualitative-r2/Attempt.lean:4796`); `AdalyFormal.Round9.Guarded.QualitativeR2.AnFam` (`AHP/round9/qualitative-r2/Attempt.lean:5161`); `AdalyFormal.Round9.Guarded.QualitativeR2.an_inner_delta` (`AHP/round9/qualitative-r2/Attempt.lean:5291`); `AdalyFormal.Round9.Guarded.QualitativeR2.pathU_anFam` (`AHP/round9/qualitative-r2/Attempt.lean:5566`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathA_anR {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    AnR (fun t => ⟪x, pathA q R V f ε a t y⟫)
```

</details>

<a id="bp-327"></a>
#### bp-327 — `AdalyFormal.Round9.Guarded.QualitativeR2.pathA_jointly_continuousAt`

Interior soft regularity and the exterior path identity yield joint curvature-angle continuity of the actual carrier.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:5955`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:530`: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathA_jointly_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:5955`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:530`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.pathA_jointly_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-027](#bp-027) (`AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible`); [bp-048](#bp-048) (`AdalyFormal.Round5.Guarded.IVTR1.exterior_carrier_path`)
- **Additional local source references:** `AdalyFormal.Round2.Guarded.Pin.selAll` (`AHP/round9/qualitative-r2/Attempt.lean:35`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round9/qualitative-r2/Attempt.lean:994`); `AdalyFormal.Round9.Guarded.Qualitative.pathU` (`AHP/round9/qualitative-r2/Attempt.lean:3962`); `AdalyFormal.Round9.Guarded.Qualitative.pathA` (`AHP/round9/qualitative-r2/Attempt.lean:3971`); `AdalyFormal.Round9.Guarded.Qualitative.path_agrees` (`AHP/round9/qualitative-r2/Attempt.lean:3982`); `AdalyFormal.Round9.Guarded.QualitativeR2.contY_deltaKLocCLM` (`AHP/round9/qualitative-r2/Attempt.lean:5480`); `AdalyFormal.Round9.Guarded.QualitativeR2.pathU_contFamY` (`AHP/round9/qualitative-r2/Attempt.lean:5942`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem pathA_jointly_continuousAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hA0 : ContinuousAt (fun ε : ℝ => pathA q R V f ε 1 0) 0)
    (hW0 : ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) 0)
    (t : ℝ) : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)
```

</details>

<a id="bp-328"></a>
#### bp-328 — `AdalyFormal.Round9.Guarded.QualitativeR2.De_rot_comm`

The genuine correction derivative commutes with diagonal gauge rotations under the displayed actual-family regularity hypotheses.

- **Source:** `AHP/round9/qualitative-r2/Attempt.lean:6899`.
- **Status:** A — compiled and independently verified. Recorded exit: `0`.
- **Axioms:** `AHP/round9/qualitative-r2/Attempt.lean.log:658`: `'AdalyFormal.Round9.Guarded.QualitativeR2.De_rot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round9/qualitative-r2/Attempt.verify.lean:6899`, identical declaration body; `AHP/round9/qualitative-r2/Attempt.verify.lean.log:658`, exit `0`; record: `'AdalyFormal.Round9.Guarded.QualitativeR2.De_rot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round9/qualitative-r2/Attempt.lean:986`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round9/qualitative-r2/Attempt.lean:989`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD` (`AHP/round9/qualitative-r2/Attempt.lean:6013`); `AdalyFormal.Round9.Guarded.QualitativeR2.hasDerivAt_quadForm` (`AHP/round9/qualitative-r2/Attempt.lean:6584`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round9/qualitative-r2/Attempt.lean:6772`); `AdalyFormal.Round9.Guarded.QualitativeR2.bulkD_rot` (`AHP/round9/qualitative-r2/Attempt.lean:6841`); `AdalyFormal.Round9.Guarded.QualitativeR2.De_symm` (`AHP/round9/qualitative-r2/Attempt.lean:6884`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem De_rot_comm {q R : ℕ} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hD : HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0) (α : ℝ)
    (y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    De (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) y) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (De y)
```

</details>

<a id="bp-329"></a>
#### bp-329 — `AdalyFormal.Round10.Assembly.R2.exists_profile_coupling_of_sourceColumns`

Exact physical source-column equations and a nonzero jet vector yield some definite profile when the whole charged kernel-line condition is supplied.

- **Source:** `AHP/round10/shared/assembly/R2_SourceGlue.lean:1454`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/assembly/R2_SourceGlue.lean.log:121`: `'AdalyFormal.Round10.Assembly.R2.exists_profile_coupling_of_sourceColumns' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-112](#bp-112) (`AdalyFormal.Round9.Guarded.QualitativeR2.CanonicalCoupling`); [bp-189](#bp-189) (`AdalyFormal.Round10.Nonvanishing.FreeProfile.exists_coupling_of_source_columns`); [bp-152](#bp-152) (`AdalyFormal.Round10.Assembly.R2.KernelLine`); [bp-154](#bp-154) (`AdalyFormal.Round10.Assembly.R2.canonicalCoupling_of_line`)
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:79`); `AdalyFormal.Round9.Guarded.QualitativeR2Joint.corrDeriv` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:294`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:317`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.prev` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:929`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.sourceRhs` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1118`); `AdalyFormal.Round10.Nonvanishing.FreeProfile.columnWeight` (`AHP/round10/shared/assembly/R2_SourceGlue.lean:1135`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem exists_profile_coupling_of_sourceColumns {q R : ℕ}
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R)
    (hline : KernelLine q R V u) (N : ℕ) (b : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (profiles : ℕ → Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (factor : ℝ)
    (hb : b N = 0) (hne : ∃ j < N, b j ≠ 0) (hf : factor ≠ 0)
    (hc : ∀ i < N, c i N = 0)
    (heq : ∀ i < N, ∀ j < N, 6*c i j + Nonvanishing.FreeProfile.prev (c i) j +
      c i (j+1) = Nonvanishing.FreeProfile.sourceRhs i j)
    (hdict : ∀ i < N, ⟪u, corrDeriv q R (profiles i) u⟫ = factor *
      (∑ j ∈ Finset.range N, Nonvanishing.FreeProfile.columnWeight (c i) i j * b j)) :
    ∃ i < N, CanonicalCoupling q R V (corrDeriv q R (profiles i))
```

</details>

<a id="bp-330"></a>
#### bp-330 — `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_U1`

The actual flat source/jet pairing is invariant under every constant diagonal phase for every physical profile.

- **Source:** `AHP/round10/shared/dictionary/R3_FreeSource.lean:1405`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R3_FreeSource.lean.log:211`: `'AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling_U1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round4.Guarded.RefuteR1.dilLu` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:83`); `AdalyFormal.Round4.Guarded.RefuteR1.dilTower` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:86`); `AdalyFormal.Round4.Guarded.RefuteR1.dilLam` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:91`); `AdalyFormal.Round9.Guarded.QualitativeR2.rotGauge` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:210`); `AdalyFormal.Round9.Guarded.QualitativeR2.rot_trivial` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:242`); `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:330`); `AdalyFormal.Round9.Guarded.AnalyticR2.flatData` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:366`); `AdalyFormal.Round10.Dictionary.Source.flatH_U1` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:818`); `AdalyFormal.Round10.Dictionary.Source.profileSourceStencil` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:980`); `AdalyFormal.Round10.Dictionary.FreeSource.profileCoupling` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:1270`); `AdalyFormal.Round10.Dictionary.FreeSource.profileSource_U1` (`AHP/round10/shared/dictionary/R3_FreeSource.lean:1398`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem profileCoupling_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      profileCoupling q R f u
```

</details>

<a id="bp-331"></a>
#### bp-331 — `AdalyFormal.Round10.Dictionary.Color.flatJet_neutral_zero`

Every neutral input has zero full flat dressed quadratic jet by global color covariance and quadratic evenness.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:1764`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:235`: `'AdalyFormal.Round10.Dictionary.Color.flatJet_neutral_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.flipElt` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1610`); `AdalyFormal.Round10.Dictionary.Color.quad_even` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1635`); `AdalyFormal.Round10.Dictionary.Color.halfE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1693`); `AdalyFormal.Round10.Dictionary.Color.flipE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1696`); `AdalyFormal.Round10.Dictionary.Color.flatJet` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1698`); `AdalyFormal.Round10.Dictionary.Color.flatJet_quad` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1701`); `AdalyFormal.Round10.Dictionary.Color.flatJet_gauge` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1705`); `AdalyFormal.Round10.Dictionary.Color.two_fixed_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1746`); `AdalyFormal.Round10.Dictionary.Color.halfE_flip_on_fixed` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1755`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem flatJet_neutral_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = u) : flatJet G a u = 0
```

</details>

<a id="bp-332"></a>
#### bp-332 — `AdalyFormal.Round10.Dictionary.Color.flatJet_single_color_zero`

A charged input in one flip eigencolor has zero full dressed jet, showing that charge alone cannot give detection.

- **Source:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean:1789`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log:239`: `'AdalyFormal.Round10.Dictionary.Color.flatJet_single_color_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round9.Guarded.QualitativeR2.flipElt` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1610`); `AdalyFormal.Round10.Dictionary.Color.quad_even` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1635`); `AdalyFormal.Round10.Dictionary.Color.halfE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1693`); `AdalyFormal.Round10.Dictionary.Color.flipE` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1696`); `AdalyFormal.Round10.Dictionary.Color.flatJet` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1698`); `AdalyFormal.Round10.Dictionary.Color.flatJet_quad` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1701`); `AdalyFormal.Round10.Dictionary.Color.flatJet_gauge` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1705`); `AdalyFormal.Round10.Dictionary.Color.two_fixed_zero` (`AHP/round10/shared/dictionary/R4_ColorResponse.lean:1746`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem flatJet_single_color_zero (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hh : halfE G u = -u) (hf : flipE G u = u ∨ flipE G u = -u) :
    flatJet G a u = 0
```

</details>

<a id="bp-333"></a>
#### bp-333 — `AdalyFormal.Round10.Nonvanishing.radius_cofinal_nonzero`

An exact reversible scalar recurrence with a nonzero seed on the even-radius progression yields arbitrarily large admissible nonzero radii at the fixed scale.

- **Source:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:62`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean.log:7`: `'AdalyFormal.Round10.Nonvanishing.radius_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-186](#bp-186) (`AdalyFormal.Round10.Nonvanishing.recurrence_cofinal_nonzero`)
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.RadiusRecurrenceData` (`AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:55`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem radius_cofinal_nonzero (coupling : ℕ → ℕ → ℝ) (q : ℕ)
    (h : RadiusRecurrenceData coupling q) :
    ∀ R₀, ∃ R, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling q R ≠ 0
```

</details>

<a id="bp-334"></a>
#### bp-334 — `AdalyFormal.Round10.Nonvanishing.dyadic_cofinal_nonzero`

Cofinal dyadic scales equipped with those exact radius-recurrence data give the required nested scalar nonvanishing.

- **Source:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:72`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean.log:8`: `'AdalyFormal.Round10.Nonvanishing.dyadic_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-333](#bp-333) (`AdalyFormal.Round10.Nonvanishing.radius_cofinal_nonzero`)
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.RadiusRecurrenceData` (`AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean:55`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem dyadic_cofinal_nonzero (coupling : ℕ → ℕ → ℝ)
    (h : ∀ j₀, ∃ j, j₀ ≤ j ∧ RadiusRecurrenceData coupling (2 ^ j)) :
    ∀ j₀, ∃ j, j₀ ≤ j ∧ ∀ R₀, ∃ R,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling (2 ^ j) R ≠ 0
```

</details>

<a id="bp-335"></a>
#### bp-335 — `AdalyFormal.Round10.Nonvanishing.transfer_progression_cofinal_nonzero`

Injective transfer dynamics preserve cofinal observable nonvanishing along the specified arithmetic progression when a nonzero seed on that progression is supplied.

- **Source:** `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean:79`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean.log:9`: `'AdalyFormal.Round10.Nonvanishing.transfer_progression_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-187](#bp-187) (`AdalyFormal.Round10.Nonvanishing.transfer_cofinal_nonzero`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem transfer_progression_cofinal_nonzero (T : E →ₗ[K] E) (hT : Function.Injective T)
    (L : E →ₗ[K] K) (x : E) (step offset k : ℕ)
    (hk : L ((T ^ (step * k + offset)) x) ≠ 0) :
    ∀ N, ∃ n, N ≤ n ∧ L ((T ^ (step * n + offset)) x) ≠ 0
```

</details>

<a id="bp-336"></a>
#### bp-336 — `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.geometric_grid_ne_zero_eventually`

A nonzero fixed bivariate polynomial evaluated on an injective geometric scale/radius grid is eventually nonzero with a radius threshold allowed to depend on the scale.

- **Source:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:78`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean.log:21`: `'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.geometric_grid_ne_zero_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.evalTwo` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:31`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.grid_ne_zero_eventually` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:56`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.dyadic_argument_injective` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:66`); `AdalyFormal.Round10.Nonvanishing.PolynomialGrid.radius_argument_injective` (`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:71`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem geometric_grid_ne_zero_eventually (p : ℝ[X][X]) (hp : p ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
      evalTwo p (ρ ^ (2 ^ j)) (ρ ^ ((2 ^ j) * R)) ≠ 0
```

</details>

<a id="bp-337"></a>
#### bp-337 — `AdalyFormal.Round12.Kernel.kernel_concentrates`

If an invariant decomposition has one strictly positive complementary part, every kernel vector lies in the remaining component; positivity, not symmetry alone, supplies spectral exclusion.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1360`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:121`: `'AdalyFormal.Round12.Kernel.kernel_concentrates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem kernel_concentrates (A : E →L[ℝ] E) (P : E →L[ℝ] E)
    (hcomm : ∀ x, A (P x) = P (A x))
    (hpos : ∀ x, x ≠ 0 → P x = 0 → 0 < ⟪x, A x⟫)
    (hidem : ∀ x, P (P x) = P x) (u : E) (hu : A u = 0) :
    P u = u
```

</details>

<a id="bp-338"></a>
#### bp-338 — `AdalyFormal.Round12.Kernel.opposite_character_disjoint`

Opposite nonreal character eigenspaces are disjoint under the stated character hypotheses.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1375`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:122`: `'AdalyFormal.Round12.Kernel.opposite_character_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem opposite_character_disjoint (T F : E →ₗ[ℝ] E)
    (J : E →ₗ[ℝ] E) (a b : ℝ) (hb : b ≠ 0)
    (hTF : ∀ x, T (F x) = F (T x))
    (hFJ : ∀ x, F (J x) = -J (F x))
    (hJ : Function.Injective J) (u : E)
    (hu : T u = a • u + b • J u)
    (hFu : T (F u) = a • F u + b • J (F u)) : F u = 0
```

</details>

<a id="bp-339"></a>
#### bp-339 — `AdalyFormal.Round12.Kernel.no_flip_eigenvector`

A flip exchanging the specified distinct character sectors cannot have a nonzero eigenvector in their single-sector kernel under the displayed assumptions.

- **Source:** `AHP/round12/shared/kernel/R1_ActualKernel.lean:1397`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/kernel/R1_ActualKernel.lean.log:123`: `'AdalyFormal.Round12.Kernel.no_flip_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-338](#bp-338) (`AdalyFormal.Round12.Kernel.opposite_character_disjoint`)

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem no_flip_eigenvector (T F J : E →ₗ[ℝ] E) (a b c : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hTF : ∀ x, T (F x) = F (T x))
    (hFJ : ∀ x, F (J x) = -J (F x))
    (hJ : Function.Injective J) (u : E)
    (hu : T u = a • u + b • J u) (hFu : F u = c • u) : u = 0
```

</details>

<a id="bp-340"></a>
#### bp-340 — `AdalyFormal.Round12.Noncancel.Star.positive_on_trace_zero`

A full star-form decomposition with nonnegative remainder and strict positivity of remainder plus leaf norms on nonzero fields implies strict zero-trace positivity. The actual physical decomposition remains an input.

- **Source:** `AHP/round12/shared/noncancel/R1_Star.lean:129`.
- **Status:** B — builder-compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round12/shared/noncancel/R1_Star.lean.log:12`: `'AdalyFormal.Round12.Noncancel.Star.positive_on_trace_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** No additional node in this ledger; use the explicit hypotheses and frozen/Mathlib background.
- **Additional local source references:** `AdalyFormal.Round12.Noncancel.Star.pairForm` (`AHP/round12/shared/noncancel/R1_Star.lean:12`); `AdalyFormal.Round12.Noncancel.Star.star_mass_lower` (`AHP/round12/shared/noncancel/R1_Star.lean:52`).

<details><summary>Exact Lean signature (explicit hypotheses retained)</summary>

```lean
theorem positive_on_trace_zero {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℝ] E) (l : E →ₗ[ℝ] ℂ) (rest : E → ℝ)
    (y z : E → ι → ℂ) (c s : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcs : c^2 + s^2 = 1) (hr : ∀ u, 0 ≤ rest u)
    (hbase : ∀ u, u ≠ 0 →
      0 < rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i)))
    (hform : ∀ u, l u = 0 → ⟪u, A u⟫ =
      rest u + ∑ i, (Complex.normSq (y u i) + Complex.normSq (z u i) +
        pairForm c s (y u i) (z u i))) :
    ∀ u, l u = 0 → u ≠ 0 → 0 < ⟪u, A u⟫
```

</details>

## Round 13 declaration ledger — complete new-name inventory

All 243 new names with an individual permitted axiom record are listed once below; repeated copies in assemblies are not new nodes. Axioms are quoted from each cited exit-0 log. Category A requires an identical declaration body and its own record in a separately replayed reviewer file. Eight additional source-only supporting declarations are indexed after this ledger without proof markers. Source signatures retain explicit hypotheses; inherited section parameters remain as in the cited source. Dependencies are named blueprint inputs, not a complete kernel dependency extraction.

### Trial

R1 closes exact P1, independently replayed. R2 preserves that proof and adds the explicit norm, Rayleigh quotient and same-index cofinal path/trial handoff; neither gives detection.

<a id="bp-341"></a>
#### bp-341 — `AdalyFormal.Round13.Trial.Fine`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1266`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:139`: `'AdalyFormal.Round13.Trial.Fine' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1266`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:139`, exit `0`; record: `'AdalyFormal.Round13.Trial.Fine' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
abbrev Fine (q R : ℕ)
```

<a id="bp-342"></a>
#### bp-342 — `AdalyFormal.Round13.Trial.seven_le_side`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1268`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:140`: `'AdalyFormal.Round13.Trial.seven_le_side' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1268`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:140`, exit `0`; record: `'AdalyFormal.Round13.Trial.seven_le_side' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341).

```lean
theorem seven_le_side {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    7 ≤ Fine q R μ + 1
```

<a id="bp-343"></a>
#### bp-343 — `AdalyFormal.Round13.Trial.patchSite`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1274`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:141`: `'AdalyFormal.Round13.Trial.patchSite' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1274`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:141`, exit `0`; record: `'AdalyFormal.Round13.Trial.patchSite' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-342](#bp-342).

```lean
def patchSite {q : ℕ} (hq : 0 < q) (R : ℕ) (v : Fin 3 → Fin 7) :
    PeriodicLatticeSite (Fine q R)
```

<a id="bp-344"></a>
#### bp-344 — `AdalyFormal.Round13.Trial.patchSite_injective`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1278`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:142`: `'AdalyFormal.Round13.Trial.patchSite_injective' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1278`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:142`, exit `0`; record: `'AdalyFormal.Round13.Trial.patchSite_injective' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-343](#bp-343).

```lean
theorem patchSite_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (patchSite hq R)
```

<a id="bp-345"></a>
#### bp-345 — `AdalyFormal.Round13.Trial.castLE_add_one`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1288`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:143`: `'AdalyFormal.Round13.Trial.castLE_add_one' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1288`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:143`, exit `0`; record: `'AdalyFormal.Round13.Trial.castLE_add_one' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem castLE_add_one {n : ℕ} (hn : 7 ≤ n+1) (v : Fin 7) (hv : v.val < 6) :
    Fin.castLE hn (v + 1) = Fin.castLE hn v + (1 : Fin (n+1))
```

<a id="bp-346"></a>
#### bp-346 — `AdalyFormal.Round13.Trial.patchSite_shift`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1296`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:144`: `'AdalyFormal.Round13.Trial.patchSite_shift' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1296`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:144`, exit `0`; record: `'AdalyFormal.Round13.Trial.patchSite_shift' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-345](#bp-345).

```lean
theorem patchSite_shift {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    periodicLatticeShift (patchSite hq R v) μ =
      patchSite hq R (Function.update v μ (v μ + 1))
```

<a id="bp-347"></a>
#### bp-347 — `AdalyFormal.Round13.Trial.centerCoord`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1308`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:145`: `'AdalyFormal.Round13.Trial.centerCoord' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1308`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:145`, exit `0`; record: `'AdalyFormal.Round13.Trial.centerCoord' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def centerCoord : Fin 3 → Fin 7
```

<a id="bp-348"></a>
#### bp-348 — `AdalyFormal.Round13.Trial.patchSite_center`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1310`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:146`: `'AdalyFormal.Round13.Trial.patchSite_center' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1310`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:146`, exit `0`; record: `'AdalyFormal.Round13.Trial.patchSite_center' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-342](#bp-342); [bp-343](#bp-343); [bp-347](#bp-347).

```lean
theorem patchSite_center {q : ℕ} (hq : 0 < q) (R : ℕ) :
    patchSite hq R centerCoord = rightSite hq R
```

<a id="bp-349"></a>
#### bp-349 — `AdalyFormal.Round13.Trial.trialCoord`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1322`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:147`: `'AdalyFormal.Round13.Trial.trialCoord' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1322`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:147`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialCoord' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def trialCoord : Fin 6 → (Fin 3 → Fin 7)
```

<a id="bp-350"></a>
#### bp-350 — `AdalyFormal.Round13.Trial.trialDir`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1324`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:148`: `'AdalyFormal.Round13.Trial.trialDir' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1324`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:148`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialDir' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def trialDir : Fin 6 → Fin 3
```

<a id="bp-351"></a>
#### bp-351 — `AdalyFormal.Round13.Trial.trialBond`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1325`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:149`: `'AdalyFormal.Round13.Trial.trialBond' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1325`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:149`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialBond' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-343](#bp-343); [bp-349](#bp-349); [bp-350](#bp-350).

```lean
def trialBond {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) : Bond (Fine q R)
```

<a id="bp-352"></a>
#### bp-352 — `AdalyFormal.Round13.Trial.trialBond_injective`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1328`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:150`: `'AdalyFormal.Round13.Trial.trialBond_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1328`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:150`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialBond_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-344](#bp-344); [bp-349](#bp-349); [bp-350](#bp-350); [bp-351](#bp-351).

```lean
theorem trialBond_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (trialBond hq R)
```

<a id="bp-353"></a>
#### bp-353 — `AdalyFormal.Round13.Trial.charged`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1337`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:151`: `'AdalyFormal.Round13.Trial.charged' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1337`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:151`, exit `0`; record: `'AdalyFormal.Round13.Trial.charged' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def charged (z : ℂ) : SuTwo
```

<a id="bp-354"></a>
#### bp-354 — `AdalyFormal.Round13.Trial.charged_norm`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1344`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:152`: `'AdalyFormal.Round13.Trial.charged_norm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1344`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:152`, exit `0`; record: `'AdalyFormal.Round13.Trial.charged_norm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353).

```lean
theorem charged_norm (z : ℂ) : ‖charged z‖^2 = Complex.normSq z
```

<a id="bp-355"></a>
#### bp-355 — `AdalyFormal.Round13.Trial.trialAmplitude`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1350`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:153`: `'AdalyFormal.Round13.Trial.trialAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1350`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:153`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def trialAmplitude : Fin 6 → ℂ
```

<a id="bp-356"></a>
#### bp-356 — `AdalyFormal.Round13.Trial.trialField`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1353`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:154`: `'AdalyFormal.Round13.Trial.trialField' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1353`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:154`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-351](#bp-351); [bp-353](#bp-353); [bp-355](#bp-355).

```lean
def trialField {q : ℕ} (hq : 0 < q) (R : ℕ) : BondFnL2 (Fine q R)
```

<a id="bp-357"></a>
#### bp-357 — `AdalyFormal.Round13.Trial.trialField_apply`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1356`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:155`: `'AdalyFormal.Round13.Trial.trialField_apply' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1356`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:155`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_apply' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-351](#bp-351); [bp-353](#bp-353); [bp-355](#bp-355); [bp-356](#bp-356).

```lean
theorem trialField_apply {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R)) :
    trialField hq R e = ∑ i : Fin 6,
      if e = trialBond hq R i then charged (trialAmplitude i) else 0
```

<a id="bp-358"></a>
#### bp-358 — `AdalyFormal.Round13.Trial.trialField_at`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1361`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:156`: `'AdalyFormal.Round13.Trial.trialField_at' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1361`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:156`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_at' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-352](#bp-352); [bp-353](#bp-353); [bp-355](#bp-355); [bp-356](#bp-356); [bp-357](#bp-357).

```lean
theorem trialField_at {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialField hq R (trialBond hq R i) = charged (trialAmplitude i)
```

<a id="bp-359"></a>
#### bp-359 — `AdalyFormal.Round13.Trial.trialField_support`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1367`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:157`: `'AdalyFormal.Round13.Trial.trialField_support' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1367`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:157`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_support' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-351](#bp-351); [bp-356](#bp-356); [bp-357](#bp-357).

```lean
theorem trialField_support {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R))
    (he : trialField hq R e ≠ 0) : ∃ i : Fin 6, e = trialBond hq R i
```

<a id="bp-360"></a>
#### bp-360 — `AdalyFormal.Round13.Trial.trialField_norm`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1375`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:158`: `'AdalyFormal.Round13.Trial.trialField_norm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1375`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:158`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_norm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-351](#bp-351); [bp-352](#bp-352); [bp-354](#bp-354); [bp-355](#bp-355); [bp-356](#bp-356); [bp-358](#bp-358); [bp-359](#bp-359).

```lean
theorem trialField_norm {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialField hq R‖^2 = (21/16 : ℝ)
```

<a id="bp-361"></a>
#### bp-361 — `AdalyFormal.Round13.Trial.trial_sites`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1425`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:159`: `'AdalyFormal.Round13.Trial.trial_sites' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1425`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:159`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_sites' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-346](#bp-346); [bp-347](#bp-347); [bp-348](#bp-348); [bp-349](#bp-349); [bp-351](#bp-351).

```lean
theorem trial_sites {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (fun i : Fin 6 => (trialBond hq R i).1) =
      ![rightSite hq R, periodicLatticeShift (rightSite hq R) 1,
        periodicLatticeShiftBack (rightSite hq R) 1,
        periodicLatticeShift (rightSite hq R) 2,
        periodicLatticeShiftBack (rightSite hq R) 2, rightSite hq R]
```

<a id="bp-362"></a>
#### bp-362 — `AdalyFormal.Round13.Trial.trial_start_near`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1456`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:160`: `'AdalyFormal.Round13.Trial.trial_start_near' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1456`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:160`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_start_near' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-361](#bp-361).

```lean
theorem trial_start_near {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (rightSite hq R) (trialBond hq R i).1 ≤ 1
```

<a id="bp-363"></a>
#### bp-363 — `AdalyFormal.Round13.Trial.trial_start_zero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1472`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:161`: `'AdalyFormal.Round13.Trial.trial_start_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1472`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:161`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_start_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-342](#bp-342); [bp-343](#bp-343); [bp-349](#bp-349); [bp-351](#bp-351).

```lean
theorem trial_start_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    ((trialBond hq R i).1 0).val = 12*(R*q)+12*q-1
```

<a id="bp-364"></a>
#### bp-364 — `AdalyFormal.Round13.Trial.trial_touch`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1481`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:162`: `'AdalyFormal.Round13.Trial.trial_touch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1481`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:162`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_touch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-363](#bp-363).

```lean
theorem trial_touch {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialBond hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
```

<a id="bp-365"></a>
#### bp-365 — `AdalyFormal.Round13.Trial.trial_collar`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1488`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:163`: `'AdalyFormal.Round13.Trial.trial_collar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1488`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:163`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_collar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-363](#bp-363).

```lean
theorem trial_collar {q R : ℕ} (hq : 0 < q) (hR18 : 18 ≤ R) (i : Fin 6) :
    (trialBond hq R i).1 ∉ (dilTower q R).Om 1 ∧
      periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2 ∉
        (dilTower q R).Om 1
```

<a id="bp-366"></a>
#### bp-366 — `AdalyFormal.Round13.Trial.trial_levelZero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1504`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:164`: `'AdalyFormal.Round13.Trial.trial_levelZero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1504`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:164`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_levelZero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-364](#bp-364); [bp-365](#bp-365).

```lean
theorem trial_levelZero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (i : Fin 6) :
    trialBond hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0
```

<a id="bp-367"></a>
#### bp-367 — `AdalyFormal.Round13.Trial.trialField_mem`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1509`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:165`: `'AdalyFormal.Round13.Trial.trialField_mem' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1509`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:165`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_mem' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-359](#bp-359); [bp-364](#bp-364).

```lean
theorem trialField_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialField hq R ∈ bondSupp (geomOf 2 1 (dilTower q R))
```

<a id="bp-368"></a>
#### bp-368 — `AdalyFormal.Round13.Trial.trialVector`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1516`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:166`: `'AdalyFormal.Round13.Trial.trialVector' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1516`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:166`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialVector' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-367](#bp-367).

```lean
def trialVector {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R)))
```

<a id="bp-369"></a>
#### bp-369 — `AdalyFormal.Round13.Trial.trial_near_exterior`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1519`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:167`: `'AdalyFormal.Round13.Trial.trial_near_exterior' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1519`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:167`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_near_exterior' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-351](#bp-351); [bp-362](#bp-362).

```lean
theorem trial_near_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (periodicLatticeShift (rightSite hq R) 0) (trialBond hq R i).1 ≤ 2 ∧
    pdist (periodicLatticeShift (rightSite hq R) 0)
      (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2) ≤ 3
```

<a id="bp-370"></a>
#### bp-370 — `AdalyFormal.Round13.Trial.trialField_hsupp`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1534`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:168`: `'AdalyFormal.Round13.Trial.trialField_hsupp' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1534`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:168`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_hsupp' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-359](#bp-359); [bp-369](#bp-369).

```lean
theorem trialField_hsupp {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∀ e : Bond (Fine q R), trialField hq R e ≠ 0 →
      ∃ w : PeriodicLatticeSite (Fine q R), w ∉ (dilTower q R).Om 0 ∧ pdist e.1 w ≤ 2
```

<a id="bp-371"></a>
#### bp-371 — `AdalyFormal.Round13.Trial.trial_higher_rows_zero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1543`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:169`: `'AdalyFormal.Round13.Trial.trial_higher_rows_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1543`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:169`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_higher_rows_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-370](#bp-370).

```lean
theorem trial_higher_rows_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ 1)
    {b : Bond (Fine q R)} (hb : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) j) :
    QlinB (geomOf 2 1 (dilTower q R)) U j (trialField hq R) b = 0
```

<a id="bp-372"></a>
#### bp-372 — `AdalyFormal.Round13.Trial.trial_mass_upper`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1550`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:170`: `'AdalyFormal.Round13.Trial.trial_mass_upper' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1550`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:170`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_mass_upper' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-360](#bp-360); [bp-370](#bp-370).

```lean
theorem trial_mass_upper {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ ≤ (21/16 : ℝ)
```

<a id="bp-373"></a>
#### bp-373 — `AdalyFormal.Round13.Trial.trial_mass_eq`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1559`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:171`: `'AdalyFormal.Round13.Trial.trial_mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1559`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:171`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-351](#bp-351); [bp-352](#bp-352); [bp-354](#bp-354); [bp-355](#bp-355); [bp-356](#bp-356); [bp-358](#bp-358); [bp-366](#bp-366); [bp-372](#bp-372).

```lean
theorem trial_mass_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ = (21/16 : ℝ)
```

<a id="bp-374"></a>
#### bp-374 — `AdalyFormal.Round13.Trial.trial_T_zero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1574`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:172`: `'AdalyFormal.Round13.Trial.trial_T_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1574`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:172`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_T_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-369](#bp-369).

```lean
theorem trial_T_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) : Tfull (geomOf 2 1 (dilTower q R)) U (trialField hq R) = 0
```

<a id="bp-375"></a>
#### bp-375 — `AdalyFormal.Round13.Trial.trial_W_eq`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1584`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:173`: `'AdalyFormal.Round13.Trial.trial_W_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1584`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:173`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_W_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-369](#bp-369).

```lean
theorem trial_W_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) (a : ℝ) :
    Wop (geomOf 2 1 (dilTower q R)) U a (trialField hq R) = trialField hq R
```

<a id="bp-376"></a>
#### bp-376 — `AdalyFormal.Round13.Trial.stepCoord`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1627`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:174`: `'AdalyFormal.Round13.Trial.stepCoord' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1627`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:174`, exit `0`; record: `'AdalyFormal.Round13.Trial.stepCoord' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def stepCoord (v : Fin 3 → Fin 7) (μ : Fin 3)
```

<a id="bp-377"></a>
#### bp-377 — `AdalyFormal.Round13.Trial.backCoord`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1628`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:175`: `'AdalyFormal.Round13.Trial.backCoord' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1628`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:175`, exit `0`; record: `'AdalyFormal.Round13.Trial.backCoord' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def backCoord (v : Fin 3 → Fin 7) (μ : Fin 3)
```

<a id="bp-378"></a>
#### bp-378 — `AdalyFormal.Round13.Trial.patchSite_back`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1630`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:176`: `'AdalyFormal.Round13.Trial.patchSite_back' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1630`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:176`, exit `0`; record: `'AdalyFormal.Round13.Trial.patchSite_back' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-346](#bp-346); [bp-377](#bp-377).

```lean
theorem patchSite_back {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : 0 < (v μ).val) :
    periodicLatticeShiftBack (patchSite hq R v) μ = patchSite hq R (backCoord v μ)
```

<a id="bp-379"></a>
#### bp-379 — `AdalyFormal.Round13.Trial.d02`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1647`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:177`: `'AdalyFormal.Round13.Trial.d02' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1647`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:177`, exit `0`; record: `'AdalyFormal.Round13.Trial.d02' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def d02 : PeriodicPlaquetteDirections
```

<a id="bp-380"></a>
#### bp-380 — `AdalyFormal.Round13.Trial.d12`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1648`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:178`: `'AdalyFormal.Round13.Trial.d12' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1648`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:178`, exit `0`; record: `'AdalyFormal.Round13.Trial.d12' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def d12 : PeriodicPlaquetteDirections
```

<a id="bp-381"></a>
#### bp-381 — `AdalyFormal.Round13.Trial.trialPlaqPattern`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1650`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:179`: `'AdalyFormal.Round13.Trial.trialPlaqPattern' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1650`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:179`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialPlaqPattern' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-379](#bp-379); [bp-380](#bp-380).

```lean
def trialPlaqPattern : Fin 19 → ((Fin 3 → Fin 7) × PeriodicPlaquetteDirections)
```

<a id="bp-382"></a>
#### bp-382 — `AdalyFormal.Round13.Trial.trialPlaq`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1657`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:180`: `'AdalyFormal.Round13.Trial.trialPlaq' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1657`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:180`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialPlaq' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-343](#bp-343); [bp-381](#bp-381).

```lean
def trialPlaq {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) : PeriodicLatticePlaquette (Fine q R)
```

<a id="bp-383"></a>
#### bp-383 — `AdalyFormal.Round13.Trial.trialPlaqPattern_injective`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1660`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:181`: `'AdalyFormal.Round13.Trial.trialPlaqPattern_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1660`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:181`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialPlaqPattern_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-381](#bp-381).

```lean
theorem trialPlaqPattern_injective : Function.Injective trialPlaqPattern
```

<a id="bp-384"></a>
#### bp-384 — `AdalyFormal.Round13.Trial.trialPlaq_injective`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1662`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:182`: `'AdalyFormal.Round13.Trial.trialPlaq_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1662`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:182`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialPlaq_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-344](#bp-344); [bp-382](#bp-382); [bp-383](#bp-383).

```lean
theorem trialPlaq_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (trialPlaq hq R)
```

<a id="bp-385"></a>
#### bp-385 — `AdalyFormal.Round13.Trial.pattern_front`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1668`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:183`: `'AdalyFormal.Round13.Trial.pattern_front' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1668`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:183`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_front' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-381](#bp-381).

```lean
theorem pattern_front : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    (d.1.1 = trialDir i ∨ d.1.2 = trialDir i) →
      ∃ k : Fin 19, trialPlaqPattern k = (trialCoord i,d)
```

<a id="bp-386"></a>
#### bp-386 — `AdalyFormal.Round13.Trial.pattern_back1`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1672`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:184`: `'AdalyFormal.Round13.Trial.pattern_back1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1672`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:184`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_back1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-377](#bp-377); [bp-381](#bp-381).

```lean
theorem pattern_back1 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.1 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.2,d)
```

<a id="bp-387"></a>
#### bp-387 — `AdalyFormal.Round13.Trial.pattern_back2`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1676`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:185`: `'AdalyFormal.Round13.Trial.pattern_back2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1676`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:185`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_back2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-377](#bp-377); [bp-381](#bp-381).

```lean
theorem pattern_back2 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.2 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.1,d)
```

<a id="bp-388"></a>
#### bp-388 — `AdalyFormal.Round13.Trial.trialCoord_positive`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1680`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:186`: `'AdalyFormal.Round13.Trial.trialCoord_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1680`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:186`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialCoord_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349).

```lean
theorem trialCoord_positive (i : Fin 6) (μ : Fin 3) : 0 < (trialCoord i μ).val
```

<a id="bp-389"></a>
#### bp-389 — `AdalyFormal.Round13.Trial.front_mem`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1683`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:187`: `'AdalyFormal.Round13.Trial.front_mem' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1683`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:187`, exit `0`; record: `'AdalyFormal.Round13.Trial.front_mem' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-349](#bp-349); [bp-350](#bp-350); [bp-382](#bp-382); [bp-385](#bp-385).

```lean
theorem front_mem {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i ∨ d.1.2 = trialDir i) :
    (patchSite hq R (trialCoord i),d) ∈ Finset.univ.image (trialPlaq hq R)
```

<a id="bp-390"></a>
#### bp-390 — `AdalyFormal.Round13.Trial.back_mem1`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1689`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:188`: `'AdalyFormal.Round13.Trial.back_mem1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1689`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:188`, exit `0`; record: `'AdalyFormal.Round13.Trial.back_mem1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-349](#bp-349); [bp-350](#bp-350); [bp-378](#bp-378); [bp-382](#bp-382); [bp-386](#bp-386); [bp-388](#bp-388).

```lean
theorem back_mem1 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.2,d) ∈
      Finset.univ.image (trialPlaq hq R)
```

<a id="bp-391"></a>
#### bp-391 — `AdalyFormal.Round13.Trial.back_mem2`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1697`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:189`: `'AdalyFormal.Round13.Trial.back_mem2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1697`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:189`, exit `0`; record: `'AdalyFormal.Round13.Trial.back_mem2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-349](#bp-349); [bp-350](#bp-350); [bp-378](#bp-378); [bp-382](#bp-382); [bp-387](#bp-387); [bp-388](#bp-388).

```lean
theorem back_mem2 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.2 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.1,d) ∈
      Finset.univ.image (trialPlaq hq R)
```

<a id="bp-392"></a>
#### bp-392 — `AdalyFormal.Round13.Trial.trial_plaq_zero_off`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1707`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:190`: `'AdalyFormal.Round13.Trial.trial_plaq_zero_off' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1707`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:190`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_plaq_zero_off' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-343](#bp-343); [bp-349](#bp-349); [bp-351](#bp-351); [bp-356](#bp-356); [bp-359](#bp-359); [bp-382](#bp-382); [bp-389](#bp-389); [bp-390](#bp-390); [bp-391](#bp-391).

```lean
theorem trial_plaq_zero_off {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R))
    (p : PeriodicLatticePlaquette (Fine q R)) (hp : p ∉ Finset.univ.image (trialPlaq hq R)) :
    contrib U (WithLp.ofLp (trialField hq R)) p = 0
```

<a id="bp-393"></a>
#### bp-393 — `AdalyFormal.Round13.Trial.trial_delta_sum`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1747`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:191`: `'AdalyFormal.Round13.Trial.trial_delta_sum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1747`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:191`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_delta_sum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-341](#bp-341); [bp-356](#bp-356); [bp-382](#bp-382); [bp-384](#bp-384); [bp-392](#bp-392).

```lean
theorem trial_delta_sum {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R)) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ (trialField hq R)⟫ =
      ∑ i : Fin 19, contrib U (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)
```

<a id="bp-394"></a>
#### bp-394 — `AdalyFormal.Round13.Trial.quadForm`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1788`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:192`: `'AdalyFormal.Round13.Trial.quadForm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1788`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:192`, exit `0`; record: `'AdalyFormal.Round13.Trial.quadForm' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def quadForm (c s : ℝ) (x y z w : ℂ) : ℝ
```

<a id="bp-395"></a>
#### bp-395 — `AdalyFormal.Round13.Trial.frozen_four_form`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1793`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:193`: `'AdalyFormal.Round13.Trial.frozen_four_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1793`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:193`, exit `0`; record: `'AdalyFormal.Round13.Trial.frozen_four_form' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-394](#bp-394).

```lean
theorem frozen_four_form {L : PeriodicLatticeExtent} (U : Cfg L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z w : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = chargedMat w) :
    contrib U A p = quadForm c s x y z w
```

<a id="bp-396"></a>
#### bp-396 — `AdalyFormal.Round13.Trial.anchorCoord`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1812`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:194`: `'AdalyFormal.Round13.Trial.anchorCoord' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1812`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:194`, exit `0`; record: `'AdalyFormal.Round13.Trial.anchorCoord' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def anchorCoord : Fin 3 → Fin 7
```

<a id="bp-397"></a>
#### bp-397 — `AdalyFormal.Round13.Trial.star_anchor`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1814`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:195`: `'AdalyFormal.Round13.Trial.star_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1814`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:195`, exit `0`; record: `'AdalyFormal.Round13.Trial.star_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-346](#bp-346); [bp-347](#bp-347); [bp-348](#bp-348); [bp-396](#bp-396).

```lean
theorem star_anchor {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (rightSite hq R) 0 = patchSite hq R anchorCoord
```

<a id="bp-398"></a>
#### bp-398 — `AdalyFormal.Round13.Trial.localStar`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1821`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:196`: `'AdalyFormal.Round13.Trial.localStar' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1821`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:196`, exit `0`; record: `'AdalyFormal.Round13.Trial.localStar' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-376](#bp-376); [bp-396](#bp-396).

```lean
def localStar (v : Fin 3 → Fin 7) (μ : Fin 3) : Prop
```

<a id="bp-399"></a>
#### bp-399 — `AdalyFormal.Round13.Trial.rightStar_patch`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1824`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:197`: `'AdalyFormal.Round13.Trial.rightStar_patch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1824`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:197`, exit `0`; record: `'AdalyFormal.Round13.Trial.rightStar_patch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-344](#bp-344); [bp-346](#bp-346); [bp-376](#bp-376); [bp-397](#bp-397); [bp-398](#bp-398).

```lean
theorem rightStar_patch {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    rightStar hq R t (patchSite hq R v,μ) =
      if localStar v μ then uθ t else 1
```

<a id="bp-400"></a>
#### bp-400 — `AdalyFormal.Round13.Trial.localField`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1833`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:198`: `'AdalyFormal.Round13.Trial.localField' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1833`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:198`, exit `0`; record: `'AdalyFormal.Round13.Trial.localField' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-353](#bp-353); [bp-355](#bp-355).

```lean
def localField (v : Fin 3 → Fin 7) (μ : Fin 3) : SuTwo
```

<a id="bp-401"></a>
#### bp-401 — `AdalyFormal.Round13.Trial.trialField_patch`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1836`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:199`: `'AdalyFormal.Round13.Trial.trialField_patch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1836`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:199`, exit `0`; record: `'AdalyFormal.Round13.Trial.trialField_patch' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-344](#bp-344); [bp-351](#bp-351); [bp-356](#bp-356); [bp-357](#bp-357); [bp-400](#bp-400).

```lean
theorem trialField_patch {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) :
    trialField hq R (patchSite hq R v,μ) = localField v μ
```

<a id="bp-402"></a>
#### bp-402 — `AdalyFormal.Round13.Trial.charged_zero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1842`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:200`: `'AdalyFormal.Round13.Trial.charged_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1842`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:200`, exit `0`; record: `'AdalyFormal.Round13.Trial.charged_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353).

```lean
theorem charged_zero : charged 0 = 0
```

<a id="bp-403"></a>
#### bp-403 — `AdalyFormal.Round13.Trial.charged_neg`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1847`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:201`: `'AdalyFormal.Round13.Trial.charged_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1847`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:201`, exit `0`; record: `'AdalyFormal.Round13.Trial.charged_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353).

```lean
theorem charged_neg (z : ℂ) : -charged z = charged (-z)
```

<a id="bp-404"></a>
#### bp-404 — `AdalyFormal.Round13.Trial.isCurved`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1852`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:202`: `'AdalyFormal.Round13.Trial.isCurved' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1852`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:202`, exit `0`; record: `'AdalyFormal.Round13.Trial.isCurved' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def isCurved (i : Fin 19) : Bool
```

<a id="bp-405"></a>
#### bp-405 — `AdalyFormal.Round13.Trial.pattern_room`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1854`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:203`: `'AdalyFormal.Round13.Trial.pattern_room' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1854`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:203`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_room' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-381](#bp-381).

```lean
theorem pattern_room (i : Fin 19) (μ : Fin 3) : ((trialPlaqPattern i).1 μ).val < 5
```

<a id="bp-406"></a>
#### bp-406 — `AdalyFormal.Round13.Trial.pattern_base_flat`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1857`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:204`: `'AdalyFormal.Round13.Trial.pattern_base_flat' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1857`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:204`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_base_flat' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-381](#bp-381); [bp-398](#bp-398).

```lean
theorem pattern_base_flat (i : Fin 19) :
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1 ∧
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2
```

<a id="bp-407"></a>
#### bp-407 — `AdalyFormal.Round13.Trial.pattern_shift_links`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1864`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:205`: `'AdalyFormal.Round13.Trial.pattern_shift_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1864`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:205`, exit `0`; record: `'AdalyFormal.Round13.Trial.pattern_shift_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-376](#bp-376); [bp-381](#bp-381); [bp-398](#bp-398); [bp-404](#bp-404).

```lean
theorem pattern_shift_links (i : Fin 19) :
    (localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2 ↔ isCurved i = true) ∧
    ¬ localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1
```

<a id="bp-408"></a>
#### bp-408 — `AdalyFormal.Round13.Trial.trial_base_links`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1873`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:206`: `'AdalyFormal.Round13.Trial.trial_base_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1873`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:206`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_base_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-381](#bp-381); [bp-382](#bp-382); [bp-399](#bp-399); [bp-405](#bp-405); [bp-406](#bp-406).

```lean
theorem trial_base_links {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.1) = 1 ∧
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.2) = 1
```

<a id="bp-409"></a>
#### bp-409 — `AdalyFormal.Round13.Trial.trial_holonomy`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1883`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:207`: `'AdalyFormal.Round13.Trial.trial_holonomy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1883`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:207`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_holonomy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-343](#bp-343); [bp-346](#bp-346); [bp-376](#bp-376); [bp-381](#bp-381); [bp-382](#bp-382); [bp-399](#bp-399); [bp-404](#bp-404); [bp-405](#bp-405); [bp-407](#bp-407); [bp-408](#bp-408).

```lean
theorem trial_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    holonomyElem (rightStar hq R t) (trialPlaq hq R i) =
      if isCurved i then uθ t else 1
```

<a id="bp-410"></a>
#### bp-410 — `AdalyFormal.Round13.Trial.uhalf_coe`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1911`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:208`: `'AdalyFormal.Round13.Trial.uhalf_coe' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1911`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:208`, exit `0`; record: `'AdalyFormal.Round13.Trial.uhalf_coe' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem uhalf_coe : ((uθ (Real.pi/2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I,0;0,-Complex.I]
```

<a id="bp-411"></a>
#### bp-411 — `AdalyFormal.Round13.Trial.trial_hol_parts`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1917`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:209`: `'AdalyFormal.Round13.Trial.trial_hol_parts' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1917`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:209`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_hol_parts' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-382](#bp-382); [bp-404](#bp-404); [bp-409](#bp-409); [bp-410](#bp-410).

```lean
theorem trial_hol_parts {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    reHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = realHol (if isCurved i then 0 else 1) ∧
    imHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = imagHol (if isCurved i then 1 else 0)
```

<a id="bp-412"></a>
#### bp-412 — `AdalyFormal.Round13.Trial.charged_add`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1958`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:210`: `'AdalyFormal.Round13.Trial.charged_add' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1958`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:210`, exit `0`; record: `'AdalyFormal.Round13.Trial.charged_add' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353).

```lean
theorem charged_add (z w : ℂ) : charged (z+w) = charged z + charged w
```

<a id="bp-413"></a>
#### bp-413 — `AdalyFormal.Round13.Trial.chargedHom`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1963`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:211`: `'AdalyFormal.Round13.Trial.chargedHom' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1963`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:211`, exit `0`; record: `'AdalyFormal.Round13.Trial.chargedHom' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353); [bp-402](#bp-402); [bp-412](#bp-412).

```lean
def chargedHom : ℂ →+ SuTwo where
  toFun
```

<a id="bp-414"></a>
#### bp-414 — `AdalyFormal.Round13.Trial.localAmplitude`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1968`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:212`: `'AdalyFormal.Round13.Trial.localAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1968`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:212`, exit `0`; record: `'AdalyFormal.Round13.Trial.localAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-355](#bp-355).

```lean
def localAmplitude (v : Fin 3 → Fin 7) (μ : Fin 3) : ℂ
```

<a id="bp-415"></a>
#### bp-415 — `AdalyFormal.Round13.Trial.localField_amplitude`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1971`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:213`: `'AdalyFormal.Round13.Trial.localField_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1971`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:213`, exit `0`; record: `'AdalyFormal.Round13.Trial.localField_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-353](#bp-353); [bp-400](#bp-400); [bp-402](#bp-402); [bp-413](#bp-413); [bp-414](#bp-414).

```lean
theorem localField_amplitude (v : Fin 3 → Fin 7) (μ : Fin 3) :
    localField v μ = charged (localAmplitude v μ)
```

<a id="bp-416"></a>
#### bp-416 — `AdalyFormal.Round13.Trial.trial_edge_values`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1980`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:214`: `'AdalyFormal.Round13.Trial.trial_edge_values' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1980`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:214`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_edge_values' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-346](#bp-346); [bp-353](#bp-353); [bp-356](#bp-356); [bp-376](#bp-376); [bp-381](#bp-381); [bp-382](#bp-382); [bp-401](#bp-401); [bp-405](#bp-405); [bp-414](#bp-414); [bp-415](#bp-415).

```lean
theorem trial_edge_values {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    let v
```

<a id="bp-417"></a>
#### bp-417 — `AdalyFormal.Round13.Trial.trial_atom_values`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:1995`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:215`: `'AdalyFormal.Round13.Trial.trial_atom_values' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:1995`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:215`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_atom_values' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-376](#bp-376); [bp-381](#bp-381); [bp-382](#bp-382); [bp-403](#bp-403); [bp-408](#bp-408); [bp-414](#bp-414); [bp-416](#bp-416).

```lean
theorem trial_atom_values {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    let v
```

<a id="bp-418"></a>
#### bp-418 — `AdalyFormal.Round13.Trial.localQuad`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2033`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:216`: `'AdalyFormal.Round13.Trial.localQuad' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2033`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:216`, exit `0`; record: `'AdalyFormal.Round13.Trial.localQuad' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-376](#bp-376); [bp-381](#bp-381); [bp-394](#bp-394); [bp-404](#bp-404); [bp-414](#bp-414).

```lean
def localQuad (i : Fin 19) : ℝ
```

<a id="bp-419"></a>
#### bp-419 — `AdalyFormal.Round13.Trial.trial_contrib_quad`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2041`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:217`: `'AdalyFormal.Round13.Trial.trial_contrib_quad' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2041`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:217`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_contrib_quad' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-382](#bp-382); [bp-395](#bp-395); [bp-411](#bp-411); [bp-417](#bp-417); [bp-418](#bp-418).

```lean
theorem trial_contrib_quad {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) =
      localQuad i
```

<a id="bp-420"></a>
#### bp-420 — `AdalyFormal.Round13.Trial.plaqNumerator`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2048`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:218`: `'AdalyFormal.Round13.Trial.plaqNumerator' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2048`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:218`, exit `0`; record: `'AdalyFormal.Round13.Trial.plaqNumerator' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def plaqNumerator : Fin 19 → ℝ
```

<a id="bp-421"></a>
#### bp-421 — `AdalyFormal.Round13.Trial.edgePattern`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2050`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:219`: `'AdalyFormal.Round13.Trial.edgePattern' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2050`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:219`, exit `0`; record: `'AdalyFormal.Round13.Trial.edgePattern' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** [bp-376](#bp-376); [bp-381](#bp-381).

```lean
def edgePattern (i : Fin 19) : Fin 4 → ((Fin 3 → Fin 7) × Fin 3)
```

<a id="bp-422"></a>
#### bp-422 — `AdalyFormal.Round13.Trial.edgeIndex`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2057`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:220`: `'AdalyFormal.Round13.Trial.edgeIndex' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2057`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:220`, exit `0`; record: `'AdalyFormal.Round13.Trial.edgeIndex' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def edgeIndex : Fin 19 → Fin 4 → Option (Fin 6)
```

<a id="bp-423"></a>
#### bp-423 — `AdalyFormal.Round13.Trial.edgeIndex_spec`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2068`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:221`: `'AdalyFormal.Round13.Trial.edgeIndex_spec' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2068`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:221`, exit `0`; record: `'AdalyFormal.Round13.Trial.edgeIndex_spec' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-349](#bp-349); [bp-350](#bp-350); [bp-421](#bp-421); [bp-422](#bp-422).

```lean
theorem edgeIndex_spec : ∀ (i : Fin 19) (k : Fin 4) (j : Fin 6),
    ((edgePattern i k).1 = trialCoord j ∧ (edgePattern i k).2 = trialDir j) ↔
      edgeIndex i k = some j
```

<a id="bp-424"></a>
#### bp-424 — `AdalyFormal.Round13.Trial.localAmplitude_edge`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2072`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:222`: `'AdalyFormal.Round13.Trial.localAmplitude_edge' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2072`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:222`, exit `0`; record: `'AdalyFormal.Round13.Trial.localAmplitude_edge' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-355](#bp-355); [bp-414](#bp-414); [bp-421](#bp-421); [bp-422](#bp-422); [bp-423](#bp-423).

```lean
theorem localAmplitude_edge (i : Fin 19) (k : Fin 4) :
    localAmplitude (edgePattern i k).1 (edgePattern i k).2 =
      (edgeIndex i k).elim 0 trialAmplitude
```

<a id="bp-425"></a>
#### bp-425 — `AdalyFormal.Round13.Trial.localQuad_value`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2079`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:223`: `'AdalyFormal.Round13.Trial.localQuad_value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2079`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:223`, exit `0`; record: `'AdalyFormal.Round13.Trial.localQuad_value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-394](#bp-394); [bp-404](#bp-404); [bp-414](#bp-414); [bp-418](#bp-418); [bp-420](#bp-420); [bp-421](#bp-421); [bp-424](#bp-424).

```lean
theorem localQuad_value (i : Fin 19) : localQuad i = plaqNumerator i / 16
```

<a id="bp-426"></a>
#### bp-426 — `AdalyFormal.Round13.Trial.trial_delta_value`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2127`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:224`: `'AdalyFormal.Round13.Trial.trial_delta_value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2127`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:224`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_delta_value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-393](#bp-393); [bp-419](#bp-419); [bp-420](#bp-420); [bp-425](#bp-425).

```lean
theorem trial_delta_value {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (rightStar hq R (Real.pi/2)) Set.univ (trialField hq R)⟫ = (-25/16 : ℝ)
```

<a id="bp-427"></a>
#### bp-427 — `AdalyFormal.Round13.Trial.trial_curved_energy`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2135`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:225`: `'AdalyFormal.Round13.Trial.trial_curved_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2135`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:225`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_curved_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-382](#bp-382); [bp-404](#bp-404); [bp-419](#bp-419); [bp-420](#bp-420); [bp-425](#bp-425).

```lean
theorem trial_curved_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)
      else 0) = (-5/2 : ℝ)
```

<a id="bp-428"></a>
#### bp-428 — `AdalyFormal.Round13.Trial.trial_flat_energy`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2143`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:226`: `'AdalyFormal.Round13.Trial.trial_flat_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2143`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:226`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_flat_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-382](#bp-382); [bp-404](#bp-404); [bp-419](#bp-419); [bp-420](#bp-420); [bp-425](#bp-425).

```lean
theorem trial_flat_energy {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (∑ i : Fin 19, if isCurved i then 0 else
      contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i)) =
        (15/16 : ℝ)
```

<a id="bp-429"></a>
#### bp-429 — `AdalyFormal.Round13.Trial.trial_carrier_energy`

Exact actual six-bond carrier energy is \(-1/4\) at half pi, for every positive q and even R at least 18. This is the complete frozen periodic operator, not a surrogate.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2151`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:227`: `'AdalyFormal.Round13.Trial.trial_carrier_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2151`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:227`, exit `0`; record: `'AdalyFormal.Round13.Trial.trial_carrier_energy' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-356](#bp-356); [bp-368](#bp-368); [bp-373](#bp-373); [bp-374](#bp-374); [bp-375](#bp-375); [bp-426](#bp-426).

```lean
theorem trial_carrier_energy {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R, vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ)
```

<a id="bp-430"></a>
#### bp-430 — `AdalyFormal.Round13.Trial.rightStar_negative_halfpi`

P1, unconditionally in the exact round-12 GAPS form. The only assumptions are positive q, even R and R at least 18.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2180`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:228`: `'AdalyFormal.Round13.Trial.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2180`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:228`, exit `0`; record: `'AdalyFormal.Round13.Trial.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-368](#bp-368); [bp-429](#bp-429).

```lean
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

<a id="bp-431"></a>
#### bp-431 — `AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi`

P1 with the original nested dyadic scale and even-radius quantifiers; no curvature cap is moved.

- **Source:** `AHP/round13/shared/trial/R1_Trial.lean:2187`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R1_Trial.lean.log:229`: `'AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r1/Trial.verify.lean:2187`, identical declaration body; `AHP/round13/trial/r1/Trial.verify.lean.log:229`, exit `0`; record: `'AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-430](#bp-430).

```lean
theorem cofinal_rightStar_negative_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ w : TwistSpace (2^j) R,
        ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0
```

<a id="bp-432"></a>
#### bp-432 — `AdalyFormal.Round13.Trial.R2.trialVector_norm_sq`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2315`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:240`: `'AdalyFormal.Round13.Trial.R2.trialVector_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2315`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:240`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.trialVector_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-360](#bp-360); [bp-368](#bp-368).

```lean
theorem trialVector_norm_sq {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialVector hq R‖^2 = (21/16 : ℝ)
```

<a id="bp-433"></a>
#### bp-433 — `AdalyFormal.Round13.Trial.R2.trialVector_ne_zero`

Supporting periodic six-bond trial identity or geometry statement, with the exact parameters displayed below.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2319`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:241`: `'AdalyFormal.Round13.Trial.R2.trialVector_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2319`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:241`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.trialVector_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-368](#bp-368); [bp-432](#bp-432).

```lean
theorem trialVector_ne_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialVector hq R ≠ 0
```

<a id="bp-434"></a>
#### bp-434 — `AdalyFormal.Round13.Trial.R2.trial_rayleigh`

The explicit trial has Rayleigh quotient \(-4/21\). This is not claimed to be a crossing eigenvalue.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2327`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:242`: `'AdalyFormal.Round13.Trial.R2.trial_rayleigh' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2327`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:242`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.trial_rayleigh' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-368](#bp-368); [bp-429](#bp-429); [bp-432](#bp-432).

```lean
theorem trial_rayleigh {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R,
      vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ /
        ‖trialVector hq R‖^2 = (-4/21 : ℝ)
```

<a id="bp-435"></a>
#### bp-435 — `AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi`

Exact P1, reusing the independently accepted R1 physical trial without extra hypotheses.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2335`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:243`: `'AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2335`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:243`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-430](#bp-430).

```lean
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

<a id="bp-436"></a>
#### bp-436 — `AdalyFormal.Round13.Trial.R2.rightStar_physical_halfpi`

Path validity, pi negativity and explicit half-pi trial facts hold together at any admissible indices selected downstream.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2343`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:244`: `'AdalyFormal.Round13.Trial.R2.rightStar_physical_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2343`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:244`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.rightStar_physical_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-368](#bp-368); [bp-429](#bp-429); [bp-432](#bp-432); [bp-433](#bp-433).

```lean
theorem rightStar_physical_halfpi {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    AdalyFormal.D1Literal.ContFam (rightStar hq R) ∧
    AnFam (rightStar hq R) ∧ rightStar hq R 0 = (fun _ => 1) ∧
    (∃ w : TwistSpace q R, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0) ∧
    trialVector hq R ≠ 0 ∧ ‖trialVector hq R‖^2 = (21/16 : ℝ) ∧
    ⟪trialVector hq R,
      vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ)
```

<a id="bp-437"></a>
#### bp-437 — `AdalyFormal.Round13.Trial.R2.cofinal_rightStar_paths_halfpi`

All path clauses and the exact half-pi trial occur at the same nested cofinal indices. No independent subsequences are intersected.

- **Source:** `AHP/round13/shared/trial/R2_Trial.lean:2357`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/trial/R2_Trial.lean.log:245`: `'AdalyFormal.Round13.Trial.R2.cofinal_rightStar_paths_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/trial/r2/Trial.verify.lean:2357`, identical declaration body; `AHP/round13/trial/r2/Trial.verify.lean.log:245`, exit `0`; record: `'AdalyFormal.Round13.Trial.R2.cofinal_rightStar_paths_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-368](#bp-368); [bp-436](#bp-436).

```lean
theorem cofinal_rightStar_paths_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
        V = rightStar (by positivity) R ∧
        AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
        (∃ z : TwistSpace (2^j) R, ⟪z, vacA (2^j) R V 1 Real.pi z⟫ < 0) ∧
        ∃ w : TwistSpace (2^j) R,
          w = trialVector (by positivity) R ∧ w ≠ 0 ∧ ‖w‖^2 = (21/16 : ℝ) ∧
          ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ = (-1/4 : ℝ) ∧
          ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ < 0
```

### Positivity

R1 supplies eight-leaf geometry, conditional mass-relative absorption and unconditional localized positivity. R2 closes the complete omitted-sum geometry and exact P2. The independent P2 replay also rechecks the identical printed R1 declarations credited A below.

<a id="bp-438"></a>
#### bp-438 — `AdalyFormal.Round13.Positivity.Leaves.leaf_code`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:816`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:41`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_code' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1783`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:135`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_code' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem leaf_code {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    code (leaf hq R i) =
      ![(0,1,0),(0,8*q-1,0),(0,0,1),(0,0,8*q-1),
        (1,0,0),(1,8*q-1,0),(2,0,0),(2,0,8*q-1)] i
```

<a id="bp-439"></a>
#### bp-439 — `AdalyFormal.Round13.Positivity.Leaves.leaf_injective`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:829`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:42`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1796`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:136`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-438](#bp-438).

```lean
theorem leaf_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (leaf hq R)
```

<a id="bp-440"></a>
#### bp-440 — `AdalyFormal.Round13.Positivity.Leaves.leaf_zero_coord`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:839`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:43`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_zero_coord' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1806`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:137`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_zero_coord' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem leaf_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    (((leaf hq R i).1) 0).val = 12*(R*q)+12*q-1
```

<a id="bp-441"></a>
#### bp-441 — `AdalyFormal.Round13.Positivity.Leaves.leaf_end_zero_coord`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:844`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:44`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_end_zero_coord' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1811`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:138`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_end_zero_coord' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-440](#bp-440).

```lean
theorem leaf_end_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    ((periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2) 0).val =
      if i.val < 4 then 12*(R*q)+12*q else 12*(R*q)+12*q-1
```

<a id="bp-442"></a>
#### bp-442 — `AdalyFormal.Round13.Positivity.Leaves.leaf_collar`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:853`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:45`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_collar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1820`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:139`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_collar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-440](#bp-440); [bp-441](#bp-441).

```lean
theorem leaf_collar {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (i : Fin 8) :
    (leaf hq R i).1 ∉ (dilTower q R).Om 1 ∧
    periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2 ∉ (dilTower q R).Om 1
```

<a id="bp-443"></a>
#### bp-443 — `AdalyFormal.Round13.Positivity.Leaves.leaf_touching`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:866`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:46`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_touching' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1833`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:140`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_touching' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-440](#bp-440).

```lean
theorem leaf_touching {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    leaf hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
```

<a id="bp-444"></a>
#### bp-444 — `AdalyFormal.Round13.Positivity.Leaves.leaf_level_zero`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:874`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:47`: `'AdalyFormal.Round13.Positivity.Leaves.leaf_level_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1841`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:141`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leaf_level_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-442](#bp-442); [bp-443](#bp-443).

```lean
theorem leaf_level_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (i : Fin 8) : leaf hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0
```

<a id="bp-445"></a>
#### bp-445 — `AdalyFormal.Round13.Positivity.Leaves.leafSet_card`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:883`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:48`: `'AdalyFormal.Round13.Positivity.Leaves.leafSet_card' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1850`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:142`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.leafSet_card' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-439](#bp-439).

```lean
theorem leafSet_card {q : ℕ} (hq : 0 < q) (R : ℕ) : (leafSet hq R).card = 8
```

<a id="bp-446"></a>
#### bp-446 — `AdalyFormal.Round13.Positivity.Leaves.eight_leaf_mass`

The true physical mass dominates the norms of eight distinct actual level-zero leaves, each paid once.

- **Source:** `AHP/round13/shared/positivity/R1_EightLeaves.lean:890`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_EightLeaves.lean.log:49`: `'AdalyFormal.Round13.Positivity.Leaves.eight_leaf_mass' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1857`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:143`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Leaves.eight_leaf_mass' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-439](#bp-439); [bp-444](#bp-444).

```lean
theorem eight_leaf_mass {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (U : Cfg (scaleUp 2 1 (dilLu q R)))
    (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i : Fin 8, ‖A (leaf hq R i)‖^2) ≤
      ⟪A,MassFull (geomOf 2 1 (dilTower q R)) 1
        (bondSectorOf (geomOf 2 1 (dilTower q R)) U) A⟫
```

<a id="bp-447"></a>
#### bp-447 — `AdalyFormal.Round13.Positivity.Local.rightStar_local_data_flat`

All actual localized data at the right star equal their flat values at every angle.

- **Source:** `AHP/round13/shared/positivity/R1_LocalPositive.lean:1423`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_LocalPositive.lean.log:19`: `'AdalyFormal.Round13.Positivity.Local.rightStar_local_data_flat' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3298`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:184`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Local.rightStar_local_data_flat' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem rightStar_local_data_flat {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (a t : ℝ) :
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) a (dilLam q R)) =
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) a (dilLam q R))
```

<a id="bp-448"></a>
#### bp-448 — `AdalyFormal.Round13.Positivity.Local.rightStar_local_positive`

Unconditional strict positivity of the genuine localized carrier, at every angle. This alone does not assert full all-plaquette positivity.

- **Source:** `AHP/round13/shared/positivity/R1_LocalPositive.lean:1443`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_LocalPositive.lean.log:22`: `'AdalyFormal.Round13.Positivity.Local.rightStar_local_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3318`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:187`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Local.rightStar_local_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-091](#bp-091); [bp-447](#bp-447).

```lean
theorem rightStar_local_positive {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R))).Ginv x⟫
```

<a id="bp-449"></a>
#### bp-449 — `AdalyFormal.Round13.Positivity.Local.cofinal_rightStar_local_positive`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_LocalPositive.lean:1451`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_LocalPositive.lean.log:25`: `'AdalyFormal.Round13.Positivity.Local.cofinal_rightStar_local_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3326`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:190`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Local.cofinal_rightStar_local_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-448](#bp-448).

```lean
theorem cofinal_rightStar_local_positive :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∀ t : ℝ, ∀ x : ↥(bondSupp (geomOf 2 1 (dilTower (2^j) R))), x ≠ 0 →
        0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu (2^j) R) (by norm_num)
          (dilTower (2^j) R) (rightStar (by positivity) R t) 1
          (dilLam (2^j) R))).Ginv x⟫
```

<a id="bp-450"></a>
#### bp-450 — `AdalyFormal.Round13.Positivity.delta_form_sum_set`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:693`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:65`: `'AdalyFormal.Round13.Positivity.delta_form_sum_set' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:693`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:65`, exit `0`; record: `'AdalyFormal.Round13.Positivity.delta_form_sum_set' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem delta_form_sum_set (U : Cfg L) (S : Set (PeriodicLatticePlaquette L))
    (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U S A⟫ = ∑ p, if p ∈ S then plaqEnergy U A p else 0
```

<a id="bp-451"></a>
#### bp-451 — `AdalyFormal.Round13.Positivity.plaqEnergy_nonneg`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:721`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:66`: `'AdalyFormal.Round13.Positivity.plaqEnergy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:721`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:66`, exit `0`; record: `'AdalyFormal.Round13.Positivity.plaqEnergy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem plaqEnergy_nonneg (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L)
    (hr : reHolonomy U p = 1) (hi : imHolonomy U p = 0) :
    0 ≤ plaqEnergy U A p
```

<a id="bp-452"></a>
#### bp-452 — `AdalyFormal.Round13.Positivity.carrier_form_split`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:736`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:67`: `'AdalyFormal.Round13.Positivity.carrier_form_split' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:736`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:67`, exit `0`; record: `'AdalyFormal.Round13.Positivity.carrier_form_split' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-450](#bp-450).

```lean
theorem carrier_form_split (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selAll selAll P).Ginv x⟫ =
      ⟪x, (dataS selIn selIn P).Ginv x⟫ + omittedEnergy P x
```

<a id="bp-453"></a>
#### bp-453 — `AdalyFormal.Round13.Positivity.localized_Dpi_nonneg`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:758`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:68`: `'AdalyFormal.Round13.Positivity.localized_Dpi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:758`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:68`, exit `0`; record: `'AdalyFormal.Round13.Positivity.localized_Dpi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-450](#bp-450); [bp-451](#bp-451).

```lean
theorem localized_Dpi_nonneg (P : IngrBParams) (x : ↥(bondSupp P.G))
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0) :
    0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫
```

<a id="bp-454"></a>
#### bp-454 — `AdalyFormal.Round13.Positivity.carrier_ge_scaled_local`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:774`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:69`: `'AdalyFormal.Round13.Positivity.carrier_ge_scaled_local' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:774`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:69`, exit `0`; record: `'AdalyFormal.Round13.Positivity.carrier_ge_scaled_local' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-452](#bp-452).

```lean
theorem carrier_ge_scaled_local (P : IngrBParams) (x : ↥(bondSupp P.G))
    (c leaves : ℝ) (hc : c ≤ 1)
    (hd : 0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫)
    (hl : leaves ≤ ⟪x, (dataS selIn selIn P).Mass x⟫)
    (ho : -(1-c)*leaves ≤ omittedEnergy P x) :
    c * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, (dataS selAll selAll P).Ginv x⟫
```

<a id="bp-455"></a>
#### bp-455 — `AdalyFormal.Round13.Positivity.carrier_ge_scaled_local_leaves`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:790`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:70`: `'AdalyFormal.Round13.Positivity.carrier_ge_scaled_local_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:790`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:70`, exit `0`; record: `'AdalyFormal.Round13.Positivity.carrier_ge_scaled_local_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-453](#bp-453); [bp-454](#bp-454).

```lean
theorem carrier_ge_scaled_local_leaves (P : IngrBParams) (ha : P.a = 1)
    (x : ↥(bondSupp P.G)) (c : ℝ) (hc : c ≤ 1)
    (leaves : Finset (Bond P.Lf)) (hl : ∀ e ∈ leaves, e ∈ bondsLam P.G 0)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (ho : -(1-c)*(∑ e ∈ leaves, ‖(iE P.G x) e‖^2) ≤ omittedEnergy P x) :
    c * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, (dataS selAll selAll P).Ginv x⟫
```

<a id="bp-456"></a>
#### bp-456 — `AdalyFormal.Round13.Positivity.carrier_positive_of_absorption`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:807`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:73`: `'AdalyFormal.Round13.Positivity.carrier_positive_of_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:807`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:73`, exit `0`; record: `'AdalyFormal.Round13.Positivity.carrier_positive_of_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-454](#bp-454).

```lean
theorem carrier_positive_of_absorption (P : IngrBParams) (x : ↥(bondSupp P.G))
    (c leaves : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hd : 0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫)
    (hl : leaves ≤ ⟪x, (dataS selIn selIn P).Mass x⟫)
    (ho : -(1-c)*leaves ≤ omittedEnergy P x)
    (hp : 0 < ⟪x, (dataS selIn selIn P).Ginv x⟫) :
    0 < ⟪x, (dataS selAll selAll P).Ginv x⟫
```

<a id="bp-457"></a>
#### bp-457 — `AdalyFormal.Round13.Positivity.full_pair_loss_bound`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:818`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:76`: `'AdalyFormal.Round13.Positivity.full_pair_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:818`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:76`, exit `0`; record: `'AdalyFormal.Round13.Positivity.full_pair_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem full_pair_loss_bound (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤
      pairForm c s y z + c*(h+k+l)^2
```

<a id="bp-458"></a>
#### bp-458 — `AdalyFormal.Round13.Positivity.full_star_loss_bound`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:827`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:77`: `'AdalyFormal.Round13.Positivity.full_star_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:827`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:77`, exit `0`; record: `'AdalyFormal.Round13.Positivity.full_star_loss_bound' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-457](#bp-457).

```lean
theorem full_star_loss_bound {ι : Type*} [Fintype ι]
    (c s : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (h k l : ι → ℝ) (y z : ι → ℂ) :
    -(1-c)*(∑ i, (Complex.normSq (y i)+(k i)^2+(Complex.normSq (z i)+(l i)^2))) ≤
      ∑ i, (pairForm c s (y i) (z i)+c*(h i+k i+l i)^2)
```

<a id="bp-459"></a>
#### bp-459 — `AdalyFormal.Round13.Positivity.omitted_loss_of_arm_decomposition`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:836`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:78`: `'AdalyFormal.Round13.Positivity.omitted_loss_of_arm_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:836`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:78`, exit `0`; record: `'AdalyFormal.Round13.Positivity.omitted_loss_of_arm_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-458](#bp-458).

```lean
theorem omitted_loss_of_arm_decomposition {ι : Type*} [Fintype ι]
    (P : IngrBParams) (x : ↥(bondSupp P.G)) (c s rest leaves : ℝ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) (hr : 0 ≤ rest)
    (h k l : ι → ℝ) (y z : ι → ℂ)
    (hm : leaves = ∑ i, (Complex.normSq (y i)+(k i)^2+(Complex.normSq (z i)+(l i)^2)))
    (he : omittedEnergy P x = rest +
      ∑ i, (pairForm c s (y i) (z i)+c*(h i+k i+l i)^2)) :
    -(1-c)*leaves ≤ omittedEnergy P x
```

<a id="bp-460"></a>
#### bp-460 — `AdalyFormal.Round13.Positivity.cos_prefix_loss`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:849`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:81`: `'AdalyFormal.Round13.Positivity.cos_prefix_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:849`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:81`, exit `0`; record: `'AdalyFormal.Round13.Positivity.cos_prefix_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem cos_prefix_loss (T t : ℝ) (hT0 : 0 ≤ T) (hT : T < Real.pi/2)
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    0 < Real.cos T ∧ Real.cos T ≤ Real.cos t ∧
      0 ≤ 1-Real.cos t ∧ 1-Real.cos t ≤ 1-Real.cos T ∧ 1-Real.cos T < 1
```

<a id="bp-461"></a>
#### bp-461 — `AdalyFormal.Round13.Positivity.zero_central_arm_negative`

The bare central-charged-zero local arm can be negative. This obstructs a shortcut, not P2.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:860`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:82`: `'AdalyFormal.Round13.Positivity.zero_central_arm_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:860`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:82`, exit `0`; record: `'AdalyFormal.Round13.Positivity.zero_central_arm_negative' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem zero_central_arm_negative : tripleForm 0 1 0 1 (-Complex.I) = -2
```

<a id="bp-462"></a>
#### bp-462 — `AdalyFormal.Round13.Positivity.halfpi_no_strict_mass_fraction`

A strict leaf-mass fraction below one cannot pay every half-pi local pair. No strict endpoint positivity is inferred.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:865`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:83`: `'AdalyFormal.Round13.Positivity.halfpi_no_strict_mass_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:865`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:83`, exit `0`; record: `'AdalyFormal.Round13.Positivity.halfpi_no_strict_mass_fraction' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem halfpi_no_strict_mass_fraction (rho : ℝ) (hrho : rho < 1) :
    ¬ (∀ y z : ℂ, -rho*(Complex.normSq y+Complex.normSq z) ≤ pairForm 0 1 y z)
```

<a id="bp-463"></a>
#### bp-463 — `AdalyFormal.Round13.Positivity.plaqEnergy_congr_field`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:907`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:86`: `'AdalyFormal.Round13.Positivity.plaqEnergy_congr_field' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:907`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:86`, exit `0`; record: `'AdalyFormal.Round13.Positivity.plaqEnergy_congr_field' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem plaqEnergy_congr_field (U : Cfg L) (A B : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = B e) :
    plaqEnergy U A p = plaqEnergy U B p
```

<a id="bp-464"></a>
#### bp-464 — `AdalyFormal.Round13.Positivity.omittedEnergy_eq_raw`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:934`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:87`: `'AdalyFormal.Round13.Positivity.omittedEnergy_eq_raw' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:934`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:87`, exit `0`; record: `'AdalyFormal.Round13.Positivity.omittedEnergy_eq_raw' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-203](#bp-203); [bp-463](#bp-463).

```lean
theorem omittedEnergy_eq_raw (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) :
    omittedEnergy P x = ∑ p, if p ∈ plaqIn P.G.Om0 then 0 else
      plaqEnergy P.U (iE P.G x) p
```

<a id="bp-465"></a>
#### bp-465 — `AdalyFormal.Round13.Positivity.localized_positive_of_unit`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:950`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:88`: `'AdalyFormal.Round13.Positivity.localized_positive_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:950`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:88`, exit `0`; record: `'AdalyFormal.Round13.Positivity.localized_positive_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-453](#bp-453).

```lean
theorem localized_positive_of_unit (P : IngrBParams) (ha : 0 ≤ P.a)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (hu : IsUnit (dataS selIn selIn P).Ginv)
    (x : ↥(bondSupp P.G)) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn P).Ginv x⟫
```

<a id="bp-466"></a>
#### bp-466 — `AdalyFormal.Round13.Positivity.physical_positive_of_leaf_loss`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:973`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:89`: `'AdalyFormal.Round13.Positivity.physical_positive_of_leaf_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:973`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:89`, exit `0`; record: `'AdalyFormal.Round13.Positivity.physical_positive_of_leaf_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-455](#bp-455); [bp-465](#bp-465).

```lean
theorem physical_positive_of_leaf_loss (P : IngrBParams) (ha : P.a = 1)
    (x : ↥(bondSupp P.G)) (hx : x ≠ 0) (t : ℝ)
    (ht0 : 0 ≤ t) (ht : t < Real.pi/2)
    (leaves : Finset (Bond P.Lf)) (hl : ∀ e ∈ leaves, e ∈ bondsLam P.G 0)
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0)
    (hu : IsUnit (dataS selIn selIn P).Ginv)
    (ho : -(1-Real.cos t)*(∑ e ∈ leaves, ‖(iE P.G x) e‖^2) ≤ omittedEnergy P x) :
    0 < ⟪x, (dataS selAll selAll P).Ginv x⟫
```

<a id="bp-467"></a>
#### bp-467 — `AdalyFormal.Round13.Positivity.frozen_right_zero_first_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:989`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:92`: `'AdalyFormal.Round13.Positivity.frozen_right_zero_first_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:989`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:92`, exit `0`; record: `'AdalyFormal.Round13.Positivity.frozen_right_zero_first_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-457](#bp-457).

```lean
theorem frozen_right_zero_first_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat h 0)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat k y)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat l z)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p
```

<a id="bp-468"></a>
#### bp-468 — `AdalyFormal.Round13.Positivity.frozen_right_zero_third_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:1004`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:95`: `'AdalyFormal.Round13.Positivity.frozen_right_zero_third_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1004`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:95`, exit `0`; record: `'AdalyFormal.Round13.Positivity.frozen_right_zero_third_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-457](#bp-457).

```lean
theorem frozen_right_zero_third_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat k y)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat l z)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat h 0)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p
```

<a id="bp-469"></a>
#### bp-469 — `AdalyFormal.Round13.Positivity.omitted_loss_of_injective_arms`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean:1021`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log:98`: `'AdalyFormal.Round13.Positivity.omitted_loss_of_injective_arms' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1021`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:98`, exit `0`; record: `'AdalyFormal.Round13.Positivity.omitted_loss_of_injective_arms' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-464](#bp-464).

```lean
theorem omitted_loss_of_injective_arms {ι : Type*} [Fintype ι]
    (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) (c : ℝ)
    (arm : ι → PeriodicLatticePlaquette P.Lf) (ha : Function.Injective arm)
    (hout : ∀ i, arm i ∉ plaqIn P.G.Om0) (budget : ι → ℝ)
    (hbad : ∀ i, -(1-c)*budget i ≤ plaqEnergy P.U (iE P.G x) (arm i))
    (hgood : ∀ p, p ∉ plaqIn P.G.Om0 → (∀ i, p ≠ arm i) →
      0 ≤ plaqEnergy P.U (iE P.G x) p) :
    -(1-c)*(∑ i, budget i) ≤ omittedEnergy P x
```

<a id="bp-470"></a>
#### bp-470 — `AdalyFormal.Round13.Positivity.Physical.exteriorPair`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:1909`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:144`: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1909`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:144`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def exteriorPair (Om : Set (PeriodicLatticeSite L)) (z : PeriodicLatticeSite L) : Prop
```

<a id="bp-471"></a>
#### bp-471 — `AdalyFormal.Round13.Positivity.Physical.exteriorPair_shift`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:1912`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:145`: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_shift' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1912`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:145`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_shift' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-470](#bp-470).

```lean
theorem exteriorPair_shift {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShift z ν)
```

<a id="bp-472"></a>
#### bp-472 — `AdalyFormal.Round13.Positivity.Physical.exteriorPair_back`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:1920`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:146`: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_back' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1920`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:146`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_back' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-470](#bp-470).

```lean
theorem exteriorPair_back {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShiftBack z ν)
```

<a id="bp-473"></a>
#### bp-473 — `AdalyFormal.Round13.Positivity.Physical.exteriorPair_vertices`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:1934`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:147`: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_vertices' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1934`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:147`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.exteriorPair_vertices' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-470](#bp-470); [bp-471](#bp-471).

```lean
theorem exteriorPair_vertices {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (p : PeriodicLatticePlaquette L) (hp : exteriorPair Om p.1) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      e.1 ∉ Om ∧ periodicLatticeShift e.1 e.2 ∉ Om
```

<a id="bp-474"></a>
#### bp-474 — `AdalyFormal.Round13.Positivity.Physical.star_edge_cases`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:1957`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:150`: `'AdalyFormal.Round13.Positivity.Physical.star_edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:1957`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:150`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.star_edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-470](#bp-470); [bp-472](#bp-472).

```lean
theorem star_edge_cases {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ Om)
    (p : PeriodicLatticePlaquette L) (e : Bond L)
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hs : e ∈ starLinks (periodicLatticeShift x 0)) :
    (∃ ν : {ν : Fin 3 // 0 < ν}, p = P1 x ν ∨ p = P2 x ν) ∨
      exteriorPair Om p.1
```

<a id="bp-475"></a>
#### bp-475 — `AdalyFormal.Round13.Positivity.Physical.plaqEnergy_zero_input`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2055`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:156`: `'AdalyFormal.Round13.Positivity.Physical.plaqEnergy_zero_input' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2055`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:156`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.plaqEnergy_zero_input' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-463](#bp-463).

```lean
theorem plaqEnergy_zero_input (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hz : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : plaqEnergy U A p = 0
```

<a id="bp-476"></a>
#### bp-476 — `AdalyFormal.Round13.Positivity.Physical.hol_flat_components`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2061`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:151`: `'AdalyFormal.Round13.Positivity.Physical.hol_flat_components' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2061`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:151`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.hol_flat_components' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem hol_flat_components (U : Cfg L) (p : PeriodicLatticePlaquette L)
    (h : holonomyElem U p = 1) : reHolonomy U p = 1 ∧ imHolonomy U p = 0
```

<a id="bp-477"></a>
#### bp-477 — `AdalyFormal.Round13.Positivity.Physical.plaqEnergy_nonneg_links`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2069`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:152`: `'AdalyFormal.Round13.Positivity.Physical.plaqEnergy_nonneg_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2069`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:152`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.plaqEnergy_nonneg_links' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-451](#bp-451); [bp-476](#bp-476).

```lean
theorem plaqEnergy_nonneg_links (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hU : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = 1) : 0 ≤ plaqEnergy U A p
```

<a id="bp-478"></a>
#### bp-478 — `AdalyFormal.Round13.Positivity.Physical.nonstar_nonneg`

Every actual non-arm plaquette contributes nonnegatively: it is flat or has supported input zero even if its holonomy is curved.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2083`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:159`: `'AdalyFormal.Round13.Positivity.Physical.nonstar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2083`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:159`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.nonstar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-473](#bp-473); [bp-474](#bp-474); [bp-475](#bp-475); [bp-477](#bp-477).

```lean
theorem nonstar_nonneg {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ G.Om0)
    (t : ℝ) (u : ↥(bondSupp G)) (p : PeriodicLatticePlaquette L)
    (hnot : ∀ ν : {ν : Fin 3 // 0 < ν}, p ≠ P1 x ν ∧ p ≠ P2 x ν) :
    0 ≤ plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) p
```

<a id="bp-479"></a>
#### bp-479 — `AdalyFormal.Round13.Positivity.Physical.right_forward_out`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2103`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:160`: `'AdalyFormal.Round13.Positivity.Physical.right_forward_out' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2103`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:160`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.right_forward_out' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem right_forward_out {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (periodicLatticeShift (rightSite hq R) 0) 0 ∉ (dilTower q R).Om 0
```

<a id="bp-480"></a>
#### bp-480 — `AdalyFormal.Round13.Positivity.Physical.hol_phase_components`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2116`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:161`: `'AdalyFormal.Round13.Positivity.Physical.hol_phase_components' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2116`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:161`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.hol_phase_components' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem hol_phase_components (U : Cfg L) (p : PeriodicLatticePlaquette L) (t : ℝ)
    (hh : holonomyElem U p = uθ t) :
    reHolonomy U p = realHol (Real.cos t) ∧ imHolonomy U p = imagHol (Real.sin t)
```

<a id="bp-481"></a>
#### bp-481 — `AdalyFormal.Round13.Positivity.Physical.norm_coordinates`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2136`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:155`: `'AdalyFormal.Round13.Positivity.Physical.norm_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2136`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:155`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.norm_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem norm_coordinates (X : SuTwo) :
    Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) +
      (((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im)^2 = ‖X‖^2
```

<a id="bp-482"></a>
#### bp-482 — `AdalyFormal.Round13.Positivity.Physical.right_first_norm_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2143`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:164`: `'AdalyFormal.Round13.Positivity.Physical.right_first_norm_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2143`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:164`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.right_first_norm_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-467](#bp-467); [bp-480](#bp-480); [bp-481](#bp-481).

```lean
theorem right_first_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖Y‖^2+‖Z‖^2) ≤ plaqEnergy U A p
```

<a id="bp-483"></a>
#### bp-483 — `AdalyFormal.Round13.Positivity.Physical.right_third_norm_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2161`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:167`: `'AdalyFormal.Round13.Positivity.Physical.right_third_norm_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2161`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:167`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.right_third_norm_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-468](#bp-468); [bp-480](#bp-480); [bp-481](#bp-481).

```lean
theorem right_third_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hZ : (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖X‖^2+‖Y‖^2) ≤ plaqEnergy U A p
```

<a id="bp-484"></a>
#### bp-484 — `AdalyFormal.Round13.Positivity.Physical.arm1_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2215`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:170`: `'AdalyFormal.Round13.Positivity.Physical.arm1_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2215`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:170`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm1_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-483](#bp-483).

```lean
theorem arm1_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShift x ν.1,0)‖^2 +
      ‖(iE G u) (x,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P1 x ν)
```

<a id="bp-485"></a>
#### bp-485 — `AdalyFormal.Round13.Positivity.Physical.arm2_lower`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2240`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:171`: `'AdalyFormal.Round13.Positivity.Physical.arm2_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2240`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:171`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm2_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-482](#bp-482).

```lean
theorem arm2_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShiftBack x ν.1,0)‖^2 +
      ‖(iE G u) (periodicLatticeShiftBack x ν.1,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P2 x ν)
```

<a id="bp-486"></a>
#### bp-486 — `AdalyFormal.Round13.Positivity.Physical.arm1_omitted`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2270`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:172`: `'AdalyFormal.Round13.Positivity.Physical.arm1_omitted' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2270`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:172`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm1_omitted' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem arm1_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P1 x ν ∉ plaqIn Om
```

<a id="bp-487"></a>
#### bp-487 — `AdalyFormal.Round13.Positivity.Physical.arm2_omitted`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2275`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:173`: `'AdalyFormal.Round13.Positivity.Physical.arm2_omitted' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2275`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:173`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm2_omitted' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem arm2_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P2 x ν ∉ plaqIn Om
```

<a id="bp-488"></a>
#### bp-488 — `AdalyFormal.Round13.Positivity.Physical.arm`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2311`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:174`: `'AdalyFormal.Round13.Positivity.Physical.arm' depends on axioms: [propext, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2311`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:174`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def arm (x : PeriodicLatticeSite L) : Fin 4 → PeriodicLatticePlaquette L
```

<a id="bp-489"></a>
#### bp-489 — `AdalyFormal.Round13.Positivity.Physical.arm_injective`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2314`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:176`: `'AdalyFormal.Round13.Positivity.Physical.arm_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2314`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:176`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.arm_injective' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-488](#bp-488).

```lean
theorem arm_injective {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) : Function.Injective (arm x)
```

<a id="bp-490"></a>
#### bp-490 — `AdalyFormal.Round13.Positivity.Physical.armBudget`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2326`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:175`: `'AdalyFormal.Round13.Positivity.Physical.armBudget' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2326`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:175`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.armBudget' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def armBudget {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) : Fin 4 → ℝ
```

<a id="bp-491"></a>
#### bp-491 — `AdalyFormal.Round13.Positivity.Physical.armBudget_sum`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2333`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:177`: `'AdalyFormal.Round13.Positivity.Physical.armBudget_sum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2333`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:177`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.armBudget_sum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-490](#bp-490).

```lean
theorem armBudget_sum {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i, armBudget hq R A i) = ∑ i : Fin 8, ‖A (leaf hq R i)‖^2
```

<a id="bp-492"></a>
#### bp-492 — `AdalyFormal.Round13.Positivity.Physical.rightStar_omitted_loss`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2348`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:178`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_omitted_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2348`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:178`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_omitted_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-469](#bp-469); [bp-478](#bp-478); [bp-479](#bp-479); [bp-484](#bp-484); [bp-485](#bp-485); [bp-486](#bp-486); [bp-487](#bp-487); [bp-488](#bp-488); [bp-489](#bp-489); [bp-490](#bp-490); [bp-491](#bp-491).

```lean
theorem rightStar_omitted_loss {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hu : (((iE (geomOf 2 1 (dilTower q R)) u) (rightSite hq R,0) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    -(1-Real.cos t)*(∑ i : Fin 8,
      ‖(iE (geomOf 2 1 (dilTower q R)) u) (leaf hq R i)‖^2) ≤
    omittedEnergy (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R)) u
```

<a id="bp-493"></a>
#### bp-493 — `AdalyFormal.Round13.Positivity.Physical.rightStar_raw_omitted_loss`

The complete raw omitted-plaquette loss bound is proved, matching precisely eight actual leaf masses and retaining the central neutral square.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:2395`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:181`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_raw_omitted_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:2395`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:181`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_raw_omitted_loss' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-464](#bp-464); [bp-492](#bp-492).

```lean
theorem rightStar_raw_omitted_loss {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hu : (((iE (geomOf 2 1 (dilTower q R)) u) (rightSite hq R,0) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    -(1-Real.cos t)*(∑ i : Fin 8,
      ‖(iE (geomOf 2 1 (dilTower q R)) u) (leaf hq R i)‖^2) ≤
      ∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then 0 else
        plaqEnergy (rightStar hq R t) (iE (geomOf 2 1 (dilTower q R)) u) p
```

<a id="bp-494"></a>
#### bp-494 — `AdalyFormal.Round13.Positivity.Physical.rightStar_local_hol`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3409`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:193`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_local_hol' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3409`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:193`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_local_hol' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-476](#bp-476).

```lean
theorem rightStar_local_hol {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : p ∈ plaqIn ((dilTower q R).Om 0)) :
    reHolonomy (rightStar hq R t) p = 1 ∧ imHolonomy (rightStar hq R t) p = 0
```

<a id="bp-495"></a>
#### bp-495 — `AdalyFormal.Round13.Positivity.Physical.rightStar_carrier_lower`

On the central-charged-zero subspace, the full physical carrier dominates \(\cos t\) times the actual localized carrier.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3427`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:194`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_carrier_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3427`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:194`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_carrier_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-453](#bp-453); [bp-454](#bp-454); [bp-492](#bp-492); [bp-494](#bp-494).

```lean
theorem rightStar_carrier_lower {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t) (u : TwistSpace q R)
    (hu : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    Real.cos t * ⟪u, (dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R t) 1 (dilLam q R))).Ginv u⟫ ≤
      ⟪u, vacA q R (rightStar hq R) 1 t u⟫
```

<a id="bp-496"></a>
#### bp-496 — `AdalyFormal.Round13.Positivity.Physical.rightStar_zero_coordinate_positive`

Supporting physical mass, full-color or periodic-geometry estimate for the P2 route, with the exact hypotheses displayed below.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3448`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:197`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_zero_coordinate_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3448`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:197`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_zero_coordinate_positive' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-495](#bp-495).

```lean
theorem rightStar_zero_coordinate_positive {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.pi/2)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hz : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    0 < ⟪u, vacA q R (rightStar hq R) 1 t u⟫
```

<a id="bp-497"></a>
#### bp-497 — `AdalyFormal.Round13.Positivity.Physical.rightStar_prefix_lower`

Every closed prefix strictly below half pi has the positive relative factor \(\cos T\), independent of q and R. No uniform ordinary-norm spectral gap is claimed.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3460`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:200`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_prefix_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3460`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:200`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_prefix_lower' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-460](#bp-460); [bp-495](#bp-495).

```lean
theorem rightStar_prefix_lower {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (T t : ℝ) (hT0 : 0 ≤ T) (hT : T < Real.pi/2) (ht0 : 0 ≤ t) (ht : t ≤ T)
    (u : TwistSpace q R)
    (hu : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    0 < Real.cos T ∧
    Real.cos T * ⟪u, (dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (fun _ => 1) 1 (dilLam q R))).Ginv u⟫ ≤
      ⟪u, vacA q R (rightStar hq R) 1 t u⟫
```

<a id="bp-498"></a>
#### bp-498 — `AdalyFormal.Round13.Positivity.Physical.rightStar_P2`

P2, unconditionally in the exact round-12 GAPS form, on the whole physical zero-coordinate subspace and open half-pi interval. No omitted-energy or unit hypothesis remains.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3490`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:203`: `'AdalyFormal.Round13.Positivity.Physical.rightStar_P2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3490`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:203`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.rightStar_P2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-221](#bp-221); [bp-496](#bp-496).

```lean
theorem rightStar_P2 :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
      (t : ℝ), 0 < t → t < Real.pi/2 →
      ∀ x : TwistSpace q R, x ≠ 0 →
        AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
          (rightSite hq R, (0 : Fin 3)) x = 0 →
        0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
```

<a id="bp-499"></a>
#### bp-499 — `AdalyFormal.Round13.Positivity.Physical.cofinal_rightStar_P2`

The original nested dyadic/even-radius version of P2 is proved. The stronger all-instance theorem remains available at P3-selected indices.

- **Source:** `AHP/round13/shared/positivity/R2_P2.lean:3502`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/positivity/R2_P2.lean.log:204`: `'AdalyFormal.Round13.Positivity.Physical.cofinal_rightStar_P2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/positivity/r2/P2.verify.lean:3502`, identical declaration body; `AHP/round13/positivity/r2/P2.verify.lean.log:204`, exit `0`; record: `'AdalyFormal.Round13.Positivity.Physical.cofinal_rightStar_P2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-498](#bp-498).

```lean
theorem cofinal_rightStar_P2 :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∀ (t : ℝ), 0 < t → t < Real.pi/2 →
        ∀ x : TwistSpace (2^j) R, x ≠ 0 →
          chargedCoordinate (2^j) R (rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
          0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫
```

### Detection

R1 closes the full flat constraint-unit prerequisite and distinguishes linear trace continuation from quadratic detection. R2 supplies the exact global finite mixed-color area dictionary, not a nonzero weighted sum. These detection certificates are builder/publication checked only.

<a id="bp-500"></a>
#### bp-500 — `AdalyFormal.Round13.Detection.ColorTrace.flatJet_zero_of_pointwise_color`

The genuine full dressed flat jet vanishes for arbitrary pointwise single-color fields. Such fields are not asserted to lie in the crossing kernel.

- **Source:** `AHP/round13/shared/detection/R1_ColorTrace.lean:336`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_ColorTrace.lean.log:29`: `'AdalyFormal.Round13.Detection.ColorTrace.flatJet_zero_of_pointwise_color' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem flatJet_zero_of_pointwise_color {L : PeriodicLatticeExtent}
    (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) (f : Bond L → ℝ)
    (hf : ∀ b, (u : BondFnL2 L) b = f b • pauliE1) : flatJet G a u = 0
```

<a id="bp-501"></a>
#### bp-501 — `AdalyFormal.Round13.Detection.ColorTrace.nonzero_trace_with_zero_jet`

A nonzero pointwise single-color field can have a nonzero trace and zero actual jet; this is not a counterexample to P3 at the crossing.

- **Source:** `AHP/round13/shared/detection/R1_ColorTrace.lean:357`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_ColorTrace.lean.log:32`: `'AdalyFormal.Round13.Detection.ColorTrace.nonzero_trace_with_zero_jet' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-500](#bp-500).

```lean
theorem nonzero_trace_with_zero_jet {L : PeriodicLatticeExtent}
    (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G)) (f : Bond L → ℝ)
    (hf : ∀ b, (u : BondFnL2 L) b = f b • pauliE1)
    (b : Bond L) (hb : f b ≠ 0) : u ≠ 0 ∧ flatJet G a u = 0
```

<a id="bp-502"></a>
#### bp-502 — `AdalyFormal.Round13.Detection.flat_N_unit`

The full actual flat constraint operator N is a unit. This is not merely a Schur compression, and no detection hypothesis is used.

- **Source:** `AHP/round13/shared/detection/R1_FlatUnit.lean:1143`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_FlatUnit.lean.log:1`: `'AdalyFormal.Round13.Detection.flat_N_unit' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem flat_N_unit {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    IsUnit (N (flatData q R))
```

<a id="bp-503"></a>
#### bp-503 — `AdalyFormal.Round13.Detection.cofinal_flat_N_units`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_FlatUnit.lean:1160`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_FlatUnit.lean.log:2`: `'AdalyFormal.Round13.Detection.cofinal_flat_N_units' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-502](#bp-502).

```lean
theorem cofinal_flat_N_units :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      IsUnit (N (flatData (2^j) R))
```

<a id="bp-504"></a>
#### bp-504 — `AdalyFormal.Round13.Detection.curlDetected_of_topJet`

Actual top-jet nonvanishing implies CurlDetected with the flat-unit guard discharged. The top-jet hypothesis remains unproved for the crossing.

- **Source:** `AHP/round13/shared/detection/R1_JetBridge.lean:3540`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_JetBridge.lean.log:363`: `'AdalyFormal.Round13.Detection.curlDetected_of_topJet' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-148](#bp-148); [bp-502](#bp-502).

```lean
theorem curlDetected_of_topJet {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (u : TwistSpace q R) (hjet : TopJetDetected hq R u) :
    CurlDetected q R u
```

<a id="bp-505"></a>
#### bp-505 — `AdalyFormal.Round13.Detection.curlDetected_of_signed_top_row`

Conditional common-cell-sign criterion. Those signs are not established; retained numerical data have mixed cell signs.

- **Source:** `AHP/round13/shared/detection/R1_JetBridge.lean:3548`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_JetBridge.lean.log:364`: `'AdalyFormal.Round13.Detection.curlDetected_of_signed_top_row' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-504](#bp-504).

```lean
theorem curlDetected_of_signed_top_row {q R j : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (hj : j < blockCount q R)
    (u : TwistSpace q R) (sign : ℝ)
    (hcell : ∀ c : Fin (4*q) × Fin (4*q),
      0 ≤ sign * AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional
        (C2fullOf (G q R) flatCfg
          (Wop (G q R) flatCfg 1 (iE (G q R) u)) (topIdx hq hj c)))
    (hone : ∃ c : Fin (4*q) × Fin (4*q),
      0 < sign * AdalyFormal.Round10.Nonvanishing.DilatedFlux.neutralFunctional
        (C2fullOf (G q R) flatCfg
          (Wop (G q R) flatCfg 1 (iE (G q R) u)) (topIdx hq hj c))) :
    CurlDetected q R u
```

<a id="bp-506"></a>
#### bp-506 — `AdalyFormal.Round13.Detection.Transfer.zero_pair_step`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:13`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:15`: `'AdalyFormal.Round13.Detection.Transfer.zero_pair_step' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem zero_pair_step (a b : ℕ → K) (u : ℕ → E) (n : ℕ)
    (hb : b n ≠ 0)
    (hr : u (n+2) = a n • u (n+1) + b n • u n)
    (h1 : u (n+1) = 0) (h2 : u (n+2) = 0) : u n = 0
```

<a id="bp-507"></a>
#### bp-507 — `AdalyFormal.Round13.Detection.Transfer.zero_prefix_of_zero_pair`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:21`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:16`: `'AdalyFormal.Round13.Detection.Transfer.zero_prefix_of_zero_pair' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-506](#bp-506).

```lean
theorem zero_prefix_of_zero_pair (a b : ℕ → K) (u : ℕ → E) (N : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hr : ∀ n < N, u (n+2) = a n • u (n+1) + b n • u n)
    (h0 : u N = 0) (h1 : u (N+1) = 0) : ∀ k ≤ N+1, u k = 0
```

<a id="bp-508"></a>
#### bp-508 — `AdalyFormal.Round13.Detection.Transfer.pair_ne_zero_of_seed`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:43`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:19`: `'AdalyFormal.Round13.Detection.Transfer.pair_ne_zero_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-507](#bp-507).

```lean
theorem pair_ne_zero_of_seed (a b : ℕ → K) (u : ℕ → E) (N k : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hr : ∀ n < N, u (n+2) = a n • u (n+1) + b n • u n)
    (hk : k ≤ N+1) (hne : u k ≠ 0) : u N ≠ 0 ∨ u (N+1) ≠ 0
```

<a id="bp-509"></a>
#### bp-509 — `AdalyFormal.Round13.Detection.Transfer.area_step`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:60`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:20`: `'AdalyFormal.Round13.Detection.Transfer.area_step' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem area_step (a b x y : ℕ → K) (n : ℕ)
    (hx : x (n+2) = a n * x (n+1) + b n * x n)
    (hy : y (n+2) = a n * y (n+1) + b n * y n) :
    area x y (n+1) = -b n * area x y n
```

<a id="bp-510"></a>
#### bp-510 — `AdalyFormal.Round13.Detection.Transfer.area_ne_zero`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:70`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:21`: `'AdalyFormal.Round13.Detection.Transfer.area_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-509](#bp-509).

```lean
theorem area_ne_zero (a b x y : ℕ → K) (N : ℕ)
    (hb : ∀ n < N, b n ≠ 0)
    (hx : ∀ n < N, x (n+2) = a n * x (n+1) + b n * x n)
    (hy : ∀ n < N, y (n+2) = a n * y (n+1) + b n * y n)
    (hseed : area x y 0 ≠ 0) : area x y N ≠ 0
```

<a id="bp-511"></a>
#### bp-511 — `AdalyFormal.Round13.Detection.Transfer.area_proportional_zero`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:84`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:22`: `'AdalyFormal.Round13.Detection.Transfer.area_proportional_zero' depends on axioms: [propext, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem area_proportional_zero (x : ℕ → K) (c : K) (n : ℕ) :
    area x (fun k => c * x k) n = 0
```

<a id="bp-512"></a>
#### bp-512 — `AdalyFormal.Round13.Detection.Transfer.decaying_trace_counterexample`

An exact recurrence has nonzero linear trace at every layer but zero oriented area. It is not identified with a physical crossing field.

- **Source:** `AHP/round13/shared/detection/R1_Transfer.lean:92`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R1_Transfer.lean.log:23`: `'AdalyFormal.Round13.Detection.Transfer.decaying_trace_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem decaying_trace_counterexample :
    ∃ x y : ℕ → ℝ,
      (∀ n, x n ≠ 0) ∧
      (∀ n, x (n+2) = (5/2:ℝ) * x (n+1) - x n) ∧
      (∀ n, y (n+2) = (5/2:ℝ) * y (n+1) - y n) ∧
      (∀ n, area x y n = 0)
```

<a id="bp-513"></a>
#### bp-513 — `AdalyFormal.Round13.Detection.Area.mixed_bilinear`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_Area.lean:15`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_Area.lean.log:1`: `'AdalyFormal.Round13.Detection.Area.mixed_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem mixed_bilinear (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y, ∀ f g, Q (a f + b g) = B f g
```

<a id="bp-514"></a>
#### bp-514 — `AdalyFormal.Round13.Detection.Area.mixed_alternating`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_Area.lean:30`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_Area.lean.log:2`: `'AdalyFormal.Round13.Detection.Area.mixed_alternating' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-513](#bp-513).

```lean
theorem mixed_alternating (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : S →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) :
    ∃ B : S →ₗ[ℝ] S →ₗ[ℝ] Y,
      (∀ f g, Q (a f + b g) = B f g) ∧ (∀ f g, B g f = -B f g)
```

<a id="bp-515"></a>
#### bp-515 — `AdalyFormal.Round13.Detection.Area.bilinear_matrix`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_Area.lean:45`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_Area.lean.log:3`: `'AdalyFormal.Round13.Detection.Area.bilinear_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem bilinear_matrix (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (f g : I → ℝ) :
    B f g = ∑ i : I, ∑ j : I,
      (f i * g j) • B (Pi.single i 1) (Pi.single j 1)
```

<a id="bp-516"></a>
#### bp-516 — `AdalyFormal.Round13.Detection.Area.bilinear_area`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_Area.lean:59`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_Area.lean.log:4`: `'AdalyFormal.Round13.Detection.Area.bilinear_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-515](#bp-515).

```lean
theorem bilinear_area (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] Y)
    (hskew : ∀ f g, B g f = -B f g) (f g : I → ℝ) :
    B f g = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • B (Pi.single i 1) (Pi.single j 1)
```

<a id="bp-517"></a>
#### bp-517 — `AdalyFormal.Round13.Detection.Area.quadratic_area`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_Area.lean:72`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_Area.lean.log:5`: `'AdalyFormal.Round13.Detection.Area.quadratic_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-514](#bp-514); [bp-516](#bp-516).

```lean
theorem quadratic_area (Q : X → Y) (hQ : IsQuadMap Q)
    (a b : (I → ℝ) →ₗ[ℝ] X) (ha : ∀ f, Q (a f) = 0) (hb : ∀ g, Q (b g) = 0)
    (hrot : ∀ f g, Q (a g - b f) = Q (a f + b g)) (f g : I → ℝ) :
    Q (a f + b g) = (1 / 2 : ℝ) • ∑ i : I, ∑ j : I,
      (f i * g j - g i * f j) • Q (a (Pi.single i 1) + b (Pi.single j 1))
```

<a id="bp-518"></a>
#### bp-518 — `AdalyFormal.Round13.Detection.ColorArea.colorCarrier`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:478`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:54`: `'AdalyFormal.Round13.Detection.ColorArea.colorCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def colorCarrier (G : TowerGeom L) (X : SuTwo) : (Bond L → ℝ) →ₗ[ℝ] ↥(bondSupp G) where
  toFun f
```

<a id="bp-519"></a>
#### bp-519 — `AdalyFormal.Round13.Detection.ColorArea.colorCarrier_apply`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:493`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:55`: `'AdalyFormal.Round13.Detection.ColorArea.colorCarrier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518).

```lean
@[simp] theorem colorCarrier_apply (G : TowerGeom L) (X : SuTwo)
    (f : Bond L → ℝ) (e : Bond L) :
    ((colorCarrier G X f : ↥(bondSupp G)) : BondFnL2 L) e =
      if e ∈ bondsOm0 G then f e • X else 0
```

<a id="bp-520"></a>
#### bp-520 — `AdalyFormal.Round13.Detection.ColorArea.colorCarrier_gauge`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:498`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:56`: `'AdalyFormal.Round13.Detection.ColorArea.colorCarrier_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518).

```lean
theorem colorCarrier_gauge (G : TowerGeom L) (X : SuTwo) (f : Bond L → ℝ)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    adEL (constGauge g) G (colorCarrier G X f) = colorCarrier G (RMap g X) f
```

<a id="bp-521"></a>
#### bp-521 — `AdalyFormal.Round13.Detection.ColorArea.colorCarrier_neg`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:507`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:57`: `'AdalyFormal.Round13.Detection.ColorArea.colorCarrier_neg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518).

```lean
theorem colorCarrier_neg (G : TowerGeom L) (X : SuTwo) (f : Bond L → ℝ) :
    colorCarrier G (-X) f = -colorCarrier G X f
```

<a id="bp-522"></a>
#### bp-522 — `AdalyFormal.Round13.Detection.ColorArea.half_pauliE2`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:514`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:58`: `'AdalyFormal.Round13.Detection.ColorArea.half_pauliE2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem half_pauliE2 : RMap (uθ (Real.pi / 2)) pauliE2 = -pauliE2
```

<a id="bp-523"></a>
#### bp-523 — `AdalyFormal.Round13.Detection.ColorArea.flip_pauliE2`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:522`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:59`: `'AdalyFormal.Round13.Detection.ColorArea.flip_pauliE2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem flip_pauliE2 : RMap flipElt pauliE2 = pauliE2
```

<a id="bp-524"></a>
#### bp-524 — `AdalyFormal.Round13.Detection.ColorArea.quarter_pauliE1`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:530`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:60`: `'AdalyFormal.Round13.Detection.ColorArea.quarter_pauliE1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem quarter_pauliE1 : RMap (uθ (Real.pi / 4)) pauliE1 = -pauliE2
```

<a id="bp-525"></a>
#### bp-525 — `AdalyFormal.Round13.Detection.ColorArea.quarter_pauliE2`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:562`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:61`: `'AdalyFormal.Round13.Detection.ColorArea.quarter_pauliE2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem quarter_pauliE2 : RMap (uθ (Real.pi / 4)) pauliE2 = pauliE1
```

<a id="bp-526"></a>
#### bp-526 — `AdalyFormal.Round13.Detection.ColorArea.color_one_zero`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:585`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:62`: `'AdalyFormal.Round13.Detection.ColorArea.color_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518); [bp-520](#bp-520); [bp-521](#bp-521).

```lean
theorem color_one_zero (G : TowerGeom L) (a : ℝ) (f : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 f) = 0
```

<a id="bp-527"></a>
#### bp-527 — `AdalyFormal.Round13.Detection.ColorArea.color_two_zero`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:594`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:63`: `'AdalyFormal.Round13.Detection.ColorArea.color_two_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518); [bp-520](#bp-520); [bp-521](#bp-521); [bp-522](#bp-522); [bp-523](#bp-523).

```lean
theorem color_two_zero (G : TowerGeom L) (a : ℝ) (g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE2 g) = 0
```

<a id="bp-528"></a>
#### bp-528 — `AdalyFormal.Round13.Detection.ColorArea.color_sum_charged`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:603`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:64`: `'AdalyFormal.Round13.Detection.ColorArea.color_sum_charged' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518); [bp-520](#bp-520); [bp-521](#bp-521); [bp-522](#bp-522).

```lean
theorem color_sum_charged (G : TowerGeom L) (f g : Bond L → ℝ) :
    halfE G (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) =
      -(colorCarrier G pauliE1 f + colorCarrier G pauliE2 g)
```

<a id="bp-529"></a>
#### bp-529 — `AdalyFormal.Round13.Detection.ColorArea.quarter_axis`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:610`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:65`: `'AdalyFormal.Round13.Detection.ColorArea.quarter_axis' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem quarter_axis : RMap (uθ (Real.pi / 4)) pauliE3 = pauliE3
```

<a id="bp-530"></a>
#### bp-530 — `AdalyFormal.Round13.Detection.ColorArea.flatJet_color_quarter`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:623`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:66`: `'AdalyFormal.Round13.Detection.ColorArea.flatJet_color_quarter' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518); [bp-520](#bp-520); [bp-521](#bp-521); [bp-524](#bp-524); [bp-525](#bp-525); [bp-528](#bp-528); [bp-529](#bp-529).

```lean
theorem flatJet_color_quarter (G : TowerGeom L) (a : ℝ) (f g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 g - colorCarrier G pauliE2 f) =
      flatJet G a (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g)
```

<a id="bp-531"></a>
#### bp-531 — `AdalyFormal.Round13.Detection.ColorArea.flatJet_area`

Exact finite alternating mixed-color expansion of the full dressed C2 jet, using actual masked two-bond inputs. No coefficient sign or local stencil is assumed.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:639`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:69`: `'AdalyFormal.Round13.Detection.ColorArea.flatJet_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-517](#bp-517); [bp-518](#bp-518); [bp-526](#bp-526); [bp-527](#bp-527); [bp-530](#bp-530).

```lean
theorem flatJet_area (G : TowerGeom L) (a : ℝ) (f g : Bond L → ℝ) :
    flatJet G a (colorCarrier G pauliE1 f + colorCarrier G pauliE2 g) =
      (1 / 2 : ℝ) • ∑ e : Bond L, ∑ d : Bond L,
        (f e * g d - g e * f d) •
          flatJet G a (colorCarrier G pauliE1 (Pi.single e 1) +
            colorCarrier G pauliE2 (Pi.single d 1))
```

<a id="bp-532"></a>
#### bp-532 — `AdalyFormal.Round13.Detection.ColorArea.imagPart`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:651`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:40`: `'AdalyFormal.Round13.Detection.ColorArea.imagPart' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def imagPart (G : TowerGeom L) (u : ↥(bondSupp G)) (e : Bond L) : ℝ
```

<a id="bp-533"></a>
#### bp-533 — `AdalyFormal.Round13.Detection.ColorArea.realPart`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:654`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:41`: `'AdalyFormal.Round13.Detection.ColorArea.realPart' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def realPart (G : TowerGeom L) (u : ↥(bondSupp G)) (e : Bond L) : ℝ
```

<a id="bp-534"></a>
#### bp-534 — `AdalyFormal.Round13.Detection.ColorArea.half_negative_diag`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:657`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:42`: `'AdalyFormal.Round13.Detection.ColorArea.half_negative_diag' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem half_negative_diag (X : SuTwo) (hX : RMap (uθ (Real.pi / 2)) X = -X) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0
```

<a id="bp-535"></a>
#### bp-535 — `AdalyFormal.Round13.Detection.ColorArea.carrier_color_decompose`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:667`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:43`: `'AdalyFormal.Round13.Detection.ColorArea.carrier_color_decompose' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518); [bp-532](#bp-532); [bp-533](#bp-533); [bp-534](#bp-534).

```lean
theorem carrier_color_decompose (G : TowerGeom L) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) :
    u = colorCarrier G pauliE1 (imagPart G u) + colorCarrier G pauliE2 (realPart G u)
```

<a id="bp-536"></a>
#### bp-536 — `AdalyFormal.Round13.Detection.ColorArea.areaCoefficient`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:687`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:46`: `'AdalyFormal.Round13.Detection.ColorArea.areaCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-518](#bp-518).

```lean
def areaCoefficient (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e d : Bond L) : ℝ
```

<a id="bp-537"></a>
#### bp-537 — `AdalyFormal.Round13.Detection.ColorArea.areaCoefficient_skew`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:691`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:47`: `'AdalyFormal.Round13.Detection.ColorArea.areaCoefficient_skew' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-514](#bp-514); [bp-518](#bp-518); [bp-526](#bp-526); [bp-527](#bp-527); [bp-530](#bp-530); [bp-536](#bp-536).

```lean
theorem areaCoefficient_skew (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e d : Bond L) :
    areaCoefficient G a p d e = -areaCoefficient G a p e d
```

<a id="bp-538"></a>
#### bp-538 — `AdalyFormal.Round13.Detection.ColorArea.areaCoefficient_diagonal`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:701`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:50`: `'AdalyFormal.Round13.Detection.ColorArea.areaCoefficient_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-536](#bp-536); [bp-537](#bp-537).

```lean
theorem areaCoefficient_diagonal (G : TowerGeom L) (a : ℝ) (p : BIdx G) (e : Bond L) :
    areaCoefficient G a p e e = 0
```

<a id="bp-539"></a>
#### bp-539 — `AdalyFormal.Round13.Detection.ColorArea.neutralJet_area`

Exact genuine neutral-row expansion as one-half the weighted ordered-pair area sum, with full interior W retained.

- **Source:** `AHP/round13/shared/detection/R2_ColorArea.lean:707`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_ColorArea.lean.log:53`: `'AdalyFormal.Round13.Detection.ColorArea.neutralJet_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-531](#bp-531); [bp-532](#bp-532); [bp-533](#bp-533); [bp-535](#bp-535); [bp-536](#bp-536).

```lean
theorem neutralJet_area (G : TowerGeom L) (a : ℝ) (u : ↥(bondSupp G))
    (hu : halfE G u = -u) (p : BIdx G) :
    neutralCoord (flatJet G a u p) = (1 / 2 : ℝ) * ∑ e : Bond L, ∑ d : Bond L,
      (imagPart G u e * realPart G u d - realPart G u e * imagPart G u d) *
        areaCoefficient G a p e d
```

<a id="bp-540"></a>
#### bp-540 — `AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4340`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:430`: `'AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def aggregateCoefficient {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (e d : Bond (L q R)) : ℝ
```

<a id="bp-541"></a>
#### bp-541 — `AdalyFormal.Round13.Detection.PhysicalArea.areaSum`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4345`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:433`: `'AdalyFormal.Round13.Detection.PhysicalArea.areaSum' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-540](#bp-540).

```lean
def areaSum {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (u : TwistSpace q R) : ℝ
```

<a id="bp-542"></a>
#### bp-542 — `AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient_skew`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4351`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:434`: `'AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient_skew' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-540](#bp-540).

```lean
theorem aggregateCoefficient_skew {q R j : ℕ} (hq : 0 < q) (hj : j < blockCount q R)
    (e d : Bond (L q R)) : aggregateCoefficient hq hj d e = -aggregateCoefficient hq hj e d
```

<a id="bp-543"></a>
#### bp-543 — `AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient_diagonal`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4359`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:437`: `'AdalyFormal.Round13.Detection.PhysicalArea.aggregateCoefficient_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-540](#bp-540).

```lean
theorem aggregateCoefficient_diagonal {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (e : Bond (L q R)) : aggregateCoefficient hq hj e e = 0
```

<a id="bp-544"></a>
#### bp-544 — `AdalyFormal.Round13.Detection.PhysicalArea.physicalJetAggregate_area`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4364`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:440`: `'AdalyFormal.Round13.Detection.PhysicalArea.physicalJetAggregate_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-540](#bp-540); [bp-541](#bp-541).

```lean
theorem physicalJetAggregate_area {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (u : TwistSpace q R)
    (hu : halfE (G q R) u = -u) :
    physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u
```

<a id="bp-545"></a>
#### bp-545 — `AdalyFormal.Round13.Detection.PhysicalArea.kernelLine_half`

Supporting exact jet, color or recurrence statement. It does not establish nonvanishing for the physical crossing generator.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4384`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:443`: `'AdalyFormal.Round13.Detection.PhysicalArea.kernelLine_half' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem kernelLine_half {q R : ℕ}
    (V : ℝ → LinkCfg (L q R)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    halfE (G q R) u = -u
```

<a id="bp-546"></a>
#### bp-546 — `AdalyFormal.Round13.Detection.PhysicalArea.crossing_physicalJetAggregate_area`

For the original KernelLine generator, the genuine physical top-jet aggregate equals one-half the actual weighted areaSum. This is an identity, not nonvanishing.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4400`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:444`: `'AdalyFormal.Round13.Detection.PhysicalArea.crossing_physicalJetAggregate_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-541](#bp-541); [bp-544](#bp-544); [bp-545](#bp-545).

```lean
theorem crossing_physicalJetAggregate_area {q R j : ℕ} (hq : 0 < q)
    (hj : j < blockCount q R) (V : ℝ → LinkCfg (L q R))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    physicalJetAggregate hq hj u = (1 / 2 : ℝ) * areaSum hq hj u
```

<a id="bp-547"></a>
#### bp-547 — `AdalyFormal.Round13.Detection.PhysicalArea.crossing_topJet_iff_area`

At that same generator, top-jet detection is equivalent to a nonzero actual weighted areaSum at some top row. Neither side is proved to hold here.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4407`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:447`: `'AdalyFormal.Round13.Detection.PhysicalArea.crossing_topJet_iff_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-541](#bp-541); [bp-546](#bp-546).

```lean
theorem crossing_topJet_iff_area {q R : ℕ} (hq : 0 < q)
    (V : ℝ → LinkCfg (L q R)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    TopJetDetected hq R u ↔ ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

<a id="bp-548"></a>
#### bp-548 — `AdalyFormal.Round13.Detection.PhysicalArea.crossing_curlDetected_of_area`

Conditional crossing-detection handoff from a nonzero weighted areaSum. Its area premise remains open; this is not a proof of P3.

- **Source:** `AHP/round13/shared/detection/R2_PhysicalArea.lean:4419`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:450`: `'AdalyFormal.Round13.Detection.PhysicalArea.crossing_curlDetected_of_area' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-504](#bp-504); [bp-541](#bp-541); [bp-547](#bp-547).

```lean
theorem crossing_curlDetected_of_area {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hR18 : 18 ≤ R) (V : ℝ → LinkCfg (L q R))
    (u : TwistSpace q R) (hline : KernelLine q R V u)
    (harea : ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0) :
    CurlDetected q R u
```

### Assembly

R1 repairs the old join and supplies continuity, positive start and P1 crossing. R2 integrates P2, proves the whole KernelLine and compiles the entire P3-to-goal implication. The independent replay passed mathematical/source/axiom checks but rejected rightStar_kernelLine as the submitted final/physical target type; A below records the verified displayed statement, not a workflow closure. Exact p2 is an eligible P2 target. P3 and GoalNeg2 are still open.

<a id="bp-549"></a>
#### bp-549 — `AdalyFormal.Round13.Assembly.R1.p1`

The P1 proof is integrated into the original physical-input predicate.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6084`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:603`: `'AdalyFormal.Round13.Assembly.R1.p1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-430](#bp-430); [bp-555](#bp-555).

```lean
theorem p1 : P1
```

<a id="bp-550"></a>
#### bp-550 — `AdalyFormal.Round13.Assembly.R1.rightStar_crossing_before_halfpi`

Unconditional actual canonical crossing before half pi, PSD and nonunit carrier, and a nonzero kernel vector. R2 subsequently strengthens this to the whole KernelLine.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6088`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:604`: `'AdalyFormal.Round13.Assembly.R1.rightStar_crossing_before_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-549](#bp-549); [bp-566](#bp-566); [bp-567](#bp-567).

```lean
theorem rightStar_crossing_before_halfpi {q R : ℕ} (hq : 0 < q)
    (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    AdalyFormal.D1Literal.PSD
      (vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R))) ∧
    ¬ IsUnit (vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R))) ∧
    ∃ u : TwistSpace q R, u ≠ 0 ∧
      vacA q R (rightStar hq R) 1 (vacEdge q R (rightStar hq R)) u = 0
```

<a id="bp-551"></a>
#### bp-551 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_P2_P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6116`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:607`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_P2_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-176](#bp-176); [bp-549](#bp-549); [bp-556](#bp-556); [bp-557](#bp-557); [bp-569](#bp-569).

```lean
theorem cofinalNoCancellation_of_P2_P3 (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

<a id="bp-552"></a>
#### bp-552 — `AdalyFormal.Round13.Assembly.R1.CofinalP2P3`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6121`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:610`: `'AdalyFormal.Round13.Assembly.R1.CofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-221](#bp-221).

```lean
def CofinalP2P3 : Prop
```

<a id="bp-553"></a>
#### bp-553 — `AdalyFormal.Round13.Assembly.R1.cofinalPhysical_of_cofinalP2P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6132`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:611`: `'AdalyFormal.Round13.Assembly.R1.cofinalPhysical_of_cofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-549](#bp-549); [bp-552](#bp-552); [bp-570](#bp-570).

```lean
theorem cofinalPhysical_of_cofinalP2P3 (h : CofinalP2P3) : CofinalPhysicalInputs
```

<a id="bp-554"></a>
#### bp-554 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalP2P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_P1Spine.lean:6140`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_P1Spine.lean.log:614`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-176](#bp-176); [bp-552](#bp-552); [bp-553](#bp-553); [bp-572](#bp-572).

```lean
theorem cofinalNoCancellation_of_cofinalP2P3 (h : CofinalP2P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

<a id="bp-555"></a>
#### bp-555 — `AdalyFormal.Round13.Assembly.R1.P1`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3392`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:372`: `'AdalyFormal.Round13.Assembly.R1.P1' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def P1 : Prop
```

<a id="bp-556"></a>
#### bp-556 — `AdalyFormal.Round13.Assembly.R1.P2`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3397`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:373`: `'AdalyFormal.Round13.Assembly.R1.P2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-221](#bp-221).

```lean
def P2 : Prop
```

<a id="bp-557"></a>
#### bp-557 — `AdalyFormal.Round13.Assembly.R1.P3`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3405`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:374`: `'AdalyFormal.Round13.Assembly.R1.P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def P3 : Prop
```

<a id="bp-558"></a>
#### bp-558 — `AdalyFormal.Round13.Assembly.R1.StartInputs`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3411`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:375`: `'AdalyFormal.Round13.Assembly.R1.StartInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def StartInputs : Prop
```

<a id="bp-559"></a>
#### bp-559 — `AdalyFormal.Round13.Assembly.R1.CofinalRightStarCurlLine`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3418`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:376`: `'AdalyFormal.Round13.Assembly.R1.CofinalRightStarCurlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def CofinalRightStarCurlLine : Prop
```

<a id="bp-560"></a>
#### bp-560 — `AdalyFormal.Round13.Assembly.R1.rightStar_fixed`

Actual right-star gauge invariance at every angle, with no crossing or detection hypothesis. This specializes the round-12 diagonal-gauge identity to the same right-star family.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3426`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:377`: `'AdalyFormal.Round13.Assembly.R1.rightStar_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-200](#bp-200).

```lean
theorem rightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (rightStar hq R t) = rightStar hq R t
```

<a id="bp-561"></a>
#### bp-561 — `AdalyFormal.Round13.Assembly.R1.detected_line_of_physicalInputs`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3431`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:378`: `'AdalyFormal.Round13.Assembly.R1.detected_line_of_physicalInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-227](#bp-227); [bp-555](#bp-555); [bp-556](#bp-556); [bp-557](#bp-557); [bp-558](#bp-558); [bp-560](#bp-560).

```lean
theorem detected_line_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3)
    {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      CurlDetected q R u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2
```

<a id="bp-562"></a>
#### bp-562 — `AdalyFormal.Round13.Assembly.R1.cofinalRightStarCurlLine_of_physicalInputs`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3448`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:381`: `'AdalyFormal.Round13.Assembly.R1.cofinalRightStarCurlLine_of_physicalInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-555](#bp-555); [bp-556](#bp-556); [bp-557](#bp-557); [bp-558](#bp-558); [bp-559](#bp-559); [bp-561](#bp-561).

```lean
theorem cofinalRightStarCurlLine_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalRightStarCurlLine
```

<a id="bp-563"></a>
#### bp-563 — `AdalyFormal.Round13.Assembly.R1.cofinalAnyPathCurlLine_of_rightStar`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3462`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:384`: `'AdalyFormal.Round13.Assembly.R1.cofinalAnyPathCurlLine_of_rightStar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-559](#bp-559).

```lean
theorem cofinalAnyPathCurlLine_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathCurlLine
```

<a id="bp-564"></a>
#### bp-564 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_rightStar`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3474`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:387`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_rightStar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-234](#bp-234); [bp-559](#bp-559); [bp-563](#bp-563).

```lean
theorem cofinalNoCancellation_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathNoResponseCancellation
```

<a id="bp-565"></a>
#### bp-565 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_physicalInputs`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:3480`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:390`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_physicalInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-555](#bp-555); [bp-556](#bp-556); [bp-557](#bp-557); [bp-558](#bp-558); [bp-562](#bp-562); [bp-564](#bp-564).

```lean
theorem cofinalNoCancellation_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalAnyPathNoResponseCancellation
```

<a id="bp-566"></a>
#### bp-566 — `AdalyFormal.Round13.Assembly.R1.rightStar_vacA_cont`

Continuity of the actual full right-star vacuum carrier, with no external continuity hypothesis.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4397`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:402`: `'AdalyFormal.Round13.Assembly.R1.rightStar_vacA_cont' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
theorem rightStar_vacA_cont {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    Continuous (vacA q R (rightStar hq R) 1)
```

<a id="bp-567"></a>
#### bp-567 — `AdalyFormal.Round13.Assembly.R1.rightStar_vacA_pd_zero`

Strict positivity of the entire actual carrier at the zero-angle start, not a selected-sector estimate.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4414`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:403`: `'AdalyFormal.Round13.Assembly.R1.rightStar_vacA_pd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-091](#bp-091).

```lean
theorem rightStar_vacA_pd_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : TwistSpace q R) (hx : x ≠ 0) :
    0 < ⟪x, vacA q R (rightStar hq R) 1 0 x⟫
```

<a id="bp-568"></a>
#### bp-568 — `AdalyFormal.Round13.Assembly.R1.startInputs`

Both actual continuity and full positive-start inputs are discharged.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4425`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:404`: `'AdalyFormal.Round13.Assembly.R1.startInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-558](#bp-558); [bp-566](#bp-566); [bp-567](#bp-567).

```lean
theorem startInputs : StartInputs
```

<a id="bp-569"></a>
#### bp-569 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_P1_P2_P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4432`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:405`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_P1_P2_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-176](#bp-176); [bp-555](#bp-555); [bp-556](#bp-556); [bp-557](#bp-557); [bp-565](#bp-565); [bp-568](#bp-568).

```lean
theorem cofinalNoCancellation_of_P1_P2_P3 (h1 : P1) (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

<a id="bp-570"></a>
#### bp-570 — `AdalyFormal.Round13.Assembly.R1.CofinalPhysicalInputs`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4438`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:393`: `'AdalyFormal.Round13.Assembly.R1.CofinalPhysicalInputs' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-152](#bp-152); [bp-221](#bp-221).

```lean
def CofinalPhysicalInputs : Prop
```

<a id="bp-571"></a>
#### bp-571 — `AdalyFormal.Round13.Assembly.R1.cofinalRightStarCurlLine_of_cofinalPhysical`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4452`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:394`: `'AdalyFormal.Round13.Assembly.R1.cofinalRightStarCurlLine_of_cofinalPhysical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-227](#bp-227); [bp-559](#bp-559); [bp-560](#bp-560); [bp-568](#bp-568); [bp-570](#bp-570).

```lean
theorem cofinalRightStarCurlLine_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    CofinalRightStarCurlLine
```

<a id="bp-572"></a>
#### bp-572 — `AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalPhysical`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R1_Spine.lean:4468`.
- **Status:** B — builder/publication compiled only. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R1_Spine.lean.log:397`: `'AdalyFormal.Round13.Assembly.R1.cofinalNoCancellation_of_cofinalPhysical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-176](#bp-176); [bp-564](#bp-564); [bp-570](#bp-570); [bp-571](#bp-571).

```lean
theorem cofinalNoCancellation_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

<a id="bp-573"></a>
#### bp-573 — `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:9667`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:67`: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:9667`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:67`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-551](#bp-551); [join-11](#join-11).

```lean
theorem goalNeg2_of_P2_P3 (h2 : P2) (h3 : P3) : GoalNeg2
```

<a id="bp-574"></a>
#### bp-574 — `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:9670`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:70`: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:9670`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:70`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-554](#bp-554); [join-11](#join-11).

```lean
theorem goalNeg2_of_cofinalP2P3 (h : CofinalP2P3) : GoalNeg2
```

<a id="bp-575"></a>
#### bp-575 — `AdalyFormal.Round13.Assembly.R2.p2`

Exact physical P2 integrated into the original predicate. This declaration meets the exact-P2 verification target gate.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11049`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:118`: `'AdalyFormal.Round13.Assembly.R2.p2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11049`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:118`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.p2' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-498](#bp-498).

```lean
theorem p2 : P2
```

<a id="bp-576"></a>
#### bp-576 — `AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine`

Unconditional original whole-kernel line, real nullity two and canonical crossing in \((0,\pi/2)\), at every admissible pair. This is verified progress, not a proof of P3 or GoalNeg2.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11050`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:120`: `'AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11050`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:120`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-227](#bp-227); [bp-430](#bp-430); [bp-498](#bp-498); [bp-560](#bp-560); [bp-568](#bp-568); [bp-575](#bp-575).

```lean
theorem rightStar_kernelLine {q R : ℕ} (hq : 0 < q)
    (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2
```

<a id="bp-577"></a>
#### bp-577 — `AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine`

The whole-kernel theorem with nested cofinal quantifiers. Its conclusion has no detection conjunct.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11061`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:86`: `'AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11061`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:86`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-576](#bp-576).

```lean
theorem cofinal_rightStar_kernelLine :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      0 < vacEdge (2^j) R (rightStar (by positivity) R) ∧
      vacEdge (2^j) R (rightStar (by positivity) R) < Real.pi/2 ∧
      ∃ u : TwistSpace (2^j) R,
        KernelLine (2^j) R (rightStar (by positivity) R) u ∧
        Module.finrank ℝ (vacA (2^j) R (rightStar (by positivity) R) 1
          (vacEdge (2^j) R (rightStar (by positivity) R))).ker = 2
```

<a id="bp-578"></a>
#### bp-578 — `AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_P3`

The original cofinal response-noncancellation premise follows conditionally from P3; not an unconditional inhabitant.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11075`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:75`: `'AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11075`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:75`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-551](#bp-551); [bp-575](#bp-575).

```lean
theorem cofinalNoCancellation_of_P3 (h3 : P3) : CofinalAnyPathNoResponseCancellation
```

<a id="bp-579"></a>
#### bp-579 — `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3`

Complete independently replayed implication P3 → pinned GoalNeg2. P3 is its sole hypothesis and remains open.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11077`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:112`: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11077`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:112`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-573](#bp-573); [bp-575](#bp-575).

```lean
theorem goalNeg2_of_P3 (h3 : P3) : GoalNeg2
```

<a id="bp-580"></a>
#### bp-580 — `AdalyFormal.Round13.Assembly.R2.CofinalP3`

Compiled supporting definition. For a Prop-valued definition, this does not assert an inhabitant.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11078`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`. Compiled definition only.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:73`: `'AdalyFormal.Round13.Assembly.R2.CofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11078`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:73`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.CofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** Exact displayed hypotheses and source-local/frozen background.

```lean
def CofinalP3 : Prop
```

<a id="bp-581"></a>
#### bp-581 — `AdalyFormal.Round13.Assembly.R2.cofinalP2P3_of_cofinalP3`

Conditional assembly reduction with every displayed input retained; no missing detection premise is discharged by this implication.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11083`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:83`: `'AdalyFormal.Round13.Assembly.R2.cofinalP2P3_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11083`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:83`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.cofinalP2P3_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-575](#bp-575); [bp-580](#bp-580).

```lean
theorem cofinalP2P3_of_cofinalP3 (h : CofinalP3) : CofinalP2P3
```

<a id="bp-582"></a>
#### bp-582 — `AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_cofinalP3`

The original cofinal response-noncancellation premise follows conditionally from nested CofinalP3, preserving the same indices.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11090`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:78`: `'AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11090`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:78`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-554](#bp-554); [bp-580](#bp-580); [bp-581](#bp-581).

```lean
theorem cofinalNoCancellation_of_cofinalP3 (h : CofinalP3) :
    CofinalAnyPathNoResponseCancellation
```

<a id="bp-583"></a>
#### bp-583 — `AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3`

Complete independently replayed implication CofinalP3 → pinned GoalNeg2. The nested detection premise remains open.

- **Source:** `AHP/round13/shared/assembly/R2_P2Goal.lean:11093`.
- **Status:** A — compiled and independently replayed. Recorded exit: `0`.
- **Axioms:** `AHP/round13/shared/assembly/R2_P2Goal.lean.log:115`: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:11093`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:115`, exit `0`; record: `'AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Direct blueprint inputs:** [bp-574](#bp-574); [bp-580](#bp-580); [bp-581](#bp-581).

```lean
theorem goalNeg2_of_cofinalP3 (h : CofinalP3) : GoalNeg2
```

### Supporting declarations without an individual axiom print

These eight declarations occur in clean compiled sources (including seven in the independently replayed P2Goal source), but no individual axiom record was requested for them. They are not assigned A/B declaration acceptance or a proof marker here. This is an evidence-granularity limitation, not an additional P1/P2/P3 hypothesis; the accepted final theorems have their own complete dependency prints. No axiom line is invented.

- `AdalyFormal.Round13.Positivity.plaqEnergy` (def): `AHP/round13/shared/assembly/R2_P2Goal.lean:9846`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.omittedEnergy` (def): `AHP/round13/shared/assembly/R2_P2Goal.lean:9883`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.Leaves.leaf` (def): `AHP/round13/shared/assembly/R2_P2Goal.lean:10254`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.Leaves.code` (def): `AHP/round13/shared/assembly/R2_P2Goal.lean:10263`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.Leaves.transverse_sizes` (theorem): `AHP/round13/shared/assembly/R2_P2Goal.lean:10265`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.Leaves.right_coord` (theorem): `AHP/round13/shared/assembly/R2_P2Goal.lean:10269`; individual axiom line: **none**.
- `AdalyFormal.Round13.Positivity.Leaves.leafSet` (def): `AHP/round13/shared/assembly/R2_P2Goal.lean:10322`; individual axiom line: **none**.
- `AdalyFormal.Round13.Detection.Transfer.area` (def): `AHP/round13/shared/detection/R1_Transfer.lean:56`; individual axiom line: **none**.

## Current physical frontier — P1/P2 closed; P3 open

The following types use the original namespace openings from the cited NOTES. `rightStar` is the consistently RIGHT family, `KernelLine` is the original whole-kernel predicate, and `vacA`/`vacEdge` are the original actual operators. No declaration with a proof hole is introduced. Former O1/O2 labels are retained as closed cross-references; their proof markers live only on their named declaration nodes.

### O0 — cofinal response noncancellation remains open

**O: no inhabitant is known.** The compiled predicate at `AHP/round10/shared/assembly/R4_ResponseHull.lean:2550` is not a proof of the following nested assertion:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
    AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
    (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
    NoResponseCancellation (2^j) R V
```

The right-star path clauses are proved. P1 and P2 now also hold at every admissible pair, and the whole crossing kernel is a charged line. Its actual response still has to be detected. The repaired [join-11](#join-11) compiles the implication from this premise to GoalNeg2; it does not prove the premise.

### P1 / former O1 — CLOSED, status A

The exact original half-pi statement is proved by [bp-430](#bp-430), `AdalyFormal.Round13.Trial.rightStar_negative_halfpi`, at `AHP/round13/shared/trial/R1_Trial.lean:2180`, axiom record `AHP/round13/shared/trial/R1_Trial.lean.log:228`. Independent replay: `AHP/round13/trial/r1/Trial.verify.lean:2180`, log line `AHP/round13/trial/r1/Trial.verify.lean.log:228`, exit 0.

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

The periodic six-bond embedding, exact full mass \(21/16\), zero higher blocking rows, \(T=0\), \(W=I\) and all nineteen touched plaquettes are proved. [bp-429](#bp-429) gives actual energy \(-1/4\). The R2 handoff [bp-437](#bp-437) keeps the path and trial at the same nested indices; [bp-434](#bp-434) gives the trial Rayleigh quotient \(-4/21\), not an eigenvalue. This obligation is no longer a numerical or finite-enumeration gap.

### P2 / former O2 — CLOSED, status A

The exact full-carrier statement is proved by [bp-498](#bp-498), `AdalyFormal.Round13.Positivity.Physical.rightStar_P2`, at `AHP/round13/shared/positivity/R2_P2.lean:3490`, log `AHP/round13/shared/positivity/R2_P2.lean.log:203`. Independent replay: `AHP/round13/positivity/r2/P2.verify.lean:3490`, log `AHP/round13/positivity/r2/P2.verify.lean.log:203`, exit 0.

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
```

The complete omitted sum is controlled, including curved exterior plaquettes with zero supported input. Eight distinct actual leaves pay the four arm losses once, with the neutral square retained. The actual full form is bounded below by \(\cos t\) times the genuine positive localized form ([bp-495](#bp-495)). Every strict closed prefix has relative factor \(\cos T>0\) ([bp-497](#bp-497)); no strict half-pi endpoint assertion or uniform ordinary-norm gap is claimed. P1, P2, continuity, positive start and gauge invariance are all integrated in [bp-576](#bp-576): the original whole-kernel line, real nullity two, and canonical crossing in \((0,\pi/2)\) are unconditional.

### P3 / O3 — detection at the same canonical crossing remains open

**O: no detection proof is supplied.** This is the original P3, now also the compiled proposition definition `AdalyFormal.Round13.Assembly.R1.P3` at `AHP/round13/shared/assembly/R1_Spine.lean:3405` ([bp-557](#bp-557)):

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The premise now has an actual whole-kernel generator at every admissible pair; it is not a vacant conditional. The full flat N-unit prerequisite is discharged by [bp-502](#bp-502), so actual TopJetDetected suffices without another inverse guard. Chargedness, a nonzero central coordinate, or nullity two does not establish quadratic noncancellation. The exact area dictionary below identifies the missing quantity, not its nonvanishing.

### O4 — cofinal detected-line alternative remains open

**O: the detection conjunct is not proved.** The existing predicate is `AdalyFormal.Round10.Assembly.R3.CofinalAnyPathCurlLine`, `AHP/round10/shared/assembly/R3_EnergyGlue.lean:2208`. For the now-constructed right-star lines, the missing existential detected family is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

The line conjunct alone is now proved by [bp-577](#bp-577). Round 12 already gives the direct implication to O0 without RegularityFacts ([bp-234](#bp-234)); the downstream goal integration is now repaired. The line and detected vector must be the same, at the same path, scale, radius and canonical crossing. No left/right reflection or intersection of unrelated cofinal subsequences is used.

### O5 — weaker nested detection-only premise remains open

**O: a compiled definition is not an inhabitant.** `AdalyFormal.Round13.Assembly.R2.CofinalP3`, `AHP/round13/shared/assembly/R2_P2Goal.lean:11078`, has the exact body:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∀ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u
```

All-instance P1 and P2 apply at whichever indices this premise selects. [bp-583](#bp-583) proves the complete implication from this premise to GoalNeg2, without further physical or regularity hypotheses.

### O6 — actual weighted mixed-color area nonvanishing remains open

**O: sufficient input for the top-jet route, not a proved estimate.** With the original DilatedFlux and the new PhysicalArea namespaces opened, it is sufficient to prove:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The weaker nested sufficient family is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) R,
      areaSum (by positivity : 0 < 2^j) hk u ≠ 0
```

The actual coefficients are defined by masked two-bond inputs to the full interior W/C2 operators, not a guessed stencil. `crossing_physicalJetAggregate_area` at `AHP/round13/shared/detection/R2_PhysicalArea.lean:4400` proves the exact factor-one-half identity, with permitted record at `AHP/round13/shared/detection/R2_PhysicalArea.lean.log:444`. It does not establish a sign, nonzero seed, physical recurrence preserving the weighted sum, or absence of cancellation. A nonzero linear trace or one nonzero determinant is insufficient.

### Alternative leaves retained, not silently assumed

The older positive-kernel, exact two-mode/Schur, source-family, scalar recurrence/transfer and moving-root polynomial routes are conditional alternatives, not additional proved facts. Their exact assumptions are retained in the ledger's Lean signatures and direct source citations. The preferred adaptive route bypasses source-column and Bloch-normalization obligations, but does not prove those older dictionaries. No exact physical MovingRootCertificate, fixed transfer representation, or certified nonzero seed is supplied. There is **no numerical certificate** of any such representation. The positive alternatives need a class-uniform inverse-relative boundary-return bound or exact common-profile invisibility; localized coercivity and a small absolute correction do not give that bound.

## Retained numerical evidence — never proof, even where Lean now closes the input

All values below were checked against retained data/summary files, not recomputed. They are floating-point evaluations, not directed-rounding intervals, certified spectral enclosures, a Lean stencil/DFT identification or a proof of cofinality. Schur eigenvalues are **not** eigenvalues of the full carrier. In the right-star reconstruction the vector has unit nine-boundary-bond norm, not unit full-carrier norm; these numerical vectors are not silently identified with a normalized Lean crossing witness.

| Open input | Instance, precision | Values and exact evidence file |
|---|---|---|
| P1: half-pi trial (now closed by Lean) | right star, \((q,R)=(2,20),(4,22),(8,24)\), 130 decimal digits | Six supported bonds, nineteen touched plaquettes: mass \(21/16\), untouched energy \(15/16\), star contribution \(-5/2\), total \(-1/4\). Without the tangent bond: \(5/4+3/4-2=0\). **AHP/round12/kernel/r2/TRIAL_CHECKS.json**, tests produced by **trial_crosscheck.py** in that directory. This retained finite stencil check is not a proof; the separate round-13 physical carrier theorem now proves the exact energy. |
| P2: zero-coordinate positivity (now closed below half pi) | right star, \(q=2,R=20\), all 64 characters, 120/155 digits | Root \(1.20803053753475603036\); next charged Schur eigenvalue \(0.9318300997626865\); neutral minimum \(1.123232889837102\); central-zero Schur minima at crossing/half-pi \(0.9317026596031793\) / \(0.5850260655789722\). **AHP/round12/kernel/r2/NUMERICS.json**, raw **star_right_q2_R20_p120.json**, **star_right_q2_R20_p155.json**. Sampled positivity remains evidence only; the separate round-13 proof establishes P2 for every angle strictly below half pi and every required field. |
| O3: same-crossing detection | same right-star runs, 120/155 digits | Adjacent top-layer sums in directions 0/1/2: \(-1.72163155\cdot10^{-76}\), \(3.76958628\cdot10^{-75}\), \(3.76958609\cdot10^{-75}\). Tangential relative differences below \(3.66\cdot10^{-113}\); null residual \(6.76444\cdot10^{-155}\), flat-solve residual \(1.91375\cdot10^{-151}\), phase/scale error \(5.71847\cdot10^{-151}\). Same **NUMERICS.json** and raw files. Tiny stable values are not exact nonzero Lean aggregates. |
| O0/O4: a second scale/radius, not cofinality | separately assembled left and right stars, \(q=1,R=20\), 90/120 digits | Root \(1.207987856419019\), next charged Schur value \(0.932012806276\), central-zero minimum \(0.931888514752\). Right tangential sums about \(3.50188783\cdot10^{-44}\); left about \(3.63040925\cdot10^{-44}\). **AHP/round12/kernel/r1/NUMERICS_SUMMARY.json**. No reflection equivalence is used. |
| O3, older candidate only | left star, \(q=1,R=18\), independent 60/80 digits | Top aggregates approximately \(1.00872731\cdot10^{-41}\), \(4.87537241\cdot10^{-40}\), \(4.87537243\cdot10^{-40}\); 80-digit solve residual \(1.1478\cdot10^{-76}\). **AHP/round12/noncancel/r1/starjet_q1_R18_p60.json**, **starjet_q1_R18_p80.json**. These belong to the left star, not the formally validated right-star family. |
| Older free-profile / scalar nonvanishing alternatives | left-only twist, \(q=2,R=28\), character \((7,7)\), 180/230/240 digits | Canonical coupling \(-5.8623291978252373\cdot10^{-108}\); scaled adaptive energy \(13.986375324657497\); restored cell-normalized adaptive coupling \(3.0182306458776947\cdot10^{-214}\); 230/240 agreement 214.50 relative digits for the coupling. **AHP/round10/assembly/r4/numerics/SUMMARY.json**. This is selected-vector, not whole-kernel or physical-normalization certification. |
| Older positive-kernel shortcut and either-sign separation | symmetric twist, \(q=2,R=18,\varepsilon=10^{-100}\), 400/500 digits | Kernel correction \(-1.8124680628969907\cdot10^{-170}\); corrected-minus-carrier crossing displacement \(+5.797\cdot10^{-171}\), 227.4 relative digits of shift agreement. **AHP/round8/guarded-idea/IDEA.md:321** and **numerics/out/agree_q2_R18_e1e-100_p400_p500.json**. Negative sign opposes the old all-positive pairing route, not the guarded refutation mechanism. |

There is no finite numerical evidence that can by itself discharge the unbounded nested quantifiers. The integration joins below are compiler obligations, so no numerical values are evidence for their elaboration. There is no new numerical evidence for the round-11 unrestricted large-mass positivity premise; that separate-pin question is not an open input on the shortest guarded route.



Detection R1 additionally re-read the retained right-star q2R20 reports at 120/155 digits: \(\max|\mathrm{cell}|/|\mathrm{sum}|\) is approximately 27.066899, 1.628277, 1.628408 in directions 0/1/2 (`AHP/round13/detection/r1/AUDIT.json`). Ratios greater than one indicate mixed cell signs at those precisions, defeating the naive common-cell-sign strategy at the evidence level. They neither refute P3 nor certify weighted aggregate nonvanishing. No new numerical solve was performed for this blueprint.

## Historical goal joins — repaired round-13 copies now compiled

The original `AHP/round10/assembly/r4/Attempt.coord.lean` and its failed exit-1 log remain unchanged (1183 reports, including 15 nonstandard dependency reports). They remain C-broken artifacts. Assembly R1 copied the source and inserted the three missing verbatim helpers `half_twice`, `half_average`, and `phase_axis_fixed`; its **single** `AHP/round13/assembly/r1/RepairedJoin.lean` execution exited **0** with **1186 permitted records**. The insertion and current source/log hashes were rechecked read-only. No repair compile was repeated here.

The status below belongs to the repaired round-13 source, not to a relabelled historical failure. Ten joins are B; the original final response-to-goal bridge also has an identical, individually printed independent R2 replay and is A. All goal arrows remain conditional on their displayed cofinal inputs.

<a id="join-1"></a>
### join-1 — `AdalyFormal.Round10.Assembly.R2.goalNeg2_of_cofinalDominatedSource`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:13940`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1467`: `'AdalyFormal.Round10.Assembly.R2.goalNeg2_of_cofinalDominatedSource' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [bp-126](#bp-126) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling`); [bp-320](#bp-320) (`AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_dominatedSource`).

```lean
theorem goalNeg2_of_cofinalDominatedSource (h : CofinalDominatedSource) : GoalNeg2
```

<a id="join-2"></a>
### join-2 — `AdalyFormal.Round10.Assembly.R2.goalNeg2_of_cofinalSourceFamily`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:13943`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1464`: `'AdalyFormal.Round10.Assembly.R2.goalNeg2_of_cofinalSourceFamily' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [bp-126](#bp-126) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling`); [bp-158](#bp-158) (`AdalyFormal.Round10.Assembly.R2.cofinalAnyProfileCoupling_of_sourceFamily`).

```lean
theorem goalNeg2_of_cofinalSourceFamily (h : CofinalSourceFamily) : GoalNeg2
```

<a id="join-3"></a>
### join-3 — `AdalyFormal.Round10.Assembly.R3.regularityFacts`

The historical join specializes already proved arbitrary-profile interior continuity, the constraint limit and the correction derivative to the compact RegularityFacts interface.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15479`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1695`: `'AdalyFormal.Round10.Assembly.R3.regularityFacts' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [bp-115](#bp-115) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_H_cont`); [bp-116](#bp-116) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.bulk_C2_tendsto`); [bp-117](#bp-117) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.hasDerivAt_corrDeriv`).

Direct local input: AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible (AHP/round4/guarded/refute-r1/Attempt.lean:1024).

```lean
theorem regularityFacts : RegularityFacts
```

<a id="join-4"></a>
### join-4 — `AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form_all`

After specializing regularity, the actual correction derivative quadratic form equals the physical flat source/jet profile coupling for every profile.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15485`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1696`: `'AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form_all' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-3](#join-3); [bp-161](#bp-161) (`AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form`).

```lean
theorem corrDeriv_profile_form_all {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u
```

<a id="join-5"></a>
### join-5 — `AdalyFormal.Round10.Assembly.R3.flatConstraintUnits`

The historical join specializes flat localized well-definedness to the two genuine flat constraint inverse guards needed by physical top-jet detection.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15509`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1701`: `'AdalyFormal.Round10.Assembly.R3.flatConstraintUnits' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** The direct local source inputs listed next.

Direct local inputs: AdalyFormal.Round9.Guarded.AnalyticR2.dil_N0_unit (AHP/round9/analytic-r2/Attempt.lean:6764); AdalyFormal.Round9.Guarded.AnalyticR2.dataFam_dil_zero (AHP/round9/analytic-r2/Attempt.lean:6737); AdalyFormal.Round4.Guarded.RefuteR1.dil_admissible (AHP/round4/guarded/refute-r1/Attempt.lean:1024). Clean builder axiom records: AHP/round9/analytic-r2/Attempt.lean.log:591 and :587; AHP/round4/guarded/refute-r1/Attempt.lean.log:133. All three list exactly [propext, Classical.choice, Quot.sound].

```lean
theorem flatConstraintUnits : FlatConstraintUnits
```

<a id="join-6"></a>
### join-6 — `AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalCurlLine`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15490`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1697`: `'AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalCurlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-3](#join-3); [bp-126](#bp-126) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling`); [bp-321](#bp-321) (`AdalyFormal.Round10.Assembly.R3.cofinalAnyProfileCoupling_of_curlLine`).

```lean
theorem goalNeg2_of_cofinalCurlLine (h : CofinalCurlLine) : GoalNeg2
```

<a id="join-7"></a>
### join-7 — `AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalAnyPathCurlLine`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15493`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1698`: `'AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalAnyPathCurlLine' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-3](#join-3); [bp-130](#bp-130) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling`); [bp-164](#bp-164) (`AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCoupling_of_curlLine`).

```lean
theorem goalNeg2_of_cofinalAnyPathCurlLine (h : CofinalAnyPathCurlLine) : GoalNeg2
```

<a id="join-8"></a>
### join-8 — `AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalJetLine`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15515`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1702`: `'AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalJetLine' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-5](#join-5); [join-6](#join-6); [bp-322](#bp-322) (`AdalyFormal.Round10.Assembly.R3.cofinalCurlLine_of_jetLine`).

```lean
theorem goalNeg2_of_cofinalJetLine (h : CofinalJetLine) : GoalNeg2
```

<a id="join-9"></a>
### join-9 — `AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalAnyPathJetLine`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15518`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1703`: `'AdalyFormal.Round10.Assembly.R3.goalNeg2_of_cofinalAnyPathJetLine' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-5](#join-5); [join-7](#join-7); [bp-165](#bp-165) (`AdalyFormal.Round10.Assembly.R3.cofinalAnyPathCurlLine_of_jetLine`).

```lean
theorem goalNeg2_of_cofinalAnyPathJetLine (h : CofinalAnyPathJetLine) : GoalNeg2
```

<a id="join-10"></a>
### join-10 — `AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalNoResponseCancellation`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15895`.
- **Status:** B — builder-compiled repaired copy. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1764`: `'AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalNoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Blueprint inputs:** [join-3](#join-3); [bp-126](#bp-126) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyProfileCoupling`); [bp-323](#bp-323) (`AdalyFormal.Round10.Assembly.R4.cofinalAnyProfileCoupling_iff_noCancellation`).

```lean
theorem goalNeg2_of_cofinalNoResponseCancellation
    (h : CofinalNoResponseCancellation) : GoalNeg2
```

<a id="join-11"></a>
### join-11 — `AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation`

The historical assembly combines the named cofinal sufficient premise with regularity and the previously compiled reduction/goal bridges to conclude the pinned negative headline. It does not prove its cofinal premise.

- **Source:** `AHP/round13/assembly/r1/RepairedJoin.lean:15900`.
- **Status:** A — compiled and independently replayed. Whole-file exit `0`; historical C-broken status is superseded only for this copy.
- **Axioms:** `AHP/round13/assembly/r1/RepairedJoin.lean.log:1767`: `'AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`. This record belongs to the clean repaired compilation.
- **Independent replay:** `AHP/round13/assembly/r2/P2Goal.verify.lean:6781`, identical declaration body; `AHP/round13/assembly/r2/P2Goal.verify.lean.log:62`, exit `0`; record: `'AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Blueprint inputs:** [join-3](#join-3); [bp-130](#bp-130) (`AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling`); [bp-177](#bp-177) (`AdalyFormal.Round10.Assembly.R4.cofinalAnyPathCoupling_iff_noCancellation`).

```lean
theorem goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (h : CofinalAnyPathNoResponseCancellation) : GoalNeg2
```

### O-target — no theorem proving GoalNeg2

Existing definition: `AdalyFormal.Round2.Guarded.Pin.GoalNeg2`, `AHP/round3/guarded/pin/Statement.lean:158`. **O:** no inhabitant or proof axiom record is supplied. The shortest remaining input is P3 or CofinalP3, followed by the now independently replayed complete goal implication. O0 remains an alternative sufficient premise; regularity integration is no longer an open compiler task. Compiling this definition or a theorem with O0 as an explicit argument does not prove the proposition.

## Audit snapshot

594 accepted declaration nodes: the inherited 340, all 243 individually printed round-13 names, and 11 repaired historical joins. Categories: 331 A and 263 B. Eight additional source-only helpers have no individual axiom print and no proof marker. P1/P2 are closed; P3, cofinal noncancellation/detected-line alternatives and GoalNeg2 remain open. Static audit passed: 602 unique labels, 1104 acyclic named dependency edges, 2620 distinct valid file:line citations, and all 594 proof markers matched permitted individual records in clean exit-0 logs. All 331 A-node replay bodies/records, 134 source/log hashes, and 18 local/publication byte-identical pairs were checked. All 251 round-13 names across 43 Lean sources are accounted for. TeX environment, brace and math-delimiter checks passed. This is a read-only source/log audit: no Lean elaboration, numerical solve, TeX/PDF build, commit or push was performed. Source/log hashes below pin the inspected artifacts; all original round-12 artifacts remain unchanged.

| Source | Source SHA-256 | Checked log | Log SHA-256 |
|---|---|---|---|
| `AHP/round3/guarded/pin/Statement.lean` | `0a06554ee453ebf71782165723546c7fbb8f69b143a004f7d7c4c39deb53dad7` | `AHP/round3/guarded/pin/Statement.lean.log` | `607a2a98901312fe87fe03a04388faf3f7ebc637194efc144b39f0bd26b594b9` |
| `AHP/round2/guarded/r2-prove/Attempt.lean` | `183d253712e04e4ccbfd13a0a367e4d6ba368bfd840230e7a4f595a0b2c4f949` | `AHP/round2/guarded/r2-prove/Attempt.lean.log` | `e19f8e6727158ec495215fd19c05529e950f60857b79b9dbdaaf3a5ca7188f06` |
| `AHP/round3/guarded/r3-prove/Attempt.lean` | `0784988b5252fe245c8b1773218d21b2a96b324ed4d8234ac878eca10357ae3f` | `AHP/round3/guarded/r3-prove/Attempt.lean.log` | `cd6c40d107a40c21c18135732fa35271031826233c70f3374ff47110d1af37c7` |
| `AHP/round4/guarded/refute-r1/Attempt.lean` | `df30c794c74bda3d1fbbc66c8cf13bcd1b0045d29a0a07cd78733e4bb4b735e1` | `AHP/round4/guarded/refute-r1/Attempt.lean.log` | `d6313562dfb8e3a257abd337c335404fe63f5d5c99116abef50c3f51e2e160f6` |
| `AHP/round4/guarded/gap-r1/Check3.lean` | `efa8a63101212eaedb1f771224ee8fe795e39000f8bf2b86bd7d5781784784c6` | `AHP/round4/guarded/gap-r1/Check3.lean.log` | `fa761a3190f3a5113163188e667c3a463895690cd8b7f5fbf87412aa05b1e66d` |
| `AHP/round4/guarded/decay-r1/Attempt.lean` | `7f15254dbc50ab07da276c1e22bbbfdbefe5f9629eda9fcc61d583bb3d9c0164` | `AHP/round4/guarded/decay-r1/Attempt.lean.log` | `9de3c957c4f885b3c230184ac14299b90dd3bc57664970040e0c8fafb5c325c7` |
| `AHP/round5/guarded/structural-r1/Attempt.lean` | `7d42aa1e1d15a3f1c816576babead3197ba0c4543c706e36c52096e7af108f18` | `AHP/round5/guarded/structural-r1/Attempt.lean.log` | `46f19606d8e524b00b3509f810beb46c2e3c2359175f91aec9c5b58a4b03b997` |
| `AHP/round5/guarded/ivt-r2/Attempt.lean` | `b95973c476baecbdbce5ca1c04c414ae7bfb4388f1bda17a9b4dfb6e0532dd99` | `AHP/round5/guarded/ivt-r2/Attempt.lean.log` | `42317e068200ade1311e6c29d7f63ad89b04edc747819c94a2bd3c46f04b4f89` |
| `AHP/round5/guarded/kernel-r2/Attempt.lean` | `600d01a0b80ae6e6eeb7d4a9d991c7cd24a637f614c8f7ea7e9259d9c8a165f7` | `AHP/round5/guarded/kernel-r2/Attempt.lean.log` | `90d979e3105ebf97a4291c805b4881050236d2085d10be42ef2519437caa1b8a` |
| `AHP/round6/closedform-r1/Attempt.lean` | `2849fe7e047e040fb9675a280beeff39e2a3cee4c4856e487058056d2a7e571d` | `AHP/round6/closedform-r1/Attempt.lean.log` | `5aaf2ba180a725b5edcba4ac9dd6a26c27017280d09f6df14858a22d0a191d14` |
| `AHP/round6/limits-r2/Attempt.lean` | `43c3bd051cf4ec664e8ba2d21d0bc0b7740f35ddf30a941e0fcc73eba258f34a` | `AHP/round6/limits-r2/Attempt.lean.log` | `691b54df662f5624443e5ff07e0a59a83bae4abda49277a37de5774e3d728a3f` |
| `AHP/round6/placement-r1/Attempt.lean` | `840438cdf7b48ac936939cecae20e6ec5b9f999a0ebb1258241ad3b28755b674` | `AHP/round6/placement-r1/Attempt.lean.log` | `cbb7801974ceb731d07bd4e6a4cd4ec6d8b728c0b0a99e46c721070d83fc9dd7` |
| `AHP/round6/placement-r2/HybridCertificate.lean` | `222368e4321067368f84719fc682ee161c53db658c51188fe4e4b2ed6cfcef0f` | `AHP/round6/placement-r2/HybridCertificate.lean.log` | `d2e5617b5fc018d634e14ee5438d1343460eb41509441b7df1f2d863eaef1843` |
| `AHP/round8/guarded-idea/Attempt.lean` | `65f16394b1e291d9eacb10339b01909c22327b855705b74f0b6ed36fc2492d15` | `AHP/round8/guarded-idea/Attempt.lean.log` | `cba691827e4514695f800334bf689c1844c718c2bf863617896a74394b777892` |
| `AHP/round9/analytic-r2/Attempt.lean` | `52614e742421836020e394fd93c21b9696d6db0be2b3b87688ecf63b0de144b9` | `AHP/round9/analytic-r2/Attempt.lean.log` | `948f34e210a83266bbed6190c71891f93b4c1d1919047ad3d114da27cf81dfd1` |
| `AHP/round9/qualitative-r2/Attempt.lean` | `b6dc8553ad1b8a7fdc5ff731b5c7df0fde0009979bdc90dbaba23b10efc5d052` | `AHP/round9/qualitative-r2/Attempt.lean.log` | `ecec4700816494dff17f2104fb52ca55dc59d4b153dd7a8f16dc1ab1983b120e` |
| `AHP/round10/shared/assembly/R1_Cofinal.lean` | `7a12e13c59dd6eb512a3d58d099722fecad904c51f3b7d364ab379c3cd5e63b0` | `AHP/round10/shared/assembly/R1_Cofinal.lean.log` | `195d73dd0e165d1d4c4c9f5bef0f4dc36da68db9749f906bc077ac98a61e8f4c` |
| `AHP/round10/shared/assembly/R3_EnergyGlue.lean` | `f967e7a62f1b8be0a05cf01e6008c03411bdd18f809036a5253788b0f2a02d6f` | `AHP/round10/shared/assembly/R3_EnergyGlue.lean.log` | `b347387342e0639a2825ff88e0b13422ee9273a7631fa738df5229c0e6de77ff` |
| `AHP/round10/shared/dictionary/R1_Dictionary.lean` | `8addcf951497b1468f852bacfcddee99fda29012186da0e97ac36f4922940148` | `AHP/round10/shared/dictionary/R1_Dictionary.lean.log` | `c1301b19c104c0cfcc02d1a9ccda43f022689f61a444f5c5bed1238e2c66e9bd` |
| `AHP/round10/shared/dictionary/R3_JetDetection.lean` | `9666e5c617ae2aadd466fbdaff9e9b58c2811e0c59777c98fd4af94a821321ba` | `AHP/round10/shared/dictionary/R3_JetDetection.lean.log` | `1dd26835b57e30c0de54f05fd6b4e205a7fd0e734bd0159261e2a20daf8e3ea5` |
| `AHP/round10/shared/assembly/R3_JetGlue.lean` | `20242d7d339eb9087440a02c67a1ac0c05077cb08ef7b88059f06607990419c4` | `AHP/round10/shared/assembly/R3_JetGlue.lean.log` | `508a7341a8939f5b3e684ff429144ed27dc04589fb92b62c921f289b596a8172` |
| `AHP/round10/shared/assembly/R2_SourceGlue.lean` | `822ac629d717a7e6041d60e3a8957448d88d0aaf6dbdaff7931de933b5907eb4` | `AHP/round10/shared/assembly/R2_SourceGlue.lean.log` | `867bbabb4442edb9197216688d42b76b2f8e130f6b53f06abbfc1e7e9dbf6c75` |
| `AHP/round10/shared/assembly/R4_ResponseHull.lean` | `581a5ad1d5999bde9791a96279bbbbac0c625560e52bda9f32f293e148b61c12` | `AHP/round10/shared/assembly/R4_ResponseHull.lean.log` | `84c19dafd81e34561b7a3262ad6bf2c391da16021e3fec1adfef4fdae422760f` |
| `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean` | `1e9baedfa9d80f366b0ea1c3bbe4bc4a5a2b2b11d9ad46a1d28989346ccc1679` | `AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean.log` | `81c23a5ea8fc98dd7bedd03f0d6e61e2ed200d4f3f4d0d2d8eb31443f983dda3` |
| `AHP/round10/shared/dictionary/R4_ColorResponse.lean` | `73a98acef49c0db5eee733b1bbf15ab48dc99f8794e969e51ce3bbc67c311f02` | `AHP/round10/shared/dictionary/R4_ColorResponse.lean.log` | `c430d22878b312469343640e3ebbc5f9c34a88953e233876a40cf3fa86796501` |
| `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean` | `d5384411a01d1a646f6035cbe159bd6dbc3918d7c1e96b74a7f78a69de221757` | `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean.log` | `a07d305814ffccef4d67901afe5bb780bb9f01dfcf8dd12cf79093ef7b9406b1` |
| `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean` | `e7b1514878c58e8f20b07fce502cf5a087c9e9461c40e88279ed15def340d464` | `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean.log` | `7f0f943129880c1dcbfa02d3acd69d8affcc470fed6149de217bd59e40738e49` |
| `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean` | `4462d0322ed5381b0d6436daf90285dd943ff102bdd41bf2fb8cf88118ff2966` | `AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean.log` | `c5fa041a503273c6984c6d3c975ebb79b1df9b2347414c833e0b4763ec728797` |
| `AHP/round12/shared/noncancel/R1_Star.lean` | `5754fb31d94f89ff3a5860f7bab10a3f05d2a080a138f06371a6662b5db2bb12` | `AHP/round12/shared/noncancel/R1_Star.lean.log` | `b72ad3b5f762eae76dd17294c0a8b2c141a2e18a6da32155249c2512f77c26a8` |
| `AHP/round12/shared/noncancel/R2_Boundary.lean` | `3c790eae0be27c2ff45ca498ff6ec33a8475e0b83433f986ef3ad20a1632a910` | `AHP/round12/shared/noncancel/R2_Boundary.lean.log` | `bf37ce27c92ddde4b34b35dd03f38e160de32f7d17d88f14f629887d1f856f4e` |
| `AHP/round12/shared/noncancel/R2_FullPlaquette.lean` | `55f109b21206ea74258b339f964ea02d3ecc108b8722349e82ed9a48a1a5d19c` | `AHP/round12/shared/noncancel/R2_FullPlaquette.lean.log` | `70d516a7301df9271ee9b4a40a25862a47df0d00711ac1db792d166d15ccfb5f` |
| `AHP/round12/shared/noncancel/R2_Mass.lean` | `4c29e43be2de023705639c6ed7ebd47e6e01719a1cfdece7dab6a08ba6178cf8` | `AHP/round12/shared/noncancel/R2_Mass.lean.log` | `f1b65d4a038158d2939816c2a78954623a7ac63121d344b0be892665710e3156` |
| `AHP/round12/shared/noncancel/R2_RightFamily.lean` | `53dd048a1fd668e42110ce58fd83f7a05bdbebf8c57d87ffc45dcc7d6b37de17` | `AHP/round12/shared/noncancel/R2_RightFamily.lean.log` | `4334f93c6b1c7688803f321bf9bfcd66a74c0dfd43c538aeae68fba2e1812da4` |
| `AHP/round12/shared/kernel/R1_ActualKernel.lean` | `374f196e2a5ff24604d121c336725d58ef54009d738e56155d21be5f6be547f8` | `AHP/round12/shared/kernel/R1_ActualKernel.lean.log` | `48ef2246108b4158db63fb169d7c2e5d3478f16f254358a9f21872ff0c73d7d2` |
| `AHP/round12/shared/kernel/R2_FirstCrossing.lean` | `11eb1086b9c6b0f1434e3729abcdae395807e746e135ef1d2fda40e712d928a6` | `AHP/round12/shared/kernel/R2_FirstCrossing.lean.log` | `55ba5307b741269225958bf5e51d1c9daf06a009b29dc7e9eb1a290af49c1511` |
| `AHP/round12/shared/kernel/R2_ResponseLine.lean` | `dbad5f2268a5d46b66f1f8f96852432813ea3517289baf4d88db4d80491b854a` | `AHP/round12/shared/kernel/R2_ResponseLine.lean.log` | `4eaf7f0506680eb11de39c3c9bb358ced07703ccc91edca693ed1b0b2a7c2c0a` |
| `AHP/round11/refute-r1/Attempt.lean` | `a8f205f07752f718ebeb2ccdb58b784a2cd3e2c843592b97c9b52302ac46c1c7` | `AHP/round11/refute-r1/Attempt.lean.log` | `5dc81ad5a068908560f5af446107318b2c3ec5f6c2f492a575a75d5e539030bb` |
| `AHP/round11/refute-r2/Attempt.lean` | `1a0c6395528506e4f1165373215ece52ce002ed40131c66879df69f0c658ae69` | `AHP/round11/refute-r2/Attempt.lean.log` | `4dd9b9696ef4d7a62eb9adb6730cb465d86fae4103e7afc41aef24fae15a89c0` |
| `AHP/round11/largea-r2/Attempt.lean` | `25838972ed3189ff4f252f52c3f4525fe7429a56e1df00d32dd89c18a7ac5410` | `AHP/round11/largea-r2/Attempt.lean.log` | `7d266459295e03b99f295bfc22dfe7ba52f1ed53c7e04e05ae621469da7f46cb` |
| `lean/src/DrRed1.lean` | `06d80b55bddd3055a53d0478e7df68e3aa6b033179066087fff5014117c15a38` | `AHP/round4/guarded/mine/ChecksV3.lean.log` | `50f6cbf48a6ef002eb0f5f2b265cafbecf5866c4c1633baba93fdcb1885f06e7` |
| `lean/src/GdGap.lean` | `f40879635be84a21e68033fa4570e0955d197c635e7c2a7b771a60189b8b7337` | `AHP/round4/guarded/mine/ChecksV3.lean.log` | `50f6cbf48a6ef002eb0f5f2b265cafbecf5866c4c1633baba93fdcb1885f06e7` |
| `lean/src/GdGen4.lean` | `143b95c9b3942a817b540e4b3c3a4e01a1c70eb38bd3918dfc1ba0fc5f5fb0e7` | `AHP/round4/guarded/mine/ChecksV3.lean.log` | `50f6cbf48a6ef002eb0f5f2b265cafbecf5866c4c1633baba93fdcb1885f06e7` |
| `AHP/round10/shared/dictionary/R3_FreeSource.lean` | `6fb957329d43fc60ed65c6af8e36051b3c975c07ca223df21dd11aef2a9cccf1` | `AHP/round10/shared/dictionary/R3_FreeSource.lean.log` | `57ef68c294139e4013f6d9e8512510ff392a2b08af94cbfd54c309796f2e6a79` |

### Round-13 source and log hashes

| Source | Source SHA-256 | Checked log | Log SHA-256 |
|---|---|---|---|
| `AHP/round13/shared/assembly/R1_P1Spine.lean` | `0dcee35ec0b8fab4114cb8bb3e86305dd5300fd597f333eedfe331795ad98ef9` | `AHP/round13/shared/assembly/R1_P1Spine.lean.log` | `fa69fc20c4a8288bda3b139e5f5766766513deb7d8e7c87485819f2c7c73f5c6` |
| `AHP/round13/shared/assembly/R1_Spine.lean` | `77fc86766ead6856c7b64580ec3a2d066f6528cee0096df4f28b567ba096a7f3` | `AHP/round13/shared/assembly/R1_Spine.lean.log` | `393efe529640324ebec06b0395cdef55d39c3e884f7520ff395cf5541184f73e` |
| `AHP/round13/shared/assembly/R2_P2Goal.lean` | `da1b94df5c82e075316f3a90cba1086643e9174f19ed7963c850e975952334ef` | `AHP/round13/shared/assembly/R2_P2Goal.lean.log` | `c8bb4cdc907865a0b0303efcdf98d84f6a5aca84bd6e7ed87e9753f6ba6ce732` |
| `AHP/round13/shared/assembly/R2_PhysicalGoal.lean` | `4aff1df2c472feaf7e782fa15d213c64bb5bb52563e480f98f91c5967c03a6a7` | `AHP/round13/shared/assembly/R2_PhysicalGoal.lean.log` | `ae5f2f47a8a3b7815e7887123ad6f56603de07a905e46d1c03b397e60812ce4a` |
| `AHP/round13/shared/detection/R1_ColorTrace.lean` | `ff03b264d900317c1290512ead499c4f21e31f3a988de5908861af358d221cc2` | `AHP/round13/shared/detection/R1_ColorTrace.lean.log` | `ff9005b2bdbe6f05bd140fe68357db1ea36fcabe0445f560ead366d38bbc43f8` |
| `AHP/round13/shared/detection/R1_FlatUnit.lean` | `740a1929956b48d0a47c5b46b8428930b24d4fd9a1449eea0a403e8e411003d5` | `AHP/round13/shared/detection/R1_FlatUnit.lean.log` | `f0672353e6023331a622dd603a2135dd89dd3205e0e18d8cea9f303fd91342bb` |
| `AHP/round13/shared/detection/R1_JetBridge.lean` | `627d2c956a6909df679f43a76d05f9cb2ab3e7a2558c2332220b9aa84bb8eca8` | `AHP/round13/shared/detection/R1_JetBridge.lean.log` | `143806332263ec6492560dbd2350aa35d47ed3d92e5e804173b9bf10ad2a5b0d` |
| `AHP/round13/shared/detection/R1_Transfer.lean` | `7b2950ce0b22add01f631d1969c6c6812cf71d20d5f5b4026f31ddedd77ea51f` | `AHP/round13/shared/detection/R1_Transfer.lean.log` | `3e7ba58bf1a7ccc080a19e04e5fd1fcbf9a5f8ebf2ec8bf37871a78c17dbbb95` |
| `AHP/round13/shared/detection/R2_Area.lean` | `fa53aab5249181299452efb16021acd0ec1e99e8a770aa4d6dc2aad8e8a293af` | `AHP/round13/shared/detection/R2_Area.lean.log` | `0be15ea47869b9e38d676e6f4c030ab3d745c433c8287a971a1f8c82d08a431c` |
| `AHP/round13/shared/detection/R2_ColorArea.lean` | `4a805e091c6b39d96cd8376ee4ac39d625f71702913175ff93c81fa1951060b2` | `AHP/round13/shared/detection/R2_ColorArea.lean.log` | `099b76e569d657ba878ac45c08f196aee89a30aa61e3a8b564ed4b985fd73191` |
| `AHP/round13/shared/detection/R2_PhysicalArea.lean` | `863b70605847a88db05bb8111d30292bceb58d099ffb5afe6711612ce77a816e` | `AHP/round13/shared/detection/R2_PhysicalArea.lean.log` | `ba855ea289d65331b1c06c4da5b4949875bd702353dfea9c02f54c9cc9a24f0b` |
| `AHP/round13/shared/positivity/R1_EightLeaves.lean` | `f358b6bb8a14c68b49ea212b33756ccb0fa92134e936b62838c88f79375bed40` | `AHP/round13/shared/positivity/R1_EightLeaves.lean.log` | `e36fe78d66dff74ea186f5b1e9e229dc3d7449b9e951e18abd5d1c1e9b1fc429` |
| `AHP/round13/shared/positivity/R1_LocalPositive.lean` | `a44c47cea47e0cf638786fa7117809bbe8fc36c863ed0878960b50c4ee680d00` | `AHP/round13/shared/positivity/R1_LocalPositive.lean.log` | `842d779a97ed2ee4854301706aed4ad0c35d5e4b1cdb9b4051fc776095533e82` |
| `AHP/round13/shared/positivity/R1_MassAbsorption.lean` | `ee1b03fd81d2fb7ed8a161d4a6fdab7abfa7e51cd876bdc2b7340810123cec3a` | `AHP/round13/shared/positivity/R1_MassAbsorption.lean.log` | `a530c17cb2299f8ff4862c0721c68a9b682d237c8cd54e6e649876afa1e35272` |
| `AHP/round13/shared/positivity/R2_P2.lean` | `a0094e4a4a93d207bd4552d787ffd2434d0a463c498b426573f08dd286ed478c` | `AHP/round13/shared/positivity/R2_P2.lean.log` | `31c4125a4728c7a18564b23ff9a76faaaf5507be5f7cc76658ef4859182f29d5` |
| `AHP/round13/shared/positivity/R2_StarGeometry.lean` | `ffd042cabdf5e9ca377847cb4138e52a5aec5b58110aeaae81e465dc3e288976` | `AHP/round13/shared/positivity/R2_StarGeometry.lean.log` | `da6ce8794d221b641e8c55e4d04d274228a89a9bca014627b005d63b892bd8f6` |
| `AHP/round13/shared/trial/R1_Trial.lean` | `65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b` | `AHP/round13/shared/trial/R1_Trial.lean.log` | `755bde8a0fd57de60627a796567d1120754f4b959767c8af431470732b56908d` |
| `AHP/round13/shared/trial/R2_Trial.lean` | `01279668c4d8cc5c5c42e41963a9857fb2f8e69f1b195c88872e197211c86db8` | `AHP/round13/shared/trial/R2_Trial.lean.log` | `8ce76a29434cc41189ba35d7c8f50010d0bfe2157b52a3c3585fb16ec77092df` |
| `AHP/round13/assembly/r1/Spine.lean` | `7c5b7be462743d73f8b195ca31a1f3b2f6cd9c53104162bfcab429ae7be9394a` | `AHP/round13/assembly/r1/Spine.lean.log` | `789790adcc7d33ead8b310fb136146175d307f84820b5e512ac82cff739230b8` |
| `AHP/round13/assembly/r2/P2Goal.verify.lean` | `da1b94df5c82e075316f3a90cba1086643e9174f19ed7963c850e975952334ef` | `AHP/round13/assembly/r2/P2Goal.verify.lean.log` | `0f5fffc8d432dca477b3408c42b15e742d53128e4bd099a5cf35f6d6c1fe70fc` |
| `AHP/round13/positivity/r2/P2.verify.lean` | `a0094e4a4a93d207bd4552d787ffd2434d0a463c498b426573f08dd286ed478c` | `AHP/round13/positivity/r2/P2.verify.lean.log` | `31c4125a4728c7a18564b23ff9a76faaaf5507be5f7cc76658ef4859182f29d5` |
| `AHP/round13/trial/r1/Trial.verify.lean` | `65dea42e0daff27c8bc07bd850e1f2bdf8029e1fc452b0600590989df0039c9b` | `AHP/round13/trial/r1/Trial.verify.lean.log` | `66174f888fa524b06216877ff40e206d3c98c7d1ce7ed8e12a783861f948ed96` |
| `AHP/round13/trial/r2/Trial.verify.lean` | `01279668c4d8cc5c5c42e41963a9857fb2f8e69f1b195c88872e197211c86db8` | `AHP/round13/trial/r2/Trial.verify.lean.log` | `64b3f7405696ea2e6aa4c6fafddbfaced55002358766fa364cc874eef4fab5b4` |
| `AHP/round13/assembly/r1/RepairedJoin.lean` | `a25d71c4da93da0c87aa2d9f55764a7e0bb745022687a1b6429f3a0a75359fde` | `AHP/round13/assembly/r1/RepairedJoin.lean.log` | `c85143eef8614673169c78736c15329d648e1ae8d6beb5c16bae385a8dbc00bb` |

## Shortest remaining route to GoalNeg2

The shortest compiled route now has **one unproved physical input**:

\[
\boxed{\mathrm{P3}\ \text{(OPEN)}}
\ \xrightarrow{\text{round-13 complete compiled implication}}
\boxed{\mathrm{GoalNeg2}\ \text{(OPEN)}}.
\]

`AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3` at `AHP/round13/shared/assembly/R2_P2Goal.lean:11077` has exactly the elaborated type:

```lean
AdalyFormal.Round13.Assembly.R1.P3 → AdalyFormal.Round2.Guarded.Pin.GoalNeg2
```

Its permitted record is `AHP/round13/shared/assembly/R2_P2Goal.lean.log:112`; the identical independent replay is `AHP/round13/assembly/r2/P2Goal.verify.lean:11077`, with record `AHP/round13/assembly/r2/P2Goal.verify.lean.log:112`, exit 0 ([bp-579](#bp-579)). The weaker nested route is `goalNeg2_of_cofinalP3` at `AHP/round13/shared/assembly/R2_P2Goal.lean:11093`, record `AHP/round13/shared/assembly/R2_P2Goal.lean.log:115`, with the identical independent record at `AHP/round13/assembly/r2/P2Goal.verify.lean.log:115` ([bp-583](#bp-583)).

The compiled chain uses proved P1/P2 and start/gauge facts to construct the whole line, applies detection to that same generator, invokes the round-12 response-hull arrow, and uses proved regularity and the round-9/10 pinned-goal bridge. All scale/radius choices remain nested and precede the small-curvature cap. Neither final implication hides P1, P2, regularity, an inverse-unit premise, simplicity, or an isolated-root assumption.

**Remaining mathematical work:** prove P3, or the nested CofinalP3, or an actual same-generator nonzero weighted areaSum sufficient for the detection handoff. A recurrence for a linear trace, a single nonzero determinant, or a stable floating-point aggregate does not prove this. P1/P2 do not need re-proving, and no join repair remains on this shortest route.

The original alternative `CofinalAnyPathNoResponseCancellation → GoalNeg2` is now compiled in [join-11](#join-11). It too remains an implication, not an inhabitant of its premise or conclusion.

## Integration status and retained historical failures

- **Closed compiler repair:** the three missing Color helpers are inserted verbatim in `AHP/round13/assembly/r1/RepairedJoin.lean`; all 1186 records are permitted and exit is 0. Earlier round-10 files retain their historical missing-helper failures.
- **Closed physical integration:** R1 supplied actual continuity and full positive start, then integrated P1. R2 integrated the complete P2 proof and discharged the original first-crossing whole-kernel theorem. The complete P3-only goal implication and nested alternative were independently replayed.
- **Review boundary:** `AHP/round13/assembly/r2/P2Goal.VERIFY.md` rejects the submitted `rightStar_kernelLine` as the final/physical target selection, while explicitly passing its mathematical statement, source fidelity and axioms. It is neither GoalNeg2 nor an exact P1–P3 target. `AdalyFormal.Round13.Assembly.R2.p2` is an exact P2 target. This documentation does not override that workflow rejection or claim unconditional goal closure.
- **Only detection remains on this route.** There is no current missing-helper or more-RAM blocker. The original round-4 perturbation and round-6 failed/unfinished extensions remain unaccepted; their statuses are not changed by these new certificates.

## What the proposed failure point actually shows about inverses

**There is still no unconditional cofinal failure family.** Conditional on P3 (or CofinalP3), using the now compiled integration, the failure point has the following inverse status:

| Object | Status at the conditional guarded failure |
|---|---|
| Uncorrected all-plaquette carrier \(A\) | **A unit.** Its ordinary inverse \(G=A^{-1}\) exists, so the Ginv-only guard is satisfied. The qualitative/profile-reflection route can make this carrier positive definite. |
| Uncorrected all-plaquette constraint \(QGQ^*\), used in \(H\) | **A unit in the admissible small-curvature bridge.** This follows from localized well-definedness and the transfer in Delta2_lit_eq_loc, not from the carrier guard alone. |
| Localized base carrier \(B\), corrected localized carrier \(C=B-D\), and localized corrected constraint | **Units** supplied by localized WellDefAt at the chosen small curvature. The uncorrected localized constraint is also a unit via NG_unit_of_N1. Thus the lift forming D uses genuine inverses. |
| Corrected all-plaquette carrier, named G1invS | **Not a unit:** it is \(A-D\). It has no ordinary inverse. |
| Corrected covariance \(G_1\) | It is Ring.inverse of the nonunit above, hence **zero by totalization**, not an existing ordinary inverse. |
| Corrected all-plaquette constraint \(N_1=QG_1Q^*\) and corrected lift \(H_1\) | \(N_1=0\); its totalized inverse and \(H_1\) vanish. The positive-energy competitor ensures the relevant coarse test space is nontrivial, so this zero constraint operator is not an ordinary invertible operator. |
| Auxiliary Dirichlet inverse for \(G'\) | Genuine by the dilated Dirichlet-unit theorem. |
| Gauge Gram inverse for the projection | Genuine at the flat point and in the sufficiently small curvature neighborhood used by regularity. |
| Scalar normalizations | \(\ell=2\) and \(\eta>0\), so these are not singular scalar normalizations. |

The exact pencil identity is **AdalyFormal.D1Residual.G1inv_lit_eq_pencil**, lean/src/DrRed1.lean:52. The totalized collapse is **AdalyFormal.D1Guarded.genFormS_collapse_G1inv**, lean/src/GdGap.lean:56:
\[
\operatorname{genFormS}(B_{\mathrm{test}})=-a\langle B_{\mathrm{test}},B_{\mathrm{test}}\rangle.
\]
Together with an admissible positive-energy test, that collapse defeats a positive coercive lower bound. It refutes the **carrier-only guarded, totalized formal reading**, if the remaining premise is proved. It is not a counterexample with every printed inverse existing, and it does not refute a version additionally guarded by full all-plaquette WellDefAt.

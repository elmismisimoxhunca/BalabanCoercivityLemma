# Round 10 nonvanishing, round 1

## Decision

**GoalNeg2 is NOT proved. No round-9 cofinal coupling premise is proved.**

This round supplies three short, independently compiled pieces, with explicit hypotheses, for the nonvanishing track. The main new estimate controls cancellation in the exact finite neutral-source sum. It is uniform in the number of blocks and does not use asymptotics, square roots, alternating signs, or numerical certificates.

The actual operator-to-block identification, the local jet nonvanishing and the jet bound remain unproved. The dictionary track's current `Core.lean` supplies symmetry infrastructure, not that block identification. No 12,000-line assembly was produced: doing so would not discharge these gaps.

## 1. Finite source domination — the preferred route

Write N=n+1, so there is at least one source block. Zero-pad a_{-1}=a_N=0 and assume the finite tridiagonal equations

\[
6a_j+a_{j-1}+a_{j+1}=\tfrac32\mathbf1_{j=0},\qquad 0\le j<N.
\]

These are the neutral-source equations documented in `AHP/round6/probe/leading_source.py`. This file does **not** identify their solution with the frozen H/J operators; that remains a dictionary obligation.

Define

\[
h_j=\mathbf1_{j=0}-2a_{j-1}+2a_{j+1},\qquad P=\sum_{j<N}h_jv_j.
\]

For the intended application v_j is the direction-1 quadratic jet at the jth coarse block of the dressed crossing vector. The actual scalar coupling is 2P, up to a nonzero physical normalization.

### Compiled theorem

If |v_j|≤|v_0| for every j<N, then

\[
|P-v_0|\le\frac{15}{19}|v_0|,\qquad |P|\ge\frac4{19}|v_0|.
\]

Consequently v_0≠0 implies P≠0 and Pv_0>0. The first source coefficient also satisfies h_0≥4/19. That finite-volume statement does not need the limiting formula h_0=36√2−50.

The finite-source cancellation problem is therefore reduced to **one local jet being nonzero and dominating the other jets**. No sign of the original coupling has to be prescribed.

### Proof of the 15/19 bound

Let

\[
S=\sum_{j<N}|a_j|,\quad x=|a_0|,\quad
L=\sum_{j<N}|a_{j-1}|,\quad U=\sum_{j<N}|a_{j+1}|.
\]

The zero boundary gives U=S−x, and L≤S. Summing the triangle inequalities for the source equations gives

\[
6S\le\tfrac32+L+U\le\tfrac32+2S-x,
\quad\text{hence}\quad 4S+x\le\tfrac32.
\]

At the first site,

\[
\tfrac32\le6x+|a_1|\le6x+U=5x+S.
\]

Therefore

\[
2(L+U)\le4S-2x
 =\frac{22}{19}(4S+x)-\frac{12}{19}(S+5x)
 \le\frac{15}{19}.
\]

Finally P−v_0=Σ_j(−2a_{j−1}+2a_{j+1})v_j, so the jet bound gives the claimed relative error. This uses no sign information about a_j.

### Lean statements

File: `SourceDominance.lean` (215 lines). Namespace: `AdalyFormal.Round10.Nonvanishing`.

- `source_l1_bound`: 2(L+U)≤15/19 from the exact finite source equations;
- `sourcePairing_error`: |P−v_0|≤(15/19)|v_0|;
- `sourcePairing_lower`: |P|≥(4/19)|v_0|;
- `sourceWeight_zero_lower`: h_0≥4/19;
- `sourcePairing_ne_zero`, `sourcePairing_same_sign`;
- `coupling_ne_zero_of_blockSourceData`: a separate dictionary/interface lemma.

The exact missing block-interface proposition is:

```lean
def BlockSourceData (coupling : ℝ) : Prop :=
  ∃ (n : ℕ) (a v : ℕ → ℝ) (factor : ℝ),
    a (n + 1) = 0 ∧
    (∀ j < n + 1,
      6 * a j + left a j + a (j + 1) = if j = 0 then (3 / 2 : ℝ) else 0) ∧
    (∀ j < n + 1, |v j| ≤ |v 0|) ∧ v 0 ≠ 0 ∧
    factor ≠ 0 ∧ coupling = factor * sourcePairing n a v
```

Here `left a j := if j = 0 then 0 else a (j - 1)` and
`sourcePairing n a v := ∑ j ∈ Finset.range (n+1), sourceWeight a j * v j`.

**We have not supplied `BlockSourceData` for any actual crossing coupling.** It is not called a proof of the coupling merely because the conditional theorem has standard axioms.

## 2. Reversible scalar recurrences — fallback

File: `RecurrenceNonvanishing.lean` (106 lines).

For a field K, suppose

\[
u_{n+d+1}=\sum_{i=0}^d c_i u_{n+i},\qquad c_0\ne0.
\]

If u vanishes from N+1 onwards, its equation at N forces u_N=0. Descending induction shows that an eventually zero solution is identically zero. Thus one nonzero value implies unboundedly many nonzero values. The proof is finite and sign-free; it does not need a dominant root or an asymptotic expansion.

Compiled:

```lean
recurrence_cofinal_nonzero
  (d : ℕ) (c u : ℕ → K) (hc : c 0 ≠ 0)
  (hr : ∀ n, u (n + (d + 1)) =
    ∑ i ∈ Finset.range (d + 1), c i * u (n + i))
  (k : ℕ) (hk : u k ≠ 0) :
  ∀ N, ∃ n, N ≤ n ∧ u n ≠ 0
```

`mathlib_recurrence_cofinal_nonzero` accepts Mathlib's `LinearRecurrence.IsSolution` directly. `RadiusRecurrenceData coupling q` puts this recurrence on `u n = coupling q (2*(n+9))`, requiring one seed on that same even-radius progression. `radius_cofinal_nonzero` then gives

```lean
∀ R₀, ∃ R, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ coupling q R ≠ 0
```

`dyadic_cofinal_nonzero` preserves the exact nested cofinal scale/radius quantifiers.

**Missing:** no recurrence or exact seed for the actual coupling was proved.

## 3. Invertible finite-dimensional transfer dynamics

File: `TransferNonvanishing.lean` (109 lines).

Let E be finite-dimensional over a field K, let T:E→E be injective and linear, and let L:E→K be linear. If L(T^k x)≠0 for one k, then L(T^n x)≠0 for unboundedly many n. There is no need to compute a scalar recurrence or its coefficients.

Proof: let P={y : L(T^n y)=0 for all n}. It is an invariant subspace. The restriction T|P is injective, hence surjective in finite dimension; therefore T⁻¹(P)=P. A zero tail means T^N x∈P, hence x∈P, contradicting the seed.

Compiled:

- `invariant_backward`;
- `transfer_eq_zero_of_zero_tail`;
- `transfer_cofinal_nonzero`;
- `transfer_quotient_cofinal_nonzero`: scalar n=L(T^n x)/denominator n with every denominator nonzero;
- `transfer_progression_cofinal_nonzero`: replace T by T^step and x by T^offset x, with a seed on that progression. Its conclusion concerns unbounded sample indices n; use a positive step when converting them to distinct physical radii.

Again, **no transfer certificate for the actual scalar coupling has been supplied.** This is an abstract block-reduction lemma with its hypotheses visible, as requested.

## 4. Mathematical cautions, not counterexamples to GoalNeg2

1. A recurrence for the **collar mode** is not automatically a recurrence for c_1(q,R). The crossing angle depends on R, the kernel is normalized, the constrained source and dressing involve inverses, and c_1 is quadratic in the mode. The scalar-recurrence theorem needs a recurrence for the scalar, or the transfer theorem needs a fixed finite-dimensional linear observable representing an unnormalized numerator. No such identity is inferred from a numerical exponential fit.
2. Unique continuation of a vector recurrence does not by itself imply nonzero quadratic jet. For example a nonzero sequence with all values in one fixed real line can satisfy an invertible second-order recurrence while every alternating area/commutator of consecutive values is zero. Thus “the mode cannot vanish on two layers” alone does not prove v_0≠0. This is an obstruction to that abbreviated argument, **not** evidence that the actual coupling premise is false.
3. Even a nonzero scalar in one character does not imply definiteness on the full kernel. Full-kernel containment in one charged complex line remains the assembly/dictionary obligation. The symmetric twist additionally requires exact partner splitting or another exact full-kernel argument.
4. The R9 q=1 Bloch calculations are evidence about the proposed local jet bound, not an exact finite-volume dilation theorem. The dictionary track's current `no_canonical_radius_dilation` also cautions that a single canonical q=1 radius cannot match both the dilated collar and core lengths when q>1.

## 5. Evidence checked this round

No new large solve was run. `check_existing_terms.py` reads only the retained R9 file
`AHP/round9/analytic-r1/numerics/out/terms_left_R8_p50.json` and writes
`existing_terms_check.json` under this round's directory.

For each of its three left-twist R=8 configurations, all 36 stored jets obey |v_j|≤|v_0|. Ratios are obtained from `term/h`; any common correction factor cancels.

| diagonal momentum | max jet ratio, j>0 | coupling / first summand |
|---|---:|---:|
| −π/8 | 0.03940051103 | 0.9787803148 |
| −0.267 | 0.05497934859 | 0.9705844895 |
| −π/32 | 0.07908414903 | 0.9580075670 |

These are decimal evaluations of earlier floating-point data, **not interval certificates**, exact jet identities, or a proof for all q,R. They support the generous bound 1 used by the new theorem but do not establish it. The data are left-twist, not a certified full-kernel result for the canonical symmetric twist.

### Subsequent held-out assembly check

After the round-1 hand-off, assembly supplied an independent actual q=2, R=22, left-only-twist calculation, character (7,7), at 140/190/220 digits. I read its 220-digit artifact, `AHP/round10/assembly/r1/numerics/left_q2_R22_p220.json`, and independently recomputed the relative-error arithmetic from the stored c_1 and v_0:

- 184 source blocks;
- c_1≈−2.772096228262375×10⁻⁸⁵, K_L≈−0.03832786838899734;
- v_0≈−1.553269178563134×10⁻⁸⁵;
- reported maximum noninitial jet ratio ≈0.0394005110280;
- recomputed |c_1/2−v_0|/|v_0|≈0.1076574921718562, below 15/19, agreeing with the reported ratio to the stored precision;
- reported source-equation residual ≈3.85×10⁻²¹⁹ and null-residual/|c_1|≈1.76×10⁻¹²⁹;
- leading term plus tail agrees with c_1 to relative discrepancy ≈5.77×10⁻²¹⁶ (decimal serialization precision).

This is additional **floating-point evidence only**, not my own operator solve, a directed-rounding certificate, or a full-character screen. It supports the finite-source criterion on a held-out actual dilated instance; the exact dictionary, local jet theorem, and full-kernel gap remain open. No Lean source or compiled hand-off changed following this check.

## 6. Exact remaining endpoint

The round-9 endpoint remains unproved:

```lean
AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalExplicitU1
```

Its definition is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧ ExplicitU1 (2^j) R
```

`ExplicitU1` asks for a nonzero canonical crossing vector, charged quarter-rotation structure, containment of the **whole** kernel in its charged line, and this exact nonvanishing clause:

```lean
∀ J' : AnalyticR1.TwistSpace q R, AnalyticR2.IsSourceDerivative q R J' →
  AnalyticR2.vacCoupling q R J' u₀ ≠ 0
```

For this track, a sufficient next hand-off is the following, with actual q,R,J',u₀ and the already-required source-derivative and crossing hypotheses:

```lean
AdalyFormal.Round10.Nonvanishing.BlockSourceData
  (AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling q R J' u₀)
```

The instantiated proposition above is **not proved here**. The exact local work left is:

- identify the source equations and the finite jet pairing with the frozen operators;
- prove the defect jet v_0≠0;
- prove |v_j|≤|v_0| for all source blocks;
- establish these and the full-kernel facts at nested cofinal dyadic scales/even radii.

Alternatively supply a recurrence/transfer certificate with an exact nonzero seed for the scalar coupling. None of these obligations is replaced by the numerical data.

## 7. Compilation and audit

Sole import of all three files: frozen `D1IVT` (which imports Mathlib, and no project definitions). New definitions in these files are explicitly abstract; no round-9 definitions were altered or silently replaced.

Every compilation used only:

```sh
AHP/round3/lean1.sh <file.lean>
```

The six final compilations (three originals, three byte-identical hand-off copies) all have exit **0**, no errors, no warnings and no `sorryAx`. Each of the 27 distinct declarations has its own `#print axioms`; every record is exactly `{propext, Classical.choice, Quot.sound}`.

Published hand-offs, independently compiled at their published paths:

- `AHP/round10/shared/nonvanishing/R1_SourceDominance.lean` (+ `.log`, `.exit`);
- `AHP/round10/shared/nonvanishing/R1_RecurrenceNonvanishing.lean` (+ `.log`, `.exit`);
- `AHP/round10/shared/nonvanishing/R1_TransferNonvanishing.lean` (+ `.log`, `.exit`);
- `AHP/round10/shared/nonvanishing/R1_STATUS.md` (interface summary).

`python3 AHP/round10/nonvanishing/r1/audit.py` writes `CHECKS.json` and passes. It verifies source hashes, hand-off byte equality, exit codes, source/log/exit timestamps, exact imports, forbidden-token absence, diagnostic absence, per-declaration axiom records and allowed dependencies. It explicitly records `goalNeg2_proved: false`.

Development failures were local tactic/elaboration errors: the two-argument absolute-value subtraction lemma name, sum-rewrite orientation, a solved-goal tactic sequence, dependent structure equality in the Mathlib recurrence wrapper, and induction context in the arithmetic-progression transfer lemma. They were repaired before the final successful recompilations. No timeout occurred. The final logs correspond to the current files; intermediate failed logs were overwritten by the wrapper during development and are not represented as successful runs.

## 8. Hygiene

Authored files are only under `AHP/round10/nonvanishing/r1/` and `AHP/round10/shared/nonvanishing/`. Earlier rounds and the dictionary/assembly tracks were read only. No protected source, integration checkout, lakefile, build, REPRODUCE script, commit, push, or removal was performed. All compiler calls used the shared two-slot wrapper. The only Python work this round was small read-only-data processing and the artifact audit.

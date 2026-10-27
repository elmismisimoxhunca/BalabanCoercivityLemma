# Guarded all-plaquette reading: round-2 statement pin

**Status: targets pinned and compiled; the mathematical question remains open.**

File: `AHP/round2/guarded/pin/Statement.lean`. Namespace: `AdalyFormal.Round2.Guarded.Pin`. This is a statement contract, not a proof or refutation of the guarded headline. The identity checks and sufficient-certificate implication are not completion targets.

## 1. The goals

| Goal | Line | Plain meaning |
|---|---:|---|
| `GoalPos1` | 154 | Prove the actual eventual `GuardPencilT`: at all sufficiently large scales and radii, with uniformly sufficiently small class parameter and a positive-energy admissible test field, invertibility of all-plaquette `Ginv` forces invertibility of `Ginv` minus the actual localized `Delta2`. |
| `GoalNeg1` | 155 | The exact logical negation of `GoalPos1`. |
| `GoalPos2` | 157 | Prove the original `P428Target8SG selAll selAll`: the uniform coercivity inequality on its entire frozen class whenever all-plaquette `Ginv` is a unit. |
| `GoalNeg2` | 158 | The exact logical negation of `GoalPos2`. |

The two positive goals are equivalent by the existing frozen theorem, used at line 178; consequently the negative goals are equivalent at line 181. A proof of either positive goal decides the positive direction, and a proof of either negative goal decides the negative direction. They are not four independent open problems.

The reference identities at lines 170 and 172 are proved by `rfl`, not by a one-way restriction to a smaller class. They identify the pins with `AdalyFormal.D1Residual.GuardPencilT` (`lean/src/DrEquiv.lean:99`) and `AdalyFormal.D1Literal.P428Target8SG selAll selAll` (`lean/src/D2Cons.lean:70`). The intermediate `GuardResidualT` is copied at line 121 and pinned by `rfl` at line 175 to `lean/src/GdR5a.lean:54`. No new positive goal is a flat-path comparison, a conditional margin bound, or the already-proved full-guard statement.

### Exact positive quantifier order

For the pencil goal:

\[
\forall\ell\ge2\;\forall a>0\;\exists m_0\ge1\;\forall m\ge m_0\;
\exists R_0\;\forall R\ge R_0\;\exists a_0>0.
\]

Then, for every depth \(k\ge1\), unit torus `Lu`, positive \(\alpha_0\) with \(12\ell^m\alpha_0\le a_0\), compatible torus, admissible tower, `LambdaOK2` region, and `ClassCoupled` configuration, the existence of **one** test field satisfying `OnLambdaTildeIn`, `OnLambdaT`, and positive `bondEnergy` implies

\[
\operatorname{IsUnit}(G^{-1}_{\rm all})\ \Longrightarrow\
\operatorname{IsUnit}(G^{-1}_{\rm all}-\Delta^{(2)}_{\rm in}).
\]

Here \(M=\ell^m\) and \(\eta=\ell^{-k}\). The displayed correction is **localized data's** `Delta2`, not the all-plaquette `Delta`, an arbitrary small symmetric matrix, or a finite difference of `Delta`.

The headline goal has the same outer order but additionally concludes `SidePow6` and chooses \(\gamma_0>0\) after \(a_0\) and before all the instance data. Its inequality is for **every** admissible test field. Neither goal fixes \(\ell=2\), \(a=1\), \(k=2\), a slab tower, or a flat interior. Neither adds invertibility of the corrected operator as a hypothesis. The pencil-to-headline equivalence may enlarge \(m_0,R_0\) and shrink \(a_0\); it is not a constant-preserving equivalence at each fixed instance.

### What a negative answer must supply

The negative definitions are literal negations, so no ambiguity about threshold order is delegated to prose. The file also defines the concrete, **unproved** sufficient certificate `CofinalPencilFailure` at line 189 and proves that it implies both negative goals (lines 206 and 218).

That certificate chooses fixed \(\ell\ge2\) and \(a>0\), then requires

\[
\forall m_0\;\exists m\ge\max(m_0,1)\;\forall R_0\;\exists R\ge R_0\;
\forall a_0>0\;\exists(k,\mathrm{Lu},\alpha_0,S,\Lambda,U,\widetilde B).
\]

All torus, tower, region, coverage, regularity, smallness and test-field conditions are present. The carrier `Ginv` must be a unit and the actual corrected pencil must not be a unit. **The radius \(R\) is chosen before \(a_0\).** The test field has positive energy. One bad finite torus, or one bad choice of \(m,R,a_0\), does not refute the eventual headline. No converse from the negation to a continuous sign-changing path is asserted.

A direct inequality refutation must similarly defeat every proposed eventual threshold and every proposed positive coercivity constant, not just one numerical constant. Alternatively, a cofinal unit/singular separation of the actual operators suffices via the residual equivalence. The frozen path certificate `SepPathFamily2` is another **sufficient** route (`lean/src/DrFamily2.lean:36,82`), not an established equivalent of the negation; its interval-unit and endpoint-sign assumptions are extra obligations.

## 2. Definitions and dependency boundary

The sole import is frozen `DrEquiv` from `lean/src`; there are no AHP imports. Twenty-two operative declarations were checked textually against their frozen sources, preserving names, signatures and bodies inside the fresh namespace; only surrounding namespace/section organization and comments differ:

- `D1Lit.lean:29–101`: selectors; the actual `DeltaS`, `DpiFullS`, `JfS`, `dataS`, `G1invS`, `H1inS`; `GenS.NmatS`, `firstTermS`, `genFormS`; the test-field inequality; and the two structural proofs needed by those definitions.
- `D2Cons.lean:56–76`: `InstIneqSG`, `CoercG8AtSG`, `P428Target8SG`.
- `GdR5a.lean:54–63`: `GuardResidualT`.
- `DrEquiv.lean:35–46,53–57,99`: `GShape`, `CPen`, `GuardPencilT`.

The remaining dependencies are the **unchanged concrete frozen definitions**, not additional parameters or stand-ins. Important anchors:

| Object | Frozen source |
|---|---|
| Fine torus / tower / admissibility / class cubes / both-endpoint bonds | `lean/src/ZStatementP428.lean:42,47,73,140,145` |
| Coverage and coupled class | `lean/src/ZR2A.lean:107`; `lean/src/ZR6A.lean:27,33,124` |
| Per-cube regularity and curl-of-curl | `lean/src/ZR2A.lean:40,47` |
| Torus compatibility, test-field restrictions, touching support | `lean/src/ZStatementP428.lean:286,230`; `lean/src/ZR2A.lean:121` |
| Lambda predicate | `lean/src/ZStatementP428.lean:189`; `lean/src/ZT4A.lean:57,88` |
| Concrete parameter assembly | `lean/src/ZXG3A.lean:63` (`gparams`) |
| Base data | `lean/src/ZXR2Ops3.lean:134` (`baseData`) |
| Carrier inverse operator, inverse and constraint solution | `lean/src/R2Algebra.lean:145,147,149` (`Ginv`, `G`, `H`) |
| Actual second-order correction | `lean/src/R2Algebra.lean:212,220` (`delta2Bil`, `Delta2`); defining form theorem at 222 |
| Corrected covariance and constraint solution | `lean/src/R2Algebra.lean:307–308` (`G1`, `H1`) |
| Energy | `lean/src/AdalyFormal/Balaban/RegularUPerturbation.lean:355` |

The locally copied `dataS`, `G1invS`, and form are each definitionally identical to the frozen assembly (lines 161, 164, 167). In particular, the correction and all inverses are those of the genuine lattice configuration. A downstream standalone Lean file must copy the needed pin definitions verbatim or use their frozen equivalents; it must not import this AHP file.

## 3. Exterior paths: a route, not a narrowing of the goals

For a path moving only bonds with **neither** endpoint in \(\Omega_0\), the existing identity reads

\[
G^{-1}_{\rm all}(t)=G^{-1}_{\rm all}(0)+\mathrm{Shift}(t),\qquad
\mathrm{Shift}(t)=p_EW_0^*(\Delta_{\rm all}(t)-\Delta_{\rm all}(0))W_0i_E.
\]

Sources: `D1Path.lean:25` (`Zb`), `DrPath1.lean:47` (`Ginv_lit_path`), `DrPath2.lean:63,77,89` (constant localized correction, localized well-definedness, and preservation of class membership). Under the stated admissibility and room conditions, localized `WellDefAt`, and the literal `Ginv` unit guard, `DrRed1.lean:52` / `DrPath3.lean:85` identifies the second operator with this carrier minus the fixed localized correction. The missing implication is invertibility transfer, not those already-proved identities.

Stage B's `AHP/fidelity/guarded/lean/UthCross.lean:36,72` proves an in-class non-unit crossing and the no-separation identity on the flat-interior twist path. On that path the localized correction is zero, and the crossing fails the guard. It is **not** a candidate for either negative goal. `GdFam.lean:30` gives equality of literal `G1invS` and `Ginv` along that whole path without unit premises.

A refuter should seek non-flat interior backgrounds, two-parameter families, and a genuinely nonzero localized correction. No such property is imposed as a new restriction on the goals. Nonzero curvature or correction alone, or a nonzero quadratic matrix element, is not a separation proof. The previously retained small-box scripts model only `Delta`, not assembled `Ginv` or `Delta2`; their compressions and scalar models cannot inhabit the certificate. No numerics were run for this pin.

## 4. Departures from Balaban's print retained by this contract

These are the disclosed readings/departures of the **guarded all-plaquette formal statement**, not a claim that the print itself is true or false. Source-reading status is inherited from `HANDOFF.md`, `paper/OPEN_ITEMS.md` B/K–N/R/S, the paper's D1–D12/N1–N6 table, and `notes/statement_sheet.tex`; this pass did not independently inspect page images.

1. **Guard and total inverses (new qualification).** Only assembled `Ginv` being a unit guards the conclusion. This is not the printed unqualified positivity assertion and not a statement presupposing every printed inverse. The covariance operators use `Ring.inverse`, totalized to zero at non-units, including the corrected and compressed inverses; upstream inverse constructions retain their own totalized definitions. `WellDefAt` includes three covariance-layer unit conditions; its proved headline `P428Target8SG2` is different. Those conditions account for a fourth covariance-layer inverse by a theorem, not all primitive inverse constructions. A cofinal family of singular corrected operators with the carrier guard true refutes this formal reading through undefined printed covariances, not through negative fully defined printed quadratic forms.
2. **D1: all-plaquette choice, other masks unchanged.** Both selectors are `Set.univ`, matching the literal sums in (3.10) and (3.11), rather than the frozen `plaqIn` localization. The carrier remains `bondSupp`, and the Dirichlet sandwich remains \(W^*\Delta W\), with its original touching-bond support machinery. This may read exterior links, despite the p.394 locality sentence. It is not an independently reconstructed printed Dirichlet operator, the both-endpoint-sandwich variant, or the consistent corner/touching reading of S-1.
3. **S-1 / D2: unchanged both-endpoint class and added coverage.** `CubeBond` still requires both endpoints, unlike the general endpoint/corner convention quoted in CMP102 p.277 and CMP96 p.224. `CoversOm0p` retains site coverage and common-cube coverage of fully interior plaquettes only. It does not cover every plaquette now read by the all-plaquette operators. Coverage is an additional tower hypothesis, not printed. No touching-class repair or shell regularity is inserted here.
4. **D3: factor and cube shapes.** Class cubes are aligned periodic boxes of side \(12M\ell^j\) fine sites, with a unique stratum index; the same fixed factor 12 occurs in coverage, regularity and smallness. The print has an \(O(1)\ge10\) associated with cubes and says unions of several big blocks; p.409 permits 12. Per-cube factors, arbitrary unions, and altered level-zero cube classes are not substituted. The physical block scale \(M\ell^j\eta\) is a reading of the source's lattice subscripts.
5. **D4: uniformity and order.** The constants \(a_0,\gamma_0\) are independent of depth, torus, tower, region, background, smallness parameter and test field, beyond the print's explicitly named independence of \(k,U\). They may depend on \(\ell,a,m,R\); \(R_0\) may depend on \(m\). This is not the stronger Total quantifier order. The residual removes \(\gamma_0\) and `SidePow6` using proved equivalences, not by silently discarding them from the headline.
6. **D5, D6: parameter ranges.** All real \(a>0\) and all natural \(\ell\ge2\) are quantified. No large-\(L\) or odd-\(L\) convention is imposed. OPEN_ITEMS S-4 records odd \(L>11\) in CMP109; a counterexample at \(\ell=2\) refutes this formal universal goal, not that narrower printed convention.
7. **Dimension, geometry, D7 / N4.** Dimension three, SU(2), finite periodic rectangular tori, extent stored as side minus one, shortest-periodic \(\ell^1\) distance, aligned half-open blocks, divisibility/tiling, and empty padding above \(k\) are retained. `TorusOK` requires \(\ell\) and \(M\) to divide every unit side and \(\ell\) to be strictly below each side. These are restrictions/conventions not all stated by the print.
8. **D8 / N3: depth and base domain.** Depth is \(k\ge1\), not including zero. `Admissible` retains strict interlevel collars and the exact p.396 \(\Omega_0\) block-neighborhood rule. The meaning of \(T_1\) is reading A (fine lattice in its own unit); the p.394 thinner-layer option, reading B, and separate operator/class domains are not introduced.
9. **N5 and radii.** \(M=\ell^m\), \(m\ge1\), matches the power-of-\(L\) convention for \(M\); \(R\) ranges over all sufficiently large naturals, not just powers, although p.408 describes both numbers as powers. The common \(R\) used in tower and Lambda collars is retained as a source reading, not a new coordinate-identification theorem.
10. **D9 / norm row.** Per-cube matrix bounds use full Frobenius norm, \(\sqrt2\) times the trace-normalized printed norm; this changes the smallness normalization. Differences and curl-of-curl `ddA` are tested only where their specified bond stencils lie in the cube. The curl-form implementation of \(\partial^*\partial\) and those boundary guards remain. Test-field `bondEnergy` instead uses the trace-normalized Hilbert–Schmidt norm.
11. **D10, D11: jets and operator assembly.** The concrete per-component one-step/raw jets, their chain, \(Q_{\rm linB}=\ell^jQ_j\), constrained solution maps and second jets remain unchanged. This is the repository's bridged implementation of (3.13)–(3.15), not a new derivation of every source operator or of analyticity on every possible printed domain. The nonlinear correction is retained, not set to zero.
12. **S-3: units, \(\eta\), and \(\tau^*\).** \(\eta=\ell^{-k}\); the assembly uses its eta-free fine-lattice conventions. The first term is \(\eta\langle\tau^*B,(QG_1Q^*)^{-1}\tau^*B\rangle\), whereas the print does not display that extra factor or embedding. The full dictionary for pairings, weights, mass subtraction, source term, second jets, and compression versus inversion is still open. This pin does not remove the factor or resolve normalization fidelity.
13. **N1, N2: region and competitors.** `LambdaOK2` includes block decomposition, inclusion in the embedded top domain and the strict unit-lattice collar; the empty region is allowed. Admissible competitors use touching support, staircase zeros and dropped-bond zeros, rather than a universal both-endpoint convention. The pulled-back operator is the genuine `GenP.genC`; its singular constraint-inverse fallback is not removed. Reading the regional constraints as the exact printed subspace remains qualified as in the statement sheet.
14. **N6: per-cube gauges.** The existential gauge and Hermitian traceless field are chosen separately inside each universal cube quantifier; there is no single global gauge premise. This is a retained source reading, not a new strengthening to global regularity.
15. **D12 and the residual's test-field condition.** The room condition \(17\ell\le RM\) is used by reduction proofs after adjusting thresholds, not added to either headline. Existence of a positive-energy test field in `GShape`/`GuardResidualT` is a formal reduction device: without one all admissible competitors are zero, so the inequality is trivial. It is not an additional restriction smuggled into `GoalPos2` and not a printed hypothesis.

## 5. Compilation and checks

Run from the existing frozen project, one file only:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/guarded/pin/Statement.lean > ../AHP/round2/guarded/pin/Statement.lean.log 2>&1
echo $? > ../AHP/round2/guarded/pin/Statement.lean.exit
```

Exit **0**. Log: `Statement.lean.log`; exit record: `Statement.lean.exit`. No errors or warnings. All **17** requested dependency records contain exactly `propext`, `Classical.choice`, `Quot.sound`, including all four goal definitions, the certificate definition, and the identity/implication checks. A `#print axioms` line for a proposition definition checks its dependencies; it does **not** prove the proposition.

A textual check matched all 22 copied operative declarations against their frozen sources. The raw whole-file prohibited-token scan, including comments and excluding no code, found no prohibited token. Sole import checked: `DrEquiv`. SHA-256 of compiled `Statement.lean`:

```text
cb10c63af2e2a51f4f4a636f36933c071d2cbdccd15aacb6837d6cd15cdd5656
```

No full build, reproduction, update, numerical sweep, commit, push, deletion, or protected-file edit was performed. Existing changes to `lean/lakefile.toml` and other threads' source directories were left alone. All files written by this pin are under `AHP/round2/guarded/pin/`.

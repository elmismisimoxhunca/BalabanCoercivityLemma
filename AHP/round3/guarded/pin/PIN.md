# Guarded all-plaquette reading: round-3 boundary-response pin

**Status: targets pinned and compiled; the mathematical question remains open.**

File: `AHP/round3/guarded/pin/Statement.lean`. Goal namespace: `AdalyFormal.Round2.Guarded.Pin`, deliberately retained. **Lines 1–248 are the complete round-2 pin byte-for-byte**, including its historical heading and both equivalent positive/negative pairs. The primary headline remains `GoalPos2`; `GoalPos1` remains its equivalent pencil formulation. No goal is renumbered or weakened.

Lines 250–352 append the five boundary-response definitions, copied verbatim from round 2 in their retained namespace `AdalyFormal.Round2.Guarded.R2Prove`, with checks and dependency prints. This is a statement contract, not a proof or refutation of the guarded headline. The identity checks, certificate implications, and already-proved boundary-response equivalence are **not completion targets**. Neither direction of the headline is decided by this pin.

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

The negative definitions are literal negations, so no ambiguity about threshold order is delegated to prose. The file also defines the concrete, **unproved** certificate `CofinalPencilFailure` at line 189 and proves that it implies both negative goals (lines 206 and 218). Round 2 additionally proved its equivalence to `GoalNeg2` (`AHP/round2/guarded/r2-refute/Attempt.lean:358`, `goalNeg2_iff_cofinalPencilFailure`). That equivalence supplies no witness and is not a new goal.

That certificate chooses fixed \(\ell\ge2\) and \(a>0\), then requires

\[
\forall m_0\;\exists m\ge\max(m_0,1)\;\forall R_0\;\exists R\ge R_0\;
\forall a_0>0\;\exists(k,\mathrm{Lu},\alpha_0,S,\Lambda,U,\widetilde B).
\]

All torus, tower, region, coverage, regularity, smallness and test-field conditions are present. The carrier `Ginv` must be a unit and the actual corrected pencil must not be a unit. **The radius \(R\) is chosen before \(a_0\).** The test field has positive energy. One bad finite torus, or one bad choice of \(m,R,a_0\), does not refute the eventual headline. No converse from the negation to a continuous sign-changing path is asserted.

A direct inequality refutation must similarly defeat every proposed eventual threshold and every proposed positive coercivity constant, not just one numerical constant. Alternatively, a cofinal unit/singular separation of the actual operators suffices via the residual equivalence. The frozen path certificate `SepPathFamily2` is another **sufficient** route (`lean/src/DrFamily2.lean:36,82`), not an established equivalent of the negation; its interval-unit and endpoint-sign assumptions are extra obligations.

## 2. Definitions and dependency boundary

The sole import is frozen `DrEquiv` from `lean/src`; there are no AHP imports. Twenty-two operative declarations were freshly checked character-for-character against their frozen sources, preserving names, signatures and bodies inside the retained pin namespace; only surrounding namespace/section organization and comments differ:

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

The locally copied `dataS`, `G1invS`, and form are each definitionally identical to the frozen assembly (lines 161, 164, 167). In particular, the correction and all inverses are those of the genuine lattice configuration.

The support appendix copies these further definitions **verbatim**, not abstract replacements:

| Definition | This pin | Round-2 source `AHP/round2/guarded/r2-prove/Attempt.lean` |
|---|---:|---:|
| `response` | 273 | 281 |
| `boundaryShift` | 290 | 409 |
| `localCorrected` | 293 | 413 |
| `CBoundaryResponse` | 299 | 534 |
| `CNoBoundaryReturn` | 306 | 558 |

`response` is generic algebra, but its concrete use here substitutes the actual copied lattice assemblies. It is not a stand-in for them. The appendix does not re-prove round 2's response equivalence or add the zero-return premise to any goal.

Downstream attempts must copy this pin's definitions and goals verbatim; they must not import this AHP file. When reusing round-2 proofs, copy only needed helpers after the pin and do not redeclare definitions already supplied here. Only frozen modules under `lean/src` may be imported.

## 3. The boundary-response question and honest stopping conditions

At an actual `IngrBParams` instance write

\[
A=(\mathrm{dataS}_{\rm all}).Ginv,\quad B=(\mathrm{dataS}_{\rm in}).Ginv,\quad
D=(\mathrm{dataS}_{\rm in}).Delta2,\quad C=B-D,\quad\Theta=A-B,
\quad W=\operatorname{range}\Theta.
\]

`boundaryShift` is exactly \(\Theta\), `localCorrected` exactly \(C\), and `response` constructs continuous linear endomorphisms of \(W\):

\[
K_B y=y+\Theta B^{-1}y,\qquad K_C y=y+\Theta C^{-1}y.
\]

The inverses are taken on the **full carrier** before restricting the response to its invariant range. No inverse/compression interchange, identification of \(W\) with a particular geometric shell, or properness/nontriviality of \(W\) is assumed.

### Positive route

The accepted round-2 equivalence is

\[
\texttt{GoalPos2}\;\longleftrightarrow\;\texttt{GShape CBoundaryResponse}.
\]

Source: `AHP/round2/guarded/r2-prove/Attempt.lean:554`, `AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response`. It uses localized well-definedness available after combining eventual thresholds via frozen `GShape_imp` (`lean/src/DrEquiv.lean:60`). It is not an equivalence preserving particular chosen constants without those hypotheses. The actual task is to **prove a side**, not re-prove this equivalence.

After strengthening the eventual thresholds, on class instances carrying the positive-energy test required by `GShape`, localized \(B,C\) are units. The literal guard makes \(K_B\) a unit; the unresolved conclusion is that \(K_C\) is a unit. Round 2's `response_sub_apply` (`:362`) gives

\[
(K_C-K_B)y=\Theta C^{-1}DB^{-1}y.
\]

Known, with their exact conditional scope:

- `pencil_isUnit_of_no_boundary_return` (`:475`) proves sufficiency of zero return for every \(y\in W\), with localized `WellDefAt` and the literal carrier guard. `GShape CNoBoundaryReturn` would suffice eventually, but is **unproved**, not a new premise of `GoalPos2`, and is not asserted necessary.
- `guarded_failure_forces_boundary_return` (`:496`) gives a nonzero \(y\in W\), \(K_Cy=0\), and nonzero return from an actual guarded failure under localized `WellDefAt`. It supplies neither a witness nor a contradiction.
- `pencil_isUnit_of_feedback_norm_lt_one` (`AHP/round2/guarded/r1-prove/Attempt.lean:355`) proves sufficiency of \(\|A^{-1}D\|<1\). No class-uniform bound is currently proved.
- `boundaryShift_kills_V` / `boundaryShift_range_le_orthogonal` (`r2-prove/Attempt.lean:435,444`) prove \(\Theta V_0=0\), \(W\subseteq V_0^\perp\), under admissibility and the room condition. \(V_0\) means zero on **all level-zero bonds**, not merely a boundary shell.

A uniformly small **absolute** return is insufficient by itself: a perturbative argument also needs control relative to \(K_B^{-1}\), for example \(\|K_B^{-1}(K_C-K_B)\|<1\). The guard asserts invertibility, not a uniform spectral gap over exterior links. Raw locality of \(D\) and separation from a boundary does not imply vanishing after \(B^{-1}\) and \(C^{-1}\); the missing statement would have to control that propagation. These cautions do not rule out a positive source-specific proof.

### Negative route

A real certificate must combine exact carrier-unit/corrected-singular separation with **all** of `TorusOK`, `Admissible`, `LambdaOK2`, frozen coverage/regularity, positive capped smallness, and a positive-energy admissible competitor, with the cofinal binders in section 1. It cannot choose the radius after receiving the cap. The cofinal certificate is enough; a continuous path or spectral sign-change construction is optional, with additional obligations if used.

`guarded_failure_forces_nonflat` (`AHP/round2/guarded/r1-refute/Attempt.lean:379`) shows, under admissibility and \(3\le RM\), that any guarded failure has a bond **based in** \(\Omega_0\) with \(Ue\ne1\). This excludes base-point-identity backgrounds; it does **not** assert nonzero curvature or supply non-flat witnesses. No extra non-flatness hypothesis is inserted into the goal.

Round 2's numerical candidate cannot be relabelled as in-class: `candidate_excluded` (`AHP/round2/guarded/r2-refute/Attempt.lean:335`) proves that its enlarged side-eight torus is compatible but its tower fails admissibility for every radius and the coupled class for every background/parameter. The original small torus also fails `TorusOK` (`:285`). Those scripts probe assembled operators but remain floating-point/finite-difference evidence on excluded geometries, not exact singularity certificates.

The earlier Stage-B flat-interior crossing (`AHP/fidelity/guarded/lean/UthCross.lean:36,72`) has zero localized correction and fails the guard; it cannot separate the two operators. Exterior-path identities and the already-proved full-guard headline do not discharge the missing corrected unit condition. No numerical script was run for this pin, and no round-2 attempt was recompiled here; their accepted status is taken from the fully read round-2 judgement and inspected source.

## 4. Departures from Balaban's print retained by this contract

These are the disclosed readings/departures of the **guarded all-plaquette formal statement**, not a claim that the print itself is true or false. Source-reading status is inherited from `HANDOFF.md`, `paper/OPEN_ITEMS.md` B/K–N/R/S, the paper's D1–D12/N1–N6 table, and `notes/statement_sheet.tex`; this pass did not independently inspect page images.

1. **Guard and total inverses (new qualification).** Only assembled `Ginv` being a unit guards the conclusion. This is not the printed unqualified positivity assertion and not a statement presupposing every printed inverse. The covariance operators use `Ring.inverse`, totalized to zero at non-units, including the corrected and compressed inverses; upstream inverse constructions retain their own totalized definitions. `WellDefAt` includes three covariance-layer unit conditions; its proved headline `P428Target8SG2` is different. Those conditions account for a fourth covariance-layer inverse by a theorem, not all primitive inverse constructions. A cofinal family of singular corrected operators with the carrier guard true refutes this formal reading through undefined printed covariances, not through negative fully defined printed quadratic forms.
2. **D1: all-plaquette choice, other masks unchanged.** Both selectors are `Set.univ`, matching the literal sums in (3.10) and (3.11), rather than the frozen `plaqIn` localization. The carrier remains `bondSupp`, and the Dirichlet sandwich remains \(W^*\Delta W\), with its original touching-bond support machinery. This may read exterior links, despite the p.394 locality sentence. It is not an independently reconstructed printed Dirichlet operator, the both-endpoint-sandwich variant, or the consistent corner/touching reading of S-1.
3. **S-1 / D2: unchanged both-endpoint class and added coverage.** `CubeBond` still requires both endpoints, unlike the general endpoint/corner convention quoted in CMP102 p.277 and CMP96 p.224. `CoversOm0p` retains site coverage and common-cube coverage of fully interior plaquettes only. It does not cover every plaquette now read by the all-plaquette operators. Coverage is an additional tower hypothesis, not printed. No touching-class repair or shell regularity is inserted here.
4. **D3: factor and cube shapes.** Class cubes are aligned periodic boxes of side \(12M\ell^j\) fine sites, with a unique stratum index; the same fixed factor 12 occurs in coverage, regularity and smallness. The print has an \(O(1)\ge10\) associated with cubes and says unions of several big blocks; p.409 permits 12. Per-cube factors, arbitrary unions, and altered level-zero cube classes are not substituted. No extra condition corresponding to p.408's third-enlargement case split is imposed; its source adequacy remains the R-b reading question. The physical block scale \(M\ell^j\eta\) is a reading of the source's lattice subscripts.
5. **D4: uniformity and order.** The constants \(a_0,\gamma_0\) are independent of depth, torus, tower, region, background, smallness parameter and test field, beyond the print's explicitly named independence of \(k,U\). They may depend on \(\ell,a,m,R\); \(R_0\) may depend on \(m\). This is not the stronger Total quantifier order. The residual removes \(\gamma_0\) and `SidePow6` using proved equivalences, not by silently discarding them from the headline.
6. **D5, D6: parameter ranges.** All real \(a>0\) and all natural \(\ell\ge2\) are quantified. No large-\(L\) or odd-\(L\) convention is imposed. OPEN_ITEMS S-4 records odd \(L>11\) in CMP109; a counterexample at \(\ell=2\) refutes this formal universal goal, not that narrower printed convention.
7. **Dimension, geometry, D7 / N4.** Dimension three, SU(2), finite periodic rectangular tori, extent stored as side minus one, shortest-periodic \(\ell^1\) distance, aligned half-open blocks, divisibility/tiling, and empty padding above \(k\) are retained. `TorusOK` requires \(\ell\) and \(M\) to divide every unit side and \(\ell\) to be strictly below each side. These are restrictions/conventions not all stated by the print.
8. **D8 / N3: depth and base domain.** Depth is \(k\ge1\), not including zero. `Admissible` retains strict interlevel collars and the exact p.396 \(\Omega_0\) block-neighborhood rule. The meaning of \(T_1\) is reading A (fine lattice in its own unit); the p.394 thinner-layer option, reading B, and separate operator/class domains are not introduced.
9. **N5 and radii.** \(M=\ell^m\), \(m\ge1\), matches the power-of-\(L\) convention for \(M\); \(R\) ranges over all sufficiently large naturals, not just powers, although p.408 describes both numbers as powers. The common \(R\) used in tower and Lambda collars is retained as a source reading, not a new coordinate-identification theorem.
10. **D9 / norm row.** Per-cube matrix bounds use full Frobenius norm, \(\sqrt2\) times the trace-normalized printed norm; this changes the smallness normalization. Differences and curl-of-curl `ddA` are tested only where their specified bond stencils lie in the cube. The curl-form implementation of \(\partial^*\partial\) and those boundary guards remain. Test-field `bondEnergy` instead uses the trace-normalized Hilbert–Schmidt norm.
11. **D10, D11: jets and operator assembly.** The concrete per-component one-step/raw jets, their chain, \(Q_{\rm linB}=\ell^jQ_j\), constrained solution maps and second jets remain unchanged. This is the repository's bridged implementation of (3.13)–(3.15), not a new derivation of every source operator or of analyticity on every possible printed domain. The nonlinear correction is retained, not set to zero.
12. **S-3: units, \(\eta\), and \(\tau^*\).** \(\eta=\ell^{-k}\); the assembly retains its eta-free fine-lattice conventions and first term \(\eta\langle\tau^*B,(QG_1Q^*)^{-1}\tau^*B\rangle\), whereas the print displays neither the extra factor nor embedding. **Round-2 update:** the guarded first-term dictionary was proved with scalar one for both linked H/C readings, retaining the frozen inside-plaquette localization (`AHP/round2/s3-normalisation/JUDGEMENT.md`, summarized in `AHP/round2/RESULTS.md`). That is not an all-plaquette dictionary or an inverse-existence theorem. The separate mass, nonlinear J and bond-energy summands, complete support/constraint identifications, and broader printed normalization remain qualified; this pin changes none of them. No inverse/compression interchange is asserted.
13. **N1, N2: region and competitors.** `LambdaOK2` includes block decomposition, inclusion in the embedded top domain and the strict unit-lattice collar; the empty region is allowed. Admissible competitors use touching support, staircase zeros and dropped-bond zeros, rather than a universal both-endpoint convention. The pulled-back operator is the genuine `GenP.genC`; its singular constraint-inverse fallback is not removed. Reading the regional constraints as the exact printed subspace remains qualified as in the statement sheet.
14. **N6: per-cube gauges.** The existential gauge and Hermitian traceless field are chosen separately inside each universal cube quantifier; there is no single global gauge premise. This is a retained source reading, not a new strengthening to global regularity.
15. **D12 and the residual's test-field condition.** The room condition \(17\ell\le RM\) is used by reduction proofs after adjusting thresholds, not added to either headline. Existence of a positive-energy test field in `GShape`/`GuardResidualT` is a formal reduction device: without one all admissible competitors are zero, so the inequality is trivial. It is not an additional restriction smuggled into `GoalPos2` and not a printed hypothesis.

## 5. Compilation and checks

Executed from the workspace root, exclusively through the shared-lock wrapper:

```sh
AHP/round3/lean1.sh AHP/round3/guarded/pin/Statement.lean
```

Exit **0**. Fresh log: `Statement.lean.log`; exit record: `Statement.lean.exit`. No errors or warnings. All **42** local declarations have individual dependency records, including all four goal definitions, the certificate, structural proofs, identity/implication checks, and five boundary-response definitions. Every record is a subset of `propext`, `Classical.choice`, `Quot.sound`. A `#print axioms` line for a proposition definition checks its dependencies; it does **not** prove the proposition.

`validate.py` was run successfully and saved `CHECKS.json`. It confirms:

- the entire 248-line round-2 pin is an exact byte prefix;
- 22 operative declarations match their frozen sources character-for-character and all five appendix definitions match the round-2 positive attempt character-for-character;
- each negative goal is the exact negation of its positive goal;
- the sole import is frozen `DrEquiv`, with no AHP import;
- the raw whole-source forbidden-token scan, including comments, has no hits;
- final exit 0, source/log/exit timestamp order, no diagnostics, complete dependency-print coverage and permitted dependency sets.

SHA-256 of the compiled round-3 `Statement.lean`:

```text
0a06554ee453ebf71782165723546c7fbb8f69b143a004f7d7c4c39deb53dad7
```

SHA-256 of the unchanged round-2 prefix:

```text
cb10c63af2e2a51f4f4a636f36933c071d2cbdccd15aacb6837d6cd15cdd5656
```

This verifies the **pin task**, not a new positive or negative result. No independent second-agent gate, numerical replay, source-page image review, or whole-project rebuild is claimed. The user's fresh reproduction pass is taken as supplied context. No direct Lean/Lake invocation, build, reproduction, dependency update, numerical sweep, deletion, commit, push, or protected-file edit was performed. All authored files are under `AHP/round3/guarded/pin/`; the shared wrapper uses its pre-existing cross-worker lock. Other threads' work was left untouched.

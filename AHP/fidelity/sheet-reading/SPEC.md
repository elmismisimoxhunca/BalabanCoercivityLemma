# sheet-reading — Q8, Q10, Q11

Reading record for statement-sheet questions Q8, Q10 and Q11 (`notes/statement_sheet.tex`, clauses A8, A10, A11). Stage A only. No Lean was run. A numerical result below is evidence about a transcribed formula, not a proof, and nothing here is a theorem.

Prediction: **forms-agree**. Every row is “matches” or “matches with a stated convention”. No row is an unmarked mismatch. The conventions are the ones already named in the sheet (η-free body, junk inverse, plaquette selection D1, touching bonds N1, η and τ* in the first term). A reader who refuses one of those conventions has a different statement; the refused reading is named in the row.

Prints were read from `sources/corpus/pages/CMP99b_p{394,419,420,421,428}.md` and from the page renders `sources/corpus/renders/CMP99b_p394-06.png`, `p419-31.png`, `p420-32.png`, `p421-33.png`, `p428-40.png` (half-scale crops of those PNGs). The renders agree with the corpus on (3.21)–(3.25), (3.119), (3.122), (3.126), (3.128), (3.129) and the p.428 paragraph on \(\tilde B\) and \(C\).

## Variant statement (Lean text, not a new claim)

Stage B should not prove a new proposition. The statement being read is the frozen chain already defined by the declarations below. The Lean text of the reading is the audit note

```lean
/-
Reading record, not a theorem.
Q8. DelpA, Gp, Wop, DpiFull match (3.24), G', and W of (3.119)
    under the η-free d = 3 convention, the junk value 0, and plaqIn for Δ.
Q10. Ginv, G, G1inv, G1, H1 match (3.122) and (3.126)–(3.129)
    under the reading of a‖QA‖² as the quadratic form (3.16).
Q11. OnLambdaTildeIn ∧ OnLambdaT is the p.428 variable set under the
    touching convention, and Cop solves (Q B)(c) = 0 on the dropped bonds
    when H0 is bijective.
-/
#check @AdalyFormal.IngredientFamilyR2.inner_Qpa
#check @AdalyFormal.IngredientFamilyR2.Gp_spec
#check @AdalyFormal.IngredientFamilyR2.inner_DpiFull
#check @AdalyFormal.IngredientFamilyR2.Cop_ker
#check @AdalyFormal.StatementLaneG.InstIneq.toBoth
```

## Q8 — `DelpA`, `Gp`, `Wop`, `DpiFull` against (3.24), \(G'\), \(W\) of (3.119)

### Term by term

| Print (render + corpus) | Lean | Row |
|---|---|---|
| (3.24), p.394: \(\langle\lambda,Q'^*aQ'\lambda\rangle=\sum_{j=0}^k a_j\sum_{y\in\Lambda_j}(L^j\eta)^{d-2}\lvert(Q'_j(U)\lambda)(y)\rvert^2\), with \(a_{j+1}=aa_j/(aL^{-2}+a_j)\), \(a_1=a_0=a>0\). | `ajSeq` (`ZR2Ops2.lean:21`) and `Qpa` (`ZR2Ops2.lean:27-30`). `aSeq` / `aSeqAux` (`ConstantA.lean:155-160`): \(d=a/L^2\), `aSeqAux a d 0 = a`. Weight in the sum is `ell^j`, not \((L^j\eta)^{d-2}\). | **Matches with the η-free, \(d=3\) convention.** \((L^j\eta)^{d-2}=\eta^{d-2}L^{j(d-2)}\). At \(d=3\) the \(j\)-dependent factor is \(L^j\). `Qpa`’s docstring says the body is η-free and \(d=3\). Removing the global factor \(\eta^{d-2}\) leaves the Lean weight. At \(\eta=1\) the two weights are equal with no factor to remove. |
| (3.23), p.394: \(\Delta_U^\eta=D_U^{\eta*}D_U^\eta\). | `lapFull = gradAdj.comp gradL2` (`R2Ops1.lean:108`), cited by `DelpA`. | **Matches**, as the \(\eta=1\) specialisation stated in the `R2Ops1` header. The covariant formula itself was not re-derived. |
| p.394: \(\Delta'_a\big|_{\Omega_0}=\Omega_0\Delta'_a\Omega_0\), \(\Delta'_a=(\Delta_U+Q'^*aQ')\) restricted to \(\Omega_0\). | `DelpA = siteMask Om0 ∘ (lapFull + Qpa) ∘ siteMask Om0` (`ZR2Ops2.lean:57-59`). | **Matches.** |
| p.394: the inverse of that Dirichlet operator is \(G'\), assuming positivity (the page says the operators are not yet known to exist). | `Gp = Ring.inverse(DelpA + (1 - siteMask)) ∘ siteMask` (`ZR2Ops2.lean:63-65`). `Gp_spec` (`ZR2Ops2.lean:130-173`): when the padded operator is a unit, `Gp f` is supported in \(\Omega_0\) and `DelpA (Gp f) = siteMask f`. | **Matches with the junk-value convention.** Where the inverse does not exist, `Ring.inverse` is 0. The print assumes the inverse. |
| (3.21)–(3.22): \(R\) is the orthogonal projection in \(L^2(\Omega_0)\) onto \(\Delta_U N(Q')\), \(N(Q')=\{\lambda:Q'\lambda=0\}\). (3.25): \(Rf=(I-G'Q'^*(Q'G'^2Q'^*)^{-1}Q'G')f\). | `Rproj = starProjection` of `lapDir '' NQp` (`R2Ops1.lean:162-172`). `NQp` (`R2Ops1.lean:162-168`) is support in \(\Omega_0\) and \(Q'_j=0\) on \(\Lambda_j\). | **Matches (3.21) with a stated convention. (3.25) is not the definition used.** The print says functions in (3.22) vanish on \(\Omega_1^c\) by the definition of \(N(Q')\). Lean imposes support in \(\Omega_0\) instead, which is the Dirichlet sentence later on the same page, and does not encode support in \(\Omega_1\). |
| (3.119), p.419: \(\langle A,\Delta_\pi A\rangle=\langle A-DG'RD^*A,\Delta(A-DG'RD^*A)\rangle\). | `Wop = 1 - gradL2 ∘ Gp ∘ Rproj ∘ gradAdj` (`ZR2Ops2.lean:67-69`). `DpiFull = Wop^* ∘ Delta ∘ Wop` (`ZR2Ops2.lean:83-84`). `inner_DpiFull` (`ZR2Ops2.lean:93-97`) is that identity. | **`Wop` matches** the map inside (3.119). **`DpiFull` matches with the D1 convention:** `Delta` (`ZR2Ops2.lean:79-81`) sums `plaqIn Ω₀` (both endpoints), not every plaquette of \(T_\eta\) as (3.10) does. That is sheet row 7 / deviation D1, not a new discrepancy in \(W\). |

### Numerics for Q8

Script: `AHP/fidelity/sheet-reading/numerics/reading_checks.py`. Seed 20261021. Absolute tolerance \(10^{-9}\). Side at most 4. Output: `numerics/results.json`.

`ajSeq` was evaluated in exact rationals against the printed recurrence for \((a,L)\in\{(1,2),(1/2,3),(3,5)\}\) and \(j=0,\ldots,6\) (21 values, all equal). For \(a=1\), \(L=2\) the sequence is \(1,1,4/5,16/21,64/85,256/341,1024/1365\). This is the same \(4/5\) as `aSeq 1 2 1` (`ConstantA.lean:246`), which is \(a_2\).

Weight check, \(d=3\), \(\eta=L^{-k}\). The ratio of the printed weight to `ell^j` is \(\eta\), independent of \(j\):

| \(L\) | \(k\) | \(j\) | \((L^j\eta)^{d-2}\) | Lean `ell^j` | ratio |
|---|---|---|---|---|---|
| 2 | 3 | 0 | \(1/8\) | \(1\) | \(1/8\) |
| 2 | 3 | 1 | \(1/4\) | \(2\) | \(1/8\) |
| 2 | 3 | 4 | \(2\) | \(16\) | \(1/8\) |
| 3 | 2 | 2 | \(1\) | \(9\) | \(1/9\) |

Dividing out \(\eta^{d-2}\) recovers `ell^j` in every row. At \(\eta=1\) the printed weight equals `ell^j` with nothing removed. A two-level comparison with \(a=1\), \(L=2\), one unit component at level 0 and one at level 1 gives weighted sum \(3\) and unweighted sum \(2\).

The mask arithmetic of `DelpA` and `Gp` was run on a random symmetric positive \(6\times 6\) matrix (4 sites in \(\Omega_0\)), not on `lapFull`. Over 8 right-hand sides: support of `Gp f` outside \(\Omega_0\) is 0, `DelpA(Gp f) - mask f` is at most \(8.9\times 10^{-16}\), and `Gp` agrees with the block inverse on \(\Omega_0\) exactly in float64. A rank-deficient \(\Omega_0\) block makes the padded operator singular (smallest singular value \(7.4\times 10^{-17}\)); that is the case where Lean returns the junk value 0, and `Gp_spec`’s `IsUnit` hypothesis fails. The junk value was not imitated.

The shape of `Wop` and `inner_DpiFull` was run with a random \(9\times 6\) matrix standing in for `gradL2`, a rank-2 orthogonal projection standing in for `Rproj`, and a random positive matrix standing in for `Delta`. The formula \(WA=A-DG'RD^*A\) holds to \(4.4\times 10^{-16}\). The two sides of (3.119) differ by at most \(1.2\times 10^{-13}\). This does not test the SU(2) covariant derivative.

## Q10 — the chain \(G^{-1}\to G\to G_1^{-1}\to G_1\to H_1\)

### Term by term

| Print | Lean | Row |
|---|---|---|
| (3.122), p.420, prose: \(G^{-1}=\Delta_\pi+DRD^*+Q^*aQ\). The display writes \(\tfrac12\langle A,(\Delta_\pi+DRD^*)A\rangle=\tfrac12\langle A,G^{-1}A\rangle-\tfrac12\langle B,aB\rangle\) on \(QA=B\). | `BaseDataS.Ginv = Dpi + Ts.comp T + Mass` (`R2Algebra.lean:145`). `T = R D^*` and `Ts` its adjoint (`ZXR2Ops3.lean:141-142`). `Tfull_adj_comp` (`ZR2Ops2.lean:104-114`) identifies \(DRD^*\) with \(T^*T\) because \(R^*R=R\). | **Matches.** |
| (3.16), p.393: \(\langle A,Q^*aQA\rangle=\sum_j a\sum_{b\in\Lambda_j}(L^j\eta)^{d-2}\lvert(Q_jA)(b)\rvert^2\). (3.128) and (3.125) write the same slot as \(a\lVert QA\rVert^2\). | `massW` (`ZXR2Ops3.lean:90-91`) is \(a\cdot\mathrm{ell}^j\). `inner_MassFull` (`ZXR2Ops3.lean:104-108`) is the weighted sum. `Mass` in `baseData` (`ZXR2Ops3.lean:146`) is that operator, projected to `bondSupp`. | **Matches with the stated convention that \(a\lVert QA\rVert^2\) means the quadratic form (3.16).** At \(\eta=1\), \(d=3\), the weight \((L^j\eta)^{d-2}\) is `ell^j`. The unweighted reading (scalar \(a\) times the square of the euclidean norm of \(QA\), no level weight) is a different number as soon as two levels are occupied. Lean implements (3.16), not that reading. |
| (3.122) / (3.27): \(G=(G^{-1})^{-1}\). | `BaseDataS.G = Ring.inverse Ginv` (`R2Algebra.lean:147`). | **Matches with the junk-value convention.** |
| (3.126), p.420: \(HB=GQ^*(QGQ^*)^{-1}B\). | `BaseDataS.H` (`R2Algebra.lean:149-151`), the same composition. | **Matches**, junk 0 when \(QGQ^*\) is not invertible. |
| (3.128), p.421: \(\langle A,G_1^{-1}A\rangle=\langle A,\Delta_\pi A\rangle-2\langle HC_\pi^{(2)}(A),J\rangle+\lVert RD^*A\rVert^2+a\lVert QA\rVert^2\), and the second display with \(A-DG'RD^*A\) in both \(\Delta\) and \(C^{(2)}\). | `BaseDataS.K` (`R2Algebra.lean:154-156`). `K_eq` (`R2Algebra.lean:168-170`): \(K(A)=\langle A,G^{-1}A\rangle-2\langle H(C_2 A),J\rangle\). `baseData` sets `C2 A = C2full (Wop A)` (`ZXR2Ops3.lean:147`), i.e. \(C_\pi^{(2)}(A)=C^{(2)}(WA)\). `G1inv` is `Classical.choose` of the unique symmetric operator with this quadratic form (`ZXR2Wire2.lean:61-64`, existence `R2Algebra.lean:186`). | **Matches**, with the (3.16) reading of \(a\lVert QA\rVert^2\) and with \(C_\pi^{(2)}\) read as \(C^{(2)}\circ W\). Uniqueness is `G1inv_unique` (`R2Algebra.lean:216`). |
| (3.129): \(H_1B=G_1Q^*(QG_1Q^*)^{-1}B\). | `BaseDataS.G1 = Ring.inverse G1inv` (`R2Algebra.lean:307`). `BaseDataS.H1` (`R2Algebra.lean:308-310`). | **Matches**, junk 0 if \(G_1^{-1}\) or \(QG_1Q^*\) is not invertible. |
| Not in (3.122)–(3.129): the wired family. | `G1in = η^{-1} · ι ∘ G_1 ∘ ι^*` (`ZXR2Wire2.lean:82-84`). `H1in = ι ∘ H_1 ∘ τ^*` (`ZXR2Wire2.lean:86-88`). `firstTerm = η ⟨τ^*B,(N)^{-1}τ^*B⟩` with \(N=Q\,(\mathrm{data.G1})\,Q^*\) (`ZXG3A.lean:35-51`). | **Matches with the η / τ\* convention (sheet item 8, open item S-3).** Algebra of those two lines: \((Q(η^{-1}G_1)Q^*)^{-1}=η(QG_1Q^*)^{-1}\), so `firstTerm` equals the quadratic form of \((Q\,\mathrm{G1in}\,Q^*)^{-1}\) and is \(η\) times the unscaled inverse. `H1` in (3.129) itself is not scaled. `τ^*` places \(B\) at the top level; the print’s \(B\) is not written that way. |
| Support of the base data. | `bondSupp` is bonds with at least one endpoint in \(\Omega_0\) (`ZXR2Ops3.lean:28-33`). `Dpi`, `T`, `Q`, `Mass` are conjugated by the inclusion (`ZXR2Ops3.lean:134-150`). | **Matches with the touching-bond convention for the bond space \(E_0\).** `Delta` inside `DpiFull` is still the both-endpoint plaquette set. The two conventions sit next to each other and are not the same set. |

### Numerics for Q10

Same script, dimensions \(E=6\), sites \(S=3\), constraint space \(F=3\). Not the lattice assembly in `baseData`. Level weights \((1,2,2)\) stand for \(a L^j\) at \(a=1\), \(L=2\), one level-0 row and two level-1 rows.

On 8 random vectors the symmetric operator \(G^{-1}-\Delta^{(2)}\) reproduces \(K\) to \(5.7\times 10^{-14}\), and `K_eq` holds to \(2.9\times 10^{-14}\). Smallest eigenvalue of the model \(G^{-1}\) is \(3.29\); the operator norm of \(\Delta^{(2)}\) is \(2.6\times 10^{-3}\); the margin is \(3.28>0\). Smallest singular value of \(QG_1Q^*\) is \(0.096\), so the inverse in (3.129) exists in this draw. \(H_1B\) agrees with the minimizer \(A=G_1Q^*\omega\), \(QG_1Q^*\omega=B\), to \(4.5\times 10^{-16}\).

The weighted mass and the unweighted \(a\lVert QA\rVert^2\) differ by at least \(2.57\) on those vectors. Replacing `Mass` by the unweighted operator moves \(\langle A,G^{-1}A\rangle\) by at least \(1.46\). So the refused reading is visible on this model, and it is not what the Lean weight computes.

For \(η=1/8\), `η ⟨B,(QG_1Q^*)^{-1}B⟩` equals `⟨B,(Q(η^{-1}G_1)Q^*)^{-1}B⟩` with residual 0 in float64, and the wired form is exactly \(η\) times the unscaled form.

## Q11 — \(\tilde B\) and \(C=\mathrm{id}-hQ_1\)

### Term by term

| Print, p.428 (render confirms the paragraph) | Lean | Row |
|---|---|---|
| Subspace \(\{B: B=0\text{ on }\Lambda^c,\ B=0\text{ on }\bigcup_{y\in\Lambda'}Ax(y),\ Q_1B=0\}\). | Split across three predicates. `OnLambdaTildeIn` (`ZStatementP428.lean:230-234`): zero on `staircasePath` for every \(y\in\Lambda'\) and every site of its block, and zero on dropped bonds. `OnLambdaT` (`ZR2A.lean:121-123`): zero unless at least one endpoint lies in \(\Lambda\). The constraint \(Q_1B=0\) is not required of \(\tilde B\); it is required of \(B=C\tilde B\) (`Cop_ker`, `ZXR2Unit2.lean:136-146`, and `Ingr.C_ker`, `ZStatementP428.lean:266-267`). | **Matches with the touching convention (sheet N1).** “\(B=0\) on \(\Lambda^c\)” read by applying CMP96 p.245’s “at least one endpoint” convention to the complement is the both-endpoint predicate `OnLambda` (`ZStatementP428.lean:198-201`). The headline `InstIneq` (`ZT5A.lean:56-62`) quantifies over `OnLambdaT`, the larger set. `InstIneq.toBoth` (`ZT5A.lean:80-84`) says the touching inequality implies the both-endpoint one. |
| \(\tilde\Lambda=\Lambda\setminus\bigl(\bigcup Ax(y)\cup\bigcup B(c)\cap c\bigr)\). | The same vanishing conditions, as just cited. `Ax` (`AxialContour.lean:153-154`) is the union of `staircasePath` (`AdmissibleSubspace.lean:366-370`) over the block minus the root. | **Matches.** The staircase order is coordinate 2, then 1, then 0. |
| \(B(c)\cap c\) is exactly one bond \(b_0\). The page does not say which fine bond of the straight edge. | `droppedBondLast` (`ReparamCDisjoint.lean:157-158`): the bond at offset \(\ell-1\) along \(c\), direction \(c\)’s direction. `IsDroppedIn` (`ZStatementP428.lean:216-219`) uses that bond for every coarse bond that touches \(\Lambda'\) (`CRowIn`, `ZStatementP428.lean:211-214`: either endpoint in \(\Lambda'\)). | **Matches with the stated convention that \(b_0\) is the last fine bond, offset \(\ell-1\), not the first.** |
| \(B=C\tilde B\). \(C\) is the identity except on the bonds \(b_0\), where \((C\tilde B)(b_0)\) solves \((QB)(c)=0\) as an equation in the single variable \(B(b_0)\). The subspace writes the constraint as \(Q_1B=0\); the prose writes \((QB)(c)=0\). | `Cop = id - hLift ∘ Q` (`ZXR2Unit2.lean:104-107`). `hLift = iotaD ∘ H0inv ∘ rhoD` (`ZXR2Unit2.lean:98-102`). `H0 = rhoD ∘ Q ∘ iotaD` (`ZXR2Unit2.lean:84-88`). `H0inv` is the inverse if `H0` is bijective and 0 otherwise (`ZXR2Unit2.lean:90-96`). `genC = Cop Lam Q1` (`ZXG3A.lean:58`). `Q1 = Q1jet` (`ZXR2Wire2.lean:71-72`), the local one-step jet (`ZXR2Unit1.lean:70-76`), not re-run here. | **Matches when `H0` is bijective, with two stated limits.** (1) The prose’s \(Q\) on the unit field \(B\) is the subspace’s \(Q_1\). (2) `Cop_ker` solves the joint linear system. The sentence “an equation on the variable \(B(b_0)\)” is the decoupled case, which the comment at `ZXR2Unit2.lean:10-18` already restricts to maps that do not read another row’s dropped bond. A coupled \(Q\) is still sent to a field with \(Q(CB)=0\), but the one-bond formula with the neighbours frozen is the wrong solution. When `H0` is singular, Lean’s `C` is the identity and does **not** solve \((QB)(c)=0\). That is the junk convention, not the printed sentence. |

### Numerics for Q11

Same script. One real component: `Cop` is \(\mathbb{R}\)-linear and `SuTwo` is an \(\mathbb{R}^3\)-vector space, so one component tests the same matrix. The torus has 4 sites on a side (extent value \(L_\mu+1=4\)), \(\ell=2\). \(\Lambda\) is the single block of the origin, 8 sites. This is a proper nonempty domain, not the whole torus.

Counts, transcribed from `blockOf`, `CoarseLattice`, `staircasePath`, `Ax`, `CRowIn`, `droppedBondLast`, `OnLambda`, `OnLambdaT`:

- 192 bonds, 8 coarse sites, 24 coarse bonds.
- \(\Lambda'=\{(0,0,0)\}\) only.
- 6 coarse bonds touch \(\Lambda'\) (3 based at the origin, 3 that arrive there).
- 7 axial bonds. The staircase transcription was checked on two paths: from \((0,0,0)\) to \((1,1,0)\) the bonds are \(((0,0,0),1)\) and \(((0,1,0),0)\); to \((1,0,0)\) the only bond is \(((0,0,0),0)\).
- 12 bonds have both endpoints in \(\Lambda\). 24 bonds touch \(\Lambda\) at exactly one endpoint. The two variable sets differ.
- All 6 dropped bonds are among those 24. The bonds \(C\) writes are invisible to the both-endpoint support. `droppedBondLast` did not collide.

`Q` in the script is **not** `Q1jet` (`ZLocJet.lean:39` is a Fréchet derivative and was not transcribed). Four linear maps were built, each cited as the \(Q\) that `Cop` (`ZXR2Unit2.lean:104-107`) takes.

| \(Q\) | What was checked | Result |
|---|---|---|
| Decoupled path sum, weights \((1,2)\) on the two fine bonds of \(c\). The path of a row does not contain another row’s dropped bond. | `Cop_id` and `Cop_ker` on 6 random fields, and the scalar solution \((CB)(b_0)=-\tfrac12 B(b_{\mathrm{first}})\). | Residuals 0. `H0=2I` (smallest singular value 2). The scalar solution is non-vacuous (largest absolute value in the sample \(1.23\)). On this one-block \(\Lambda\), every path bond is axial, dropped, or outside \(\Lambda\) (`path_bonds_visible_to_tilde = 0`), so a legal \(\tilde B\) is already in the kernel and \(C\) does not move \(b_0\). That is a fact about this \(Q\) and this block, not a failure of `Cop`. |
| Reads one \(\tilde B\)-legal bond plus \(2B(b_0)\). The free bond found is \(((0,1,0),2)\), both endpoints in \(\Lambda\), not axial, not dropped. | Same identities, and on a random touching \(\tilde B\): \((C\tilde B)(b_0)=-\tfrac12\tilde B(\mathrm{free})\). | Residuals 0. For the sampled \(\tilde B\), the value written on every \(b_0\) is \(-0.437\), with formula error 0. So \(C\) does move \(b_0\) when \(Q\) can see a bond \(\tilde B\) is allowed to carry, and \((Q\,C\tilde B)(c)=0\) on all 6 rows. |
| Coupled, dropped bonds only: \(2B(b_0(c))+0.3B(b_0(c_{\mathrm{next}}))\). | `Cop_ker` against a one-bond formula that freezes the neighbour. | `Cop` residual at most \(5.9\times 10^{-17}\), and \(C\) sets every \(b_0\) to 0 (the only solution of a dropped-only invertible system). The frozen-neighbour formula leaves a residual of at least \(0.45\). The joint reading holds; the one-variable reading does not, on this \(Q\). |
| Ignores \(b_0\) (reads only the first path bond). | The junk branch `H0inv = 0`. | `H0` singular (smallest singular value 0). `C` is the identity (residual 0). \(Q(CB)\) on the rows has size \(2.57\), so the equation is not solved. |

A random both-endpoint field satisfied `OnLambda`, `OnLambdaT` and `OnLambdaTildeIn`. A random touching field satisfied `OnLambdaT` and `OnLambdaTildeIn` and failed `OnLambda`. The inclusion used by `InstIneq.toBoth` is visible on this torus: 24 bonds are allowed by the touching predicate and forbidden by the both-endpoint predicate.

## What was not run

`gradL2`, `lapFull`, `Qlev`, `QlinStepL`, `Q1jet`, the plaquette sum inside `Delta`, and the SU(2)-valued field were not transcribed. The numerical \(Q\) is a stand-in for the linear map `Cop` is proved for, which the Lean file says is any linear \(Q\). Identifying that \(Q\) with the printed one-step jet remains the separate convention D10/D11.

## Stage B

No new proof target. The rows are reading questions, and the algebraic identities they turn on (`Gp_spec`, `inner_DpiFull`, `K_eq`, `Cop_id`, `Cop_ker`, `InstIneq.toBoth`) are already in the frozen tree.

Optional audit file, only after `REPRODUCE.sh` has finished and the oleans exist: `AHP/fidelity/sheet-reading/lean/ReadingAudit.lean`. It should `#check` and `#print axioms` the declarations above and not state a new theorem. Do not edit `lean/`, the lakefile, `paper/`, `notes/`, or `expected/`. `lake env lean` on that file is enough; it does not need to be a Lake module.

Imports:

```lean
import ZR2Ops2
import R2Ops1
import R2Algebra
import ZXR2Ops3
import ZXR2Unit2
import ZXR2Wire2
import ZXG3A
import ZStatementP428
import ZR2A
import ZT5A
```

Declarations to print: `inner_Qpa`, `Gp_spec`, `inner_DpiFull`, `Tfull_adj_comp`, `Rproj_adjoint_mul`, `BaseDataS.K_eq`, `BaseDataS.exists_G1inv`, `BaseDataS.G1inv_unique`, `Cop_id`, `Cop_ker`, `InstIneq.toBoth`.

Expected axioms: a subset of `propext`, `Classical.choice`, `Quot.sound`. Any `sorryAx` is a failure of the audit, not a result about the reading. The reading itself is closed by the term table above, not by those prints.

# S-3 pin: the first term of (3.156)

## Disposition

**PINNED, not proved or refuted.** `Statement.lean` contains independently assembled physical-unit first terms, four open propositions, and three logical contract checks. It does not import any AHP file. Its sole import is the frozen `ZT5A` module.

Primary target: **`AdalyFormal.Round2.S3Pin.GoalPos1`**, exact equality with constant **\(c(\ell,k)=1\)**. This is the plain-H convention explicitly offered on p.421. `GoalPos2` pins the other, linked H/C convention offered in the same sentence. Both are supported by the pages; they are representations of the same intended construction, not competing powers chosen independently for H and C.

The important correction to the earlier Stage-A design is the **argument of \(C_j\)** in (3.14). The old `plainH = eta² raw` recipe paired with *plain* H is not the plain-H recipe of the printed paragraph. The old `draft` and `linearEta` recipes are not retained as defensible additional readings. No old matrix calculation or depth-one comparison is an open goal here.

## Goals, in plain words

All names below have namespace `AdalyFormal.Round2.S3Pin`.

| Goal | Exact content |
|---|---|
| `GoalPos1` | At every encoded admissible configuration, every depth \(k\ge1\), and whenever all inverses used on either side exist, the frozen `GenP.firstTerm P B` equals `PrintedFirstTerm P .plainH B` for every admissible printed test field B. No restriction to flat U, full support, top-only jets, or depth one. |
| `GoalNeg1` | One such actual configuration with \(k\ge2\), and two nonzero admissible fields, for which both printed values are nonzero and the frozen/printed ratios differ, using `.plainH`. |
| `GoalPos2` | The same exact equality with `.dimensionlessH`: H divides each level input by its spacing, while C uses the quadratic coefficient at the correspondingly scaled argument. |
| `GoalNeg2` | The same genuine depth-at-least-two ratio witness for `.dimensionlessH`. |

The compiled helpers `GoalNeg1_implies_not_GoalPos1` and `GoalNeg2_implies_not_GoalPos2` prove the required negative-to-negation implication. `RatioWitness_no_scalar` proves more: a witness rules out **every** scalar on that configuration's admissible subspace, even a scalar depending on U or the geometry. Thus it rules out any positive scalar depending only on \((\ell,k)\). None of these helpers supplies a witness or proves a positive goal.

Exact equality is selected instead of an unspecified existential scalar. A depth-dependent scalar alone would not automatically preserve a depth-uniform coercivity constant, nor would changing only one summand rescale the entire quadratic form. The choice \(c=1\) avoids both problems. This pin concerns the requested **first summand**, not a new proof of the entire coercivity inequality.

### Configuration and test-field quantifiers

`AdmissibleConfiguration P` uses the actual `IngrBParams`, including actual `LinkCfg` U, the tower, unit torus, Lambda and mass parameter. It requires:

- \(\ell\ge2\), \(k\ge1\), \(a>0\);
- some \(m\ge1\), \(R\ge18\), \(\alpha>0\), with \(M=\ell^m\);
- the frozen `TorusOK`, `Admissible`, `LambdaOK2`, and factor-12 `ClassCoupled` predicates, with \(\eta=\ell^{-k}\).

`AdmissibleB` is the subspace printed after (3.156): touching Lambda support, zero on the frozen axial staircases based at `LamPrime`, and **global** `P.Q1 B = 0`. It is not an arbitrary two-coordinate vector and not merely the selected `CRowIn` equations. We do not assert here that every frozen `Cop Bt` meets these three requirements; the positive goal could usefully be proved for all B, which would remove that separate parametrization issue altogether. No invertibility of `H0` is needed to evaluate the first term: C and the one-step lift are not used in its definition.

`InversesExist` explicitly guards the padded site operator, G, its constraint covariance, G1, and its constraint covariance, **on both sides**. No assumed equality appears in this guard. Invertibility is not claimed to imply positivity. The comparison is threshold-free algebra once these inverses exist; we have not introduced or purported to find the print's unspecified smallness threshold. A negative answer would be a normalization counterexample on this guarded encoded regime, not by itself a counterexample to the sufficiently-small-field coercivity headline.

## Source evidence and line convention

A citation such as **p.421:28** means printed page 421, **line 28 of `sources/corpus/pages/CMP99b_p421.md`**. Long printed paragraphs occupy one transcription line. Equation numbers provide independent locators.

Read the required corpus pages 393–396 and 421–428, additionally 392, 419 and 420 for the preceding definitions. Directly inspected the renders of (3.24), (3.119), (3.122), (3.126)–(3.129), (3.136), (3.156) and (3.157), plus (3.8), (3.10)–(3.16). In particular:

- **p.393:28**, (3.14), has `C_j(U, L^j eta A)`, not `C_j(U,A)` in that position.
- **p.421:28** offers H with an input factor \((L^j\eta)^{-1}\), **or** plain H together with \(L^j\eta C_j^{(2)}(A)\).
- **p.422:92**, (3.136), has exponent \(d+1\) and starts its level sum at 1.
- **p.428:32**, (3.156), has neither an external eta nor a tau; **p.428:35** states the constrained B subspace. **p.428:40–43**, (3.157), is the C-parametrized Gaussian identity, not a license to invert a top-level compression.

The original PNGs exceed the image reader's dimensions. `renders/p392.png`, `p393.png`, `p394.png`, `p419.png`, `p420.png`, `p421.png`, and `p428.png` are proportional reductions of the existing corpus renders to at most 1900 pixels per side. The corpus p.422 PNG is absent on this machine; `renders/p422.png` was rendered from PDF page 34 of the repository's CMP99b PDF with pypdfium2 5.14.0, scale 2.5, then reduced with Pillow 13.0.0. These temporary packages were installed only under this item's directory and removed after image inspection. No dependency/configuration file elsewhere was changed.

The source PDF SHA-256 is `39f8033b35838c7bdd14f97c7fb1edb0b35d4190b8b88f31d19d12a72d542861`, matching the corpus metadata. The derived p.422 image SHA-256 is `d283740aca6d64c8a8637528087c54cd3b1fd8dd649159414497dc29fb3578ab`.

## Physical-unit dictionary

Let \(s_j=\ell^j\eta\), \(d=3\), \(W_F=\operatorname{diag}(s_j^3)\), and let a superscript \(t\) mean the **unweighted** real Hilbert adjoint. A subscript `body` below refers to the frozen unit-spacing construction, not to an independently chosen matrix. Frozen file locators in the table are relative to `lean/src/`.

The following table pins the intended coordinate identifications and their source. These are the dictionary to establish in proving the open goals, **not additional hypotheses** and not a claim that the full dictionary has already been proved.

| Printed object / convention | Concrete pin and intended relation to frozen objects | Source and frozen locators |
|---|---|---|
| Unit vs fine coordinates | Unit site y is fine site \(\ell^k y\); fine spacing \(\eta=\ell^{-k}\); level j spacing \(s_j\), top spacing 1. `mesh`, `spacing`, `unitBondEmb`. | p.393:49–53; p.427:39. `ZXR2Wire1.lean:27–29`, `ZXR2Wire2.lean:37`. |
| Lie-algebra chart and trace | Physical A has the same numerical value in the skew-Hermitian chart \(iA_h\); the expansion variable is \(\eta A\), **not** a second rescaling of the stored physical field. Normalized trace gives \(-\tfrac12\operatorname{ReTr}(XY)\). | p.392:61,107–120; `AdalyFormal/Balaban/SuTwoInner.lean:101–112,483–486`, `ZXR2Wire2.lean:45–53`. |
| Fine pairing | `finePair = eta³ * inner`. Same measure on fine sites. | p.392:103; p.393:87–88. |
| Multilevel pairing | `levelPair f g = inner f (W_F g)`. Each level has its own \(s_j^3\) volume. | p.393:51,57; p.422:50,61,92. This extends the explicitly printed fine measure to the indicated coarse lattices; the kernel and (3.136) powers corroborate it. |
| D and D* | `PrintedD = eta⁻¹ gradL2`; `PrintedDs` is its adjoint. The two fine measures are equal, so no extra volume quotient appears in this adjoint. | (3.8), p.392:66–70; (3.23), p.394:58. `R2Ops1.lean:76–88`. |
| Site mass and G' | `PrintedQpa` uses **recursive** `ajSeq`, weight \(a_j s_j\), divided by the fine metric \(\eta^3\). `PrintedDelp` is the physical Dirichlet sandwich; `PrintedGp` inverts it on the site subspace. Expected \(G'_{phys}=\eta^2 G'_{body}\), after handling the exterior padding correctly. | (3.24), p.394:66–70 and Dirichlet paragraph 70–85. `ZR2Ops2.lean:22–63`. |
| R and gauge extension W | `PrintedR` is the projection onto the image of the **physical** Dirichlet Laplacian of `NQp`; `PrintedW = I - D G' R D*`. Expected R and W agree with their frozen bodies. | (3.21)–(3.23), p.394:38–58; (3.119), p.419:55. `R2Ops1.lean:169–181`, `ZR2Ops2.lean:66–67`. |
| Delta and Delta-pi | `PrintedDelta = eta⁻² Delta`; `PrintedDpi` is rebuilt as the restriction of \(W^t\Delta W\). Hence its physical quadratic form has overall factor eta relative to its body. | (3.10), p.392:90–94; (3.119), p.419:55. `ZR2Ops2.lean:75–83`. Localisation departure below. |
| Q | `PrintedQ = QfullOf` restricted to `bondSupp`, hence expected equal to `P.data.Q`: row j is \(\ell^{-j}\) times the genuine raw first jet. | (3.14)–(3.15), p.393:28–41. `ZXR2Sector.lean:57–71,97–107`. |
| Q* | `PrintedQs = eta⁻³ Q^t W_F`. This is the adjoint determined by the two physical pairings, **not** `P.data.Qs` itself. | Same pairing sources; (3.122)/(3.126), p.420:25–38,82. `ZXR2Ops3.lean:140–141`. |
| Bond mass | `PrintedMass = PrintedQs diag(a*s_j⁻²) PrintedQ`; its form is \(\sum a s_j\lVert Q_j A\rVert^2\). Expected coordinate operator \(\eta^{-2}\) times the frozen bond mass. **Constant a**, not `ajSeq`. | (3.16), p.393:57; (3.128), p.421:33–37. `ZXR2Ops3.lean:98–115`. |
| G, plain H | Rebuilt from (3.122) and (3.126) with the physical adjoint. Expected \(G_{phys}=\eta^2G_{body}\) and \(H_{phys}=H_{body}\) as maps on the common numerical field coordinates. The constraint metric cancels through the inverse; this is an obligation, not a premise. | p.420:25–38,82. `R2Algebra.lean:145–150`. |
| Source J | `PrintedJ = pE (-JSU2Loc eta ...)`, with actual U. Expected \(J_{phys}=\eta^{-3}P.data.J\). The eta³ fine pairing cancels this factor **for a fixed paired field only**. | (3.11), p.392:103–107; `ZLocJ.lean:71–89`, `ZXR2Wire2.lean:45–53`. |
| Raw second jet | The actual bilinear map is `D2B P.G P.U j`, with diagonal `C2rawB = 1/2 D2B(A,A)`. No free jet, arbitrary source or abstract matrix is quantified. | `ZLocJet.lean:90–117`, `ZXR2Sector.lean:73–89`; nonlinear raw map (3.13), p.392:119–120; (3.14), p.393:28. |
| Printed \(C_j^{(2)}\) | `PrintedCjBil` evaluates that raw bilinear jet on **two** \(\ell^{-j}A\) inputs. Thus \(C_j^{(2)}(A)=\ell^{-2j}\mathrm{raw}_j(A)\). | (3.14), p.393:28; derivation below. |
| C, plain-H convention | `PrintedCBil .plainH` uses \(s_j C_j^{(2)}(WA)\): expected \(\eta\ell^{-j}\mathrm{raw}_j(WA)\), hence eta times frozen C after W is identified. | p.421:28,33–36; frozen `ZXR2Sector.lean:109–111`, `ZXR2Ops3.lean:143`. |
| C, dimensionless-H convention | `PrintedCBil .dimensionlessH` uses \(C_j^{(2)}(s_j WA)\), while `PrintedHFor` is \(H\operatorname{diag}(s_j^{-1})\). Neither of these two changes may be made alone. | p.421:28; p.422:67–70. |
| G1 | `PrintedKBil` assembles the full (3.128), including actual J and the quadratic composite jet. `PrintedG1inv` is its symmetrized Riesz representative **divided by eta³**, and `PrintedG1` its inverse. Expected \(G_{1,phys}^{-1}=\eta^{-2}P.G1inv\), \(G_{1,phys}=\eta^2\,\texttt{(P.data.G1 P.G1inv)}\). | p.421:33–45; `R2Algebra.lean:153–161,306–309`, `ZXR2Wire2.lean:58–64`. |
| `G1in` vs physical G1 | `G1in = eta⁻¹ iE G1_body pE` is the **kernel/unweighted-dual representative**, not the physical coordinate action on a source integrated with eta³. Multiplying that kernel representative by the fine volume gives \(\eta^2 iE G1_{body}pE\). Do not conflate the two. | `ZXR2Wire2.lean:80–84`; fine measure p.392:103; the printed inverse construction p.421:33–45. |
| B and tau* | `PrintedB` explicitly inserts unit B into level k and zeros all lower levels. Intended equality `PrintedB P B = adjoint P.tau B` has **no scalar**; top measure is 1. We did not define insertion by tau*. | p.427:39–48; p.428:32–35. `ZXR2Wire1.lean:27–44`; previous **full-support-only** result `ZGU1D.lean:55–87` is not asserted at general support. |
| Inverse order | `PrintedN` acts on **all of F**. Only after its inverse is formed is it evaluated on the inserted top-level B. Expected \(N_{phys}=\eta^{-1}N_{body}W_F\), hence \(N_{phys}^{-1}=\eta W_F^{-1}N_{body}^{-1}\). | p.420:34–38,82; p.421:45; p.422:50–54; p.428:32. Frozen `ZXG3A.lean:35,50`. |
| First term | \(\langle E_kB,N_{phys}^{-1}E_kB\rangle_F\), with the physical pairing. The intended cancellation yields the frozen external eta, without placing one in the printed definition. | (3.156), p.428:32. The actual equality is **GoalPos1/2**, not an imported theorem. |

### Why the old power count is not pinned

Write \(\mathrm{raw}_j(A)=\tfrac12 D^2q_j(0)[A,A]\). Multiplying (3.14) by \(s_j\) and comparing its second-degree part gives

\[
 C_j^{(2)}(s_j A)=\eta^2\mathrm{raw}_j(A).
\]

Because the left side is quadratic in its **argument**, this identifies

\[
 C_j^{(2)}(A)=\ell^{-2j}\mathrm{raw}_j(A),\qquad
 s_j C_j^{(2)}(A)=\eta\ell^{-j}\mathrm{raw}_j(A).
\]

The old Stage-A `plainH` recipe identified the second coefficient of a *quotient* with \(C_j^{(2)}(A)\) without undoing the argument rescaling. Its \(\eta^2\mathrm{raw}_j\) is the raw/dimensionless input **before** the \(s_j^{-1}\) in H, not the input to plain H. In the code here this distinction is visible in `PrintedCjBil`, `CInputScale`, `COutputScale`, and `PrintedHFor`. The original numerical scripts were read but not rerun, copied or modified.

Equation (3.136) corroborates rather than changes this dictionary: transferring H across the pairing gives a level measure \(s_j^3\), and the plain-H C input supplies one further \(s_j\). Differentiating its quadratic form yields the displayed \(s_j^{d+1}=s_j^4\). It is **not** another factor to multiply into C on top of those already accounted for. The level-zero raw second jet is zero by the actual recursion, explaining the printed level sum beginning at 1.

This argument is a source/coordinate derivation explaining the definition. The requested Lean comparisons of the whole physical inverse chain at arbitrary depth are still open. In particular, neither the argument nor the earlier depth-one theorem is being counted as a proof of `GoalPos1`.

## Every retained departure / limitation

1. **Scope specialization:** dimension 3, gauge group SU(2), finite periodic rectangular tori and real skew-Hermitian coordinates. The print allows more general dimension/group and uses Hermitian coordinates. Normalized trace is retained, not replaced with the full Frobenius norm.
2. **Geometry:** frozen aligned half-open blocking, periodic l1 distance, natural radii, empty tower padding above k, fixed factor-12 boxes, and the p.396 choice of Omega0 are retained. The alternative thinner operator domain on p.394 is not separately introduced. R>=18 and M a positive power of ell retain the encoded operating regime rather than asserting that 18 is the source's optimal radius. Powers of R and odd-only ell are not imposed.
3. **Coverage/class:** `ClassCoupled` includes the disclosed site and inside-plaquette coverage clauses; its cube regularity uses the frozen both-endpoint `CubeBond`. We are not identifying these extra clauses with the p.396 prose or solving S-2.
4. **Boundary/localization:** `bondSupp` has touching bonds; `bondsLam` uses the frozen touching-minus-next-level selector. Delta and J retain the inside-plaquette `plaqIn` restriction. The print writes unrestricted plaquette sums in (3.10)/(3.11) and states Dirichlet conditions in prose. Calling these definitions “Printed” therefore means **the pinned printed scale reading on the fixed S-1 localisation convention**, not a claim that the separate S-1 reading is settled. Changing selectors at the same time would confound this item.
5. **Primitive averaging implementation:** the actual frozen per-component jets and actual background tower are shared. They are not arbitrary matrices, and no global `RegTower` premise is added (it would impose unprinted control outside Omega0). The per-component implementation/fidelity and analytic existence on the printed class are inherited issues, not discharged here. Neither raw jets nor J can be freely chosen by a counterexample builder.
6. **Physical inner products represented in unweighted carriers:** positive diagonal metrics are explicit rather than new Lean inner-product instances. The unweighted Riesz conversion and symmetrization are exact finite-dimensional constructions, not stand-ins for unknown operators. The weighted-adjoint and scale dictionary still require proof.
7. **Inverse convention:** `Ring.inverse` totalizes definitions, but every inverse used by an open comparison is guarded, including both versions of the padded site operator. No singular fallback can serve as a negative witness. We do not prove these guards from regularity, nor replace invertibility with positivity.
8. **Test subspace:** touching Lambda support and the frozen staircase realization of Ax are retained; global Q1 kernel is imposed as printed. C-parametrization support/constraint transfer is not assumed. Proper nonempty domains are allowed but not required; a ratio witness necessarily supplies two genuinely nonzero fields. No full-support simplification is built into the goals.
9. **Quantifiers:** these are first-term normalization identities on the guarded regime, with no cofinal threshold refutation of the coercivity theorem. They do not reprove source smallness estimates. Exact equality uses scalar 1, independent of all geometry, background, mass, depth and field.
10. **Other summands:** the constant-a subtraction, the final unit one-step nonlinear term involving `D2in`, and `bondEnergy` are not additional open goals in this pin. Their common units are not certified by compiling a definition of the first summand. Likewise no equality of inverse-of-compression and compression-of-inverse is asserted.
11. **Reading coverage:** the two source-offered H/C representations are pinned separately. The old stand-in `plainH`, `draft`, and `linearEta` alternatives are rejected for the argument-tracking reasons above, not proved false as genuine lattice models. No assertion is made that every conceivable historical/source interpretation has been exhausted.

## Compilation and acceptance boundary

Run exactly, serially, from the existing frozen project:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s3-normalisation/pin/Statement.lean > ../AHP/round2/s3-normalisation/pin/Statement.lean.log 2>&1
echo $? > ../AHP/round2/s3-normalisation/pin/Statement.lean.exit
```

**Verified final run: exit 0, no warnings or errors.** All 15 dependency records contain only `propext`, `Classical.choice`, `Quot.sound`. The sibling `Statement.lean.log` and `Statement.lean.exit` are the verification artifacts. A separate check confirmed: sole import `ZT5A`, eight `#check` commands, four `def Goal… : Prop` declarations, three logical helper theorems, no forbidden construct, and removal of the temporary image packages.

- `Statement.lean` SHA-256: `9133de3969b6a26d2f6c373d4bb56c1d0ce6d545bd161b69a851e6af2416962c`.
- `Statement.lean.log` SHA-256: `a27a45e83b590973229c22a5490eb2c49992bcbf74e84cfbdab22506a326e282`.
- Locations: `PrintedFirstTerm` line 247; `AdmissibleB` 253; `AdmissibleConfiguration` 263; `InversesExist` 273; `GoalPos1` 283; `GoalPos2` 290; `RatioWitness` 297; `GoalNeg1` 305; `GoalNeg2` 307; logical helpers 310–330.

The eight `#check` commands cover the first term, configuration/test/guard predicates, and all four goals. **Axioms printed for a `def ... : Prop` validate its dependencies; they do not prove the proposition.** The only proved propositions in this file are the three negative-contract helpers.

No `lake build`, `REPRODUCE.sh`, or `lake update` was run. No numerical lattice experiment was run. No file outside `AHP/round2/s3-normalisation/` was written, and no commit or push was made. This completes the requested **pinning** task only; S-3 requires a proof of a positive goal or a genuine negative witness after review of this source dictionary.

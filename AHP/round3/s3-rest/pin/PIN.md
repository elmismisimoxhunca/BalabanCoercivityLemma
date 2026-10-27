# Round 3 S-3 rest — statement pin

## Scope and status

**PIN ONLY.** The new question is the **whole (3.156) form and (3.157) instance inequality**, including the separate mass subtraction, final nonlinear term, and the metric on the independent variables. The already-proved first-term comparison is reused as a dictionary, not submitted as a new open goal.

`Statement.lean` imports only frozen `ZT5A`. Key new locations: mass subtraction line 314, bond energy 319, unit raw jet 341, remainder 356, corridor inverse 370, Dtilde 379, C 384, H1 390, final nonlinear term 404, full form 408, full inequality 414; `GoalPos1/2` at 451/457, `GoalNeg1/2` at 513/514. The definitions from `abbrev Fine` through `InversesExist` are copied **verbatim**, in their original namespace `AdalyFormal.Round2.S3Pin`, from `AHP/round2/s3-normalisation/pin/Statement.lean`. No AHP module is imported. The old goals and proofs are not copied. New declarations have namespace `AdalyFormal.Round3.S3Rest`.

The candidate constant is explicitly **\(c(\ell,k)=1\)**; **a is unchanged**. This is not an existential constant to be fitted after seeing U or a test field. Both p.421 H/C conventions are quantified in each positive goal.

The key remaining source issue is identified, not hidden: **CMP99b p.427 describes \(\widetilde D^{(2)}\) qualitatively but does not give its coefficients.** Its concrete realization is supplied by the frozen code's cited later source, **CMP109 p.267**, independently rendered and read for this pin. That page's (2.11) explicitly refers back to CMP99b (3.156) and prints the contribution \(\langle H_1 h\widetilde C^{(2)},J\rangle\). Thus the expression inserted into H1 in the current pin is the **lifted unit remainder**, not a freely chosen quadratic map.

## Goals, in plain words

| Goal | Content |
|---|---|
| `GoalPos1` | At every round-two admissible configuration, every depth k >= 1, under exactly the round-two inverse guards, and for **each** p.421 H/C convention: the separate mass and nonlinear terms agree for all B; the whole form agrees for all B; the reconstructed C and bond energy agree for all independent fields; and frozen `InstIneq gamma` is equivalent to `PrintedInstIneq (1*gamma)`. Uses the **raw unit constraint** and raw quadratic remainder together. |
| `GoalPos2` | The same statement, with the unit constraint **and** its quadratic remainder both divided by ell. The corridor inverse changes along with the constraint. This is the linked normalized representation, not a change of only the nonlinear summand. |
| `GoalNeg1` | A genuine configuration at depth >= 2 and a p.421 H/C reading, with the original inverse guards **and nonsingular corridor matrices**, two nonzero admitted independent fields whose C-images satisfy the printed support/Ax/global-Q1 subspace, nonzero denominators, and unequal final-nonlinear/independent-energy ratios. In addition it must satisfy `NoGammaMassRepair`: an actual inequality truth-value separation for every positive gamma/a rescaling for which the rescaled inverses exist. Uses the raw constraint. |
| `GoalNeg2` | The same strong witness for the linked normalized constraint. |

`ScaleWitness_not_comparison`, `GoalNeg1_implies_not_GoalPos1`, and `GoalNeg2_implies_not_GoalPos2` are **logical contract checks only**. They supply neither a comparison proof nor a witness.

### A necessary distinction about the negative request

Unequal summand ratios disprove a common **termwise normalization**, but **alone they do not prove non-equivalence of two universally quantified inequalities**. Even two different positive quadratic forms on one finite-dimensional test space have sharp lower bounds, and those two numbers can be matched by a suitable gamma rescaling. Nor does a changed coefficient of the mass term by itself exclude rescaling a.

The negative goals therefore do **not** make that invalid inference. They include the additional, explicitly named `NoGammaMassRepair` obligation. It states that for every positive c and d whose rescaled instance has the requisite inverses, there is a **positive gamma** for which

\[
\operatorname{InstIneq}(P,\gamma)
\quad\not\leftrightarrow\quad
\operatorname{PrintedInstIneq}(P[a\leftarrow d a],c\gamma).
\]

Changing a here changes it **everywhere**, including G', G1 and the inverses, not just the visible subtraction. No singular rescaled instance is allowed to furnish the separator. The witness is deliberately stronger than the exact negation of `GoalPos1/2`; failure to construct it does not prove either positive goal. In particular, a ratio calculation without `NoGammaMassRepair` must be reported only as a termwise obstruction, not as a refutation of equivalence of the complete inequalities. These strong negative goals also exclude factors depending only on (ell,k), since they exclude every scalar pair already at the witnessed configuration.

The equality goals test **all B**, not merely B satisfying constraints. This avoids importing an unproved assertion that every frozen `Cop Bt` satisfies global Q1. The actual instance comparison retains exactly the frozen independent-field domain. Negative ratio fields additionally satisfy the stricter printed subspace and use the same parametrized field on both sides.

## Reused dictionary and guards

The round-two dictionary is unchanged: fine mesh \(\eta=\ell^{-k}\), level spacing \(s_j=\ell^j\eta\), fine pairing \(\eta^3\langle\cdot,\cdot\rangle\), level pairing with weights \(s_j^3\), physical weighted adjoints, genuine componentwise averaging jets, explicit top insertion, and inverses on the **whole multilevel space before insertion/compression**.

`AdmissibleConfiguration` is copied, not weakened to a toy geometry: actual `IngrBParams`, ell >= 2, k >= 1, a > 0, some m >= 1, R >= 18, alpha > 0, M = ell^m, and actual `TorusOK`, `Admissible`, `LambdaOK2`, factor-12 `ClassCoupled`. No flat-background or full-support restriction is added.

`InversesExist` is also copied verbatim: the frozen and printed padded site inverses, G, constraint covariance, G1 and its constraint covariance are guarded. **There is no extra hypothesis in either positive goal.** The new linear-map corridor inverse is totalized, just like the frozen `H0inv`; equality at a singular corridor is a statement about the extensions, not existence of a printed inverse. `CorridorInversesExist` isolates the physical regime of this newly used inverse; every negative witness requires it. On that regime the positive goals, if proved, would establish the requested ordinary-inverse comparison as well. Deriving the raw/normalized corridor guards from the frozen bijectivity guard is a possible proof step, not an assumed comparison.

No positivity, smallness threshold or non-vacuity of the guards is inferred from invertibility. The new goals are algebraic normalization tests in the retained encoded regime, not proofs of inverse existence from printed regularity.

## Printed counterparts, including all scale choices

Page citations are **printed page numbers**. Equation numbers locate the displays. `p.NNN:line` below means a line of `sources/corpus/pages/CMP99b_pNNN.md` where needed. Frozen file paths in this table are relative to `lean/src/`.

| Object | Construction in the pin | Printed source / frozen definition being tested |
|---|---|---|
| Lie-algebra pairing | `PrintedTracePair X Y = -ReTr(XY)/2`; skew-Hermitian chart X=iA_h. | CMP99b p.392 first sentence: normalized trace, tr 1=1; (3.11). Frozen `AdalyFormal/Balaban/SuTwoInner.lean:104-106,483-486`. No unnormalized Frobenius norm branch: the print explicitly fixes this convention. |
| Unit pairing | `PrintedUnitPair = sum_b 1^3 * PrintedTracePair`; same numerical unit field B. | p.427 Sect. E says unit lattice; p.392 (3.11) gives lattice-volume pairing; p.393 (3.16) places level k at s_k=1. No eta^3 multiplies the unit B pairing. |
| Mass subtraction | `PrintedMassSubtraction = a * PrintedUnitPair B B`. | p.427 (3.155), p.428 (3.156). **Constant a**: p.393 (3.16), p.420 (3.122), p.421 (3.128). The a_j recursion at p.394 (3.24) is for the site mass only. Compare `ZXG3A.lean:54-55`. |
| Independent-field energy | `PrintedBondEnergy Bt = PrintedUnitPair Bt Bt`. Bt is zero-extended from the tilde domain; it is **not C Bt**. | p.428 (3.157)-(3.158) and the following lower-bound sentence. Compare `AdalyFormal/Balaban/RegularUPerturbation.lean:355-356` and `ZT5A.lean:56-61`. |
| Unit raw Q | First derivative of the actual raw one-step component map on the actual blocked unit background, reconstructed as `PrintedUnitRawQ`, not defined by P.Q1. | pp.392-393 (3.13)-(3.15); the eta=1 specialization has raw derivative ell*Q1. Primitive `ZLocJet.lean:39-40`, unit assembly `ZXR2Unit1.lean:69-77`, background `ZXR2Wire2.lean:67-69`. |
| Unit raw second coefficient | `C2StepL 1 ell unitBgU`, transported through the fixed su(2) coordinates and read at the coarse bond. Its definition includes the Taylor 1/2. | p.393 (3.14), p.427 description after (3.155); CMP109 p.267 gives the explicit linearizing change. Primitive `ZLocJet.lean:89-101`; frozen `C2tilde`, `ZXR2Unit1.lean:80-82`. No arbitrary second jet or independent J is permitted. |
| Raw / normalized constraint | Raw: Q_raw and R_raw. Normalized: Q_raw/ell and R_raw/ell. | p.393 (3.14), j=1 and eta=1. **Both** the linear part and remainder change. CMP109 p.267 uses raw equation L*Qtilde B + Ctilde(B), hence supports the raw representation directly. |
| Corridor matrix and lift | `rho * PrintedUnitQ * iota`; invert that finite coupled matrix; then `iota * inverse * rho`. All are genuine linear maps on the actual dropped variables. | p.428 text between (3.156) and (3.157); CMP109 p.267: h supported on b0, L*Qtilde*h=I. Frozen `ZXR2Unit2.lean:84-105`. The coupled solution is a disclosed realization; source single-row decoupling is not proved here. |
| Dtilde | Apply that corridor lift to the matching unit quadratic remainder, obtaining a **unit-bond field**. | CMP109 p.267: Dtilde^(2)=Ctilde^(2) before h, change B'=B-h Dtilde(B), and (2.11) prints H1 h Ctilde^(2) and cites (3.156). CMP99b p.427 alone does not specify this formula. Compare frozen `ZXR2Wire2.lean:90-91`: ell^-1 times hLift applied to raw C2tilde. |
| Physical H1 | Independently assembled `PrintedG1 * PrintedQs * inverse PrintedN`. The alternative H convention composes with diag(s_j^-1). | p.421 (3.129) and the paragraph before (3.128), p.422 paragraph after (3.133). The inserted field is at level k, with s_k=1, so this extra factor is 1 there. Compare `ZXR2Wire2.lean:86-87`. No inverse-of-compression is used. |
| Physical J and pairing | The copied `PrintedJ` has eta^-3 relative to the frozen source; `finePair` has eta^3. The final term is **2** times this fine pairing with physical H1 applied to the inserted, lifted unit remainder. | p.392 (3.8), (3.11); p.428 (3.156). Frozen source `ZXR2Wire2.lean:45-53`; frozen final nonlinear term `ZXG3A.lean:55`. No additional eta belongs to the unit remainder. This cancellation alone is NOT a proof: the H1, lift and remainder identifications still need checking. |
| First term | Copied `PrintedFirstTerm`, including level pair, full N inverse and explicit top insertion. | pp.421-422 (3.129),(3.132); p.428 (3.156). Round-two theorem `r1-prove/Attempt.lean:816` already identifies it under its guards, for all B and both linked H/C conventions. Not a new target by itself. |
| C and full inequality | `PrintedUnitC = id - printedLift * printedUnitQ`; `PrintedGenForm = first - mass - nonlinear`; `PrintedInstIneq` quantifies the same Bt support conditions as frozen `InstIneq`. | p.428 (3.156),(3.157) and lower-bound sentence. Frozen `ZXG3A.lean:50-58`, `ZT5A.lean:56-61`. |

The inherited physical dictionary's detailed scale citations are also present beside every copied definition: D, D*, R, padded G', W and Delta from pp.392/394/419; Q and weighted mass from p.393; G/H from p.420; the two linked C/H conventions and G1 from pp.421-422. Nothing inside that previously accepted dictionary has been reweighted here.

## Reading disposition

1. **Raw constraint + raw remainder, preferred.** Directly supported by CMP109 p.267's displayed linearization and the explicit reference to (3.156). The lift inverts the raw derivative; writing it with normalized Q1 instead introduces exactly one ell^-1 outside the normalized corridor inverse. This is a source derivation to be checked against the concrete operators, not a definition by scaling `P.D2in`.
2. **Normalized constraint + normalized remainder, equivalent intended representation.** Supported by dividing the whole constraint in (3.14) by ell at unit spacing. It is separately pinned to prevent a one-sided normalization change. Together with the two p.421 H/C conventions this gives four concrete representation combinations, covered by two goals.
3. **CMP99b-only reading of Dtilde: underdetermined.** The words “quadratic polynomial ... properties similar ... restricted to unit blocks” at p.427 do not uniquely specify a map or its coefficient. There is no additional finite list of scalar powers forced by those words. A CMP99b-only identification remains a **reading question**; inventing an arbitrary quadratic map or an arbitrary scalar family would not supply another faithful closed target. The later source resolves the intended convention only if its application to the CMP99b setting is accepted.
4. **Not defensible extra scale branches:** full rather than normalized trace; site a_j in the unit mass subtraction; eta^3 on unit energy; a fine eta multiplying the unit remainder; dividing only the remainder or only the constraint by ell; unlifted coarse remainder fed directly to H1. The pages or carrier types exclude these as the stated representations. They are possible diagnostic mutations, not additional printed readings.

## Retained departures from the print and limitations

- Dimension three, SU(2), real skew-Hermitian coordinates, finite periodic rectangular tori; the print's greater generality is not claimed.
- Frozen aligned half-open tiling, periodic l1 distances, natural radii, empty tower padding, factor-12 boxes, M a positive ell-power, R >= 18, p.396 Omega0 selection. R is not required to be an ell-power; ell is not restricted to the later odd >11 convention.
- Both-endpoint class regularity, added site/inside-plaquette coverage, touching bond carriers and Lambda selectors, and **inside-plaquette Delta/J** remain unchanged. “Printed” means the printed **units** under those retained S-1/S-2 choices, not proof that the selectors/class are the literal source.
- Genuine frozen componentwise jets and their blocked background are shared primitives. Their complete identification with the analytic averaging maps on the printed class, and control of derivative totalizations, remain inherited issues. No extra global regularity assumption is smuggled in.
- The corridor is a coupled finite system on the retained `CRowIn` dropped variables. Balaban describes local single-variable equations. This pin neither proves decoupling nor changes the dropped set to force it.
- **New source supplement:** CMP109 p.267 is used for the formula omitted at CMP99b p.427. The later paper's notation Dtilde before applying h is not silently identified with CMP99b's unit-field argument of H1. The explicit (2.11) comparison is the reason for the lifted reading.
- Ring inverses, including the new corridor inverse, are totalized for definitions. Original first-term guards are unchanged in positive goals. Physical negative witnesses require both corridor inverses in addition; no singular inverse can produce a negative certificate. Guards are not proved inhabited or implied by smallness.
- The positive form comparison is all-B. The full `PrintedInstIneq` retains the frozen independent-field domain; the source-global support/Ax/Q1 parametrization theorem is not asserted. The negative fields explicitly meet both the frozen independent-variable conditions and the printed subspace conditions on their C-images.
- Inequalities are compared at every real gamma (therefore also positive gamma); the negative no-repair separators use positive gamma. No threshold-uniform coercivity or refutation of Balaban's sufficiently-small-field headline is claimed.
- The constant candidate 1 is uniform in depth. If a future variant uses a k-dependent factor, preservation of a k-uniform headline constant would require a separate bound; it does not follow merely from an instance equivalence.
- The mass/energy normalization conjuncts are included to audit the whole inequality, **not** advertised as independent new open problems. The substantive new comparison is the final J term through H1 and the unit corridor/second jet, and its assembly with the other terms.
- Gaussian integration, covariance (3.157), source thresholds and inverse positivity are not newly formalized by defining `PrintedInstIneq`.

## Source inspection and verification

Read HANDOFF; OPEN_ITEMS B, K-N, R, S; Stage-B and round-two results; round-two S-3 PIN, judgement and positive attempt including the proof of its first-term identity; CMP99b corpus pages 421-428 and the earlier definitions used by the dictionary. Inspected all eight round-two saved renders (392,393,394,419,420,421,422,428).

The additional image `renders/CMP109_p267.png` was rendered with the already-installed PyMuPDF from PDF page 19 of `sources/compute/balaban_su2_papers/balaban_CMP109_1987_RGapproach_I.pdf`, proportionally reduced to a longest side of 1900 pixels. No packages installed. Direct image inspection confirms L*Qtilde*h=I, the inverse coefficient's ell^-1, Dtilde^(2)=Ctilde^(2), H1 h Ctilde^(2) in (2.11), and the explicit reference to (3.156).

Compilation is **only** via:

```sh
AHP/round3/lean1.sh AHP/round3/s3-rest/pin/Statement.lean
```

The shared wrapper writes `Statement.lean.log` and `Statement.lean.exit`. **Final current-source compilation: exit 0; 23/23 permitted dependency records, no warnings or errors.** `VERIFY.md` records the audit and final source/log hashes. A successful compile of `def GoalPosN : Prop` validates its construction and dependencies; **it is not a proof of that proposition**.

No numerical experiment is needed for this pin and none was run. No protected file, other AHP path, lake configuration or source module was edited. No commit or push was made.

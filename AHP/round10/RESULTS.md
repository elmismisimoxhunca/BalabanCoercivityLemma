# Round 10 results: the guarded reading is not yet refuted in Lean

## Decision

**No verified attempt proves the pinned `GoalNeg2` or `GoalNeg1` without extra hypotheses. The guarded reading remains open.** This is neither a refutation nor a proof of that reading.

The targets are `AdalyFormal.Round2.Guarded.Pin.GoalNeg2`, the negation of `P428Target8SG selAll selAll`, and `GoalNeg1`, the negation of `GuardPencilT`. They are equivalent by the pinned bridge. A theorem with type `X → GoalNeg2` does not close either target until `X` is proved. An allowed axiom list does not discharge an explicit hypothesis.

Across all four rounds, the dictionary, nonvanishing and assembly tracks delivered useful compiled results, but none proved an original round-9 cofinal coupling premise. The latest assembly instead gives an exact characterization of that premise by a whole-kernel noncancellation condition. That condition is still unproved.

## Evidence checked for this report

This report inspected the current sources, recorded compiler exits, raw axiom records and audit hashes; **no new Lean compilation was run**.

- All **19 shared Lean publications** under `AHP/round10/shared/` have recorded exit 0. Their logs have no error/warning diagnostics or `sorryAx`; every recorded dependency is among `propext`, `Classical.choice`, `Quot.sound`. These are compact auxiliary results, not unconditional negative goals.
- Current final-round assembly, dictionary and nonvanishing source/log hashes match their audit records. In particular, `shared/assembly/R4_ResponseHull.lean` has 2,612 lines and 191 dependency records; `shared/dictionary/R4_ColorResponse.lean` has 2,185 lines and 194 records; `shared/nonvanishing/R4_PolynomialCertificate.lean` has 306 lines and 29 records.
- `AHP/round9/qualitative-r2/Attempt.lean` and `Attempt.verify.lean` remain byte-identical, both with recorded exit 0. Their 16,596-byte statement-pin prefix is unchanged. The independent `Attempt.VERIFY.md` verdict is **does-not-close-goal**, because the main declarations retain coupling hypotheses.
- `AHP/round10/assembly/r4/Attempt.lean` preserves that entire 628,675-byte round-9 source prefix. The 16,769-line assembly is **not compiled** and has no `.log` or `.exit` record. Earlier large wrapper runs were memory-killed; compact compilations do not certify the historical assembly. Its final conditional goal applications cannot be counted as verified results.

## Decisive declarations and their axiom records

Paths below are repository-relative. Each quoted axiom record comes from the indicated log; multiline records are joined onto one line. All are standard-axiom results, but their conclusions and hypotheses still matter.

### 1. The verified bridge to the pinned goal remains conditional

`AHP/round9/qualitative-r2/Attempt.lean:12102`:

```lean
theorem goalNeg2_of_cofinalAnyPathCoupling
    (h : CofinalAnyPathCoupling) : GoalNeg2
```

Namespace: `AdalyFormal.Round9.Guarded.QualitativeR2Joint`. The missing input is not supplied by round 10. The canonical-profile bridge at line 11729 and free-profile bridge at line 11906 likewise retain their cofinal coupling inputs.

`AHP/round9/qualitative-r2/Attempt.verify.lean.log:1210`:

```text
'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 2. A single vector can be detected exactly by its actual localized curl

`AHP/round10/shared/dictionary/R3_FreeSource.lean:1292` proves `adaptive_energy`; line 1313 proves `exists_profile_iff_curlDetected`. The actual coupling is twice the localized curl pairing. Choosing the vector's response profile gives twice its curl-square energy. Some profile couples nontrivially to that vector exactly when `CurlDetected` holds. This removes the tridiagonal source-column and Fourier-normalization obligations on the free-profile route; it does not prove detection at a crossing.

The same file's `.log:188` and `.log:192`:

```text
'AdalyFormal.Round10.Dictionary.FreeSource.adaptive_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round10.Dictionary.FreeSource.exists_profile_iff_curlDetected' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 3. Physical top-jet detection implies curl detection, not conversely by assumption

`AHP/round10/shared/dictionary/R3_JetDetection.lean:2478`, `curlDetected_of_topJet`, combines the dictionary with the actual dilated blocking/flux proof. It assumes positive scale, radius at least one, the full flat constraint matrix is a unit, and `TopJetDetected` for the input vector. **The crossing-specific top-jet hypothesis remains unproved.**

The same file's `.log:341`:

```text
'AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 4. The actual correction derivative is connected to this coupling

`AHP/round10/shared/assembly/R4_ResponseHull.lean:2169`, `AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form`, identifies the derivative's quadratic form with `profileCoupling`. It explicitly assumes `ProfileRegular`: continuity of the actual lift, convergence of the quadratic jet, and the actual correction derivative. Round-9 theorems establish the underlying regularity facts; their concrete round-10 historical specialization is still in the uncompiled assembly.

The same file's `.log:234`:

```text
'AdalyFormal.Round10.Assembly.R3.corrDeriv_profile_form' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 5. The final whole-kernel reduction is an equivalence, not a noncancellation proof

`AHP/round10/shared/assembly/R4_ResponseHull.lean:2432`, `exists_positive_profile_iff_noCancellation`, characterizes a single positive definite profile on the entire crossing kernel. Line 2576 proves:

```lean
theorem cofinalAnyPathCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation
```

Namespace: `AdalyFormal.Round10.Assembly.R4`. The same file's `.log:270` and `.log:295`:

```text
'AdalyFormal.Round10.Assembly.R4.exists_positive_profile_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round10.Assembly.R4.cofinalAnyPathCoupling_iff_noCancellation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 6. Two compiled obstructions explain why easy shortcuts fail

`AHP/round10/shared/dictionary/R4_ColorResponse.lean:2168`, `exists_charged_invisible`, constructs an actual nonzero charged carrier field with zero full quadratic jet and zero coupling to every profile. **It is not proved to lie in a crossing kernel.** It refutes “nonzero and charged implies detectable,” not the requested coupling premise.

The same file's `.log:342`:

```text
'AdalyFormal.Round10.Dictionary.ColorObstruction.exists_charged_invisible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`AHP/round10/shared/assembly/R2_ProfileQuantifiers.lean:47`, `no_profile_definite`, supplies an abstract U(1)-invariant example where each nonzero vector can be detected by some profile, but no single profile is definite on all vectors. Its `.log:10`:

```text
'AdalyFormal.Round10.Assembly.ProfileQuantifiers.no_profile_definite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 7. Cofinal scalar nonvanishing still requires an actual certificate

`AHP/round10/shared/nonvanishing/R4_PolynomialCertificate.lean:186`, `moving_root_cofinal_nonzero`, proves nested cofinal nonvanishing **from** `MovingRootCertificate coupling`. No such certificate for the frozen coupling was supplied. Line 286, `switchingRoot_not_cofinal`, disproves the shortcut from one nonzero sample and an algebraic crossing equation to cofinal nonvanishing.

The same file's `.log:41` and `.log:77`:

```text
'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.moving_root_cofinal_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round10.Nonvanishing.PolynomialGrid.switchingRoot_not_cofinal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exact remaining Lean statement

The preferred missing theorem has type:

```lean
AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation
```

Here is its existing definition from `shared/assembly/R4_ResponseHull.lean:2550`, with that file's namespace openings and notation:

```lean
def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V
```

The condition is not an unspecified scalar. Its compiled definitions are:

```lean
abbrev ProfileSpace (q R : ℕ) :=
  EuclideanSpace ℝ (Bond (scaleUp 2 1 (dilLu q R)))

def responseGradient (q R : ℕ) (u : TwistSpace q R) : ProfileSpace q R :=
  WithLp.toLp 2 (fun b => 2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
    (Dictionary.FreeSource.responseProfile q R u) b)

def responseHull (K : Submodule ℝ E) (Q : E → F) : Set F :=
  closedConvexHull ℝ (Q '' {u | u ∈ K ∧ ‖u‖ = 1})

def crossingKernel (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R) := (vacA q R V 1 (vacEdge q R V)).ker

def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  (0 : ProfileSpace q R) ∉ responseHull (crossingKernel q R V) (responseGradient q R)
```

`responseHull` uses the surrounding real inner-product-space variables from the source. These excerpts describe an existing proposition, not a new proof of it.

In plain words: above every dyadic-scale bound, choose a scale; **at that chosen scale**, above every radius bound, choose an even radius at least 18 and a valid exterior path. At its vacuum crossing, zero must lie outside the closed convex hull of the responses of **all unit vectors in the full crossing kernel**. This gives one common definite profile, not a different profile for each vector. The profile and positive definiteness constant may depend on the instance.

The canonical-path alternative, `CofinalNoResponseCancellation`, fixes `V = uthPath (2^j) R`; it is also unproved. A sufficient alternative is cofinal `CurlDetected` together with `KernelLine`, which puts the **entire** crossing kernel in one charged complex line. Neither crossing-specific detection nor that whole-kernel containment has been proved for the required cofinal family.

Even after supplying the missing theorem, the historical assembly must be checked: `regularityFacts`, `flatConstraintUnits` and the final conditional applications in `assembly/r4/Attempt.lean` are not compilation evidence. The original round-9 goal bridge is independently compiled; the new concrete join to it is not.

## Why it resisted

1. **The source dictionary is no longer the main obstacle on the free-profile route.** The actual finite-difference source, curl-energy pairing and physical blocking identity now compile. They reduce the problem to genuine crossing nondegeneracy; they do not create it.
2. **A nonzero crossing field does not automatically have a nonzero quadratic jet.** The charged invisible field above rules out an unrestricted version of that inference. Linear unique continuation alone cannot prove this quadratic statement, nor prevent cancellation in a transverse aggregate.
3. **Detecting a selected vector is weaker than controlling the whole kernel.** Adaptive energy picks a profile depending on the vector. A single common profile requires response-hull noncancellation or another whole-kernel argument. Selected-character simplicity is not full-kernel simplicity. Full spatial covariance, transverse character decomposition and spectral exclusion remain unfinished; the claimed canonical scale-to-radius isometry is unavailable because matching both core and collar lengths forces the undilated scale.
4. **Finite samples do not establish nested cofinal quantifiers.** Earlier domination, recurrence and transfer lemmas remain conditional. The polynomial route needs an exact actual-operator representation, crossing/numerator identities and a nonzero certificate, not a fitted exponential or one numerical seed. Its moving-root counterexample makes that distinction explicit.
5. **The numerical evidence is strong but of the wrong logical scope.** For example, the held-out scale 2, radius 28, selected-character calculation gives canonical coupling approximately \(-5.8623291978252373\times10^{-108}\), with over 214 relative digits of agreement between the 230- and 240-digit runs. The adaptive energy and independent source computations agree as well. These are not interval certificates, all-character screens, whole-kernel definiteness proofs or cofinal Lean proofs.

No obstruction to the actual cofinal coupling premise was proved either. The outcome is an unresolved mathematical input plus deferred assembly verification, not merely a compiler failure.

## What the proposed failure point shows about inverses

**There is no unconditional cofinal failure family from round 10.** The following describes the failure point supplied by the established separation/goal reductions **if their missing coupling premise is proved**.

Let \(A\) be the uncorrected all-plaquette carrier and \(D\) the localized correction. The separation conclusion is

\[
\operatorname{IsUnit}(A),\qquad \neg\operatorname{IsUnit}(A-D).
\]

Thus **the carrier \(A\) is a unit at the failure point**; its genuine inverse exists and the pinned carrier guard is satisfied. On the qualitative route the failure can occur before the carrier crossing, while \(A\) is positive definite. The singular *vacuum reference carrier* used to define the crossing kernel is not itself the guarded failure point.

Not all other inverses in the printed construction exist there:

| Operator being inverted | Status at the conditional failure point |
| --- | --- |
| Uncorrected all-plaquette carrier \(A\) | A unit; \(G=A^{-1}\) is a genuine inverse. |
| Uncorrected all-plaquette constraint matrix \(QGQ^*\), used in \(H\) | A unit under the admissible small-curvature bridge hypotheses. This does **not** follow from the carrier guard alone: the proof inside `lean/src/DrRed1.lean:36`, `Delta2_lit_eq_loc`, transfers the property from localized data. |
| Localized carrier, corrected localized carrier, and corrected localized constraint matrix | Genuine inverses are supplied by localized `WellDefAt` in the bridge's small-curvature regime. The uncorrected localized constraint matrix is also a unit (`NG_unit_of_N1`). The localized lift used to form \(D\) is not a singular inverse silently set to zero. |
| Corrected all-plaquette carrier `G1invS selAll selAll`, equal to \(A-D\) | **Not a unit. No genuine inverse exists.** `Ring.inverse` nevertheless defines `G1`, returning zero on this non-unit. |
| Corrected all-plaquette constraint matrix `NmatS`, namely \(QG_1Q^*\) | Zero because \(G_1=0\). On the nontrivial coarse space of the positive-energy test it has no genuine inverse. Its totalised inverse is zero, and \(H_1=0\). |

The auxiliary Dirichlet inverse defining \(G'\) is genuine (`dil_LP_unit`); the gauge Gram inverse used to express the projection is genuine at the flat point (`dil_Gam_unit`) and remains so in the sufficiently small interior-curvature neighborhood used for regularity. Flat localized carrier and constraint units are established by `dil_B0_unit` and `dil_N0_unit`. These are round-9 results in `AHP/round9/qualitative-r2/Attempt.lean`; they do not repair either singular corrected all-plaquette operator. Scalar normalizations are nonsingular here: \(\ell=2\) and \(\eta>0\).

The pencil identity is `AdalyFormal.D1Residual.G1inv_lit_eq_pencil` in `lean/src/DrRed1.lean:52`. The zero-on-nonunit definitions are visible in `lean/src/IngredientG1H1.lean`; the literal collapse is proved by `genFormS_collapse_G1inv` in `lean/src/GdGap.lean:56`:

\[
\operatorname{genFormS}(B)=-a\langle B,B\rangle.
\]

That collapse, tested on a positive-energy field, is how the carrier-only guarded inequality would fail. It attacks the **carrier-guarded, totalised Lean reading**. It is not a counterexample in which every printed inverse exists, and it does not refute a statement additionally guarded by full all-plaquette `WellDefAt`.

## Bottom line

Round 10 supplies a much sharper actual-operator dictionary and an exact whole-kernel criterion. It does **not** supply the missing cofinal noncancellation theorem or a verified unconditional pinned negative goal. The intended failure has an invertible carrier but singular corrected operators handled by totalisation; claiming that all printed inverses exist there would be incorrect.

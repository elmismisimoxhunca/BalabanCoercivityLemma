# Assembly round 4 — exact whole-kernel criterion; GoalNeg2 still open

## Decision

**GoalNeg2 is NOT proved. No original round-9 cofinal coupling premise is proved.**

The new compiled result characterizes the free-profile premise without assuming a simple charged kernel. It is an equivalence with a precise convex noncancellation condition on the **entire actual crossing kernel**. That condition is not established for any cofinal family. This is a useful alternative interface, not closure of the requested theorem.

## 1. Compiled deliverables

| File | Lines | Printed dependency records | Exit |
|---|---:|---:|---:|
| `Cone.lean` | 99 | 6 | 0 |
| `Compact.lean` | 2612 | 191 | 0 |
| `../../shared/assembly/R4_ResponseHull.lean` | 2612 | 191 | 0 |

`Compact.lean` and the byte-identical shared publication were independently compiled with the required `AHP/round3/lean1.sh` wrapper. All final logs have no warnings/errors and use only `propext`, `Classical.choice`, `Quot.sound`. The abstract file imports frozen `D1IVT`; the actual file imports frozen `DrEquiv` via the unchanged R3 energy-glue prefix. There are **26 new R4 declarations**, each individually printed and audited.

New namespace: `AdalyFormal.Round10.Assembly.R4`.

## 2. Plain mathematics: one common profile, not a vector-dependent profile

Let K be a real linear subspace of E and let Q:E->F satisfy Q(a u)=a^2 Q(u). Define

    C = closed convex hull {Q(u) : u in K, ||u||=1}.

Then the following are equivalent:

1. There are a continuous real linear functional f and c>0 such that f(Q(u)) >= c ||u||^2 for every u in K.
2. Zero is not in C.

Proof: (1) places the hull in the closed half-space f>=c, which excludes zero. For (2), the geometric Hahn–Banach separation theorem strictly separates the point zero from the closed convex set C. Apply the resulting positive margin to unit vectors, then use quadratic homogeneity and normalize every nonzero u. The zero vector is handled by Q(0)=0. No compactness, continuity of Q, kernel dimension, or spatial-character hypothesis is silently assumed.

`common_coercive_iff_notMem_responseHull` is this equivalence. `response_ne_zero_of_notMem_responseHull` gives the necessary individual nonzero-response condition. It does not reverse that implication: nonzero responses can still convexly cancel. The R2 U(1)-invariant traceless-pencil counterexample remains applicable to that quantifier mistake.

## 3. Actual frozen-operator application

Write

    r_u(b) = <E3, [iE H0 C2_0(W0 iE u)](b)>,
    Q(u) = 2 * curl_P^* curl_P(r_u),   P=plaqIn Omega0.

The profile space is the physical Euclidean space of **all fine bonds**, not a Bloch cell. In Lean `responseGradient` is exactly `2 * PhaseSource.linearSourceScalar P r_u` placed in this Euclidean space. Its factor and sign follow from dictionary R3's exact finite summation by parts, not from numerical normalization.

`profileCoupling_gradient` proves, for every q,R,f,u without spectral hypotheses,

    profileCoupling(q,R,f,u) = <f, responseGradient(q,R,u)>.

`responseGradient_smul` proves quadratic homogeneity from the actual frozen quadratic C2. The Riesz isomorphism identifies every real continuous linear functional on the physical profile space with an allowed real profile. Negating a profile handles the negative-definite sign. Thus

```lean
theorem exists_canonicalCoupling_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hr : ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, R3.ProfileRegular q R f) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ,
      CanonicalCoupling q R V (corrDeriv q R f)) ↔ NoResponseCancellation q R V
```

The theorem concerns the **original** round-9 `CanonicalCoupling`, `corrDeriv`, `vacA` and `vacEdge`. The known calculus inputs remain explicit as `ProfileRegular`, exactly as in the compiled R3 arbitrary-profile form identity. They are not replaced by assumed derivatives.

There is also an exact detection equivalence:

```lean
responseGradient q R u ≠ 0 ↔ Dictionary.FreeSource.CurlDetected q R u
```

Therefore the new condition implies `CurlDetected` for **every nonzero actual crossing-kernel vector**, not just a selected generator. It is strictly stronger than that vectorwise necessary condition in general.

## 4. Exact missing statements

These definitions are compiled, but their truth is **not proved**:

```lean
def crossingKernel (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R) := (vacA q R V 1 (vacEdge q R V)).ker

def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  (0 : ProfileSpace q R) ∉ responseHull (crossingKernel q R V) (responseGradient q R)

def CofinalNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      NoResponseCancellation (2^j) R (uthPath (2^j) R)

def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V
```

The two compiled cofinal theorems are

```lean
cofinalAnyProfileCoupling_iff_noCancellation (hr : R3.RegularityFacts) :
  CofinalAnyProfileCoupling ↔ CofinalNoResponseCancellation

cofinalAnyPathCoupling_iff_noCancellation (hr : R3.RegularityFacts) :
  CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation
```

They preserve the nested quantifiers, not a diagonal sequence of one radius per scale. They avoid `KernelLine` but do not prove a new nondegeneracy fact. `cofinalNoCancellation_of_curlLine` and its any-path version recover this criterion from the already compiled R3 sufficient line premises.

To finish this route one must prove `CofinalAnyPathNoResponseCancellation` (or its canonical-path version). Alternatively the R3 route still suffices: actual crossing `TopJetDetected`/`CurlDetected`, whole-kernel `KernelLine`, and nested cofinal coverage. None is supplied by this round.

## 5. Cross-track review and combination

The audit reads every current file under `AHP/round10/shared/`, inspects every shared Lean source/log/exit and all tracks' NOTES. It records hashes, complete dependency records, diagnostic checks and timestamps. Earlier shared declarations are not all independently recompiled by this R4 worker; the consumed R3 energy-glue prefix is recompiled twice unchanged. Its provenance hashes and operative copies are rechecked against the previous audit and original sources.

- **Dictionary R1–R3:** exact gauge symmetry, actual source derivative, source/curl energy identity and actual physical blocking/flux connection are credited. Full spatial W/Q/T covariance, character decomposition and spectral exclusion are not inferred from them. The canonical q=1 radius-isometry obstruction is retained.
- **Dictionary R4 current compiled artifacts:** full constant-color covariance, neutral-input zero jet, charged-input neutral jet, single-color zero jet, mixed-color response law, and an actual nonzero charged field invisible to every profile. I inspected the construction and all recorded axioms in `R4_ColorResponse.lean` and the scalar/color harness. The constructed field is NOT a crossing field. This refutes the shortcut nonzero+charged => detectable; it does not refute the actual coupling premise. At review time the track's r4 NOTES was still marked work-in-progress; compiled artifacts, not an assumed final hand-off, are the evidence.
- **Nonvanishing R4:** finite polynomial/Bezout certificate implies nested cofinal scalar nonvanishing even at moving crossing roots. No such certificate is constructed for the frozen coupling. One fixed rho and fixed polynomials are genuine restrictions; varying momenta/multiple roots/inverses are not automatically covered. Its exact A(T)=T(T-1), B(T)=T example disproves propagation from one nonzero root sample alone, not the physical premise.
- **Assembly R4:** the full-kernel response hull is an alternative to the missing single-character/simplicity theorem. Neither the abstract polynomial certificate nor color selection proves this hull excludes zero.

The new dictionary color bodies and nonvanishing polynomial certificate are appended unchanged to the historical assembly after omitting only already-present definitions/imports. No conditional result is relabeled unconditional.

## 6. Historical assembly: deliberately NOT compiled

`Attempt.lean` has **16769 lines** and starts with all **628675 unchanged bytes** of `AHP/round9/qualitative-r2/Attempt.lean`. It also preserves the complete R3 assembly prefix. The known regularity and flat-unit specialization and final conditional GoalNeg2 applications remain **uncompiled**, following the coordinator's explicit memory restriction. No `.log` or `.exit` is fabricated for this file.

`GoalAppendix.lean` records the exact new conditional applications:

```lean
goalNeg2_of_cofinalNoResponseCancellation
  (h : CofinalNoResponseCancellation) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyProfileCoupling
    ((cofinalAnyProfileCoupling_iff_noCancellation R3.regularityFacts).mpr h)

goalNeg2_of_cofinalAnyPathNoResponseCancellation
  (h : CofinalAnyPathNoResponseCancellation) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyPathCoupling
    ((cofinalAnyPathCoupling_iff_noCancellation R3.regularityFacts).mpr h)
```

Even a successful later historical compile would not discharge either displayed h. Compilation of that join is an additional verification obligation, not the mathematical obstruction.

## 7. Independent held-out numerical cross-check — evidence only

Case **q=2,R=28,left-only twist, character (7,7)**, not the author's tested radius. `numerics/crosscheck.py` evaluates the actual R6 transcription at **180,230,240 digits**, with a 2 GiB address-space cap, single-threaded BLAS, and heavy scheduling. The final 240-digit run was freshly executed during this continuation; all three exits are 0.

- Canonical left coupling: **-5.86232919782523726539491734831e-108**.
- Scaled adaptive energy: **13.9863753246574966997745240213**.
- Independently accumulated physical-cell circulation squares and the adjoint-source **full neutral KKT** solve agree with the direct lift energy.
- 230/240 agreement: **214.50 relative digits** for the canonical coupling, **213.69** for the energy. 180/230 agreement: 171.13 and 171.02 respectively.
- At 240 digits: direct-curl discrepancy **1.20e-239**, source-reciprocity discrepancy **8.76e-239**, full lift KKT residual **1.11e-237**, full source residual **2.95e-238**.
- Null residual / |canonical coupling|: **7.39e-134**.
- Restored **cell-normalized** adaptive coupling: **3.01823064587769465215989586439e-214**.
- Peak RSS **1001368 KiB**, below 1 GiB.

Scaling the jet before the neutral solve is explicit and its square is restored in the reported coupling. This is not a certification of the Lean physical aggregate normalization, an interval enclosure, all-character exclusion, whole-kernel definiteness, or cofinality. In particular a positive adaptive energy for one selected vector does not verify the new convex noncancellation condition.

## 8. Reproduction and hygiene

Focused compilation only; **do not compile the historical Attempt on this worker**:

```sh
python3 AHP/round10/assembly/r4/build.py
AHP/round3/lean1.sh AHP/round10/assembly/r4/Cone.lean
AHP/round3/lean1.sh AHP/round10/assembly/r4/Compact.lean
AHP/round3/lean1.sh AHP/round10/shared/assembly/R4_ResponseHull.lean
python3 AHP/round10/assembly/r4/numerics/summarize.py
python3 AHP/round10/assembly/r4/audit.py
```

`AUDIT.json` records all checks and explicit false goal/premise closure flags. `ASSEMBLY.json` records the historical byte-prefix check. A retained initial development-failure log is not counted as successful evidence. No compiler timed out or was relaunched while pending in this continuation.

Only assembly-owned round-10 files and the assembly gap ledger were changed. No protected source, prior round, other track's source, integration checkout, lakefile, build/REPRODUCE, commit, push, worktree, or credential operation was performed. No numerical evidence is used in a Lean proof.

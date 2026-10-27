# Round 10 assembly gap ledger — round 4 (final assembly report)

Owner: assembly. **GoalNeg2 is OPEN. No original round-9 cofinal coupling premise is proved.** Standard-axiom conditional implications are not goal closure. No obstruction disproving the actual coupling premise was found.

## 1. What now compiles, and what it removes

1. **Actual source/energy dictionary (R2–R3):** for every real physical profile f and carrier vector u,
   \[
   F_f(u)=2\langle H_0C^2_0(W_0i_Eu),J'[f]\rangle
          =2\sum_{p\in\operatorname{plaqIn}(\Omega_0)}c_{r_u}(p)c_f(p),
   \qquad r_u(b)=\langle E_3,(i_EH_0C^2_0(W_0i_Eu))(b)\rangle.
   \]
   Thus choosing f=r_u gives twice the localized curl-square energy, and some profile couples iff `CurlDetected q R u`. No source-column recurrence, tail domination or Bloch normalization is needed on this route.
2. **Physical blocking/flux (nonvanishing + dictionary R3):** actual `TopJetDetected` implies `CurlDetected`, with the known full-flat constraint unit explicit. The physical two-layer flux factor is exactly 1/8. This does NOT prove `TopJetDetected` for a crossing vector.
3. **Actual derivative join (assembly R3):** `corrDeriv_profile_form` identifies F_f with the original `corrDeriv` quadratic form, under `ProfileRegular`, three already-proved round-9 regularity facts retained explicitly in the compact file.
4. **Whole-kernel line route (assembly R2–R3):** `KernelLine` plus `CurlDetected` gives a single definite adaptive profile. Neither whole-kernel containment nor crossing detection is proved at cofinal instances.
5. **NEW full-kernel criterion (assembly R4):** `F_f(u)=<f,responseGradient u>` with the actual physical gradient `2*linearSourceScalar P r_u`. Hahn–Banach and Riesz prove that SOME profile is definite on the ENTIRE kernel iff zero is outside the closed convex hull of the gradients of its unit vectors. No `KernelLine`, simplicity, character splitting or prescribed sign is required. **The hull condition itself remains unproved.** It is an exact characterization, not a supplied nondegeneracy theorem.

## 2. Preferred exact remaining Lean target: free path and full-kernel noncancellation

The following names are in `AdalyFormal.Round10.Assembly.R4`. Original round-9 and frozen namespaces are opened as in `shared/assembly/R4_ResponseHull.lean`. These definitions are compiled, not proved propositions.

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

def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V
```

**Exact missing theorem type:** `CofinalAnyPathNoResponseCancellation`.

The canonical-path alternative is also sufficient and still missing:

```lean
def CofinalNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      NoResponseCancellation (2^j) R (uthPath (2^j) R)
```

The compact compiled equivalences are exactly:

```lean
cofinalAnyPathCoupling_iff_noCancellation (hr : R3.RegularityFacts) :
  CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation

cofinalAnyProfileCoupling_iff_noCancellation (hr : R3.RegularityFacts) :
  CofinalAnyProfileCoupling ↔ CofinalNoResponseCancellation
```

The original left sides are the round-9 premises. At a single instance, `exists_canonicalCoupling_iff_noCancellation` retains only `∀ f, R3.ProfileRegular q R f` as the known calculus input. A negative definite profile is replaced by its negative. The positive constant need not be uniform in q,R.

**What this does not allow:** individual nonzero gradients do not imply hull noncancellation. R4 proves `responseGradient q R u ≠ 0 ↔ CurlDetected q R u`, so the condition necessarily detects EVERY nonzero kernel vector; it must additionally rule out their convex cancellation. Choosing a different adaptive profile for each vector does not supply one definite profile. The compiled R2 `R2_ProfileQuantifiers.lean` remains an exact counterexample to that quantifier shortcut.

## 3. Retained sufficient route: actual crossing jet plus whole-kernel line

These are the R3 canonical-path premises, still unproved:

```lean
def CofinalCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R (uthPath (2^j) R) u ∧
      CurlDetected (2^j) R u

def CofinalJetLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ u : TwistSpace (2^j) R, R2.KernelLine (2^j) R (uthPath (2^j) R) u ∧
      ∃ (i : ℕ) (hi : i < blockCount (2^j) R),
        physicalJetAggregate (q := 2^j) (by positivity) hi u ≠ 0
```

`physicalJetAggregate` is `Dictionary.JetDetection.physicalJetAggregate`, definitionally nonvanishing R3's physical neutral top sum. `blockCount q R=4*q*(R+1)`. It includes the genuine normalized C2 and ALL physical even transverse cells. The any-path versions add exactly the path clauses from section 2; they are compiled in `R3_EnergyGlue.lean` / `R3_JetGlue.lean`.

`KernelLine`, in assembly R2, is the whole-kernel condition, NOT selected-character simplicity:

```lean
def KernelLine (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})
```

Still missing: crossing-specific nonzero physical jet/curl; whole-kernel containment or the noncancellation replacement; nested cofinal coverage. A nonzero vector need not have a nonzero quadratic jet, and a nonzero jet need not have a nonzero transverse sum. Gauge symmetry does not prove spectral exclusion.

## 4. Final-round other-track results: useful, but not the missing theorem

**Dictionary R4, compiled current publication `R4_ColorResponse.lean`:** full constant-color covariance of the flat dressed jet and constrained lift, neutral-input zero jet, charged-input neutral jet, single-color vanishing and mixed-color response scaling. `ColorObstruction.exists_charged_invisible` constructs, for every q>0 and R, an actual nonzero charged carrier field with

```lean
vacJet q R u = 0 ∧ (∀ f, profileCoupling q R f u = 0)
```

It does NOT prove that this field is in a crossing kernel. It rules out the proposed inference nonzero+charged => detectable, not the requested actual premise. Current source/log/exit and all axioms were independently inspected by assembly; the track's r4 NOTES was still work-in-progress at review. No claim is made that the full spatial W/Q/T covariance, Fourier decomposition or spectral simplicity is now proved.

**Nonvanishing R4, compiled `R4_PolynomialCertificate.lean`:** `MovingRootCertificate coupling` suffices for nested cofinal scalar nonvanishing. Its exact input includes fixed real polynomials A,B,U,V,P with `U*A+V*B=Polynomial.C P`, a nonzero exact evaluation of P, and actual moving-crossing/cleared-numerator identities on `rho^(2^j), rho^((2^j)*R)`, for one fixed `0<rho<1`. NO certificate identifying these polynomials with a frozen coupling is supplied. Scalar nonvanishing also does not control an unexamined full kernel.

The compiled example `A(T)=T(T-1), B(T)=T` proves one exact nonzero sample at T=1 does not exclude the common root T=0, or force cofinal nonvanishing under a moving root choice. It is not a counterexample to a physical premise. Several independent transfer roots, varying phases and inverse normalization require an actual representation theorem; they are not supplied by a fitted exponential.

Earlier fixed-source/source-family/recurrence alternatives remain documented in their NOTES. Their additional physical dictionary or certificate assumptions are not silently credited as proved. The canonical q=1 radius-isometry claim remains withdrawn: matching both core and collars forces q=1.

## 5. Remaining assembly verification: known regularity and final GoalNeg2 join

`R3.ProfileRegular` consists of actual H continuity, pointwise C2 convergence and `HasDerivAt bulkD corrDeriv 0`; `R3.RegularityFacts` quantifies this over q>0, even R>=18 and all profiles. The exact historical specialization remains:

```lean
theorem regularityFacts : RegularityFacts := by
  intro q R hq hR hR18 f
  exact ⟨bulk_H_cont hq (by omega) (dil_admissible hq hR) f,
    bulk_C2_tendsto hq (dil_admissible hq hR) f,
    hasDerivAt_corrDeriv hq hR (by omega) f⟩

theorem flatConstraintUnits : FlatConstraintUnits := by
  intro q R hq hR hR18
  have h := dil_N0_unit hq (by omega) (dil_admissible hq hR)
  rw [dataFam_dil_zero] at h
  exact h
```

This is **uncompiled assembly text**, not a new mathematical premise claimed established by this worker. The round-9 input theorems are already compiled, but the concrete historical join still requires checking. R4 `GoalAppendix.lean` applies:

```lean
goalNeg2_of_cofinalAnyPathCoupling
  ((cofinalAnyPathCoupling_iff_noCancellation R3.regularityFacts).mpr h)
```

where `h : CofinalAnyPathNoResponseCancellation` is NOT proved. Its canonical-path counterpart is analogous.

`assembly/r4/Attempt.lean`: **16769 lines**, complete unchanged **628675-byte round-9 prefix**, full R3 prefix, new R4 assembly/color/polynomial bodies appended. **ASSEMBLED, NOT COMPILED**, per coordinator memory instruction; no success log/exit exists. Compiling it later would only verify conditional implications until h is actually supplied.

## 6. Assembly R4 compilation/audit evidence

- `assembly/r4/Cone.lean`: 99 lines, 6 records, exit 0.
- `assembly/r4/Compact.lean` and byte-identical `shared/assembly/R4_ResponseHull.lean`: **2612 lines**, **191 records each**, independent clean exits 0.
- **26 new assembly R4 declarations**, all individually printed. Every record is a subset of `propext`, `Classical.choice`, `Quot.sound`; no prohibited proof devices or diagnostics.
- `assembly/r4/AUDIT.json` reads/audits all shared sources/logs/exits and records all track NOTES hashes. Shared publications are inspected, not all recompiled in this round. The consumed R3 actual-energy prefix and copied operative definitions are checked unchanged.
- `assembly/r4/NOTES.md` supplies the mathematics, exact interfaces, reproduction and limitations. No protected edit, historical compile, build/REPRODUCE, commit/push or worktree operation was performed.

## 7. Independent held-out nonvanishing/energy test — NOT a proof

Actual **q=2,R=28,left-only twist,(7,7)**, independent **180/230/240-digit** runs, 2 GiB address-space cap and heavy scheduling. The 240-digit run was freshly executed in the final continuation. The actual R6 transcription and earlier left-only boundary construction are read-only; numerical normalization remains explicitly cell-based.

- Canonical left coupling **-5.86232919782523726539491734831e-108**.
- Scaled adaptive energy **13.9863753246574966997745240213**.
- 230/240 relative agreement **214.50 digits** for coupling, **213.69 digits** for energy (180/230: 171.13 / 171.02).
- Direct circulation-square sum vs lift energy discrepancy **1.20e-239**; independent adjoint-source full KKT pairing discrepancy **8.76e-239** at 240 digits.
- Full lift/source KKT residuals **1.11e-237 / 2.95e-238**; null residual divided by |canonical coupling| **7.39e-134**.
- Restored cell-normalized adaptive coupling **3.01823064587769465215989586439e-214**.
- Peak RSS **1001368 KiB**, all exits 0. `assembly/r4/numerics/SUMMARY.json` records raw-file hashes, comparisons and qualifications.

These checks support the source-energy identity and selected-vector detection at another radius. They are NOT interval certificates, a physical Lean normalization dictionary, all-character spectral exclusion, full-kernel noncancellation, or nested cofinality. In particular they do not discharge section 2.

## Final unresolved work

1. Prove full-kernel response noncancellation at nested cofinal instances for some valid exterior paths; OR prove genuine crossing jet/curl detection plus whole-kernel charged-line containment there.
2. If using the polynomial/transfer alternative, supply the exact actual-operator representation and finite nonzero certificate, not merely a numerical seed.
3. Verify the deferred historical regularity/unit/conditional goal join in a memory-appropriate setting.

**No unconditional pinned negative goal is delivered.**

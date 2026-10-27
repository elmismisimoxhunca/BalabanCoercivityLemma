# Round 9.2, qualitative route: the soft premise is a theorem; one coupling remains

**Status: `GoalNeg2` is NOT closed.** `CofinalTwistSeparation` is not proved either. What
compiled is a conditional reduction, strictly simpler than the earlier ones.

```lean
theorem cofinalTwistSeparation_of_cofinalCanonicalCoupling
    (h : CofinalCanonicalCoupling) : CofinalTwistSeparation            -- Attempt.lean:11716
theorem goalNeg2_of_cofinalCanonicalCoupling
    (h : CofinalCanonicalCoupling) : GoalNeg2                         -- Attempt.lean:11729
theorem goalNeg2_of_cofinalAnyProfileCoupling
    (h : CofinalAnyProfileCoupling) : GoalNeg2                        -- Attempt.lean:11906
theorem goalNeg2_of_cofinalAnyPathCoupling
    (h : CofinalAnyPathCoupling) : GoalNeg2                           -- Attempt.lean:12102 (weakest)
```

**X = `CofinalCanonicalCoupling`** (`Attempt.lean:11711`), unproved. For infinitely many dyadic
scales \(q=2^j\), and for each of them infinitely many even \(R\ge18\), the single-defect
correction has the following property.
- Its actual first-order coefficient
  \(D_e=\frac{d}{d\varepsilon}\big|_{0}\,\mathrm{twistD}(\varepsilon)\) (`corrDeriv`, a `deriv`)
  is definite, of either sign, on the kernel of the vacuum carrier of the round-8 twist.
- The kernel is taken at the canonical crossing angle \(t_*\): the end of the initial positive
  semidefinite interval on \([0,\pi]\) (`vacEdge`).

```lean
def CofinalCanonicalCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    CanonicalCoupling (2^j) R (uthPath (2^j) R) (corrDeriv (2^j) R (dilMask (2^j) R))
-- CanonicalCoupling q R V De := ∃ c > 0,
--   (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c‖u‖² ≤ ⟪u, De u⟫) ∨
--   (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c‖u‖² ≤ -⟪u, De u⟫)
-- corrDeriv q R f := deriv (fun ε => bulkD q R f ε) 0
```

Compared with the first part of this round, X has **no soft-regularity clause**:
- the first part's premise was `CofinalTwistSoftCouplingFwd` = (S) soft regularity ∧ (N) coupling;
- (S) is now a theorem for every profile, scale and radius;
- `cofinalCanonicalCoupling_iff` (`:11774`) proves X ↔ `CofinalTwistSoftCouplingFwd`.

What remains is one nondegeneracy per instance: a single number, round 8's \(c_1(q,R)\neq0\),
once the kernel is known to be one charged complex line (`CofinalExplicitU1`). It is **not** a
finite list of explicit inequalities, and no qualitative argument found here produces it
(section 4).

---

## 1. What is new in this part

1. **Soft regularity for every profile** (`interiorSoft_corrDeriv`, `:11653`). The analytic
   route (`AHP/round9/analytic-r1`, `analytic-r2`) built a theory of smooth curvature families
   based at the trivial background. It covers:
   - continuity of \(W\), \(T\), \(Q\), the carriers and the constrained inverse \(H\);
   - convergence of the second jet \(C^2\);
   - existence of the source derivative \(J'\);
   - convergence of \(\Delta^{(2)}(\varepsilon)/\varepsilon\).

   They used it for the single-defect family, with a one-sided limit. Here the theory is
   instantiated at the interior family \(\varepsilon\mapsto\) `maskedU (ε f) 1` of an **arbitrary**
   profile \(f\), with the **two-sided** limit. This gives this round's `InteriorSoft q R f`
   with derivative `corrDeriv q R f`, for every \(f\), every \(q>0\) and every even \(R\ge16\).
   The two-sided derivative is what the gauge flip needs (section 3.7).
2. **The canonical crossing at every instance** (`twist_vacuum_crossing_all`, `:11677`). The
   first part used the frozen localized theorem, whose thresholds are existential. The
   analytic route's `dil_flat_unit` (`:10768`, a direct kernel argument) makes the flat
   localized carrier a unit at every \(q>0\), \(R\ge1\). So the crossing, and the per-instance
   separation below, hold at **every** instance, with no thresholds.
3. **Per-instance separation** (`twistSeparation_eventually_of_coupling`, `:11699`). For every
   \(q>0\) and every even \(R\ge18\): if the coupling is definite at \((q,R)\), the literal
   round-8 family separates at every small positive curvature.
4. **Free profile, no bound** (`CofinalAnyProfileCoupling`, `:11869`).
   - Scaling: `corrDeriv q R (c·f) = c • corrDeriv q R f` (`:11813`).
   - So any profile with a definite coupling can be rescaled into the class bound
     \(|f|\le1\) (`pathSoftCoupling_of_profile`, `:11887`).
   - This premise therefore asks only for **some** real interior profile with a definite
     coupling.
   - **Any exterior path** (`CofinalAnyPathCoupling`, `:12077`): the weakest premise also
     frees the exterior path. It may be any continuous, real-analytic path from the trivial
     field whose vacuum carrier has a negative direction at \(\pi\). The canonical crossing of
     that path is used, and the round-8 twist is one such path
     (`cofinalAnyPathCoupling_of_anyProfile`, `:12109`). It feeds round 9.1's
     `goalNeg2_of_cofinalVacuumCoupling`.
5. **Explicit coupling** (`corrDeriv_dilMask_form`, `:11967`). The quadratic form of the actual
   first-order coefficient is the analytic route's explicit vacuum coupling
   \[\langle u,D_eu\rangle=2\langle H_0\,C^{2}_0(W_0u),\,J'\rangle,\]
   with all of \(H_0,C^2_0,W_0\) at the flat background and \(J'\) the curvature derivative of
   the localized source. This gives two explicit forms of X: `CofinalExplicitCoupling` and the
   complex-line form `CofinalExplicitU1`.
6. **What the positive reading forces.**
   - `goalPos1_forces_degenerate_coupling` (`:11737`): at every large scale and every large
     even radius, the single-defect coupling is not definite on the canonical kernel.
   - `goalPos1_forces_degenerate_profiles` (`:11923`): this holds for **every** interior profile.
   - If the kernel is one complex line (as computed), the positive reading therefore needs
     \(\langle u_0,D_e[f]u_0\rangle=0\) for every profile \(f\): the whole coupling functional
     vanishes.

## 2. The compiled theorems of this part (namespace `AdalyFormal.Round9.Guarded.QualitativeR2Joint`)

| line | declaration | content |
|---:|---|---|
| 11439–11466 | `bulkV`, `bulkU_link_contDiff`, `bulkV_smooth`, `bulkV_contFam`, `bulkU_zero` | the interior family of any profile has \(C^\infty\) links and is flat at \(\varepsilon=0\) |
| 11472–11483 | `bulk_dataFam_zero(_eq)`, `bulkD_eq_dataFam`, `bulkA_eq_dataFam` | the family is the analytic route's `dataFam`; its flat point is the flat data |
| 11487–11583 | `bulk_LP0`, `bulk_Gam0`, `bulk_reg0`, `bulk_W_cont`, `bulk_T_cont`, `bulk_Q_cont`, `bulk_carrier_cont`, `bulk_H_cont`, `bulk_C2_tendsto` | continuity at the flat interior (generic lemmas `continuousAt_Wop` `:9063`, `continuousAt_Ginv_dataS` `:9558`, `continuousAt_H` `:9580`, units `dil_flat_unit` `:10768`, `dil_N0_unit` `:10837`) |
| 11585, 11600 | `bulk_J_tendsto`, `bulk_exists_D1` | two-sided source derivative and two-sided limit of \(\Delta^{(2)}(\varepsilon)/\varepsilon\) (`exists_source_derivative` `:9813`, `tendsto_Delta2_div` `:9624`) |
| 11616–11662 | `bulkD_zero`, `bulk_hasDerivAt`, `corrDeriv`, `hasDerivAt_corrDeriv`, **`interiorSoft_corrDeriv`**, `interiorSoft_exists` | **(S) is a theorem**, every profile, every \(q>0\), even \(R\ge16\) |
| 11671, 11677 | `flat_loc_unit`, **`twist_vacuum_crossing_all`** | canonical crossing, forwards and backwards, at every instance |
| 11699 | **`twistSeparation_eventually_of_coupling`** | per instance: coupling ⇒ separation at all small \(\varepsilon>0\) |
| 11711–11737 | **`CofinalCanonicalCoupling`**, **`cofinalTwistSeparation_of_…`**, **`goalNeg2_of_…`**, `not_…_of_goalPos1`, `goalPos1_forces_degenerate_coupling` | main reduction and its converse |
| 11758, 11774 | `twistSoftCouplingFwd_iff`, `cofinalCanonicalCoupling_iff` | X is the first part's premise minus (S) |
| 11790–11923 | `bulkU_smul`, `bulkD_smul`, `corrDeriv_smul`, `canonicalCoupling_smul`, **`CofinalAnyProfileCoupling`**, `exists_profile_scale`, `pathSoftCoupling_of_profile`, **`goalNeg2_of_cofinalAnyProfileCoupling`**, `not_…_of_goalPos1`, `cofinalAnyProfileCoupling_of_canonical`, `goalPos1_forces_degenerate_profiles` | weakest premise: some real profile |
| 11943–12061 | `bulkU_dilMask`, `bulkD_dilMask`, `corrDeriv_dilMask_form`, `ExplicitCoupling`, `CofinalExplicitCoupling`, `ExplicitU1`, `CofinalExplicitU1`, bridges | explicit forms of X |
| 12077–12109 | **`CofinalAnyPathCoupling`**, `cofinalVacuumCoupling_of_anyPath`, **`goalNeg2_of_cofinalAnyPathCoupling`**, `not_…_of_goalPos1`, `cofinalAnyPathCoupling_of_anyProfile` | weakest premise: some analytic exterior path and some profile |

Implications (all compiled; the left column are open premises):

```
CofinalExplicitU1 ─┐
CofinalExplicitCoupling ─→ CofinalCanonicalCoupling ⇔ CofinalTwistSoftCouplingFwd (part 1)
                                │                         └─→ CofinalTwistSeparation (round 8) ─→ GoalNeg2
                                └─→ CofinalAnyProfileCoupling ─→ CofinalAnyPathCoupling ─→ CofinalVacuumCoupling (9.1) ─→ GoalNeg2
                                                                 (also ─→ CofinalPathSoftCoupling (part 1) ─→ GoalNeg2)
GoalPos1 ─→ ¬ each of these; and eventually, for every profile, a non-definite coupling
```

## 3. The argument in plain mathematics

Notation as in round 8:
- mass \(a=1\), \(\ell=2\), \(k=1\), \(q=2^j\), the dilated tower;
- \(A(\varepsilon,t)\): actual all-plaquette carrier, single defect of strength \(\varepsilon\),
  exterior twist \(U_t\);
- \(D(\varepsilon)\): localized correction, independent of \(t\), with \(D(0)=0\);
- \(\mathrm{vac}(t)=A(0,t)\).

**3.1 Isolated non-units** (part 1, `isUnit_punctured` `:4917`). Coefficients of \(A(\varepsilon,\cdot)\) and \(A(\varepsilon,\cdot)-D(\varepsilon)\)
are real-analytic in the angle (`pathA_anR` `:5601`: the frozen continuity chain of the plaquette
Hessian redone with `AnalyticAt`). The Gram determinant is analytic, so by the identity
theorem non-units are isolated once there is a unit somewhere.

**3.2 Positive definite at angle 0, negative at \(\pi\).**
- At the flat configuration, \(\mathrm{Ginv}_{\rm all}\ge\mathrm{Ginv}_{\rm loc}\) (curl-square
  monotonicity, part 1).
- \(\mathrm{Ginv}_{\rm loc}\) is positive definite at every \(q,R\) (`dil_flat_pos`/`dil_flat_unit`,
  analytic route). If its form vanishes at \(x\), then \(x\) is curl-free on \(\Omega_0\),
  vanishes on the bonds not touching \(\Omega_1\), and has zero level-1 averages. Integrating
  along longitudinal lines writes \(x=D\xi\). The level-1 averages then force
  \(\xi\in N(Q')\), and \(T(D\xi)=0\) forces \(D\xi=0\).
- Round 5 gives a negative direction at \(t=\pi\).

**3.3 The canonical crossing** (`vacEdge` `:5852`, `psdEdge_spec` `:5007`). Let \(t_*\) be the supremum of
the initial PSD interval in \([0,\pi]\). Then:
- \(\mathrm{vac}(t_*)\) is PSD and singular;
- by 3.1, it is positive definite at angles arbitrarily close before \(t_*\);
- it has a negative direction at angles arbitrarily close after \(t_*\).

The same holds for the backward twist (`twist_vacuum_crossing_all`).

**3.4 Soft regularity for every profile** (new). Fix a profile \(f\) and the family
\(U_\varepsilon=\) `maskedU (ε f) 1`. Its links \(\mathrm{Ug}(\varepsilon f_e)\) are \(C^\infty\) in
\(\varepsilon\), and \(U_0\) is flat.

At the flat point:
- the Dirichlet operator \(L_P\) and the constraint Gram \(\Gamma\) are units;
- the localized carrier \(B_0\) is a unit (3.2);
- \(QG_0Q^*\) is a unit (`dil_N0_unit`).

The analytic route's generic lemmas then give:
- continuity at \(\varepsilon=0\) of \(W\), \(T\), \(Q\), every assembled carrier, and
  \(H=GQ^*(QGQ^*)^{-1}\);
- convergence of \(C^2(\varepsilon)\);
- a two-sided derivative \(J'\) of the localized source (which vanishes at the flat point);
- \(\Delta^{(2)}(\varepsilon)/\varepsilon\to D_1\) as \(\varepsilon\to0\), \(\varepsilon\neq0\).

Since \(D(0)=0\), this is `HasDerivAt D D₁ 0`. With continuity of the carrier and of \(W\), it is
exactly this round's (S), with \(D_e=\) `deriv D 0` (`corrDeriv`).

**3.5 Joint continuity** (part 1, `pathA_jointly_continuousAt`). The frozen exterior path formula
\(A(\varepsilon,t)=A(\varepsilon,0)+p_EW_\varepsilon^*(\Delta(U_{\varepsilon,t})-\Delta(U_{\varepsilon,0}))W_\varepsilon i_E\)
turns the continuity of (S) into joint continuity in \((\varepsilon,t)\).

**3.6 Pre-crossing separation** (round 9.1 `first_order_separation` `:3729`). Assume crossing data
as in 3.3, joint continuity, \(D(\varepsilon)=\varepsilon D_e+o(\varepsilon)\), and
\(D_e\ge c>0\) on \(\ker\mathrm{vac}(t_*)\). Then for every small \(\varepsilon>0\) there is an
angle before \(t_*\) where \(A\) is positive definite and \(A-D\) is singular.

**3.7 The gauge flip** (part 1, `De_flip` `:6594`).
- The constant gauge \(w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\) maps the family at
  \((\varepsilon,t)\) to the family at \((-\varepsilon,-t)\).
- The all-plaquette carrier is gauge covariant (`Ginv_all_gauge` `:6381`), and the correction
  form is gauge invariant (frozen).
- Differentiating the invariance at \(\varepsilon=0\) (two-sided derivative) gives
  \(\langle \mathrm{Ad}_wu,D_e\mathrm{Ad}_wu\rangle=-\langle u,D_eu\rangle\).
- A negative coupling on the forward kernel is therefore a positive coupling on the backward
  kernel. A backward separation at \(s\) is a literal `TwistSeparation` at the angle \(-s\).

So a definite coupling of **either** sign gives separation at all small \(\varepsilon>0\).

**3.8 Diagonal \(U(1)\)** (part 1, `De_rot_comm` `:6899`, `canonicalCoupling_of_U1` `:6945`). All links
are diagonal, so \(\mathrm{vac}\) and \(D_e\) commute with the rotations
\(J_\alpha=\mathrm{Ad}_{\mathrm{diag}(e^{i\alpha},e^{-i\alpha})}\). On a charged complex line
\(\mathrm{span}\{u_0,Ju_0\}\), \(D_e\) acts as the scalar
\(c_1=\langle u_0,D_eu_0\rangle/\|u_0\|^2\). So definiteness is \(c_1\neq0\).

**3.9 Free profile and explicit form** (new).
- **Scaling.** `maskedU (ε·(c f)) = maskedU ((cε) f)`, hence \(D_e[cf]=c\,D_e[f]\). Every
  profile has a positive multiple with \(|f|\le1\).
- **Explicit form.** For the single-defect profile, the family is round 4's `dilU ε 1`.
  The analytic route's `dil_D1_form` (`:10977`) identifies the quadratic form of any limit of
  \(\Delta^{(2)}(\varepsilon)/\varepsilon\) with \(2\langle H_0C^2_0(W_0u),J'\rangle\). Here this
  is applied to the right-hand slope of `corrDeriv`.

## 4. What is left, and why this route does not close it

**X is one statement per instance:** a definite coupling on one specific kernel. Each of the
following implies X at \((q,R)\):
- **Complex-line form** (`ExplicitU1`): the canonical kernel is the complex line of one charged
  \(u_0\), and the single real number \(2\langle H_0C^2_0(W_0u_0),J'\rangle\neq0\);
- **Free-profile form:** the same for **some** profile.

**Numerics** (round 8, floating point; collected in `numerics/premise_evidence.md`):
- \(q=2\), \(R=18,20,24,30\): \(c_1=-1.81\times10^{-70}\), \(-5.01\times10^{-78}\),
  \(-3.83\times10^{-93}\), \(-8.11\times10^{-116}\);
- \(q=4\), \(R=18\): \(c_1=-4.72\times10^{-127}\);
- \(c_1(2,R)=K\rho_k^{8R}\) with \(K=-0.0191639341944987\);
- the screened instances show exactly one non-positive sector at \(t_*\) (charged).

So X is numerically true at every computed instance. It is unproved for infinitely many.

**Why no qualitative argument found here produces it** (details: round 9.1 NOTES section 6).
1. The coupling is \(O(\rho^{2RM})\) for every exterior path and every profile.
   - The correction sees fields only through the level-1 blocking jet \(C^2\), inside
     \(\Omega_1\).
   - Admissibility keeps \(\Omega_1\) at distance \(>RM\) from \(\partial\Omega_0\), where every
     vacuum crossing mode is generated.
   - No parameter of the pinned statement (exterior field, profile, tower, mass) removes this
     collar, because the cofinal quantifiers force \(R,M\to\infty\).
2. There is no structural zero and no structural sign.
   - The sign differs between \(q=1\) (positive) and \(q=2,4\) (negative).
   - The finite sum for \(c_1\) has terms of both signs.
   - The flip (3.7) shows that the sign is irrelevant; only nonvanishing matters.
3. Analyticity only propagates a nonzero coefficient.
   - In the angle, it turned the crossing into a theorem (3.3).
   - In the curvature, it turns \(c_1\neq0\) into separation for all small \(\varepsilon\).
   - It cannot produce \(c_1\neq0\): every evaluation point is as exponentially small as
     \(c_1\), and the special points \(\varepsilon=0\), \(\varepsilon=\pi\) are useless or
     outside the class.
4. A **generic-parameter idea**, considered and not pursued:
   - The refuter picks the mass \(a\) once, before all instances. If \(a\mapsto c_1(q,R;a)\)
     were analytic and not identically zero for each \((q,R)\), then a single \(a\) off a
     countable set would work at every instance.
   - "Not identically zero in \(a\)" is again an exponentially small nonvanishing.
   - Nothing guarantees that the crossing persists as \(a\) varies, since the mass term adds
     positivity.
   - The bridge would also have to be redone for general \(a\).
5. The free-profile form makes X **linear**: "the field \(H_0C^2_0(W_0u_0)\) is not orthogonal
   to all linearized interior sources". Proving it is a unique-continuation statement for the
   frozen localized operators (\(W\), \(Q\), \(G\), \(H\)). There is no operator or Fourier
   dictionary for these in `lean/src`.

**What would close X:**
- (a) uniform asymptotics, i.e. a half-space constant \(K(k)\neq0\) with finite-size error
  bounds and identification of the canonical crossing with the predicted mode (the analytic
  route);
- (b) a unique-continuation nonvanishing theorem for the frozen localized operators;
- (c) a resultant/transfer-matrix argument: an invertible linear recurrence in \(R\) turns one
  certified nonzero value into infinitely many (round 9.1 §6.7).

Each of these needs an operator dictionary for the frozen assembly that does not exist yet.

## 5. Files, compilation, axioms

`Attempt.lean` (12189 lines) is the concatenation of:

| lines | part | source |
|---:|---|---|
| 1–2928 | round-8 `Attempt.lean`, verbatim; it begins with the round-3 pin and the round-5 `ivt-r2` attempt | `AHP/round8/guarded-idea/Attempt.lean` |
| 2929–4749 | round-9.1 qualitative appendix, verbatim | `AHP/round9/qualitative-r1/Appendix.lean` |
| 4750–7015 | round-9.2 part 1 (`QualitativeR2`), verbatim | `Appendix.lean`; lines 1–7015 = `history/Attempt.r2a.lean`, compiled earlier this round |
| 7016–8731 | analytic route, pass 1 (`AnalyticR1`), verbatim | `snap/AnalyticR1_Appendix.lean` = `AHP/round9/analytic-r1/Appendix.lean` |
| 8732–11381 | analytic route, pass 2 (`AnalyticR2`), verbatim snapshot taken 2026-10-23 02:29 UTC | `snap/AnalyticR2_Appendix.lean` (sha256 in `snap/SHA256SUMS`; it was compiled by that route, its log in `snap/`) |
| 11382–12189 | round-9.2 part 2 (`QualitativeR2Joint`), with one `#print axioms` line per declaration | `Appendix2.lean` = `scratch/P6_joint.lean` + records |

- Sole import: frozen `DrEquiv`.
- No `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque` or
  `axiom` command anywhere in the source, comments included.
- The analytic route's code is used **unchanged**. Credit for `dil_flat_unit`, the smooth-family
  theory and `dil_D1_form` belongs to that route. This part instantiates it at arbitrary
  profiles, with the two-sided limit, and joins it to this route's crossing/flip/\(U(1)\) theorems.
- Its top-level `set_option maxHeartbeats 1000000` is reset to the pin's value at the start of
  part 2.

**Result of the wrapper** `AHP/round3/lean1.sh Attempt.lean`: `Attempt.lean.log`,
`Attempt.lean.exit`, `CHECKS.json`; summary in section 7.

`audit.py` checks:
- **Prefixes and structure:**
  - the pin, the round-5 attempt and round 8 are byte prefixes;
  - `history/Attempt.r2a.lean` = round 8 + round 9.1 appendix + `Appendix.lean`, and is a byte
    prefix;
  - the snapshots match their recorded sha256, and the analytic-r1 snapshot equals the live
    file;
  - the file equals `history/Attempt.r2a.lean` + snapshots + `Appendix2.lean`.
- **Source:** sole import `DrEquiv`; no forbidden tokens.
- **Compile:**
  - exit 0, with source ≤ log ≤ exit timestamps;
  - no error or warning lines, and no `sorryAx`.
- **Axioms:**
  - every dependency record is a subset of {`propext`, `Classical.choice`, `Quot.sound`};
  - each declaration of `Appendix.lean` and `Appendix2.lean` has its own record, with exactly
    these three.

**Compile history of this part** (wrapper only; no `lake build`, no `REPRODUCE.sh`; each job
launched detached and polled):
1. `scratch/Draft5.lean`: exit 1. The errors were:
   - a missing Frobenius norm instance on \(M_2\);
   - three normed-vs-topological-vector-space instance mismatches between the generalized
     `HasDerivAt`/`deriv` and the normed-section lemmas (`hasDerivAt_iff_tendsto_slope_zero`,
     `HasDerivAt.deriv`, `HasDerivAt.scomp`, `tendsto_slope_zero_right`). They were fixed by
     passing the function explicitly.

   A first detached launch died with its shell (empty log, no exit file). It was relaunched
   with `setsid`.
2. `scratch/Draft6.lean`: exit 1.
   - `ContDiffAt.comp` unified against the expected type the wrong way.
   - Two remaining `HasDerivAt.deriv` mismatches.
3. `scratch/Draft7.lean`: **exit 0**, no errors, no warnings, no `sorryAx`.
4. `Attempt.lean` = Draft7 + `twistSoftCouplingFwd_iff`, `cofinalCanonicalCoupling_iff`: exit 0,
   no errors, no warnings, audit pass (log kept as `history/Attempt.r2b0.lean.log`).
5. **Final** `Attempt.lean` = (4) + section G (`CofinalAnyPathCoupling`).

Logs of 1–3 are in `history/`. The first part of this round (`history/Attempt.r2a.lean`, its
log, exit, `NOTES.r2a.md` and `CHECKS.r2a.json`) is kept unchanged. The earlier compile history
of part 1 is in `history/NOTES.r2a.md` §6.

## 6. Hygiene

- Only files under `AHP/round9/qualitative-r2/` were written.
- The analytic route's directories and every earlier round were read, never written. No bytecode
  was written there.
- `lean/`, the lakefile, `paper/`, `notes/`, `expected/`, `extras/` and the integration checkout
  were not touched.
- No `lake build`, no `REPRODUCE.sh`, no commit or push.
- Scratch drafts are deleted after the final audit (inside this directory only).

## 7. Final compile and audit

- `AHP/round3/lean1.sh AHP/round9/qualitative-r2/Attempt.lean` (03:20 to 03:27 UTC): **exit 0**,
  no error lines, **no warning lines**, no `sorryAx`.
- `python3 audit.py` gives `CHECKS.json` with `pass: true`:
  - 774 dependency records, all ⊆ {`propext`, `Classical.choice`, `Quot.sound`};
  - 244 own declarations (177 from part 1, 67 from part 2), each with its own record and
    exactly these three axioms;
  - every prefix and structure check is true;
  - `Attempt.lean` sha256 `b6dc8553ad1b8a7fdc5ff731b5c7df0fde0009979bdc90dbaba23b10efc5d052`.
- Main axiom lines (log):
  - `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalCanonicalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - `'AdalyFormal.Round9.Guarded.QualitativeR2Joint.goalNeg2_of_cofinalAnyPathCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]`
- The analytic-r2 snapshot no longer equals that route's live `Appendix.lean`. That route kept
  working after the snapshot. This is informational: the snapshot is the code compiled here.

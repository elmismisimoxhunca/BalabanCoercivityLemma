# Round 9.2, qualitative route: the vacuum crossing is a theorem, the two twist directions are gauge equivalent, and one coupling remains

**Status: `GoalNeg2` is NOT closed.** `CofinalTwistSeparation` is not proved either.

What compiled (standard axioms only, `Attempt.lean`):
- unconditional theorems about the actual operators that remove whole clauses from the earlier premises;
- a reduction of round 8's literal target to a strictly simpler premise:

```lean
theorem cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd
    (h : CofinalTwistSoftCouplingFwd) : CofinalTwistSeparation          -- Attempt.lean:6665
theorem goalNeg2_of_cofinalTwistSoftCouplingFwd
    (h : CofinalTwistSoftCouplingFwd) : GoalNeg2                         -- Attempt.lean:6669
```

**X = `CofinalTwistSoftCouplingFwd`**, unproved. For infinitely many dyadic scales
\(q=2^j\), and for each of them infinitely many even \(R\ge18\), two things hold at
\((q,R)\):
- **(S) soft regularity** `InteriorSoft q R (dilMask q R) De`. This concerns the interior
  family \(\varepsilon\mapsto\) `maskedU (ε·dilMask) 1` only: the single-defect curvature and
  the trivial exterior field. It asks that, at \(\varepsilon=0\):
  - the all-plaquette carrier is continuous;
  - the dressing \(W\) is continuous;
  - the localized correction is differentiable, with derivative \(D_e\).
- **(N) nondegeneracy** `CanonicalCoupling q R (uthPath q R) De`. \(D_e\) is definite, of
  **either** sign, on the kernel of the vacuum carrier of the round-8 twist at its
  **canonical crossing** `vacEdge` (the end of the initial positive semidefinite interval on
  \([0,\pi]\)).

No vacuum-crossing hypothesis, no joint continuity in (curvature, angle), no angle
derivative, no gap constant, no scalar action and no sign case distinction appear. Those
are now theorems or are no longer needed.

---

## 1. What is new, in one paragraph

Round 9.1's premise `CofinalVacuumCoupling` had three clauses:
1. a vacuum crossing (positive definite just before, a negative direction just after);
2. regularity (joint continuity, plus a curvature derivative of the correction);
3. a definite coupling on the vacuum kernel.

This round:
- **proves (1)** for the actual twist at every large scale and radius. The ingredients are
  the frozen localized theorem, a monotonicity at the flat background, round 5's negative
  endpoint, and analyticity in the angle with the identity theorem.
- **reduces (2)** to continuity and differentiability of the interior family at the flat
  interior.
- **reaches the literal round-8 family without post-crossing analysis**, through a global
  gauge flip. The flip shows that the twist at \((\varepsilon,t)\) is unitarily equivalent to
  the twist at \((-\varepsilon,-t)\). A negative coupling at positive angle (the measured case,
  \(c_1<0\)) is therefore a positive coupling at negative angle, where the pre-crossing
  argument applies. `TwistSeparation` allows any real angle.
- **proves the \(U(1)\) commutation** that round 9.1 assumed. On a charged complex line, (N) is
  exactly round 8's \(c_1(q,R)\neq0\).

## 2. The compiled theorems

`Attempt.lean` (7015 lines) consists of:
- `AHP/round8/guarded-idea/Attempt.lean`, verbatim (lines 1-2928);
- the round-9.1 appendix, verbatim (2929-4749, namespace `…Round9.Guarded.Qualitative`);
- this round's `Appendix.lean` (4750-7015, namespace `AdalyFormal.Round9.Guarded.QualitativeR2`).

Sole import: frozen `DrEquiv`. All 177 new declarations print exactly
`[propext, Classical.choice, Quot.sound]`.

| line | declaration | content |
|---:|---|---|
| 4898, 4904, 4917 | `isUnit_iff_gramDet`, `analyticAt_gramDet`, `isUnit_punctured` | a symmetric operator is a unit iff its Gram determinant is \(\neq0\); analytic matrix coefficients give an analytic determinant; **isolated non-units** once a unit somewhere (identity theorem) |
| 4999, 5007 | `psdEdge`, `psdEdge_spec` | the end of the initial PSD interval is a genuine crossing: PSD and singular there, PD arbitrarily close before, a negative direction arbitrarily close after |
| 5161-5314 | `AnFam`, `an_*`, `an_inner_delta`, `anM_uMat`, `anFam_Uth` | frozen `D1Cont` chain with `Continuous` replaced by entrywise real-analyticity: every matrix coefficient of the plaquette Hessian is analytic along an analytic link family; the frozen twist is analytic |
| 5331-5480 | `ContFamY`, `contY_*`, `contY_deltaKLocCLM` | the same chain over an arbitrary parameter space (used for \((\varepsilon,t)\)) |
| 5601, 5633, 5642 | `pathA_anR`, `pathA_isolated`, `pathC_isolated` | carrier coefficients analytic in the angle (frozen exterior path formula); isolated non-units of carrier and corrected carrier at **every** curvature |
| 5675-5739 | `flat_delta_le_univ`, `Ginv_loc_psd_flat`, `Ginv_loc_le_all_flat`, `Ginv_all_pd_flat` | at the trivial background: localized carrier PSD, all-plaquette carrier \(\ge\) localized; a localized unit makes the all-plaquette carrier PD |
| 5759 | `flat_loc_unit_eventually` | **frozen localized theorem** (`M2RightInv.p428Target8`): for all large \(j\), then all large even \(R\), the localized carrier of the trivial configuration is a unit |
| 5810-5836 | `vacA_pd_zero`, `vacA_uth_pi_negative`, `vacA_uthNeg_pi_negative` | vacuum twist PD at angle 0, negative direction at \(\pm\pi\) |
| 5852-5867 | `vacEdge`, `VacuumCrossesAt`, `vacuum_crossing` | the canonical crossing and its properties |
| 5886 | **`twist_vacuum_crossing`** | **unconditional**: for all large \(j\), then all large even \(R\), the vacuum twist crosses at `vacEdge`, forwards and backwards |
| 5905 | **`twist_isolated_nonunits`** | **unconditional**: at every curvature the singular angles of the curved twist, and of its corrected carrier, are isolated |
| 5955 | `pathA_jointly_continuousAt` | joint continuity in (curvature, angle) from continuity in the curvature, at the untwisted angle, of the carrier and of \(W\) |
| 5999-6020 | `bulkU`, `bulkA`, `bulkD`, `InteriorSoft` | the interior family and premise (S) |
| 6086, 6095 | `CanonicalCoupling`, `CanonicalCouplingPos` | premise (N); positive version |
| 6102, 6119 | `vacuumCoupling_of_soft`, `pathSeparation_eventually_of_soft` | (S) + (N) give round 9.1's `VacuumCoupling`; pre-crossing separation at every small curvature |
| 6157 | `twistSeparation_of_uthNeg` | a separation of the backward twist at \(s\) is a literal `TwistSeparation` at angle \(-s\) |
| 6170-6216 | `TwistSoftCoupling`, `twistSeparation_eventually`, `cofinalTwistSeparation_of_cofinalTwistSoftCoupling` | literal target, positive coupling on the forward OR the backward kernel |
| 6224-6274 | `PathSoftCoupling`, `goalNeg2_of_cofinalPathSoftCoupling` | weakest premise for `GoalNeg2`: free bounded profile, either sign, either side |
| 6381 | **`Ginv_all_gauge`** | the all-plaquette carrier is gauge covariant (frozen `GaugeCov` lane, extended to `selAll`) |
| 6436-6498 | `flipElt`, `flipGauge`, `flip_pathU`, `flip_bulkU` | the constant gauge \(w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\) maps the family at \((\varepsilon,t)\) to \((-\varepsilon,-t)\) |
| 6509-6549 | `pathA_flip`, `vacA_flip`, `vacEdge_flip`, `bulkD_flip` | backward vacuum twist \(\cong\) forward one; same canonical crossing; correction at \(\varepsilon\) \(\cong\) correction at \(-\varepsilon\) |
| 6594, 6620 | **`De_flip`**, `couplingPos_back` | the coupling is **odd** under the flip; a negative forward coupling is a positive backward coupling |
| 6642-6672 | **`TwistSoftCouplingFwd`**, `CofinalTwistSoftCouplingFwd`, **`cofinalTwistSeparation_of_cofinalTwistSoftCouplingFwd`**, `goalNeg2_of_…`, `not_…_of_goalPos1` | **main reduction** and its converse |
| 6678 | `twistSeparation_eventually_of_fwd` | per instance: for all large \(j\), then all large even \(R\), X at \((2^j,R)\) gives `TwistSeparation` at every small \(\varepsilon>0\) |
| 6692 | `goalPos1_forces_no_softCoupling` | the positive reading forces (S) or (N) to fail at every large instance |
| 6772-6899 | `rotGauge`, `vacA_rot`, `bulkD_rot`, `De_symm`, `De_rot_comm` | diagonal \(U(1)\): the vacuum carrier and \(D_e\) commute with the rotations; \(D_e\) is symmetric |
| 6932-6990 | `CanonicalU1Line`, `canonicalCoupling_of_U1`, `TwistSoftU1`, `cofinalTwistSeparation_of_cofinalTwistSoftU1` | (N) in complex-line form: \(\langle u_0,D_eu_0\rangle\neq0\) |

Implications (all compiled):

```
CofinalTwistSoftU1 ─→ CofinalTwistSoftCouplingFwd ─→ CofinalTwistSoftCoupling ─→ CofinalTwistSeparation (round 8) ─→ GoalNeg2
                                                           └─→ CofinalPathSoftCoupling ─→ CofinalVacuumCoupling (9.1) ─→ GoalNeg2
GoalPos1 ─→ ¬ each of these
```

## 3. The argument in plain mathematics

Notation (mass \(a=1\), \(\ell=2\), \(k=1\), \(q=2^j\), the dilated tower of round 4):
- \(A(\varepsilon,t)\): actual all-plaquette carrier for the single defect of strength
  \(\varepsilon\) and the frozen exterior twist \(U_t\) (`twistA`);
- \(D(\varepsilon)\): localized correction (`twistD`), independent of \(t\), with \(D(0)=0\);
- \(\mathrm{vac}(t)=A(0,t)\).

### 3.1 Isolated non-units by the identity theorem

Let \(E\) be finite-dimensional and \(t\mapsto A(t)\) symmetric, with every coefficient
\(\langle x,A(t)y\rangle\) real-analytic. Then:
- the Gram determinant \(g(t)=\det[\langle e_i,A(t)e_j\rangle]\) is analytic;
- \(A(t)\) is a unit iff \(g(t)\neq0\).

If \(A\) is a unit somewhere, \(g\not\equiv0\) on the connected line. By the isolated-zeros
principle (Mathlib `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and the identity
theorem), every \(t\) has a punctured neighbourhood of units (`isUnit_punctured`).

### 3.2 Analyticity of the actual carrier in the angle

The frozen exterior path formula (round 5) gives
\[A(\varepsilon,t)=A(\varepsilon,0)+p_E\,W_\varepsilon^*\bigl(\Delta(U_{\varepsilon,t})-\Delta(U_{\varepsilon,0})\bigr)W_\varepsilon\,i_E,\]
with \(W_\varepsilon\) independent of \(t\). The plaquette Hessian \(\Delta(U)\) (curl part
and \(\Delta'\) part) is built from link matrices by products, adjoints, traces, real parts
and finite sums. Each of these preserves entrywise real-analyticity; this is the frozen
continuity chain `D1Cont`, re-proved with `AnalyticAt`. The twist links are
\(\mathrm{diag}(e^{it},e^{-it})\). So the coefficients of \(A(\varepsilon,\cdot)\) are analytic
at **every** curvature and for every profile.

Since \(D\) does not depend on \(t\), the same holds for \(A-D\). Hence:
- the singular angles of the carrier and of the corrected carrier are discrete
  (`twist_isolated_nonunits`);
- at fixed interior data, the positive reading along the twist is an inclusion of two
  discrete sets of zeros.

### 3.3 The vacuum carrier is positive definite at angle 0

At \(\varepsilon=0,t=0\) every link is \(1\). The carriers differ only in the plaquette set
of \(\Delta\):
\[\mathrm{Ginv}_S=p_EW^*\Delta_SW\,i_E+T^*T+\mathrm{Mass}.\]
At the trivial background \(\Delta'=0\), and
\(\langle y,\Delta_Py\rangle=\|\chi_P\,\mathrm{curl}\,y\|^2\) is monotone in \(P\). Since the
mass term is \(\ge0\),
\[\mathrm{Ginv}_{\rm all}\ \ge\ \mathrm{Ginv}_{\rm loc}\ \ge0.\]

The frozen localized theorem `M2RightInv.p428Target8` (the proved localized statement)
gives, for every large \(m\) and then every large \(R\), the instance inequality at every
class configuration. With the positive-energy competitor, `WellDefAt_loc_of_inst` makes the
localized carrier a unit; the trivial configuration is in the class (`dil_regular` at
\(\varepsilon=0\)). PSD plus unit is PD, so \(\mathrm{vac}(0)\) is positive definite.

The thresholds of the frozen theorem are existential, but the cofinal premise only needs
large \(j\) and large \(R\).

### 3.4 The canonical crossing

Round 5 gives a negative direction of \(\mathrm{vac}(\pi)\). Since
\(\mathrm{diag}(e^{-i\pi},e^{i\pi})=\mathrm{diag}(e^{i\pi},e^{-i\pi})\), the same holds at
\(-\pi\).

Let \(t_*\) be the supremum of the initial PSD interval in \([0,\pi]\) (`vacEdge`). Then
\(0<t_*<\pi\), \(\mathrm{vac}(t_*)\) is PSD and singular, and negative directions occur
arbitrarily close after \(t_*\). The isolated non-units of §3.2 give
**positive definiteness arbitrarily close before \(t_*\)**: PSD plus unit is PD. The same
holds for the backward twist \(s\mapsto U_{-s}\) (`twist_vacuum_crossing`). Round 9.1 had
assumed exactly these clauses.

### 3.5 Joint continuity is interior continuity

By the formula in §3.2 and the frozen continuity chain over \(\mathbb R^2\),
\((\varepsilon,t)\mapsto A(\varepsilon,t)\) is jointly continuous at \((0,t)\) for every \(t\)
as soon as \(\varepsilon\mapsto A(\varepsilon,0)\) and \(\varepsilon\mapsto W_\varepsilon\) are
continuous at \(0\) (`pathA_jointly_continuousAt`). These are the first two clauses of (S).

### 3.6 Pre-crossing separation on one side

This is round 9.1's `first_order_separation` (compiled there, reused here). It needs:
- the crossing data of §3.4;
- joint continuity (§3.5);
- \(D(\varepsilon)=\varepsilon D_e+o(\varepsilon)\) (third clause of (S), with \(D(0)=0\));
- \(D_e\ge c>0\) on \(\ker\mathrm{vac}(t_*)\).

It gives, for every small \(\varepsilon>0\), an angle where \(A(\varepsilon,t)\) is positive
definite and \(A(\varepsilon,t)-D(\varepsilon)\) is singular. It applies to the forward twist
or, verbatim, to the backward twist. A separation of the backward twist at \(s\) is a
literal `TwistSeparation` at the angle \(t=-s\).

### 3.7 The gauge flip

- **Covariance.** The frozen `GaugeCov` lane proves
  \(\Delta_P(U^\gamma)\mathrm{Ad}_\gamma=\mathrm{Ad}_\gamma\Delta_P(U)\) for every plaquette set
  \(P\), together with the covariance of \(W\), \(T\), the mass and the localized data. Hence
  the **all-plaquette** carrier is covariant (`Ginv_all_gauge`), and the quadratic form of the
  correction is invariant (frozen `delta2_gauge`).
- **The flip.** The constant gauge \(w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\) conjugates
  \(\mathrm{diag}(a,\bar a)\) into \(\mathrm{diag}(\bar a,a)\). It therefore maps the family at
  \((\varepsilon,t)\) to the family at \((-\varepsilon,-t)\).
- **Consequences.**
  - The backward vacuum twist is unitarily equivalent to the forward one, and the canonical
    crossings coincide (`vacA_flip`, `vacEdge_flip`).
  - \(\langle \mathrm{Ad}_wu,D(-\varepsilon)\mathrm{Ad}_wu\rangle=\langle u,D(\varepsilon)u\rangle\).
    Differentiating at \(0\):
    \[\langle \mathrm{Ad}_wu,D_e\,\mathrm{Ad}_wu\rangle=-\langle u,D_eu\rangle\qquad(\texttt{De\_flip}).\]
  - So \(D_e\le-c\) on the forward kernel iff \(D_e\ge c\) on the backward kernel
    (`couplingPos_back`). A coupling of **either** sign on the forward canonical kernel gives a
    pre-crossing separation on one side, and the literal target follows.

The phenomena of the earlier rounds are one mechanism seen through the flip:
- round 8's post-crossing separation at positive angles (\(c_1<0\));
- round 9.1's pre-crossing separation for the reflected profile.

Both are the pre-crossing separation of the literal family at **negative** angles.

### 3.8 Diagonal \(U(1)\)

All links of the family are diagonal, so the constant rotations
\(\mathrm{diag}(e^{i\alpha},e^{-i\alpha})\) fix every configuration (`rot_pathU`, `rot_bulkU`).
By covariance:
- the vacuum carrier commutes with \(J_\alpha=\mathrm{Ad}_{\mathrm{rot}\,\alpha}\);
- \(D_e\) is symmetric and commutes with \(J_\alpha\) (`De_symm`, `De_rot_comm`).

Suppose the canonical kernel lies in \(\mathrm{span}\{u_0,Ju_0\}\), where \(J=J_{\pi/4}\) and
\(J^2u_0=-u_0\) (i.e. \(u_0\) is charged). Then \(D_e\) acts on it as the scalar
\(\langle u_0,D_eu_0\rangle/\|u_0\|^2\) (round 9.1 `scalar_on_complex_line`). So (N)
becomes **\(c_1(q,R)=\langle u_0,D_eu_0\rangle/\|u_0\|^2\neq0\)** (`CanonicalU1Line`).
Round 9.1 had assumed the commutation; here it is proved.

## 4. What X is, exactly, and what is left

```lean
def InteriorSoft (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (De : E →L[ℝ] E) : Prop :=
  ContinuousAt (fun ε : ℝ => bulkA q R f ε) 0 ∧
  ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1) 0 ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0
--   bulkU q R f ε = maskedU q R (fun e => ε * f e) (fun _ => 1)
--   bulkA = (dataS selAll selAll (bulkP q R f ε)).Ginv, bulkD = localized Delta2

def CanonicalCoupling (q R : ℕ) (V) (De) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))
--   vacEdge q R V = sSup {t ∈ [0,π] | vacA ≥ 0 on [0,t]}

def TwistSoftCouplingFwd (q R : ℕ) : Prop :=
  ∃ De, InteriorSoft q R (dilMask q R) De ∧ CanonicalCoupling q R (uthPath q R) De

def CofinalTwistSoftCouplingFwd : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    TwistSoftCouplingFwd (2^j) R
```

Per instance, X is therefore one analytic lemma (S) and one nondegeneracy (N). Neither is
"finitely many explicit inequalities".

**(S) soft regularity.** A statement about the interior family at the flat interior, with
no exterior angle and no spectral content. It is the expected analyticity of the frozen
assembly. A formal proof needs continuity at the flat interior of:
- `Gp`, the inverse of the Dirichlet operator \(\Omega_0(\Delta_U+Q'^*aQ')\Omega_0\). It is a
  unit there: a field supported in \(\Omega_0\) with zero gradient vanishes.
- `Rproj`, the orthogonal projection onto \(\Delta_UN(Q')\). This needs constant rank of the
  constraints near the flat interior.
- The background tower and the raw jets `Qfull`, `C2full`: derivatives of the averaging maps
  in the field, continuous in the background. This needs joint smoothness of the averaging
  maps, which the frozen library proves only in the field.
- \(H=GQ^*(QGQ^*)^{-1}\). \(G\) is a unit at the flat interior by the frozen theorem, as in §3.3.
- The source \(J\) and its \(\varepsilon\)-derivative.

None of this is in the frozen library, and it was not attempted here.

**(N) nondegeneracy.** An exact statement about an exponentially small number. Round 8
measured \(c_1=K\rho_k^{4qR}\) with \(K\approx-0.019\). Round 9.1 §6 explains why no
qualitative argument produces its nonvanishing:
- every coupling of a crossing mode to the correction crosses a collar of width \(>RM\);
- there is no structural sign or zero;
- the identity theorem only propagates a nonzero coefficient, it cannot produce one;
- `lean/src` has no dilation identity.

This round removes everything around (N) but not (N) itself. The analyticity in the angle
(§3.1–3.2) is what turns the crossing into a theorem. It cannot turn an exponentially
small coupling into a nonzero one.

**What would close X.**
- **(N):** a uniform nonvanishing theorem, either a half-space constant \(K(k)\neq0\) with
  finite-size error bounds (the asymptotic route), or a structural unique-continuation
  argument.
- **(S):** a formal smoothness theorem for the frozen assembly at the flat interior.

**How X compares with the earlier premises**, for the literal family:

| premise | vacuum crossing | joint continuity | angle derivative / gap / scalars | coupling |
|---|---|---|---|---|
| round 8 `CofinalTwistSeparation` | — (spectral statement at positive curvature) | — | — | — |
| round 9.1 `CofinalVacuumNondegeneracy` | assumed | Fréchet in \((\varepsilon,t)\) | slope \(\sigma<0\), gap \(g\), scalar actions | \(c\neq0\) |
| round 9.1 `CofinalVacuumCoupling` (free \(V,f\)) | assumed | assumed | none | definite, either sign (via profile reflection) |
| analytic-r1 `InteriorSoft ∧ VacuumLeftSpectral` (left twist) | kernel assumed | derived | slope negative definite | definite |
| **this round `CofinalTwistSoftCouplingFwd`** | **theorem** | **derived from (S)** | **none** | **definite, either sign, literal family** |

## 5. Numerical evidence (floating point; no certificates; nothing new computed)

`numerics/premise_evidence.py` reads round 8's vacuum and screen outputs and round 9.1's
reflected run (read-only) and writes `numerics/premise_evidence.{json,md}`.

| q | R | char | canonical root \(t_*\) | partner splitting | \(c_1\) | other sectors at \(t_*\) |
|---|---|---|---|---|---|---|
| 2 | 18 | (7, 7) | 0.5639715179856 | 2.115e-161 | -1.81247e-70 | min 0.05196 (128 sectors, IEEE double) |
| 2 | 20 | (7, 7) | 0.5639715179856 | 1.008e-178 | -5.01215e-78 | not screened |
| 2 | 24 | (7, 7) | 0.5639715179856 | 2.287e-213 | -3.83294e-93 | not screened |
| 2 | 30 | (7, 7) | 0.5639715179856 | 2.473e-265 | -8.10577e-116 | not screened |
| 4 | 18 | (15, 15) | 0.5593474882146 | 9.411e-276 | -4.71992e-127 | min 0.01359 (512 sectors, IEEE double) |

Reading of the table:
- **The canonical crossing is the computed crossing.** At the screened instances the only
  non-positive sector at \(t_*\) is the first character, charged. So the end of the initial
  PSD interval of the full carrier is this crossing.
- **The kernel is one charged complex line.** The partner splitting is positive.
- **(N) holds with the negative sign**, and \(c_1\) is the \(U(1)\) scalar of §3.8.
- **Through the flip**, round 9.1's reflected run (curvature \(-10^{-100}\)) is the literal
  family at negative angle. Corrected crossing before the carrier crossing:
  \(t_{C1}-t_{B1}=-5.797\times10^{-171}\). Carrier boundary spectrum there:
  \(1.874\times10^{-170},2.115\times10^{-161},0.998,\dots\) (PD). Corrected lowest eigenvalue
  \(1.6\times10^{-400}\) (singular). Pairing \(+1.812\times10^{-170}\).
- **(S) is supported** by round 8's exact boundary-Schur shifts: they equal the first-order
  prediction \(\varepsilon|c_1|/|\sigma|\) to 8+ digits at \(q=2\) (\(R=18,24,30\)) and
  \(q=4\) (\(R=18\)) (round 9.1 `prediction_check`).

## 6. Files, compilation, axioms

| file | content |
|---|---|
| `Attempt.lean`, `.log`, `.exit` | deliverable; `AHP/round3/lean1.sh` wrapper: exit **0**, no errors, **no warnings**, 433 dependency records |
| `Appendix.lean` | this round's section alone (needs the prefix) |
| `audit.py`, `CHECKS.json` | artifact audit, `pass: true` |
| `scratch/build.py` | assembles `Appendix.lean` and the attempt from `scratch/{appendix_head,P1_abstract,P2_lattice,P3_concrete,P4_flip,P5_u1}.lean` |
| `numerics/premise_evidence.py`, `.json`, `.md` | section 5 |
| `history/Draft{1,2,4}.lean.{log,exit}` | logs of the failed drafts (below) |

`audit.py` checks:
- the round-3 pin, the round-5 IVT attempt and the round-8 attempt are byte prefixes, and the
  round-9.1 appendix follows verbatim;
- the file equals round-8 `Attempt.lean` + round-9.1 `Appendix.lean` + `Appendix.lean`;
- the only import is `DrEquiv`;
- no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque` or
  `axiom` command in the raw source;
- exit 0, with source ≤ log ≤ exit timestamps;
- no error lines, no warning lines, no `sorryAx`;
- every dependency record ⊆ {`propext`, `Classical.choice`, `Quot.sound`};
- each of the 177 appendix declarations has its own record, with exactly these three axioms.

Compile history (wrapper only; no `lake build`, no `REPRODUCE.sh`; no job relaunched):
1. `scratch/S1.lean` (abstract part, `import D1IVT`): exit 1. `AnalyticAt.comp` argument
   forms were wrong; after fixing them, exit 0.
2. `scratch/S2.lean` (abstract + analytic chain): exit 1, because `uMat`/`Uth` need
   `import D1Path`; then exit 0. `scratch/Chk1.lean` checked that the frozen gauge lane lies
   in the import closure of `DrEquiv`: exit 0.
3. `Draft1` (full file): exit 1, 15.5 min.
   - A `let`-bound geometry blocked `pE_inner_right` in `simp`.
   - A `rw` under `Delta2` hit the 16M-heartbeat limit.
4. `Draft2`: exit 1. Two `rw` motive errors, from rewriting an `IngrBParams` under `dataS`.
   Fixed by rewriting the configuration instead and by round 5's `Delta2` congruence trick.
5. `Draft3`: exit 0, no warnings.
6. `Draft4` (+ gauge flip): exit 1, 24 min. `congr 1` in `vacEdge_flip` triggered a
   heartbeat-limit `whnf`; `couplingPos_back` then failed on the missing constant. Replaced by
   `congrArg sSup` on an explicit set equality.
7. `Draft5`: exit 0, no warnings.
8. `Draft6` (+ \(U(1)\)): exit 0, no warnings.
9. `Attempt.lean` (Draft6 + header comment): exit 0, but the audit failed. 48 appendix
   declarations lacked their own `#print axioms` record; the records were added.
10. `Attempt.lean`: exit 0, no warnings; audit pass, 431 records.
11. **Final** `Attempt.lean`, adding `twistSeparation_eventually_of_fwd` and
    `goalPos1_forces_no_softCoupling`: exit 0, no errors, no warnings, 433 records, audit pass.

Superseded drafts and test files were deleted (inside this directory only).

**Hygiene.**
- Only files under `AHP/round9/qualitative-r2/` were written.
- Earlier rounds' outputs were read, never written. No bytecode was written there.
- No protected source, lakefile, paper, notes, expected, extras, earlier round or the
  integration checkout was touched.
- No commit or push.

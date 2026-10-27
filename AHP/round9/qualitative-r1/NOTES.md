# Round 9, qualitative route (r1): first-order separation without asymptotics, free exterior path and free profile

**Status: `GoalNeg2` is NOT closed.** `CofinalTwistSeparation` is not proved either.
What compiled (standard axioms only) are reductions of `GoalNeg2` to statements about
**zero curvature** plus soft first-order regularity:

| theorem (`Attempt.lean` line) | statement |
|---|---|
| `goalNeg2_of_cofinalVacuumCoupling` (4680) | `CofinalVacuumCoupling → GoalNeg2` — **main reduction, weakest X** |
| `goalNeg2_of_cofinalDefectLineCoupling` (4728) | the same premise for the round-4/5 family itself (frozen twist, single defect line) |
| `cofinalTwistSeparation_of_cofinalVacuum` (4333) | `CofinalVacuumNondegeneracy → CofinalTwistSeparation` (the literal round-8 target, both signs, stronger regularity) |
| `not_cofinalVacuumCoupling_of_goalPos1` (4684), `goalPos1_forces_no_vacuum_coupling` (4690) | the positive reading forbids X |

**X = `CofinalVacuumCoupling`** (`Attempt.lean:4657`, unproved). The quantifiers: for
infinitely many dyadic scales \(q=2^j\) and, for each, infinitely many even \(R\ge18\),
there are SOME continuous exterior path \(V\) and SOME interior profile \(f\) with
\(|f|\le1\) such that `VacuumCoupling q R V f` (`:4543`) holds:

1. **vacuum crossing** (zero curvature; the same for every profile): the vacuum carrier
   along \(V\) is positive definite at angles arbitrarily close before some \(t_*\), and
   has a negative direction at angles arbitrarily close after \(t_*\);
2. **regularity:**
   - the actual carrier is jointly continuous in (curvature, angle) at zero curvature,
     for angles near \(t_*\);
   - the actual correction is differentiable in the curvature at \(0\), with derivative
     \(D_\varepsilon\);
3. **nondegeneracy:** \(D_\varepsilon\) is definite, of **either sign**, on the kernel of
   the vacuum carrier at \(t_*\).

Nothing in X is a spectral statement at positive curvature. No angle derivative, no gap
constant and no scalar action on the kernel are assumed. No value of the coupling is
used, only its definiteness.

What X still is: an infinite family of exact statements about the actual vacuum
operators (an implicitly defined crossing angle, its kernel, and a first-order coupling
that is exponentially small in \(Rq\)), plus an unproved soft analytic lemma. It is not
"finitely many explicit inequalities per instance". Section 6 explains why no
qualitative argument removes the per-instance nondegeneracy.

---

## 1. At fixed scale and radius the question is perturbative

Notation:
- \(A(\varepsilon,t)\): the actual all-plaquette carrier (mass 1) at interior curvature
  \(\varepsilon\) and exterior angle \(t\);
- \(D(\varepsilon)\): the actual localized correction. It does not depend on \(t\)
  (round 5; here `pathD_constant`), and \(D(0)=0\) (round 6; here `pathD_zero`).

Separation at \(\varepsilon\) means: some \(t\) has \(A(\varepsilon,t)\) a unit and
\(A(\varepsilon,t)-D(\varepsilon)\) singular. Since \(D(\varepsilon)\to0\), on any set of
angles where \(A(0,\cdot)\) is uniformly invertible, \(A-D\) is invertible for small
\(\varepsilon\). So at small curvature a separation can only split off a **vacuum
crossing** \(t_*\).

Every proof therefore needs a nondegeneracy: the leading order of the splitting between
the corrected crossing and the carrier crossing must be nonzero. The identity-theorem
idea of the brief says the same thing: if the two zero sets agreed for all small
\(\varepsilon\), every Taylor coefficient of the splitting would vanish, so one nonzero
coefficient suffices. The first coefficient is the definiteness of
\(D_\varepsilon=D'(0)\) on \(K=\ker A(0,t_*)\). With the \(U(1)\) symmetry it is one number
\(c\), round 8's \(c_1(q,R)\).

## 2. The pre-crossing theorem: `first_order_separation` (`:3729`)

Abstract, finite-dimensional, compiled. Hypotheses:
- \(A(\varepsilon,t)\) and \(D(\varepsilon)\) are symmetric;
- \(t\mapsto A(\varepsilon,t)\) is continuous for every \(\varepsilon\);
- joint continuity at \((0,t)\) for \(t\) near \(t_*\), in metric form;
- \(A(0,\cdot)\) is positive definite at points arbitrarily close before \(t_*\) and has
  a negative direction at points arbitrarily close after \(t_*\);
- \(\|D(\varepsilon)-\varepsilon D_\varepsilon\|=o(\varepsilon)\) as \(\varepsilon\to0^+\),
  with \(\langle u,D_\varepsilon u\rangle\ge c\|u\|^2\), \(c>0\), for
  \(u\in\ker A(0,t_*)\).

Conclusion: there is \(\varepsilon_0>0\) such that every \(0<\varepsilon<\varepsilon_0\) has
an angle where \(A(\varepsilon,t)\) is **positive definite** (hence a unit) and
\(A(\varepsilon,t)-D(\varepsilon)\) is singular.

Proof (every step compiled):
1. **Vacuum structure.** \(A_0:=A(0,t_*)\) is PSD, as a limit of PD operators
   (`psd_of_pd_before`). Let \(K=\ker A_0\). Compactness of the unit sphere in
   \(K^\perp\) gives a gap: \(\langle y,A_0y\rangle\ge g\|y\|^2\) on \(K^\perp\) with
   \(g>0\) (`exists_gap_of_psd`).
2. **Window.**
   - Joint continuity at \(t_*\) gives a radius \(r_1\): there
     \(\|A(\varepsilon,s)-A_0\|<\delta_0/2\), where \(\delta_0=\min(g/2,1/\kappa)\) and
     \(\kappa=\tfrac2g\bigl(d+c+4(d+1)^2/c\bigr)\), \(d=\|D_\varepsilon\|\).
   - Pick \(t_0<t_*<t_1\) inside that radius, with \(A(0,t_0)\) PD and \(A(0,t_1)\)
     negative on some \(w\).
   - The margin of \(A(0,t_0)\) comes from the frozen `psd_coercive`.
   - Continuity at \((0,t_0)\) and \((0,t_1)\) carries these signs to the corrected
     carrier at every small \(\varepsilon\).
3. **First singular point.** The corrected carrier \(C(t)=A(\varepsilon,t)-D(\varepsilon)\)
   is PD at \(t_0\) and negative at \(t_1\). Round 5's `first_carrier_crossing` gives a
   first singular point \(t_C\in(t_0,t_1)\), where \(C(t_C)\) is PSD and singular.
4. **Comparison** (`pos_of_psd_add`, `:3579`). Write
   \(A(\varepsilon,t_C)=C+\varepsilon D_\varepsilon+R\) with \(\|R\|\le\mu\varepsilon\), \(\mu=c/4\),
   \(C\succeq0\) and \(\|C-A_0\|\le\delta_0\). For \(x=u+y\) (\(u\in K\), \(y\in K^\perp\)):
   - a fraction \(\kappa\varepsilon\) of the PSD form of \(C\) absorbs the
     \(K\)–\(K^\perp\) cross terms;
   - this gives
     \(\langle x,Ax\rangle\ge\varepsilon\bigl[(c-2\mu)U^2-2(\kappa\delta+d)UY+(\kappa(g-\delta)-d-2\mu)Y^2\bigr]>0\),
     where \(U=\|u\|\), \(Y=\|y\|\) (`quad_pos`).

   So \(A(\varepsilon,t_C)\) is positive definite, and the corrected carrier is singular
   at \(t_C\). \(C\) itself may be singular; its PSD form is what kills the cross terms.
   That is why no angle derivative and no Schur complement are needed.

This is the pre-crossing sign (\(c>0\)). The next section gets the other sign for free.

## 3. Path families, and the profile reflection

The class constrains only the interior amplitudes:
- the exterior field is free (round 4/5);
- any bounded interior amplitude mask is allowed (round 5's `maskedU`,
  `masked_regular`).

So the counterexample may use any continuous exterior path \(V\) and any interior profile
\(f\), \(|f|\le1\), at amplitude \(\varepsilon\).

| declaration | content |
|---|---|
| `pathU q R V f ε t` (`:3962`) | links `Ug (ε f e)` on bonds touching \(\Omega_0\), `V t` on the purely exterior bonds |
| `pathA`, `pathD` (`:3971`, `:3977`) | the actual pinned carrier and localized correction of that configuration (mass 1) |
| `pathA_continuous`, `pathD_constant`, `pathD_zero` | continuity in the path parameter (`exterior_carrier_path`, `cont_deltaKLocCLM`); exterior independence of the correction (`data_congr_U`); zero correction at zero curvature (round 6's flat-interior argument) |
| `goalNeg2_of_cofinalPathSeparation` (`:4139`) | cofinal bookkeeping, `masked_regular` in place of `dil_regular` (witnesses below) |
| `vacA`, `pathA_zero` (`:4481`, `:4494`) | at zero curvature every profile has the same vacuum carrier |
| `pathA_neg`, `pathD_neg` (`:4509`, `:4515`) | **reflecting the profile reflects the curvature**: `pathA q R V (−f) ε = pathA q R V f (−ε)`, and the same for `pathD` |
| `eventually_pathSeparation_of_coupling` (`:4600`) | `VacuumCoupling` ⟹ for \(f'=f\) or \(f'=-f\), a separation at every small curvature |
| `twistA_eq_path`, `twistD_eq_path` | the round-4/5 family is `V = uthPath` (frozen `Uth`), `f = dilMask` |

The bookkeeping witnesses are round 8's:
- \(\ell=2\), \(a=1\), \(m=j+1\);
- \(R\) is chosen before the cap \(a_0\);
- \(\varepsilon<\min(a_0/(3840q),1)\), \(\alpha=160\varepsilon\).

The reflection is what makes the sign irrelevant. The correction at profile \(-f\) and
curvature \(\varepsilon\) equals the correction at \(f\) and \(-\varepsilon\), so its first-order
coefficient is \(-D_\varepsilon\). A negative coupling for \(f\) is therefore a positive
coupling for \(-f\), and section 2 applies.

For the round-4 defect line, \(c_1<0\) (round 8, \(q=2,4\)). The theorem then separates
pre-crossing for the reversed defect \(-\)`dilMask`; section 7 checks this numerically.

`CofinalDefectLineCoupling` (`:4715`) is X restricted to that family, i.e. round 8's
vacuum data. It implies X (`cofinalVacuumCoupling_of_defectLine`), hence `GoalNeg2`.

## 4. Both signs for a fixed family: the literal `CofinalTwistSeparation`

`CofinalTwistSeparation` fixes the profile `dilMask` and positive curvature. There the
sign is \(c_1<0\), i.e. post-crossing: the corrected crossing comes after the carrier's,
where the carrier is an indefinite unit. The weak argument of section 2 does not reach
this case; it would need Schur-complement or inertia control at positive curvature. This
round handles it with stronger hypotheses:
- `perturbative_sign_change` (`:3101`, abstract, both signs). It assumes:
  - joint Fréchet differentiability of \(A\) at \((0,t_*)\), and \(D=\varepsilon D_\varepsilon+o(\varepsilon)\);
  - kernel \(K\neq0\) with gap \(g\);
  - the first-order operators act as scalars on \(K\): \(A_t\) as \(\sigma<0\), \(A_\varepsilon\)
    as \(\alpha\), \(D_\varepsilon\) as \(c\ne0\).

  Its conclusion is round 8's `SignChangeControl` interval:
  - \(c>0\): the carrier is PD on the window;
  - \(c<0\): the carrier is an indefinite unit there, certified by round 8's
    `unit_of_definite_complements`.
- The window is explicit: corrected crossing at \(\tau_C=\varepsilon(\alpha-c)/s\), window
  \(\tau_C\pm\varepsilon|c|/(3s)\), with \(s=-\sigma\).
- `VacuumNondegeneracy q R` (`:4313`) is these data for the round-4 family.
  `cofinalTwistSeparation_of_cofinalVacuum` (`:4333`) turns the cofinal version into
  round 8's premise.
- `scalar_on_complex_line` (`:3363`), `PathVacuumNondegeneracyU1`, `pathVacuum_of_U1`:
  the scalar clauses follow from the diagonal \(U(1)\) symmetry. A symmetric operator
  commuting with an orthogonal \(J\) is a scalar on \(\mathrm{span}\{u_0,Ju_0\}\) when
  \(J^2u_0=-u_0\).

This branch needs strictly more regularity than X. It exists because the brief asks for
`X → CofinalTwistSeparation`.

## 5. X in Lean, and the implications

```lean
def VacuumCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0) ∧
    (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ →
      ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 ∧
    0 < c ∧ ((∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

def CofinalVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      VacuumCoupling (2^j) R V f
```

The implications:
```
CofinalDefectLineCoupling ─→ CofinalVacuumCoupling ─→ CofinalPathSeparation ─→ GoalNeg2
CofinalVacuumNondegeneracy ─→ CofinalTwistSeparation (round 8) ─→ GoalNeg2
CofinalVacuumNondegeneracy ─→ CofinalPathVacuum ─→ CofinalPathSeparation
GoalPos1 ─→ ¬ CofinalVacuumCoupling   (and ¬ CofinalPathVacuum, ¬ CofinalTwistSeparation)
```

Relation to the parallel round-9 analytic route (`AHP/round9/analytic-r1`, compiled
separately, as of this writing): that route handles either sign for a FIXED profile with
Schur complements. It needs an angle derivative at the vacuum crossing, and derives joint
continuity from interior continuity. This route needs no angle derivative and no Schur
complements (a first crossing approached from PD instead), and gets the other sign from
the free profile by reflection. The two reductions are complementary, and either can be
combined with an exterior path of one's choice (for instance a left-only twist).

How X compares with `CofinalTwistSeparation`:
- `CofinalTwistSeparation` is "∀δ ∃ε<δ ∃t: unit and non-unit". It is a spectral
  statement at positive curvature, for arbitrarily small curvature.
- X needs, per instance, only the vacuum crossing data and the definiteness of one
  first-order operator on one vacuum kernel. Its only positive-curvature content is soft
  regularity (continuity of the carrier, differentiability of the correction), which
  holds for any smooth assembly.
- The exterior path and the profile are existential, which is an extra freedom.

## 6. Why no qualitative argument removes the per-instance nondegeneracy

These are paper arguments and measurements, not theorems.

1. **The coupling is intrinsically exponentially small, in every admissible geometry.**
   - Admissibility forces the collar: \(\mathrm{dist}(\Omega_0^c,\Omega_1)>R\cdot M\).
   - The correction sees fields only through the blocking jet \(C^{(2)}\) on the
     level-\(\ge1\) coarse bonds, i.e. inside \(\Omega_1\).
   - Exterior fields act only on plaquettes straddling \(\partial\Omega_0\). The interior
     amplitudes are small, and the flat carrier has an \(O(1)\) gap (numerically: boundary
     Schur minimum 1.09 at \(t=0\), every sector \(\ge0.05\)), so crossings must come
     from the exterior.
   - A vacuum crossing vector solves \(Bv=-E_b\Theta_bv_b\). It is a Green's function of
     the flat interior carrier \(B\) from \(\partial\Omega_0\), and decays at \(B\)'s rate.

   So \(\langle v,D_\varepsilon v\rangle=O(\rho^{2RM})\) for every exterior path and profile.
   Round 8 measured \(c_1=K\rho_k^{4Rq}\), with \(K\) constant to 15 digits. The positive
   reading fails, if it fails, only by exponentially small amounts.
2. **No structural zero, no structural sign.**
   - No symmetry kills the coupling: \(U(1)\) and the translations make it a scalar per
     character, and the defect breaks the left/right reflection.
   - No positivity forces it either. \(\langle x,D'(0)x\rangle=2\langle C^{(2)}_0(W_0x),H_0^*J'_0[f]\rangle\)
     (paper formula) pairs a quadratic blocking jet with a fixed vector. For \(SU(2)\) this
     pairs commutator terms, so the form is indefinite for every profile.
   - The finite sum for \(c_1\) has mixed signs (round 8: \(+4.0\times10^{-72}\),
     \(-1.85\times10^{-70}\)).
3. **The identity theorem only propagates a nonzero coefficient.**
   - It turns "some coefficient \(\ne0\)" into "all small \(\varepsilon\)"; that is section
     2.
   - It cannot produce the coefficient. A non-identity at a moderate \(\varepsilon_1\) is
     as exponentially small as \(c_1\): round 8 found shifts near \(10^{-192}\) already at
     \(\varepsilon=10^{-6}\).
   - Special points do not help. \(\varepsilon=0\) gives \(D=0\). \(\varepsilon=\pi\) makes the
     defect holonomy the centre element \(\mathrm{Ug}(\pi)=-1\), with reversed defect
     Hessian, and lies outside the class.
4. **No dilation or covering identity.**
   - The dilated geometry keeps blocking stride 2 and a one-bond defect.
   - Per transverse character, the longitudinal problem has segment lengths
     \(4q, 2Rq, 8Rq+8q\).
   - `lean/src` contains no operator dilation identity (grep: only `ASC2.S_scaling`, a
     scaling of constants).

   So no instance transports to larger \(q\) or \(R\).
5. **The free profile makes the condition linear, not easier to certify.** The coupling
   \(c(f)\) is linear in \(f\). "Some profile couples" means \(H_0C^{(2)}_0(W_0v)\) is not
   orthogonal to all linearized interior sources. This is a qualitative unique-continuation
   statement about one vacuum vector, but its size is still \(O(\rho^{2RM})\). Paper only.
6. **The reachable-set argument** (round 8 §1.5, made concrete here; paper only).
   - In the slab geometry each boundary plaquette has exactly one purely exterior link,
     and that link lies in no other relevant plaquette. So the exterior Hessians
     \(\Theta(W)=\sum_p\Theta_p(h_p)\) are reached with independent \(h_p\in SU(2)\).
   - The positive reading says \(Z_C\cap T\subseteq Z_B=Z_C+\delta N\). It forces
     \(\langle y,\delta N\,y\rangle=0\) on all reachable crossing kernels.
   - If those kernels are rich enough, \(\delta N=E_b^*(\cdots)E_b=0\) exactly.
   - Refuting \(\delta N=0\) is again an exponentially small nonvanishing statement.
7. **Remaining finite-input idea (plan only, not formalized).**
   - Per character, the vacuum data are built from transfer-matrix powers whose period is
     independent of \(q\).
   - A resultant-type nondegeneracy quantity \(\Phi_q(R)\) is then an exponential
     polynomial in \(R\). A linear recurrence with invertible last coefficient would turn
     one nonzero value into infinitely many \(R\).
   - At fixed wave number the constants are \((q,R)\)-independent. The honest finite input
     becomes the half-space constant \(K(k)\ne0\) plus uniform exponential error bounds:
     the asymptotic route, not this one.

## 7. Numerical evidence (floating point, mpmath; no certificates)

**Round-8 vacuum data** (`AHP/round8/guarded-idea/numerics/out/vac_*.json`), for \(q=2\)
(\(R=18,20,24,30\)) and \(q=4\) (\(R=18\)):
- first crossing in character \((7,7)\), resp. \((15,15)\), at \(t_*=0.5639715\), resp.
  \(0.5593475\);
- simple complex charged kernel;
- partner splitting \(2.1\times10^{-161}\) (\(q=2,R=18\));
- slope \(-3.127\), resp. \(-2.629\);
- \(c_1=-1.812\times10^{-70}\) (\(q=2,R=18\)), \(-4.72\times10^{-127}\) (\(q=4,R=18\)).

This is clause 3 of `VacuumCoupling` for (`uthPath`, `dilMask`), numerically, at these
instances. Clause 2 is not computed.

**First-order window vs exact Schur shifts** (`numerics/prediction_check.py`, reads round 8
read-only; output `numerics/prediction_check.json`):

| \(q\) | \(R\) | \(\varepsilon\) | predicted \(\varepsilon|c_1|/|\sigma|\) | measured \(t_{C1}-t_{B1}\) | ratio |
|---|---|---|---|---|---|
| 2 | 18 | 1e-100 | 5.797060885e-171 | 5.797060748e-171 | 0.99999998 |
| 2 | 24 | 1e-140 | 1.225941543e-233 | 1.225941543e-233 | 1.0 |
| 2 | 30 | 1e-170 | 2.592576994e-286 | 2.592576994e-286 | 1.0 |
| 4 | 18 | 1e-170 | 1.795530923e-297 | 1.795530923e-297 | 1.0 |

The other round-8 runs lie outside the window \(\varepsilon\ll g/|c_1|\) (localized-mode or
quadratic regimes), which the theorems allow: they only claim \(\varepsilon<\varepsilon_0\).

**Reflection check (new)** (`numerics/reflected_sepcheck.py`). It runs round 8's exact
boundary-Schur `sepcheck.run` at \(q=2\), \(R=18\), curvature \(-10^{-100}\), 400 digits,
character \((7,7)\), i.e. the reversed defect \(-\)`dilMask`. Round 8's directory is never
written: `OUTDIR` is redirected and no bytecode is written. Output:
`numerics/out/sep_q2_R18_e-1e-100_p400_s7_7_reflected.json`.

| quantity | reflected (\(-10^{-100}\)) | round 8 (\(+10^{-100}\)) |
|---|---|---|
| \(t_{B1}\) | 0.563971518 | 0.563971518 |
| \(t_{C1}-t_{B1}\) | \(-5.797061022\times10^{-171}\) (**before**) | \(+5.797060748\times10^{-171}\) (after) |
| carrier boundary spectrum at \(t_{C1}\) | \(1.874\times10^{-170},\ 2.115\times10^{-161},\ 0.998,\dots\) (**PD**) | \(-1.874\times10^{-170},\ 2.115\times10^{-161},\dots\) (indefinite unit) |
| corrected lowest eigenvalue at \(t_{C1}\) | \(1.6\times10^{-400}\) (singular) | \(-2.2\times10^{-400}\) (singular) |
| unit-kernel pairing \(\langle v,Dv\rangle\) | \(+1.812468145\times10^{-170}\) | \(-1.812468063\times10^{-170}\) |
| corrected-kernel augmented residual | \(1.2\times10^{-394}\) | \(1.5\times10^{-394}\) |

Interval data (reflected): at \(t_{B1}-1.16\times10^{-170}\) and
\(t_{B1}-6.09\times10^{-171}\) both carriers are PD. At \(t_{B1}-5.80\times10^{-172}\) the
carrier is PD and the corrected carrier has one negative direction. That is exactly the
pre-crossing interval of `first_order_separation`.

The pairing flips sign with the profile, as the linearity predicts. The magnitudes differ
in the 8th digit, which is the even second-order term. The run took 657 s, peak RSS 0.9
GB, through `"$BB_CLI" heavy run`. Its log is `numerics/reflected_q2_R18_em100_p400.log`
(ends with the `RESULT` line). The `.exit` file was not written: the launching subshell
ended with the tool call, while the detached job completed.

## 8. Lean: files, compilation, axioms

`Attempt.lean` (4749 lines) = `AHP/round8/guarded-idea/Attempt.lean` **verbatim** (2928
lines; it contains the round-3 pin and the round-5 bridge), followed by `Appendix.lean`
(1821 lines, namespace `AdalyFormal.Round9.Guarded.Qualitative`). Sole import: frozen
`DrEquiv`.

| file | content |
|---|---|
| `Attempt.lean`, `.log`, `.exit` | deliverable; `AHP/round3/lean1.sh` wrapper: exit **0**, no errors, **no warnings**, 256 dependency records |
| `CHECKS.json` | `audit.py` output: `pass: true` |
| `Appendix.lean` | the round-9 section alone (needs the prefix) |
| `audit.py` | audit (below) |
| `scratch/build.py` | assembles `Appendix.lean`, the draft or `Attempt.lean`, and `scratch/Abstract1.lean`, from `scratch/{appendix_head,AbstractCore,AbstractWeak,ConcreteCore,ConcreteWeak}.lean` |
| `scratch/Abstract1.lean`, `.log`, `.exit` | the abstract section alone, with copies of `unit_of_definite_complements` and `first_carrier_crossing` (`scratch/scratch_head.lean`), importing only the frozen Mathlib-only `D1IVT`: exit 0, no warnings; a fast test, not a deliverable |
| `numerics/*` | section 7 |

`audit.py` checks:
- the round-3 pin, the round-5 IVT attempt and the whole round-8 attempt are byte
  prefixes;
- the file equals round-8 `Attempt.lean` + `Appendix.lean`;
- the only import is `DrEquiv`;
- the raw source contains no `sorry`, `admit`, `native_decide`, `unsafe`,
  `implemented_by`, `extern`, `opaque` or `axiom` command;
- exit 0, with source ≤ log ≤ exit timestamps;
- no error lines and no `sorryAx`;
- every dependency record ⊆ {`propext`, `Classical.choice`, `Quot.sound`};
- each of the 74 appendix declarations has its own record.

All 74 print exactly `[propext, Classical.choice, Quot.sound]`.

**Compile history** (wrapper only; no `lake build`, no `REPRODUCE.sh`):
1. On the original 16 GB host two environment probes (`Names*.lean`) never produced
   output: one died before Lean started, one was terminated (exit 143) under memory
   contention. The host was then restarted; queued jobs never ran. Those files were
   removed.
2. `Draft1` (first appendix): exit 1, four errors in the concrete layer:
   - a `simp` goal in `pathD_zero`;
   - a dependent-`rw` timeout in `twistD_eq_path`, fixed with round 5's `Delta2` congruence trick;
   - an ambiguous `not_imp`;
   - an under-determined `_`.
3. `Draft2`: exit 0, six deprecation warnings.
4. `Draft3` (weak theorem and coupling layer): exit 1 (a `neg_smul` rewrite), then exit 0,
   no warnings.
5. `Draft4` (local joint continuity): exit 0, no warnings. `Attempt.lean` was compiled
   from the identical source, exit 0.
6. `Draft5` (adds the defect-line special case): exit 0, no warnings. `Attempt.lean` was
   compiled from the identical source (`cmp` equal), exit 0, identical log.
7. **Final** `Attempt.lean`: the same source with only the appendix header comment
   rewritten. Exit 0, no errors, no warnings, 256 dependency records, audit pass.

Superseded drafts 1–5 and their logs were deleted (inside this directory only).

**Hygiene.**
- Only files under `AHP/round9/qualitative-r1/` were written.
- The round-6 probe and round-8 numerics were imported read-only, with bytecode writing
  disabled. No `__pycache__` appeared there.
- No protected source, lakefile, paper, notes, expected, extras, earlier round or the
  integration checkout was touched.
- No commit or push.

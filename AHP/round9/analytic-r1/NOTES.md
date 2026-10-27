# Round 9, analytic route, pass 1: perturbation in the curvature

**Status: open. `GoalNeg2` is not proved.** No pinned goal (`AHP/round3/guarded/pin/Statement.lean:154-158`) is closed here. Everything below is either a compiled theorem with explicit, unproved hypotheses, or numerical evidence.

**Final compiled reduction** (`Attempt.lean:4539`):

```lean
theorem goalNeg2_of_interiorSoft_vacuumLeftSpectral (hs : InteriorSoft)
    (hc : VacuumLeftSpectral) : GoalNeg2
```

So X = `InteriorSoft ∧ VacuumLeftSpectral` (section 3). Both are statements at **zero curvature** (first order in ε for the correction):

- **`InteriorSoft`** is non-spectral. For every \(q>0\) and even \(R\ge18\), the single interior family \(\varepsilon\mapsto\) `dilU q R ε 1` (curved interior, trivial exterior) satisfies three conditions as \(\varepsilon\downarrow0\):
  - its all-plaquette carrier is continuous;
  - its dressing \(W\) is continuous;
  - its localized correction has a first-order coefficient \(D_1\).

  No exterior angle appears.
- **`VacuumLeftSpectral`** is spectral and needs only infinitely many dyadic scales and, for each, infinitely many radii. For those, the zero-curvature carrier with the **left-only exterior twist** has an angle \(t_0\) with:
  - a nonzero kernel;
  - an angle derivative that is negative definite on the kernel;
  - \(D_1\) definite (of either sign) on the kernel.

What this pass adds:

1. **Step (2) of the IDEA.md route, proved in Lean** (`separation_of_vacuum_kernel`, finite-dimensional, Schur complements). This is the perturbation from zero curvature to *every* small positive curvature. No positivity of the carrier is needed, either sign of the correction works, and no relation between \(\varepsilon\) and any gap is needed.
2. **The bridge with the exterior field free** (`goalNeg2_of_cofinalExtSeparation`). Round 8's `CofinalTwistSeparation` implies its premise. This allows the left-only twist, whose vacuum crossing is a single boundary mode with an O(1) gap. The round-8 twist has an exponentially small left/right splitting instead (section 4.5).
3. **Joint continuity in (curvature, angle) is derived, not assumed.** It follows from the frozen exterior path formula and a multi-parameter version of frozen `D1Cont`. Hence the soft premise contains no exterior angle.
4. **Numerics for step (1)** (evidence only):
   - The normalised vacuum coefficient \(K=c_1/\rho_k^{4qR}\) is a q-independent function \(K(k)\) of the transverse momentum. The dictionary was checked against the actual q = 2, 4, 8 families.
   - \(K<0\) on the whole computed range \(-1.37\le k\le-0.049\).
   - At the first-crossing character, \(K\in[-0.0197,-0.0180]\) for q = 2, …, 256.
   - \(c_1\) is dominated (102–104 %) by one local term at the defect.
   - All-character screens of the left twist (q = 2 and q = 4, R = 18; 128 and 512 sectors) show a single crossing character at \(t_0\).

## 1. What compiled

`Attempt.lean` is the complete round-8 `AHP/round8/guarded-idea/Attempt.lean`, which begins with the round-3 pin and the round-5 `ivt-r2` attempt, followed byte-for-byte by `Appendix.lean`. Sole import: frozen `DrEquiv`. Namespace `AdalyFormal.Round9.Guarded.AnalyticR1`.

The wrapper `AHP/round3/lean1.sh` gives exit **0**, with no errors and no warnings. All **86** new declarations print exactly `[propext, Classical.choice, Quot.sound]`. `audit.py` writes `CHECKS.json` and passes; it checks:

- the pin, round-5 and round-8 byte prefixes, and file = round 8 + `Appendix.lean`;
- the sole import;
- forbidden tokens in the raw source, comments included;
- exit 0, with source ≤ log ≤ exit timestamps;
- no errors and no `sorryAx` in the log;
- every dependency record is within the three allowed axioms, and every new declaration has its own record.

| Line | Declaration | Content (theorem unless a `def` of a premise) |
|---:|---|---|
| 2966 | `exists_psd_nonunit_path` | Frozen `D1IVT.exists_nonunit_path`, proof copied, also returning that the non-unit found is PSD. |
| 3039 | `exists_coercive_on_range` | Positivity of a quadratic form on the range of an idempotent is uniform. |
| 3085, 3088 | `schurC`, `schurS` | \(C(Z)=(1-P)Z(1-P)+P\) and \(S(Z)=PZP-PZ(1-P)C(Z)^{-1}(1-P)ZP\). |
| 3137 | `schur_unit_iff` | If \(P^2=P\) and \(C(Z)\) is a unit, then \(Z\) is a unit iff \(S(Z)\) is injective on \(\operatorname{ran}P\). |
| 3247 | `vacuum_schur_slope` | If \(X(t_0)P=PX(t_0)=0\), then \((t-t_0)^{-1}S(X(t))\to PX'P\). |
| 3286, 3321 | `schur_difference_identity`, `schur_difference_tendsto` | \(c\,[S(X)-S(X-D)]-PD_1P\to0\) as \(X\to X_0\), \(D\to0\), \(cD\to D_1\). |
| 3376 | `core_separation` | Path lemma on \(\operatorname{ran}P\): at the first singular corrected Schur form, the carrier Schur form is injective. |
| 3462, 3709 | `separation_of_vacuum_data_pos`, `separation_of_vacuum_data` | The abstract theorem with a given projection; positive sign, then either sign (reflect \(t\mapsto2t_0-t\) and negate). |
| 3788 | **`separation_of_vacuum_kernel`** | **The abstract step (2)** (section 2.1). |
| 3851-3923 | `TwistSpace`, `ZeroCurvatureRegularity`, `VacuumCrossing`, `VacuumNondegeneracy`, `eventually_twistSeparation_of_vacuum`, `CofinalVacuumNondegeneracy`, **`cofinalTwistSeparation_of_cofinalVacuum`**, `goalNeg2_of_cofinalVacuum`, `not_cofinalVacuum_of_goalPos1` | The same for the round-8 family `twistA`/`twistD`: zero-curvature data imply round 8's `CofinalTwistSeparation`. |
| 3938-4005 | `extP`, `extA`, `extD`, `ExtSeparation`, `CofinalExtSeparation`, **`goalNeg2_of_cofinalExtSeparation`**, `not_cofinalExtSeparation_of_goalPos1`, `extSeparation_of_twistSeparation`, `cofinalExtSeparation_of_cofinalTwistSeparation` | The curved dilated family with an **arbitrary exterior field**, and the cofinal bridge with the exterior field free. Round 8's premise implies its premise; `GoalPos1` refutes it. |
| 4016-4052 | `dilU_agree`, `extD_congr`, `extPath_cont`, `extA_continuous` | \(D\) is independent of the exterior field (frozen `data_congr_U`). The carrier is continuous in the angle along any continuous exterior path (round-5 proof, path left free). |
| 4077-4141 | `PathRegularity`, `PathCrossing`, `PathVacuumNondegeneracy`, `eventually_extSeparation_of_pathVacuum`, `CofinalPathVacuum`, … | Step (2) along any continuous exterior path; cofinal form. |
| 4147-4203 | `leftTwist`, `leftTwist_cont`, `CofinalLeftVacuum`, `goalNeg2_of_cofinalLeftVacuum`, `LeftSoft`, `LeftSpectral`, `cofinalLeftVacuum_of_soft_spectral`, `goalNeg2_of_leftSoft_leftSpectral` | The left-only twist (\(U_\theta\) on exterior bonds with base coordinate \(<4q\)), and an intermediate split of its premise. |
| 4228-4372 | `ContFamT`, `contT_*`, **`contT_deltaKLocCLM`** | Frozen `D1Cont`, proofs verbatim up to renaming, with the parameter space \(\mathbb R\) replaced by any topological space. |
| 4401-4420 | `uMat_continuous`, `Ug_coe`, `dilU_contFamT` | \(U_g(t)=\operatorname{diag}(e^{it},e^{-it})\). The curved family with a continuous exterior path is continuous in (curvature, angle). |
| 4436, 4448 | `tendsto_clm_comp`, **`extA_joint_tendsto`** | Joint one-sided continuity of the carrier in (ε, t) at ε = 0⁺, from continuity in ε of the carrier at the base exterior field and of \(W\). |
| 4501-4532 | `leftTwist_zero`, `InteriorRegularity`, `leftRegularity_of_interior`, `InteriorSoft`, `VacuumLeftSpectral` | The exterior-free soft premise and the spectral premise. |
| 4539 | **`goalNeg2_of_interiorSoft_vacuumLeftSpectral`** | **Final reduction: `InteriorSoft → VacuumLeftSpectral → GoalNeg2`.** |
| 4551 | `not_interiorSoft_and_spectral_of_goalPos1` | `GoalPos1` refutes X. |

Retained records (from `Attempt.lean.log`):

```text
'AdalyFormal.Round9.Guarded.AnalyticR1.separation_of_vacuum_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR1.cofinalTwistSeparation_of_cofinalVacuum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_cofinalExtSeparation' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR1.extA_joint_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR1.goalNeg2_of_interiorSoft_vacuumLeftSpectral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 2. The argument in plain mathematics

### 2.1 The abstract theorem (`separation_of_vacuum_kernel`)

Let \(E\) be a finite-dimensional real inner product space. Let \(X(\varepsilon,t)\) and \(D(\varepsilon)\) be symmetric operators, with \(t\mapsto X(\varepsilon,t)\) continuous for every \(\varepsilon\). Assume:

- (R1) \(X(\varepsilon,s)\to X(0,t)\) as \((\varepsilon,s)\to(0^+,t)\), for \(|t-t_0|<\eta_0\).
- (R2) \(\varepsilon^{-1}D(\varepsilon)\to D_1\) as \(\varepsilon\downarrow0\).
- (V1) \(K=\ker X(0,t_0)\neq0\), and \(X(0,\cdot)\) has a derivative \(X'\) at \(t_0\).
- (V2) \(\langle v,X'v\rangle<0\) for \(0\neq v\in K\).
- (V3) \(D_1\) is definite on \(K\), of **either** sign.

Then there is \(\delta>0\) such that for **every** \(\varepsilon\in(0,\delta)\) some \(t\) has \(X(\varepsilon,t)\) a unit and \(X(\varepsilon,t)-D(\varepsilon)\) not a unit.

### 2.2 Proof

Let \(P\) be the orthogonal projection onto \(K\) and \(Q=1-P\). Then \(X_0=X(0,t_0)\) satisfies \(X_0P=PX_0=0\), so \(C(X_0)=QX_0Q+P\) is a unit. Hence \(C(Z)\) is a unit for \(Z\) near \(X_0\).

1. **Schur reduction.** For such \(Z\): \(Z\) is a unit iff its Schur complement \(S(Z)\) is injective on \(K\).
2. **Vacuum slope.** \(S(X(0,t))=(t-t_0)(PX'P+o(1))\). Fix \(\eta\) with:
   - \(S(X(0,t_0-\eta))\ge\tfrac\sigma2\eta\) on \(K\);
   - \(S(X(0,t_0+\eta))\le-\tfrac\sigma2\eta\) on \(K\);
   - the bounds of step 3 hold on \([t_0-\eta,t_0+\eta]\).
3. **Corrected minus carrier.** An exact algebraic identity for \(S(X)-S(X-D)\), together with (R1), (R2) and \(X_0P=PX_0=0\), gives
   \[\varepsilon^{-1}[S(X(\varepsilon,t))-S(X(\varepsilon,t)-D(\varepsilon))]\to PD_1P\]
   uniformly for \(t\) near \(t_0\).
4. **Positive sign** (\(D_1\ge\nu>0\) on \(K\)). For small \(\varepsilon\):
   - \(S_B(t)=S(X(\varepsilon,t)-D(\varepsilon))\) is \(\ge0\) on \(K\) at \(t_0-\eta\);
   - \(S_B\) has a negative direction at \(t_0+\eta\);
   - \(S_A-S_B\ge\varepsilon\nu/2\) on \(K\) throughout the interval, where \(S_A(t)=S(X(\varepsilon,t))\).
5. **First singular point.** Apply the PSD path lemma to \(S_B+Q\). At the first \(s\) where \(S_B(s)\) is singular it is PSD, so \(S_A(s)\) is positive definite on \(K\). Hence \(X(\varepsilon,s)\) is a unit and \(X(\varepsilon,s)-D(\varepsilon)\) is not.
6. **Negative sign.** Apply the positive case to \(-X(\varepsilon,2t_0-t)\) and \(-D\): same slope, correction \(-D_1>0\). The separation then lies after \(t_0\), at an indefinite carrier unit: the round-8 post-crossing mechanism.

### 2.3 On the actual operators

- **Exterior path.** For a continuous exterior path \(V\), set:
  - \(X(\varepsilon,t)=\) `extA q R ε (V t)`, the all-plaquette carrier for `dilU q R ε (V t)`;
  - \(D(\varepsilon)=\) `extD q R ε (V 0)`.
- **Ingredients.**
  - Symmetry: frozen `Ginv_symm`, `Delta2_spec`.
  - \(t\)-continuity: `extA_continuous`, via the frozen path formula `exterior_carrier_path`.
  - \(D\) independent of the exterior field: `extD_congr`, via frozen `data_congr_U`.

  So the pinned `¬ CPen` at the separating angle is exactly \(X-D\) there.
- **Bookkeeping.** The class bookkeeping is round 8's: \(\ell=2\), \(k=1\), \(a=1\), \(m=j+1\), \(q=2^j\), \(R\) chosen before the cap, \(\varepsilon<\min(a_0/(3840q),1)\), \(\alpha=160\varepsilon\). The class holds for every exterior field (`dil_regular` takes an arbitrary \(V\)), so the bridge leaves \(V\) free.

### 2.4 Joint continuity is not an extra assumption

By `exterior_carrier_path`,
\[X(\varepsilon,t)=X(\varepsilon,0)+p_E\,W_\varepsilon^*\bigl(\Delta(U_{\varepsilon,t})-\Delta(U_{\varepsilon,0})\bigr)W_\varepsilon\,i_E,\]
where \(W_\varepsilon\) is the dressing of `dilU q R ε (V 0)`. The plaquette operator \(\Delta(U_{\varepsilon,t})\) is jointly continuous in \((\varepsilon,t)\) (`contT_deltaKLocCLM` with `dilU_contFamT`). Hence (R1) follows from continuity in \(\varepsilon\) alone of \(X(\varepsilon,0)\) and of \(W_\varepsilon\) (`extA_joint_tendsto`). For the left twist, \(V(0)\) is the trivial exterior field (`leftTwist_zero`), which gives `InteriorRegularity`.

### 2.5 Why the left twist

- **Round-8 twist.** It twists the transverse exterior bonds next to **both** ends of \(\Omega_0\) (\(x=lo-1\) and \(x=hi\)). At zero curvature the vacuum is then mirror symmetric: \(x\mapsto lo+hi-1-x\) maps blocks, \(\Omega_0\), \(\Omega_1\), the coarse constraint bonds and the twisted bonds to themselves. The first crossing is therefore a near-degenerate even/odd pair of boundary modes, split by tunnelling through \(\Omega_0\): \(2.1\times10^{-161}\) at \(q=2,R=18\), and below \(10^{-79}\) at \(q=8,R=2\). (V3) then concerns the exact balanced mode.
- **Left-only twist.** `leftTwist` removes the right crossing. The kernel is one boundary mode, with next Schur eigenvalue \(\approx1\) in its character. Then:
  - \(c_1\) is twice the balanced value;
  - the crossing angle is unchanged;
  - the exterior part has the affine pencil form \(C+\cos t\,A+\sin t\,B\) (numerical error \(<10^{-50}\)).

## 3. X: what is left, exactly

### 3.1 `InteriorSoft` (`Attempt.lean:4525`; unproved, non-spectral)

For every \(q>0\) and even \(R\ge18\) there is \(D_1\) such that, as \(\varepsilon\downarrow0\):

- `extA q R ε 1` → `extA q R 0 1`;
- `Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1` → its value at \(\varepsilon=0\);
- \(\varepsilon^{-1}\,\)`extD q R ε 1` → \(D_1\).

This is analyticity, at the flat interior, of the frozen assembly in the single interior curvature. Mathematically it is standard. Formally it is long, and nothing of it is in the frozen library: only exterior-angle continuity is there. It requires continuity at \(\varepsilon=0\), in operator norm on the fixed carrier, of:

- **`Gp`**, the inverse of `DelpA + (1 − mask)`. It is positive definite at the flat interior, since a field supported in \(\Omega_0\) with zero gradient vanishes.
- **`Rproj`**, the projection onto \(\Delta_UN(Q')\). It needs surjectivity of the constraint map at the flat interior. Then \(P_{\ker}=1-C^*(CC^*)^{-1}C\). The projection onto \(\operatorname{ran}(KQ)\), for invertible \(K\) and projection \(Q\), is \(KQ(QK^*KQ+1-Q)^{-1}QK^*\). Both are continuous.
- The tower `UbarTower` and the raw jets `Qfull`, `C2full` (logarithms near the identity).
- \(H=GQ^*(QGQ^*)^{-1}\). This needs the localized carrier \(B\) to be a unit at the flat interior: it is positive definite numerically, in every character screened.
- The source \(J\) and its \(\varepsilon\)-derivative.

### 3.2 `VacuumLeftSpectral` (`Attempt.lean:4532`; unproved, spectral)

For infinitely many \(j\), and for each infinitely many even \(R\ge18\), let \(D_1\) be the limit of \(\varepsilon^{-1}\,\)`extD (2^j) R ε 1`. Then `PathCrossing` holds for the left twist. That is, at zero curvature there are \(t_0\) and \(X'\) with:

- \(X'\) is the angle derivative of the left-twisted vacuum carrier at \(t_0\);
- the carrier is singular at \(t_0\);
- \(\langle v,X'v\rangle<0\) on its kernel;
- \(D_1\) is definite on its kernel.

Expected proof (the task's route):

- **Characters.** Two-site translation symmetry (round 6 `twoSite_exact_symmetry`; operator equivariance is still unproved). The crossing is in a diagonal character.
- **Kernel.** One complex line, by the U(1) diagonal symmetry. It is two-dimensional over the reals, and \(D_1\) acts on it as the scalar \(c_1(q,R)\). So (V3) is exactly \(c_1\neq0\).
- **Structure.** The data say \(c_1=K_L(k)\,\rho_k^{4qR}(1+O(e^{-\kappa qR}))\). The collar decay \(\rho_k\) has \(2\cosh\kappa=3+T\) and \(T=4(1-\cos k)\). \(K_L=2K\) is a half-space constant.

Then (V3) for all large \(R\) reduces to \(K_L(k)\neq0\) plus uniform finite-size bounds. A closed form for \(K\) needs the flat-collar transfer matrices, which are explicit, joined to the \(\Omega_1\) interface problem: level-1 constraints, gauge fixing \(R\) and dressing \(W\). That interface solution was not obtained.

The theorem does not need the first crossing. Any transversal crossing whose full kernel carries a definite \(D_1\) works, for instance the fixed character \(k=-\pi/8\), which is available for every \(q\ge2\). But no other character may be singular at the same angle.

### 3.3 Weaker or intermediate premises also compiled

- `CofinalLeftVacuum`, `LeftSoft ∧ LeftSpectral`: the same content, with joint continuity assumed instead of derived.
- `CofinalVacuumNondegeneracy`: the round-8 twist. It implies round 8's `CofinalTwistSeparation`. Its (V3) additionally needs the exponentially small splitting and the balanced-mode identification.

## 4. Numerical evidence (round 9; evidence only)

The operators are the round-6 transcription of the actual pinned assemblies (`AHP/round6/probe/probe.py`; dictionary with Lean citations in `SOURCES.md`), imported read-only. The coefficient is \(c_1=2\sum_jh_jC^{(2)}_j(W_0v_0)\) (round-6 `leading_source`/`leading_vacuum`, generalised). Precision is mpmath at 30–80 digits; there are no interval enclosures. Tables are in `numerics/tables.md`; raw data are in `numerics/out/`.

### 4.1 Dictionary: q-dilated sector = q = 1 geometry with a Bloch phase

| actual family | its value | q = 1 geometry with phase \(e^{2ik}\) |
|---|---|---|
| q=2, R=2, (7,7) | \(K=-0.0191639318172\) | R=4: \(-0.0191639318210\) |
| q=4, R=2, (15,15) | \(K=-0.0179649513089\) | R=6: \(-0.0179649513041\) |
| q=8, R=2, (29,29), left twist | \(K_L=-0.0394128337756\) | R=16: \(2\times(-0.0197064168878)\) |

Roots and slopes agree to all printed digits. \(K\) is \(R\)-independent: at \(k=-\pi/8\), \(K=-0.019163934194498\) for \(R=8,10\), round 8's 15-digit value at \(R=18\)–30.

### 4.2 \(K(k)\) on the diagonal (q = 1 geometry, R = 6)

\(K<0\) at every computed \(k\in[-1.374,-0.049]\):
- \(K(-\pi/8)=-0.019164\);
- \(K(-0.30)=-0.019719\) (near the extremum);
- \(K(-\pi/16)=-0.017965\);
- \(K(-\pi/64)=-0.006614\).

It vanishes linearly as \(k\to0\) (q = 1 suppression, \(K(0)\approx10^{-48}\)). Off-diagonal values are \(-0.0157\) to \(-0.0216\); the defect breaks \(y\leftrightarrow z\). The left twist gives \(K_L=2K\) at the five momenta checked.

### 4.3 First-crossing character per scale (diagonal candidates and neighbours)

| q | first (m,m) | \(k=\pi m/4q\) | root | gap to next root scanned | K |
|---|---|---|---|---|---|
| 2 | (−1,−1) | −0.3927 | 0.5639715180 | 2.1e-2 | −0.019164 |
| 4 | (−1,−1) | −0.1963 | 0.5593474882 | 4.6e-3 | −0.017965 |
| 8 | (−3,−3) | −0.2945 | 0.5578780650 | 1.3e-3 | −0.019706 |
| 16 | (−5,−5) | −0.2454 | 0.5576231381 | 2.5e-4 | −0.019246 |
| 32 | (−11,−11) | −0.2700 | 0.5575077988 | 9.4e-5 | −0.019561 |
| 64 | (−21,−21) | −0.2577 | 0.5575041229 | 3.7e-6 | −0.019427 |
| 128 | (−43,−43) | −0.2638 | 0.5574907011 | 9.0e-6 | −0.019500 |
| 256 | (−86,−86) | −0.2638 | 0.5574907011 | 2.9e-6 | −0.019500 |

Only ±2 around the diagonal estimate was scanned.

### 4.4 All-character screen of the left twist (vacuum, double-precision spectra)

`numerics/screen_left.py`, `out/screen_left_q2_R18_vacuum.json`: 128 sectors (64 characters × neutral/charged).
- The localized augmented system has the required inertia (\(B\) PD) in all 128 sectors.
- At \(t=0\) every boundary Schur minimum is \(\ge0.99999\).
- At \(t=0.56397151\) (within \(10^{-8}\) of \(t_0\)), the only non-positive sector is (7,7) charged, at \(3\times10^{-8}\) (double-precision zero). It changes sign between 0.5639 and 0.5641.
- The next lowest are (0,0) charged at 0.0520 and (7,0)/(0,7) at 0.0567.

The q = 4, R = 18 screen (`out/screen_left_q4_R18_vacuum.json`, 512 sectors, 2946 s) is complete:
- \(B\) has the required inertia in all 512 sectors.
- At \(t=0\) every boundary Schur minimum is \(\ge0.99999\).
- At \(t=0.55934749\) the only non-positive sector is (15,15) charged, at \(-4.9\times10^{-9}\) (double-precision zero). It changes sign between 0.5593 and 0.5594.
- The next lowest are (15,14)/(14,15) at 0.0137, then (14,14) at 0.0149.

Summary: `numerics/SCREEN_Q4.md`.

### 4.5 The near-degeneracy trap of the symmetric twist

For the actual q = 8, R = 2 round-8 family, the left/right splitting is below \(10^{-79}\). A 50-digit run reports a spurious "splitting" of \(3.7\times10^{-48}\) and \(c_1\approx3.7\times10^{-103}\). At 80 digits the kernel is still unresolved:
- in character (29,29) the computed vector is right-localised and \(c_1\approx0\);
- in (28,28) it is left-localised and \(c_1\) takes the one-sided value.

The left twist has no such pair: at 50 digits, \(c_1=-6.404\times10^{-31}\), left mass 1, and next Schur eigenvalue 1.02.

### 4.6 Structure of \(c_1\) (left twist, R = 8)

The defect coarse bond \(j=0\) carries 102.2 %, 103.0 % and 104.4 % of \(c_1\) at \(k=-\pi/8,-0.267,-\pi/32\). The \(j=1\) term contributes −2.2 to −4.5 %, and later terms alternate and shrink by factors of about 30–60. In the \(n\to\infty\) limit, \(h_0=36\sqrt2-50=0.91169\) and \(h_1=-3s(1-s^2)=-0.49957\), with \(s=3-2\sqrt2\). So \(\operatorname{sign}c_1=\operatorname{sign}C^{(2)}_0(W_0v_0)\), a single local jet of the dressed vacuum mode at the defect block. In the collar, successive ratios equal \(\rho_k\) to 10 digits.

## 5. What this does not show

- Neither `InteriorSoft` nor `VacuumLeftSpectral` is proved, and nor are the intermediate premises. The reduction is conditional, and `GoalNeg2` remains open.
- The numerics are floating point, with no certified enclosures. Large q is covered only through the q = 1-geometry dictionary, which was checked at q = 2, 4, 8. The character screens are double precision. No closed form for \(K(k)\) and no finite-size bound was obtained.
- The reduction of (V3) to \(c_1\neq0\) by U(1) and translation symmetry is an argument, not a Lean theorem. Operator equivariance of the frozen assembly is unproved.

## 6. Files, commands, compile history

| File | Content |
|---|---|
| `Attempt.lean`, `.log`, `.exit` | Deliverable (round-8 Attempt + `Appendix.lean`); exit 0. |
| `Appendix.lean` | The round-9 section alone. |
| `audit.py`, `CHECKS.json`, `audit.out` | Artifact audit (pass). |
| `numerics/kscan.py`, `firstsector.py`, `actual_check.py`, `lefttwist.py`, `terms.py`, `screen_left.py` | Vacuum data for an arbitrary Bloch phase; first character per scale; actual-family checks; left-twist variant; term structure; all-character screen. |
| `numerics/summarise.py`, `tables.md`, `SUMMARY.json`, `screen_summary.py`, `SCREEN_Q4.md` | Tables and screen summaries (no new numerics). |
| `numerics/batch_r9*.sh`, `*.out`, `*.exit`, `*.log`, `out/*.json` | Job lists and raw outputs. Heavy runs used `"$BB_CLI" heavy run`, 3 GiB caps, single-threaded BLAS. |
| `history/` | Earlier compiled sources and logs (below). |

Reproduce:

```sh
AHP/round3/lean1.sh AHP/round9/analytic-r1/Attempt.lean   # exit 0
python3 AHP/round9/analytic-r1/audit.py                     # pass
cd AHP/round9/analytic-r1/numerics && "$BB_CLI" heavy run -- bash batch_r9.sh
```

Compile history: all through the wrapper, one at a time, launched in persistent terminals after an early background launch died with its tool scope.

1. `Scratch1.lean` and `Scratch3.lean` never finished: no exit file, deleted, and not relaunched as such.
2. `Scratch4.lean` (abstract part): exit 1, two tactic errors.
3. `Attempt.lean` v1–v3: exit 1. Each failed on one error, an instance-path unification failure in `DifferentiableAt.hasDerivAt`; the abstract declarations were clean.
4. v4: exit 0, 54 declarations. It uses an explicit `HasDerivAt` witness inside the crossing data.
5. v5: exit 0, 58 declarations, with the `LeftSoft`/`LeftSpectral` split.
6. v6: exit 1, two errors: a `ContinuousMul` instance not synthesized for operators on `BondFnL2`, and a `rw` pattern under a lambda.
7. v7: launched by mistake on the unchanged v6 source and closed within a minute. It produced no exit file and is not counted.
8. v8: exit 0, 86 declarations, no warnings, audit pass.
9. **Final v9**: v8 with the appendix header docstring updated (comments only, line numbers shifted by 7). Exit 0, 86 declarations, no warnings, audit pass.

`history/` holds the `Scratch4` source and log (item 2), the v1 source, the v1–v3 logs (item 3), the v4 and v5 sources and logs (items 4–5), the v6 log (item 6), and the v8 source (item 8; its log was replaced by the final v9 compile).

Hygiene: files were written only under `AHP/round9/analytic-r1/`, and scratch files were deleted only there. No protected file, earlier round, lakefile or integration checkout was touched. There was no `lake build`, no `REPRODUCE.sh`, and no commit or push.

# Round 9, analytic route, pass 2: the soft premise proved, the spectral premise made explicit

**Status: open. `GoalNeg2` is NOT proved.** No pinned goal (`AHP/round3/guarded/pin/Statement.lean:154-158`) is closed here. Everything below is either a compiled theorem with explicit, unproved hypotheses, or numerical evidence from round 1. No new numerics were run in this pass.

**Final compiled reduction** (`Attempt.lean:7608`):

```lean
theorem goalNeg2_of_vacuumLeftCouplingD (h : VacuumLeftCouplingD) : GoalNeg2
```

For the round-8 twist, the strongest form of the requested `X → CofinalTwistSeparation` is `Attempt.lean:7632`:

```lean
theorem cofinalTwistSeparation_of_twistVacuumCouplingD (h : CofinalTwistVacuumCouplingD) :
    CofinalTwistSeparation
```

So X = `VacuumLeftCouplingD` (section 3). It concerns only **zero-curvature (vacuum) operators**, and every ingredient is explicit. Fix infinitely many \(j\) and, for each, infinitely many even \(R\ge18\). Put:

- \(q=2^j\);
- \(A(t)=\) `extA q R 0 (leftTwist q R t)`, the vacuum all-plaquette carrier with the left exterior twist at angle \(t\);
- \(J'\), the curvature derivative of the localized source.

Then there must be an angle \(t_0\) such that:

- **(V1)** \(\ker A(t_0)\neq0\);
- **(V2)** \(\langle v,A'(t_0)v\rangle<0\) for \(0\neq v\in\ker A(t_0)\), where \(A'\) is `deriv`; the derivative is now proved to exist;
- **(V3)** the explicit coupling \(v\mapsto2\langle H_0C^{(2)}_0(W_0v),J'\rangle\) of the flat localized data is definite, of either sign, on \(\ker A(t_0)\setminus0\).

What this pass adds to round 1 (all compiled, standard axioms only):

1. **Round 1's soft premise is a theorem.** `interiorSoft_proved` (:7282) holds for every \(q>0\) and every even \(R\ge18\). Round 1's \(X\) was `InteriorSoft ∧ VacuumLeftSpectral`; it is now `VacuumLeftSpectral` alone (`goalNeg2_of_vacuumLeftSpectral`, :7287).
2. **The first-order coefficient is identified.** Every limit \(D_1\) of \(\varepsilon^{-1}\Delta^{(2)}(\varepsilon)\) satisfies \(\langle A,D_1A\rangle=2\langle H_0C^{(2)}_0(W_0A),J'\rangle\) (`dil_D1_form`, :6904). The premise no longer mentions a limit operator.
3. **The angle derivative is computed, not assumed.** The plaquette operator is \(C^\omega\) along smooth links (`contDiff_deltaKLocCLM`, :7234). Hence the vacuum carrier is differentiable in the exterior angle, for the left twist and for the round-8 twist (`hasDerivAt_extA_vac`, :7522).
4. **The vacuum path starts positive definite.** At the trivial exterior field the vacuum all-plaquette carrier is positive definite (`extA_vac_one_pos`, :7541), so a crossing angle is never \(0\) (`leftTwist_crossing_ne_zero`, `Uth_crossing_ne_zero`). Round 1's screens saw this numerically for two cases (every boundary Schur minimum \(\ge0.99999\) at \(t=0\)); it is now a theorem for all \(q\) and \(R\).

## 1. What compiled

`Attempt.lean` is round 1's `AHP/round9/analytic-r1/Attempt.lean` verbatim (4644 lines, sha256 `35588209…`), followed byte for byte by `Appendix.lean`. The round-1 file itself begins with round 8, round 5 `ivt-r2` and the round-3 pin. The sole import is frozen `DrEquiv`. The new namespace is `AdalyFormal.Round9.Guarded.AnalyticR2`.

- **Final file:** 7875 lines, sha256 `52614e742421836020e394fd93c21b9696d6db0be2b3b87688ecf63b0de144b9`.
- **Compile:** the wrapper `AHP/round3/lean1.sh` gives exit **0** (about 4 min 53 s), with no error lines and no warning lines.
- **Audit:** `audit.py` writes `CHECKS.json` and `audit.out` and gives **pass = true**. It checks:
  - the pin, round-5, round-8 and analytic-r1 byte prefixes, and that the file equals round 1 + `Appendix.lean`;
  - that the imports are exactly `[DrEquiv]`;
  - that no forbidden token appears in the raw source, comments included;
  - exit 0, and source ≤ log ≤ exit timestamps;
  - no error lines and no `sorryAx` in the log;
  - 500 dependency records, none outside `{propext, Classical.choice, Quot.sound}`;
  - that each of the **232** appendix declarations has its own record. Of these, 188 come from v2 and 44 are new in v3.

Retained records (from `Attempt.lean.log`):

```text
'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCouplingD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.cofinalTwistSeparation_of_twistVacuumCouplingD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.interiorSoft_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.hasDerivAt_extA_vac' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.extA_vac_one_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.dil_D1_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round9.Guarded.AnalyticR2.goalNeg2_of_vacuumLeftCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Main declarations (line numbers in the final `Attempt.lean`)

Each entry is a theorem unless it is a `def` of a premise. "NOT proved" marks premises.

| Line | Declaration | Content |
|---:|---|---|
| 7282 | **`interiorSoft_proved`** | `InteriorSoft` (round 1, :4525) holds. |
| 7287, 7291 | `goalNeg2_of_vacuumLeftSpectral`, `not_vacuumLeftSpectral_of_goalPos1` | `VacuumLeftSpectral → GoalNeg2`; `GoalPos1` refutes `VacuumLeftSpectral`. |
| 7296 | `zeroCurvatureRegularity_proved` | Round 1's `ZeroCurvatureRegularity` for the round-8 family, every \(q>0\) and even \(R\ge18\). |
| 7312, 7320, 7330 | `CofinalTwistVacuumCrossing` (def, NOT proved), `cofinalTwistSeparation_of_twistVacuumCrossing`, `goalNeg2_of_twistVacuumCrossing` | Round-8 twist, abstract \(D_1\): premise → `CofinalTwistSeparation` → `GoalNeg2`. |
| 7344, 7348, 7353 | `flatData`, `vacCoupling`, `IsSourceDerivative` | The flat localized data; the coupling \(2\langle H_0C^{(2)}_0(W_0v),J'\rangle\); \(J'=\lim\varepsilon^{-1}J(\varepsilon)\). |
| 7358, 7368 | `CouplingCrossing`, `VacuumLeftCoupling` (defs, NOT proved) | Crossing data with the explicit coupling, but with an asserted derivative \(X'\). |
| 7373, 7386, 7397 | `pathCrossing_of_couplingCrossing`, `vacuumLeftSpectral_of_coupling`, `goalNeg2_of_vacuumLeftCoupling` | Coupling form → round 1's `PathCrossing` (via `dil_D1_form`) → `GoalNeg2`. |
| 7401, 7408, 7427 | `CofinalTwistVacuumCoupling` (def, NOT proved), `cofinalTwistSeparation_of_twistVacuumCoupling`, `goalNeg2_of_twistVacuumCoupling` | The same for the round-8 twist. |
| 7522 | **`hasDerivAt_extA_vac`** | For an exterior path with smooth links: `HasDerivAt (t ↦ extA q R 0 (V t)) (deriv …) t₀` at every \(t_0\). |
| 7541, 7552, 7562 | `extA_vac_one_pos`, `leftTwist_crossing_ne_zero`, `Uth_crossing_ne_zero` | \(A(0)\) is positive definite; neither twist crosses at angle \(0\). |
| 7575, 7583 | `CouplingCrossingD` (def, NOT proved), `couplingCrossing_of_D` | (V1)–(V3) with \(A'=\) `deriv`; → `CouplingCrossing` for smooth paths. |
| 7591, 7596 | `VacuumLeftCouplingD` (def, NOT proved: **X**), `vacuumLeftCoupling_of_D` | The cofinal left-twist premise; → `VacuumLeftCoupling`. |
| 7608 | **`goalNeg2_of_vacuumLeftCouplingD`** | **Headline: X → `GoalNeg2`.** |
| 7611 | `not_vacuumLeftCouplingD_of_goalPos1` | `GoalPos1` refutes X. |
| 7616, 7621, 7632, 7636 | `CofinalTwistVacuumCouplingD` (def, NOT proved), `twistVacuumCoupling_of_D`, **`cofinalTwistSeparation_of_twistVacuumCouplingD`**, `goalNeg2_of_twistVacuumCouplingD` | The same for the round-8 twist: **X₈ → `CofinalTwistSeparation`**. |

### Supporting declarations

| Line | Declarations | Content |
|---:|---|---|
| 4699, 4727 | `tendsto_of_inner`, `tendsto_clm_of_inner` | Finite-dimensional convergence from inner products. |
| 4920, 4970 | `Rproj_formula`, `continuousAt_Rproj` | Gauge projection \(R=1-X\Gamma^{-1}X^*\) (frozen `M1Site.Rproj_eq_strat`); continuity where \(\Gamma\) is a unit. |
| 5107, 5138 | `delpA_unit`, `wq_pos` | Frozen `CvOX1` lemmas (outside the `DrEquiv` closure), copied. |
| 5279, 5307, 5317, 5328 | `SG_rawStep_fam`, `contDiffAt_qStep_fam`, `continuousAt_fderiv_qStep`, `continuousAt_fderiv2_qStep` | The raw blocking step is jointly smooth in (curvature, field), so both field jets are continuous. |
| 5433, 5444, 5468, 5485, 5507 | `continuousAt_QfullOf`, `tendsto_C2fullOf`, `dataFam`, `continuousAt_Ginv_dataS`, `continuousAt_H` | Continuity of \(Q\), \(C^{(2)}\), the carriers and \(H\) along a family; data on one fixed carrier. |
| 5527, 5551, 5588 | `tendsto_Delta2_div_form`, `tendsto_Delta2_div`, `limit_Delta2_div_form` | \(\langle A,\varepsilon^{-1}\Delta^{(2)}A\rangle\to2\langle H_0C^{(2)}_0A,J'\rangle\); polarization gives \(\varepsilon^{-1}\Delta^{(2)}\to D_1\); the form of every limit. |
| 5740 | `exists_source_derivative` | The localized source is smooth in \(\varepsilon\) and \(J(0)=0\). |
| 5795–5874 | `contDiffAt_Ug`, `dilU_smooth`, `dilU_zero`, `dil_LP_unit`, `dil_Gam_unit`, `dil_Qs_inj` | Flat-point units (Dirichlet operator, \(\Gamma\), \(Q^*\)). |
| 5936 | `final_step` | Frozen `NsPtD2.final_step`, copied. |
| 6579, 6615, 6639 | **`dil_flat_kernel`**, `flat_ginv_form_in`, **`dil_flat_pos`** | The flat localized carrier of the dilated tower is positive definite (section 2.2). |
| 6737–6938 | `dataFam_dil_zero`, `dil_B0_unit`, `dil_Qs0_inj`, `dil_N0_unit`, `extD_eq_dataFam`, `dil_W_cont`, `dil_H_cont`, `dil_C2_tendsto`, `dil_J_tendsto`, `dil_exists_D1`, **`dil_D1_form`**, `interiorRegularity_of_admissible`, `interiorSoft_of_admissible` | Assembly of `InteriorSoft` and the \(D_1\) form. |
| 6969, 6995, 7014 | `inner_Dpi_flat_sel`, `flat_sel_le`, `dil_flat_all_pos` (+ `_psd`, `_unit`) | At the trivial background the all-plaquette form dominates the localized one, so it is positive definite. |
| 7075–7242 | `SmoothFam`, `cdF_*`, `contDiff_of_inner`, **`contDiff_deltaKLocCLM`**, `hasDerivAt_path_formula` | Frozen `D1Cont` with `ContDiff ℝ ⊤` in place of `Continuous`; the abstract derivative of the exterior path formula. |
| 7466–7496 | `uMat_contDiff`, `vac_smooth`, `leftTwist_vac_smooth`, `Uth_vac_smooth` | The links of both twists are \(C^\omega\) in the angle: \(\mathrm{diag}(e^{it},e^{-it})=\exp(it\sigma_3)\), via round 1's `Ug_coe`. |

Round-1 and round-8 results used: `goalNeg2_of_cofinalTwistSeparation` (:2856), `separation_of_vacuum_kernel` (:3788), `goalNeg2_of_cofinalExtSeparation` (:3963), `eventually_extSeparation_of_pathVacuum` (:4099), `extA_joint_tendsto` (:4448), `goalNeg2_of_interiorSoft_vacuumLeftSpectral` (:4539). Round 5's `exterior_carrier_path` (:1798) is used for the path formula.

## 2. The arguments in plain mathematics

Notation, for the curved dilated family \(U_\varepsilon=\) `dilU q R ε 1`:

- **Geometry.** Curvature \(\varepsilon\) sits on the round-4 defect line, and the exterior field is trivial. The fine sides are \((12Rq+16q,8q,8q)\), \(\Omega_0=\{4q\le x_0<12Rq+12q\}\) and \(\Omega_1=\{2Rq+4q\le x_0<10Rq+12q\}\). The parameters are \(\ell=2\), \(k=1\), \(a=1\).
- **Localized assembly.** It has:
  - the gauge-fixing operators: the Dirichlet operator \(L_P\), the constraint Gram \(\Gamma\), the projection \(R\) and \(T\);
  - the dressing \(W\) built from them;
  - the blocking jets \(Q\) and \(C^{(2)}\) of the raw step;
  - the localized carrier \(B=\) `Ginv`;
  - \(H=GQ^*(QGQ^*)^{-1}\) with \(G=B^{-1}\);
  - the source \(J\);
  - the correction \(\Delta^{(2)}\).

### 2.1 `InteriorSoft`

The claim: as \(\varepsilon\to0^+\), the all-plaquette carrier and \(W\) are continuous, and \(\varepsilon^{-1}\Delta^{(2)}(\varepsilon)\) converges.

1. The links are smooth (analytic) in \(\varepsilon\), and \(U_0\) is trivial (`dilU_smooth`, `dilU_zero`). So every site operator built from the links is continuous in \(\varepsilon\).
2. \(L_P=\Delta'_a+(1-\text{mask})\) is a unit at every configuration (`dil_LP_unit`). \(\Gamma\) is a unit at the flat point (`dil_Gam_unit`, frozen `MS6.exists_Gami_strat`). Units form an open set, so \(R=1-X\Gamma^{-1}X^*\), \(T\) and \(W\) are continuous at \(\varepsilon=0\).
3. The raw blocking step is jointly smooth in (curvature, field) (frozen `SG` calculus over \(\mathbb R\times X\)), so its first and second field jets \(Q\) and \(C^{(2)}\) are continuous at \(0\).
4. Hence every carrier is continuous at \(0\) (`continuousAt_Ginv_dataS`).
5. \(B_0\) is positive definite (2.2) and \(Q^*\) is injective at the flat point (`dil_Qs_inj`, frozen `W6F.qs_injective_strat`). So \(N=QGQ^*\) is a unit and \(H\) is continuous at \(0\).
6. \(J\) is smooth with \(J(0)=0\) (`exists_source_derivative`), so \(\varepsilon^{-1}J(\varepsilon)\to J'\).
7. \(\Delta^{(2)}\) is symmetric with \(\langle A,\Delta^{(2)}A\rangle=2\langle HC^{(2)}(A),J\rangle\) (frozen `Delta2_spec`). Dividing by \(\varepsilon\) and using 2–6 gives convergence of the quadratic form. Polarization and finite dimension give \(\varepsilon^{-1}\Delta^{(2)}\to D_1\).

### 2.2 The flat localized carrier is positive definite (`dil_flat_kernel`, `dil_flat_pos`)

At the trivial background,
\[\langle x,B_0x\rangle=\|\chi\,\mathrm{curl}\,x\|^2+\|Tx\|^2+\sum_j a\ell^j\|Q_jx\|^2\]
(`flat_ginv_form_in`, from frozen `NsPtD1.flat_ginv_form`). Suppose this vanishes. Then:

1. \(x\) is curl-free on the plaquettes of \(\Omega_0\).
2. \(x\) vanishes on every bond not touching \(\Omega_1\) (level-0 rows of \(Q\)).
3. The level-1 rows of \(x\) vanish.
4. Integrate \(x\) along the longitudinal lines from the left boundary. This gives a site field \(\xi\) with \(x=D\xi\) on the bonds before the right edge.
5. \(\xi=0\) in the left collar, and \(\xi\) is a transverse constant \(c\) in the right collar. The level-1 rows telescope along the longitudinal chain of blocks, which forces \(c=0\).
6. Hence \(\xi\in N(Q')\) and \(x=D\xi\) everywhere. Then \(T(D\xi)=0\) forces \(D\xi=0\) (frozen `final_step`, copied).

### 2.3 The first-order coefficient (`dil_D1_form`)

From step 7 of 2.1, for every \(A\):
\[\langle A,\varepsilon^{-1}\Delta^{(2)}(\varepsilon)A\rangle=2\langle H(\varepsilon)C^{(2)}(\varepsilon)(W(\varepsilon)A),\varepsilon^{-1}J(\varepsilon)\rangle\to2\langle H_0C^{(2)}_0(W_0A),J'\rangle,\]
and the data at \(\varepsilon=0\) are the flat data (`dataFam_dil_zero`). So every limit \(D_1\) has this quadratic form, which is `vacCoupling q R J' A`. Hence (V3) for \(D_1\) is exactly definiteness of `vacCoupling` on the kernel (`pathCrossing_of_couplingCrossing`).

### 2.4 Smoothness in the exterior angle (`contDiff_deltaKLocCLM`, `hasDerivAt_extA_vac`)

**Path formula.** Round 5's `exterior_carrier_path` is the frozen `DrPath1.Ginv_lit_path` proof. It gives
\[A(t)=A(0)+p_E\,W_0^*\bigl(\Delta(U_t)-\Delta(U_0)\bigr)W_0\,i_E,\]
where \(W_0\) is the dressing at the base field (it does not depend on the exterior field) and \(\Delta(U)=\) `deltaKLocCLM U univ`.

**Smoothness of \(\Delta\).** Every matrix entry \(\langle x,\Delta(U)y\rangle\) is a finite sum of real parts of traces of products of link matrices, their adjoints and constant matrices (frozen `bilPlaq_atoms`, `inner_deltaKLocCLM`). So it is \(C^\omega\) whenever the links are. This is the frozen `D1Cont` proof, with `ContDiff ℝ ⊤` in place of `Continuous`.

**The twisted links.** For both the left twist and the round-8 twist, the exterior links are \(\mathrm{diag}(e^{it},e^{-it})=\exp(it\sigma_3)\) or \(1\), and the other links of the vacuum family are trivial. So \(t\mapsto A(t)\) is \(C^\omega\), and
\[A'(t_0)=p_EW_0^*\Delta'(t_0)W_0i_E.\]

### 2.5 The vacuum path starts positive definite (`flat_sel_le`, `extA_vac_one_pos`)

At the trivial background the \(\Delta'\) part of every plaquette form vanishes (frozen `deltaPrimeBilNormLoc_trivialU`). So:

- the all-plaquette carrier form is \(\|\mathrm{curl}(W_0x)\|^2+\|Tx\|^2+\sum_ja\ell^j\|Q_jx\|^2\);
- the localized form is the same with the curl masked to the localized plaquettes.

Masking only removes nonnegative terms, so \(\langle x,A(0)x\rangle\ge\langle x,B_0x\rangle>0\) for \(x\neq0\) (2.2). Both twists are trivial at \(t=0\), so (V1) forces \(t_0\neq0\).

### 2.6 The chain of implications

Each arrow is compiled:

1. `VacuumLeftCouplingD` → `VacuumLeftCoupling` (2.4: the derivative exists and equals `deriv`).
2. → `VacuumLeftSpectral` (2.3).
3. → `GoalNeg2`, using `interiorSoft_proved` and round 1's `goalNeg2_of_interiorSoft_vacuumLeftSpectral`.

That last step relies on round 1's perturbation theorem `separation_of_vacuum_kernel` (Schur complements). Under (V1)–(V3), for every small \(\varepsilon>0\) there is an angle with the carrier a unit and carrier minus correction not a unit. The cofinal bookkeeping is round 8's, with the exterior field free: \(m=j+1\), \(R\) chosen before the cap, \(\varepsilon<\min(a_0/(3840q),1)\), \(\alpha=160\varepsilon\).

For the round-8 twist, the chain is `CofinalTwistVacuumCouplingD` → `CofinalTwistVacuumCoupling` → `CofinalTwistVacuumCrossing` → `CofinalTwistSeparation`.

## 3. X exactly, and what is left

### 3.1 The premise

**`VacuumLeftCouplingD`** (`Attempt.lean:7591`) reads:

\[
\forall j_0\,\exists j\ge j_0\,\forall R_0\,\exists R\ge R_0:\ 2\mid R,\ R\ge18,\ \forall J'\ \bigl(\text{IsSourceDerivative}(2^j,R,J')\Rightarrow\text{CouplingCrossingD}(2^j,R,\text{leftTwist},J')\bigr).
\]

`CouplingCrossingD q R V J'` (:7575) is: there is \(t_0\) with (V1), (V2) and (V3) of the introduction, where \(A(t)=\) `extA q R 0 (V t)` and \(A'(t_0)=\) `deriv (t ↦ extA q R 0 (V t)) t₀`.

The source derivative \(J'\) exists and is unique (`dil_J_tendsto`), so the \(\forall J'\) is not vacuous. `GoalPos1` refutes X (`not_vacuumLeftCouplingD_of_goalPos1`).

**`CofinalTwistVacuumCouplingD`** (:7616) is the same statement for the round-8 twist `Uth ((dilTower q R).Om 0)`. It is the X of the requested `X → CofinalTwistSeparation`. For this symmetric twist, (V3) additionally involves the exponentially small left/right splitting described in round 1's NOTES, section 4.5. The left-twist form avoids that splitting and is the recommended target.

Weaker intermediate premises are also compiled, each with its bridge:

- `VacuumLeftCoupling` / `CofinalTwistVacuumCoupling`: the derivative is asserted rather than computed.
- `VacuumLeftSpectral` / `CofinalTwistVacuumCrossing`: an abstract limit \(D_1\) replaces the explicit coupling.

### 3.2 Why X is not proved here

X is a spectral statement about an explicit but large operator (\(8q\times8q\) transverse sections, length \(12Rq+16q\)), required for cofinally many \(q\) and \(R\). None of the following is available in Lean:

1. **Sector reduction.** This needs operator equivariance of the frozen assembly under transverse two-site translations, and under the diagonal \(U(1)\) of the abelian twist. Round 6 has `twoSite_exact_symmetry` for the configuration, not for the operators.
2. **Simplicity across characters.** No character other than the crossing one may be singular at \(t_0\), because (V3) concerns the full kernel.
3. **A closed form for the crossing character, or certified bounds.** The flat-collar transfer matrices are explicit. The obstacle is the \(\Omega_1\) interface problem: level-1 constraints, gauge fixing \(R\) and dressing \(W\).
4. **The sign of the coupling on the kernel**, \(c_1\neq0\), and transversality (V2).

### 3.3 Expected route (round 1 data, evidence only)

1. **Character.** The first crossing is in a diagonal character \((m,m)\), with \(k=\pi m/4q\).
2. **Kernel.** Within that character the kernel is one complex line. Under \(U(1)\) invariance the coupling acts on it as a scalar \(c_1(q,R)\), so (V3) is exactly \(c_1\neq0\).
3. **Asymptotics.** The numerics fit \(c_1=K_L(k)\,\rho_k^{4qR}(1+O(e^{-\kappa qR}))\), where \(2\cosh\kappa=3+4(1-\cos k)\) and \(K_L=2K\).
4. **Signs.** \(K<0\) at every computed \(k\in[-1.37,-0.049]\). At the first-crossing character, \(K\in[-0.0197,-0.0180]\) for \(q=2,\dots,256\).
5. **Transversality.** The vacuum slope is about \(-3.13\) in the actual \(q=2\), \(R=2\) family, character (7,7).

Two all-character screens of the left twist were run, both at \(R=18\).

| | q = 2 | q = 4 |
|---|---|---|
| Sectors | 128 | 512 |
| Only crossing sector | (7,7) at \(t_0=0.56397\) | (15,15) at \(t_0=0.55935\) |
| Next lowest | 0.052 | 0.0137 |
| \(B\) has the required inertia | all sectors | all sectors |

These numerics are floating point (double-precision spectra; mpmath for \(c_1\)), with no interval enclosures. Large \(q\) rests on the q = 1-geometry dictionary, which was checked at q = 2, 4 and 8. Tables are in `AHP/round9/analytic-r1/numerics/`.

## 4. Lean engineering notes (for later rounds)

- **Instance paths for operator-valued calculus.** In this Mathlib, `Differentiable`, `deriv` and `HasDerivAt` take plain `AddCommGroup`/`Module`/`TopologicalSpace` instances. Lemmas such as `DifferentiableAt.hasDerivAt`, `Differentiable.add` and `HasDerivAt.const_add` go through `NormedAddCommGroup`.
  - For the concrete submodule carrier `TwistSpace q R →L[ℝ] TwistSpace q R`, the two paths do not unify during elaboration. Round 1's v1–v3 failures had the same cause.
  - For an abstract inner-product space they do unify: `scratch/ProbeDeriv2.lean` exits 0, while `scratch/ProbeDeriv.lean` records the failures.
  - Workaround: state the calculus lemma abstractly (`hasDerivAt_path_formula`) and instantiate it. This is the same pattern round 1 uses for `separation_of_vacuum_kernel`.
- **Frobenius scope.** `open scoped Matrix.Norms.Frobenius` must stay confined to statements about matrix-valued functions. Opened around carrier statements, it breaks instance synthesis of `Inner ℝ (TwistSpace q R)` (first pre-flight compile).
- **Name clashes.** `Ug_coe` is referred to by its full name, because the round-1 namespace is opened wholesale.

## 5. Files, commands, compile history

| File | Content |
|---|---|
| `Attempt.lean`, `.log`, `.exit` | Deliverable: round-1 `Attempt.lean` + `Appendix.lean`; exit 0. |
| `Appendix.lean` | The round-2 appendix alone: `parts_header.lean` + `parts/*.lean` + `final_parts/*.lean` + `#print axioms` lines. |
| `parts/P1.lean`–`P8.lean`, `P9a.lean`, `P9b.lean` | Sources compiled with the dev harness (sections A–K, M, N). |
| `final_parts/P9.lean`, `P9x.lean` | Sources that need round-1 declarations (sections L, O). |
| `parts_header.lean` | Appendix header docstring. |
| `build.py` | Assembler. `dev` writes `dev/Dev.lean`; `full` writes `dev/Full.lean`, a pre-flight copy of the final content; `final` writes `Appendix.lean` and `Attempt.lean` and **overwrites** `Attempt.lean`. |
| `audit.py`, `CHECKS.json`, `audit.out` | Artifact audit (pass). It audits artifacts and proves nothing mathematical. |
| `dev/H0_pin.lean`, `H1_dil.lean`, `H2_r1defs.lean`, `Dev.lean`(+log, exit) | Iteration harness: dev-only verbatim copies of the pin and of the round-4 and round-1 definitions. `Dev.lean` holds the last iteration (P9b only). |
| `scratch/` | Probes. `ProbeDeriv*.lean` cover the instance-path issue; `Probe1–3`, `S1`, `S2` and `T1–T4` are earlier probes from this pass. |
| `history/Attempt.v1.lean`(+log, exit) | v1: exit 0, 7132 lines, `InteriorSoft` proved, abstract \(D_1\). |
| `history/Attempt.v2.lean`(+log, exit), `Appendix.v2.lean`, `CHECKS.v2.json` | v2: exit 0, 7294 lines, sha256 `a0ba00cc…`, audit pass; explicit coupling. |

Reproduce (from the repository root):

```sh
python3 AHP/round9/analytic-r2/build.py final             # regenerates Appendix.lean and Attempt.lean (same bytes)
AHP/round3/lean1.sh AHP/round9/analytic-r2/Attempt.lean   # exit 0, about 5 minutes
python3 AHP/round9/analytic-r2/audit.py                   # pass; writes CHECKS.json
```

Compile history of this pass, all through the wrapper and one at a time:

1. **Dev iterations** (`dev/Dev.lean`, parts only).
   - Many runs for P1–P8.
   - P1–P9a: first two errors (a `positivity` goal and a `rw` under `PiLp`), then exit 0 with one `simpa` lint, which was fixed.
   - P9b: exit 0 with one unused-simp-argument lint, which was fixed. Then exit 0 clean, with `hasDerivAt_path_formula` added.
2. **v1, v2.** Final builds with exit 0 (`history/`).
3. **Pre-flight `dev/Full.lean`** (the v3 content).
   - Run 1: exit 1, instance failures caused by the Frobenius scope.
   - Runs 2 and 3: exit 1, the instance-path failures of section 4.
   - Run 4: exit 0 clean.
   - The file was then deleted; `build.py full` regenerates it.
4. **v3 = final `Attempt.lean`.** Exit 0, 7875 lines, no errors, no warnings, audit pass.

Hygiene:

- Files were written only under `AHP/round9/analytic-r2/`, and deleted only there (`dev/Full.lean*`).
- No protected file, earlier round, lakefile or integration checkout was touched.
- No `lake build`, no `REPRODUCE.sh`, no commit or push.

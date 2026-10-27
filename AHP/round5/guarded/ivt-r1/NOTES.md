# Guarded IVT route — round 5, pass 1

**closedGoal: `none`.** No pinned positive or negative goal is proved.

The numerical sign check supports this route, including at a genuinely admissible small geometry. The new Lean result proves the exact continuous-path reduction for the actual curved-twist operators, including radius-before-cap bookkeeping. It does **not** prove the spectral hypothesis needed to apply that reduction.

## Contract and verification

`Attempt.lean` starts with the entire round-3 pin **byte-for-byte**. Its first 1639 lines are the entire round-4 `refute-r1/Attempt.lean`, also byte-for-byte. Only frozen `DrEquiv` is imported. Every inherited and new local declaration has its own dependency print.

Final commands, executed directly in the bash tool:

```sh
AHP/round3/lean1.sh AHP/round5/guarded/ivt-r1/Attempt.lean
python3 AHP/round5/guarded/ivt-r1/audit.py
```

Final wrapper exit **0**, no errors or warnings. There are **116 local declarations** and **136 dependency records**, all subsets of `propext`, `Classical.choice`, `Quot.sound`. See `Attempt.lean.log`, `Attempt.lean.exit`, and `CHECKS.json`. This is builder verification, not an independent judge replay.

Main conditional declaration, line 1888:

```text
'AdalyFormal.Round5.Guarded.IVTR1.goalNeg2_of_twist_crossings' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Source SHA-256:

```text
64a93e3f111abbddfcac55216a66665695c339272f99483851cc0bed973c90c6
```

Its type has the explicit, **unproved** argument `hcross`. The dependency record does not prove that argument. Calling this a closed `GoalNeg2` would be incorrect.

The round-3 judgement and pin, the round-4 mining report and route notes, and the supplied obstacle text for routes without notes were inspected. The mining catalogue is not independently reverified here. Lost round-4 compiles are not counted as evidence. The reused refute-r1 source is freshly compiled as part of this attempt.

## What is newly compiled

All new names have prefix `AdalyFormal.Round5.Guarded.IVTR1.`

### 1. Curved exterior path, without a flat-interior substitution

`twistU` (1703) is exactly

\[
U_\theta=\operatorname{dilU}(q,R,\varepsilon,
  \operatorname{Uth}(\Omega_0,\theta)).
\]

`twistP`, `twistA`, `twistD` use the actual pinned assemblies, with
\(A=G^{-1}_{\rm all}\) and \(D=\Delta^{(2)}_{\rm in}\). There is no abstract matrix in place of either operator.

- `twist_agrees` (1717): every non-exterior bond is fixed along the path.
- `twist_cont` (1724): the link matrices form a continuous family.
- `twist_data_constant` (1734): all localized base data are constant, despite the **curved** interior. This uses the actual frozen locality theorem, admissibility and \(34\le R(2q)\).
- `twistD_constant` (1742): the genuine assembled correction is constant along the path. No unit hypothesis or continuity of a totalized inverse across a singular point is used.
- `twistA_continuous` (1819): the actual all-plaquette carrier is operator-norm continuous. The proof uses the frozen exterior-path identity, reproduced with qualified locality references, and continuity of the plaquette operator.

### 2. The cap and class can be fixed before the angle

`uniform_curved_family` (1757) strengthens the ordering of the inherited fixed-exterior certificate. For every \(q>0\), even \(R\ge6\), and cap \(a_0>0\), it chooses **one** pair \(\alpha,\varepsilon\) such that:

- capped positive smallness, TorusOK, all admissibility clauses and LambdaOK2 hold;
- the fixed free-bond competitor has positive energy and satisfies both restrictions;
- **for every exterior field V**, the same amplitudes give full ClassCoupled membership and an interior plaquette with nonidentity holonomy.

Thus one does not choose a new class parameter at each angle. The inherited construction still supplies all cofinal geometric and competitor obligations.

### 3. The IVT step does not need a cap-independent correction lower bound

`guarded_separation_of_kernel_positive` (1666) proves the following finite-dimensional statement. Suppose A is a continuous symmetric path, D is fixed and symmetric, \(A(0)-D\) is PSD, and, for some \(T>0\),

\[
\operatorname{IsUnit}(A(t))\quad(0\le t<T),\qquad
A(T)v=0,\qquad \langle v,Dv\rangle>0.
\]

Then there exists \(0\le t<T\) with A(t) a unit and A(t)-D a nonunit. Indeed, at T the corrected quadratic form on v is strictly negative, so frozen `exists_nonunit_path` finds a corrected singular point **strictly before T**. The interval guard therefore holds at that point.

This avoids a separate epsilon/delta construction of a near-null mode: any strictly positive correction on an **exact kernel at the first carrier crossing** suffices. Its size may depend on curvature, scale, radius and cap. `unit_of_strict_quadratic` (1686) also verifies that strict positive definiteness can supply the interval guard, without a uniform numeric gap.

`twist_separation_of_kernel_positive` (1843) specializes this to the actual curved family. Continuity, symmetry and constancy of D are discharged. Initial corrected PSD, the interval carrier guard, the exact endpoint kernel and its positive D-pairing remain explicit hypotheses. The conclusion is exactly a unit of the pinned all-plaquette carrier and failure of the pinned `CPen`, not a compressed substitute.

### 4. Cofinal bookkeeping is now linked to the actual IVT criterion

`KernelPositiveCrossing` (1878) explicitly names those remaining spectral hypotheses at mass a=1. It is a proposition definition, not a proved fact.

`goalNeg2_of_twist_crossings` (1888) proves that the following additional premise implies the **unchanged** `GoalNeg2`:

> For every positive q and every even R at least 18, and every positive amplitude bound delta, there is \(0<\varepsilon<\delta\) satisfying `KernelPositiveCrossing q R epsilon`.

The proof chooses \(\ell=2,a=1,m=m_0+1,q=2^{m_0}\), then
\(R=2(R_0+18)\), **before receiving the cap**. Afterwards it requests a crossing below

\[
\delta=\min\left(\frac{a_0}{3840q},1\right),\qquad
\alpha=160\varepsilon.
\]

It proves capped smallness, reuses the full class/geometry/competitor theorems, applies the exact actual-family IVT theorem, and constructs the pin's `CofinalPencilFailure`. This is a conditional sufficient route, not a weakening or replacement of a pinned goal. The displayed crossing premise is not established.

## Numerical experiment

### Assembly and limits

Scripts are under `numerics/`. `crossing.py` uses the single Abelian defect of the inherited family and Uth on exterior bonds, with \(\ell=M=2,k=1,a=1\). The physical transverse sides are 8. Computation of correction forms uses the period-two transverse sector; `sectors.py` independently assembles all **16** carrier Fourier sectors, retaining phases before inverses, for the R=2 experiment.

The inherited numerical formula transcriptions cite their frozen Lean sources in `assembly.py`, `delta_ops.py`, `wide_probe.py`, and `lift_probe.py`. Their historical standalone-main comments do not describe the new driver; only the imported helper routines are used here.

New `jet2.py` evaluates the raw map's order-two directional Taylor coefficients. The final runs compute **both Q and C2 by Taylor arithmetic**, rather than using a finite difference of Delta or an arbitrary correction matrix. Log and exponential scalar factors use 14-term series near identity. This is floating point, **not** interval arithmetic, exact coefficients, or a Lean operator dictionary. Normalized finite-difference refinements independently check the directional C2 values. In particular, no finite-difference Hessian is used to locate a corrected root.

All numerical processes enforce a **1900 MiB address-space ceiling**, below 2 GB, and run single-threaded through `bb heavy run`. Final peak RSS is at most **796628 KiB**. No dense full-lattice inverse was silently substituted by a compression; each sector's inverses are computed before its boundary Schur complement. The sector-to-frozen-operator identification remains unproved.

### Smallest admissible instance: R=2

Physical fine sides: **(40,8,8)**. Omega0=[4,36), Omega1=[8,32), unit Lambda=[10,12). The inherited round-3 `wide_coverage` covers this small case; it is not the earlier excluded thin-top geometry. It is admissible but does not satisfy the separate reduction room inequality.

For \(\varepsilon=0.0015625\), one may take \(\alpha=0.25\), cap=6. The frozen regularity amplitude inequality and cap inequality are satisfied. The numerical localized gap is positive.

- Numerical carrier crossing: \(\theta_A\approx0.5864553914372679\).
- The two numerical kernel modes have projected D eigenvalues
  \(1.4227226852\times10^{-11}\) and \(1.4227228775\times10^{-11}\).
- At \(\theta_A-10^{-12}\), the two lowest carrier eigenvalues are approximately \(2.199\times10^{-12}\), while their D forms are approximately \(1.423\times10^{-11}\). Thus the computed corrected test forms are about **\(-1.203\times10^{-11}\)**.
- At the same angle, the independent all-sector computation has minimum carrier eigenvalue **\(2.223\times10^{-12}\)**. All other sectors have lowest eigenvalue greater than 0.1247. This is numerical positive definiteness of the transcribed sectors, not a certified full-carrier unit.
- Flipping interior epsilon leaves the sampled correction sign positive: projected values about \(1.423\times10^{-11}\).
- Halving epsilon gives positive projected values about \(2.858\times10^{-12}\). No uniform scaling law or arbitrary-cap conclusion is inferred from two amplitudes.

Data: `crossing_R2_eps0.0015625.json`, `crossing_R2_eps-0.0015625.json`, `crossing_R2_eps0.00078125.json`, and `sectors_R2.json`.

### R=6 diagnostic

Physical fine sides: **(88,8,8)**. This is the smallest R directly covered by the parameterized round-4 dilated certificate. With the same positive epsilon, the numerical four-dimensional near-zero cluster has two positive projected D eigenvalues about **\(4.2830384\times10^{-18}\)** and two values indistinguishable from zero.

This is an important limitation, not a sign certificate. The carrier residual is about **\(8.27\times10^{-15}\)**, much larger than that correction. The cluster may contain distinct true eigenvalues whose splitting cannot be resolved in double precision. A positive direction in the approximate cluster need not lie in the **exact first-crossing kernel**. No pre-crossing corrected negativity is resolved at R=6, and the other 15 sectors were not sampled there. R=6 also does not satisfy the reduction room inequality at M=2.

Data: `crossing_R6_eps0.0015625.json`, generated by the final Taylor-Q run in `crossing_R6_AD.log`. The earlier R=6 finite-difference-Q trial was superseded and is not final evidence.

Reproduction of the final numerical runs:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r1/numerics/crossing.py 2 0.0015625
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r1/numerics/crossing.py 2 -0.0015625
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r1/numerics/crossing.py 2 0.00078125
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r1/numerics/crossing.py 6 0.0015625
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 bb heavy run -- python3 AHP/round5/guarded/ivt-r1/numerics/sectors.py
```

These are numerical probes, not a reproduction/build command for the project.

## Concrete obstacle / next exact work

What is still needed is an actual proof of `KernelPositiveCrossing` for arbitrarily small positive curvature on a cofinal collection of scales and radii. In particular:

1. Establish an initial PSD corrected carrier and an exact first carrier crossing with the guard valid throughout the preceding interval, on the **curved** family. The flat-interior crossing theorem does not directly assert this for dilU.
2. Prove that an exact vector in that first-crossing kernel has **strictly positive** pairing with the genuine assembled D. This requires control of the inverse-propagated mode and the raw-jet/source pairing. Nontrivial holonomy does not imply nonzero D, still less the required sign.
3. Preserve that argument for arbitrarily large m and R, with R chosen before the cap. No verified spectral dilation/Fourier theorem or certified numerical error bound is supplied here.

The successful small numerical sign check is therefore encouraging but insufficient. The R=6 unresolved cluster illustrates why a sampled positive projected correction cannot simply be promoted to the required exact kernel sign. Changing the positive-energy competitor does not change this sign: that competitor is a non-vacuity witness, not an argument of the assembled correction.

The constant-correction, path-continuity, full-class, and cofinal-quantifier steps are now compiled. The remaining spectral crossing/sign obligation is substantive and open.

All authored files are under `AHP/round5/guarded/ivt-r1/`. No protected source, earlier round, lakefile, paper, notes directory, expected output, extras, git commit or push was touched. Lean was invoked only through the serialization wrapper; no direct compiler/build/update/reproduction command or BB terminal was used. One intermediate Lean attempt hit a heartbeats limit in a dependent equality proof; it had a completed nonzero exit and was repaired before the successful recompiles. No timed-out live invocation was duplicated.

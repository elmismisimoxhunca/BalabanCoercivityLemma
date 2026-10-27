# Round 11 probe: the exterior mechanism is bounded, but the window exceeds 4

## Decision

**Do not pursue “arbitrarily many exterior plaquettes per bond”: the frozen lattice has fixed valence.** The exterior-only mechanism is bounded independently of volume, blocking factor and number of twisted links. A bond belongs to only four plaquettes. Moreover, the field carrier contains **touching bonds only**; completely exterior bonds can carry the background twist, but not the test field.

The existing singleton is far from optimal. The same uniform exterior twist, with a transverse checkerboard field, gives a massless Rayleigh quotient **−8**. A compact three-component collar ansatz gives **−4√5 ≈ −8.94427191**; extending the collar gives approximately **−8.947073557014**. Thus there is a promising, much wider *finite-window* refutation, not evidence of an all-positive-mass refutation.

For a flat-touch slab, an elementary bound on the entire bad-boundary operator is **−9**, including arbitrary nonabelian exterior links. A less sharp bound **−12** applies to arbitrary domain shapes with identity background on all touching bonds. The completely unrestricted bare SU(2) plaquette operator has the uniform bound **−16**. These are analytical estimates derived below, **not new Lean theorems**.

**The answer to “is the slice false for every a>0?” remains open.** Boundedness defeats the proposed unbounded-negative-direction strategy; it does not prove the full positive headline at large mass. The carrier mass is a weighted block-average form, not a global scalar identity, and the final form subtracts mass and includes nonlinear/source corrections. No new slice is counted as formally closed here; no Lean file was written or compiled.

**Source reading:** CMP99b defines a positive parameter in (3.24), but its principal propagator estimates explicitly specialize to **a=1** (Theorems 3.1 and 3.3, pp.397,399). The p.428 paragraph does not assert a separate universal quantifier over a. An all-a theorem is therefore a strengthening of the explicitly stated analytic estimates, not something forced by that paragraph. The already-formal a=1 refutation is within the printed specialization.

## 1. What the frozen carrier actually is

Authoritative definitions, rather than historical module headers:

| Object | Frozen location | Content |
|---|---|---|
| E₀ | `lean/src/ZXR2Ops3.lean:25-34` | `bondSupp`: fields supported on bonds with at least one endpoint in Ω₀ |
| Constraint rows | `ZXR2Ops3.lean:49-55` | level-j touching Λj bonds, excluding bonds touching Ωj+1 |
| Mass | `ZXR2Ops3.lean:98-114` | `MassFull = Qfull* diag(a ell^j) Qfull` |
| Site mass and W | `lean/src/ZR2Ops2.lean:22-68` | `ajSeq`, `Qpa`, padded Dirichlet inverse `Gp`, `Wop = I − grad Gp R grad*` |
| Selector dependence | `lean/src/D1Lit.lean:39-64` | `Dpi = iE* W* Delta_corner W iE`; changing selectors only replaces Dpi and J |
| Base carrier | `lean/src/R2Algebra.lean:145-180` | `Ginv = Dpi + T* T + Mass`, `T=R grad*` |
| Corrected inverse carrier | `R2Algebra.lean:154-162,222-233` | G1inv represents `Ginv − Delta2`; `Delta2` contains `2〈H C2(A),J〉` |
| Final form | `D1Lit.lean:85-101` | `eta〈tau*B,N⁻¹tau*B〉 − a〈B,B〉 − 2〈H1(D2in B),J〉` |

In equations, for a fine field A in E₀,

\[
\langle A,G^{-1}A\rangle
=\langle WA,\Delta_{\rm corner}WA\rangle
 +\|R D^*A\|^2
 +a\sum_{(j,b)\in\mathfrak B}\ell^j\|(Q_{\rm full}A)_{j,b}\|^2.
\]

The normalized `Qfull` includes the factor \(\ell^{-j}\); see `lean/src/ZXR2Sector.lean:97-109`. Therefore the mass is **not** \(aI\) on all fine bonds. It has an averaging kernel in higher-level regions. Also a appears inside the site inverse defining W. One may not globally obtain a carrier spectrum merely by adding a to eigenvalues of Delta.

The unweighted `PiLp 2` operators are the eta-free bodies: `lean/src/R2Ops1.lean:20-24`. Refining the lattice does not supply an extra negative factor of eta inverse relative to mass; the common fine-form scaling was already factored out.

### Why the boundary collar is simpler

For identity background on touching bonds, and a sufficiently separated level-zero collar:

1. `Q0=id`; the collar bonds are actual level-zero constraint rows.
2. Higher-level rows do not read this collar (`D1Mass.QlinB_sing_zero`, extended by linearity/locality).
3. `R D*A=0` there, so `WA=A` (`D1Geo2.Tfull_sing_zero`, `Wop_sing`, with the same locality extension).

Consequently the **restriction of the actual carrier form to those collar fields** is exactly

\[
\langle A,G^{-1}A\rangle
=\langle A,\Delta_{\rm corner}A\rangle+a\|A\|^2.
\]

These are collar restrictions of a form, **not** inverse boundary compressions. The scripts never replace an inverse of the full carrier by an inverse of a boundary matrix.

On flat-touch admissible slabs there is also a useful global identity behind our full-carrier computation: if N spans the site-average kernel, then G′R has range in N, which is supported in Ω₁. The resulting gradient correction has zero curl on all interior flat plaquettes and vanishes on boundary plaquettes. Hence \(\Delta\,\mathrm{grad}N=0\), and W drops out of the Delta quadratic term in this particular family. This is not a generic statement about W for nonflat class members. The full numerical implementation applies W explicitly and checks this identity independently.

## 2. Exactly where the old proof uses a<4

`AHP/round7/s1-odd/r2/Attempt.lean:397-401` invokes `exists_nonunit_Ginv`. The actual strict sign calculation is `lean/src/D1Main.lean:100-143` (`Fth_pi_neg`):

- singleton supported on an outward normal touching bond;
- `Wop_sing`: WA=A;
- `Tfull_sing_zero`: TA=0;
- boundary Delta pairing at pi: \(-4\|A\|^2\);
- `D1Mass.Mass_sing_le`: mass at most \(a\|A\|^2\).

Thus the proof establishes

\[
\langle A,G^{-1}(\pi)A\rangle\le(a-4)\|A\|^2<0.
\]

The frozen proof uses an **upper bound**, not a universally proved mass equality for arbitrary geometry. In the separated admissible slab, the level-zero row is present and equality holds.

At theta=0 the reused theorem proves **PSD**, not strict positivity (`D1Main.Fth_zero_psd`); PSD is sufficient for its IVT argument. Continuity and symmetry then give a singular point before pi. Round 7 proves that corner and all selectors give the same compressed carrier (`corner_Dpi_eq_all`, `corner_Ginv_eq_all`) and that every exterior-twist background is in `ClassCoupledFour`.

At singularity, the totalized inverse cascade is decisive: `lean/src/D1Collapse.lean:58` gives the final form \(-a\|B\|^2\), and the positive-energy seed defeats every positive coercivity constant. The extension should replace the endpoint witness, not redesign this collapse argument.

## 3. Numerical experiment and admissible embedding

### Geometry and class

The physical slabs are the already-tested round-5/6 dilated family, with

\[
\ell=2,\quad k=1,\quad R=18,\quad M=2q,
\]
\[
T=(232q,8q,8q),\quad
\Omega_0=[4q,228q)\times T_\perp,\quad
\Omega_1=[40q,192q)\times T_\perp.
\]

`AHP/round5/guarded/ivt-r2/Attempt.lean:986-995` gives the geometry; `dil_torus`, `dil_admissible`, `dil_coverage` occur at 1012,1024,1342. The round-7 transverse slab coverage lemma converts the existing coverage to four-touch coverage. Setting U=1 on every touching bond gives the exact zero logarithm for every touching-class regularity inequality, for **any positive cap**; see round-7 `perCubeRegularTouch_of_one_on_touch`.

Our reduced collars are translated by +4q into that physical slab. Their width is at most eight fine layers, far from Ω₁. They are **not substitute tiny tori claimed admissible**. Transverse periods 8,16,24 correspond to q=1,2,3; the 24-period test only uses the normal boundary field. No new Lean instantiation certificate is supplied here.

### Transcription and checks

- `search.py`: neutral and charged diagonal-SU(2) sectors, patterned exterior phases, sparse collar matrices.
- `nonabelian.py`: independent real three-component SU(2) transcription, general exterior axes and Haar samples.
- `full_carrier.py`: full longitudinal carrier on the physical q=1 slab; two-site transverse Bloch cells, **all 16 characters and both neutral/charged sectors**. It includes W, T and the actual weighted Q mass.

The local plaquette formula follows `DeltaPrimeOperator.secondBilPlaq` in the ordered edge list **ZW,WX,XY,YZ**, not just a cosine-weighted scalar curl. Charged commutator terms are retained. Neutral transcription agrees with `lean/src/CvO23.lean:162` and the round-3 diagnostic. The charged formula agrees with `AHP/round6/probe/probe.py:206-230`.

Both implementations compare their plaquette matrices with direct normalized 2×2 traces: 50 diagonal and 40 general-SU(2) random plaquettes, maximum discrepancy **1.07e−14**. The nonabelian center configuration agrees with the separate neutral implementation to **3.4e−14**. A dense 256-dimensional spectral check independently confirms the first collar value to **9e−15**.

### Results

Uniform exterior twist at theta=pi; minimum of the collar Delta restriction:

| Test field space | Transverse side | Minimum |
|---|---:|---:|
| Boundary normal bonds only | 8,16,24 | −8 |
| One interior layer plus incoming normals | 8,16 | −8.944271909999 ≈ −4√5 |
| Two interior layers | 8,16 | −8.947065710174 |
| Four interior layers | 8,16 | −8.947073556952 |
| Eight interior layers | 8,16 | −8.947073557014 |

Selected width-four, side-eight exterior patterns:

| Pattern | Theta / distribution | Lowest observed |
|---|---|---:|
| Uniform | pi/2 | −4.761346219290 |
| Alternating exterior angle signs | pi/2 | −4.843404944225 |
| Uniform / sign-alternating / opposite directional signs | pi | −8.947073556952 |
| Single exterior link | pi | −0.792409135888 |
| Five random center-link patterns | 0 or pi | −7.292696756635 |
| Five random diagonal patterns | uniform angles in [−pi,pi] | −5.745304037021 |
| Constant orthogonal SU(2) axes | pi/2 | −3.465969529872 |
| Five independent Haar-SU(2) patterns | — | −5.207712217348 |
| Five random-axis patterns near −1 | angle in [0.8pi,1.2pi] | −8.533915329297 |

These are sampled minima, **not a global optimization certificate**. The bounded scalar optimizer encounters a nonglobal charged local minimum near theta=2.75394; the explicit endpoint and angle grid are retained rather than mislabelling that optimizer as global.

Actual full carrier, uniform theta=pi, complete 32-sector screen:

| Mass coefficient | Minimum full-carrier eigenvalue |
|---:|---:|
| Mass removed | −8.947073557014 |
| 8 | −0.947073557014 |
| 9 | +0.052926442986 |
| 20 | +1.941490153890 |

Here “mass removed” means W is the positive-a family W and only the bond mass term is omitted; it is **not** an attempted a=0 statement slice. On this flat-touch family W is independent of positive a by the kernel identity used in the transcription. The full implementation uses

\[
L=P_{\Omega_0}\operatorname{lap}N,\quad H=L^*L,\quad
F=L^*\operatorname{grad}^*E,\quad G=\operatorname{grad}N,
\]
\[
WE=E-GH^{-1}F,\qquad T^*T=F^*H^{-1}F.
\]

Every W term remains in its matrix-vector product. The maximum computed entry of Delta G is **2.45e−16**. The largest full-carrier eigenpair residual is **1.24e−8**; collar residuals are below **9.6e−11**. All calculations are ordinary double precision, not directed-rounding intervals. In particular, the positive entries do not prove positivity for all backgrounds, masses, radii, scales, or the final `InstIneqS`.

**Numerical pitfall caught:** complex ARPACK can return a positive eigenvalue while missing a highly multiple exact gauge-zero eigenspace in massless runs. The final scripts include an explicit local-gradient null-vector check/fallback. `arpack_candidate` and `explicit_null_used` in JSON disclose where this was needed. No such fallback changes a negative minimum or the positive-mass screen.

## 4. Why no unbounded exterior negativity is possible

The following are paper calculations from the frozen SU(2) formula, not compiled Lean results.

Write a plaquette holonomy as \(cI+v\cdot E\), with \(c^2+|v|^2=1\), in the orthonormal anti-Hermitian basis used by the scripts. Write the four signed, transported edge variables in the frozen cyclic order as \(z_i\in\mathbb R^3\). The source-normalized full plaquette form is

\[
q_p(z)=c\left|\sum_i z_i\right|^2+
2\sum_{i<j}v\cdot(z_i\times z_j).
\]

Its diagonal blocks are cI. Each off-diagonal block is \(cI\pm[v]_\times\), of norm at most one: parallel to v the norm is |c|, perpendicular to v it is \(\sqrt{c^2+|v|^2}=1\). Transport rotations preserve these bounds. With r nonzero edge positions, the block row-sum bound is r. Therefore

\[
q_p\ge-r\sum_{e\in\partial p}\|A_e\|^2.
\]

Consequences:

1. **Arbitrary U, bare Delta:** r≤4 and each bond occurs in four plaquettes, hence
   \(\langle A,\Delta A\rangle\ge-16\|A\|^2\).
   No volume or number of twisted bonds occurs in this bound.
2. **Identity on touching bonds:** a plaquette all of whose edges touch Ω₀ is flat and contributes a nonnegative curl square. Every remaining selected plaquette has at least one exterior edge where A=0, so r≤3. Thus its total bad contribution is at least **−12 times the squared norm of the touching boundary-shell field**.
3. **Slab improvement:** each bad plaquette has two normal crossing bonds and one tangential boundary bond. Split the shell into normal n and tangential t components. Normal-normal block norm is at most 8, tangential-tangential block norm at most 1, and the cross block has norm at most √8 (four incidences per normal, two per tangential). Thus
   \[
   q_{\rm bad}\ge-8\|n\|^2-2\sqrt8\|n\|\|t\|-\|t\|^2
   \ge-9(\|n\|^2+\|t\|^2).
   \]
   This includes arbitrary SU(2) exterior choices, not only Cartan twists. Interior plaquettes add a nonnegative form.

For separated flat-touch towers, W leaves this shell unchanged, the mass contains **a times its squared norm**, and the good W-sandwiched plaquettes and T term are nonnegative. Consequently a≥9 on slabs, or a≥12 using the general-shape estimate, eliminates **strict negativity produced by the exterior-only boundary mechanism**. These thresholds are sufficient bounds, not optimal transition values, and nonnegativity alone does not rule out a nullspace.

**Do not substitute a≥16 as a proof for the full headline.** The −16 bound is for bare Delta. For a general nonflat member W is not an orthogonal contraction; Mass is not aI; G1inv has a correction; genFormS subtracts a coarse mass. Every one of those distinctions matters.

## 5. Concrete wider-window witnesses

### Simplest: checkerboard normals

At theta=pi, put a fixed Lie-algebra generator on the incoming normal boundary bonds with amplitudes

\[
f(y,z)=(-1)^{y+z},
\]

and set all other fields to zero. Each of the two transverse forward differences is twice the amplitude. Hence Delta pairing divided by squared norm is −8, rather than the singleton's −4. The actual carrier quotient is a−8. An even transverse period can be chosen independently of ell; alternatively finite alternating square patches approach −8 and avoid global parity issues.

This gives a direct **candidate** extension to 0<a<8 using the same continuous Utheta path, class proof, IVT and collapse theorem. Formal work still needs to carry the geometry and quantifiers for every ell and arbitrarily large m,R.

### Stronger but still compact: one-layer three-variable ansatz

Use the same checkerboard factor. Let n be the incoming normal amplitude, m the next interior normal amplitude, and t the common amplitude on the two tangential bonds at the boundary plane. All other fields vanish. Per transverse site,

\[
\|A\|^2=n^2+m^2+2t^2,\qquad
\langle A,\Delta A\rangle=-8n^2+8m^2-8(n+m)t.
\]

The generalized eigenvalues of this 3×3 form are 0 and ±4√5. For the negative direction take

\[
n=1,\qquad t=\sqrt5-2,\qquad m=(\sqrt5-2)^2.
\]

A rational alternative is n=1, m=1/16, t=1/4, with quotient

\[
-\frac{2584}{289}=-\frac{152}{17}\approx-8.941176470588.
\]

The rational vector was independently evaluated in the assembled matrix with zero reported floating discrepancy. It is a likely cheaper formal target than a half-space spectral-limit theorem. The width-eight value near −8.947 is only a numerical refinement, not needed for a useful precise window.

## 6. Printed treatment of a

Read from the adjudicated corpus, without modifying it:

- `sources/corpus/pages/CMP99b_p393.md:54-58`, (3.16): weighted Q*aQ contains a.
- `CMP99b_p394.md:63-70`, (3.24): recursive site weights, explicitly \(a_1=a_0=a>0\).
- `CMP99b_p397.md:77-80`, **Theorem 3.1:** “the operator G′(U) **(a=1)** satisfies the inequalities”. Constants are stated dependent on d and L only.
- `CMP99b_p399.md:64-67`, **Theorem 3.3:** again “the operator G(U) **(a=1)**”.
- `CMP99b_p428.md:30-32`, (3.156): retains the algebraic subtraction a〈B,B〉.
- `CMP99b_p428.md:53`: the coercivity paragraph promises a lower bound independent of k and U; it neither says independent of a nor adds “for every a>0”.

Thus **general positive a is allowed in definitions; a=1 is explicit in the major analytic theorems.** Retaining a symbol in (3.156) is not a universal-a proof. A paper should distinguish the frozen strengthened all-a question from the source's stated a=1 analytic scope, and not describe a possible large-a repair as rescuing the printed a=1 touching reading.

## 7. Plan for the attack tracks

1. **Finite-window refutation track.** Formalize the normal checkerboard endpoint first (target 0<a<8), then the rational three-variable endpoint (0<a<152/17), or exact radical endpoint (0<a<4√5). Reuse the round-7 pin verbatim, its class/locality transfer and D1 collapse. Do not silently substitute a toy spectral theorem for the exact slice with its m,R,cap and gamma quantifiers.
2. **Mass-domination track.** First formalize the SU(2) local block bound and the −9 slab/−12 shell estimate. Prove shell mass coverage and W-shell locality for admissible towers. Only then attempt large-a positivity of the **full** base and corrected carriers, constraint surjectivity/invertibility, and finally genFormS after the explicit mass subtraction. Carrier positivity alone is not success.
3. **Beyond-the-slab/refutation track.** If seeking every a>0, search for a qualitatively different mechanism: averaging-kernel directions or corrected/final-form failure without a base-carrier crossing. Merely enlarging a flat-touch exterior pattern cannot work by unbounded negativity. Test concave geometry if improving the finite threshold, keeping four-touch coverage; do not conflate that with an unbounded sequence.
4. **Source/statement track.** Record the explicit a=1 specializations and state exactly which theorem is claimed: the source reading, a widened counterexample window, or a genuinely strengthened all-a proposition.

No claim of positivity for a≥9/12, nor of refutation beyond the already-formal 0<a<4 range, is counted as closed in this probe.

## 8. Reproduction and resource audit

Run each script with a 1.8 GiB address-space cap (installed by the scripts), single-thread BLAS, and bytecode disabled:

```sh
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  bb heavy run -- python3 AHP/round11/probe/search.py
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  bb heavy run -- python3 AHP/round11/probe/nonabelian.py
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  bb heavy run -- python3 AHP/round11/probe/full_carrier.py
```

All three recorded `.exit` files contain 0. Final wall times were about 3.5 s, 1.7 s and 68.5 s; peak RSS at most **104 MiB**. Commands ran through the heavy scheduler, with no Lean jobs. The initial numerical run exposed the multiple-zero-eigenvalue issue described above; the final runs include its explicit check. All authoring was confined to `AHP/round11/probe/`; no earlier round, protected source, lakefile, integration checkout, git commit/push, build or REPRODUCE command was touched.

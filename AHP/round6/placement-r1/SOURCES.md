# Numerical operator dictionary — boundary placement

`placement_probe.py` imports `AHP/round6/probe/probe.py` read-only with Python bytecode disabled. It does not call that module's `run` function or write its output directory. Its only change to the family is overriding `Family.angle`: the interior defect coordinate is `4*q+2`, rather than `(2*R+4)*q`. Exterior fields in the source diagnostic are at angle zero; the formal theorem permits every exterior field.

The imported module's full dictionary is `AHP/round6/probe/SOURCES.md`. The references below cover every operator actually used in the new diagnostic. This is a transcription dictionary, not a formal numerical/Lean equivalence theorem.

## Family and geometry

- `AHP/round6/placement-r1/Attempt.lean:986-995`: the verbatim `dilLu`, `dilTower`, `dilLam` geometry. Physical fine sides `(q*(12*R+16),8*q,8*q)`.
- Same file `:2451-2458`: new `placementPattern` and `placementU`. Fine link at `x=4*q+2`, direction 1, even transverse coordinates. The computational cell is period two, not a new admissible torus. The source solve is the zero transverse character and neutral SU(2) component.
- Same file `:2496-2507`: actual `placementP` assembly and its compiled zero-correction theorem.
- `lean/src/ZR2B4.lean:30-44`: `Ug epsilon = diag(exp(i epsilon),exp(-i epsilon))`.
- `lean/src/D1Path.lean:25-47`: exterior-bond predicate and twist.
- `lean/src/ZXR2Wire1.lean:20`: `geomOf`.
- `lean/src/ZXR2Ops3.lean:26,30,50`: touching carrier bonds, carrier subspace, level constraint bonds. `Family.b0` implements the actual level-zero bond-set difference, not all collar-touching bonds without the Omega1 exclusion.

## Linear assembly and full source solve

- `lean/src/AdalyFormal/Balaban/CovariantOperators.lean:247,301,315`: adjoint transport, gradient, curl. Charged transport is multiplication by `exp(2*i*angle)`; neutral transport is identity.
- `lean/src/R2Ops1.lean:108,135,141,150,166,170`: Laplacian, site average, constrained kernel/image and projection.
- `lean/src/AdalyFormal/Balaban/QjComposite.lean:675` and `AdalyFormal/Balaban/TowerLawCovariant.lean:171`: site averaging and staircase order.
- `lean/src/ZR2Ops2.lean:27,63,67,100`: site penalty, padded inverse, W and T. With N a basis of the site-average kernel, L=P_Omega0 lap N, H=L*L, F=L* grad* E, G=grad N, the transcription uses `W E=E-G H^-1 F` and `T*T=F* H^-1 F`.
- `lean/src/ZXR2Ops3.lean:98,102,134`: level weights, mass and assembled `baseData`.
- `lean/src/D1Lit.lean:41,45,56,61`: selected Delta, W dressing, source sign and assembled selected data. At mesh one the source used here is plus i times the localized imaginary-holonomy divergence.
- `lean/src/R2Algebra.lean:145,149,220-226`: carrier, constrained H and genuine correction identity.

The sparse augmented matrix is

\[
\begin{pmatrix}
K&-V&-F^*\\
-V^*&Z+H&H\\
-F&H&0
\end{pmatrix},
\quad
K=E^*\Delta_{in}E+\mathrm{Mass},\ V=E^*\Delta_{in}G,\ Z=G^*\Delta_{in}G.
\]

The full neutral KKT matrix appends the actual Q and Q* constraint blocks. Its multiplier is H*J when the inverses exist. `Family.hj` solves this complete system; it does not invert a boundary compression. The independent candidate has zero carrier/auxiliary fields, multiplier `J` on identity level-zero rows, and zero positive-level multiplier. `Q* j0 = J` is checked directly in the mpmath matrix. The formal theorem separately handles singular totalized cases and does not need numerical invertibility.

## Plaquette Hessian and source

- `lean/src/AdalyFormal/Target/ClayStatement.lean:1286`: plaquette word.
- `lean/src/AdalyFormal/Balaban/SuTwoInner.lean:104`: the SU(2) inner product.
- `lean/src/AdalyFormal/Balaban/DeltaPrime.lean:125,133`: real/imaginary holonomy.
- `lean/src/AdalyFormal/Balaban/DeltaPrimeOperator.lean:287-330,363,376,386,395`: ordered plaquette contributions and bilinear forms.
- `lean/src/ZLocOps.lean:119,186`: normalized symmetrization and localized curl-plus-Delta-prime.
- `lean/src/ZLocJ.lean:20,49,71` and `lean/src/AdalyFormal/Balaban/SourceJ.lean:228`: localized curvature and covariant divergence source.

The new source solve uses the neutral zero character: neutral plaquette energy is `cos(h)*(v1+v2-v3-v4)^2`, and the source is the signed boundary of `sin(h)`. It is not replaced by a mask of nontrivial holonomy.

## Raw jets and the zero mechanism

- `lean/src/R2Raw1.lean:36,43,68,74`: raw path products and endpoint block corrections.
- `lean/src/AdalyFormal/Balaban/UbarTowerCovariance.lean:237`: blocked link.
- `lean/src/AdalyFormal/Balaban/SuTwoLogExpCore.lean:164,226`: group exponential/logarithm.
- `lean/src/R2RawX.lean:187`, `lean/src/ZLocJet.lean:35,39,89,100`: derivatives.
- `lean/src/ZXR2Sector.lean:83,97,109`: normalized first jet and one-half second derivative; level-one normalization is another factor one-half.
- `lean/src/ZXR2Sector.lean:69`, `lean/src/ZLocJet.lean:118`: identity first jet and zero second jet at level zero.
- `lean/src/GdTheta.lean:56,70`: zero level-zero pairing and source factorization through Q*.
- `lean/src/GdAbs.lean:23,29,38`: QH identity on unit constraints, singular inverse branch, and correction-zero theorem.
- `AHP/round6/placement-r1/Attempt.lean:2423,2473,2502,2749`: new actual source-support proof, family flat-neighborhood proof, family zero theorem, and general boundary-strip zero theorem.

`Family.rawjet` uses analytic order-two Taylor arithmetic in mpmath, not a finite-difference Hessian. `Family.correction(w,hj)` evaluates the exact transcribed expression `2 sum (H*J)_b C2_b(w)` on positive-level rows. The new test w is an arbitrary charged bond field; it is NOT asserted to equal Wv for a chosen carrier vector and is not a kernel/crossing vector. This distinction is recorded in the script, data and report. Since the positive-level multiplier is zero, the expression vanishes for every input; the Lean theorem proves vanishing for all actual dressed carrier inputs without relying on that numerical observation.

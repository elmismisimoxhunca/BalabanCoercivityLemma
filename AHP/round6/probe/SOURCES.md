# Operator dictionary for the numerical scripts

All paths below are in the unchanged checkout. The scripts are transcriptions, not Lean definitions, proofs or interval certificates. `probe.py`, `check.py`, `batch.py`, and subsequent drivers share this dictionary. The validation imports the older numerical helpers read-only, with bytecode writing disabled.

## Family, carriers, and symmetry

- `AHP/round5/guarded/ivt-r2/Attempt.lean:986-995`: `dilLu`, `dilTower`, `dilLam`. Physical fine sides are `(q*(12*R+16),8*q,8*q)`. Omega0 is `[4*q,(12*R+12)*q)`; Omega1 is `[(2*R+4)*q,(10*R+12)*q)` in the longitudinal coordinate, with both full transverse circles.
- Same file `:1379-1387`: `dilPattern`, `dilU`. The defect is a direction-1 link at `x=(2*R+4)*q`, with both transverse coordinates even. Crucially, the period is **2**, not `2*q`.
- Same file `:1703-1716`: `twistU`, `twistP`, `twistA`, `twistD`. The mass parameter is exactly 1, ell=2, k=1. q dilates geometry, **not** ell or the level-one blocking stride.
- `lean/src/ZR2B4.lean:30-44`: `Xm`, `Ug`; this is `diag(exp(i*eps),exp(-i*eps))`.
- `lean/src/D1Path.lean:25-47`: `Zb`, `uMat`, `Uth`. The exterior twist is on bonds with neither endpoint in Omega0.
- `lean/src/ZXR2Wire1.lean:20`: `geomOf`; `lean/src/ZXR2Ops3.lean:26,30,50`: touching bond carrier and level constraints. Neither the physical torus nor its admissibility is replaced by the period-two cell.

Translations by two in either transverse direction form `C_(4q) x C_(4q)`. Their characters are `exp(2*pi*i*iy/(4q))`, `exp(2*pi*i*iz/(4q))`. A lifted cell field at `(x,y+2a,z+2b)` is the cell value times the two characters, divided by `4q` for isometry. Background, sets, blocking paths, and all primitive operators are equivariant. Adjoints, orthogonal projections, and (when they exist) full inverses consequently preserve the sectors. For a **linear** operator this gives `(4q)^2` sectors, not a compression followed by an inverse.

The diagonal SU(2) background also commutes with global diagonal gauge rotations. In the orthonormal basis `E1=diag(i,-i)`, `E2=[[0,1],[-1,0]]`, `E3=[[0,i],[i,0]]`, write the charged coordinate as `z=v2+i*v3`. It transforms by `exp(2*i*angle)`. This separates one neutral real component and one charged complex component. A simple complex charged kernel has real dimension **two**, not one.

The nonlinear second jet is not sector-preserving as a linear map. Its neutral quadratic output from one charged character is translation invariant, so it pairs with the zero-sector neutral `H*J`. The lift's `1/(4q)^2` quadratic factor cancels the number of translated cells. `correction()` uses this cancellation explicitly; it does not invert a compressed nonlinear operator.

## Linear primitives

- `lean/src/AdalyFormal/Balaban/CovariantOperators.lean:247,301,315`: adjoint SU(2) transport, gradient and curl. The scalar charged gradient is `-f(x)+exp(2*i*angle)*f(x+mu)`, including Bloch phases on wrapping.
- `lean/src/R2Ops1.lean:108,135,141,150,166,170`: laplacian, site averaging, constrained site kernel, image and projection.
- `lean/src/AdalyFormal/Balaban/QjComposite.lean:675`: step average; staircase order is 2,1,0, from `AdalyFormal/Balaban/TowerLawCovariant.lean:171`.
- `lean/src/ZR2Ops2.lean:27,63,67,100`: site penalization, padded inverse, W, T. Let N be any full-rank basis of the site-average kernel, L=P_Omega0 lap N, H=L*L, F=L* grad* E, G=grad N. Then `W E=E-G H^-1 F` and `T*T=F* H^-1 F`. Our N is explicitly constructed from the eight entries of each disjoint site-average block; it is **not orthonormal**, which is immaterial to the image projection formula.
- `lean/src/ZXR2Ops3.lean:98,102,134`: mass weights `1` on level zero and `2` on level one, assembled data, and `C2(W A)`.
- `lean/src/R2Algebra.lean:145,149,222`: carrier, H, and genuine correction pairing.
- `lean/src/D1Lit.lean:41,45,56,61`: selected Delta, W dressing, sign of source, selected assembled data. At mesh one, source is **+i** times the localized divergence of imaginary holonomy.

For localized Delta, set K=E*Delta E+mass, V=E*Delta G, Z=G*Delta G. The actual B inverse is obtained from the sparse Hermitian augmented system

```
[K, -V, -F*; -V*, Z+H, H; -F, H, 0].
```

Eliminating the last two variables gives `W*Delta W+T*T+mass`. Thus the carrier is never replaced by the inverse of a selected boundary compression. The boundary Schur is computed **after full inversion**. On omitted plaquette edges G is zero, so A=B+E_boundary Theta E_boundary*. The localized constrained solve uses the further exact KKT block `[Aug,Q*;Q,0]`: its multiplier is `(Q B^-1 Q*)^-1 Q B^-1 J=H*J`.

## Plaquette Hessian and source

- `lean/src/AdalyFormal/Target/ClayStatement.lean:1286` (module path may be resolved through imports): plaquette word.
- `lean/src/AdalyFormal/Balaban/SuTwoInner.lean:104`: `-Re trace(XY)/2`, for which E1,E2,E3 above are orthonormal.
- `lean/src/AdalyFormal/Balaban/DeltaPrime.lean:125,133`: real/imaginary holonomy.
- `lean/src/AdalyFormal/Balaban/DeltaPrimeOperator.lean:287-330,363,376,386,395`: four ordered contributions and first/second plaquette bilinear forms.
- `lean/src/ZLocOps.lean:119,186`: normalized symmetrization and curl-plus-Delta-prime form.
- `lean/src/ZLocJ.lean:20,49,71`, `AdalyFormal/Balaban/SourceJ.lean:228`: localized source and covariant divergence.

If a plaquette word is `diag(exp(ih),exp(-ih))`, and the four **ordered** charged contributions are `a1=-R(U_nu)v3`, `a2=-v4`, `a3=v1`, `a4=R(U_mu)v2`, its energy is

`cos(h)*|sum ar|^2 + 2*sin(h)*sum_(r<s) Im(conj(ar)*as)`.

The neutral energy is `cos(h)*(v1+v2-v3-v4)^2`. The neutral source is the signed boundary of `sin(h)`. `plaq()` scatters these formulas with Bloch phases before any inversion.

## Raw jets

- `lean/src/R2Raw1.lean:36,43,68,74`: rProd, endpoint block corrections and raw step.
- `lean/src/AdalyFormal/Balaban/UbarTowerCovariance.lean:237`: blocked link.
- `lean/src/AdalyFormal/Balaban/SuTwoLogExpCore.lean:164,226`: exponential/logarithm (all base log arguments here are near identity).
- `lean/src/R2RawX.lean:187`, `lean/src/ZLocJet.lean:35,39,89,100`: first and second derivatives.
- `lean/src/ZXR2Sector.lean:83,97,109`: second Taylor coefficient is one-half of the second derivative, and both jets at level one have the additional **1/2** normalization.

`rawjet()` carries exact order-two directional Taylor algebra in mpmath, not a finite difference and not a fixed truncated power series in eps. A charged variation has SU(2) upper entries `(a0+a2*t^2, b1*t)`. Multiplication, inverse, exp, and log coefficients are evaluated analytically with arbitrary-precision trigonometric functions. It returns the normalized first charged and second neutral coefficients. The neutral first jet is exactly the average of the sixteen middle-path fine-bond entries. Flat charged first-jet rows have that same expression; all curved rows are differentiated explicitly.

The genuine value is `2 sum_i (H*J)_i C2_i(Wv)`; level-zero C2 is zero. This includes propagation of J through the full localized constrained solve. It is not simply a curvature mask or a finite difference of Delta.

## Further reductions checked in this probe

- `positivity.py` uses the same `R2Algebra.lean:145,149,222` assembly, replacing localized Delta in the augmented system by Delta minus the full raw-jet Hessian paired with H*J. The local Hessian is computed from `R2Raw1.lean:74` and `ZXR2Sector.lean:109`, not guessed from the carrier.
- `path_identity.py` reduces only the omitted-plaquette contribution using `D1Path.lean:46` and `DeltaPrimeOperator.lean:287-395` / `ZLocOps.lean:119,186`. The observed sine/cosine pencil identity and its Loewner consequence are mathematical reductions, not new frozen declarations.
- `leading_source.py` reduces the epsilon derivative of `D1Lit.lean:56` / `ZLocJ.lean:49,71`, propagated by the constrained H of `R2Algebra.lean:149`. In the neutral transverse-uniform channel, `ZXR2Sector.lean:97` imposes the two-site average constraint. The curl form of `ZLocOps.lean:186` on `(a_j,-a_j)` has diagonal 6 and off-diagonal 1. Its finite tridiagonal Green function is the hyperbolic-sine expression in PROBE.md.
- `leading_vacuum.py` computes the first epsilon coefficient of `R2Algebra.lean:222` by pairing that explicit source derivative with the **actual vacuum** `ZXR2Sector.lean:109` second jet on the numerically reconstructed first kernel. It is a finite-sum coefficient, not a positive assumption. In the decisive test it is negative.

# s1-touching — shell regularity, stage A

Not a theorem. Nothing here was compiled. Numerical output is evidence about a transcribed quadratic form, not a proof of `P428Target8` or of its negation.

Rejected predecessor: `AHP/attempts/s1-touching/` (`SOL_VERDICT.md`, reject). That draft's `CoversPlaqCorner` asked every one-corner plaquette of \(\Omega_0\) to have all four bonds as touching bonds of one frozen class cube. Frozen cubes sit in \(\Omega_0\) (`DescribedAt`, `ZStatementP428.lean:131`, and `classCube_sub_om0` in `D1Final.lean:36`). A proper nonempty \(M\)-block domain has a one-corner plaquette whose opposite bond has both endpoints outside \(\Omega_0\), so the coverage class collapsed to \(\Omega_0\in\{\emptyset,T\}\). This note does not use `CoversPlaqCorner`, does not claim `plaqCorner = plaqIn`, and does not conclude the frozen `InstIneq`.

## What changed relative to the print

CMP 102 p.277, as quoted in `paper/OPEN_ITEMS.md` S-1: a region is the bonds with at least one endpoint in it, and the plaquettes with at least one corner in it.

| piece | print / frozen | this variant |
|---|---|---|
| \(\Delta\), \(J\) on \(\Omega_0\) | print (3.10), (3.11) sum every plaquette of \(T_\eta\); frozen `plaqIn` (`ZR2Ops2.lean:74`) keeps only plaquettes whose four bonds have both endpoints in \(\Omega_0\) | `plaqCorner`: at least one corner in \(\Omega_0\) |
| bonds of a class cube | print, CMP 102 bond sentence: at least one endpoint; frozen `CubeBond` (`ZStatementP428.lean:145`): both endpoints | not merely `TouchBond`. Smallness is required on `ReadBond`: every bond of every plaquette that has a corner in the cube. That set contains bonds with **neither** endpoint in the cube |
| where the cube sits | `DescribedAt` / `IsClassCube` (`ZStatementP428.lean:131`, `:140`): sites in \(B^j\cup B^{j+1}\subset\Omega_0\) | unchanged. Cubes do not move outside \(\Omega_0\) |
| coverage | `CoversOm0c` (`ZR2A.lean:107`) and `CoversPlaqOm0c` (`ZR6A.lean:27`), packaged as `ClassCoupled` (`ZR6A.lean:124`) | same two coverage conjuncts. No corner-coverage conjunct |
| \(\Lambda\), \(\tilde B\) | already at-least-one (`OnLambdaT` `ZR2A.lean:121`, `CRowIn` `ZStatementP428.lean:211`) | unchanged |
| quantifiers | `P428Target8` (`ZT5A.lean:291`) | same order, same \(c=12\), same \(k\ge 1\) |

The outer-bond clause is the departure from a literal CMP 102 **bond** reading. A plaquette with one corner in the cube has an opposite bond whose endpoints both lie outside the cube, so "at least one endpoint" does not see it. The operators do see it, because the plaquette has a corner in \(\Omega_0\). Putting (3.35) and (3.36) on `ReadBond` is the plaquette sentence pushed onto every bond that plaquette reads. It is stronger than the printed bond convention. It constrains the additional bonds read by the corner operators: site coverage puts each corner in \(\Omega_0\) in some cube, and that cube's `ReadBond` then contains all four boundary bonds of the plaquette, without the cube's sites leaving \(\Omega_0\). Non-vacuity instead uses frozen coverage and the flat configuration; it does not require this strengthening.

`TouchBond` alone does not do this. On every slab and cube tested below, the bonds with neither endpoint in \(\Omega_0\) are disjoint from `TouchBond(\(\Omega_0\))` and meet `ReadBond(\(\Omega_0\))`.

## Variant, in Lean text

Uncompiled. Intended file later: `AHP/fidelity/s1-touching/lean/ShellTouch.lean`. Names below are proposals, not declarations in `lean/`.

```lean
import ZStatementP428
import ZR2A
import ZR6A
import ZR2Ops2
import D1Lit

open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.D1Literal
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)

/-- CMP 102 bond sentence: at least one endpoint. Not the shell. -/
def TouchBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  b.1 ∈ sites ∨ periodicLatticeShift b.1 b.2 ∈ sites

/-- CMP 102 plaquette sentence: at least one of the four corners. -/
def plaqCorner {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L)) :
    Set (PeriodicLatticePlaquette L) :=
  {p | p.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.1 ∈ S
    ∨ periodicLatticeShift p.1 p.2.1.2 ∈ S
    ∨ periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∈ S}

/-- Bonds read by a corner-plaquette of `sites`, including bonds with neither endpoint in `sites`. -/
def ReadBond {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L)) (b : Bond L) : Prop :=
  ∃ p : PeriodicLatticePlaquette L, p ∈ plaqCorner sites ∧ b ∈ periodicPlaquetteBoundaryEdges p

def CurlReadsRead {L : PeriodicLatticeExtent} (sites : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (a b : Fin 3) : Prop :=
  ReadBond sites (periodicLatticeShift x a, b) ∧ ReadBond sites (x, b) ∧
  ReadBond sites (periodicLatticeShift x b, a) ∧ ReadBond sites (x, a)

/-- `PerCubeRegular2` (`ZR2A.lean:48`) with `CubeBond` replaced by `ReadBond` and `CurlReads` by `CurlReadsRead`.
Cube sites, the factor `f`, the index, and the quantifier order `∃ g,A` inside `∀` cube stay as in `ZR2A.lean:48`. -/
def PerCubeRegularShell {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ), IsClassCube ell M f k S sites j →
    ∃ (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ)
      (A : Bond L → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ e : Bond L, ReadBond sites e →
        HT (A e) ∧
        ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ)
          = NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
        frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
      (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
        ReadBond sites ((x, ν) : Bond L) → ReadBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
        frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν)))
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
      (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
        (∀ ν : Fin 3, ν ≠ μ → CurlReadsRead sites (periodicLatticeShiftBack x ν) ν μ ∧
          CurlReadsRead sites x ν μ) →
        frobNorm (ddA η A x μ)
          < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

/-- Frozen coverage, shell regularity. Same factor `c` in both, as in `ClassCoupled` (`ZR6A.lean:124`). -/
def ClassCoupledShell {L : PeriodicLatticeExtent} (ell M c k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ PerCubeRegularShell ell M c k S α₀ η U

/-- Touching selector for `D1Lit.PlaqSel`. Not a `selIn`/`selAll` synonym. -/
def selCorner : PlaqSel := fun _ G => plaqCorner G.Om0

/-- Same quantifiers as `P428Target8` (`ZT5A.lean:291`) / `P428Target8S` (`D1Lit.lean:123`).
The class hypothesis is `ClassCoupledShell`, not `ClassCoupled`.
The form is `GenS.genFormS selCorner selCorner`, not `genForm` and not `selAll`. -/
def P428Target8Shell : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ →
          (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
          TorusOK ell (ell ^ m) Lu →
          ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
          ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
          ∀ (U : LinkCfg (scaleUp ell k Lu)),
            ClassCoupledShell ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
            InstIneqS (sD := selCorner) (sJ := selCorner) ell k (by omega) a Lu γ₀ S Lam U
```

`InstIneqS` is `D1Lit.lean:96`: the frozen inequality with `GenS.genFormS`, so \(\Delta\) and \(J\) run over `selCorner`. `P428Target8S selCorner selCorner` is a different statement: it keeps the frozen `ClassCoupled`. The old configuration gives negative raw touching Delta in that frozen class, but no refutation of this selector-specific headline has been established here: its gauge-fixed `genForm` still needs analysis.

Proper nonempty \(\Omega_0\) is not excluded. `CoversOm0p` is the frozen coverage predicate, already true for the NV slab (`slab3_coversp`, used by `D1Final.lean:141`). `PerCubeRegularShell` constrains \(U\), not the tower. The constant configuration \(U=1\) satisfies it with \(A=0\), for every \(\alpha_0>0\).

## Prediction

1. `plaqCorner(Ω)` is not `plaqIn(S)` for any site set \(S\), whenever \(\Omega\) is a proper block domain with a face large enough to hold a unit plaquette one step outside. The corners of `plaqCorner(Ω)` force \(S\) to contain the closed 1-neighborhood, and that neighborhood contains a face plaquette with no corner in \(\Omega\). Admissible towers cannot repair this: `Admissible` (`ZStatementP428.lean:73`) requires \(M\)-block unions, \(M=\ell^m\ge 2\), and a one-site shell is not an \(M\)-block layer. So the touching operators are not the frozen operators on another admissible tower.

2. The old configuration \(U_\theta\) (`D1Path.lean:46`) still makes the touching quadratic form negative for \(|\theta|>\pi/2\). On the outward bond the four plaquettes \(P_1,P_2\) (`D1Eval2.lean:65`) have two corners in the slab, so they lie in `plaqCorner` and not in `plaqIn`. `BdPt.delta_pi` (`D1Geo1.lean:94`) gives \(-4\) times the normalised Hilbert–Schmidt square at \(\theta=\pi\) for the all-plaquette sum; the same four plaquettes are the only ones that see that bond, so the touching sum equals the all-plaquette sum. `TouchBond` does not see the flux: \(U_\theta\) is nontrivial only on `Zb` (neither endpoint in \(\Omega_0\)), and a touching bond of a cube inside \(\Omega_0\) meets \(\Omega_0\). `ReadBond` does see that flux. Whether \(U_\theta\) lies in `ClassCoupledShell` is then the smallness test below, not a coverage collapse.

3. In the Cartan sector the transcribed form is \(Q(A)=\sum_p \cos\varphi_p\,(\mathrm{curl}\,A)_p^2\). It is negative only if some selected plaquette has \(|\varphi|>\pi/2\). After the gauge in (3.35), a bond phase of the diagonal representative obeys \(|\theta|<\ a_0/(\sqrt{2}\,\ell^j)\) and a parallel difference obeys \(|\Delta\theta|<\ a_0/(\sqrt{2}\,\ell^{2j})\), because `frobNorm(diag(1,-1))=\sqrt{2}` (`RMapLipschitz.lean:60`) and \(\eta\) cancels between \(U=\exp(i\eta A)\) and the printed powers of \((\ell^j\eta)^{-1}\). A plaquette angle is two such differences, so \(|\varphi|\le 2|\Delta\theta|\). At level \(j=0\), the prover may choose \(a_0\le \pi/(2\sqrt{2})\approx 1.111\) and then every shell-regular Cartan configuration has \(\cos\varphi\ge 0\) on every touching plaquette, hence \(Q\ge 0\). The old negative range \(|\theta|>\pi/2\) and the one-plaquette flux of angle \(\pi\) both need a larger cap. This is a model threshold for the \(\eta=1\) Cartan form of \(\Delta\), not a value of \(\gamma_0\) and not a theorem.

4. A counterexample is more likely than a rewriting, but only against the literal touching-bond class or against `P428Target8S selCorner selCorner` (frozen class, touching operators). Against `P428Target8Shell`, these numerics do not supply a counterexample inside every \(a_0>0\). They also do not suggest that the frozen theorem implies it. Raw non-abelian \(\Delta\) is already slightly indefinite for both `plaqCorner` and `plaqIn` at link size \(0.05\); that does not separate the two readings and does not touch `genForm`.

## Numerical method

Script: `AHP/fidelity/s1-touching/numerics/shell_touch.py`. Output: `AHP/fidelity/s1-touching/numerics/results.json`. Runtime 58 s, tori of side 4, 6 and 8, one Cartan component or three `su(2)` components. Numpy dense spectra. Not a Lean execution.

Transcribed operators, with the line they follow:

- plaquette holonomy `ClayStatement.lean:1286`, boundary edges `:1295`, shift `:1281`
- `curlValueCovariant` `CovariantOperators.lean:315`, `RMap` `:247` (\(UXU^{\mathsf H}\))
- `hsInner` `SuTwoInner.lean:104`, \(-\frac12\mathrm{Re}\,\mathrm{tr}(XY)\) on traceless skew-Hermitian matrices; witness `T_1=i\,\mathrm{diag}(1,-1)` at `CovariantOperators.lean:128`
- `reHolonomy`, `imHolonomy` `DeltaPrime.lean:125`, `:133`
- `bilPlaq_atoms` `DeltaPrimeOperator.lean:433` (raw trace, six imaginary brackets)
- the sum `hsInner(curl,curl)+\frac12 bilPlaq` as in `delta_form_sum` `D1Eval.lean:56`
- `U_θ` and `Zb` `D1Path.lean:46`, `:25`
- `plaqIn` `ZR2Ops2.lean:74` as "all four corners"

Unit check against the closed Cartan form \(Q=\mathrm{curl}^2\cos\varphi\): second brackets vanish on the Cartan; one plaquette with a unit field on one edge gives \(\cos\varphi\in\{1,0,-1,1/2\}\) at \(\varphi\in\{0,\pi/2,\pi,\pi/3\}\). `frobNorm(diag(1,-1))=\sqrt{2}` and `hsInner(T_1,T_1)=1`.

Global check against `BdPt.delta_pi`: slab \(x_0<W\), field on the outward bond at \(x_0=W-1\). Touching and all-plaquette Rayleigh quotients equal \(4\cos\theta\); the inside quotient is \(0\).

## Results

Rayleigh quotient of the outward bond, Cartan \(U_\theta\). The identity \(4\cos\theta\) holds on every tested slab, including side 8.

| torus | \(\theta=\pi\) touch / in / all | \(\theta=\pi/2\) touch | \(\theta=0\) touch |
|---|---|---|---|
| side 4, width 2 | \(-4\) / \(0\) / \(-4\) | \(0\) | \(4\) |
| side 6, width 2 | \(-4\) / \(0\) / \(-4\) | \(0\) | \(4\) |
| side 6, width 4 | \(-4\) / \(0\) / \(-4\) | \(0\) | \(4\) |
| side 8, width 2 | \(-4\) / \(0\) / \(-4\) | \(0\) | \(4\) |

Spectrum of the touching Cartan form at \(\theta=\pi\): minimum \(-10\) (side 4) and \(-10\) (side 6, width 2), with 64 and 144 negative eigenvalues. The inside form on the same \(U_\theta\) has minimum \(0\) up to \(10^{-14}\). At \(\theta=0\) the touching form is positive semidefinite (minimum \(0\), first positive eigenvalue about \(0.59\) on side 4).

Bond counts. `touch ∩ far = 0` on every geometry. `read ∩ far` is 64, 144, 144, 256, 72 on the five geometries below. So \(U_\theta\) changes no touching bond of \(\Omega_0\) and does change read-bonds.

Rewrite test. For each proper nonempty \(\Omega\), every site set \(S\) with `plaqIn(S)=plaqCorner(Ω)` would have to contain every corner of every touching plaquette, and that corner set already contains a face plaquette with no corner in \(\Omega\). Count of such face plaquettes found, at least one in each case:

| geometry | \(\|\Omega\|\) | touching plaquettes | inside plaquettes | face plaquettes outside `plaqCorner` but inside `plaqIn` of the forced corners | forced corners \(M=2\)-block-closed? |
|---|---|---|---|---|---|
| side 4, slab width 2 | 32 | 128 | 64 | yes (example base \((2,0,0)\), directions \(0,1\)) | yes |
| side 6, slab width 2 | 72 | 288 | 144 | yes (base \((2,0,0)\), directions \(1,2\)) | no |
| side 6, slab width 4 | 144 | 504 | 360 | yes | yes |
| side 8, slab width 2 | 128 | 512 | 256 | yes | no |
| side 8, aligned \(2\times2\times2\) cube | 8 | 54 | 6 | yes (base \((0,0,2)\)) | no |

Block closure of the forced corner set is not the obstruction. Equality of the plaquette sets already fails when the corner set happens to be a union of \(M=2\) blocks (side 4, width 2). On side 6, width 2, the one-site shell is not an \(M=2\) block union either, which is the separate `Admissible` obstruction.

Cartan search inside a cap \(|\theta|\le\theta_{\max}\) and \(|\Delta\theta|\le\theta_{\max}\).

- Cap \(\pi/2\) (phase cap corresponding to \(a_0=\pi/\sqrt{2}\approx 2.221\)): a one-plaquette flux with edge phases \(\pm\pi/4\), holonomy \(\pi\), parallel gap \(\pi/2\), sits in the cap. On the side-6 width-2 slab its curl test field has \(Q\approx -9.64\) and the touching spectrum has minimum \(\approx -2.94\) (one negative eigenvalue). Random phases on read-bonds, 8 trials, minimum eigenvalues from \(-6.65\) to \(-5.84\). The single-bond four-plaquette search reached sum of cosines \(-2.62\) (the geometry does not attain the formal \(-4\)).
- Cap \(\pi/4\) (phase cap corresponding to \(a_0=\pi/(2\sqrt{2})\approx 1.111\)): the same flux has parallel gap \(\pi/2\) and is outside the cap. Random read-bond phases, 6 trials at cap \(\pi/8\) and 6 at cap \(0.3\), all have minimum \(0\) up to \(10^{-14}\). The single-bond search at cap \(\pi/4\) stayed nonnegative (best sum of cosines \(0.34\); the two-difference bound gives \(4\cos(\pi/2)=0\)).

A row in `results.json` tagged `a0_equals_phase_cap` caps phases at \(1.111\), which is the number \(\pi/(2\sqrt{2})\) itself and not the phase cap \(a_0/\sqrt{2}\). It goes negative and is not the threshold test. The threshold test is the cap \(\pi/4\).

Non-abelian raw \(\Delta\) on the side-4 width-2 slab, links \(\exp(\varepsilon)\) with coefficients uniform in \([-\varepsilon,\varepsilon]\), seed 0, touching plaquettes, dimension 576:

| \(\varepsilon\) | minimum | negative eigenvalues |
|---|---|---|
| 0 | \(0\) (about \(-5\cdot 10^{-15}\)) | 0 |
| 0.05 | \(-0.223\) | 105 |
| 0.2 | \(-1.177\) | 121 |

The same seed at \(\varepsilon=0.05\), now with a flat divergence penalty of weight 1 (not Lean's \(RD^*\)): touching minimum \(-0.044\) (33 negative), inside (`plaqIn`) minimum \(-0.066\) (53 negative). The frozen plaquette set is at least as indefinite as the touching set. A negative raw \(\Delta\) at this size is therefore not a touching-only counterexample. The independently recorded decomposition in `numerics/attack_check.json` (produced by `attack_check.py`, not `shell_touch.py`) attributes the main-sequence minimum \(-0.2233\) to curl energy \(+0.0190\) and half-bilPlaq energy \(-0.2423\), with flat divergence energy \(4.350\). The fresh-seed-0 configuration instead has minimum \(-0.2573\), curl \(+0.0238\), half-bilPlaq \(-0.2811\), and flat divergence energy \(4.632\). These are recorded reviewer measurements, not measurements rerun by the decision pass. Weight-1 penalisation leaves a negative minimum for both selectors; it is not an exact projection eliminating all pure-gauge modes. No claim is made about `genForm`, `Ginv`, or `InstIneq`.

## What this does and does not decide

- Rewriting the touching operators as frozen `plaqIn` operators on an admissible tower: no, on these domains. The plaquette sets differ, and on the side-6 width-2 slab the forced shell is not \(M\)-block-closed.
- Old counterexamples against the touching **operators**: yes. Rayleigh \(-4\) at \(\theta=\pi\), agreeing with `BdPt.delta_pi`, on four tori. They do not inhabit `ClassCoupledShell` unless \(a_0\) is large enough for phase \(\pi\) (model bound \(a_0>\pi\sqrt{2}\approx 4.44\) at level 0). They do inhabit a `TouchBond`-only regularity clause.
- A new Cartan counterexample to raw touching \(\Delta\) inside a large shell cap: yes, the holonomy-\(\pi\) plaquette at edge phases \(\pm\pi/4\). The nonnegative conclusion at the gradient-constrained cap \(\pi/4\) is a Cartan-model analytic bound. Only the single-bond constrained search tests that regime numerically; no lattice-wide gradient-constrained sampler was run. The random caps \(\pi/8\) and \(0.3\) already force nonnegative weights by the pointwise phase bound alone.
- `P428Target8Shell` as a theorem or a refutation: not decided. A refutation of the whole statement must defeat its complete quantifier order, including arbitrarily small prover choices of \(a_0>0\), and must concern the gauge-fixed `genForm`, not just raw Delta. Neither requirement was tested. A literal selector-identification route to `P428Target8` would need equality of the plaquette sets, which fails on the tested domains. This does not exclude a subtler form identity, inequality, or analytic comparison.

A counterexample is more likely than a rewriting if the class is the literal touching-bond class. For the shell class actually proposed, rewriting is impossible and a refutation is not the present evidence; the statement is a new comparison, smaller in \(U\) and larger in the plaquette sum.

## Stage B plan

Compile only under `AHP/fidelity/s1-touching/lean/`, with `lake env lean`, after the cold build has produced oleans. Do not edit `lean/`, `paper/`, `notes/`, `expected/`, or the lakefile. `#print axioms` on every theorem. Expected axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`, `native_decide`, or `axiom`.

Imports:

- `ZStatementP428` for `CubeBond`, `Admissible`, `DescribedAt`, `IsClassCube`, `siteBox`, `BlockClosed`
- `ZR2A` for `PerCubeRegular2`, `CurlReads`, `CoversOm0c`, `ddA`, `curlA`
- `ZR6A` for `CoversPlaqOm0c`, `CoversOm0p`, `ClassCoupled`
- `ZR2Ops2` for `plaqIn`
- `AdalyFormal.Target.ClayStatement` for `periodicPlaquetteBoundaryEdges`, `periodicPlaquetteHolonomy`, `periodicLatticeShift`
- `D1Lit` for `PlaqSel`, `InstIneqS`, `selIn`, `selAll` (comparison only)
- `D1Path`, `D1Geo1` for `Uth`, `Zb`, `BdPt`, `delta_pi` if the \(U_\theta\) exclusion is formalised in the same environment

Targets, in order:

1. Definitions above, plus `CubeBond sites e → ReadBond sites e` when every direction has at least two sites. This is the inclusion `PerCubeRegularShell → PerCubeRegular2` and `ClassCoupledShell → ClassCoupled`.
2. `no_plaqIn_eq_plaqCorner`: if \(\Omega\) is a proper nonempty slab of width \(W\) with \(2\le W\le N-2\) on the period-\(N\) torus, no site set \(S\) satisfies `plaqIn S = plaqCorner Ω`. Proof shape: the face plaquette at \(x_0=W\) with directions \(1,2\) has all four corners in the forced 1-neighborhood and no corner in \(\Omega\). One concrete slab is enough; do not quantify over all subsets by search.
3. The selector-only statement `P428Target8S selCorner selCorner` is not the variant. Record, if the imports are cheap enough, that the four `BdPt` plaquettes lie in `plaqCorner` and not in `plaqIn`. Do not re-prove `not_P428Target8Literal`.
4. Do not prove `P428Target8Shell`. Do not claim it follows from `p428Target8`. A later proof would have to build `genForm` at `selCorner` under `PerCubeRegularShell` and is out of this comparison.

`#print axioms` names: `ClassCoupledShell.toFrozen` (or whatever the inclusion is called) and `no_plaqIn_eq_plaqCorner`.

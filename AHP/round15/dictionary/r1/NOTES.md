# Round 15 dictionary R1 — exact collar model and the remaining physical identification

## Verdict and audit boundary

**The constant-coefficient collar model is now explicit, and its dominant
reciprocal transfer pair is compiled.  The frozen right-star identification is
not yet proved in Lean.**  In particular, this round does not prove
`AreaSeedRightStar`, `CofinalUnitDominantAreaSeed`, P3, CofinalP3, or
`GoalNeg2`.

The main result is `AdalyFormal.Round15.Dictionary.collar_dictionary`.  It
contains all of the following, with no additional physical hypothesis:

* an explicit two-sided inverse of the displayed 16-by-16 companion matrix;
* the exact second-order recurrence for two independent sparse charged modes;
* the dominant eigenvalue `rho` and its reciprocal, each acting on both sparse
  modes.

The matrix is the reduced eight-transverse-component, two-sublattice companion
matrix identified from the frozen-family numerical operator at `q=1,R=20` and
transverse character `(1,0)`.  Its entries are Gaussian rationals.  No numerical
value is a Lean premise: Lean checks the displayed matrix, inverse, recurrence,
and eigenpairs directly.

## Compiled artifacts

| File | Role | Exit | Log status |
|---|---|---:|---|
| `AHP/round15/dictionary/r1/Collar.lean` | local main source | 0 | clean; all axiom records are `[propext, Classical.choice, Quot.sound]` |
| `AHP/round15/shared/dictionary/R1_Collar.lean` | byte-identical reusable publication | 0 | clean; all axiom records are `[propext, Classical.choice, Quot.sound]` |
| `AHP/round15/dictionary/r1/PhysicalGap.lean` | exact open physical predicate and the same model certificate | 0 | clean; all axiom records are permitted |
| `AHP/round15/shared/dictionary/R1_PhysicalGap.lean` | byte-identical reusable publication | 0 | clean; all axiom records are permitted |

All four files were compiled with

```sh
bb heavy run -- AHP/round3/lean1.sh AHP/round15/dictionary/r1/Collar.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/shared/dictionary/R1_Collar.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/dictionary/r1/PhysicalGap.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/shared/dictionary/R1_PhysicalGap.lean
```

There is no `sorry`, `admit`, new axiom, `native_decide`, `unsafe`,
`implemented_by`, `extern`, or `opaque`.  The only import is frozen `DrEquiv`.
No AHP file is imported as a Lean module, and neither `lake build` nor
`REPRODUCE.sh` was run.

The main declaration has the exact form

```lean
theorem collar_dictionary :
    (dominantTransfer * dominantTransferInverse = 1 ∧
      dominantTransferInverse * dominantTransfer = 1) ∧
    (Matrix.mulVec dominantTransfer (forward mode0) = (rho : ℂ) • forward mode0 ∧
      Matrix.mulVec dominantTransfer (forward mode1) = (rho : ℂ) • forward mode1 ∧
      Matrix.mulVec dominantTransfer (backward mode0) = (1/rho : ℂ) • backward mode0 ∧
      Matrix.mulVec dominantTransfer (backward mode1) = (1/rho : ℂ) • backward mode1) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode0 (n+2)) +
      Matrix.mulVec collarB (observation mode0 (n+1)) +
      Matrix.mulVec collarC (observation mode0 n) = 0) ∧
    (∀ n : ℕ, Matrix.mulVec collarA (observation mode1 (n+2)) +
      Matrix.mulVec collarB (observation mode1 (n+1)) +
      Matrix.mulVec collarC (observation mode1 n) = 0)
```

The auxiliary theorems are `transfer_inverse`, `dominant_recurrence`, and
`dominant_eigenpairs`.  The two matrix equalities in `transfer_inverse` are
literal two-sided inverse identities, not a determinant or spectral-gap
assertion.

## 1. Exact collar recurrence and dominant roots

Write the eight transverse components in the order used by the numerical
extraction: first the four internal cells of direction 1, then the four internal
cells of direction 2.  The cells are `(0,0),(1,0),(0,1),(1,1)`.  The four
longitudinal direction-0 coordinates are eliminated exactly.  The resulting
recurrence is

\[
  C\,v_{x-1}+B\,v_x+A\,v_{x+1}=0,
\]

where `A = collarA`, `B = collarB`, and `C = collarC` are the displayed Gaussian
rational matrices.  The numerical interface audit locates the constant block
region at `s+1 <= x <= hi-2`; at `q=1,R=20`, this is `213 <= x <= 250`.

The companion is

\[
  T(w_n,w_{n-1})=(w_{n+1},w_n),\qquad
  T^{-1}(w_{n+1},w_n)=(w_n,w_{n-1}),
\]

and `dominantTransferInverse` is displayed explicitly.  The inverse identity is
checked by Lean, not inferred from an eigenvalue calculation.

The dominant root is exactly

\[
  \rho=\frac{5-\sqrt2+\sqrt{23-10\sqrt2}}2
       =3.281001445410988081735482912278\ldots
\]

and `rho_quad` proves `rho^2 = (5-Real.sqrt 2)*rho-1`.  Its reciprocal is

\[
  \rho^{-1}=\frac{5-\sqrt2-\sqrt{23-10\sqrt2}}2
           =0.304784992215916869462828363512\ldots
\]

The phase is `phase = (1+Complex.I)/(Real.sqrt 2 : ℂ)`, with `phase^2 = Complex.I`.
The two independent sparse modes are `mode0 = [1,phase,1,phase,0,0,0,0]` and
`mode1 = [0,0,0,0,1,phase,1,phase]`.  Their adjacent-layer states are `forward`
and `backward`.

## 2. Other q=1 character factors

`factor_audit.py` checks all 16 characters against the displayed transfer
matrices.  The worst characteristic-polynomial relative discrepancy is
`1.06e-14`; every transfer determinant is numerically one to `1.4e-15`.  For
readability, put \(y=\lambda+\lambda^{-1}\).  The roots in each row are
\(\lambda_\pm(y)=(y\pm\sqrt{y^2-4})/2\), with the displayed multiplicities.

| Characters | `y` and multiplicities |
|---|---|
| `(0,0)` | `11` (2), `7` (4), `3` (2) |
| `(0,2),(2,0)` | `9` (4), `5` (4) |
| `(2,2)` | `7` (8) |
| `(0,1),(1,0),(0,3),(3,0)` | `5-√2` (2), `5+√2` (2), `9-√2` (2), `9+√2` (2) |
| `(1,1),(1,3),(3,1),(3,3)` | `7-2√2` (2), `7` (4), `7+2√2` (2) |
| `(1,2),(2,1),(2,3),(3,2)` | `7-√2` (4), `7+√2` (4) |

Thus the dominant class has four reciprocal pairs with `y=5±√2` and `y=9±√2`.
The pair relevant to the right-star top-row observable is `y=5-√2`, giving the
`rho` above.  The other three growing roots in that class are
`6.254324184971964608…`, `7.451586833933618872…`, and
`10.317288874877429663…`; their inverses are also included in the factor audit.

## 3. Numerical evidence, never a proof premise

All scripts use the existing `AHP/round6/probe/probe.py` frozen-family assembly.
They are non-interval numerical diagnostics only.

### Exact factor and rate audits

`FACTOR_AUDIT.json` records the character factors above and the exact dominant
rate

\[
  \rho^8=13429.238092478386528127955543581\ldots
\]

The power 8 is geometric, not an assumed Laurent recurrence: `R -> R+2` adds
four fine collar layers, and the mixed-colour area is quadratic in the carrier.
The retained right-star `areaSum` values give successive `rate * rho^8` of
`0.99999952, 0.99999988, 0.99999997, 0.999999993, 0.9999999983, 0.9999999996`
at `R=22,24,26,28,30,32`.  Normalizing by `rho^(4R)` gives
`0.0133612153, 0.0133612089, 0.0133612074, 0.0133612070, 0.0133612069,
0.0133612069`, converging toward the previously observed `0.0133612072` to
its displayed precision.  This is evidence for the dominant model, not an exact
leading-coefficient proof.

### Actual crossing-generator reconstruction

`crossing_mode_probe.py` reuses the completed structure-probe drive and checks
it against the completed sector area, without refitting a root.

* At `R=20`, the reconstructed sector `areaSum` agrees with the retained value
  to relative error `8.1e-17`; at `R=22`, to `5.2e-28`.
* The maximum deep-collar relative recurrence residual is `9.4e-16` at both
  radii.  The complete modal one-step relative errors are `2.86e-15` and
  `2.91e-15`.
* The two `rho` growing-mode coefficient norms are approximately
  `3.72e-20` and `3.09e-20`.  The other growing-mode coefficients are many
  orders smaller (`1e-31` to `1e-35`), so the `rho` branch dominates the actual
  crossing generator rather than merely being one possible mode.
* At `R=22`, the corresponding coefficient ratios agree with `rho^-4` to about
  `1e-14`.  The larger growing branches are also present only at much smaller
  numerical levels, and are not used as proof premises.

These results explain the failed same-row three-term fit: the observable is a
quadratic function of a two-sublattice matrix recurrence with interface rows,
not a scalar same-row recurrence.

### Interface rows

`interface_audit.py` gives `s=212,hi=252` at `q=1,R=20` and shows:

* the same `A,B,C` blocks hold for `x=213` through `x=250`;
* the interface row `x=212` has `K0` difference `0.0078125` and `Kminus`
  difference `0.015625` from the constant block;
* auxiliary augmented-system interactions remain at `x=210,211,212`, and the
  exterior-star modification appears at `x=251`.

Consequently an exact top-row leading coefficient must include the interface
and dressed-jet rows, not just the constant block.  Those interface identities
are still missing in Lean.

## 4. Exact physical statement still missing

The following is the precise remaining identification for the model proved in
this round.  It is compiled in `PhysicalGap.lean` and its byte-identical shared
publication.  The `Q1C10PhysicalDictionary` predicate is **defined but not
inhabited**.  The coordinate types are the actual physical ones: the
longitudinal coordinate is `Fin 256`, and both transverse coordinates are
`Fin 8` at `q=1,R=20`.

```lean
def physicalLayer (u : TwistSpace 1 20) (x : Fin (12*1*20+16)) : Fin 8 → ℂ :=
  fun i =>
    let d : Fin 3 := if i.val < 4 then 1 else 2
    let c : Fin 4 := if h : i.val < 4 then ⟨i.val, by omega⟩ else ⟨i.val-4, by omega⟩
    let yz : Fin 8 × Fin 8 := ![(0,0),(1,0),(0,1),(1,1)] c
    let site : PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) :=
      Function.update (Function.update (Function.update
        (rightSite (q := 1) (by norm_num) 20) 0 x) 1 yz.1) 2 yz.2
    (AdalyFormal.Round13.Detection.ColorArea.realPart (G 1 20) u (site,d) : ℂ) +
      (AdalyFormal.Round13.Detection.ColorArea.imagPart (G 1 20) u (site,d) : ℂ) * Complex.I

def Q1C10PhysicalDictionary : Prop :=
  ∀ u : TwistSpace 1 20,
    KernelLine 1 20 (rightStar (q := 1) (by norm_num) 20) u →
    ∀ x : Fin (12*1*20+16), 213 ≤ x.val → x.val ≤ 250 →
      Matrix.mulVec collarC (physicalLayer u (x-1)) +
        Matrix.mulVec collarB (physicalLayer u x) +
        Matrix.mulVec collarA (physicalLayer u (x+1)) = 0
```

This is the missing exact dictionary between the actual frozen carrier and the
compiled model.  It has not been proved.  In particular, the current Lean file
does not assert that `collarA`, `collarB`, `collarC`, or `dominantTransfer` is
definitionally equal to a frozen operator.

The interface/dressed-jet identification needed to turn this into an exact
same-generator top-row `areaSum` formula is also still open.  A later round
must additionally prove the actual leading constant nonzero, including the
interface, rather than infer it from the numerical normalized value.

## 5. Original goal statements remain open

The preferred per-instance seed is still exactly

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
    ∃ j : ℕ, ∃ hj : j < blockCount q R, areaSum hq hj u ≠ 0
```

The preferred cofinal normalized alternative is still exactly

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∃ observable : ℕ → ℕ → ℝ,
  RadiusDominantData observable (2^j) ∧
  ∀ n : ℕ, ∃ u : TwistSpace (2^j) (2*(n+9)),
    KernelLine (2^j) (2*(n+9)) (rightStar (by positivity) (2*(n+9))) u ∧
    ‖u‖ = 1 ∧
    ∃ k : ℕ, ∃ hk : k < blockCount (2^j) (2*(n+9)),
      areaSum (by positivity : 0 < 2^j) hk u = observable (2^j) (2*(n+9))
```

where

```lean
def RadiusDominantData (observable : ℕ → ℕ → ℝ) (q : ℕ) : Prop :=
  ∃ r K : ℝ, 0 < r ∧ K ≠ 0 ∧
    Tendsto (fun n => observable q (2*(n+9)) / r^n) atTop (𝓝 K)
```

No inhabitant of either physical seed is supplied.  The compiled
`collar_dictionary` is an exact model certificate, not an unconditional proof
of the frozen physical goal.

## 6. Reproduction and scope

```sh
python3 AHP/round15/dictionary/r1/inspect_full.py --q 1 --R 20 --iy 1 --iz 0 --x 220 --dps 50
python3 AHP/round15/dictionary/r1/interface_audit.py --q 1 --R 20 --iy 1 --iz 0 --dps 50
python3 AHP/round15/dictionary/r1/crossing_mode_probe.py --q 1 --R 20 --iy 1 --iz 0 --dps 50
python3 AHP/round15/dictionary/r1/crossing_mode_probe.py --q 1 --R 22 --iy 1 --iz 0 --dps 40
python3 AHP/round15/dictionary/r1/factor_audit.py
python3 AHP/round15/dictionary/r1/build_lean.py
python3 AHP/round15/dictionary/r1/build_physical_gap.py
bb heavy run -- AHP/round3/lean1.sh AHP/round15/dictionary/r1/Collar.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/shared/dictionary/R1_Collar.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/dictionary/r1/PhysicalGap.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round15/shared/dictionary/R1_PhysicalGap.lean
python3 AHP/round15/dictionary/r1/audit.py
```

Writes are confined to `AHP/round15/dictionary/r1/` and
`AHP/round15/shared/dictionary/`.  Earlier rounds, frozen modules, the lakefile,
the integration checkout, and git history were not changed.  No git commit or
push was made.

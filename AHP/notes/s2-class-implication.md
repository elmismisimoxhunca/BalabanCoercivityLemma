# S-2 — class implication

Uncompiled draft: [ClassImplication.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s2-class-implication/ClassImplication.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited. The scout returned nothing; this is not a blocked item.

## What the draft states

`CubeBond` is both endpoints (`ZStatementP428`). `TouchBond` is one endpoint.

`ClassCoupled` is `CoversOm0p ∧ PerCubeRegular2` (`ZR6A`).

- `CoversOm0c` quantifies sites of `Ω₀`. It does not mention `CubeBond`. The touching classes keep it.
- `CoversPlaqOm0c` uses `CubeBond` twice. The antecedent is `plaqIn` (`cubeAnte_iff_plaqIn`: all four boundary bonds have both endpoints in `Ω₀`). The consequent asks for `CubeBond` of one `IsClassCube`. `CoversPlaqTouch` replaces both occurrences by `TouchBond`. That makes the antecedent larger and the consequent weaker, so it is not a substitution of a stronger bond predicate.
- `PerCubeRegular2` uses `CubeBond` only as a hypothesis of the bounds (value, forward difference, and `CurlReads`). `PerCubeRegularTouch` widens those hypotheses to `TouchBond` / `CurlReadsTouch`. `PerCubeRegularTouch.toFrozen` drops back to `CubeBond` by `CubeBond.toTouch`. No geometry.

`ClassCoupledTouch` is `CoversOm0c ∧ CoversPlaqTouch ∧ PerCubeRegularTouch`. The draft gives it the type `ClassCoupledTouch → ClassCoupled` (`ClassCoupledTouch.toFrozen`). The coverage half is `CoversPlaqTouch.toFrozen`: a class cube is a `siteBox` (`DescribedAt`), and a product set that meets every edge of a unit square contains all four corners (`touchCover_cubeBond`), so the touching witness is a `CubeBond` witness.

`ClassCoupledCorner` uses `CoversPlaqCorner` instead: every plaquette with at least one corner in `Ω₀` has all four bonds `TouchBond` of one class cube. That antecedent is not the `TouchBond` rewrite of `CoversPlaqOm0c` (a one-corner plaquette need not meet `Ω₀` on all four bonds). `CoversPlaqCorner.toTouch` lands in `CoversPlaqTouch`, so `ClassCoupledCorner → ClassCoupledTouch → ClassCoupled`.

## Headline

`P428Target8Touch` is `P428Target8` with `ClassCoupled` replaced by `ClassCoupledTouch` and with the same `InstIneq` conclusion. `P428Target8Corner` uses `ClassCoupledCorner`. The draft gives

`P428Target8 → P428Target8Touch → P428Target8Corner`

(`targetTouch_of_frozen`, `targetCorner_of_touch`). Quantifiers, `SidePow6`, factor `12`, smallness `(12 : ℝ) * M * α₀ ≤ a₀`, `TorusOK`, `Admissible`, and `LambdaOK2` are the frozen ones. `Λ` stays `OnLambdaT` / `CRowIn` / `OnLambdaTildeIn`.

`InstIneq` still uses the frozen `plaqIn` operators. The draft does not claim those operators equal a one-corner sum, and it does not mention `not_P428Target8Literal` or `not_P428Target8LiteralBoth`.

The converse inclusions are not stated. Nothing here says either touching class is inhabited on a proper nonempty `Ω₀`. The S-1 saturation argument for `CoversPlaqCorner` is not re-proved in this file.

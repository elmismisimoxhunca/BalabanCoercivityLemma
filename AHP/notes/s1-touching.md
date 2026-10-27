# S-1 — consistent touching reading

Uncompiled draft: [Touching.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s1-touching/Touching.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Statement-sheet rows 5 and 7 were not edited and stay open until a rebuild.

## Decision

On the towers the consistent reading actually quantifies over, the one-corner operators and the frozen `plaqIn` operators are the same set of plaquettes, and the touching class implies the frozen `ClassCoupled`. The frozen `InstIneq` is then the touching-operator inequality. The draft is the implication `touching_of_frozen : P428Target8 → P428Target8Touching`.

This is agreement on the relevant fields, not a new analytic estimate. It is not a claim that `not_P428Target8Literal` or `not_P428Target8LiteralBoth` are false.

## What “touching” is in the draft

CMP 102 p.277: a domain is the bonds with at least one endpoint in it, and the plaquettes with at least one corner in it.

- `TouchBond`: one endpoint in the set. `CubeBond` (both endpoints) implies it.
- `plaqCorner`: one of the four corners in the set. `plaqIn` is all four.
- `PerCubeRegularTouch`: `PerCubeRegular2` with `TouchBond` and `CurlReadsTouch`.
- `CoversPlaqCorner`: every `plaqCorner` plaquette of `Ω₀` has all four bonds `TouchBond` of one `IsClassCube`.
- `ClassCoupledTouch`: frozen `CoversOm0c` (sites; no bond convention), `CoversPlaqCorner`, and `PerCubeRegularTouch`.
- `Λ` is not changed. The frozen statement already uses `OnLambdaT`, `OnLambdaTildeIn` and `CRowIn` (`ZT5A` header (3), `ZR2A.OnLambdaT`, `ZStatementP428.CRowIn`). `bondsOm0` is already one endpoint (`ZXR2Ops3`).

`P428Target8Touching` has the frozen quantifiers (`ell ≥ 2`, `a > 0`, then `m₀`, `R₀`, then `a₀`, `γ₀`, then `k ≥ 1`). The conclusion at each `(S, Λ, U)` in `ClassCoupledTouch` is

`plaqCorner (S.Om 0) = plaqIn (S.Om 0)` and the frozen `InstIneq`.

`deltaKLocCLM_congr` and `JSU2Loc_congr` turn that set equality into equality of the localised `Δ` and `J`. The draft does not push the equality through `Classical.choose` in `G1invS`; the stated conclusion is the frozen inequality plus the set equality.

## Why the sets agree only after coverage

`CoversPlaqCorner`, `Admissible` and `M ≥ 2` (`M = ell^m`, `m ≥ 1`, `ell ≥ 2`) force `Ω₀ = ∅` or `Ω₀` the whole fine torus (`saturated_of_coversCorner`). On those two sets, `plaqCorner = plaqIn`.

A nonempty proper `BlockClosed M` set has an exit edge (`exists_exit`). From that edge the draft builds a unit plaquette with one corner in `Ω₀` and one boundary bond in `NoEnd` (both endpoints outside). A class cube’s sites lie in `Ω₀` (`class_sites_subset_om0`, from `DescribedAt` and `admissible_mono`), so that bond is not a `TouchBond` of any class cube. Hence `¬ CoversPlaqCorner` (`not_CoversPlaqCorner_of_proper`). The same plaquette is in `plaqCorner \ plaqIn` (`corner_differs_on_proper`).

The rectangle step: a `siteBox` is a product of coordinate arcs. A vertex cover of a unit square by a product set contains an opposite pair of corners, and the product then contains all four. So touch-covering a plaquette by a class cube implies `CubeBond` on all four bonds (`touchCover_cubeBond`). Therefore `CoversPlaqCorner → CoversPlaqOm0c`, and `PerCubeRegularTouch → PerCubeRegular2`, so `ClassCoupledTouch → ClassCoupled` (`ClassCoupledTouch.toFrozen`). That inclusion is part of this draft only. It is not a compiled S-2 theorem.

## Why the known counterexamples do not inhabit this class

`not_P428Target8Literal` and `not_P428Target8LiteralBoth` (`D1Final`, `D2Final`) use the frozen `ClassCoupled` on `SlabNv`, with `U_θ` equal to `diag(e^{iθ}, e^{-iθ})` on `Zb` (no endpoint in `Ω₀`) and `1` elsewhere (`D1Path.Uth`). `BdPt.delta_pi` gets `-4 ‖X‖²` from the four plaquettes `P1`, `P2` on the outward bond. Those plaquettes have two corners in `Ω₀`, so they lie in `plaqCorner`, and one bond of each lies in `Zb`, so they do not lie in `plaqIn`.

`U_θ = 1` on every bond that meets `Ω₀`, so widening `CubeBond` to `TouchBond` does not throw `U_θ` out of the regularity clause. What throws the slab out is `CoversPlaqCorner`: the slab’s `Ω₀` is a nonempty proper block union (`SlabNv_bdpt`), so the coverage conjunct is false. The literal refutations remain refutations of touching operators against the both-endpoint class. They are not refutations of operators and class together.

## What was not done

No `lean`, `lake`, or axiom print. Frozen files were not edited. Rows 5 and 7 of `notes/statement_sheet.tex` stay open. The draft’s proofs are not checked by a compiler; a failed elaboration would leave the comparison unproved.

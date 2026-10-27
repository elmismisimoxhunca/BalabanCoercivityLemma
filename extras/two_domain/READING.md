# READING.md -- the two-domain reading of CMP99b pp.394/396 and which Lean statement carries which (lane `two_domain_20261019`)

## 1. Sources, verbatim (page images opened and read in this lane)

Images (400 dpi crops saved by lane `r_bridge_20261019`, re-opened here): `compute/r_bridge_20261019/images/CMP99b_p394-06_crop.png`, `compute/r_bridge_20261019/images/CMP99b_p396-08_crop.png`.
The print's sign is `\leqq`, written `≦`.

| # | Page | Verbatim (read at the image) |
|---|---|---|
| P1 | p.394, para. after (3.24), line 2 | "The operator `Δ_U^η ↾ Ω_0` is the covariant Laplace operator with Dirichlet boundary conditions on `Ω_0^c`." |
| P2 | same para. | "Let us introduce a domain `Ω_0` such that `Ω_1 ⊂ Ω_0` and `Ω_0` is a union of big blocks of the lattice `T_1`, e.g. we may take `Ω_0 = {a union of big blocks in T_1, with distances to Ω_1 ≦ RM}`, or we may add to `Ω_1` a thinner layer of the big blocks surrounding `Ω_1`. For such `Ω_0` we consider the operator `Δ'_a` with Dirichlet boundary conditions on `∂Ω_0`, i.e. the operator `Δ'_a ↾ Ω_0 = Ω_0 Δ'_a Ω_0`." |
| P3 | same para. | "The operators with the boundary conditions have a very important property. They depend on the configuration `U` restricted to `Ω_0`." |
| P4 | p.396, top of the crop | "such that `□ ⊂ B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1})`, `□ ∩ B^j(Λ_j) ≠ ∅`, and `□` is a union of several big blocks of the lattice `T_{L^{-j}}`, which implies that its size in the lattice `T_η` is `O(1)ML^jη`. Here `O(1)` will mean a number `≧ 10`. The set `Λ_0` in the above condition means `Λ_0 = Ω_0 \ Ω_1`, where `Ω_0 = {a union of big blocks of the lattice T_1, such that their distances to Ω_1 are ≦ RM}`." |
| P5 | p.396, after (3.36) | "Let us notice that these regularity conditions do not impose any constraints on `U` outside the domain `Ω_0`." |

Reading facts (not judgements).  P2 states the OPERATOR domain `Ω_0` for any union of big blocks containing `Ω_1` ("e.g." the `≦ RM` layer, or "a thinner layer").  P4 defines the stratum `Λ_0 = Ω_0 \ Ω_1` of the cube
class of (3.35)/(3.36) by the same letter `Ω_0` together with the explicit `≦ RM` description.  The print uses one symbol in both places; it does not say, in these sentences, which of the two sets is meant
when they differ.  Both readings are Lean statements here: one domain (the repository's `thin_layer_20261019`, `AdmSplitNB`, class read from the same tower) and two domains (this lane).

## 2. The two-domain statement (what the Lean objects are)

* `S` (type `Tower`) is the OPERATOR tower: `S.Om 0 = Ω_0^op` is ANY union of `M`-blocks with the strict level-0 collar `R_0 M` (`AdmSplitNB`, lane thin_layer; no base law, no upper bound).  Everything the conclusion `InstAtWD ... S Lam U` reads
  (`gparams`, `plaqIn (S.Om 0)`, `siteMask`) comes from `S`.
* `Sc` (type `Tower`) is the CLASS tower: `Sc.Om 0 = Ω_0^cl`.  Hypotheses on `Sc`: `Sc.Om j = S.Om j` for `j >= 1`; `S.Om 0 ⊆ Sc.Om 0`.  Nothing else: `Sc` need not be admissible, block-closed or radial.  The class hypothesis
  (`ClassCoupledP Cl`, `ClassCoupledCap`, `ClassCoupled c`, `ClassCoupledΦ`) is read from `Sc`: the cubes (`B^0 = Sc.Om 0 \ Sc.Om 1`), the coverage of the sites and plaquettes of `Sc.Om 0`, the regularity.
* The "≦ RM layer" of P4 is the special case `Admissible ell M Rc k Sc` (any `Rc`); it is covered because the statements do not use admissibility of `Sc`.  `twodom_instance_inequality` instantiates it:
  `S` = slab at level-0 radius `R` (`AdmSplitNB`, thin), `Sc` = the same slab geometry at radius `Rb > R` (`Admissible ell M Rb 2 Sc`), `S.Om 0 ⊊ Sc.Om 0`; `twodom_union_instance_inequality` takes the union-class family hypothesis at the same towers and the same curved `U`, with the family containing the cut-missing cube of `plain_cut_fails`.

Lean carriers: `famTwoDom_union` (printed class: unions of big blocks, boxes included), `famTwoDom_box` (grid-aligned boxes `z + f M ell^j`), `famTwoDom_cap` (p.408 level-0 boxes, regularity on `cube ∩ Om0`),
`mixedTwoDom`, `totalTwoDom`, `target8TwoDom` (the frozen `P428Target8` with `InstIneq`, one radius `R`).

## 3. The three checks the owner asked for (facts)

1. **Meeting clause.**  For a connected cube (a box) the cut `C ∩ Ω_0^op` of a level-0 cube of `Sc` meets `B^0(S)` whenever it is nonempty (`path_exists_T`, a unit-step path leaves `Ω_1` inside `Ω_0^op` because of the collar).  For a DISCONNECTED union
   of blocks it can fail: `plain_cut_fails` (TD6) is an explicit slab example in which `C` is an `IsClassUnion` of index 0 for `Sc` (one `M`-slab inside `B^1`, one inside `B^0(Sc) \ Om0(S)`), `C ∩ S.Om 0` is the first slab, it is
   nonempty, lies inside `S.Om 1`, and is NOT a `UnionAt` of index 0 for `S`.  So the naive reduction `C ↦ C ∩ Ω_0^op` fails for unions.  `cover_cut` (TD2) repairs it: when the cut misses `B^0(S)`, `far_block_exists` (TD1) gives an
   `M`-block `E ⊆ B^0(S)` at `l^1`-distance `>= 4` from `S.Om 1` (discrete intermediate-value argument along unit steps; uses the level-0 collar with `R_0 >= 4`); `E` is regular because the coverage hypothesis of `Sc` covers a site of `E`
   by a regular `Sc`-class union that contains the whole `M`-block; `regBody_glue` (TD1) glues the regular pieces (single gauge, single `A`; no bond, curl or second-difference stencil connects pieces at distance `>= 4`).
2. **Level-0 collar of the `Ω_0^op` tower.**  Unchanged from lane thin_layer: the headline threshold `R_1(ell, a)` binds `R_0`; below it nothing is claimed.  The union form takes `max R_1 4` (the far block needs `3M+1 <= R_0 M`); the box, cap, mixed, total
   and frozen forms keep `R_1`.
3. **Plaquette coverage after cutting.**  A plaquette `p` all of whose boundary bonds have both endpoints in `Ω_0^op` is covered in `Sc` by a cube `C` (`CubeBond C e`, both endpoints in `C`); the cut `C ∩ Ω_0^op` (or the glued `Q ⊇` cut) has
   `CubeBond` on the same bonds because the endpoints are also in `Ω_0^op` (hypothesis on `p`).  The bond convention (both endpoints) is the repository's, inherited unchanged.

## 4. Inherited conventions (not changed here)
3 dimensions; aligned half-open site blocks; periodic `l^1` distance `pdist`; `T_1` = the fine lattice at unit spacing (reading A of lane r_bridge); `CubeBond` = both endpoints (CMP96 p.224 uses "at least one endpoint"; this is a pre-existing source-identification
issue of the repository, not touched).  `R_1` is existential (not an explicit value).

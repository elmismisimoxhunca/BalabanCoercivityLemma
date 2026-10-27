# S-1, round 1, refutation attempt

## Result

**closedGoal: `none`.** No proof of `Round2.S1.GoalNeg1`, `GoalNeg2`, or `GoalNeg3` was found. No weakened negative proposition was substituted.

Final file: `AHP/round2/s1-touching/r1-refute/Attempt.lean`.

Furthest compiled partial result:

**`Round2.S1.corner_instIneq_iff_frozen` — Attempt.lean:492.**

For any tower with nested domains and the **pinned common-cube corner coverage**, the actual corner-selector `InstIneqS` is equivalent to frozen `InstIneq`, for all its other displayed parameters and every configuration. This comparison includes the full form, J, the chosen corrected inverse, the genuine jets and C, and the totalised inverse convention. It is not merely a raw-Delta comparison, not a flat-field restriction, and requires no invertibility premise. It does **not** assert a headline or either direction of a class inclusion.

The primary refutation route therefore stops at an exact operator identification, not at an unexplained numerical positivity observation. The shell fallback does not have this coverage hypothesis and is not covered by this comparison.

## Pinned statements and fidelity

All 22 pinned definitions and goal wrappers were copied verbatim, together with their namespace and variable context, from `../pin/Statement.lean`. The complete declaration block between `namespace Round2.S1` and the checking commands is byte-identical. No AHP module is imported.

The product-box helper block from `AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean`, from `TouchBond.endpoints` through `touchCover_cubeBond`, was also copied verbatim. Its four corner definitions were not changed. Only frozen modules are imported: `ZStatementP428`, `ZR2A`, `ZR6A`, `ZR2Ops2`, `D1Lit`, `D1Final`, `ZR8Class`.

All print departures remain those recorded in `../pin/PIN.md`. Especially important here:

- Requiring each corner-selected plaquette's four edges to touch **one common frozen class box** is additional coverage, not the CMP102 endpoint/corner convention alone.
- Product boxes contained in the tower's strata are material to the geometric lemma. They were not replaced with arbitrary unions or boxes outside Omega0.
- The primary class is not the Stage-B shell class. The latter retains frozen coverage and imposes stronger-than-printed ReadBond regularity.
- This attempt neither refutes Balaban's printed theorem nor establishes printed-statement fidelity.

## Numerical search, performed before the Lean proofs

Files: `search.py`, `search.json`, `search.log`, `search.exit` (exit 0).

The script cites the frozen Lean file and line for every modelled operator and the pin lines for its selectors. It uses only numpy and the Python standard library, sets a **3 GiB virtual-memory hard limit**, and was run through the heavy wrapper with one BLAS thread. It never implements a substitute for `genForm`, Q, J, W, or any inverse. Results are evidence only.

### 1. Coverage search

On the side-4 torus, enumerate all **256** unions of the eight aligned side-2 blocks. Relax the class cubes to every periodic product cube of every side 1 through 4 contained in the domain; ignore the actual class's factor, alignment, stratum and unique-index restrictions. Thus this is a larger covering family, not an actual admissible-tower enumeration.

For **49,152** box/plaquette pairs, four touching edges always forced all four corners into the box. Under the relaxed corner coverage, only block masks **0 and 255**, the empty and whole domains, passed. No proper nonempty candidate for negating the collapse obligation emerged. This finite enumeration alone is not a proof of `TouchCoverageCollapse`.

### 2. Large phases on invisible bonds

Test slabs `(side,width) = (4,2), (6,2), (8,2), (16,8)` and the genuine `Uth` pattern: identity on touching bonds, diagonal phase theta on bonds having neither endpoint in Omega0.

The outward unit Cartan bond reproduced

\[
Q_{\mathrm{corner}} = 4\cos\theta,
\]

including **-4 at theta = pi** and zero to rounding at pi/2. The counts of read-bonds outside the touching bond set were **64, 144, 256, 1024**, respectively. The opposite direction-1 bond at the outward face has neither endpoint in the slab, while its plaquette is corner-selected. No class cube contained in Omega0 can touch this edge. Thus this mechanism violates primary corner coverage for **every theta**, including zero; it is not an in-class counterexample.

This geometric exclusion was then formalised for the actual cofinal NV slab family, not just the small numerical tori.

### 3. Small-phase Cartan search

For sides 4 and 16, four trials at each of

\[
a_0\in\{\pi/(2\sqrt2),\ 0.1,\ 0.01\},\qquad \ell=k=2,
\]

scale a random diagonal phase field until all three global scalar analogues of the regularity bounds, evaluated at the most restrictive index j=2, have maximum ratio **0.9** to their bounds. This checks pointwise phases, forward differences, and the actual exterior curl-of-curl stencil, not a componentwise Laplacian. In particular the eta factors cancel when the phase field is converted to the Hermitian logarithm. This is stronger numerical regularity control than checking only a pointwise phase cap.

All sampled plaquette cosines were positive; the smallest was about **0.9999898614**. Random-test Rayleigh quotients were positive for the all, corner and inside selectors. Side-4 corner matrices were also diagonalised: the lowest recorded eigenvalue was about **-5.19e-15**, inside the stated numerical-zero tolerance 1e-10. No small-phase Cartan raw-Delta candidate emerged.

These trials do not certify class membership, admissibility, Lambda, or the headline thresholds. The side-4 experiments are outside depth-two headline geometry; side 16 is not thereby an actual tower witness either. The whole-torus selector and slab selectors were tested on the same globally regular numerical phase fields. Raw non-Abelian negativity was already recorded in Stage A for both frozen and corner selectors; it is not a separating mechanism and was not relabelled as a full-form counterexample here.

## Compiled partial results

All names below are in `Round2.S1`.

| Declaration | Line | Exact scope |
|---|---:|---|
| `cornerCoverage_no_unseen_read_bond` | 446 | Under nesting and pinned coverage, every bond read by a corner-selected plaquette touches Omega0. This immediately obstructs the invisible-exterior-edge strategy. |
| `cornerCoverage_selector_eq` | 460 | Under the same assumptions, `plaqCorner (S.Om 0) = plaqIn (S.Om 0)`. Uses the common product-box witness and the copied Stage-B vertex-cover argument. |
| `genForm_corner_eq_frozen` | 481 | For any genuine `IngrBParams`, equality of the selected plaquette sets at its geometry yields equality of the complete actual forms. The proof unfolds the selector-dependent chain and uses frozen `pin_genForm`. |
| **`corner_instIneq_iff_frozen`** | **492** | The full instance inequality equivalence under nesting and corner coverage; main partial result. |
| `bdpt_not_cornerCoverage` | 508 | Any frozen `BdPt` slab-boundary witness contradicts pinned corner coverage on a nested tower. |
| `old_slab_family_excluded` | 526 | For **every ell >= 2, positive M divisible by ell, R >= 18, arbitrary alpha, eta and U**, the actual `SlabNv ell M R` fails `ClassCoupledCorner ell M 12 2`. This excludes the old headline-refutation family uniformly over configurations and caps. |

The last theorem uses frozen `SlabNv_bdpt`, `slabGeo_inst`, `scaleUp_nv`, and `slab3_admissible`. It is not a theorem that the frozen or shell class is empty: those are different classes.

The equality result does not contradict Stage B's selector nonrepresentability on a proper slab. That slab fails the newly pinned corner-coverage hypothesis. No claim is made that corner selectors generally equal inside selectors.

## Why each negative goal remains unclosed

- **GoalNeg1:** the hidden-bond family is formally outside the pinned class; on any tower with the pinned coverage, the entire instance form reduces to the frozen form. A negative headline would still need an explicit in-class configuration and a supported nonzero test field defeating every candidate threshold and cap. None was supplied. The new equality can instead be used by a positive worker with the Stage-B class inclusion and frozen theorem; that headline derivation is not compiled here.
- **GoalNeg2:** no counterexample to the collapse/equivalence package was found. The finite search supports collapse, and the compiled selector equality supports the operator part of a positive reduction. This file does not prove universal shift-connectivity collapse or the headline equivalence package.
- **GoalNeg3:** shell coverage is only frozen coverage, so the primary equality/exclusion theorems cannot be applied to it. No failure of the actual shell `InstIneqS`, with all regularity clauses and cofinal threshold quantifiers, was found. The old large-phase path and the new raw-Cartan scans do not satisfy that obligation. Bounding diagonal phases in one gauge also does not by itself exclude every possible shell gauge representation.

## Validation and commands

Final serial compilation:

```sh
export PATH=$HOME/.elan/bin:$PATH
cd /home/sebastian/BalabanCoercivityLemma/lean
"$BB_CLI" heavy run -- lake env lean ../AHP/round2/s1-touching/r1-refute/Attempt.lean > ../AHP/round2/s1-touching/r1-refute/Attempt.lean.log 2>&1
echo $? > ../AHP/round2/s1-touching/r1-refute/Attempt.lean.exit
```

Final numerical rerun, from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 "$BB_CLI" heavy run -- python3 AHP/round2/s1-touching/r1-refute/search.py > AHP/round2/s1-touching/r1-refute/search.log 2>&1
echo $? > AHP/round2/s1-touching/r1-refute/search.exit
```

Final audit: both exit codes **0**; no Lean errors or warnings; all **47 local declarations** have dependency prints; **56 total dependency records**, including explicitly printed imported helpers, contain only `propext`, `Classical.choice`, `Quot.sound` (or no dependencies). The raw forbidden-token scan has zero hits. All pinned declarations and the copied geometric helper block are byte-identical to their sources.

Main line:

```text
'Round2.S1.corner_instIneq_iff_frozen' depends on axioms: [propext, Classical.choice, Quot.sound]
```

SHA-256:

- `Attempt.lean`: `d0ad2c5d323199275db34f7c0df294d81aae1b41d8b0de7fa450a98965100386`
- `Attempt.lean.log`: `ee82326a344546c6962e68bea4928301e4faa30e3d47060e0e1507462cf3081c`
- `search.py`: `bc296a5ce4356fe4895c6d18882fba996e538dd28f47903cab8d32526081708e`
- `search.json`: `a976b34e3a263c8bf1267b1b559138a5ffb63477250fb2fc3e31faf257c0e16e`

Only `AHP/round2/s1-touching/r1-refute/` was written. No build, reproduction, lake update, removal, git commit or push was run. The pre-existing tracked change to `lean/lakefile.toml` was left untouched. This worker has no durable goal of its own; no parent goal was changed.

# S-4 — odd L, the sites-only cell

Uncompiled draft: [OddSites.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s4-odd-sites/OddSites.lean). Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen files were not edited.

The odd-`ell` sites-only body is not decided. It is not called true and not called false.

## What was asked

`paper/OPEN_ITEMS.md` item S-4 quotes Balaban, CMP 109 p.251, as verified on the page image on 2026-10-20: \(L\) is an odd positive integer \(> 11\). This session did not reopen that image. The quote is used only as recorded there.

`FamilyTorusSitesConstAt` (`lean/src/CaT2d.lean`) keeps `CovSitesF` and `PerCubeRegularF` and drops plaquette coverage. The committed table says it fails for `ell = 2`, and for even `ell ≥ 4` with `ell ∣ 2(c-1)` and `9 ell ≤ 2(c-1)`. It is undecided for the other even rows and for every odd `ell ≥ 3`. Those odd values include every `L` in the CMP 109 sentence.

## Obstruction

The even negation does not apply to any odd `ell`, including every odd `ell > 11`. The arithmetic window in which that negation lives is nevertheless nonempty there. Site coverage still does not imply plaquette coverage on the decoupled tower. What fails is the exact block-sum cancellation the even estimate uses.

| Piece | Odd `ell` |
|---|---|
| `2 ∣ ell`, required by `not_familyTorusSitesConstAt_S`, `main_neg_S`, `wellDefG_punctured`, `H0_bij_path` | False. `not_two_dvd_of_odd`. |
| `ell ∣ 2(c-1)`, `9 ell ≤ 2(c-1)`, `c ≥ 10`, `w ≥ 10` | Inhabited. `c = 9 ell + 1`, `w = 19`. `odd_arith_window`, and `balaban_odd_window` for `ell > 11`. |
| `CovSitesF ∧ ¬ CovPlaqF` on `neS` under `SoRel` | Already in `sites_not_imp_plaq_S` (`SoA3.lean`), no even hypothesis. Not re-proved. |
| Both `ell × ell` block sums zero, steps in `{+d,-d}`, `d ≠ 0` | Impossible. `no_const_step_blockzero_odd`. |
| One homogeneous `τ ≠ 0` with `τ S_q ∈ 2 π ell² ℤ` | Exists whenever the sums are not both zero. Not a gauge theorem. |

`balaban_odd_window` is the S-4 range. For `ell = 13`, the witness is `c = 118`, `w = 19`: `2(c-1) = 234 = 18 · 13` and `9 · 13 = 117 ≤ 234`. Same shape for every larger odd `ell`. No tower is constructed.

## Where the even proof uses evenness

`not_familyTorusSitesConstAt_S` (`SoA1.lean`) assumes `hE : 2 ∣ ell` and calls `main_neg_S` (`SoM3.lean`), which assumes the same and calls `wellDefG_punctured` (`SoU2.lean`). That lemma assumes `hE` and uses `dsP_analytic`. `H0_bij_path` in the same file assumes `hE` and calls `nested_z0Setup_S` and `unit_temporal_stag0`, the zero-angle temporal background. That is the block cancellation.

`chain_instance_S` (`SoE8.lean`) has no `2 ∣ ell` in its binders. This draft does not claim it is valid at odd `ell`, and does not claim it is not. It is not an analytic negation by itself.

`so_stag0_class` (`SoD0.lean`) puts the direction-0 staggered field in the factor-`c` class for every real `t`, because a direction-0 bond based at `soC` is not a bond of any factor-`c` class cube (`so_bond_uncovered`, `SoGeo.lean`: the binder is every site with that `x₀`, so the uncovered set is that transverse slice). Regularity does not forbid a large angle on those bonds. The obstruction is not a smallness ban on `τ`.

`sites_not_imp_plaq_S` therefore still separates the sites-only class from the both-clause class at odd `ell` in this window. `FamilyTorusCovConstAt` does not transfer by deleting a redundant hypothesis.

## The arithmetic

Fix `d ≠ 0` and `h(x+1, y) = h(x, y) ± d`. In `ZMod (2d)` one has `-d ≡ d`, so every step adds `d`. After `ell` steps,

\[
h(ell+i, j) - h(i, j) ≡ d · ell \pmod{2d}.
\]

If both block sums are `0`, the sum of these `ell²` differences is `0`. It is also the class of `d · ell³`. For odd `ell`, `ell³ = 2t + 1`, so that class is the class of `d`. And `(d : ZMod (2d)) ≠ 0` because `2d ∣ d` forces `d = 0`. This is `no_const_step_blockzero_odd`. The unit-step case is `no_unit_step_blockzero_odd`. It is the same statement shape as `no_uniform_step_blockzero_odd`, not that declaration, and it is not compiled.

Constant magnitude matters because a single plaquette cosine depends on `|Δθ|` only. The lemma does not exclude a profile whose steps are not of one magnitude, and it does not exclude branch offsets. Sol's correction stands: vanishing of the blocked angle is not the homogeneous condition `τ S_q ∈ 2 π ell² ℤ`. The draft proves only the integer sums in that example (`ell_three_linear_sums`: at `ell = 3`, `h(x, y) = x`, the sums are `9` and `36`). It does not prove the angles.

`no_nearby_tau_odd` and `fixed_branch_no_nearby` forbid two nearby parameters on a fixed `±1` profile. They do not forbid one parameter. `homogeneous_one_tau` produces one: if `S₀ ≠ 0`, `τ = 2 π ell² S₀`; if `S₀ = 0`, then `S₁ ≠ 0` and `τ = 2 π ell² S₁`. `const_step_one_lattice_tau` joins this to the block-sum obstruction. A single lattice point is not `WellDefG`, not a negative `genForm`, and not a sites-only counterexample.

## What would close the cell

A negation would need a competitor, on a sites-covered and plaquette-uncovered tower, for which `WellDefG` holds and `genForm` falls below every proposed `γ₀`, at odd `ell`. The even competitor uses the cancellation that `no_const_step_blockzero_odd` rules out. A positive proof would need the inequality on configurations that `sites_not_imp_plaq_S` shows are outside the both-clause class. Neither argument is in this file.

Still not supplied, and not claimed: a coupled-sector or perpendicular-sector estimate, a classification of odd uniform-weight profiles with branch offsets, a bound on a residue ratio, and crossings at odd `ell`. The rank-one `Z`-chain sentence in the paper stays an unproved explanation. It is not used.

## What this does not say

- Not that `FamilyTorusSitesConstAt` fails at odd `ell`, or at odd `ell > 11`.
- Not that it holds there.
- Not that Balaban's lemma is false, or that odd `L` is safe.
- Not that `τ S_q ∈ 2 π ell² ℤ` makes a blocked background trivial.
- Not a re-proof of `sites_not_imp_plaq_S`, `no_uniform_step_blockzero_odd`, or `no_nearby_tau_odd`.
- No `lean` run, no axiom print. `compiled` is false.

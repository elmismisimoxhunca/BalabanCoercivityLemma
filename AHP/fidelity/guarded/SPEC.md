# Design: guarded all-plaquette reading (item 5)

Prediction: **unknown**. Not a theorem. Nothing here was compiled. No file under `lean/`, `paper/`, `notes/`, `expected/`, or `extras/` was edited.

`P428Target8SG selAll selAll` (`lean/src/D2Cons.lean:70`) is the literal inequality guarded by `IsUnit Ginv`. It is equivalent to `GuardResidualT selAll selAll` (`lean/src/GdR5a.lean:54`, equivalence `P428Target8SG_iff_residualT` at `:114`) and to `GuardPencilT` (`lean/src/DrEquiv.lean:99`, equivalence `P428Target8SG_iff_pencilT` at `:116`). The equivalences enlarge the thresholds `m₀`, `R₀` and shrink `a₀`; they are not constant-preserving. `SolR345Audit.full_guard_literal` (`lean/src/SolR345Audit.lean:68`) proves the different statement `P428Target8SG2`, whose guard `WellDefAt` already includes `IsUnit G1inv`. It is not this implication.

## Variant (the missing implication)

The frozen pencil identity (`lean/src/DrRed1.lean:52`, `G1inv_lit_eq_pencil`) says that under `Admissible`, `0 < ell`, `17 ell ≤ R M`, `IsUnit Ginv_lit` and `WellDefAt selIn selIn`,

```text
G1invS selAll selAll = Ginv_lit - Delta2_loc
```

with `Delta2_loc` the correction of the localised data (`R2Algebra.lean:220`, form `2⟨H C₂(A), J⟩`). Along an exterior-only path (`lean/src/DrPath1.lean:47`, `Ginv_lit_path`; bonds outside `Zb`, `D1Path.lean:25`) this is

```text
IsUnit (Ginv_lit(0) + Shift(t)) → IsUnit (Ginv_lit(0) + Shift(t) - D)
```

where `Shift(t) = pE W₀* (Δ_t - Δ_0) W₀ iE`, `Δ` is `deltaKLocCLM` on every plaquette (`ZLocOps.lean:181`), `W₀` and `D = Delta2_loc(0)` do not depend on `t`, and class membership is copied from the start (`classCoupled_path`). `D = 0` when the localised source is orthogonal to the range `Delta2` sees (`GdR6b.lean:40`, `Delta2_eq_zero_of_Jperp`); the flat background has `J = 0` (`ZLocJ.lean:110`, `JSU2Loc_trivial`).

`GuardPencilT` asserts that implication eventually in `m` and `R`, inside `ClassCoupled` at factor 12, and only when a positive-energy test field exists. One bad torus does not negate it. The scalar path in `AHP/attempts/sg-guarded/PencilPin.lean` suggests a bare-transfer obstruction; that file is an UNCOMPILED draft, has no lattice, and supplies no certified result.

The unresolved headline is the existing `GuardPencilT`, but it is NOT approved as a Stage-B deliverable. The decision sends only structural comparisons below; see DECISION.md for the binding exact signatures. An intermediate assembly that does not decide the headline:

```lean
-- proposed, not compiled, not a theorem of the tree
-- On the depth-two slab, ell = 2, a = 1, m ≥ 1, R ≥ 18:
-- Ginv_lit ∘ Uth is PSD at θ = 0 and negative in some direction at θ = π,
-- hence singular at some θ ∈ [0, π).
-- This is exists_nonunit_path (D1IVT.lean:86) applied to GinvLit,
-- using GinvLit_cont (DrPath3.lean:69), form monotonicity plus
-- Ginv_psd_flat at θ = 0 (GdGap2.lean:42; alternatively D1Main.lean:66),
-- and domination_fails_pi (GdR6a.lean:109).
-- On this path the interior is identically 1, so J_loc = 0 and D = 0.
-- Singular Ginv and singular pencil are the same point. Not a separation.
```

## What was searched

The guard hypothesis is `IsUnit` of literal `Ginv` (`R2Algebra.lean:145`: `Dpi + T* T + Mass`). Assembling `W`, `T`, `Mass`, `Q`, `H`, `C₂` and `Delta2` was not done. The script transcribes only the operator the path identity says moves, and the flat checks that operator against its kernel.

| Piece | Lean | In the script |
|---|---|---|
| curl | `CovariantOperators.lean:315` | `curl_matrix` |
| plaquette holonomy | `ClayStatement.lean:1286` | `holonomy` |
| `R(U)X = UXUᴴ` | `CovariantOperators.lean` `RMap_coe_apply` | `rmap` |
| `⟪X,Y⟫ = -½ Re Tr(XY)` | `SuTwoInner.lean:104` | `hs` |
| `Re`/`Im` of `U(∂p)` | `DeltaPrime.lean:125`, `:133` | `_re_im` |
| `a₁…a₄`, `bilPlaq` | `DeltaPrimeOperator.lean:287–330`, `:376`, `:395` | `_a_of`, `_bil_plaq` |
| normalised `Δ'` `(1/4)(raw+flip)` | `ZLocOps.lean:119` | `delta_prime_matrix` |
| `⟨x,Δx⟩ = ⟪χ curl, χ curl⟫ + Δ'` | `ZLocOps.lean:186` | `delta_matrix` |
| `U_θ` on `Zb` | `D1Path.lean:46`, `:25` | `config` |
| shift `Δ(t)-Δ(0)` | `DrPath1.lean:47` | `M(θ) - M(0)` at fixed interior |

Not transcribed, and not claimed to have been: `Wop` (`ZR2Ops2.lean:67`), `Mass`, `Tfull`, `Delta2`, `Ginv`, `G1inv`, `genFormS`, the inequality `InstIneqSG`. A finite-difference of `Δ` in an interior bond is a probe of support, not `Delta2`.

Geometry: periodic 3-torus, side `N ∈ {3,4}` (at most 8). `Ω₀ = {0,1}³`, proper and nonempty. Counts for `N = 3`: 81 bonds, 12 `BothIn`, 45 `Zb`, 24 shell bonds, 6 plaquettes in `plaqIn`. For `N = 4`: 192 bonds, 156 in `Zb`, same 12 `BothIn` and 6 `plaqIn`. Bond field dimension `9 N³` (3 directions × 3 of `su(2)`). Dense eigenproblems, well under 4 GB.

Scripts: `numerics/delta_pencil_probe.py`, `numerics/crossing_gap.py`. Retained output: `numerics/crossing_results.json` and `numerics/probe_results.json` (the latter regenerated during ATTACK). The committed probe main uses `interior_mode="one"`, not `"uniform"`; its nonzero-epsilon grid is the one-bond family. Uniform flux was checked separately by the attacker, not by that committed main.

### Checks that the transcription matches the flat operator

At `U = 1`:

- `Δ'` is the zero matrix (max entry `0`).
- `⟨grad λ, Δ grad λ⟩ = 0`.
- Kernel dimension equals `3 N³ + 6` (gradients of site `su(2)` fields, plus harmonic 1-forms): **87** on `N = 3`, **198** on `N = 4`.
- The matrix is symmetric to `0` in float64. Largest eigenvalue `9` (`N = 3`) and the form is positive semidefinite up to `10⁻¹⁴`.

These are checks of `D*D` at the trivial background, not of `Ginv`.

### Pure exterior path and separate uniform-flux support check

Setting every `BothIn` direction-0 bond to `u_ε` leaves `plaqIn` holonomy equal to `1` by cancellation of parallel edges. ATTACK reports a separate uniform-branch check with `Im` Frobenius sum `0` at `ε ∈ {0, 0.05, 0.2}`; this is not the committed main's grid. On that uniform family the localised source vanishes, so it is not a candidate for separation. The retained one-bond grid instead has Im sums approximately `0`, `0.1414`, `0.5619`. All numbers in the following bullets are at `ε = 0`, where the two modes coincide.

On the pure path `ε = 0` (this is `Uth`):

- `N = 3`, compression of `Δ(θ)` onto the flat positive subspace: `+3` at `θ = 0`, `+1.43` at `π/8`, `-0.53` at `π/4`, `-6.44` at `π`.
- `N = 4`: `+2` at `θ = 0`, `+0.34` at `π/8`, `-1.41` at `π/4`, `-6.78` at `π`.
- The most negative eigenvalue of the shift `Δ(θ)-Δ(0)`, compressed, reaches about `-14`.
- Twelve random `SU(2)` assignments of `Zb` (`N = 3`, flat interior) all made that compression negative (most negative value about `-6.4`).

`Δ` itself is indefinite for `θ ≥ π/8`. It is not invertible: a kernel remains (below). The probe flag that printed `hit=True` on this grid meant "compression indefinite and bounded away from zero", and when `ε = 0` the stand-in correction was `0`, so it was not a split between two operators. For the 14 nonzero-epsilon `hit=True` rows per lattice, the carrier compression was already indefinite (`carrier_min < 0`); these are not positive-carrier-to-negative-pencil crossings either. Indefiniteness is NOT itself non-invertibility, and compression is not the full operator. No grid row supplies a full transcribed unit with a singular pencil.

### One-bond interior defect (nonzero `plaqIn` holonomy)

One `BothIn` bond, base `(0,0,0)` direction `0`, set to `u_ε`. Two `plaqIn` plaquettes then have `Re Tr U(∂p) = 2 cos ε` (`1.911` at `ε = 0.3`). `Im` Frobenius sum on `plaqIn` is `0.562` at `ε = 0.2`. The localised operator `Δ_in` moves by operator norm `0.634` at `ε = 0.2` (`N = 3` and `N = 4`, same small block). This is the scale of an interior change of `Δ`, not of `Delta2`.

Spectrum of `Δ` (`N = 3`; `N = 4` is the same shape, kernel `198` at `θ = 0`):

| θ | ε | λ_min | eigenvalues with \|λ\| ≤ 10⁻⁶ |
|---|---|---|---|
| 0 | 0 | 0 | 87 |
| 0.05 | 0 | −0.135 | 31 |
| 0.10 | 0 | −0.282 | 31 |
| π | 0 | −6.44 | 87 |
| 0 | 0.2 | −0.250 | 69 |
| 0.05 | 0.2 | −0.232 | 31 |

`λ_min` leaves `0` linearly in `θ` (about `-2.7 θ` for small `θ`), which is the commutator term of `Δ'` (order `Im U(∂p)`), not the `(Re U - 1) ~ θ²` term. A kernel of size `31` (`N = 3`) or `108` (`N = 4`) survives every tested `θ > 0`. **`Δ` was never a unit** in this search, so the guard hypothesis was never true of this operator. Zero cases of "carrier invertible, pencil singular".

Overlap of an interior finite-difference `D_Δ = Δ(ε=0.2) - Δ(ε=0)` with eigenvectors of the flat-interior operator (`N = 3`): the second and third bullets are hand-computed diagnostics, independently reconstructed during ATTACK, not output of either committed script. Here both matrices use the same θ. Do not cite these as scripted replay results.

- Surviving near-zero mode: `⟨v, D_Δ v⟩` is `10⁻¹⁷` to `10⁻²⁸` while `‖D_Δ‖ ~ 0.8`. That mode does not see the interior bond.
- Most negative mode at `θ = 0.05`: `λ = -0.135`, `⟨v, D_Δ v⟩ = +0.017`.
- Least negative departing mode at `θ = 0.05`: `λ = -8.7×10⁻⁴`, `⟨w, D_Δ w⟩ = +8.2×10⁻⁴`, the same order as `λ`.

So an interior change of `Δ` does move the eigenvalues that have just left zero, and does not move the kernel that stays. Both facts are about `Δ`, not about `Ginv` or `Delta2`.

## Why this does not decide the guard

1. `Ginv_lit = T*T + Mass + W* Δ W` with `T`, `Mass`, `W` frozen along the path (`DrPath1.lean:47`). The mass and gauge terms are exactly what can clear the kernel `Δ` keeps. Their absence is why the search never saw a unit.
2. On `Uth` the interior is `1`, so `D = 0` and the pencil equals `Ginv`. A singular `θ` on that path, if it exists, is not a separation.
3. `domination_fails_pi` already puts a negative direction of literal `Ginv` in the class at `θ = π`, for every `α₀ > 0`, on the slab with `R ≥ 18`. The margin `‖Delta2‖ < coercivity constant` (`DrMargin.lean`) does not apply on the whole class: coercivity of literal `Ginv` fails at `π` independently of `α₀`. Choosing `a₀` small does not remove `Uth(π)` from the class.
4. One torus, and a cofinal family in `m` and `R`, are different quantifiers (`SepPathFamily2` is a sufficient certificate, not the negation). `N ≤ 4` is far below `R ≥ 18` and `M = ell^m`.

## Structural reading, and the proof plan

`exists_nonunit_path` is an intermediate-value argument: a continuous symmetric family that is positive semidefinite at `0` and negative on some vector at `T` is singular at some earlier time, and the first such time is still positive semidefinite (a kernel, not yet an indefinite unit). The ingredients already exist, including named flat positivity: `D1Main.lean:66` (`Fth_zero_psd`) and `GdGap2.lean:42` (`Ginv_psd_flat`, for any selectors). `D1Main.lean:141` already gives the non-unit crossing under the boundary-point hypotheses. Thus the proposed slab crossing is an assembly/recheck, not a new missing ingredient. Moreover `GdFam.lean:30` already gives `G1invS_eq_Ginv_theta` unconditionally on this path under its geometry hypotheses. These comparisons do not separate `Ginv` from `Ginv - D`.

DECIDER QUALIFICATION: the three numbered points below are heuristic research directions, NOT approved implications. `exists_nonunit_path` exports only existence of a non-unit, not a first-singularity or PSD-at-crossing assertion. Its proof constructs a PSD crossing, but obtaining that stronger statement requires a separate declaration. In particular, `⟨v,Dv⟩ = 0` need not imply `Dv = 0`; off-diagonal coupling can shift a root. Visibility alone does not establish a moved root, and invisibility does not prove coincident roots or the guard implication. Neither alternative below is established by the probes.

A proof of `GuardPencilT` cannot be the bare margin, and cannot be "small `α₀` forces every exterior link close to `1`": `Zb` is disjoint from `CubeBond (Ω₀)` (`ZT6B.lean` `perCubeRegular2_congr`, `D1Path.lean:77`). The route that matches the identity and the numerics is:

1. Along an exterior path, let `t_*` be the first time `Ginv_lit` fails to be a unit. By the same supremum as `exists_nonunit_path`, `Ginv_lit(t_*)` is positive semidefinite with a kernel vector `v`.
2. Before `t_*`, `psd_coercive` (`D1IVT.lean:47`) gives a gap. `Ginv - D` stays a unit on that interval if `⟨v, D v⟩ = 0` for every such first kernel vector and `‖D‖` cannot eat the gap in the transverse directions. `D` depends only on the interior.
3. The numerical substitute for (2) splits in two. The kernel `Δ` never loses is orthogonal to an interior bond. The first eigenvalues that leave zero are not: their interior matrix element is of the same order as the eigenvalue. If the first kernel vector of the gauge-fixed `Ginv` is one of those departing modes, a nonzero `Delta2` moves `t_*` and the implication fails at the moved root (one `θ` per scale; cofinally many scales would negate `GuardPencilT`). If the first kernel vector is invisible to `Delta2`, as the surviving `Δ`-kernel is invisible to the interior bond, the roots coincide and the implication holds on that path.

Stage B should prove (1), and should not claim (2) until the kernel vector of `Ginv_lit` at `t_*` is identified. A counterexample file is not justified: this search never produced a unit `Ginv` with a singular pencil, and `Δ` is the wrong operator to inhabit `SepPathFamily2`.

## Stage-B Lean plan

Write `AHP/fidelity/guarded/lean/UthCross.lean` only after `REPRODUCE.sh` has finished. Do not import `DrSkeleton.lean`. Suggested imports, all already in the Lake project:

- `DrPath3` (`GinvLit`, `GinvLit_cont`, `G1Lit_eq`)
- `DrPath1` (`Ginv_lit_path`)
- `DrRed1` (`G1inv_lit_eq_pencil`)
- `D1IVT` (`PSD`, `exists_nonunit_path`, `psd_coercive`)
- `GdR5b` (`Fth_zero_isUnit`)
- `GdGap2` (`Ginv_psd_flat` at :42, `Ginv_form_mono_flat` at :125)
- `D1Main` (`Fth_zero_psd` at :66, `exists_nonunit_Ginv` at :141)
- `GdFam` (`G1invS_eq_Ginv_theta` at :30)
- `GdR6a` (`domination_fails_pi`, `Ginv_loc_psd_twist`)
- `D1Path` (`Uth`, `Zb`)
- `GdR6b` (`Delta2_eq_zero_of_Jperp`) for the disclosure that the singular `θ` on flat `Uth` has `D = 0`

Historical design outline (superseded by the exact comparison signatures in DECISION.md):

1. `Ginv_lit_psd_at_zero` on the slab at `θ = 0`: literal `Ginv` is `PSD`, from `Ginv_form_mono_flat` and `Ginv_psd_flat`.
2. `Uth_hits_nonunit`: `∃ θ, 0 ≤ θ ∧ θ < π ∧ ¬ IsUnit (GinvLit … (Uth θ))`, by `exists_nonunit_path`, continuity, (1), and the negative vector in `domination_fails_pi`. Scope: `ell = 2`, `k = 2`, `a = 1`, `m ≥ 1`, `R ≥ 18`, the slab `SlabNv`. Not for general towers.
3. `Uth_singular_is_not_a_split`: on that same path `Delta2_loc = 0`, so `¬ IsUnit Ginv` and `¬ IsUnit (Ginv - Delta2_loc)` are the same. Discharge `J = 0` by `JSU2Loc_trivial` or `Delta2_eq_zero_of_Jperp`.
4. Stop. Do not state `GuardPencilT`. Do not state `SepPathFamily2`. A later file may attack the kernel vector of (2) only after (1)–(3) print axioms `propext`, `Classical.choice`, `Quot.sound` or a subset.

Check, when the build is allowed: `lake env lean` on that file and `#print axioms` of the three names. No `sorry`.

## Files

- `AHP/fidelity/guarded/SPEC.md`
- `AHP/fidelity/guarded/numerics/delta_pencil_probe.py`
- `AHP/fidelity/guarded/numerics/crossing_gap.py`
- `AHP/fidelity/guarded/numerics/crossing_results.json`
- `AHP/fidelity/guarded/numerics/probe_results.json` (regenerated during ATTACK)

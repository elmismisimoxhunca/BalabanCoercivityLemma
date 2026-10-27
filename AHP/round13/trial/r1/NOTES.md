# Round 13 — trial R1: P1 proved on the actual right-star carrier

## Verdict and verification boundary

**P1 is CLOSED.** The explicit six-bond periodic field has actual frozen vacuum-carrier energy exactly `-1/4`, for **every** `q > 0`, even `R ≥ 18`. The original nested cofinal dyadic/even quantifiers are also proved.

This is **not** a proof of P2, P3, `KernelLine`, `CofinalAnyPathNoResponseCancellation`, or `GoalNeg2`. No physical estimate is assumed in the P1 theorem. There is no reflection, Schur-complement identification, numerical premise, or inverse-unit premise.

| Certificate | Lines | Exit | New declarations |
|---|---:|---:|---:|
| `AHP/round13/trial/r1/Trial.lean` | 2298 | 0 | 91 |
| `AHP/round13/shared/trial/R1_Trial.lean` | 2298 | 0 | 91 |

The source files are byte-identical. Each was compiled separately, sequentially, with `bb heavy run -- AHP/round3/lean1.sh <file>`. Each has its own `.lean.log` and `.lean.exit`. These are two builder executions, **not independent mathematical review**. `audit.py` passes; `AUDIT.json` pins source/log hashes, standard axiom records, theorem locations, and five verbatim source-fragment checks. The only import is frozen `DrEquiv`. All printed dependencies are subsets of `{propext, Classical.choice, Quot.sound}`. No forbidden proof mechanism occurs.

## Exact delivered statements

Namespace `AdalyFormal.Round13.Trial`, with the original family/operator namespaces opened:

```lean
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

This is the P1 form in `AHP/round12/shared/GAPS.md`, verbatim. `TwistSpace` is the original `AdalyFormal.Round9.Guarded.AnalyticR1.TwistSpace`, copied verbatim from the round-12 first-crossing package. `rightStar`, `vacA`, and their canonical equality are copied verbatim from `R2_RightFamily.lean`.

The stronger explicit-witness theorem is:

```lean
theorem trial_carrier_energy {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R,
      vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ)
```

The cofinal theorem is:

```lean
theorem cofinal_rightStar_negative_halfpi :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      ∃ w : TwistSpace (2^j) R,
        ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0
```

It chooses `j = j₀` and `R = 2*(R₀+18)`. It does not move a radius choice past a later cap or use a finite sample as cofinality.

Literal final dependency records, present in both clean logs:

```text
'AdalyFormal.Round13.Trial.trial_carrier_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round13.Trial.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]
'AdalyFormal.Round13.Trial.cofinal_rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Physical proof, not a surrogate calculation

1. **Periodic embedding.** `patchSite` embeds a seven-site coordinate box about the original `rightSite` by actual `Fin` addition. `patchSite_injective` proves no periodic collisions; `patchSite_shift` and `patchSite_back` identify actual forward/backward lattice shifts. `trialBond_injective` gives six distinct actual bonds. Negative transverse offsets wrap correctly; no integer-lattice-to-torus assumption remains.
2. **Explicit charged field.** `charged z` is the actual traceless skew-Hermitian matrix `!![0,z;-star z,0]`. `trialField` is the sum of six actual `sing` fields: centre `1`, positive normal neighbours `-I/4`, negative normal neighbours `I/4`, and the direction-1 tangent at the centre `-I/4`. `charged_norm` and `trialField_norm` prove the exact physical norm square `21/16`.
3. **Carrier and collar geometry.** `trialField_mem` puts this field in the original touching-bond carrier. `trial_collar` and `trial_levelZero` prove that its endpoints avoid `Omega1` and that all six rows genuinely occur at level zero. The common exterior witness is the site immediately to the right of `rightSite`; every supported base lies within distance two of it, and every supported endpoint within distance three.
4. **Higher-level exclusion and exact mass.** Frozen `D1Literal.QlinB_supp_zero` / `Mass_supp_le` in `lean/src/D2Geo5.lean` already give the needed upper bound for fields supported within distance two of the complement. They are imported through `DrEquiv`, not modified. `trial_higher_rows_zero` instantiates the higher-row vanishing. Combining `Mass_supp_le` with the copied level-zero lower extraction gives `trial_mass_eq = 21/16`, for **arbitrary background U**. This closes the upper/equal-mass gap; it does not infer equality from `leaf_mass_le` alone.
5. **Actual dressing and gauge term.** The copied round-12 arbitrary-orientation single-bond locality lemmas, plus linearity, give `trial_T_zero` and `trial_W_eq` on the complete trial. They hold for arbitrary U (and arbitrary mass parameter in W), without an inverse-unit hypothesis.
6. **Complete frozen plaquette enumeration.** `trialPlaqPattern` lists nineteen actual plaquettes. `trialPlaq_injective` proves distinctness. `pattern_front`, `pattern_back1`, `pattern_back2`, and the actual inverse-shift identities classify every possible field-bearing boundary edge. `trial_plaq_zero_off` proves exact zero curl and bilinear contribution on every other torus plaquette, for arbitrary U. Thus `trial_delta_sum` is an equality for the **entire frozen all-plaquette operator**, not an unproved finite truncation.
7. **Actual right-star links, holonomy, and atoms.** `rightStar_patch`, `trial_base_links`, and `trial_holonomy` evaluate the original right-star configuration. Only entries 4, 9, 11, 12 among the nineteen are curved; their holonomy is `uθ t`. `trial_hol_parts` evaluates the true real/imaginary holonomy at half pi. `trial_edge_values` and `trial_atom_values` identify the four actual frozen atoms in the order `[2,3,0,1]`, with signs `[-,-,+,+]` and the true transports. The copied round-12 plaquette algebra is extended to `frozen_four_form` so the one flat plaquette with a nonzero fourth atom is retained.
8. **Kernel-checked finite arithmetic.** `edgeIndex_spec` validates the entire finite incidence table by ordinary `decide` (kernel reduction). `localQuad_value` proves the nineteen exact contributions by `norm_num`, after explicit definitional reduction. The numerators over 16 are `[1,1,1,1,-8,1,1,1,1,-8,1,-16,-8,1,1,1,1,1,1]`. Consequently `trial_flat_energy = 15/16`, `trial_curved_energy = -5/2`, and `trial_delta_value = -25/16`. No Python output is an assumption or a proof oracle.
9. **Original carrier join.** Copied `vacA_rightStar`, frozen `BaseDataS.inner_Ginv`, and the actual W/T/mass identities yield `trial_carrier_energy = -25/16 + 0 + 21/16 = -1/4`.

## Publication locations

All locations refer to `AHP/round13/shared/trial/R1_Trial.lean`:

| Declaration | Line |
|---|---:|
| `patchSite_injective` | 1278 |
| `trialBond_injective` | 1328 |
| `trialField_norm` | 1375 |
| `trial_higher_rows_zero` | 1543 |
| `trial_mass_eq` | 1559 |
| `trial_T_zero` | 1574 |
| `trial_W_eq` | 1584 |
| `trialPlaq_injective` | 1662 |
| `trial_delta_sum` | 1747 |
| `trial_delta_value` | 2127 |
| `trial_curved_energy` | 2135 |
| `trial_flat_energy` | 2143 |
| `trial_carrier_energy` | 2151 |
| `rightStar_negative_halfpi` | 2180 |
| `cofinal_rightStar_negative_halfpi` | 2187 |

For assembly, the five `*Body.lean.txt` files are the new namespace-only fragments; `build.py` shows their order. They use the verbatim RightFamily, Boundary, Mass, Star/Plaquette, and TwistSpace interfaces. Do not concatenate repeated historical namespace declarations blindly with another compact package. These are source certificates, not new importable `.olean` modules.

## Anything still missing

**No P1 obligation remains.** This track has not proved the following other physical premises (quoted verbatim from the requested GAPS section, with its namespace openings). They are recorded here as open requirements, not declarations with proof holes:

```lean
-- P2: all physical fields, including the neutral coordinate.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

-- P3: detection of that SAME actual canonical crossing line.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The first-crossing package's continuity, initial-positivity and gauge inputs, and the downstream historical GoalNeg2 joins, remain the assembly track's verification responsibilities. P1 alone does not produce a crossing, a kernel line, detection, or the pinned negative goal.

## Reproduction

```sh
python3 AHP/round13/trial/r1/build.py --publish
bb heavy run -- AHP/round3/lean1.sh AHP/round13/trial/r1/Trial.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/trial/R1_Trial.lean
python3 AHP/round13/trial/r1/audit.py
```

No `lake build`, `REPRODUCE.sh`, commit, push, external deletion, or edit outside this track and `AHP/round13/shared/trial/` was performed. No new numerical experiment is needed for the result.

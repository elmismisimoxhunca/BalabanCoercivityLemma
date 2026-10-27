# Prosecution — s4-odd-sites (Kimi lane)

Target: the uncompiled draft [OddSites.lean](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/s4-odd-sites/OddSites.lean) and its note [s4-odd-sites.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/s4-odd-sites.md). Draft outcome under attack: **blocked** (the odd-`ell` sites-only cell `FamilyTorusSitesConstAt` is undecided).

Prosecution method: read every frozen declaration the draft names, hand-check the arithmetic obstruction, try to decide the cell from the existing tree, and audit hygiene. No `lean`/`lake` run (prohibited). No file outside `AHP/` touched (`git status --porcelain` shows only untracked `.bb/` and `AHP/`).

## Verdict

**ACQUITTED-AS-TESTED.** The blocked verdict withstands prosecution: every cited frozen fact checks out, the obstruction argument is mathematically sound, and no existing theorem of the tree decides the odd cell. Two findings below, neither of which overturns the outcome.

## What was verified against the frozen sources

| Draft claim | Check | Result |
|---|---|---|
| `not_familyTorusSitesConstAt_S` assumes `hE : 2 ∣ ell` | `SoA1.lean:37` | Exact. |
| `main_neg_S` assumes `2 ∣ ell` | `SoM3.lean:34` | Exact. |
| `wellDefG_punctured` assumes `2 ∣ ell` and calls `dsP_analytic` | `SoU2.lean:89,94` | Exact. |
| `H0_bij_path` assumes `2 ∣ ell`, calls `nested_z0Setup_S` and `unit_temporal_stag0` | `SoU2.lean:69,72,76` | Exact. |
| `chain_instance_S` has no `2 ∣ ell` binder | `SoE8.lean:70` | Exact (see Finding 1). |
| `sites_not_imp_plaq_S` needs only `2 ≤ ell`, gives `CovSitesF ∧ ¬ CovPlaqF` | `SoA3.lean:86-89` | Exact. |
| `no_uniform_step_blockzero_odd` is the d=1 shape of the draft's lemma, a different declaration | `SoPar.lean:22` | Exact. |
| `no_nearby_tau_odd` forbids two *nearby* parameters, not one | `SoPar.lean:55` | Exact. |
| `fixed_branch_no_nearby` exists and does the same with a common branch offset `K` | `SolSitesAffine.lean:6` | Exact. |
| `FamilyTorusSitesConstAt` keeps `CovSitesF ∧ PerCubeRegularF`, drops plaquettes | `CaT2d.lean:121-131` | Exact. |
| Committed table: fails at `ell = 2` and even `ell ≥ 4` with `ell ∣ 2(c-1)`, `9 ell ≤ 2(c-1)` | `CaT2d.lean:135`, `SoA2.lean:18,28` | Exact. `SoA3.lean:10` itself says the analytic refutation "is not built" for odd `ell`. |
| `so_stag0_class` holds for every real `t` with no evenness hypothesis | `SoD0.lean:22-25` | Exact. |
| `so_bond_uncovered`: binder is every site with `(x 0).val = soC …`; the direction-0 bond is in no class cube | `SoGeo.lean:71-76` | Exact. |
| S-4 quote: "L is an odd, positive integer > 11" (CMP 109 p.251, verified on the page image 2026-10-20) | `paper/OPEN_ITEMS.md:333` | Exact; the draft reuses the recorded quote and does not reopen the image. |
| `SoRel ell c` is `ell * (cfv - 1) = 2 * (c - 1)` | `SoGeo.lean:35` | The draft's `w = 19, c = 9 ell + 1` gives `18 ell = 2(c-1)`, satisfying it. |

## Attempt to refute "undecided" from the tree

Exhaustive grep for `FamilyTorusSitesConstAt`: the tree contains only the definition (`CaT2d`), the `ell = 2` negation (`not_familyTorusSitesConstAt_two`), the even negations (`not_familyTorusSitesConstAt_S`, `_div`, both requiring `2 ∣ ell`), and the implication `familyTorusSitesConstAt_imp_cov` (`CsA2.lean:84`), which decides nothing at odd `ell`. No positive sites-only theorem exists. The cell is genuinely undecided in the committed tree; the draft's outcome cannot be refuted.

## Hand-check of the obstruction argument

`no_const_step_blockzero_odd`: steps `±d` all satisfy `±d ≡ d (mod 2d)`, so `h(ell+i,j) − h(i,j) ≡ ell·d (mod 2d)` for each of the `ell²` pairs. If both block sums were `0`, then `2d ∣ ell³·d`, i.e. `2 ∣ ell³`, contradicting `ell` odd. Sound. The odd-cube expansion `(2t+1)³ = 2(4t³+6t²+3t)+1` used in `odd_cube_form` is correct. `hdne` (`(d : ZMod 2d) ≠ 0` for `0 < d`) is correct: `2d ∣ d` forces `d·(1−2q)=0` over ℤ, impossible. The hypothesis `0 < d` is necessary (d = 0 admits h ≡ 0) and is present. `homogeneous_one_tau` (one `τ` from nonzero sums) is trivially correct and honestly labelled "not a blocking criterion". The `ell = 3` sums (`9`, `36`) are correct. The ell = 13 window (`c = 118`, `2(c-1) = 234 = 18·13`, `117 ≤ 234`) is correct.

## Finding 1 (minor, wording): the note understates `chain_instance_S`

The note says the draft "does not claim it is valid at odd ell, and does not claim it is not". But `SoE8` is in the build (`MODULES.tsv:2683`) and is not one of the five sorry-carrying modules (`expected/forbidden_tokens.expected.txt`), so `chain_instance_S` is a compiled theorem whose binders (`3 ≤ ell`, `ell ∣ M`, `0 < M`, `1 ≤ R`, `SoRel ell c`, `10 ≤ c`) admit every odd `ell ≥ 3`. It *is* valid at odd `ell`. This does not change the verdict — it is a positive coupled-sector spectral fact at the staggered background, not an analytic negation, exactly as the note says ("not an analytic negation by itself") — but the accurate sentence is "valid at odd ell, and not a decision of the cell", not agnosticism.

## Finding 2 (disclosure): the script as written is likely not elaboration-clean

Consistent with the honestly declared `compiled: false`, and not checkable here (no `lean` run permitted). On paper the script contains probable elaboration errors, all mechanical:

1. **Duplicate rewrite.** In `hsumconst`, `rw [← Int.cast_natCast, ← Int.cast_natCast, Int.cast_mul]`: the first `← Int.cast_natCast` rewrites *all* occurrences, so the second finds no instance and fails; moreover the forward `Int.cast_mul` has no literal `↑(a*b)` to fire on while `c` is a let-bound fvar.
2. **Trailing `rfl` after auto-closing `rw`.** `delta_zmod` (`rw […, sub_zero]; rfl`), `hsub` (`rw [← Int.cast_sub]; rfl`), `hcong` (`rw [hself, zero_mul]; rfl`), and `hbad` (`rw [← hcong, ← hsumconst, hsumcast]; rfl`) each leave a syntactic `0 = 0` (or `a = a`) that `rw`'s built-in `rfl` already closes; the extra `rfl` fails with "no goals".
3. **`unfold c` on a let-bound local** in `hsub` may not apply (depends on `unfold` accepting local lets at this toolchain).

None of these touches a statement; the mathematical content above was verified by hand. But the note should be read as "not even elaboration-checked", which it already effectively says.

## Hygiene

- Draft imports only `Mathlib`; no frozen module imported, none edited.
- Token scan of `OddSites.lean`: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`.
- The draft never calls the cell true or false, never calls itself a theorem of the project tree, and its "What this does not say" list is accurate.
- `compiled: false`, `frozenFilesEdited: false` in the draft JSON are both true as measured.

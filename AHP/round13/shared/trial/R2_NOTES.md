# Trial R2 — retain accepted P1; complete cofinal handoff

## Verdict

**P1 remains proved, with no remaining physical trial obligation.** R1's complete
certificate and independent acceptance are preserved unchanged. R2 does not redo
the finite stencil argument: it appends six small consumer declarations to the
byte-identical accepted R1 source. These combine the explicit negative trial with
all right-star path clauses at the same nested cofinal indices.

**This track does not prove P2, P3, KernelLine, response noncancellation, or
GoalNeg2.** The exact Rayleigh quotient below concerns the trial, not a crossing
eigenvector or an eigenvalue.

## Certificates and audit

| Certificate | Lines | Exit | Printed dependency records |
|---|---:|---:|---:|
| `AHP/round13/trial/r2/Trial.lean` | 2387 | 0 | 201 |
| `AHP/round13/shared/trial/R2_Trial.lean` | 2387 | 0 | 201 |

Both files are byte-identical, import only frozen `DrEquiv`, and were compiled
separately through `bb heavy run -- AHP/round3/lean1.sh`. Every printed dependency
list is a subset of `{propext, Classical.choice, Quot.sound}`. Six harmless linter
warnings remain (four inherited; two unused binder-name warnings in the exact
P1 type). No forbidden proof mechanism occurs.

`audit.py` passes and writes `AUDIT.json` plus `shared/trial/R2_AUDIT.json`. It
checks both clean final compilations, all 201 printed commands/records, the six
new declarations, all 91 inherited trial declarations, byte identity, the exact
P1 type against the requested round-12 GAPS statement, and the five original
verbatim interface copies. It also rechecks the original builder, publication,
and independent-reviewer R1 artifacts **read-only**.

The first R2 attempt exited 1 because the appended cofinal type was missing an
`open AdalyFormal.StatementLane` for `scaleUp`. Its cascading elaboration failure
is retained in `first_compile.log` / `.exit`; it is not an accepted certificate.
After adding the namespace opening, both final source paths compiled with exit 0.
No timeout or active-job relaunch occurred.

**Verification boundary:** R1 was independently accepted in
`AHP/round13/trial/r1/Trial.VERIFY.md`. R2's appendix has two builder executions,
not an independent reviewer replay. No numerical evaluation is used as proof.

## Exact P1, unchanged

With the original namespaces opened, `AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi`
at shared line 2335 has exactly the requested type:

```lean
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
```

Its proof term is the existing `AdalyFormal.Round13.Trial.rightStar_negative_halfpi`.
No extra hypothesis or replacement operator is introduced. Literal record:

```text
'AdalyFormal.Round13.Trial.R2.rightStar_negative_halfpi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The retained `trial_carrier_energy` at line 2151 proves actual full-carrier energy
`-1/4` for the explicit six-bond `trialVector hq R`. Its R1 proof already establishes:
collision-free periodic embedding, exact physical mass `21/16` including the upper
bound, vanishing higher-level blocking rows, `T=0`, `W=id`, full enumeration of
nineteen actual plaquettes, flat contribution `15/16`, and curved contribution
`-5/2`. The original canonical `vacA_rightStar` identity finishes the join. See
R1 NOTES for the physical proof inventory; none of these facts is replaced by a
local surrogate or a lower-mass-only argument in R2.

## New reusable declarations

Namespace `AdalyFormal.Round13.Trial.R2`, shared file locations:

| Declaration | Line | Content |
|---|---:|---|
| `trialVector_norm_sq` | 2315 | Actual carrier norm squared is `21/16`, every positive q and every R. |
| `trialVector_ne_zero` | 2319 | Explicit trial is nonzero, with no even-radius hypothesis needed. |
| `trial_rayleigh` | 2327 | Actual half-pi Rayleigh quotient is exactly `-4/21`, for even R≥18. |
| `rightStar_negative_halfpi` | 2335 | Exact P1 consumer, reusing the accepted proof. |
| `rightStar_physical_halfpi` | 2343 | All path clauses, pi negativity, trial nonzero/norm/energy at any selected admissible q,R. |
| `cofinal_rightStar_paths_halfpi` | 2357 | All these clauses together in the original nested quantifier order. |

The final cofinal statement is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
    V = rightStar (by positivity) R ∧
    AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
    (∃ z : TwistSpace (2^j) R, ⟪z, vacA (2^j) R V 1 Real.pi z⟫ < 0) ∧
    ∃ w : TwistSpace (2^j) R,
      w = trialVector (by positivity) R ∧ w ≠ 0 ∧ ‖w‖^2 = (21/16 : ℝ) ∧
      ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ = (-1/4 : ℝ) ∧
      ⟪w, vacA (2^j) R V 1 (Real.pi/2) w⟫ < 0
```

It chooses `j=j₀`, `R=2*(R₀+18)`, the original `rightStar`, and the explicit
`trialVector`. The pi and half-pi witnesses need not be the same vector, but their
path, scale, and radius are the same. No cap is moved and no separate cofinal
subsequences are intersected. For any future P2/P3-selected cofinal family, use
`rightStar_physical_halfpi` at its selected indices rather than intersecting it
with the particular radius sequence above.

The exact appendix is published as `shared/trial/R2_HandoffBody.lean.txt` for
source-level assembly. It assumes the existing R1 declarations and is checked
inside `R2_Trial.lean`; it is not a separate importable module. The original
R1 main declaration names and interfaces remain available unchanged.

## Exact remaining physical statements — not proved by this track

No P1 statement remains missing. With the round-12 shared-package opens, the
other original obligations are, verbatim:

```lean
-- P2: strict full-carrier positivity, retaining the central neutral coordinate.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫

-- P3: detection at the SAME canonical crossing line.
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
```

The weaker sufficient joint cofinal remainder, still not provided here, is:

```lean
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
```

R1 assembly separately constructs the canonical crossing and supplies the
conditional downstream joins; P1 alone does not construct a whole KernelLine or
prove detection. This R2 trial file contains no conditional theorem represented
as an unconditional solution of those obligations.

## Reproduction and write boundary

```sh
python3 AHP/round13/trial/r2/build.py --publish
bb heavy run -- AHP/round3/lean1.sh AHP/round13/trial/r2/Trial.lean
bb heavy run -- AHP/round3/lean1.sh AHP/round13/shared/trial/R2_Trial.lean
python3 AHP/round13/trial/r2/audit.py
```

Only `AHP/round13/trial/r2/` and new `R2_*` files under
`AHP/round13/shared/trial/` were written. No earlier certificate was modified;
no `lake build`, `REPRODUCE.sh`, numerical solve, deletion, commit, or push was run.

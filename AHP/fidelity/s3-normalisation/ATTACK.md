# s3-normalisation — attack

Role: attack the design in `SPEC.md` and its script `numerics/first_term_readings.py`.
Verdict: **the design survives.** The prediction "fails" is supported by
exact rational arithmetic, reproduced twice (the design script re-run, and an
independent re-transcription, `numerics/attack_check.py`, 37/37 PASS).
Nothing below is a theorem. No Lean was run. Numerics are evidence only.

## 1. Does the variant say what it claims about the print?

Yes. The claim under test,

```lean
def FirstTermScalarClaim (ρ : Reading) : Prop :=
  ∃ c : ℚ, ∀ B : Fin 2 → ℚ,
    eta * schur S_lane (tauStar B) = c * schur (S ρ) (tauStar B)
```

is the faithful formalisation of "the external `η` and `τ*` in the frozen
first term (`ZXG3A.lean:50`) are a normalisation matching the printed first
term of (3.156)". The print (`CMP99b_p428.md`, (3.156) and (3.157)) shows no
`η` and no `τ`, and the SPEC says exactly that. The three readings (plainH,
draft, linearEta) are pinned to specific Taylor counts on pp. 393/421/422,
and the SPEC states what each power is at `j = k` and why (3.136) does not
adjudicate. The uniformBody control is explicitly labelled "not a page
reading" — no overclaim.

One scope note (disclosed, not an error): the claim quantifies over **all**
`B : Fin 2 → ℚ`. The print considers (3.156) on the subspace
`{B : B = 0 on Λ^c, B = 0 on Ax(y), Q_1 B = 0}` (p. 428). The stand-in matrix
model has no `Q_1 B = 0` constraint, so the refutation is of the universal
scalar claim, which is the claim the normalisation reading needs: a scalar
that works only on a subspace is not a normalisation of the form. Stage B
formalises exactly the stated variant, so the numerics and the Lean target
test the same thing.

Robustness worth recording: the spread test (is `frozen/printed` constant in
`B`?) is immune to any **global** mis-weighting — a wrong overall pairing
weight or a wrong overall power of `η` on the whole first term would shift
all ratios by one constant and be invisible. It detects exactly the
level-dependent discrepancy the three readings disagree about. The
uniformBody control (spread exactly `1`, exact and float) validates that the
pipeline returns scalar `1` precisely when `K_print = η • K_lane`.

## 2. Hypothesis class: is the witness non-vacuous?

The literal checklist item ("proper nonempty `Omega_0`") does not apply —
this target is a finite matrix model of the weights, with no tower. Its
non-vacuity purpose is served, and I checked each piece:

* All four modelled operators (lane, plainH, draft, linearEta) and the
  uniformBody control are positive definite **in exact rationals** (every
  leading principal minor positive). The design checks this with a
  pivot-product Sylvester test; `attack_check.py` rechecks with the
  fraction-free Bareiss algorithm. Agreement. So the inverses in the first
  term are genuine inverses, never the Lean junk value `0` of
  `Ring.inverse`. This matters: a counterexample that worked only through
  the junk value would refute nothing about the normalisation.
* `rank Q = 4` (full row rank) and `det(Q S^{-1} Q*) ≠ 0` for all five
  operators — now recorded explicitly. In the design script invertibility was
  only implicit (Gauss-Jordan would have raised).
* Both levels carry a nonzero jet and `H* J = (1,1,1,1)` with
  `J = (3/2, 2, 3/2, 1)`, so both levels genuinely enter the cross term —
  the premise "second jet nonzero at two levels" of the variant's docstring
  is met.
* Exact H-invariance: `lam(η • Quad) = lam(Quad)` in rationals. The design
  only float-checked this (`H_invariance_err = 0.0`); the exact check is now
  in `attack_check.py` (PASS). This closes the one place where the exact
  model reused `lam` across readings on the strength of a float check.

## 3. Do the numerical operators match the cited Lean lines?

Every citation was checked against the actual file text:

| script object | cited line | verified content |
|---|---|---|
| `eta = ell^{-k}` | `ZXR2Wire2.lean:37` | `eta := ((P.ell : ℝ) ^ P.k)⁻¹` ✓ |
| `Q_j = ell^{-j} Qlin_j` | `ZXR2Sector.lean:100` (def `QfullOf` :97) | `(ell ^ j)⁻¹ • QlinB` ✓ |
| `C_lane_j = ell^{-j} raw_j` | `ZXR2Sector.lean:111` (def `C2fullOf` :109) | `(ell ^ j)⁻¹ • C2rawB` ✓ |
| mass weight `a * ell^j` | `ZXR2Ops3.lean:99` (def `massW` :98) | `a * (G.ell : ℝ) ^ j`, docstring "d = 3, η-free body" ✓ |
| Mass form | `ZXR2Ops3.lean:112` | `inner_MassFull`: `Σ_p a * ell^j * ‖Qfull A p‖²` ✓ |
| `Quad = Quad0 + Mass` | `R2Algebra.lean:145` | `Ginv = Dpi + Ts∘T + Mass` ✓ (Quad0 stand-in, labelled) |
| `G = Quad⁻¹` | `R2Algebra.lean:147` | `Ring.inverse D.Ginv` ✓ |
| `H = G Q* (Q G Q*)⁻¹` | `R2Algebra.lean:149-150` | verbatim ✓ |
| `K = ⟨A,Quad A⟩ - 2⟨H(CA),J⟩` | `R2Algebra.lean:153` | verbatim (with `‖T A‖²` folded into Quad0, labelled) ✓ |
| `N = Q S⁻¹ Q*` | `ZXG3A.lean:35` | `Nmat = (Q.comp G1).comp Qs` ✓ |
| `firstTerm = η⟨τ*B, N⁻¹ τ*B⟩` | `ZXG3A.lean:50` | verbatim ✓ |
| `τ*` = B at level k, 0 below, no scalar | `ZXG3A.lean:46-49`, `ZGU1D.lean:55,67` | docstring + `tau_adj_apply`/`tau_adj_norm` ✓ |
| `J` at `η = 1`; `JSU2` carries `(η⁻¹)³` | `ZXR2Wire2.lean:51-53`, `ZIngredientJ.lean:111` | verbatim ✓ |

The cross-term assembly in the script (`Sc` with
`⟨A, Sc A⟩ = 2 Σ_b λ_b θ f (v·A)²`, i.e. `C(A)_b = θ f (v·A)²`) matches the
SPEC's description, and the printed-side operator is
`S_ρ = η • Quad_lane − Sc(C_ρ)` exactly as the variant docstring states.
One trivial imprecision, in the design JSON docstring only (SPEC.md is
correct): "`τ* B` ... (ZXG3A.lean:50)" — line 50 is `firstTerm`; the `τ*`
comment is lines 46-49.

## 4. Are the numbers reproducible and the tolerances honest?

Re-ran `first_term_readings.py`: output identical to `out/results.json` and
to every figure in SPEC.md:

* frozen values `14/5, 12/5, 64/5, 27` on the four fields ✓
* plainH `56/57, 48/53, 256/273, 27/28`, spread `371/342` ✓
  (`(56/57)/(48/53) = 2968/2736 = 371/342`, checked by hand)
* draft `14/13, 4/3, 64/53, 9/8`, spread `26/21` ✓ (max `4/3`, min `14/13`)
* linearEta `7/6, 3/2, 4/3, 27/22`, spread `9/7` ✓
* uniformBody `1, 1, 1, 1` ✓
* top-level-only: plainH `1`, draft `29/28`, linearEta `29/26`, all
  B-independent, as claimed ✓
* the three `no_scalar_*` Lean rationals in SPEC.md match the stored printed
  values: plainH `57/20, 53/20`; draft `13/5, 9/5`; linearEta `12/5, 8/5` ✓
* float seed 2: spreads `1.00608 / 1.03028 / 1.11087` at θ=0.02 and
  `1.02688 / 1.12848 / 1.64707` at θ=0.08; lane least eigenvalue `0.9652`
  at θ=0.08 (SPEC says `0.965`) ✓; θ=0 gives spread 1 everywhere ✓
* a_j check: flat first term `1.0` vs `0.8`, relative gap `1/5` ✓
  (`a_2 = 1/(1·2^{-2}+1) = 4/5` verified by hand)

Tolerances: the exact witness uses `fractions.Fraction` throughout — no
tolerance is involved in the headline refutation. The float part uses a
`1e-8` positive-definiteness gate (documented in the code); all eigenvalues
are far above it. The claim "uniformBody stays at 1 exactly" is backed by
the stored float `1.0`, by η = 1/2 being dyadic (scaling exact in binary
floating point), and by the exact rational case. "H residual 0" is the
stored `0.0`. Nothing is smoothed over.

Independent recomputation: `numerics/attack_check.py` re-transcribes the
witness from SPEC.md (no import of the design script) and uses a different
computational path — Bareiss determinants, rank by elimination, Schur values
by solving the saddle-point system `[S Q*; Q 0][x;y] = [0;f]` instead of
forming and inverting `Q S⁻¹ Q*`. 37/37 checks PASS, including the two the
design left implicit (exact H-invariance, recorded `det Nmat ≠ 0` and
`rank Q`). During development this script caught its own transcription bug
(column vs row of `Q^T`) by *disagreeing* with the design — the disagreement
was resolved against numpy and was mine, not the design's; the episode
confirms the two paths are genuinely independent.

## 5. Findings

No fatal or substantive issue. Recorded minors:

1. Design JSON docstring cites `ZXG3A.lean:50` for `τ*`; correct is
   `ZXG3A.lean:46-49` (as SPEC.md has it). Cosmetic.
2. The exact model's reuse of `lam` across readings rested on a float check;
   now backed by an exact rational check (`attack_check.py`).
3. Scope note of section 1: the model has no `Q_1 B = 0` subspace; the
   refutation is of the universal scalar claim. This is the claim the
   normalisation reading needs, but Stage B should keep the variant text as
   stated and not strengthen the English conclusion to "no scalar on any
   subspace".
4. As SPEC.md already discloses ("What this does not close"): a fourth
   reading of (3.14), different from the three powers, is not excluded. The
   attack found no reason to doubt that disclosure's wording.

## 6. Stage B readiness

The plan (`lean/NoScalar.lean`, no frozen-cone imports, explicit 4×4 rational
matrices, leading minors or exhibited inverses, then the three ratio
inequalities) matches what the numerics establish. Two practical notes for
Stage B: exhibiting `M * M⁻¹ = 1` by `norm_num` gives the `IsUnit` witnesses
needed to rewrite `Ring.inverse`; and the frozen/printed rationals to derive
are exactly those listed in section 4 above. The optional
`plainH_top_only_eq` (ratio `1`) is correctly labelled "not a closing of
S-3".

Verdict: **attack fails to break the design.** The prediction "fails" stands
on exact rational evidence, twice reproduced, with honest tolerances and
correct Lean citations.

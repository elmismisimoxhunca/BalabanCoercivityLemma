# s3-normalisation — design

Item 4 / S-3. Evidence only. Nothing below is a theorem. No Lean was run.

**Prediction: fails.** None of the three page readings of the η placement makes the frozen first term a scalar multiple of the printed first term, with the scalar independent of the test field, once the second jet is nonzero at two levels. Stage B should formalise that counterexample. A uniform factor η on the whole cross term does match with scalar 1, but that factor is not what the pages give at every level.

## What is being compared

Frozen first term, `ZXG3A.lean:50`:

```lean
P.eta * ⟪τ* B, Ring.inverse (Nmat P) (τ* B)⟫
```

with `P.eta = ((ell : ℝ) ^ k)⁻¹` (`ZXR2Wire2.lean:37`) and `Nmat = Q ∘ G1 ∘ Q*` (`ZXG3A.lean:35`). The comment at `ZXG3A.lean:46-49` says `τ*` puts `B` at level `k` with no scalar, and that the external `η` is there because `G1in = η⁻¹ • ι • G1 • pE` (`ZXR2Wire2.lean:82-84`). `τ*` copies values on full support (`ZGU1D.lean:55`, norm `ZGU1D.lean:67`).

Printed `(3.156)` (`sources/corpus/pages/CMP99b_p428.md`) is

```latex
\langle B,(QG_1Q^*)^{-1}B\rangle - a\langle B,B\rangle - 2\langle H_1\tilde D^{(2)}(B),J\rangle
```

with no `η` and no `τ`. `(3.157)` on the same page is the Gaussian integral for `C^{(k)}(Λ)`. It also has no `η`. It does not fix the scalar in front of the first term.

The first term is the Schur complement of `K` (`R2Algebra.lean:153`):

```lean
K A = ⟪A, Dpi A⟫ - 2 * ⟪H (C2 A), J⟫ + ‖T A‖^2 + ⟪A, Mass A⟫
```

`H = G Q* (Q G Q*)⁻¹` (`R2Algebra.lean:149-150`), `G = Ginv⁻¹` (`:147`), `Ginv = Dpi + Ts∘T + Mass` (`:145`). The value on `f = τ* B` is `⟨f, (Q K⁻¹ Q*)⁻¹ f⟩`. The frozen first term multiplies that by `η`.

Lane weights the model copies:

| piece | formula | Lean |
|---|---|---|
| `Q_j` | `ell^{-j} • Qlin_j` | `ZXR2Sector.lean:100` (`QfullOf` at `:97`) |
| `C_j` | `ell^{-j} • raw_j` | `ZXR2Sector.lean:111` (`C2fullOf` at `:109`) |
| mass weight | `a * ell^j` (`d = 3`) | `ZXR2Ops3.lean:99` (`massW` at `:98`) |
| mass form | `Σ weight ‖Q A‖²` | `ZXR2Ops3.lean:112` |
| source | `J` at `η = 1` | `ZXR2Wire2.lean:52` (`JSU2Loc 1`) |
| `JSU2 η` | factor `(η⁻¹)^3` | `ZIngredientJ.lean:111` |

`Quad0`, the stand-in for `Dpi + Ts∘T`, is the identity in both models. It is not `gradCovariant`. The jets `Qlin` and `raw` are stand-ins for `QlinB` and `C2rawB`. A universal scalar identity for these weights would have to hold for every full-rank jet, including these.

`H` is unchanged when `Quad` is replaced by `η • Quad` and `Q` is held fixed (the inverse and the constraint inverse cancel). The float check records this residual as `0`. So the three readings differ only by how they build `C` from `raw`.

## Three readings, pinned to the pages

Same `Q` as the lane (the linear term of `(3.14)` is `L^{-j} Dq`, which is what `QfullOf` stores). Same quadratic part `Quad_print = η • Quad_lane`: `R2Ops1` says `Δ`, `DRD*` and `Q*aQ` are the η-free bodies with `η^{d-2}` divided out, and at `d = 3` that factor is `η`. Printed bond mass is `(3.16)` (`CMP99b_p393.md`): `a (L^j η)^{d-2} |Q_j A|² = η • (a L^j |Q_j A|²)`.

The cross term is the part the three readings split. Let `raw_j(A) = ½ D²q_j(0)(A,A)`, the η-free second jet (`C2rawB`).

**plainH (top-level power `η^{-1}`).** `(3.14)` on `CMP99b_p393.md`:

```latex
\frac{1}{L^j\eta} Q_j(U,\eta A) = Q_j(U)A + \frac{1}{L^j\eta} C_j(U, L^j\eta A).
```

Taylor in the dimensionless field: `Q_j(U, ηA) = η Dq·A + η² raw + ⋯`. The second-order piece of the left side is `η L^{-j} raw`. p.421 (`CMP99b_p421.md`), the plain-`H` sentence before `(3.128)`: take `H` as in `(3.126)`, and then `C^{(2)}(A) = L^j η C_j^{(2)}(A)` on `Λ_j`. That product is `η² raw`, at every level. The code stores `L^{-j} raw`. At the top level `j = k` only, `L^{-k} = η`, so `(stored) / (printed) = η / η² = η^{-1}`. The `(3.11)` pairing weight `η^d` (`CMP99b_p392.md`) times the `η^{-3}` in `JSU2` cancels at `d = 3`, so no further power. Assembly: `C_j = η² raw_j`.

**draft (power `1`).** The unweighted pairing against `JSU2Loc 1` already equals the printed pairing at `d = 3`, and this reading takes the field being paired to be the stored `C2fullOf`, with no further `η`. Assembly: `C_j = L^{-j} raw_j`. This is the reading behind the rejected headline in `AHP/attempts/s3-eta-tau/`.

**linearEta (top-level power `η`).** The other placement of the single `η` in `(3.14)`: `η` sits on the linear jet only, the second jet is the η-free `raw`, and the plain-`H` factor `L^j η` cancels the denominator. Then `C^{(2)} = raw`. At `j = k`, `(stored) / (printed) = η`. Assembly: `C_j = raw_j`.

`(3.136)` (`CMP99b_p422.md`) multiplies by `(L^j η)^{d+1}`. At `j = k` that weight is `1`, so it does not choose among the three powers. At `j < k` it is another level-dependent factor, not a fourth global power. `(3.24)` (`CMP99b_p394.md`) is the site recursion `a_1 = a_0 = a`, `a_{j+1} = a a_j / (a L^{-2} + a_j)`. `(3.128)` and `(3.16)` use a constant `a`. It is not one of the three readings. On a diagonal flat model (`k = 2`, `ell = 2`, `Quad0 = 0`, `Q_j = ell^{-j}` on coordinate `j`, `B = 1` at the top) the frozen flat first term is `1` with constant `a` and `0.8` if level 2 uses `a_2 = 4/5`. Relative gap `1/5`.

**Not a fourth page reading.** The control `uniformBody` sets `C_j = η • (stored C_j) = η L^{-j} raw_j`, i.e. one global factor on the cross term, the same factor as on `Quad`. Then `K_print = η K_lane` and the frozen first term equals the printed one with scalar `1`. That is what the external `η` was written to do (`ZXG3A.lean:46-49`). It is not the plain-H Taylor formula above: `η² raw` equals `η L^{-j} raw` for every `j` only if `L^{-j} = η` for every `j`, i.e. only at `j = k`.

## Numerical method

Script: `AHP/fidelity/s3-normalisation/numerics/first_term_readings.py`. Output: `AHP/fidelity/s3-normalisation/numerics/out/results.json`.

For each reading, build `S` with `⟨A, S A⟩ = K(A)`, require every leading principal minor positive, embed `B` by `τ*` (zeros below level `k`, no scalar), and compute

```text
frozen  = η * ⟨τ* B, (Q S_lane^{-1} Q*)^{-1} τ* B⟩
printed =     ⟨τ* B, (Q S_print^{-1} Q*)^{-1} τ* B⟩
```

A reading "matches up to a scalar" only if `frozen / printed` is the same rational for every listed `B`, and that rational does not depend on the non-flat strength. Flat background (`raw = 0`) makes every ratio `1`. It cannot separate the readings. Sol's verdict already says the flat reduction cannot see this, because `J` vanishes.

### Exact witness (the counterexample)

`ell = 2`, `k = 1`, `η = 1/2`, `a = 1`, `θ = 1/10`. Four fine coordinates, two bonds per level. Rational arithmetic (`fractions.Fraction`), not floats.

```text
Qlin_0 = [[1, 0, 1, 0], [0, 1, 0, 1]]
Qlin_1 = [[1, 1, 0, 0], [0, 1, 1, 0]]
Q_j    = ell^{-j} Qlin_j
Quad0  = I_4
J      = (3/2, 2, 3/2, 1)     so that H* J = (1, 1, 1, 1)
```

Both levels of `H* J` are nonzero, so both jets enter `K`. Rank-one raw jets, scaled by `θ`:

```text
level 0:  v = (1,0,0,0) and (0,1,1,0)
level 1:  v = (0,0,1,0) and (1,0,1,1)
```

`C(A)_b = θ • (factor) • (v·A)²`. All four operators (`lane`, `plainH`, `draft`, `linearEta`) have positive leading minors.

Both levels active. Frozen value is the same for every reading (`14/5`, `12/5`, `64/5`, `27` on the four fields). Printed values are not a fixed multiple of it:

| `B` | plainH | draft | linearEta | uniformBody |
|---|---|---|---|---|
| `(1, 0)` | `56/57` | `14/13` | `7/6` | `1` |
| `(0, 1)` | `48/53` | `4/3` | `3/2` | `1` |
| `(1, 2)` | `256/273` | `64/53` | `4/3` | `1` |
| `(3, -1)` | `27/28` | `9/8` | `27/22` | `1` |
| one scalar? | no, spread `371/342` | no, spread `26/21` | no, spread `9/7` | yes, scalar `1` |

So `56/57 ≠ 48/53`, `14/13 ≠ 4/3`, and `7/6 ≠ 3/2`. No stated scalar works for any of the three readings.

Top level only (level-0 raw set to `0`, same `Q`, `J`, `θ`). This is the situation in which plainH's power really is the global factor `η^{-1}`:

| reading | ratio on every `B` |
|---|---|
| plainH | `1` |
| draft | `29/28` |
| linearEta | `29/26` |
| uniformBody | `1` |

plainH matches here, with scalar `1`. draft and linearEta are constant in `B` on this particular jet, but the constants are not `1` and are not functions of `η` alone: at `θ = 0` every ratio is `1`, while `29/28 ≠ 1`. Turning on the lower jet destroys even the `B`-independence.

### Float check

Seed 2, `k = 1`, `ell = 2`, `η = 1/2`, six coordinates, two bonds per level, random full jets, eight random `B`. Same assemblies. `H` residual `0`.

| `θ` | plainH spread | draft spread | linearEta spread | uniformBody |
|---|---|---|---|---|
| `0` | `1` (ratio `1`) | `1` | `1` | `1` |
| `0.02` | `1.00608` | `1.03028` | `1.11087` | `1` exactly |
| `0.08` | `1.02688` | `1.12848` | `1.64707` | `1` exactly |

Same split as the exact witness. At `θ = 0.08` the lane form is still positive definite (least eigenvalue `0.965`). uniformBody stays at `1` to the printed digits; the three page readings do not.

## Variant the numbers refute

```lean
/-- Claim under test. Expected false once both levels carry a second jet.
`S_lane` is the symmetric operator of `K` with `C_j = ell^{-j} • raw_j`
and mass weight `a * ell^j`. `S_ρ` uses the same `Q` and `Quad_print = η • Quad_lane`,
and `C` from one of `plainH` / `draft` / `linearEta` as pinned in SPEC.md.
`τ* B` is `B` at level `k` and `0` below. -/
def FirstTermScalarClaim (ρ : Reading) : Prop :=
  ∃ c : ℚ, ∀ B : Fin 2 → ℚ,
    eta * schur S_lane (tauStar B) = c * schur (S ρ) (tauStar B)
```

Refutation on the witness above, for each `ρ`:

```lean
def no_scalar_plainH : Prop :=
  ((14 / 5 : ℚ) / (57 / 20)) ≠ ((12 / 5) / (53 / 20))

def no_scalar_draft : Prop :=
  ((14 / 5 : ℚ) / (13 / 5)) ≠ ((12 / 5) / (9 / 5))

def no_scalar_linearEta : Prop :=
  ((14 / 5 : ℚ) / (12 / 5)) ≠ ((12 / 5) / (8 / 5))
```

Those three inequalities are the pairs `B = (1,0)` and `B = (0,1)`. They are not the proof. Stage B has to derive the four rationals from the matrices, then close the inequalities.

The matching control, not a page reading:

```lean
/-- If `C_print = η • C_lane` at every level and `Quad_print = η • Quad_lane`,
then `S_print = η • S_lane` and the external `η` cancels. Scalar `1`.
This is the algebra of `G1in` (`ZXR2Wire2.lean:82`), not (3.14)+(p.421) at `j < k`. -/
def uniform_body_cancels : Prop :=
  ∀ B, eta * schur S_lane (tauStar B) = schur (eta • S_lane) (tauStar B)
```

## Stage B

Write `AHP/fidelity/s3-normalisation/lean/NoScalar.lean`. Do not import the frozen cone. The three readings are not definitions in `lean/`. Copy the weight formulas and cite the lines above in comments.

Imports:

```lean
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
```

Declarations:

1. The matrices `Q0`, `Q1`, `Q`, `Quad`, `J`, `raw`, `θ = 1/10`, over `ℚ`.
2. `S_lane`, `S_plainH`, `S_draft`, `S_linearEta` by the formulas in this note.
3. Positive-definiteness of each `S` (leading minors, or an exhibited inverse with `M * M⁻¹ = 1` by `norm_num`).
4. `no_scalar_plainH_of_witness`, `no_scalar_draft_of_witness`, `no_scalar_linearEta_of_witness`: the two ratios differ. Compute the Schur values by exhibiting the inverses, not by quoting this note.
5. Optional, and not a closing of S-3: `plainH_top_only_eq`, the same data with the level-0 jet zero, ratio `1`.

Check, after `REPRODUCE.sh` has finished and without editing `lean/`, `paper/`, `notes/`, `expected/`, or the lakefile:

```text
lake env lean AHP/fidelity/s3-normalisation/lean/NoScalar.lean
```

then `#print axioms` on each declaration. Accept only `propext`, `Classical.choice`, `Quot.sound`, or a subset. No `sorryAx`.

What this does not close: whether some other reading of `(3.14)`, different from these three, makes `K_print = η • K_lane` on a real `LinkCfg`. The uniform-body algebra does that, and the code comment describes `C2fullOf` as an η-free body, but the Taylor count on p.393 and p.421 does not agree with `L^{-j}` at levels `j < k`. That remaining gap is a reading of the header against the page, not a scalar identity of the three powers.

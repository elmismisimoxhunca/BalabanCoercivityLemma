# sheet-variants — statement-sheet alternatives (stage A)

Item 6, testable part. Each yes/no question in `notes/statement_sheet.tex` is named Qn for clause An. This file writes the formal alternative, says how it sits relative to the frozen `P428Target8` (`lean/src/ZT5A.lean:291`), and records what the small-torus checks showed. Nothing below is a new proof. Existing Lean declarations are named as such. Script output is evidence about predicates and about one matrix identity.

Question map, and what this file does with each:

| id | sheet question | here |
|---|---|---|
| Q1 | A1, periodic \(l^1\), dimension 3, torus sides | convention, no variant |
| Q2(a) | big-block side \(M\ell^j\) | same geometry as reading A; the coarser block is Q3 |
| Q2(b) | strict collar | variant below; inequality open |
| Q3 | \(T_1\) = fine lattice | reading B |
| Q4 | same \(R\) for the unit collar | reading B's site-radius, plus the embedding identity |
| Q5 | one cube factor, boxes | already proved elsewhere; not reopened |
| Q6(a) | gauge inside "for every cube" | global-gauge variant |
| Q6(b) | both endpoints | not repeated (target `s1-touching`) |
| Q7 | coverage | not repeated (target `coverage-row`) |
| Q8, Q10, Q11 | operators, chain, \(C\) | reading-only (target `sheet-reading`) |
| Q9 | plaquette selection | not repeated (literal refutations and target `guarded`) |
| Q12 | trace-normalised norm | factor 2, equivalent after rescaling \(\gamma_0\) |
| Q13 | quantifier order | compared with `P428Target8Total` |

Aggregate prediction: **unknown**. The items do not share one status. Per item: Q1 convention; Q2(b) the non-strict statement implies the frozen one and is not known to hold; Q3 neither implication, and the reading-B statement is a restriction of the already-proved `Target8Layer`; Q4 the unit/fine collars agree under the embedding; Q6(a) frozen implies the variant, not conversely; Q12 equivalent; Q13 `P428Target8Total` implies the frozen statement, not conversely, and both are already proved.

## Q1 — convention, no variant

Sheet A1 asks whether a 3-torus, \(\eta=\ell^{-k}\), periodic \(l^1\) distance, and sides divisible by \(\ell\) and \(M\) are acceptable. The frozen distance is `pdist` (`ZStatementP428.lean:66`), whose comment says the circular wrap is not printed. `TorusOK` is `ZStatementP428.lean:286`. Dimension 3 and \(SU(2)\) are the whole development.

No alternative is reasonable to prove beside the frozen statement. A different dimension or group is a different formalisation, not a variant of this lemma. Changing only the wrap would drop the torus. **Classification: convention. No stage-B file.**

## Q2(b) — non-strict collar

Print (CMP96 (2.2), as transcribed at `RB1.lean` and matched by `collar_iff_rat`): distance strictly greater than \(RM\). Frozen conjunct, `Admissible` at `ZStatementP428.lean:78-79`:

```text
x ∉ S.Om j → ∀ y ∈ S.Om (j+1), R * bigSide M ell j < pdist x y
```

`bigSide` is `ZStatementP428.lean:51`. On naturals, `R * bigSide < pdist` is one site stronger than `R * bigSide ≤ pdist`.

### Variant

```lean
def AdmissibleNonStrict {L : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j, k < j → S.Om j = ∅) ∧
  (∀ j, j ≤ k → ∀ μ, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j, j ≤ k → ∀ x, x ∉ S.Om j → ∀ y ∈ S.Om (j + 1),
      R * bigSide M ell j ≤ pdist x y) ∧
  (∀ x, x ∈ S.Om 0 ↔
      ∃ y ∈ S.Om 1, ∃ z, (∀ μ, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M)

def CoercG8AtNonStrict (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ S, AdmissibleNonStrict ell M R k S →
  ∀ Lam, LambdaOK2 ell M R k S Lam →
  ∀ U, ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneq ell k hell a Lu γ₀ S Lam U

def P428Target8_NonStrict : Prop :=
  ∀ ell, 2 ≤ ell → ∀ a, 0 < a →
    ∃ m₀, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∃ R₀, ∀ R, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
        ∃ a₀, 0 < a₀ ∧ ∃ γ₀, 0 < γ₀ ∧
          ∀ k, 1 ≤ k → ∀ Lu α₀, 0 < α₀ →
            (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
              CoercG8AtNonStrict ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀
```

Same binders as `P428Target8`. Only the collar atom changes from `<` to `≤`.

### Relationship

- Every strict tower is non-strict, because `n < d` implies `n ≤ d`. So the non-strict hypothesis class contains the frozen one.
- Therefore the implication **`P428Target8_NonStrict → P428Target8` is provable from the class inclusion alone**, without proving either coercivity statement. The frozen statement does **not** imply the non-strict one unless the two classes agree, which they do not as predicates.
- They are not equivalent as predicates. They are not known to be equivalent under the headline constraint \(M=\ell^m\), \(\ell\ge 2\).
- The inequality itself is **not** claimed true and **not** claimed false. A one-site thinner collar at levels \(j\ge 1\) is not the same data as `Admissible` at radius \(R-1\): clause 6 still uses radius \(R\), and `LambdaOK2` still uses \(R\). Quoting the frozen theorem at \(R-1\) does not discharge it.

Clause 6 already forces the **level-0** collar to be strict. That is the existing Lean theorem `om0Print_collar` (`RB2.lean:76`). So at \(k=1\), where the level-1 collar quantifies over the empty `Ω₂`, the two predicates agree on any tower that keeps clause 6. The gap, if it is inhabited at headline sizes, sits at some \(1\le j<k\).

### Numerics

Script `numerics/sheet_variants.py`, distance transcribed from `pdist` / `pcd` (`ZStatementP428.lean:57-71`). Side 8. Evidence, not a proof.

1. **Predicate separator, outside the headline.** `ell=2`, `M=1`, `R=1`, `k=2`, side 8. `M=1` is not \(\ell^m\) for \(\ell\ge 2\). `Ω₂ = [0,4)³` (64 sites), `Ω₁` omits the single side-2 block `[4,6)×[4,6)×[0,2)`, `Ω₀` is the whole torus. The script checks nesting, emptiness above \(k\), divisibility, block closure, and clause 6. Strict collar fails and non-strict collar holds. Witness: `j=1`, \(x=(4,4,0)\), \(y=(3,3,0)\), distance \(2\), radius \(2\). So `AdmissibleNonStrict` does not imply `Admissible` as a predicate on all `M`.
2. **Level 0 stays strict.** `Om0Print` for `M=2`, `R=1`, `Ω₁={0}` has 80 sites, and the complement is at distance 3 from `Ω₁`. Radius `R*M=2`, so the strict collar holds. This matches `om0Print_collar`; it is not a new fact.
3. **No in-regime separator fits on side ≤ 8.** Smallest headline parameters with \(k\ge 2\) are `ell=2`, `M=2`, `k=2`. Then `bigSide` at level 2 is 8, so on a side-8 torus a block-closed `Ω₂` is empty or the whole torus. A nonempty proper level-2 block needs a larger side. Not run (side cap 8).

### Stage B

File `AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean`.

Imports: `ZT5A` (brings `Admissible`, `InstIneq`, `P428Target8`, `SidePow6`, `TorusOK`, `LambdaOK2`, `ClassCoupled`).

Declarations to compile, not to treat as a proof of the inequality:

- `AdmissibleNonStrict`, `CoercG8AtNonStrict`, `P428Target8_NonStrict` as above.
- `admissible_imp_nonstrict : Admissible ell M R k S → AdmissibleNonStrict ell M R k S`.
- `nonstrict_target_imp_frozen : P428Target8_NonStrict → P428Target8`.
- A concrete separator at `M=1` (the tower above), proved by hand or by `decide` on the finite side-8 facts. Do not use `native_decide`. State the disclosure: `M=1` is outside `SidePow6`.
- Do **not** assert `P428Target8_NonStrict`. Leave the inequality open.

Expected axioms of the comparison lemmas: `propext`, `Classical.choice`, `Quot.sound`, or a subset. Check with `#print axioms`.

## Q3 and Q4 — reading B of \(T_1\)

Sheet A3: is \(T_1\) on p.396 the fine lattice (blocks of \(M\) fine sites, radius \(RM\) fine sites)? Reading A says yes. Reading B takes \(T_1\) as the level-\(k\) unit lattice: blocks of side \(M\ell^k\), radius \(R\cdot M\ell^k\). That set is `Om0Unit` (`RB2.lean:41`). Reading A is `Om0Print` (`RB1.lean:59`). `admissible_iff_print` (`RB1.lean:185`) identifies `Admissible` with the printed tower under reading A, for `ell>0`, `M>0`, plus empty padding.

Sheet A4 asks whether "\(RM\)" in the unit-lattice collar is the same \(R\) as in (2.2). Two different comparisons get mixed here:

- Reading B keeps the **symbol** \(R\) but measures the base-law radius in coarser units. In fine sites that radius is \(\ell^k\) times the level-0 collar radius \(RM\).
- `LambdaOK` (`ZStatementP428.lean:189-195`) uses `R * M < pdist` on the **unit** torus, with `emb(y)μ = ell^k * yμ`. The level-\(k\) fine collar uses radius `R * bigSide M ell k = R * M * ell^k`. Those are the same \(R\) if distance scales by \(\ell^k\).

Sol, `SolRBridgeAudit.lean`: `readingB_satisfies_collar` (line 8) says `Om0Unit` satisfies the **fine** `Collar0 M R` (`RB2.lean:45`); `readingB_fine_blockClosed` (line 15) says it is `BlockClosed M`; `readingB_strictly_larger` (line 24) says \(x_{400}=(4,0,0)\) lies in `Om0Unit 2 2 1 1` and not in `Om0Print 2 1`, on the side-8 torus `Lw`. OPEN_ITEMS R-a: (2.2) does not exclude reading B. Those three are Lean theorems in the audit module. This note does not re-prove them.

### Variant

```lean
def ReadingBTower {L : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower L) : Prop :=
  AdmNoBase ell M R k S ∧
  S.Om 0 = Om0Unit ell M R k (S.Om 1)

def P428Target8_ReadingB : Prop :=
  ∀ ell, 2 ≤ ell → ∀ a, 0 < a →
    ∃ m₀, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m → ∃ R₀, ∀ R, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧
        ∃ a₀, 0 < a₀ ∧ ∃ γ₀, 0 < γ₀ ∧
          ∀ k, 1 ≤ k → ∀ Lu α₀, 0 < α₀ →
            (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
              TorusOK ell (ell ^ m) Lu →
              ∀ S, ReadingBTower ell (ell ^ m) R k S →
              ∀ Lam, LambdaOK2 ell (ell ^ m) R k S Lam →
              ∀ U, ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
                InstIneq ell k (by omega) a Lu γ₀ S Lam U
```

`AdmNoBase` is `THL2.lean:23`: the first five conjuncts of `Admissible`, strict collar kept, clause 6 dropped. `ReadingBTower` puts reading B's base law back as an equation.

### Relationship

- **Neither statement implies the other.** A reading-B tower has `Ω₀ = Om0Unit`, while `Admissible` has `Ω₀ = Om0Print`. Sol's `readingB_strictly_larger` separates those two sets, so a tower with the reading-B base law fails clause 6. A frozen tower has the small base law, so it fails the reading-B equation whenever the two sets differ.
- **Not equivalent.**
- **`Target8Layer` implies `P428Target8_ReadingB`.** `Target8Layer` (`THL6.lean:164`) is a proved Lean theorem (`target8Layer`, same file) with the same outer binders, quantifying over every `AdmNoBase` tower. `ReadingBTower` adds an equation, so it is a smaller class. The restriction is logic, not a new estimate. It is not an implication from the frozen `P428Target8` alone: the frozen statement quantifies only over `Admissible`.
- Not "likely false". The comparison above is the reason to expect the reading-B **statement** to hold. That expectation is only as strong as `target8Layer`, which is already a Lean theorem, plus the one-line restriction. It is not a numerical extrapolation.

### Vacuity, checked on side 8

`Om0Unit` can be strictly larger and still be a bad witness.

- Sol's parameters `ell=2`, `M=2`, `R=1`, `k=1`, side 8, `Ω₁={0}`: `|Om0Print|=80`, `|Om0Unit|=512` (the whole torus). \(x_{400}\) is in the difference, as Sol states. `Collar0` holds because the complement is empty. The collar theorem is true there and gives no boundary.
- Same sizes with `Ω₁=[0,4)³`, which is one block of side `M ell = 4`, so the level-1 block law can hold: `|Om0Unit|=512`, `|Om0Print|=448`, `Ω₁` sits in both, complement of `Om0Print` has minimum distance 3. Geometry of `AdmNoBase` can hold with `Ω₀` the whole torus and clause 6 failing. **Proper** `Ω₀` (nonempty and not the torus) does not occur for these headline sizes at `R≥1` on side 8: every side-4 block meets the radius-4 neighbourhood of a nonempty `Ω₁`.
- Below the headline, `M=1`, `ell=2`, `R=1`, `k=1`, side 8, `Ω₁={0}`: `|Om0Print|=7`, `|Om0Unit|=80`, \((4,4,4)\) is outside `Om0Unit`, \((2,0,0)\) is in `Om0Unit` and not in `Om0Print`. Minimum distance from the complement of `Om0Unit` to `Ω₁` is 3, so the fine collar of radius `R*M=1` holds with a nonempty complement. This shows the geometry can be proper. It is not a `SidePow6` tower.

So: do not cite the side-8 headline witness as a proper domain. Do not call `P428Target8_ReadingB` non-vacuous. `ClassCoupled` on the full-torus witness was not built. The implication from `Target8Layer` remains valid even if every proper reading-B tower were absent; a stage-B note has to say that.

### Q4 embedding, same \(R\)

Separate small check, not reading B. For `ell=2`, `k=1`, `M=2`, `R=3`, unit side 4, fine side 8, all \(4^3\cdot 4^3 = 4096\) pairs of unit sites: `pdist_fine(emb y, emb z) = ell^k * pdist_unit(y,z)`, and `R*M < pdist_unit` agrees with `R*M*ell^k < pdist_fine`. Zero mismatches. This is evidence for an identity, not a proof.

### Variant (identity, not a new headline)

```lean
theorem pdist_emb_scales {Lu : PeriodicLatticeExtent} (ell k : ℕ) (hk : 0 < ell ^ k)
    (y z : PeriodicLatticeSite Lu) :
    pdist (emb ell k y) (emb ell k z) = ell ^ k * pdist y z
```

with `emb` the map in `LambdaOK` (`ZStatementP428.lean:192`). Consequence to state in the same file: the unit atom `R * M < pdist y y'` is equivalent to the fine atom `R * bigSide M ell k < pdist (emb y) (emb y')`. **The two collars agree. Same \(R\).** This does not choose reading B.

### Stage B

File `AHP/fidelity/sheet-variants/lean/ReadingB.lean`.

Imports: `THL6` (for `Target8Layer`, `target8Layer`, `AdmNoBase` via `THL2`), `RB2` (for `Om0Unit`). `SolRBridgeAudit` only if the file also re-exports Sol's three theorems; it is not required for the restriction.

Declarations:

- `ReadingBTower`, `P428Target8_ReadingB`.
- `readingB_of_layer : Target8Layer → P428Target8_ReadingB`.
- `readingB_not_admissible_side8`: the full-torus witness (`Ω₁=[0,4)³`, `Ω₀` everything, `ell=M=2`, `R=k=1`) satisfies `ReadingBTower` and fails clause 6. Disclosure: `Ω₀` is not a proper subset.
- Do not claim a proper in-regime `Ω₀`. A proper-domain lemma needs a larger torus and is out of this stage's numerics.

File `AHP/fidelity/sheet-variants/lean/LambdaScale.lean`.

Imports: `ZStatementP428`.

Declaration: `pdist_emb_scales` and the iff of the two collar atoms. Expected outcome: proved, axioms among the three standard ones.

## Q5 — already proved, not reopened

The sheet's alternative to one factor \(c=12\) and to boxes is already in the tree:

- `P428Genuine8AllC` (`ZT5A.lean:257`): every \(c\ge 10\), constants may depend on \(c\). `P428Genuine8AllC.toHead` instantiates \(c=12\).
- `P428Target8Total` (`TT_F.lean:29`): constants before \(c\ge 10\). Implies the frozen headline (`toTarget`, line 70).
- `P428Target8FamilyTorus` (`MXQ_Tor.lean:58`): each cube its own factor.
- `P428Target8FamilyTorusU` (`UNI_Tor.lean:73`): unions of blocks.

Acceptability of "one factor and boxes" remains a reading question for the owner. No new variant, no numerics.

## Q6(a) — one global gauge

`PerCubeRegular2` (`ZR2A.lean:47-68`) has `∃ g, ∃ A` **inside** `∀` class cube. The print (sheet A6) has the same order: for each cube there exists a gauge on that cube. The alternative pulls one gauge out.

### Variant

```lean
def GlobalRegular {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
    ∀ sites j, IsClassCube ell M f k S sites j →
      ∃ A : Bond L → Matrix (Fin 2) (Fin 2) ℂ,
        -- same three blocks as PerCubeRegular2 (ZR2A.lean:52-68), with this g
        True

def ClassCoupledGlobal {L : PeriodicLatticeExtent}
    (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ GlobalRegular ell M c k S α₀ η U

def P428Target8_Global : Prop :=
  -- binders identical to P428Target8 / CoercG8At, with ClassCoupled replaced by ClassCoupledGlobal
  True
```

The `True` placeholders are the transcribed bounds, not a different estimate. Stage B should copy `ZR2A.lean:52-68` with the quantifiers swapped, not invent a new smallness.

### Relationship

- `GlobalRegular → PerCubeRegular2`: instantiate the same `g` at each cube. Pure quantifier logic.
- Therefore **the frozen theorem implies `P428Target8_Global`**. The global hypothesis class is smaller, so the claim is weaker.
- **Not conversely, and not equivalent**, as quantifiers. The converse is not a theorem of the quantifier order.
- Not false: it is the weaker claim. Flat \(U=1\) is gauged by \(g=1\) on every cube at once, so the smaller class still contains the flat configurations already in the frozen class. The variant is not an empty hypothesis.

### Numerics

The gauge formula is `periodicGaugeTransform` (`ClayStatement.lean:1312-1316`): \(\gamma(x)\, U(x,\mu)\, \gamma(x+\mu)^{-1}\). The script uses that formula on a 4-cycle, links \(I,I,I,-I\), with matrices in \(\{\pm I\}\subset SU(2)\). A "cube" in the script is a **2-bond arc, not an `IsClassCube`**. Do not read the numbers as a class-cube counterexample.

- Holonomy of the cycle is \(-I\).
- Each of the four arcs has a gauge (values in \(\{\pm I\}\)) making those two links equal to \(I\).
- Propagating a single gauge around the cycle returns \(g_0\cdot(-I)\), not \(g_0\).
- For any gauge, the gauged holonomy is conjugate to \(-I\). In this central subgroup the conjugate is \(-I\) itself, which is not \(I\). So no global gauge flattens every link, while each arc has its own gauge.

That separates `∀ arc ∃ g` from `∃ g ∀ arc` for this formula. It does not exhibit an `IsClassCube` configuration in `PerCubeRegular2` but not `GlobalRegular`. Stage B's one-way implication does not need such a configuration. A Lean counterexample to equivalence inside `IsClassCube` is optional and was not found here.

### Stage B

File `AHP/fidelity/sheet-variants/lean/GlobalGauge.lean`.

Imports: `ZT5A` (reaches `PerCubeRegular2` and `ClassCoupled`).

Declarations:

- `GlobalRegular`, `ClassCoupledGlobal`, `P428Target8_Global`, with the bounds copied from `ZR2A.lean:52-68`.
- `global_imp_perCube : GlobalRegular … U → PerCubeRegular2 … U`.
- `frozen_imp_global : P428Target8 → P428Target8_Global`.
- Do not claim the converse. Optional, only if a real class-cube witness is written by hand: `¬ (∀ U, PerCubeRegular2 … U → GlobalRegular … U)` on a named finite configuration. The 4-cycle is not that witness.

## Q12 — Hilbert–Schmidt versus trace-normalised

Two different norms are in play. Do not mix them.

**Lower bound (this question).** Sheet A12. `bondEnergy` (`RegularUPerturbation.lean:355`) is \(\sum_b \|B(b)\|^2\). On `SuTwo`, `norm_sq_eq_half_frobSq` (`RMapLipschitz.lean:145`) is \(\|Y\|^2 = \tfrac12 \mathrm{frobSq}(Y)\), and `frobSq` (`RMapLipschitz.lean:60`) is \(\sum_{ij}|Y_{ij}|^2\). `hsInner` (`SuTwoInner.lean:104`) is \(-\tfrac12 \mathrm{Tr}(XY)\) on the anti-hermitian carrier, and `hsInner_self_eq_sumNormSq` identifies it with \(\tfrac12\sum|X_{ij}|^2\). The module comment records the printed sentences: Hilbert–Schmidt \(|X|^2=\mathrm{tr}\, X^*X\) with \(\mathrm{tr}\, 1=1\), so the printed squared norm is \(\tfrac12 \mathrm{Tr}(X^*X)=\|X\|^2\). The frozen lower bound already uses the trace-normalised norm.

The alternative "drop the normalisation" uses the un-normalised square `frobSq = 2 \|·\|^2`.

**Class bound (not this question).** `PerCubeRegular2` bounds `frobNorm = sqrt(frobSq)` (`RMapLipschitz.lean:136`), which is \(\sqrt 2\) times the printed norm. That factor is absorbed in \(\alpha_0\), not in \(\gamma_0\). Deviation \(\sqrt 2\). Leave it alone.

### Variant

```lean
noncomputable def bondEnergyHS {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, frobSq (A b : Matrix (Fin 2) (Fin 2) ℂ)

def InstIneqHS (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu))
    (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ Bt, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergyHS Bt ≤
      GenP.genForm (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

def P428Target8_HS : Prop :=
  -- same binders as P428Target8, with InstIneq replaced by InstIneqHS
  True
```

### Relationship

**Equivalent**, because \(\gamma_0\) is existential and the factor does not depend on the field.

- `bondEnergyHS Bt = 2 * bondEnergy Bt` for every `Bt`, by `norm_sq_eq_half_frobSq` summed over bonds.
- If `γ * bondEnergy ≤ form` then `(γ/2) * bondEnergyHS ≤ form`, and conversely.
- The same \(\gamma_0\) is used for every torus, tower, \(U\) and \(\tilde B\). Dividing by 2 preserves that uniformity. So **`P428Target8` and `P428Target8_HS` imply each other.**

The quadratic form inside `genForm` is not changed. Only the norm on the left of `InstIneq` (`ZT5A.lean:56-63`) changes.

### Numerics

Entrywise check of the factor, on the family \(X=\begin{pmatrix} ia & b+ic \\ -b+ic & -ia \end{pmatrix}\) (traceless and skew-hermitian) at \((a,b,c)\in\{(1,0,0),(0,1,0),(0,0,1),(2,-3,5),(0,0,0),(1,1,1)\}\): `frobSq = 2 * (a²+b²+c²)` in every case, including zero. The three Pauli generators \(i\sigma_k\), as in `SuTwoInner.lean:506-522`, each have `frobSq = 2` and `hsInner = 1`. On three sample bonds with \(\gamma=6\), the printed left side is 48 and the un-normalised left side with \(\gamma/2\) is 48. Evidence for the constant, not a substitute for `norm_sq_eq_half_frobSq`.

### Stage B

File `AHP/fidelity/sheet-variants/lean/NormHS.lean`.

Imports: `ZT5A`, `AdalyFormal.Balaban.RMapLipschitz`.

Declarations:

- `bondEnergyHS`, `bondEnergyHS_eq_two : bondEnergyHS A = 2 * bondEnergy A`.
- `InstIneqHS`, `P428Target8_HS`.
- `target_iff_hs : P428Target8 ↔ P428Target8_HS`.

The equality lemma should be a sum of the existing identity, not a new matrix calculation. Axioms: the three standard ones, or fewer.

## Q13 — quantifier order against `P428Target8Total`

Frozen `P428Target8` (`ZT5A.lean:291-294`), unfolded through `P428Genuine8` and `P428Core8`:

```text
∀ ell≥2, ∀ a>0, ∃ m₀≥1, ∀ m≥m₀, ∃ R₀, ∀ R≥R₀,
  ∃ a₀>0, ∃ γ₀>0, ∀ k≥1, ∀ Lu, ∀ α₀>0 with 12 * ell^m * α₀ ≤ a₀,
    CoercG8At … 12 …        -- conclusion InstIneq, ZT5A.lean:89
```

`R₀` may depend on \(m\). `a₀` and `γ₀` may depend on \(\ell,a,m,R\). They do not depend on \(k\), the torus, \(\alpha_0\), the tower, \(\Lambda\), \(U\), or \(\tilde B\).

`P428Target8Total` (`TT_F.lean:29-36`):

```text
∀ ell≥2, ∀ a>0, ∃ m₁≥1, ∃ R₁, ∃ a₀>0, ∃ γ₀>0,
  ∀ c≥10, ∀ m≥m₁, ∀ R≥R₁, ∀ k≥1, ∀ Lu, ∀ α₀>0 with c * ell^m * α₀ ≤ a₀,
    CoercG8AtWD … c …
```

Differences, all of them real:

1. `m₁`, `R₁`, `a₀`, `γ₀` are chosen before \(c\), \(m\) and \(R\). One \(R₁\) serves every large \(m\).
2. The cube factor is every \(c\ge 10\), not the constant 12.
3. The conclusion is `CoercG8AtWD` (invertibility and the inequality), not `InstIneq` alone.

### Relationship

- **`P428Target8Total` implies `P428Target8`.** Already a Lean theorem: `P428Target8Total.toTarget` (`TT_F.lean:70`), through `toAllC.toTarget`. Also `p428Target8Total` proves the stronger statement (line 43).
- **The frozen statement does not imply Total.** The binder shapes are not equivalent. Toy predicate \(P(m,R)\iff R\ge m\), checked in the script for \(m<40\) and a window of three radii: the frozen shape holds by taking \(R₀(m)=m\); the Total shape fails because no single \(R₁\) works for every larger \(m\). This toy is **not** the coercivity predicate. It only shows that one shape does not entail the other. For the real predicate both shapes are already proved, by different theorems.
- Not equivalent. Not false.
- A weaker reading, closer to the printed words "independent of \(k\) and \(U\)" only, is `P428Genuine8Print` (`ZT5A.lean:244`): `γ₀` may depend on the unit torus. **Frozen implies it**, theorem `P428Genuine8.toPrint` (`ZT5A.lean:266`). The converse is the stronger uniformity in the torus, which is what the frozen statement actually says, not what this weaker variant says.

Whether the frozen order is what Balaban's sentence means is a reading question. The formal comparison is the one above.

### Stage B

File `AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean`.

Imports: `TT_F` (which reaches `P428Target8`).

Declarations, re-exports only, no new estimate:

- `total_imp_frozen : P428Target8Total → P428Target8 := P428Target8Total.toTarget` (or the existing theorem named again).
- A comment, not a fake proof, recording the three binder differences.
- Optional: `frozen_imp_print` by unfolding `P428Genuine8.toPrint` under the outer quantifiers of `P428Target8`. That direction is frozen ⇒ weaker, and it is already true at the inner statement.

`#print axioms` on the re-export. Do not re-prove `p428Target8Total`.

## What was not given a variant

- **Q2(a).** Big blocks of side \(M\ell^j\) fine sites are reading A. `admissible_iff_print` already identifies that reading with `Admissible`. The coarser block is reading B above.
- **Q6(b), Q7, Q9.** Other fidelity targets. Touching bonds: `not_P428Target8Literal` and `not_P428Target8LiteralBoth` are existing refutations of touching operators with the frozen class, not of Q6(a).
- **Q8, Q10, Q11.** Reading questions. No formal alternative is proposed here.

## Numerical method

`python3 AHP/fidelity/sheet-variants/numerics/sheet_variants.py`

No Lean, no lake, no `REPRODUCE.sh`. Sides 4 and 8 only. Sets of at most \(8^3=512\) sites. Exact integer arithmetic for distances, \(\pm I\) products, and the norm factor. Output copied in `numerics/results.txt`. All six groups passed after the two test-harness mistakes in the first run were corrected (a non-closed one-point `Ω₁` had been mis-labelled admissible; the toy Total-shape check had used a bounded \(m\) range on which a large \(R₁\) accidentally worked).

Operators transcribed:

| check | Lean |
|---|---|
| `pcd`, `pdist` | `ZStatementP428.lean:57-71` |
| `Om0Rad` / `Om0Print` / `Om0Unit` | `RB2.lean:31-42`, `RB1.lean:59` |
| `Collar0` | `RB2.lean:45-46` |
| `Admissible` conjuncts | `ZStatementP428.lean:73-83` |
| gauge step | `ClayStatement.lean:1312-1316` |
| `frobSq` versus \(\|·\|^2\) | `RMapLipschitz.lean:60`, `:145`; Pauli values `SuTwoInner.lean:506-522` |
| unit embedding | `ZStatementP428.lean:192` and `:195` |

## Stage-B file list

| file under `AHP/fidelity/sheet-variants/lean/` | imports | expected outcome |
|---|---|---|
| `CollarNonStrict.lean` | `ZT5A` | one-way implication and an `M=1` separator; inequality left open |
| `ReadingB.lean` | `THL6`, `RB2` | `Target8Layer → P428Target8_ReadingB`; side-8 full-torus separation; proper domain not claimed |
| `LambdaScale.lean` | `ZStatementP428` | embedding identity; collars agree |
| `GlobalGauge.lean` | `ZT5A` | frozen implies global-gauge variant; converse not claimed |
| `NormHS.lean` | `ZT5A`, `AdalyFormal.Balaban.RMapLipschitz` | equivalence via `γ₀ ↦ γ₀/2` |
| `QuantifierOrder.lean` | `TT_F` | re-export `toTarget`; no new proof |

Compile each with `lake env lean` from `lean/`, then `#print axioms`. Accept only `propext`, `Classical.choice`, `Quot.sound`. Do not edit `lean/`, `paper/`, `notes/`, `expected/`, or the lakefile. Do not import these files into `Check*.lean` in this stage.

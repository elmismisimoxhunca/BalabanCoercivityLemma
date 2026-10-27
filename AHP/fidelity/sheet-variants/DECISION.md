# sheet-variants — decision

**Decision: `lean-comparison`.** Send the precisely scoped comparisons below to Stage B, not a new analytic headline and not a counterexample to the printed assertion. This file supersedes SPEC.md's stage-B list and its unqualified non-implication claims. SPEC.md and ATTACK.md remain the design/attack record.

No Lean, lake, or REPRODUCE.sh was run. No candidate below is certified. Compilation and axiom inspection are still required, after the cold-build gate.

## 1. Disposition by sheet question

| Question | Stage-B disposition | What remains |
|---|---|---|
| Q1, Q2(a) | No new target; retain the disclosed geometric conventions / existing reading-A bridge. | Source acceptability is a reading question. |
| Q2(b) | Compare strict and non-strict tower predicates; compile the disclosed `M=1` separator and the depth-one equivalence. | The print says strict. Do **not** assert a non-strict coercivity headline, or infer its failure from a tower separator. |
| Q3 | Conditional restriction `Target8Layer → P428Target8_ReadingB`, with the same class, operators, and one radius. | No proper in-regime, covered, nonzero-test-field reading-B instance was supplied. No new unconditional fidelity closure. Which meaning of `T_1` is intended remains reading-only. |
| Q4 | Exact distance scaling and collar-atom equivalence for an explicitly defined embedding; also correct the small-torus regime bound. | This compares embedded unit-site pairs only. It does not identify the full fine complement of `Omega_k` with its embedded unit-site complement or decide the source's use of `R`. |
| Q5 | Already covered by existing AllC / Total / Family / union declarations; no duplicate work. | Acceptability of boxes or a fixed factor is reading-only. |
| Q6(a) | Exact global-gauge-to-per-cube inclusion, including unchanged coverage and a flat regularity witness. | The print and frozen predicate already put the gauge inside the cube quantifier. Do not promote the global variant as a faithful replacement or claim strict inclusion for actual class cubes. |
| Q6(b), Q7, Q9 | Other fidelity targets. | No duplicate closure here. |
| Q8, Q10, Q11 | `sheet-reading`. | No operator-identification target here. |
| Q12 | Energy identity, instance equivalence, and headline equivalence with the left-hand norm alone changed. | This does not address the class-bound square-root factor or the eta/tau* first term (S-3). |
| Q13 | Re-export Total's implication; formalize the **abstract** threshold-order example if desired as listed below. | Do not claim non-implication between the actual named headlines. The source's intended uniformity remains reading-only. |

The aggregate is not `reading-only`: several exact predicates and identities are formally testable. It is not `lean-proof`: some alternatives intentionally change printed clauses, and reading-B analytic non-vacuity has not passed the stated test. It is not `lean-counterexample`: no faithful in-regime analytic counterexample was supplied.

## 2. Repairs and additional findings

### Accepted attack repairs D1–D5

1. Use `numerics/attack_check.py`, groups 1, 4, 5, as the evidence for the 448/512/3 figures, exhaustive central-subgroup gauges, and entrywise Pauli values. The design's hardcoded Pauli dictionary is not independent evidence. The coordinate family does contain `i sigma_1` at `(a,b,c)=(0,0,1)`.
2. Correct the reading-B saturation statement to **nonempty unions of side-4 blocks**, at `ell=M=2`, `R=k=1`, fine side 8. For an arbitrary nonempty set the sentence is false: the site `(5,5,5)` is distance 6 from `[0,4)^3`. Do not generalize this finite check to all tori or parameters. The `M=1, Omega_1={0}` proper set is not even a `ReadingBTower` witness: the singleton violates level-one block closure. It is a base-set example only.
3. The central 4-cycle checks cover all 16 gauges in `{+I,-I}^4`, not an exhaustive search over SU(2). Telescoping and central holonomy explain the general flattening obstruction; neither calculation supplies an `IsClassCube` regularity separator. Global regularity permits nonzero bounded `A`; it is not global exact flattening.
4. Correct source locators: `lean/src/RB2.lean:26-27` (`Om0Rad`), `:29-31` (`om0Print_eq_rad`), `:41-42` (`Om0Unit`); `lean/src/ZStatementP428.lean:51` (`bigSide`); `lean/src/AdalyFormal/Balaban/SuTwoInner.lean:505-523` (Pauli definitions); `lean/src/ZR6A.lean:33-34,124-125` (`CoversOm0p`, `ClassCoupled`). `LambdaOK` at `ZStatementP428.lean:189-195` existentially binds an embedding; it does not export one. Define `unitEmb` below.
5. The original script's dead loop and misleading distance/Pauli comments are not adopted. New Stage-B arguments must use the cited definitions, not that commentary.

### D6 is not accepted verbatim: unit and fine sides were confused

`TorusOK ell M Lu` is a predicate on **unit** extent `Lu` (`ZStatementP428.lean:286-289`, consumed at `ZT5A.lean:89-97`). The attack's parameter enumeration applies it to the **fine** side. Its purported single fit `(ell,M,k,fine side)=(2,2,2,8)` has unit side 2 and fails `ell < unit side`.

In the actual headline, `ell | unit side` and `ell < unit side`, with `ell>=2`, force unit side at least `2*ell`; `k>=2` then forces fine side at least `2*ell^(k+1)>=16`. Thus **no** depth-at-least-two headline case fits under fine side 8. This strengthens the negative search limitation, but for a different reason than either report gave. `M=1` also fails `SidePow6` for `ell>=2,m>=1`.

For a geometry-only side-8 tower with `ell=M=2,k=2`, the block argument still works, but should be worded correctly: if `Omega_2` is the whole torus, nesting forces `Omega_1,Omega_0` to be the whole torus, and the relevant complement quantifiers are empty; if `Omega_2` is empty, the `j>=1` collars are vacuous and the retained base law forces the strict level-zero collar. This is not a headline instance. Do not say a full `Omega_k` produces a distance-zero failure.

### Further correction: predicate inclusion is not logical independence

SPEC and ATTACK overstate several relationships. A missing hypothesis-inclusion route does not establish that one **closed analytic proposition** fails to imply another. In particular `TT_F.lean:43` already provides `p428Target8Total`; an implication into Total can ignore its premise. It is incorrect to say that the actual frozen proposition does not imply Total. The threshold toy separates unrestricted quantifier **schemas**, not the actual coercivity propositions. The same caution applies to reading A versus B, non-strict collars, and global gauges. Only the displayed inclusion directions and explicitly named predicate separators are approved. No converse-impossibility claim is approved for the real analytic statements or the real global regularity class.

### Further correction: the original collar-atom numerical check had no true cases

At unit side 4, `R=3,M=2`, the periodic l1 distance is at most 6; the test `6 < distance` is false for all 4096 pairs. The distance-scaling computation still has content, but the inequality comparison never exercised its true branch. A supplementary `R=M=1` check exercises both branches: 3648 true and 448 false pairs, zero mismatches. This is geometry only, not a headline non-vacuity witness.

## 3. Reproduction evidence

Freshly ran `numerics/attack_check.py` under a 4-GiB virtual-memory limit: exit 0, `all_checks True n 9`, 1.956 seconds. Output: `numerics/decision_attack_results.txt`; timing: `numerics/decision_attack_resources.txt`. The group-8 label incorrectly says “256 nonempty”; the code enumerates masks 1 through 255 and reports 255 strict cases. Treat this as **255 nonempty unions**, not 256 tested nonempty unions. No new universal conclusion follows from the sample sweep or the bounded quantifier toy.

Also ran the new `numerics/decision_checks.py` under the same cap: exit 0; output `numerics/decision_results.txt`. It cites the actual `scaleUp`, distance, divisibility, `LambdaOK`, and `TorusOK` source lines. Results: no actual headline fit with `k>=2` and fine side at most 8; the original collar test has 0 true cases; the additional collar test has both truth values and zero mismatches. All torus sides used are at most 8. Both scripts completed in seconds. Numerical results are evidence, not proof.

## 4. Exact Stage-B contract

All new declarations belong to `namespace AdalyFormal.Fidelity.SheetVariants`, under `AHP/fidelity/sheet-variants/lean/`. The signatures below omit proof bodies because this is Stage A. They are proposed declarations, not compiled results. No `True` placeholders, opaque surrogate regularity, or altered frozen predicates are permitted.

Use the existing namespaces as needed:

```lean
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.ThinLayer (AdmNoBase Target8Layer)
open AdalyFormal.RBridge (Om0Unit)
```

Only open namespaces supplied by each file's imports. All unqualified names in the following contracts refer to these namespaces or this new namespace.

### 4.1 `CollarNonStrict.lean` — imports `ZT5A`, optionally `RB2`

Define exactly:

```lean
def AdmissibleNonStrict {L : PeriodicLatticeExtent}
    (ell M R k : ℕ) (S : Tower L) : Prop :=
  (∀ j : ℕ, S.Om (j + 1) ⊆ S.Om j) ∧
  (∀ j : ℕ, k < j → S.Om j = ∅) ∧
  (∀ j : ℕ, j ≤ k → ∀ μ : Fin 3, bigSide M ell j ∣ (L μ + 1)) ∧
  (∀ j : ℕ, j ≤ k → BlockClosed (bigSide M ell j) (S.Om j)) ∧
  (∀ j : ℕ, j ≤ k → ∀ x : PeriodicLatticeSite L, x ∉ S.Om j →
    ∀ y ∈ S.Om (j + 1), R * bigSide M ell j ≤ pdist x y) ∧
  (∀ x : PeriodicLatticeSite L, x ∈ S.Om 0 ↔
    ∃ y ∈ S.Om 1, ∃ z : PeriodicLatticeSite L,
      (∀ μ : Fin 3, (z μ).val / M = (x μ).val / M) ∧ pdist z y ≤ R * M)

def L8 : PeriodicLatticeExtent := fun _ => 7

def collarSep : Tower L8 :=
  ⟨fun j => if j = 0 then Set.univ
    else if j = 1 then {x | ¬ (4 ≤ (x 0).val ∧ (x 0).val < 6 ∧
      4 ≤ (x 1).val ∧ (x 1).val < 6 ∧ (x 2).val < 2)}
    else if j = 2 then {x | ∀ μ : Fin 3, (x μ).val < 4}
    else ∅⟩
```

Required proof signatures:

```lean
admissible_imp_nonstrict {L : PeriodicLatticeExtent} (ell M R k : ℕ)
    (S : Tower L) :
    Admissible ell M R k S → AdmissibleNonStrict ell M R k S

admissibleNonStrict_k1_iff {L : PeriodicLatticeExtent} (ell M R : ℕ)
    (S : Tower L) :
    AdmissibleNonStrict ell M R 1 S ↔ Admissible ell M R 1 S

collar_separator :
    AdmissibleNonStrict 2 1 1 2 collarSep ∧ ¬ Admissible 2 1 1 2 collarSep
```

The separator has `Omega_0` equal to the torus and is outside the headline. Its non-strict/strict difference is at `j=1`, witnessed by `(4,4,0)` and `(3,3,0)`, both at distance 2. It is not an analytic counterexample. Prefer coordinate arithmetic over a huge reduction of quantified sets. No non-strict coercivity assertion is authorized.

### 4.2 `ReadingB.lean` — imports `THL6`, `RB2`

```lean
def ReadingBTower {L : PeriodicLatticeExtent}
    (ell M R k : ℕ) (S : Tower L) : Prop :=
  AdmNoBase ell M R k S ∧ S.Om 0 = Om0Unit ell M R k (S.Om 1)

def P428Target8_ReadingB : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        SidePow6 ell (ell ^ m) a ∧
        ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
          ∀ k : ℕ, 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ),
            0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
            TorusOK ell (ell ^ m) Lu →
            ∀ S : Tower (scaleUp ell k Lu), ReadingBTower ell (ell ^ m) R k S →
            ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell (ell ^ m) R k S Lam →
            ∀ U : LinkCfg (scaleUp ell k Lu),
              ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
                InstIneq ell k (by omega) a Lu γ₀ S Lam U
```

Required signature:

```lean
readingB_of_layer : Target8Layer → P428Target8_ReadingB
```

This must be a restriction using `ReadingBTower`'s first conjunct. Do not replace the class domain by another tower, change radii, or claim the conditional restriction establishes proper-domain analytic non-vacuity. No new reading-B witness or unconditional printed identification is required or credited by this plan.

### 4.3 `LambdaScale.lean` — imports `ZStatementP428`

Define a total map explicitly; its modulo does not wrap when the scaling factor is positive:

```lean
def unitEmb {Lu : PeriodicLatticeExtent} (ell k : ℕ)
    (y : PeriodicLatticeSite Lu) : PeriodicLatticeSite (scaleUp ell k Lu) :=
  fun μ => ⟨(ell ^ k * (y μ).val) % (scaleUp ell k Lu μ + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩
```

Required signatures:

```lean
unitEmb_val {Lu : PeriodicLatticeExtent} (ell k : ℕ) (hs : 0 < ell ^ k)
    (y : PeriodicLatticeSite Lu) (μ : Fin 3) :
    (unitEmb ell k y μ).val = ell ^ k * (y μ).val

pdist_emb_scales {Lu : PeriodicLatticeExtent} (ell k : ℕ) (hs : 0 < ell ^ k)
    (y z : PeriodicLatticeSite Lu) :
    pdist (unitEmb ell k y) (unitEmb ell k z) = ell ^ k * pdist y z

lambda_collar_scale_iff {Lu : PeriodicLatticeExtent} (ell k M R : ℕ)
    (hs : 0 < ell ^ k) (y z : PeriodicLatticeSite Lu) :
    (R * M < pdist y z) ↔
      R * bigSide M ell k < pdist (unitEmb ell k y) (unitEmb ell k z)

headline_fine_side_ge16 (ell M k : ℕ) (Lu : PeriodicLatticeExtent)
    (hell : 2 ≤ ell) (hk : 2 ≤ k) (hT : TorusOK ell M Lu) (μ : Fin 3) :
    16 ≤ scaleUp ell k Lu μ + 1
```

The last bound does not need an admissible tower or `M=ell^m`; the actual torus constraints already suffice. Positive scaling is essential for the first three results. The distance statement covers all rectangular extents, not just the cubic numerical examples.

### 4.4 `GlobalGauge.lean` — imports `ZT5A`

The design's `True` placeholders are rejected. Define exactly:

```lean
def GlobalRegular {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  ∃ g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ,
    ∀ (sites : Set (PeriodicLatticeSite L)) (j : ℕ),
      IsClassCube ell M f k S sites j →
      ∃ A : Bond L → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ e : Bond L, CubeBond sites e →
          HT (A e) ∧
          ((periodicGaugeTransform g U e : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
            Matrix (Fin 2) (Fin 2) ℂ) =
              NormedSpace.exp (((η : ℂ) * Complex.I) • A e) ∧
          frobNorm (A e) < (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 1)) ∧
        (∀ (μ ν : Fin 3) (x : PeriodicLatticeSite L),
          CubeBond sites ((x, ν) : Bond L) →
          CubeBond sites ((periodicLatticeShift x μ, ν) : Bond L) →
          frobNorm ((η⁻¹ : ℝ) • (A (periodicLatticeShift x μ, ν) - A (x, ν))) <
            (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 2)) ∧
        (∀ (μ : Fin 3) (x : PeriodicLatticeSite L),
          (∀ ν : Fin 3, ν ≠ μ →
            CurlReads sites (periodicLatticeShiftBack x ν) ν μ ∧ CurlReads sites x ν μ) →
          frobNorm (ddA η A x μ) <
            (f : ℝ) * M * α₀ * (((ell : ℝ) ^ j * η)⁻¹ ^ 3))

def ClassCoupledGlobal {L : PeriodicLatticeExtent}
    (ell M c k : ℕ) (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) : Prop :=
  CoversOm0p ell M c k S ∧ GlobalRegular ell M c k S α₀ η U
```

Required signatures:

```lean
global_imp_perCube {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (U : LinkCfg L) :
    GlobalRegular ell M f k S α₀ η U → PerCubeRegular2 ell M f k S α₀ η U

globalClass_imp_frozenClass {L : PeriodicLatticeExtent} (ell M c k : ℕ)
    (S : Tower L) (α₀ η : ℝ) (U : LinkCfg L) :
    ClassCoupledGlobal ell M c k S α₀ η U → ClassCoupled ell M c k S α₀ η U

global_flat {L : PeriodicLatticeExtent} (ell M f k : ℕ) (S : Tower L)
    (α₀ η : ℝ) (hell : 0 < ell) (hM : 0 < M) (hf : 0 < f)
    (hα : 0 < α₀) (hη : 0 < η) :
    GlobalRegular ell M f k S α₀ η (fun _ => 1)
```

For `global_flat`, use the actual witnesses `g=1`, `A=0`; the positive assumptions discharge **strict** bounds. This is regularity non-emptiness, not a proof of coverage or of a nonzero admissible test field. A global-gauge headline and a strict-class-separation assertion are not part of this plan.

### 4.5 `NormHS.lean` — imports `ZT5A`, `AdalyFormal.Balaban.RMapLipschitz`

```lean
noncomputable def bondEnergyHS {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) : ℝ :=
  ∑ b : Bond L, frobSq (A b : Matrix (Fin 2) (Fin 2) ℂ)

def InstIneqHS (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ₀ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergyHS Bt ≤
      GenP.genForm (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))

def CoercG8AtHS (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
    ∀ S : Tower (scaleUp ell k Lu), Admissible ell M R k S →
    ∀ Lam : Set (PeriodicLatticeSite Lu), LambdaOK2 ell M R k S Lam →
    ∀ U : LinkCfg (scaleUp ell k Lu),
      ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        InstIneqHS ell k hell a Lu γ₀ S Lam U

def P428Target8_HS : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        SidePow6 ell (ell ^ m) a ∧
        ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
          ∀ k : ℕ, 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ),
            0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
              CoercG8AtHS ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀
```

Required signatures:

```lean
bondEnergyHS_eq_two {L : PeriodicLatticeExtent} (A : Bond L → SuTwo) :
    bondEnergyHS A = 2 * bondEnergy A

instIneqHS_iff (ell k : ℕ) (hell : 0 < ell) (a : ℝ)
    (Lu : PeriodicLatticeExtent) (γ : ℝ) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) :
    InstIneqHS ell k hell a Lu (γ / 2) S Lam U ↔
      InstIneq ell k hell a Lu γ S Lam U

target_iff_hs : P428Target8 ↔ P428Target8_HS
```

Prove these by the finite sum of `RMapLipschitz.norm_sq_eq_half_frobSq` (`:145-149`), then transport the same positive constant uniformly through the unchanged binders. Do not prove the iff by independently importing two analytic conclusions and ignoring the norm relation. The pointwise identity applies to nonzero as well as zero fields; the hypothesis class and admissible test fields are unchanged. No scalar change to `genForm`, `a`, `alpha_0`, or operators is authorized.

### 4.6 `QuantifierOrder.lean` — imports `TT_F`

Required signatures:

```lean
total_imp_frozen : AdalyFormal.Total.P428Target8Total → P428Target8

threshold_order_toy :
    (∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → m ≤ R) ∧
    ¬ (∃ m₁ : ℕ, 1 ≤ m₁ ∧ ∃ R₁ : ℕ,
      ∀ m : ℕ, m₁ ≤ m → ∀ R : ℕ, R₁ ≤ R → m ≤ R)
```

The first is a named re-export of `AdalyFormal.Total.P428Target8Total.toTarget` (`TT_F.lean:70`). The second is an infinite natural-number arithmetic example, not a bounded Python conclusion and not a statement about coercivity. Keep the three actual differences visible: choice of thresholds/constants before `c,m,R`, all `c>=10` rather than 12, and well-definedness in the conclusion.

## 5. Acceptance and limits

After the parent confirms the cold reproduction passed, compile each of the six files under the target's `lean/` directory with `lake env lean`, without changing the lakefile or frozen tree. Print axioms for every listed proof declaration and for any new helper used to prove them; allow only `propext`, `Classical.choice`, `Quot.sound`, or subsets. No `sorry`, new axiom, `native_decide`, or unverified external computation. Save commands, exit codes, and complete axiom output under this target. A declaration that fails compilation is unfinished, not silently dropped or weakened.

Count closures only at the scope actually checked: a predicate comparison, a norm re-expression, an existing restriction, or a documented reading disposition. This decision does not certify the non-strict inequality, proper-domain reading-B non-vacuity, strict global-class inclusion, S-1, S-2, S-3, or the guarded all-plaquette headline. It does not alter the statement sheet or paper. No protected path, git history, or remote was changed.

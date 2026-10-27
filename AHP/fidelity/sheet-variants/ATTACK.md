# sheet-variants — attack

Role: attack the design in `SPEC.md` and its script `numerics/sheet_variants.py`.
Verdict: **the design survives with repairs** (schema outcome: `repairable`).
Every variant's stated relationship to the frozen `P428Target8` is logically
correct, every cited Lean line was checked against the file text, and every
number in `results.txt` reproduces exactly (design script re-run: output
identical). An independent re-transcription, `numerics/attack_check.py`
(output `numerics/attack_results.txt`, 9/9 groups PASS), confirmed every
claim it tested and strengthened several. Nothing below is a theorem. No
Lean was run. Numerics are evidence only.

The defects found are in SPEC's wording and evidence trail, not in its
conclusions: one literally false sentence (missing block-closure
qualification), one paragraph of numbers the script never computed, two
checks that were weaker than their claims, and small line-citation drift.
All are repairable by editing SPEC.md; none changes a stage-B file.

## 1. Does each variant say what it claims about the print?

Yes, for all six treated questions. Checked against `notes/statement_sheet.tex`
and the Lean sources:

* **Q2(b) non-strict collar.** The print's (2.2) is strict (`> RM`, sheet A2,
  transcribed at `RB1.lean`, matched by `collar_iff_rat`). The frozen collar
  atom is `R * bigSide M ell j < pdist x y` (`ZStatementP428.lean:78-79`,
  verified). The variant changes exactly that atom to `≤`. The two claimed
  relationships are correct: `AdmissibleNonStrict` is the strictly larger
  hypothesis class (`n < d → n ≤ d`), so `P428Target8_NonStrict → P428Target8`
  is class inclusion; and quoting the frozen theorem at `R−1` does not
  discharge the non-strict statement because clause 6 (`:80-83`) and
  `LambdaOK2` still use radius `R`. The claim that clause 6 forces the
  level-0 collar to be strict is the existing theorem `om0Print_collar`
  (`RB2.lean:76`, verified: `Collar0 M R (Om0Print M R Om1) Om1` with `<`),
  so at `k=1` (level-1 collar vacuous over `Ω₂ = ∅`) the predicates agree on
  clause-6 towers — swept, see §4 item 8. The inequality is correctly left
  open in both directions.
* **Q3 reading B.** `Om0Unit` (`RB2.lean:41-42`), `Om0Print` (`RB1.lean:59-60`),
  `AdmNoBase` (`THL2.lean:23`, verified: first five conjuncts of `Admissible`,
  strict collar kept, clause 6 dropped), `Target8Layer` (`THL6.lean:164`,
  verified: `P428Target8` with `Admissible → AdmNoBase`, proved at
  `target8Layer`, `:174`). Sol's three theorems are at
  `SolRBridgeAudit.lean:8, 15, 24` exactly as cited. "Neither statement
  implies the other" is right: whenever `Om0Unit ≠ Om0Print` a reading-B
  tower fails clause 6 (which forces `Ω₀ = Om0Print` via `om0clause_iff_print`,
  used in `admissible_iff_print`, `RB1.lean:185`), and a frozen tower fails
  the reading-B equation; the side-8 separation witnesses the difference.
  "`Target8Layer` implies the reading-B statement by restriction" is pure
  logic and correctly described as such.
* **Q4 same R.** `LambdaOK` (`ZStatementP428.lean:189-195`) has the unit atom
  `R * M < pdist y y'` (`:195`) with `(emb y μ).val = ell^k * (y μ).val`
  (`:192`); the fine collar radius at level `k` is `R * bigSide M ell k =
  R * M * ell^k`. The claimed equivalence of the two atoms under `emb` is
  correct (exact scaling, `ell^k > 0`). One spec gap, repairable: `emb` is
  **not a Lean declaration** — `LambdaOK` has `∃ emb` with that property.
  Stage B's `pdist_emb_scales` must define `emb` concretely
  (`fun y μ => ⟨ell^k * (y μ).val, …⟩`); the identity is about that explicit
  map. Verified numerically at three parameter sets (§4 item 6).
* **Q6(a) global gauge.** `PerCubeRegular2` (`ZR2A.lean:47-68`, verified) has
  `∃ g, ∃ A` inside `∀ IsClassCube`; the print has the same order (sheet A6).
  `ClassCoupled = CoversOm0p ∧ PerCubeRegular2` (`ZR6A.lean:124`, verified),
  so `ClassCoupledGlobal` mirrors it. Both directions stated correctly:
  `GlobalRegular → PerCubeRegular2` (instantiate one `g`), the global class
  is smaller, the variant weaker, frozen implies variant, not conversely.
  Flat `U = 1` with `g = 1`, `A = 0` keeps the variant non-empty.
* **Q12 norm.** `bondEnergy = ∑ ‖A b‖²` (`RegularUPerturbation.lean:355`),
  `‖Y‖² = ½ frobSq Y` (`norm_sq_eq_half_frobSq`, `RMapLipschitz.lean:145`),
  `frobSq` at `:60`, `hsInner` at `SuTwoInner.lean:104`,
  `hsInner_self_eq_sumNormSq` at `:143` — all verified. The claim
  `bondEnergyHS = 2 * bondEnergy` and the equivalence of the two targets via
  the uniform rescaling `γ₀ ↦ γ₀/2` (γ₀ is existential and field-independent)
  are correct. The separation from the class-bound `√2` factor (in
  `frobNorm`, absorbed in `α₀`, a different deviation) is correctly drawn.
* **Q13 quantifier order.** The unfoldings of `P428Target8` (`ZT5A.lean:291-294`,
  through `P428Genuine8` `:229` and `P428Core8At` `:170` at `c = 12`) and of
  `P428Target8Total` (`TT_F.lean:29-35`) match the sources exactly; the three
  binder differences are real; `P428Target8Total.toTarget` is at `TT_F.lean:70`
  via `toAllC` (`:67`), and `p428Target8Total` proves Total at `:43`.
  `P428Genuine8Print` (`ZT5A.lean:244`) and `P428Genuine8.toPrint` (`:266`)
  are as described. The toy predicate is disclosed as not being the
  coercivity predicate.
* **Q5** correctly points at already-proved variants (`P428Genuine8AllC`
  `ZT5A.lean:257`, `toHead` `:277`; `P428Target8FamilyTorus` `MXQ_Tor.lean:58`;
  `P428Target8FamilyTorusU` `UNI_Tor.lean:73` — all verified) and reopens
  nothing.

## 2. Hypothesis class: proper nonempty Ω₀?

* **Q2(b) variant class.** In-regime (`M = ℓ^m`) it contains the whole frozen
  class (strict ⇒ non-strict), which has proper `Ω₀` witnesses in the
  development — properly inhabited. The `M = 1` separator has `Ω₀` = the
  whole torus; SPEC discloses `M = 1` is outside `SidePow6`, and the
  separation happens at level `j = 1`, so the full-torus `Ω₀` is not a
  hidden vacuity. Checked independently (§4 item 7): the strict collar fails
  only by equality (`min dist = 2 = R·bigSide(1)`, 2 equality pairs).
* **Q3 variant class.** Proper nonempty `Ω₀` at headline sizes is **not
  shown**: on side ≤ 8 at `R ≥ 1`, `Om0Unit` is the whole torus for every
  admissible `Ω₁` (§4 item 2: exhaustive over all 255 nonempty side-4-block
  unions). SPEC says exactly this and the stage-B plan correctly refuses to
  claim a proper in-regime domain; the `Target8Layer` implication survives
  vacuity. The `M = 1` proper example (80/512 sites, min complement
  distance 3) is below the headline and is labelled as such. Honest.
  **However**, SPEC's supporting sentence is literally false as written —
  defect D2 below.
* **Q6(a) variant class.** Non-empty (flat configurations). Whether it
  differs from `PerCubeRegular2` inside `IsClassCube` is explicitly not
  claimed — the 4-cycle witness is a 2-bond arc, not a class cube, and SPEC
  says so.
* **Q12, Q13.** Class unchanged / re-export only. Nothing to check.

## 3. Do the numerical operators match the cited Lean lines?

Every operator was checked against the actual file text. Exact matches:
`pcd`/`pdist` (`ZStatementP428.lean:58-67`; SPEC's "57-71" contains them),
`bigSide` (`:51`), `Admissible` (`:73-83`, collar `:78-79`), `TorusOK`
(`:286-289`), `Om0Rad`/`SetDistLe`/`IsBigBlock` semantics (block ids = floor
division, half-open blocks cut at multiples of `s` = `BigBlockCell`),
`Collar0` (`RB2.lean:45-46`), the gauge step `γ(x) U γ(x+μ)⁻¹`
(`ClayStatement.lean:1312-1316`), the `(a,b,c)` traceless skew-hermitian
family vs `frobSq` (entrywise re-derived in the attack script), and the unit
embedding. Citation drift found (all minor, repairable):

* Script header: "Om0Rad: `RB2.lean:31-32`" — the def is `RB2.lean:26-27`;
  "Om0Print = Om0Rad M (R*M) `RB2.lean:34-35`" — `om0Print_eq_rad` is
  `:29-31`. SPEC's table range "RB2.lean:31-42" covers `Om0Unit` (`:41-42`)
  but not `Om0Rad`.
* Script comment "bigSide = M*ell^j (line 50)" — line 51.
* SPEC: Pauli generators "as in `SuTwoInner.lean:506-522`" — `pauliE1Val` is
  `:505`, `pauliE3` `:522-523`, `hsInner_e1_e1` `:524`.
* SPEC does not cite `ZR6A.lean:33,124` for `CoversOm0p`/`ClassCoupled`
  (used in the Q6(a) variant) — worth adding.

## 4. Are the numbers reproducible and the tolerances honest?

Re-ran `sheet_variants.py`: output identical to `numerics/results.txt`, all
six groups PASS, < 1 s, trivial RAM, sides ≤ 8, exact integer arithmetic
throughout — there are no tolerances, and none are needed. Independent
re-transcription `numerics/attack_check.py` (no import of the design script;
own distance matrix, own matrix arithmetic, own sweeps), 9/9 groups PASS:

1. **SPEC's unstaged numbers confirmed.** The Q3 vacuity paragraph states
   `|Om0Unit|=512`, `|Om0Print|=448`, min complement distance 3 for
   `Ω₁ = [0,4)³` — figures the design script never computes (results.txt has
   no 448). All three confirmed, plus the excluded-block shape (the 8 side-2
   blocks with ≥ 2 block-coordinates ≥ 2). See defect D1.
2. **No proper reading-B domain at headline sizes on side 8 — with the
   needed qualification.** For `Ω₁` an arbitrary nonempty set the claim is
   false: `min dist([0,4)³, (5,5,5)) = 6 > 4`. For `Ω₁` a nonempty union of
   side-4 blocks (what `AdmNoBase` requires at `k = 1`) it holds: max
   block-pair min-distance is 3 < 4 ≤ 4R, and `Om0Unit` is the full torus
   for all 255 nonempty unions. Conclusion stands; sentence needs the
   qualification. See defect D2.
3. **Headline-parameter enumeration.** `(ell, M=ℓ^m, k≥2)` fittable on side
   ≤ 8 under `TorusOK` + divisibility: exactly `(8, 2, 2, 2)`, where
   `bigSide(k) = 8 = side`. This strengthens SPEC's "smallest headline
   parameters" to "the only fittable headline parameters". Note the
   no-separator argument then has one more step than SPEC records: `Ω_k` =
   torus kills both collars (distance 0), `Ω_k = ∅` makes the `j ≥ 1`
   collars vacuous and clause 6 forces the strict level-0 collar
   (`om0Print_collar`). The design's `no-inregime-gap-on-side8` check tests
   only the arithmetic `2·2² = 8`.
4. **Global-gauge impossibility, exhaustive.** All 16 gauges in `{±I}⁴`:
   none flattens the 4-cycle, every gauged holonomy is `−I`, and each 2-bond
   arc flattens independently. The design checked only one propagated gauge
   and conjugation by `g₀ = I`. Conclusion unchanged. (Still not an
   `IsClassCube` witness — SPEC's disclosure stands.)
5. **Pauli values, entrywise.** `frobSq(E_i) = 2`, half = 1, computed from
   the definitions `!![0,i;i,0]`, `!![0,1;−1,0]`, `!![i,0;0,−i]`; the
   `(a,b,c)` family re-checked with explicit complex entries at 7 samples.
   The design's `pauli-frobSq-2` "check" was a hardcoded dict compared
   against itself — vacuous as code; the real evidence was the family check
   (which does contain all three Paulis at `(1,0,0)`, `(0,1,0)`, `(0,0,1)`).
   The script comment "E1 = iσ1 is not of this real form" is wrong:
   `(a,b,c) = (0,0,1)` is exactly `iσ₁`. Harmless but should be fixed.
6. **Embedding identity at two more parameter sets.** `(ell,k,unit) =
   (3,1,2) → fine 6` and `(2,2,2) → fine 8`: 64 pairs each, 0 mismatches.
   Design had `(2,1,4)`: 4096 pairs, 0 mismatches.
7. **Collar separator, independent construction.** Same tower rebuilt from
   scratch: all five non-collar conjuncts hold, clause 6 holds, strict fails
   only by equality (min distance exactly `R·bigSide(1) = 2`, attained at 2
   pairs including SPEC's witness `x=(4,4,0)`, `y=(3,3,0)`). Confirmed.
8. **k=1 agreement sweep.** All 256 nonempty side-4-block unions (`M=2`) and
   300 seeded side-2-block unions (`M=1`): strict and non-strict collar
   predicates agree on every clause-6 tower at `k=1`. Evidence for SPEC's
   agreement claim; the mathematical content is `om0Print_collar`.
9. **Q13 toy, second window.** `m < 60`, radius window 4, `R₁ < 20`: frozen
   shape holds, Total shape fails. Agrees with the design's window.

## 5. Defects (all repairable in SPEC.md; none touches a conclusion)

* **D1. Numbers stated as checked that the script never computed.** The
  `Ω₁ = [0,4)³` figures (448/512/3) sit in a subsection titled "Vacuity,
  checked on side 8", and the method section says "Output copied in
  `numerics/results.txt`". They are correct (attack §4.1) but hand-derived.
  Repair: add the case to `sheet_variants.py` (or cite
  `numerics/attack_check.py`, which now covers it) and regenerate
  `results.txt`.
* **D2. Literally false vacuity sentence.** "every side-4 block meets the
  radius-4 neighbourhood of a nonempty Ω₁" fails for `Ω₁ = {(5,5,5)}`
  (distance 6 > 4). It holds — and is all that is needed — for `Ω₁` a
  nonempty union of side-4 blocks (the `AdmNoBase` block-closure conjunct).
  Repair: add "for Ω₁ block-closed at side M·ellᵏ (as AdmNoBase requires)".
* **D3. Two checks weaker than their claims** (global gauge: one gauge +
  trivial conjugation; Pauli values: hardcoded dict). Both conclusions now
  independently verified (attack §4.4–4.5). Repair: strengthen the design
  script or point at `attack_check.py`; fix the wrong "E1 is not of this
  real form" comment; remove the dead `for x in om[j]: pass` loop in
  `admissible_parts`.
* **D4. Citation drift** listed in §3 (Om0Rad/eq_rad lines, bigSide line,
  Pauli line range, missing ZR6A citation). Cosmetic but this target is
  about statement fidelity; the citations should be exact.
* **D5. `emb` treated as an existing map** in the Q4 variant theorem; it is
  an existential inside `LambdaOK`. Stage B must define it explicitly.
* **D6. Minor imprecisions.** "Smallest headline parameters with k ≥ 2" →
  the only fittable ones on side ≤ 8 (§4.3). The design script's
  `sol-x400-distance` parenthetical ("Sol's decide proof uses the block, not
  this single distance") is misleading: Sol's `decide` decides exactly
  `pdist x400 zeroSite ≤ 4`, the single distance the script computes.
  Aggregate `prediction: "unknown"` in RESULT.json is defensible only
  because the per-item dispositions in SPEC's question map are decisive;
  consider stating them in the JSON.

## 6. Stage-B readiness

The six-file plan is sound and matches what the numerics establish:

* Import claims verified: `ZT5A` imports `ZR6A` (reaches `ClassCoupled`,
  `PerCubeRegular2`); `Check8.lean` imports `RB4` and `THL1-THL8` into one
  environment, so `ReadingB.lean`'s `THL6 + RB2` mix is safe; `TT_F` reaches
  `P428Target8`; `ZStatementP428` is a module.
* Practical notes for stage B: define `emb` concretely in `LambdaScale.lean`
  (D5); the `M = 1` separator in `CollarNonStrict.lean` should be a hand
  proof (`decide` over 512-site set membership may be heavy); keep the
  disclosed `M = 1`-outside-`SidePow6` wording; `ReadingB.lean` must not
  claim a proper in-regime `Ω₀` (D2's qualified fact is the reason none fits
  on side ≤ 8); `NormHS.lean`'s `bondEnergyHS_eq_two` is a sum over bonds of
  `norm_sq_eq_half_frobSq`; `QuantifierOrder.lean` re-exports only.
* Before stage B, repair D1–D4 in SPEC.md so the sheet-facing document says
  only what its evidence shows.

Verdict: **attack fails to break the design's content; SPEC.md needs the
four repairs D1–D4 (and should take D5–D6) before stage B.** Schema outcome:
`repairable`.

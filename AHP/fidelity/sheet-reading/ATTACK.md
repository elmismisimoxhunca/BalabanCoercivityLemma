# ATTACK: sheet-reading

Verdict: **PASS WITH NITS.** Every reading row I could check is substantively
correct: the print quotes match the corpus, the Lean transcriptions match the
actual definitions, the numerics reproduce bit-for-bit and the tolerances are
honest. The one systematic defect is **line-number drift**: 18 citations in
`SPEC.md` and the script's comment headers point at the wrong lines (always
the right file, the right declaration name and, I verified, the right
semantics at the true location). Against the workspace rule "every operator a
script models must cite the Lean file and line it transcribes" these must be
corrected before Stage B, but none of them changes any reading verdict.

Method: every cited Lean definition was read in `lean/src/` (flat modules and
`AdalyFormal/Balaban/`, `AdalyFormal/Target/`); every print quote was compared
with `sources/corpus/pages/CMP99b_p{393,394,419,420,421,428}.md`; the script
was re-run (0.11 s) and diffed against the committed `results.json`
(identical). No Lean was compiled. The page renders could not be re-read here
(no image processor in this environment); see §5.

## 1. Does the variant say what it claims about the print? — YES

Checked against the corpus transcriptions:

- (3.21)/(3.22)/(3.25) (`CMP99b_p394.md:41-95`): `R = Δ_U N(Q')`,
  `N(Q') = {λ : Q'λ = 0}`, the sentence that functions in (3.22) "vanish on
  `Ω₁^c`", and `Rf = (I - G'Q'*(Q'G'²Q'*)⁻¹Q'G')f` with "We do not know yet if
  the operators ..." — all exactly as the SPEC's R row states, including the
  SPEC's disclosure that (3.25) is not the definition used and that Lean's
  `NQp` imposes support in `Ω₀` where the print's (3.22) functions vanish on
  `Ω₁^c`. The disclosure is accurate, not a hidden mismatch.
- (3.24) (`CMP99b_p394.md:64-70`): weight `(L^j η)^{d-2}`, recurrence
  `a_{j+1} = a a_j/(aL^{-2} + a_j)`, `a_1 = a_0 = a > 0` — as quoted.
- (3.16) (`CMP99b_p393.md:55-58`): flat `a` (not `a_j`) with weight
  `(L^j η)^{d-2}` — as the Q10 row states; the Lean site/bond split
  (`ajSeq` in `Qpa`, flat `a` in `massW`) mirrors the print's split.
- (3.119) (`CMP99b_p419.md:53-55`), (3.122) (`CMP99b_p420.md:23-29`, display
  plus prose `G⁻¹ = Δ_π + DRD* + Q*aQ`), (3.126) (`:80-82`),
  (3.128) (`CMP99b_p421.md:30-38`, both displays, the second with
  `C^{(2)}(A - DG'RD*A)`), (3.129) (`:43-45`) — all as quoted.
- p.428 (`CMP99b_p428.md:30-53`): the subspace
  `{B : B=0 on Λ^c, B=0 on ∪ Ax(y), Q_1B=0}`, `B(c)∩c` = exactly one bond
  `b₀`, and `C` "an identity operator on almost all bonds, except the bonds
  `b₀`" solving `(QB)(c) = 0` "considered as an equation on the variable
  `B(b₀)`" — verbatim as the SPEC's Q11 row. The print indeed does not say
  which fine bond of the edge `b₀` is, so the `droppedBondLast` (offset
  `ℓ-1`) convention is genuinely a convention, and the SPEC says so.

The "forms-agree" prediction holds row by row: every row is "matches" or
"matches with a stated convention", and the conventions named (η-free `d=3`
body, junk inverse `0`, `plaqIn` for Δ, touching bonds N1, η/τ* in the first
term, `a‖QA‖²` as (3.16), `b₀` = last fine bond) are exactly the ones the
sheet already names (A8, A9, A12, N1, D1, item 8 of Part C). No unmarked
mismatch found.

One soft caveat (nit, not a mismatch): the Q8 weight row's phrase "removing
the global factor `η^{d-2}` leaves the Lean weight" is heuristic — at
`η = ℓ^{-k} < 1` the printed weight genuinely is `η·ℓ^j ≠ ℓ^j`; the honest
content is the `η = 1` specialisation, which the row also states ("At `η=1`
they are equal with no factor to remove") and which the sheet records as
inherited, not re-derived. Read as an equality claim it would be wrong; read
as the named convention it is fine. The row labels it a convention, so this
is a wording caveat only.

## 2. Hypothesis class: proper nonempty Ω₀ / Λ — YES

The script's own geometry checks establish this for the Q11 model (side-4
torus, `ℓ=2`): `Λ` = the origin block is 8 of 64 sites (proper, nonempty),
`LamPrime == [(0,0,0)]` is asserted (`check_cop`), both bond classes are
asserted nonempty (`touch_only` 24, `both` 12), and `LamPrime` failure or an
empty row set aborts the run. Re-run confirms: 192 bonds, 24 coarse bonds,
6 constraint rows, 7 axial bonds, all 6 dropped bonds among the 24
touching-only bonds (`dropped_outside_both` lists all six). The inclusion the
headline uses (`InstIneq.toBoth`: both-endpoint ⇒ touching) is non-vacuous
on this torus — 24 bonds separate the two predicates, and the script's random
touching field passes `OnLambdaT`/`OnLambdaTildeIn` and fails `OnLambda` as
claimed. The Q8 mask model uses 4 of 6 sites (proper, nonempty). The Q10
model is abstract matrix algebra with no `Ω₀`; that is disclosed ("Not the
lattice assembly in `baseData`") and appropriate, since the reading question
there is the chain (3.122)→(3.129), not the domain. No additional check was
needed.

## 3. Do the numerical operators match the cited Lean lines? — semantics YES, line numbers NO in 18 places

I read every transcribed definition at its true location and compared it with
the script/SPEC transcription. **Every transcription is semantically
correct**; the defects are wrong line numbers. Catalogue (cited → actual):

In the script header (`reading_checks.py`) and its inline comments:

1. `inBlock`, `AdmissibleSubspace.lean:111-114` → def at `:115-116` (cited
   range is the docstring). Script `in_block` matches the def.
2. `CoarseLattice`, `:154` (membership `:157`) → def `:144-145`,
   `mem_CoarseLattice` `:147`. Script `coarse_sites` matches.
3. `corner1`, `:331-333` → def `:345`. `corner2`, `:328-331` → def `:348-349`
   (and the cited ranges have corner2 *before* corner1; the file defines
   corner1 first). Script `corner1`/`corner2` match (update coord 2, then 1).
4. `isG1inv_sub`, `R2Algebra.lean:236-242` → theorem at `:230-234` (the cited
   range is `G1inv_coercive`). Script's `g1inv = ginv - delta2` matches.
5. `QG1Qs_isUnit_of_small`, `:325-332` → theorem at `:318-323`. The script's
   smallness margin (`evals[0] - ‖Δ2‖ > 0`) models exactly its `ε < c`
   hypothesis.
6. `K_eq`, `R2Algebra.lean:168-170` → theorem at `:173-175` (the cited range
   is `inner_Ginv`). Script `keq` matches.
7. `massW`, `ZXR2Ops3.lean:90-91` → def `:98-99`; `inner_MassFull`,
   `:104-108` → theorem `:112-117`. `a * ℓ^j` confirmed at the true location.
8. `Q11` comment block range `ZStatementP428.lean:205-234` for
   `LamPrime/CRowIn/IsDroppedIn/OnLambda/OnLambdaTildeIn` — `OnLambda` is at
   `:198-201`, outside the cited range (the SPEC table cites it correctly).

In `SPEC.md` (not in the script):

9. `NQp`, `R2Ops1.lean:162-168` → def `:150-156` (the cited range is
   `lapDir`/`RImage`). The stated content (support in `Ω₀`, `Q'_j = 0` on
   `Λ_j`) matches the true def.
10. `Rproj = starProjection of lapDir '' NQp`, `:162-172` — `Rproj` itself is
    `:170-171`; the range spans the `lapDir`/`RImage`/`Rproj` chain. Loose,
    defensible as a chain citation, but the companion `NQp` cite (9) is wrong.
11. `BaseDataS.K`, `:154-156` → def `:153-154`.
12. `G1inv_unique`, `R2Algebra.lean:216` → theorem `:205-207`.
13. `bondSupp`, `ZXR2Ops3.lean:28-33` → def `:30-36` (touching-bond carrier
    confirmed: `bondsOm0` uses `∨`, `:26-27`).
14. `T`/`Ts` in `baseData`, `:141-142` → `:137-138`. `Mass` `:146` → `:141`.
    `C2 := C2full (Wop …)` `:147` → `:142`.
15. `Gp_spec`, `:130-173` — theorem starts `:130`; `BothIn` begins at `:173`,
    so the proof ends earlier. Start line right, end line overshoots.

Verified correct (a sample of the rest): `ajSeq` `ZR2Ops2.lean:21`,
`Qpa :27-30` (weight `ajSeq * ℓ^j` confirmed), `DelpA :57-59`, `Gp :63-65`,
`Wop :67-69`, `Delta :79-81` (`plaqIn` both-endpoints, `:73-76`),
`DpiFull :83-84`, `inner_DpiFull :93-97`, `Tfull_adj_comp :104-114`,
`aSeqAux/aSeq` `ConstantA.lean:155-160`, the `4/5` example `:246`,
`lapFull R2Ops1.lean:108`, `Ginv/G/H` `R2Algebra.lean:145-151`,
`exists_G1inv :186`, `G1/H1 :307-310`, `G1in/H1in` `ZXR2Wire2.lean:82-88`,
`G1inv = Classical.choose` `:61-64`, `Nmat/firstTerm` `ZXG3A.lean:35-51`,
`genC :58`, `OnLambdaT ZR2A.lean:121-123`, `OnLambdaTildeIn :230-234`,
`CRowIn :211`, `IsDroppedIn :216`, `C_ker :266`, `Ax` `AxialContour.lean:153`
(block-minus-root biUnion confirmed), `staircasePath`
`AdmissibleSubspace.lean:366-370` (order 2,1,0 confirmed), `axisSegment :294`,
`blockOf :120`, `droppedBondLast` `ReparamCDisjoint.lean:157-158` (offset
`ℓ-1` confirmed), `pathSite` `QOne.lean:175-176`, `periodicLatticeShift`
`ClayStatement.lean:1281-1283`, `Cop/hLift/H0/H0inv` `ZXR2Unit2.lean:84-107`,
`Cop_id :127-134`, `Cop_ker :136-146`, `InstIneq :56`, `InstIneq.toBoth :80`.
The design JSON's own line cites are all correct; the drift is only in the
SPEC's expanded tables and the script comments.

Semantic spot checks beyond line numbers:

- `H0inv` (`ZXR2Unit2.lean:90-96`) is the inverse when `H0` is bijective, `0`
  otherwise — the script's `cop_from_q` does exactly this, including the
  junk branch test.
- `Cop = id - hLift ∘ Q` (`:104-107`) — script matches; `Cop_ker` is only
  claimed on rows `CRowIn`, and the script only checks rows.
- The script's four stand-in `Q`s are honestly labelled: `Q1jet`
  (`ZXR2Unit1.lean:70`, calling the Fréchet jet `QlinStepL`,
  `ZLocJet.lean:38-39`) was **not** transcribed, and the SPEC says the
  identification with the printed one-step jet remains convention D10/D11.
- The coupled-`Q` test genuinely demonstrates the SPEC's limit (2): joint
  solution residual `5.9e-17`, frozen-neighbour one-bond formula residual
  `≥ 0.45`, and `C` sets every `b₀` to `0` on a dropped-only invertible
  system. The "equation on the variable `B(b₀)`" print sentence is the
  decoupled case, exactly as the SPEC (and the Lean comment at
  `ZXR2Unit2.lean:10-15`) restricts it.
- The η-algebra of the wired row: `G1in = η⁻¹ ι G1 ι*` (`ZXR2Wire2.lean:82-83`)
  and `firstTerm = η⟨τ*B, (Q data.G1 Q*)⁻¹ τ*B⟩` (`ZXG3A.lean:50-51`) give
  `(Q G1in Q*)⁻¹ = η (Q G1 Q*)⁻¹`; the script checks this identity and the
  factor-η relation with residual 0 at `η = 1/8`. Algebra and code agree.

## 4. Are the numerical tolerances honest? — YES

- Tolerance is absolute `1e-9` against residuals `0` to `1.2e-13` — no
  tolerance is doing any work; every "pass" is 4+ orders inside it.
- Singularity/bijectivity thresholds (`1e-8`) have clear margins in both
  directions: singular padding sv `7.4e-17` (fail-if-above `1e-8`), `H0`
  smallest svs `2.0` and `1.7` (fail-if-below `1e-8`).
- Non-vacuity guards are honest and pass with margin: scalar solution max
  `1.23` vs guard `1e-3`; free-bond value `0.437` vs `1e-8`; naive-formula
  residual `0.45` vs `1e-6`; junk-branch `‖Q(CB)‖` `2.57` vs `1e-6`.
- The refused-reading gaps are large and reported as gaps, not as passes:
  weighted vs unweighted mass differ by `≥ 2.57`; unweighted `Ginv` moves
  the form by `≥ 1.46`.
- The junk value `0` was not imitated anywhere (singular-`H0` and
  singular-padding cases only record the singularity); the SPEC says so and
  the code does so.
- Reproducibility: re-run with seed 20261021 produces a byte-identical
  `results.json` (diffed). All numbers quoted in the SPEC and in the design
  summary (`8.9e-16`, `7.4e-17`, `4.4e-16`, `1.2e-13`, `5.7e-14`, `3.28`,
  `0.096`, `4.5e-16`, `2.57`, `1.23`, `-0.437`, `5.9e-17`, `0.45`, `2.57`,
  the 21 exact `a_j` values, the four weight rows) match the committed JSON.
- One-scope honesty check: the path-`Q` result "C does not move `b₀` for a
  legal `B̃`" is correctly labelled "a fact about this `Q` and this block,
  not a failure of `Cop`" — the script even asserts
  `path_bonds_visible_to_tilde = 0` so the statement cannot silently
  generalise.

## 5. What could not be attacked here

- The page renders (`sources/corpus/renders/CMP99b_p{394,419,420,421,428}-*.png`)
  could not be re-read: they are 2400×3800 PNGs and no image processor is
  available in this environment. The corpus `.md` files carry their own
  adjudicated image re-read notes for exactly the passages used (p.394:
  "RE-CONFIRMED ... directly against the image at full resolution"; p.428:
  "Re-verified by 1.8x crop"), so the chain render→corpus→SPEC has one
  project-verified and one attack-verified link. The SPEC's claim "the
  renders agree with the corpus" was therefore verified only at the corpus
  level.
- `gradL2`, `lapFull`, `Qlev`, `QlinStepL`, `Q1jet`, the plaquette sum
  inside `Delta` and the SU(2) field were not transcribed (disclosed); the
  covariant-derivative content of `W`, `R` and `Q₁` is untested by design.
- Import compatibility of the ten Stage-B modules was not testable without
  compiling. All ten exist as modules; the eleven Stage-B declaration names
  all exist (checked textually, including namespaces:
  `AdalyFormal.IngredientFamilyR2.*` for the `ZR2Ops2`/`ZXR2Unit2` items,
  `AdalyFormal.StatementLaneG.InstIneq.toBoth`,
  `AdalyFormal.IngredientFamilyR2.BaseDataS.*` for the `R2Algebra` items).
  The five `#check` names in the SPEC's audit note all resolve.

## Findings

- **F1 (must fix before Stage B, cosmetic):** 18 wrong or loose line
  citations catalogued in §3 (script: items 1-8; SPEC: items 9-15 and the
  loose `Rproj` range). All names and semantics are correct at the true
  locations; the errors look like drift after file edits. Fix the numbers;
  no reading verdict changes.
- **F2 (wording nit):** the Q8 weight row's "removing the global factor
  `η^{d-2}`" phrasing should not be read as an equality at `η < 1`; the
  `η = 1` specialisation stated beside it is the honest content. Consider
  rewording so a hostile reader cannot quote it as a weight identity.
- **F3 (limitation, disclosed):** render-level agreement with the corpus was
  not re-verifiable in this environment; only the corpus level was attacked.

Nothing found that challenges the "forms-agree" prediction, any single
reading row, the numerical evidence, or the Stage-B plan.

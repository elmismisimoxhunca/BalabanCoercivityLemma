# SOL VERDICT — s5-lighter-coverage

**Verdict: REJECT the advertised uncovered-plaquette conclusion. Grade: 2.**

Reject means **not established by this draft**, not that the lighter hypothesis is sufficient or that the claimed obstruction is impossible. S-5 remains open. The elementary arithmetic and the identification of the frozen consumer survive. `compiled` is false; no draft declaration is certified as a theorem of the project tree.

## Evidence read

Read `HANDOFF.md` and all of `paper/OPEN_ITEMS.md`, the complete draft `LighterCoverage.lean`, `AHP/notes/s5-lighter-coverage.md`, the existing on-disk `PROSECUTION.md` (although the request's prosecution value was null), and both local external-reading reports. No external repository text was fetched or copied.

Independently inspected these frozen definitions and proof steps:

| Source | Checked content |
|---|---|
| `lean/src/ZR8Read.lean:88` | The copied recursion for `rhoT` |
| `lean/src/ZR8Geo.lean:94` | Closed periodic-distance ball |
| `lean/src/CJ2.lean:223` | `ReadRow`: level, alignment, distance bound |
| `lean/src/CJ3.lean:93–133,171–265` | Fine-plaquette ball hypothesis, `cube_index_ge`, and `plaq_small_class` including its coverage extraction and index estimate |
| `lean/src/CJ4.lean:143–218` | `read_region`, `classRows_read`, and the actual call to `plaq_small_class` |
| `lean/src/ZR6A.lean:27–35,124–125` | `CoversPlaqOm0c`, `CoversOm0p`, `ClassCoupled` |
| `lean/src/ZR2A.lean:47–70` | Per-cube gauge and index-dependent bounds |
| `lean/src/ZStatementP428.lean:51–86,122–146` | Big side, admissibility, periodic boxes, class-cube predicate, both-endpoint cube bonds |
| `lean/src/ZXR2Ops3.lean:26–52` | Touching `bondsOm0` versus level-dependent coarse `bondsLam` |

Grade 2 records inspection of the actual frozen definitions, not a compiler check or a fresh printed-page audit.

## What stands

The relevant frozen consumer is correctly named. `classRows_read` introduces every site and pair of directions in the read ball, then invokes `plaq_small_class` with `read_region`. The latter puts the site's radius-2 ball inside the preceding tower domain. `plaq_small_class` obtains one factor-c class cube containing all four boundary bonds through `hU.1.2 p hp`, then spends the cube-index estimate to obtain its decay bound. A gauge somewhere on each bond is not this hypothesis.

The copied radius satisfies, by hand arithmetic,

\[
\operatorname{readRadius}(\ell,m)\ge4\ell^{m+1}\ge8\ell^m>\ell^m=M
\]

for \(\ell\ge2\). The value at \((2,1)\) is 32. With \(j=m+1\), the `ReadRow` distance allowance is zero; conditional on an appropriate `bondsLam j` row, this is a legitimate level choice. None of this supplies an admissible nonempty witness or an uncovered plaquette.

The interval lemma is correct for its stated nonperiodic natural-coordinate model: no interval of M consecutive sites contains 0, 1 and M. The class-side inequality is also correct as arithmetic. These statements have not been elaboration-checked.

## Decisive gap: one row bond is not the active set

The lighter clause quantifies over every eligible side-M cube containing **any** active bond. The draft excludes only cubes containing the one selected row bond b. It does not exclude a different active bond near the far plaquette whose eligible cube contains the whole plaquette. Nor does it define a lighter-class predicate with a precise active set and prove failure of its coverage consequence on a tower.

`bondsLam j` indexes one coarse row sector. It is not automatically the free-unit-bond set in the external account, and the frozen fine-domain mask `bondsOm0` is different again. A record `(y, direction)` can describe different geometric bond lengths in these uses. The draft's assertion that the active set is `bondsLam` is therefore a missing identification, not a conclusion supplied by the frozen definition.

Under an enlarged unit-bond interpretation covering `bondsOm0`, an internal plaquette has active boundary bonds of its own. **If** an eligible side-M cube containing that plaquette is available, the lighter clause gauges it. Thus the radius comparison alone cannot establish non-coverage. This conditional observation is enough to expose the missing quantifier; it is not a positive transfer result.

## Qualifications to the prosecution

The prosecution's main quantifier objection is upheld. Its stronger statements are not all adopted:

- The local reports quote cubes **contained in Omega_k** and also describe additional seam and second-cover regularity clauses. Identifying active bonds with `bondsOm0` alone does not remove that containment requirement. Although `read_region` gives containment in Omega_(j-1), hence Omega_0, it does not generally give Omega_k. Therefore the prosecution's unconditional assertion that coverage holds under its Scenario A needs an additional domain/eligible-cube identification. No such general coverage conclusion is certified here.
- Scenario B and its proposed extra-geometry repair are not a completed tower construction or exhaustive classification; this review does not certify them.
- The frozen term cannot simply be supplied with a side-M gauge in place of `ClassCoupled`. But a mismatched input type does **not** prove that no implication, gluing argument or alternative analytic proof could bridge it. The index-dependent estimate is a concrete remaining obligation, not an impossibility result.
- A larger numerical side parameter alone does not establish unequal **periodic site sets**: `siteBox` can saturate a torus. Any universal statement that a side-M cube is never a class cube needs appropriate non-saturation hypotheses. The draft proves only a side-length inequality.
- The displayed ball is a sufficient region used by this proof. Its radius alone does not prove every site in it is indispensable to the mathematical operator or every alternative proof.

## Required disposition

Retain the arithmetic as an uncompiled diagnostic. Withdraw the summary “the lighter hypothesis does not cover the needed fine plaquette” as an established result. To settle that negative route, define the lighter hypothesis with the active unit bonds, cube containment, alignment, other regularity clauses and bounds; construct admissible data and a needed plaquette; exclude **every** eligible regular cube, not merely cubes containing b. A positive route instead needs to derive the scale-sensitive plaquette estimates or replace their downstream use.

Do not write that the coercivity inequality, the external argument, or Balaban's printed lemma is refuted; that coverage automatically holds under the literal quoted lighter clause; or that this draft closes S-5. `paperSentence` is empty and no paper insertion is authorized.

## Verification and write scope

Manifest SHA-256 matches were measured for all nine inspected frozen modules: 9/9. A raw whole-word prohibited-token scan of `LighterCoverage.lean` found 0 matches. Forty-two radius spot checks passed, including the value 32; these are diagnostics only. Before this review's write, `git diff --name-only` was empty and status showed only untracked `.bb/` and `AHP/`.

Only `AHP/attempts/s5-lighter-coverage/SOL_VERDICT.md` was written by this review. No compiler/build command, dependency download, deletion, commit or push was run. Frozen files, configuration, Check files, expected outputs, paper and statement sheet were untouched. No fresh dependency audit was performed. `compiled` remains false.

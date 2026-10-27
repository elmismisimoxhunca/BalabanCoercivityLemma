# residual-open — prosecution (Kimi lane)

Review only. No Lean fragment. Not a Lake root. Not compiled. Not a theorem of the project tree. Frozen modules, `lakefile.toml`, `paper/`, `CLAIMS`, `OPEN_ITEMS`, and `notes/statement_sheet.tex` were not edited. No `lean`, `lake`, `elan`, `REPRODUCE.sh`, or `#print axioms` was run. `compiled` is false.

Material prosecuted: [residual-open.md](/home/sebastian/BalabanCoercivityLemma/AHP/notes/residual-open.md) and [NOTE.md](/home/sebastian/BalabanCoercivityLemma/AHP/attempts/residual-open/NOTE.md). Prior [Sol verdict](SOL_VERDICT.md) rejected an empty submission; this prosecution examines the classification now present.

## Verdict

**Could not refute. Classification stands, with four qualifications.**

The mandate was to refute any sentence that turns a diagnostic into a theorem or moves the source \(a_1\) and the formal \(a_0\) together. Both notes contain no such sentence. Every load-bearing factual claim was re-checked against the frozen sources (read-only; no build) and holds. The draft's own "Must not write" list is internally consistent and is respected by both files.

## Refutation attempts, each failed

**Attempt 1 — "Sol's three radii are a threshold."** Searched both notes for any sentence promoting the radii \(12, 21, 18\) / \(12, 11, 18\) at \((\ell,M) = (2,1), (2,2), (3,1)\) to a threshold, a least \(R\), or a theorem. Found the opposite, twice: "Not a threshold in \(\ell\) and \(M\). Not a theorem" (note, R-b) and "A bounded diagnostic. Not a threshold for all \(\ell, M\). Not a theorem that those radii are least" (NOTE.md). The numbers transcribe `paper/OPEN_ITEMS.md` R-b verbatim and the draft discloses they were not recomputed. No refutation.

**Attempt 2 — "The third-enlargement sentence is a clause of the formal family."** Checked `lean/src/C5C.lean:29-31` (`IsDCube`: \(j \le k\), `GridCorner (bigSide M ell j) c`, one seed \(x_0 \in \mathrm{towerBj}\,S\,j \cap \mathrm{dCube}\)) and `lean/src/C5G.lean:33-35` (`IsDCubePrint`: adds the disjunct \((x_0 \in S.\mathrm{Om}\,j \land x_0 \notin S.\mathrm{Om}\,(j{+}1)) \lor (j = 0 \land x_0 \notin S.\mathrm{Om}\,1)\)). Neither mentions \(\tilde\square^3\), containment in \(B^j\), or meeting \(B^{j+1}\). The printed sentence is confirmed in `sources/corpus/pages/CMP99b_p408.md:31` as the opening move of the local-sequence construction, after \(\mathscr{D}_j\) membership is fixed at line 29. The draft's claim — present on the page, absent from the predicates — is exact. No refutation.

**Attempt 3 — "Formal sufficiency for the larger family is necessity for the restricted family."** The draft states the contrapositive discipline explicitly: "Sufficiency already proved for the larger formal family still applies to any subfamily. A smaller hypothesis does not become a necessity theorem." This is logically correct (universal over a superset restricts; it never yields necessity on a subset). No refutation.

**Attempt 4 — "34 is excluded" / "the formal collar requires powers of \(L\)."** `collarOK` (`lean/src/SH2.lean:29`) is `18 * bigSide M ell j + 3 ≤ (R + 3) * bigSide M ell (j - 1)` with `bigSide M ell j = M * ell ^ j` (`lean/src/ZStatementP428.lean:51`). No power binder anywhere; `cube5_in_union` (`lean/src/C5C.lean:60`) binds \(\ell, M, R : \mathbb{N}\) with \(2 \le \ell\), \(0 < M\), \(21\ell \le R\) only. The page's "We take these numbers as powers of \(L\)" (`CMP99b_p408.md:31`) is a parameter choice sentence, not a necessity proof — the draft says exactly this. Arithmetic check of "34 is admitted": with \(\ell = 2\) and \(R = 34\), `collarOK` at index \(j\) is \(36 \cdot M 2^{j-1} + 3 \le 37 \cdot M 2^{j-1}\), i.e. \(M 2^{j-1} \ge 3\) — the stated regime. `collar_power_ell2` (`lean/src/RB3.lean:56`) is \(34 \le 2^r \leftrightarrow 6 \le r\), separate arithmetic whose docstring names \(34 = 18\cdot 2 - 2\); the draft correctly refuses to read it as sharpness on the power-restricted set. No refutation.

**Attempt 5 — "\(a_1\) and \(a_0\) are identified anywhere."** Grepped both notes for any equation or identification of the two constants. Found only separation: "The source threshold is \(a_1\)"; "These are not the printed hypothesis \(O(1)\,M\alpha_0 \le a_1\)"; "\(a_1\) and \(a_0\) are not identified." Checked the formal side: `FamTorusCap` (`lean/src/L0C2.lean:146-159`) carries an existential \(a_0 > 0\) with \((f:\mathbb{R}) \cdot (\ell^m:\mathbb{R}) \cdot \alpha_0 \le a_0\); `level0_instance_inequality` (`lean/src/L0C5.lean:36`) has \((12\,\ell:\mathbb{R}) \cdot (\ell^m:\mathbb{R}) \cdot \alpha_0 \le a_0\) — factor \(12\ell\) against the same formal \(a_0\), as the draft says. The printed side (`CMP99b_p408.md:19,21`) sets \(\alpha_1 = O(1)M\alpha_0\) and assumes \(O(1)M\alpha_0 \le a_1\). The draft never equates them. No refutation.

**Attempt 6 — "`level0_case_complete` is promoted to Corollary 3.6 or Theorems 3.1–3.3."** The declaration (`lean/src/L0C3.lean:33-44`) is the conjunction of: (i) local-domain containment and `IsClassCubeAlt` membership at factors \(10\) and \(12\), and (ii) `FamTorusCap` (via `cap_unconditional`). The draft calls the module comment stale, cites the must-not-write registry (`paper/OPEN_ITEMS.md:315` lists `L0C3.lean:31-32`), and denies exterior regularity of local \(\Omega_0(\square)\), Theorems 3.1–3.3, and \(a_0 = a_1\). Verified the declaration form matches that description. No refutation.

**Attempt 7 — "Level-0 non-box unions are closed in either direction."** `DescribedAt0` (`lean/src/P4L4.lean:141-144`) requires `sites = siteBox z (f * bigSide M ell 0)` — one box; it may leave \(\Omega_0\) and must meet \((\Omega_1)^c\). `DescribedAtAlt`/`IsClassCubeAlt` (`lean/src/L0C2.lean:25-30`) use that box at index \(0\) and `DescribedAt` at positive index; `boxClass` (`lean/src/UNI_Tor.lean:25`) is `IsClassCube`. `IsClassSetW` (`lean/src/GenCl1.lean:125-130`) is genuinely different (two distinct level-\(j\) blocks, bounding box, no single-box equality). The draft's claim that `FamTorusCap` quantifiers do not range over non-box unions, and that the statement is neither proved nor refuted by the unreconstructed cap-route example, matches the sources. No refutation.

**Attempt 8 — "Kimi debt is discharged by this note."** The debt table in NOTE.md lists all six lanes (`cube5`, `mixed12`, `level0_class`, `p409_sharp`, `r_bridge`, `thin_layer`) as "not done"/"none" and states this classification does not replace a Kimi pass. This prosecution is the `residual-open` lane only; it does not discharge the other five lanes. The draft does not claim otherwise. No refutation.

## Qualifications (do not refute; record)

1. **Transcribed, not recomputed.** The radii \(12, 21, 18\) / \(12, 11, 18\) are copied from `paper/OPEN_ITEMS.md` R-b; the underlying Sol trial script was not rerun here (and could not be: no build authorized). The draft discloses this; the transcription was verified verbatim against line 325.
2. **Regime precision.** "34 is admitted by the natural-number collar in that regime" requires \(M\ell^{j-1} \ge 3\); at \(j = 1, \ell = 2\) this forces \(M \ge 3\). The draft says "in the regime \(M\ell^{j-1} \ge 3\)", which is correct; this prosecution only stresses that the regime is a hypothesis, not free.
3. **Paraphrase compression.** The summary note's "IsDCubePrint adds, at \(j = 0\), a seed outside \(\Omega_1\)" compresses the actual second disjunct; NOTE.md's fuller rendering (first disjunct \(B^j\) membership, second disjunct \(j = 0 \land x_0 \notin \Omega_1\)) is the accurate one. Consistent, not contradictory.
4. **Wording delta vs OPEN_ITEMS.** `paper/OPEN_ITEMS.md` R-c says "the first power of 2 above is 64"; the draft says "the first power of \(2\) at or above \(34\) is \(64\)." Same fact (\(2^5 = 32 < 34 \le 64 = 2^6\)); the draft's phrasing is the more precise one.

## Meta-checks

- `git status --porcelain` shows only untracked `.bb/` and `AHP/`; no frozen file modified.
- No `.lean` file exists under `AHP/`; nothing to compile; `compiled` stays false.
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern` introduced (the only textual hits are English words like "admitted").
- No sentence in either file calls any item a theorem, closes any residual, identifies \(a_1\) with \(a_0\), or promotes Sol's three samples past "bounded diagnostic."

## Outcome

The classification is adopted as prosecuted: **no refutation found, four qualifications recorded**. The four mathematical residuals stay open; the five other Kimi lanes stay document debt. Nothing here is a theorem. A later authorized rebuild, printing only `propext`, `Classical.choice`, and `Quot.sound`, remains the only path to that word.

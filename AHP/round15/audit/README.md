# Round-15 timeout closeout audit

## Outcome

`guarded-collar` (`wfr_5df3dc43-d69b-4118-bbde-2106f7836520`) failed at its **24-hour total run timeout** on 2026-10-27. It stopped in Work, with 7 successful calls, 2 earlier failed attempts subsequently retried, and 1 cancelled dictionary R2 call. The original Blueprint phase never began. No unconditional seed/P3/GoalNeg2 claim was submitted, so no closure-verification call was triggered.

The coordinator confirmed the cancelled dictionary worker was idle and found no relevant Lean/numerical process remaining. No worker or proof search was restarted. The separate **documentation-only** Kimi K3.1 Pro high run (`wfr_e42c066f-a662-4a53-831f-359b383ed641`) completed the promised Markdown and leanblueprint deliverables. The coordinator then checked all 101 canonical source/axiom citations and 89 namespace-qualified secondary source citations, corrected one ambiguous secondary citation and two wording issues, and verified labels, proof markers, balanced new TeX environments, and byte-identical inherited checkpoints. See `BLUEPRINT_VALIDATION.json` and `verify_blueprint.py`. This reporting success does not turn the failed research workflow into a successful proof run.

An attempted ordinary reporting delegate was rejected before creation because native delegates could not override the pinned model configuration. No thread was created by that failed attempt. The reporting-only workflow is the fallback; it has no research/retry loop.

## Verified retained evidence

Run `audit_retained.py --workflow-history <saved-history.jsonl> --output <report.json>` through `bb heavy run --` to reproduce this static audit. The workflow export is saved in the parent thread's storage under `workflows/guarded-collar-timeout.jsonl`.

- `TIMEOUT_AUDIT.json` records complete axiom records, exact source/log hashes, source positions, exit metadata, errors and a comment/string-aware forbidden-token scan. `SUMMARY.json` is a compact derivative.
- There are **101 unique round-15/late-KData names with retained builder axiom evidence** across the selected files. This is not a count of all new unprinted helpers, all inlined historical declarations, independent replays, or proved physical premises.
- Every accepted retained record has only `propext`, `Classical.choice`, `Quot.sound`, or a subset (including the empty set). The six local/shared source pairs are byte-identical.
- All new accepted results are **B: builder compilation evidence**, not A: independently replayed here. No Lean build was run in this closeout.
- Seed R2 has 421 complete printed records including two axiom-free records, whereas its older audit counted 419 nonempty records. Its current source was deterministically regenerated after compilation; the source/log hashes match the retained paired builder audit, and the reconstruction from the unchanged R1 base plus R2Declarations matches byte-for-byte. This is provenance evidence, not an independent replay.
- Assembly R2 retains the earlier compiled matrix-only source hash `a6d141eb46842741e72e9b8dd758fa1203c0dfa53c6b07a64ef6d86bf1ced5dc`. Its local log is a copy of the retained publication log, not another compilation.
- Dictionary R2 `KData.lean` has a clean retained builder run for four new explicit-matrix lemmas: `q1B00_inv`, `q1_schurA`, `q1_schurB`, `q1_schurC`. They do not identify those matrices with the frozen physical operator.

## Rejected late evidence

`dictionary/r2/Stencil.lean` is **not accepted**. Its `.exit` says 0 but predates the current source and log. The current 8192-byte log is incomplete and contains a syntax error at source line 993. Its current source is newer than the zero marker. This is precisely why a zero marker or a few permitted axiom lines cannot certify a whole file.

`Support.lean`, `DeepCollar.lean` and `Transport.lean` also do not have acceptable current whole-file evidence. No physical-row identity from these attempts is promoted. No proof repair is undertaken in this closeout. The larger uncompiled vector assembly is not accepted either.

## Mathematical disposition

Preserved results include the explicit collar model algebra, conditional seed/limit/assembly implications, exact arithmetic audits of 336 transcribed character blocks, and high-precision leading-area data at q=1,2,4, even R=18..40. Assembly's q=1,R=42 held-out runs succeeded; q=2,R=42 timed out and is excluded.

The **first-inverse-only all-plaquette reading is numerically strongly disfavoured / conjectured false**. This is an evidential classification, not a probability estimate or formal refutation. The full-guard all-plaquette theorem is already proved. Source-reading questions are separate.

The physical dictionary, nonzero same-generator area seed, P3, CofinalP3 and GoalNeg2 remain open. No further proof search is planned without renewed authorization. This open auxiliary refutation does not invalidate the existing formalisation of Balaban's multiscale coercivity theorem.

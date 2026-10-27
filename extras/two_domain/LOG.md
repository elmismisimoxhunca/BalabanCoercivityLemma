# LOG
2026-10-19 lane created
- Read thin_layer READING/STATEMENT/THL6, level0_class L0C2, union_cubes UNI_Tor/UNI_Base. Plan:
  (1) cap two-domain: ClassCoupledCap is monotone in Om 0 -> trivial from famTorusLayerCap.
  (2) union two-domain (printed class, boxes included): F' = all S-class unions regular w/ factor present in F; cut C∩Om0op; if the cut misses B0op (C disconnected, cut inside B1),
      glue a far M-block E (pdist>=4 from Om1, inside B0op) whose regularity comes from the coverage hypothesis; needs R0>=4.
  (3) Total/Target8 from box-family. (4) witness with Om0op < Om0cl (slab3 R vs Rb). (5) gates.
- TD1 (regBody_mono_b, glue_side, regBody_glue, far_block_exists, block lemmas) and TD2 (cover_cut, famTwoDom_union: TwoDomFamP unionClass, threshold max R1 4) compile, axioms = propext/choice/Quot.sound.
  Key fact found: the cut C∩Om0op of a DISCONNECTED union cube can miss B0(op) (lie inside B1); repaired by gluing a far M-block (pdist>=4 from Om1) whose regularity comes from the coverage hypothesis.
- TD5 (non-vacuity: slab S at radius R, Sc = Admissible Rb, same curved U in ClassCoupled Sc, positive-energy competitor, conclusion at S), TD6 (plain cut C∩Om0 fails: slab example), TD7 (statement closure + census) compile.
- run_both.sh (builds b1 then b2, TD1..TD7) started detached.
- READING.md written (pp.394/396 images re-read; quotes P1-P5).
- Final src: TD1 TD2 TD3 TD4 TD5 TD6 TD7 (+ controls/TD_CtlSorry, TD7ctl).  oneDom_of_twoDom / oneDomCap_of_twoDom / totalLayer_of_twoDom added (consistency: Sc := S).
- Disclosure: `pkill -f "<task id>"` matched the invoking shell (exit 144) once; a stale background `until` loop was then killed by explicit PID; earlier b2 of a first pipeline run was killed by explicit PIDs (1327331 1329972 1329975 1329986) so that the builds could be redone on the final sources.  No other process was touched.
- GATES (facts, final sources): builds b1/b2 CHAIN OK both; out_b1.sha == out_b2.sha (14 files: 7 oleans + 7 logs byte-identical).  leanchecker TD1..TD7 all exit 0, control (missing module) exit 1.
  Census (in-Lean): roots=1029, union_of_axioms=[Quot.sound, Classical.choice, propext], roots_with_nonstandard_axioms=0; control with one sorry: roots flagged 1 (TD_ctl_bad), sorryAx in union.
  Forbidden tokens (scan_forbidden.py comment/attribute-stripped as in thin_layer, scan_forbidden2.py comments+strings only, attributes kept): 0 hits in src/*.lean; 11/11 positive controls fire; negative control (tokens only in comments/strings) silent.  s77 scan: selftest ALL CONTROLS OK, LIVE 0.
  Per-headline #print axioms: gate_record/axioms_headlines.txt (23), builtin prints of every module: gate_record/axioms_all_modules_builtin_prints.txt.  Statement closure of each headline: gate_record/statement_closure_and_census.txt (the only new definition in the closure of famTwoDom_union is TwoDomFamP (module TD2); AdmSplitNB comes from THL6; the rest are frozen statement modules).
  MUTANTS: 6 comment-only controls (one per module TD1..TD6) COMPILE; 16 mutations FAIL at their own module (M01-M16; first errors in gate_record/mutant_first_errors.txt), covering: glue separation 4->3 (M01), far-block threshold 4->3 (M02) and distance 3M+1->3M (M03), nearness radius 3->2 (M04), cover_cut threshold (M05), inclusion of the domains reversed (M06), regularity clause of F' -> True (M07), glued piece -> cut alone (M08), agreement for j>=1 weakened to j>=2 (M09), class read from S instead of Sc (M10), factor bound 10->9 (M11), frozen threshold m0' only (M12), witness strictness R<Rb -> R<=Rb (M13), Sc admissible at the thin radius (M14), second slab at the thin radius (M15), plain-cut claim negation dropped (M16).

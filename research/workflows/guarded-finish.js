export const meta = {
  name: "guarded-finish",
  description: "Close the guarded all-plaquette reading: prove the last premise (CofinalCanonicalCoupling, or a weaker compiled variant) via a Lean symmetry dictionary and a nonvanishing argument for the flat-lattice coupling coefficient. Astra (xhigh) on three tracks for up to four rounds, Astra verifies and assembles.",
  phases: [
    { title: "Work", detail: "Dictionary, nonvanishing, assembly tracks, rounds 1-4" },
    { title: "Verify", detail: "Astra recompiles any claimed GoalNeg2" },
    { title: "Report", detail: "Plain summary" },
  ],
};

const COMMON = [
  "GOAL. Prove the pinned GoalNeg2 of AHP/round3/guarded/pin/Statement.lean with no extra hypotheses: the invertibility-guarded all-plaquette reading P428Target8SG selAll selAll is false. Everything except one premise is already compiled.",
  "THE LAST PREMISE. AHP/round9/qualitative-r2/Attempt.lean (12189 lines, compiles, standard axioms) proves goalNeg2_of_cofinalCanonicalCoupling : CofinalCanonicalCoupling -> GoalNeg2 (:11729), plus weaker-premise bridges goalNeg2_of_cofinalAnyProfileCoupling (:11906, premise :11869) and goalNeg2_of_cofinalAnyPathCoupling (:12102, premise :12077), the explicit forms CofinalExplicitCoupling (:12007) and CofinalExplicitU1 (:12050), and the unconditional facts interiorSoft_corrDeriv (:11653), twist_vacuum_crossing_all (:11677), twistSeparation_eventually_of_coupling (:11699), corrDeriv_dilMask_form (:11967: <u, D_e u> = 2 <H0 C2_0(W0 u), J'>). AHP/round9/analytic-r2/Attempt.lean has the left-twist variant (goalNeg2_of_vacuumLeftCouplingD :7608, premise VacuumLeftCouplingD :7591), interiorSoft_proved, dil_D1_form, hasDerivAt_extA_vac, extA_vac_one_pos. AHP/round6/closedform-r1/Attempt.lean:2643 has twoSite_exact_symmetry (orthogonal two-site translation action on the carrier space with background and holonomy invariance). Prove ANY one of these premises; pick whichever is easiest. They only need INFINITELY MANY dyadic scales q = 2^j and, for each, INFINITELY MANY even R >= 18 (you may restrict to a convenient arithmetic progression of R, or a single convenient sequence of j). The coupling's SIGN is irrelevant; only nonvanishing (definiteness on the kernel) is needed.",
  "READ FIRST: AHP/round9/qualitative-r2/NOTES.md and AHP/round9/analytic-r2/NOTES.md (and the r1 notes), AHP/round9/RESULTS.md if present, AHP/round8/guarded-idea/IDEA.md, AHP/round6/probe/PROBE.md. Numerics in those directories transcribe the actual operators with Lean line citations.",
  "KNOWN NUMERICS (evidence only): the q-dilated character sector equals the q = 1 geometry with the same Bloch phase; first-crossing character is diagonal for q = 2..256, with a single crossing sector and the next sector bounded away (0.052 at q = 2, 0.0137 at q = 4, R = 18); c1(q,R) = K(k) * rho_k^(4qR) * (1 + O(e^(-kappa qR))) with K in [-0.0197, -0.0180] and R-independent to 15 digits; K < 0 for all diagonal k in [-1.374, -0.049], vanishing linearly as k -> 0; c1 is about 102-104% of the defect-block level-0 jet term, with an alternating geometrically decaying tail; h_0 = 36 sqrt2 - 50.",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma (Lean 4.31, Mathlib, oleans built). Write only under AHP/round10/<track>/. Shared hand-off area: AHP/round10/shared/ (any track may add compiled Lean files and notes there; never overwrite another track's file). Do not edit lean/ (lakefile, lean/src/BalabanCompact*, Compact* belong to another thread), paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your own track directory. No git commit or push.",
  "COMPILING. The machine has 16 GB RAM. Compile ONLY with AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs machine-wide; writes .log and .exit). Run it directly in bash with a long timeout; if the bash call still times out, poll for .exit and never relaunch the same file. Keep your working files small: develop new lemmas in short files that import only frozen lean/src modules and contain only the definitions they need (copied verbatim), and assemble the 12000-line file only at the end. Never run lake build or REPRODUCE.sh. Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque stand-ins; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath; keep jobs under 2 GB and use \"$BB_CLI\" heavy run -- for anything over a minute. Numerics never replace a proof step.",
  "DELIVERABLES per round in AHP/round10/<track>/rN/: compiled .lean files with .log/.exit, NOTES.md (plain mathematics: what is proved, what is left, the exact Lean statement of what is left). Be strict: never call a conditional result a proof. If you find the premise is false, or a mathematical obstruction, say so plainly with evidence.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const tracks = [
  {
    key: "dictionary",
    aim: "TRACK: SYMMETRY DICTIONARY (Lean infrastructure). Prove that the frozen operators of the canonical family (the vacuum carrier extA at zero curvature along the twist, the localized B, and the first-order coupling corrDeriv / the bilinear form 2<H0 C2_0(W0 u), J'>) commute with the two-site transverse translation action of twoSite_exact_symmetry, and with the U(1) (diagonal phase) symmetry if one exists for the vacuum background. Deduce the sector decomposition: an orthogonal (or unitary on the complexification) splitting of the carrier space into invariant character subspaces on which the operators act blockwise, with the dimension of each block independent of R up to the explicit collar length, and with the kernel at the crossing contained in one character block. Also prove the dilation identity the numerics suggest: the q-dilated character block is isometric to the q = 1 block with the same Bloch phase, with the operators corresponding. Publish compiled results in AHP/round10/shared/dictionary/. Build the minimum the nonvanishing track needs; ask in NOTES.md what it needs next round.",
  },
  {
    key: "nonvanishing",
    aim: "TRACK: NONVANISHING OF THE COUPLING. Find and formalise an argument that c1(q,R) != 0 (or the coupling form is definite on the crossing kernel) for infinitely many scales and radii. Work on the single character block (use the dictionary track's results from AHP/round10/shared/dictionary/ when available; until then work abstractly: state the block reduction as a hypothesis in a separate lemma, so the pieces snap together later). Candidate arguments: (a) TRANSFER MATRIX IN R: in one block, growing R by one adds one flat collar layer, so the crossing kernel restricted to the collar is a solution of a constant-coefficient linear recurrence; then c1(q, R) as a function of R is an explicit combination of powers of the recurrence roots, and you need only that it is not identically zero along some arithmetic progression of R, which follows from nonvanishing of a single leading constant or from two consecutive values (Mathlib has Algebra/LinearRecurrence.lean); (b) EXACT RATIONAL INSTANCE + ANALYTIC IDENTITY: at one small admissible (q,R) compute c1 exactly in Q(sqrt2) (h_0 = 36 sqrt2 - 50 suggests the entries live there) and transport by the recurrence/dilation; (c) UNIQUE CONTINUATION: a nonzero solution of the flat recurrence cannot vanish on two consecutive layers, so the coupling, which reads the kernel on the Omega_1 interface, is nonzero unless the kernel vanishes identically there; (d) SIGN: prove K(k) < 0 by an explicit positivity argument (the numerics show a definite sign on the whole relevant k range). Choose the route that minimises the Lean work. Formalise your chosen route in short files and publish compiled pieces in AHP/round10/shared/nonvanishing/.",
  },
  {
    key: "assembly",
    aim: "TRACK: ASSEMBLY AND CROSS-CHECK. (1) Each round, read everything in AHP/round10/shared/ and the other tracks' NOTES.md, and try to combine the compiled pieces with the round-9 bridge into a proof of one round-9 premise and hence GoalNeg2. Copy AHP/round9/qualitative-r2/Attempt.lean verbatim as the start of AHP/round10/assembly/rN/Attempt.lean and append. (2) Keep a precise list, in AHP/round10/shared/GAPS.md, of the exact Lean statements still missing between the shared pieces and the chosen premise; update it every round so the other tracks know what to build. (3) Independently test any claimed nonvanishing argument numerically at high precision on a case the authors did not use (another q, R, or the left twist), and record the result in GAPS.md. (4) If a cheaper premise appears (for example a free choice of exterior path or interior profile that makes the coupling easy to compute, via goalNeg2_of_cofinalAnyPathCoupling or goalNeg2_of_cofinalAnyProfileCoupling), pursue it.",
  },
];

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["track", "round", "files", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "remainingGap", "evidence"],
  properties: {
    track: { type: "string" },
    round: { type: "integer" },
    files: { type: "array", items: { type: "string" } },
    exitCode: { type: "integer" },
    closedGoal: { type: "string" },
    mainDeclaration: { type: "string" },
    axiomLine: { type: "string" },
    remainingGap: { type: "string" },
    evidence: { type: "string" },
  },
};

const verifySchema = {
  type: "object",
  additionalProperties: false,
  required: ["file", "recompiledExit", "statementMatchesPin", "pinUnchanged", "axiomsStandard", "forbiddenTokens", "noExtraHypotheses", "verdict", "reasons"],
  properties: {
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    statementMatchesPin: { type: "boolean" },
    pinUnchanged: { type: "boolean" },
    axiomsStandard: { type: "boolean" },
    forbiddenTokens: { type: "array", items: { type: "string" } },
    noExtraHypotheses: { type: "boolean" },
    verdict: { enum: ["closes-goal", "does-not-close"] },
    reasons: { type: "string" },
  },
};

async function retry(label, fn) {
  for (let attempt = 1; attempt <= 3; attempt++) {
    try {
      return await fn(attempt);
    } catch (err) {
      log(label + " attempt " + attempt + " failed: " + String(err).slice(0, 200));
    }
  }
  log(label + " gave up after 3 attempts");
  return null;
}

const history = [];
let closed = null;
for (let round = 1; round <= 4 && !closed; round++) {
  phase("Work");
  const outs = await parallel(tracks.map((t) => () => retry(t.key + ":r" + round, () => agent(
    COMMON + "\n\n" + t.aim + "\n\nROUND " + round + " of at most 4. Work in AHP/round10/" + t.key + "/r" + round + "/." +
      (history.length ? "\nAll earlier rounds (read the files they name; build on compiled work, do not redo it):\n" + JSON.stringify(history) : ""),
    { label: t.key + ":r" + round, phase: "Work", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
  ))));
  const roundRec = { round: round, results: outs };
  for (const a of outs) {
    if (!a || a.exitCode !== 0 || !/GoalNeg[12]/.test(a.closedGoal || "") || /^none/i.test(a.closedGoal || "")) continue;
    const file = a.files && a.files.length ? a.files[0] : "";
    const ver = await retry("verify:" + a.track + ":r" + round, () => agent(
      "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via AHP/round3/lean1.sh (long bash timeout; on timeout poll .exit, never relaunch; never lake build). Write only the files named below. VERIFY: copy " + file + " byte-for-byte to " + file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: (1) exit 0; (2) the main declaration " + a.mainDeclaration + " has type exactly GoalNeg2 (or GoalNeg1) of AHP/round3/guarded/pin/Statement.lean with no extra hypotheses; (3) the pin text appears unchanged; (4) every #print axioms line lists only propext, Classical.choice, Quot.sound; (5) no sorry, admit, axiom declaration, native_decide, unsafe, implemented_by, extern or opaque. closes-goal only if all pass. Write " + file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nClaim:\n" + JSON.stringify(a),
      { label: "verify:" + a.track + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
    ));
    roundRec.verify = ver;
    if (ver && ver.verdict === "closes-goal") { closed = { attempt: a, verify: ver }; break; }
  }
  history.push(roundRec);
  log("round " + round + (closed ? ": GoalNeg2 closed" : ": not closed"));
}

phase("Report");
const report = await retry("report", () => agent(
  "Workspace /home/sebastian/BalabanCoercivityLemma. Write AHP/round10/RESULTS.md in plain words: whether the guarded reading is now refuted in Lean (only if a verified attempt proves pinned GoalNeg2 or GoalNeg1 with no extra hypotheses), the decisive declarations (file, name, axiom line), and if not, the exact remaining Lean statement and why it resisted. Also state what the failure point shows: the carrier A is a unit there; which other inverses of the printed construction exist or are totalised. Do not edit other files. As your last action, call bb_workflow_result once.\n" + JSON.stringify({ closed: closed, history: history }),
  {
    label: "report",
    phase: "Report",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "high",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["status", "closedBy", "summary", "remaining"],
      properties: {
        status: { enum: ["closed-fails", "open"] },
        closedBy: { type: "array", items: { type: "string" } },
        summary: { type: "string" },
        remaining: { type: "string" },
      },
    },
  },
));

return { closed: closed, history: history, report: report };

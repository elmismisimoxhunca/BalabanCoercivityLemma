export const meta = {
  name: "guarded-noncancel",
  description: "Bounded Astra attempt on the last premise of the Ginv-only guarded reading (whole-kernel response noncancellation), two tracks for up to two rounds, then a required blueprint of the whole refutation.",
  phases: [
    { title: "Work", detail: "Noncancellation proof and kernel-structure tracks" },
    { title: "Verify", detail: "Astra recompiles any claimed premise or GoalNeg2" },
    { title: "Blueprint", detail: "Dependency blueprint from GoalNeg2 down to every leaf, compiled or open" },
  ],
};

const COMMON = [
  "GOAL. The Ginv-only guarded all-plaquette reading (pinned GoalNeg2 in AHP/round3/guarded/pin/Statement.lean: the negation of P428Target8SG selAll selAll) is reduced in Lean to ONE premise. Prove it, or prove a strictly weaker sufficient premise, or prove the premise is false.",
  "THE PREMISE. AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation, defined at AHP/round10/shared/assembly/R4_ResponseHull.lean:2550; equivalence with round-9 CofinalAnyPathCoupling at :2576 (cofinalAnyPathCoupling_iff_noCancellation, under RegularityFacts); round-9 bridge goalNeg2_of_cofinalAnyPathCoupling at AHP/round9/qualitative-r2/Attempt.lean:12102. In words: for infinitely many dyadic q = 2^j and, for each, infinitely many even R >= 18, some analytic exterior path V from the trivial field with a negative carrier direction at pi exists such that 0 is NOT in the closed convex hull of the response gradients of all unit vectors of the crossing kernel. Sufficient: CurlDetected for every kernel vector plus KernelLine (the whole crossing kernel is one charged complex line). Compiled tools: adaptive_energy and exists_profile_iff_curlDetected (shared/dictionary/R3_FreeSource.lean), curlDetected_of_topJet (shared/dictionary/R3_JetDetection.lean:2478, needs flat N unit and TopJetDetected), corrDeriv_profile_form (shared/assembly/R4_ResponseHull.lean:2169), U(1) and translation results (shared/dictionary/R1_Dictionary.lean). Compiled obstructions to shortcuts: exists_charged_invisible (shared/dictionary/R4_ColorResponse.lean:2168: a nonzero charged field with zero jet, not shown to be in a crossing kernel), no_profile_definite (shared/assembly/R2_ProfileQuantifiers.lean:47), switchingRoot_not_cofinal (shared/nonvanishing/R4_PolynomialCertificate.lean:286).",
  "FREEDOM YOU HAVE. You choose the scales, the radii (any infinite set of even R >= 18 per scale), and the exterior path V (any analytic path from the trivial field with a negative direction at pi). Use this: a path whose crossing kernel is forced to be small (one charged line, by symmetry plus a simple eigenvalue) or whose kernel vectors all have nonzero top jet makes the premise much easier. The left twist (AHP/round9/analytic-r2, leftTwist) removes a degenerate left/right splitting.",
  "READ FIRST: AHP/round10/RESULTS.md, AHP/round10/shared/GAPS.md, AHP/round10/shared/COORDINATOR.md, the round-10 NOTES.md files, AHP/round9/*/NOTES.md, AHP/round8/guarded-idea/IDEA.md.",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma. Write only under AHP/round12/<track>/ and AHP/round12/shared/. Do not edit lean/, paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "COMPILING. 16 GB RAM, 8 GB per command. Compile ONLY with AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs; writes .log and .exit); long bash timeout; on timeout poll .exit, never relaunch. Compact files only: copy needed definitions verbatim, import only frozen lean/src modules; NEVER compile the 12k-line round-9 file or the round-10 assembly Attempt.lean. Never run lake build or REPRODUCE.sh. No sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath for evidence only (jobs under 2 GB).",
  "DELIVERABLES in AHP/round12/<track>/rN/: compiled .lean with .log/.exit, NOTES.md with the exact Lean statement of what is left. Never call a conditional result a proof.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const tracks = [
  { key: "noncancel", aim: "TRACK: PROVE NONCANCELLATION. Choose a path and scale/radius family that makes the crossing kernel tractable, and prove CofinalAnyPathNoResponseCancellation for it (or KernelLine + CurlDetected). Candidate routes: (a) a path with enough symmetry that the crossing kernel lies in one charged character and is one complex line, proved by symmetry plus a simple-eigenvalue argument at the vacuum crossing; (b) prove TopJetDetected for every nonzero vector of the crossing kernel by showing the crossing kernel vectors are boundary Green's functions that cannot vanish on the level-1 interface (unique continuation for the flat recurrence on the collar); (c) any argument that the response gradients of unit kernel vectors stay in an open half-space. Publish compiled pieces in AHP/round12/shared/." },
  { key: "kernel", aim: "TRACK: CROSSING-KERNEL STRUCTURE AND CROSS-CHECK. Build what the noncancellation track needs about the vacuum crossing kernel: its dimension, its character decomposition, simplicity at the first crossing for a chosen path, and the absence of charged-invisible vectors (exists_charged_invisible) in it. Test every claim numerically at high precision on cases the other track did not use, and record in AHP/round12/shared/GAPS.md the exact Lean statements still missing between the shared pieces and the premise. If you find the premise FALSE for every admissible path (e.g. kernel cancellation forced), prove that instead." },
];

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["track", "round", "files", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "remainingGap", "evidence"],
  properties: {
    track: { type: "string" }, round: { type: "integer" }, files: { type: "array", items: { type: "string" } },
    exitCode: { type: "integer" }, closedGoal: { type: "string" }, mainDeclaration: { type: "string" },
    axiomLine: { type: "string" }, remainingGap: { type: "string" }, evidence: { type: "string" },
  },
};

const verifySchema = {
  type: "object",
  additionalProperties: false,
  required: ["file", "recompiledExit", "statementCorrect", "axiomsStandard", "forbiddenTokens", "noExtraHypotheses", "verdict", "reasons"],
  properties: {
    file: { type: "string" }, recompiledExit: { type: "integer" }, statementCorrect: { type: "boolean" },
    axiomsStandard: { type: "boolean" }, forbiddenTokens: { type: "array", items: { type: "string" } },
    noExtraHypotheses: { type: "boolean" }, verdict: { enum: ["accept", "reject"] }, reasons: { type: "string" },
  },
};

async function retry(label, fn) {
  for (let attempt = 1; attempt <= 3; attempt++) {
    try { return await fn(attempt); } catch (err) { log(label + " attempt " + attempt + " failed: " + String(err).slice(0, 200)); }
  }
  log(label + " gave up after 3 attempts");
  return null;
}

const history = [];
let closed = null;
for (let round = 1; round <= 2 && !closed; round++) {
  phase("Work");
  const outs = await parallel(tracks.map((t) => () => retry(t.key + ":r" + round, () => agent(
    COMMON + "\n\n" + t.aim + "\n\nROUND " + round + " of 2. Work in AHP/round12/" + t.key + "/r" + round + "/." +
      (history.length ? "\nEarlier round (build on compiled work):\n" + JSON.stringify(history) : ""),
    { label: t.key + ":r" + round, phase: "Work", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
  ))));
  const rec = { round: round, results: outs, verify: [] };
  for (const a of outs) {
    if (!a || a.exitCode !== 0 || !a.closedGoal || /^none/i.test(a.closedGoal)) continue;
    const file = a.files && a.files.length ? a.files[0] : "";
    const ver = await retry("verify:" + a.track + ":r" + round, () => agent(
      "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via AHP/round3/lean1.sh (long timeout; poll .exit on timeout; never relaunch; never lake build). Write only the files named below. VERIFY: copy " + file + " to " + file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: exit 0; the main declaration " + a.mainDeclaration + " has exactly the claimed type (" + a.closedGoal + "): either CofinalAnyPathNoResponseCancellation (or CofinalAnyPathCoupling, CofinalCanonicalCoupling, or another round-9/10 premise whose bridge to GoalNeg2 is compiled), or GoalNeg2 itself, or the negation of the premise; every copied definition matches its source verbatim; no extra hypotheses; every #print axioms line lists only propext, Classical.choice, Quot.sound; no forbidden token. Write " + file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nClaim:\n" + JSON.stringify(a),
      { label: "verify:" + a.track + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
    ));
    rec.verify.push(ver);
    if (ver && ver.verdict === "accept") { closed = { attempt: a, verify: ver }; break; }
  }
  history.push(rec);
  log("round " + round + (closed ? ": premise settled" : ": not settled"));
}

phase("Blueprint");
const blueprint = await retry("blueprint", () => agent(
  COMMON.split("\n").filter((l) => !l.startsWith("GOAL") && !l.startsWith("FREEDOM")).join("\n") +
    "\n\nWRITE THE BLUEPRINT of the Ginv-only guarded refutation, whatever this run's outcome. Output AHP/round12/BLUEPRINT.md (Markdown with LaTeX) and AHP/round12/blueprint/content.tex (leanblueprint-style LaTeX: one \\begin{theorem}/\\begin{lemma}/\\begin{definition} per node, with \\label, \\lean{fully.qualified.Name}, \\uses{...}, and \\leanok exactly when the declaration is compiled with standard axioms; mark open nodes without \\leanok). Coverage: start at the pinned target GoalNeg2 (AHP/round3/guarded/pin/Statement.lean) and its equivalences (GoalNeg1, GuardPencilT, P428Target8SG, boundary-response forms from rounds 2-3), then every bridge and reduction actually compiled in rounds 4 to 12 down to the leaves: the remaining open premise(s) and the unconditional facts used. For each node give: plain-mathematics statement (one to three sentences, Balaban notation where possible), Lean name, file:line, compiled status with the axiom line from its log, and direct dependencies. Mark separately: (1) compiled and independently verified; (2) compiled by a builder only; (3) assembled but uncompiled because of memory (the round-9 regularity specialisation, the round-10 assembly joins); (4) open. Include the numerical evidence for each open leaf (values, precision, file) clearly labelled as evidence. End with: the single shortest path from the open leaf to GoalNeg2, the list of memory-blocked joins that need a large-RAM compile, and what the failure point shows (carrier A a unit, corrected G1 not, which other inverses exist). Verify every file:line and every \\leanok against the actual logs; do not invent names. Do not edit other files.\nThis run's results:\n" + JSON.stringify({ closed: closed, history: history }),
  {
    label: "blueprint",
    phase: "Blueprint",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "xhigh",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["markdown", "tex", "nodes", "compiledNodes", "openNodes", "memoryBlockedNodes", "status"],
      properties: {
        markdown: { type: "string" }, tex: { type: "string" }, nodes: { type: "integer" },
        compiledNodes: { type: "integer" }, openNodes: { type: "array", items: { type: "string" } },
        memoryBlockedNodes: { type: "array", items: { type: "string" } },
        status: { enum: ["refuted-in-lean", "refuted-modulo-memory-blocked-joins", "open"] },
      },
    },
  },
));

return { closed: closed, history: history, blueprint: blueprint };

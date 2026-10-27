export const meta = {
  name: "guarded-star",
  description: "Round 13 on the Ginv-only guarded reading: close the three physical inputs for the round-12 right-star family (negative half-pi trial, zero-coordinate carrier positivity, curl detection at the crossing), assemble, and update the blueprint. Astra only.",
  phases: [
    { title: "Work", detail: "Trial, positivity, detection, assembly tracks" },
    { title: "Verify", detail: "Astra recompiles any claimed premise or GoalNeg2" },
    { title: "Blueprint", detail: "Update the round-12 blueprint with this round's nodes" },
  ],
};

const COMMON = [
  "CONTEXT. Read in full first: AHP/round12/BLUEPRINT.md (sections on the mathematical spine and open nodes), AHP/round12/shared/GAPS.md (kernel round 2, 'Exact remaining physical statements for one consistently RIGHT star'), AHP/round12/shared/noncancel/R2_NOTES.md (sections A-D and 'Late kernel-track evidence: concrete half-pi trial'), AHP/round12/shared/COORDINATOR.md, AHP/round12/noncancel/r2/NOTES.md, AHP/round12/kernel/r2/NOTES.md.",
  "GOAL. Prove the pinned GoalNeg2 (AHP/round3/guarded/pin/Statement.lean) via the round-12 route: for the right-star family (AdalyFormal.Round12.Noncancel.RightFamily, cofinal_rightStar_paths in AHP/round12/shared/noncancel/R2_RightFamily.lean / R2_StarLocal.lean), prove (P1) a physical negative trial at angle pi/2, (P2) strict full-carrier positivity on the subspace where the central charged coordinate vanishes, up to the crossing, and (P3) CurlDetected (or TopJetDetected) for the actual crossing generator, all with the nested cofinal quantifiers. Then R2_FirstCrossing (AHP/round12/shared/kernel/R2_FirstCrossing.lean) gives the crossing in (0, pi/2) and KernelLine from P1+P2, R2_ResponseLine.cofinal_noCancellation_of_curlLine gives CofinalAnyPathNoResponseCancellation from KernelLine+P3, and the round-9/10 bridges give GoalNeg2. Exact Lean forms of P1-P3 are in the GAPS/NOTES sections named above; use them verbatim.",
  "NUMERICAL EVIDENCE (round 12, not proofs): P1: the finite trial centre 1, four normal neighbours +/- i/4, one tangent -i/4 gives local mass 21/16 + flat 15/16 - star 5/2 = -1/4, identical at q2R20, q4R22, q8R24 (kernel/r2/TRIAL_CHECKS.json). P2: central-zero Schur minimum about 0.93 at the crossing (q=1,R=20; q=2,R=20). P3: tangential physical jet about 3.77e-75 at q=2,R=20, stable to 1e-113. Crossing angle about 1.2080 (right star), next charged Schur eigenvalue about 0.932.",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma. Write only under AHP/round13/<track>/ and AHP/round13/shared/. Do not edit lean/, paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "COMPILING. The machine currently has 78 GB, but each bb command is capped at 8 GB. Compile ONLY with AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs; writes .log and .exit); long bash timeout; on timeout poll .exit, never relaunch. Compact files only (copy needed definitions verbatim from the round-12 shared files; import only frozen lean/src modules). Never run lake build or REPRODUCE.sh. No sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath for evidence only (under 2 GB).",
  "DELIVERABLES in AHP/round13/<track>/rN/: compiled .lean with .log/.exit, NOTES.md with the exact Lean statement of anything still missing. Publish reusable compiled pieces in AHP/round13/shared/<track>/. Never call a conditional result a proof.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const tracks = [
  { key: "trial", aim: "TRACK P1: NEGATIVE HALF-PI TRIAL. Turn the -1/4 finite-stencil computation into a Lean theorem about the actual frozen carrier on the right-star family at every chosen scale and radius: prove the periodic embedding of the stencil has no collisions, that the actual plaquette sum over the stencil equals the local formula (use R2_StarLocal's frozen three-form and plaquette identities), that the mass on the stencil equals the local unit mass exactly (an UPPER bound or equality is needed; leaf_mass_le is only a lower bound), and that higher-level mass and W/T contributions vanish on it (R2_Boundary gives W = A on omitted plaquette edges). Conclude <v, A(pi/2) v> < 0 with an explicit v. This is the most finite of the three inputs; finish it first and publish it." },
  { key: "positivity", aim: "TRACK P2: ZERO-COORDINATE POSITIVITY. Prove strict positivity of the actual full carrier on the subspace where the central charged coordinate vanishes, for every angle in [0, the crossing] (or [0, pi/2]), at every chosen scale and radius. Decompose the carrier as (flat localized part, positive definite with a uniform constant from the frozen proof: see AHP/round4/guarded/MINE.md) + (star perturbation supported on the finitely many star plaquettes); show the star perturbation is only negative through the central charged coordinate (the round-12 local forms R2_FullPlaquette, R2_Mass retain the neutral square and the eight distinct leaves), so on its complement it is bounded below by the flat part minus an explicit, scale-independent constant smaller than the flat constant. Prove whatever uniform lower bound this needs in Lean." },
  { key: "detection", aim: "TRACK P3: DETECTION AT THE CROSSING. Prove CurlDetected (or TopJetDetected, via curlDetected_of_topJet in AHP/round10/shared/dictionary/R3_JetDetection.lean:2478, which needs the flat N unit) for the actual crossing generator of the right-star family. The generator is a boundary-localized mode; its level-1 jet is exponentially small but nonzero. Routes: unique continuation on the flat collar (a nonzero solution of the flat recurrence cannot vanish on two consecutive layers, so its trace on the Omega_1 interface is nonzero), combined with the dictionary identity that turns a nonzero interface trace into a nonzero top jet; or a sign argument for the tangential jet component. Use AHP/round10/nonvanishing (R1_RecurrenceNonvanishing, R2_SourceFamily) and AHP/round12/kernel/r2/ActualResponse.lean." },
  { key: "assembly", aim: "TRACK: ASSEMBLY. Each round, read AHP/round13/shared/ and the other tracks' NOTES.md, and combine compiled pieces with R2_FirstCrossing, R2_ResponseLine and the round-9 bridge into CofinalAnyPathNoResponseCancellation and then GoalNeg2. Keep AHP/round13/shared/GAPS.md current with the exact missing Lean statements. Separately, repair the round-10 broken join: in AHP/round13/assembly/, make a copy of AHP/round10/assembly/r4/Attempt.lean with the missing helpers (half_twice, half_average, phase_axis_fixed and anything they need, copied verbatim from AHP/round10/shared/dictionary/R4_ColorResponse.lean) inserted before the Color section, and compile it once with lean1.sh in a bb terminal (not a bash command: the file needs more than 8 GB; it compiled in about 10 minutes on 78 GB). Record the result." },
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
    COMMON + "\n\n" + t.aim + "\n\nROUND " + round + " of 2. Work in AHP/round13/" + t.key + "/r" + round + "/." +
      (history.length ? "\nEarlier round (build on compiled work, do not redo it):\n" + JSON.stringify(history) : ""),
    { label: t.key + ":r" + round, phase: "Work", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
  ))));
  const rec = { round: round, results: outs, verify: [] };
  for (const a of outs) {
    if (!a || a.exitCode !== 0 || !a.closedGoal || /^none/i.test(a.closedGoal)) continue;
    const file = a.files && a.files.length ? a.files[0] : "";
    const ver = await retry("verify:" + a.track + ":r" + round, () => agent(
      "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via AHP/round3/lean1.sh (long timeout; poll .exit on timeout; never relaunch; never lake build). Write only the files named below. VERIFY: copy " + file + " to " + file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: exit 0; the main declaration " + a.mainDeclaration + " has exactly the claimed type (" + a.closedGoal + ") and that type is GoalNeg2 of AHP/round3/guarded/pin/Statement.lean, or CofinalAnyPathNoResponseCancellation / another round-9-12 premise whose compiled bridge to GoalNeg2 exists, or one of P1-P3 in the exact form recorded in AHP/round12/shared/GAPS.md; every copied definition matches its source verbatim; no extra hypotheses; every #print axioms line lists only propext, Classical.choice, Quot.sound; no forbidden token. Write " + file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nClaim:\n" + JSON.stringify(a),
      { label: "verify:" + a.track + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
    ));
    rec.verify.push({ track: a.track, claim: a.closedGoal, verify: ver });
    if (ver && ver.verdict === "accept" && /GoalNeg2|NoResponseCancellation/.test(a.closedGoal)) { closed = { attempt: a, verify: ver }; }
  }
  history.push(rec);
  log("round " + round + (closed ? ": premise or goal settled" : ": not settled"));
}

phase("Blueprint");
const blueprint = await retry("blueprint", () => agent(
  COMMON.split("\n").filter((l) => !l.startsWith("GOAL")).join("\n") +
    "\n\nUPDATE THE BLUEPRINT. Copy AHP/round12/BLUEPRINT.md and AHP/round12/blueprint/content.tex to AHP/round13/BLUEPRINT.md and AHP/round13/blueprint/content.tex, then update them with every round-13 node: new compiled declarations (with file:line, axiom line from the log, status A/B per the round-12 convention), changes of status of P1, P2, P3 and of the round-10 join (C-broken -> compiled, if the assembly track's repaired compile succeeded), and the new shortest path to GoalNeg2. Verify every file:line and every \\leanok against the logs; do not invent names. Add a short changelog section at the top listing what changed since round 12. Do not edit other files.\nThis run's results:\n" + JSON.stringify({ closed: closed, history: history }),
  {
    label: "blueprint", phase: "Blueprint", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh",
    schema: {
      type: "object", additionalProperties: false,
      required: ["markdown", "tex", "nodes", "compiledNodes", "openNodes", "status"],
      properties: {
        markdown: { type: "string" }, tex: { type: "string" }, nodes: { type: "integer" }, compiledNodes: { type: "integer" },
        openNodes: { type: "array", items: { type: "string" } },
        status: { enum: ["refuted-in-lean", "open"] },
      },
    },
  },
));

return { closed: closed, history: history, blueprint: blueprint };

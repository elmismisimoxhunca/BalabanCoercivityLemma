export const meta = {
  name: "guarded-p3",
  description: "Round 14 on the Ginv-only guarded reading: prove P3 (curl detection of the right-star crossing generator), the last input of the compiled P3 -> GoalNeg2 bridge, and update the blueprint. Kimi K3.1 Pro.",
  phases: [
    { title: "Work", detail: "Transfer, cancellation, path-choice and assembly tracks on P3" },
    { title: "Verify", detail: "Astra recompiles any claimed premise or GoalNeg2" },
    { title: "Blueprint", detail: "Update the round-13 blueprint with this round's nodes" },
  ],
};

const COMMON = [
  "CONTEXT. Read in full first: AHP/round13/BLUEPRINT.md (changelog, verdict, mathematical spine, open node P3), AHP/round13/shared/GAPS.md, AHP/round13/shared/detection/R2_NOTES.md and AHP/round13/detection/r2/NOTES.md (exact P3 remainders, area dictionary, numerical cell ratios), AHP/round13/detection/r1/NOTES.md.",
  "GOAL. Prove P3, verbatim from AHP/round13/shared/assembly/R2_P2Goal.lean:8327: forall {q R} (hq : 0 < q) (hR : 2 | R) (hR18 : 18 <= R) (u : TwistSpace q R), KernelLine q R (rightStar hq R) u -> CurlDetected q R u; or the cofinal form CofinalP3 (:11078), whose bridge goalNeg2_of_cofinalP3 (:11093) is compiled. goalNeg2_of_P3 (:11077) then gives the pinned GoalNeg2. Already compiled and independently verified: rightStar_kernelLine (:11050: crossing in (0,pi/2), whole kernel one charged line, real finrank 2), flat_N_unit (detection r1), curlDetected_of_topJet (round10 R3_JetDetection.lean:2478), and crossing_physicalJetAggregate_area (AHP/round13/shared/detection/R2_PhysicalArea.lean: for the KernelLine generator, physicalJetAggregate = (1/2) * areaSum with true W/C2 coefficients). So P3 reduces to: the weighted mixed-colour areaSum of the crossing generator is nonzero at some physical top row.",
  "NUMERICAL EVIDENCE (not proofs): tangential physical jet about 3.77e-75 at q=2,R=20 (right star), stable to 1e-113 across 120/155 digits; max |cell|/|sum| about 27.07, 1.63, 1.63 (mixed cell signs, heavy cancellation, so a naive common-sign argument fails); crossing angle about 1.20803; next charged Schur eigenvalue about 0.932.",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma. Write only under AHP/round14/<track>/ and AHP/round14/shared/. Do not edit lean/, paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "COMPILING. Each bb command is capped at 8 GB. Compile ONLY with AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs; writes .log and .exit); long bash timeout; on timeout poll .exit, never relaunch. Compact files only (copy needed definitions verbatim from the round-13 shared files; import only frozen lean/src modules). Never run lake build or REPRODUCE.sh. No sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath for evidence only (under 2 GB).",
  "DELIVERABLES in AHP/round14/<track>/rN/: compiled .lean with .log/.exit, NOTES.md with the exact Lean statement of anything still missing. Publish reusable compiled pieces in AHP/round14/shared/<track>/. Never call a conditional result a proof.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const tracks = [
  { key: "transfer", aim: "TRACK: TRANSFER ACROSS THE COLLAR. The crossing generator solves the flat recurrence on the collar between the star and Omega_1. Express the top-row areaSum as a fixed linear functional of the generator's two-layer data at the star side, transported by the explicit flat transfer matrix (constant coefficients, eigenvalues rho, 1/rho in each transverse character). Then nonvanishing reduces to: the functional applied to rho^(2RM)-weighted data is nonzero, i.e. a single leading constant times a nonzero two-layer seed, plus an exponentially smaller remainder. Use detection r1 Transfer.lean (finite two-layer continuation, area propagation) and round-10 R1_TransferNonvanishing / R1_RecurrenceNonvanishing. A sparse cofinal sequence of R is allowed (CofinalP3 needs only infinitely many R per scale)." },
  { key: "cancellation", aim: "TRACK: STRUCTURE OF THE AREA SUM. Find an exact identity or sign structure that controls the weighted mixed-colour areaSum despite cancellation: e.g. since the kernel is one complex line, the sum is |c|^2 times a fixed number per instance; compute that number in closed form on the collar, or find a telescoping/summation-by-parts identity reducing it to a boundary term of fixed sign. Use R2_Area, R2_ColorArea, R2_PhysicalArea and the U(1)/quarter-gauge symmetry of the line." },
  { key: "pathchoice", aim: "TRACK: A BETTER PATH. CofinalAnyPathNoResponseCancellation lets you choose the exterior path. If the right star's areaSum is hard, design a modified star (different arm lengths, an added tangential arm, a left/right double star, or a placement that makes the crossing mode overlap Omega_1 more strongly) for which detection is easy (e.g. a single dominant cell), and re-establish P1, P2 and the kernel line for it by reusing the round-13 proofs (R1_Trial, R2_P2, R2_P2Goal) with minimal changes. Check numerically first that the new family has no heavy cancellation." },
  { key: "assembly", aim: "TRACK: ASSEMBLY. Each round, read AHP/round14/shared/ and the other tracks' NOTES.md; combine any P3 (or path-variant P1+P2+P3) proof with the compiled bridges into GoalNeg2. Keep AHP/round14/shared/GAPS.md current with the exact missing Lean statements, and test any claimed nonvanishing argument numerically at high precision on a case its authors did not use." },
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
    COMMON + "\n\n" + t.aim + "\n\nROUND " + round + " of 2. Work in AHP/round14/" + t.key + "/r" + round + "/." +
      (history.length ? "\nEarlier round (build on compiled work, do not redo it):\n" + JSON.stringify(history) : ""),
    { label: t.key + ":r" + round, phase: "Work", model: "cpa/kimi-k3.1-pro", reasoningLevel: "max", schema: attemptSchema },
  ))));
  const rec = { round: round, results: outs, verify: [] };
  for (const a of outs) {
    if (!a || a.exitCode !== 0 || !a.closedGoal || /^none/i.test(a.closedGoal)) continue;
    const file = a.files && a.files.length ? a.files[0] : "";
    const ver = await retry("verify:" + a.track + ":r" + round, () => agent(
      "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via AHP/round3/lean1.sh (long timeout; poll .exit on timeout; never relaunch; never lake build). Write only the files named below. VERIFY: copy " + file + " to " + file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: exit 0; the main declaration " + a.mainDeclaration + " has exactly the claimed type (" + a.closedGoal + ") and that type is GoalNeg2 of AHP/round3/guarded/pin/Statement.lean, or CofinalAnyPathNoResponseCancellation / another round-9-12 premise whose compiled bridge to GoalNeg2 exists, or P3 or CofinalP3 exactly as in AHP/round13/shared/assembly/R2_P2Goal.lean (or a path-variant premise with a compiled bridge to GoalNeg2); every copied definition matches its source verbatim; no extra hypotheses; every #print axioms line lists only propext, Classical.choice, Quot.sound; no forbidden token. Write " + file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nClaim:\n" + JSON.stringify(a),
      { label: "verify:" + a.track + ":r" + round, phase: "Verify", model: "cpa/kimi-k3.1-pro", reasoningLevel: "high", schema: verifySchema },
    ));
    rec.verify.push({ track: a.track, claim: a.closedGoal, verify: ver });
    if (ver && ver.verdict === "accept" && /GoalNeg2|NoResponseCancellation|P3/.test(a.closedGoal)) { closed = { attempt: a, verify: ver }; }
  }
  history.push(rec);
  log("round " + round + (closed ? ": premise or goal settled" : ": not settled"));
}

phase("Blueprint");
const blueprint = await retry("blueprint", () => agent(
  COMMON.split("\n").filter((l) => !l.startsWith("GOAL")).join("\n") +
    "\n\nUPDATE THE BLUEPRINT. Copy AHP/round13/BLUEPRINT.md and AHP/round13/blueprint/content.tex to AHP/round14/BLUEPRINT.md and AHP/round14/blueprint/content.tex, then update them with every round-14 node: new compiled declarations (with file:line, axiom line from the log, status A/B per the round-12 convention), the change of status of P3 and of GoalNeg2, and the new shortest path to GoalNeg2. Verify every file:line and every \\leanok against the logs; do not invent names. Add a short changelog section at the top listing what changed since round 13. Do not edit other files.\nThis run's results:\n" + JSON.stringify({ closed: closed, history: history }),
  {
    label: "blueprint", phase: "Blueprint", model: "cpa/kimi-k3.1-pro", reasoningLevel: "max",
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

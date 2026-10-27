export const meta = {
  name: "guarded-collar",
  description: "Round 15 on the Ginv-only guarded reading: build the physical collar-recurrence dictionary for the frozen right-star operator and prove AreaSeedRightStar (one nonzero area sum per instance), closing GoalNeg2 through the compiled chain; update the blueprint. Kimi K3.1 Pro.",
  phases: [
    { title: "Work", detail: "Collar dictionary, seed, numerics and assembly tracks" },
    { title: "Verify", detail: "Kimi independently recompiles claimed premises or GoalNeg2" },
    { title: "Blueprint", detail: "Update the round-14 blueprint with this round's nodes" },
  ],
};

const COMMON = [
  "CONTEXT. Read in full first: AHP/round14/BLUEPRINT.md (changelog, verdict, open node), AHP/round14/shared/GAPS.md, and AHP/round14/{transfer,cancellation,pathchoice,assembly}/r2/NOTES.md.",
  "GOAL. Prove AdalyFormal.Round14.Transfer.Physical.AreaSeedRightStar (exact statement in AHP/round14/shared/GAPS.md and AHP/round14/transfer/r2/NOTES.md): forall {q R} (hq : 0 < q) (hR : 2 | R) (hR18 : 18 <= R), exists u : TwistSpace q R, KernelLine q R (rightStar hq R) u and exists j, exists hj : j < blockCount q R, areaSum hq hj u != 0; or its cofinal form CofinalUnitDominantAreaSeed / CofinalLaurentAreaSeed (only infinitely many dyadic q and, for each, infinitely many even R are needed). The chain AreaSeedRightStar -> P3 -> GoalNeg2 is compiled (assembly r1 p3_of_areaNonvanishing, assembly r2 areaNonvanishing_of_areaSeed, round13 goalNeg2_of_P3 in AHP/round13/shared/assembly/R2_P2Goal.lean:11077). Compiled facts to use: rightStar_kernelLine (crossing in (0,pi/2), kernel one charged line); chargedArea_eq_sesquilinear and the (a^2+b^2) scaling (area is one number per instance); transfer r2 Collar.lean (two-layer quadratic coefficients, Laurent and dominant normalized-limit nonvanishing); flat_N_unit.",
  "THE MISSING STEP every round-14 track hit: an exact dictionary between the FROZEN right-star operator restricted to the flat collar (between the star and Omega_1) and an explicit constant-coefficient recurrence, so that the crossing generator on the collar is an explicit combination of the recurrence modes and the top-row areaSum is an explicit function of R with a computable leading coefficient. With that, nonvanishing reduces to one leading constant being nonzero (Laurent/dominant interfaces already compiled).",
  "RESEARCH CAUTION. The scalar-mode recurrence, fixed-size leading coefficient, and dominant-mode ansatz below are proposals to test, not established physical facts. Derive the actual matrix recurrence from the frozen operator; report any obstruction instead of assuming scalar decoupling, nonzero quadratic area from a nonzero vector, radius-independent seed, or an unproved spectral gap. Cofinal Laurent/dominant certificates are sufficient conditions, not asserted equivalent to P3. Prioritize the exact physical dictionary over more generic conditional interfaces.",
  "NUMERICAL EVIDENCE (not proofs): right star, top-row area sums nonzero and stable at q=1, R=20..28 (120/155 digits); all 84 q=1,R=20 row aggregates positive; last-row radius ratio about 13429.238, normalized coefficient about 0.0133612072; a same-row three-term Laurent fit through R=26 FAILED held-out R=28, so the true recurrence is not that naive one (the transverse character mixing or the interface rows matter). Tail star at q=4: all 256 cells positive.",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma. Write only under AHP/round15/<track>/ and AHP/round15/shared/. Do not edit lean/, paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "COMPILING. Each bb command is capped at 8 GB. Compile ONLY with bb heavy run -- AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs; writes .log and .exit); use a long bash timeout. On timeout inspect processes and .exit before any retry; use an event/timer subscription for unfinished work, never a sleep-and-check loop or duplicate compile. Compact files only (copy needed definitions verbatim from earlier shared files; import only frozen lean/src modules). Never run lake build or REPRODUCE.sh. No sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath for evidence only (under 2 GB).",
  "DELIVERABLES in AHP/round15/<track>/rN/: compiled .lean with .log/.exit, NOTES.md with the exact Lean statement of anything still missing. Publish reusable compiled pieces in AHP/round15/shared/<track>/. Never call a conditional result an unconditional proof. Put the .lean file containing mainDeclaration first in the files result array. On a retry inspect existing processes, sources, logs and .exit files before starting anything; reuse completed work.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const tracks = [
  { key: "dictionary", aim: "TRACK: COLLAR DICTIONARY. Prove in Lean that on the flat collar the frozen right-star carrier (vacA at the crossing, after the round-12 star reduction) acts by an explicit constant-coefficient operator: per layer a fixed finite matrix in each transverse character (use the compiled two-site translation symmetry, round6 twoSite_exact_symmetry and round10 R1_Dictionary, and the charged U(1) line), so that kernel vectors satisfy an explicit second-order matrix recurrence between layers with an invertible transfer matrix. State the recurrence, its transfer matrix and its eigenvalues (rho, 1/rho per character) exactly. First identify numerically, with the existing high-precision scripts, the exact per-layer recurrence that the crossing generator satisfies (the naive same-row fit failed: include interface rows and character coupling), then formalise exactly that." },
  { key: "seed", aim: "TRACK: SEED AND LEADING CONSTANT. Using the dictionary (from AHP/round15/shared/dictionary when available; until then state it as an explicit hypothesis in a separate lemma so pieces snap together), express the top-row areaSum of the crossing generator as (leading constant) * rho^(2 R M-dependent power) * |seed|^2 + exponentially smaller remainder, with the seed the generator's two-layer data at the star side (nonzero by flat unique continuation, transfer r1 Transfer.lean) and the leading constant computed in closed form on a FIXED-size problem (the star neighbourhood plus the Omega_1 interface rows), independent of R. Prove the constant is nonzero (an exact rational or algebraic-number computation on a fixed finite matrix is acceptable, e.g. norm_num/decide on explicit rationals or Q(sqrt2)), and conclude CofinalUnitDominantAreaSeed or AreaSeedRightStar via the compiled Laurent/dominant interfaces." },
  { key: "numerics", aim: "TRACK: EXACT NUMERICS FOR THE OTHER TWO. Provide, at high precision, (1) the exact per-layer recurrence the crossing generator satisfies on the collar, character by character, including the interface rows, with residuals; (2) the leading constant and its stability across R (R = 18..40, q = 1, 2, 4); (3) an exact rational or Q(sqrt2) closed form for the fixed finite matrices whose determinant/entry gives the leading constant, if one exists. Publish in AHP/round15/shared/numerics/ with scripts and a short README that the Lean tracks can follow. Also try to reproduce the failed same-row Laurent fit and explain why it failed." },
  { key: "assembly", aim: "TRACK: ASSEMBLY. Each round, read AHP/round15/shared/ and the other tracks' NOTES.md; combine any dictionary + seed results with the compiled chain AreaSeedRightStar -> P3 -> GoalNeg2 into GoalNeg2. Keep AHP/round15/shared/GAPS.md current with the exact missing Lean statements, and re-test any claimed nonvanishing on cases its authors did not use." },
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
    COMMON + "\n\n" + t.aim + "\n\nROUND " + round + " of 2. Work in AHP/round15/" + t.key + "/r" + round + "/." +
      (history.length ? "\nEarlier round (build on compiled work, do not redo it):\n" + JSON.stringify(history) : ""),
    { label: t.key + ":r" + round, phase: "Work", model: "cpa/kimi-k3.1-pro", reasoningLevel: "max", schema: attemptSchema },
  ))));
  const rec = { round: round, results: outs, verify: [] };
  for (const a of outs) {
    if (!a || a.exitCode !== 0 || !a.closedGoal || /^none/i.test(a.closedGoal)) continue;
    const file = a.files && a.files.length ? a.files[0] : "";
    const ver = await retry("verify:" + a.track + ":r" + round, () => agent(
      "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via bb heavy run -- AHP/round3/lean1.sh (long timeout; on timeout inspect existing processes and .exit, then use an event/timer subscription if needed; never duplicate a running compile; never lake build). Write only the files named below. VERIFY: copy " + file + " to " + file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: exit 0; the main declaration " + a.mainDeclaration + " has exactly the claimed type (" + a.closedGoal + ") and that type is GoalNeg2 of AHP/round3/guarded/pin/Statement.lean, or CofinalAnyPathNoResponseCancellation / another round-9-12 premise whose compiled bridge to GoalNeg2 exists, or AreaSeedRightStar or one of its compiled cofinal forms (CofinalUnitDominantAreaSeed, CofinalLaurentAreaSeed) exactly as in AHP/round14/shared/GAPS.md, or P3/CofinalP3 as in AHP/round13/shared/assembly/R2_P2Goal.lean; every copied definition matches its source verbatim; no extra hypotheses; every #print axioms line lists only propext, Classical.choice, Quot.sound; no forbidden token. Write " + file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nClaim:\n" + JSON.stringify(a),
      { label: "verify:" + a.track + ":r" + round, phase: "Verify", model: "cpa/kimi-k3.1-pro", reasoningLevel: "high", schema: verifySchema },
    ));
    rec.verify.push({ track: a.track, claim: a.closedGoal, verify: ver });
    if (ver && ver.verdict === "accept" && /^GoalNeg2$/.test(a.closedGoal)) { closed = { attempt: a, verify: ver }; }
  }
  history.push(rec);
  log("round " + round + (closed ? ": premise or goal settled" : ": not settled"));
}

phase("Blueprint");
const blueprint = await retry("blueprint", () => agent(
  COMMON.split("\n").filter((l) => !l.startsWith("GOAL")).join("\n") +
    "\n\nUPDATE THE BLUEPRINT. Copy AHP/round14/BLUEPRINT.md and AHP/round14/blueprint/content.tex to AHP/round15/BLUEPRINT.md and AHP/round15/blueprint/content.tex, then update them with every round-15 node: new compiled declarations (with file:line, axiom line from the log, status A/B per the round-12 convention), the change of status of AreaSeedRightStar, P3 and GoalNeg2, and the new shortest path to GoalNeg2. Verify every file:line and every \\leanok against the logs; do not invent names. Add a short changelog section at the top listing what changed since round 14. Do not edit other files.\nThis run's results:\n" + JSON.stringify({ closed: closed, history: history }),
  {
    label: "blueprint", phase: "Blueprint", model: "cpa/kimi-k3.1-pro", reasoningLevel: "high",
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

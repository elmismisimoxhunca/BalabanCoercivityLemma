export const meta = {
  name: "fidelity-guarded2",
  description: "Continue the guarded attack after the connection outage: finish stranded compiles, try the continuity counterexample (interior curvature plus exterior twist), one structural proof route, the S-3 raw constraint, and judge. Astra in every role.",
  phases: [
    { title: "Attack", detail: "Continuity refutation, exact-kernel refutation, structural proof, S-3 raw" },
    { title: "Verify", detail: "Independent recompile, statement match, axioms" },
    { title: "Judge", detail: "Closed or open" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. lean/.lake oleans from the 2026-10-21 fresh build are ready.",
  "Compile ONLY through AHP/round3/lean1.sh <file.lean>; it serialises Lean across workers and writes <file.lean>.log and <file.lean>.exit. Run it directly in your bash tool (not in a bb terminal: terminals were lost in the last outage). If your bash call times out, do not relaunch: poll for the .exit file. Never call lake env lean, lake build, REPRODUCE.sh or lake update directly. Keep numerical scripts under 2 GB.",
  "Earlier compiles in AHP/round4/guarded/{gap-r2,decay-r2,perturb-r1,refute-r2} were lost when the bb connection dropped; they have no .exit file and nothing is running. They are not verified. You may recompile them through lean1.sh if your route needs them.",
  "Write only under AHP/round5/<item>/. Do not edit lean/ (including lean/lakefile.toml and any lean/src/BalabanCompact*, lean/src/Compact* files, which belong to another thread), paper/, notes/, expected/, extras/, or earlier AHP rounds. Never run rm outside AHP/round5/<item>/. No git commit or push.",
  "Lean files cannot import AHP files. Copy needed definitions verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const CONTEXT = "Guarded item. Read in full first: AHP/round3/guarded/JUDGEMENT.md, AHP/round3/guarded/pin/PIN.md, AHP/round4/guarded/MINE.md, and NOTES.md (or the obstacle text below) of every route in AHP/round4/guarded/. Pinned goals: AHP/round3/guarded/pin/Statement.lean (GoalPos1/2 = GuardPencilT / P428Target8SG selAll selAll; GoalNeg1/2 their negations). Copy that file verbatim as the start of your Attempt.lean; never change a goal. Notation: A = Ginv_all (carrier), B = Ginv_in, D = Delta2_in (assembled correction), C = B - D, Theta = A - B. Failure of the guarded headline at an instance means: A is a unit but the corrected operator (A - D, equivalently K_C on range Theta) is not, with all class conditions, LambdaOK2, the cap and a positive-energy competitor. Facts established in round 4 (some compiled, some not yet verified): (1) PERTURB: on the flat-interior Uth exterior-twist path, localized B is constant and D = 0, A is a unit at theta = 0 and singular at some theta < pi, so by connectedness no class-uniform gap for A or K_B exists; (2) GAP r1 (compiled): a scalar model shows the guard plus small D does not force K_C invertible; pencil failure forces negative boundary energy; (3) DECAY r1 (compiled): ||K_C - K_B|| <= ||Theta|| ||D|| b c; DECAY r2 (uncompiled New.lean): K_B^-1 (K_C - K_B) y = Theta A^-1 D C^-1 y; (4) REFUTE r1 (compiled, AHP/round4/guarded/refute-r1/Attempt.lean:1599 cofinal_in_class_curved_competitor): cofinal in-class configurations with unbounded m and R, R before every cap, exact nontrivial holonomy on an interior plaquette, positive-energy competitor; dil_in_class_nonflat_competitor (:1423) allows an arbitrary exterior field V; (5) MINE: Total gives localized coercivity and correction bounds linear in 12*M*alpha0; nothing uniform for A.";

const tracks = [
  {
    key: "ivt",
    item: "guarded",
    pin: "AHP/round3/guarded/pin/Statement.lean",
    aim: "REFUTATION BY CONTINUITY. Combine fact (4) and fact (1): take refute-r1's cofinal curved in-class configuration (interior curvature, so D != 0) and put the Uth exterior twist on its exterior field V (dil_in_class_nonflat_competitor allows any exterior V). Along theta, the class conditions hold for every theta (the class does not see exterior bonds, see AHP/round3/s1-proper/r1-refute Uth_perCubeRegularTouch and AHP/round4/guarded/perturb-r1). Goal: a theta where A is positive definite (hence a unit) but A - D has a vector with negative quadratic form; then a continuous path from a point where A - D is positive definite reaches a non-unit of A - D while A stays positive definite (use the finite-dimensional continuous-path argument of D1IVT.lean:86 / D1Main.lean:141). Key inequality: on the near-null direction v of A near the crossing, <A v, v> tends to 0 while <D v, v> stays bounded below by a positive quantity depending on the curvature but not on theta. First check numerically, on the smallest admissible instance, the sign and size of <D v, v> on A's lowest mode as theta approaches the crossing; if it is negative, flip the interior curvature (its sign is a free parameter) or choose the competitor accordingly. The cap is given last and arbitrarily small, so <D v, v> may be tiny: that is fine as long as it is positive, because <A v, v> can be made smaller than any positive number. Then formalise for every m above any threshold and every R above any threshold, R before the cap, and close GoalNeg2 (or GoalNeg1).",
  },
  {
    key: "kernel",
    item: "guarded",
    pin: "AHP/round3/guarded/pin/Statement.lean",
    aim: "REFUTATION, EXACT MODEL. Lift the exact two-coordinate separations drafted in AHP/round4/guarded/gap-r2/Work.lean and AHP/round4/guarded/decay-r2/Model.lean (uncompiled; compile them first) to an actual lattice instance: identify which lattice modes play the two coordinates, and certify exact corrected singularity with an explicit nonzero kernel vector together with IsUnit A. Use refute-r1's cofinal family for the class obligations. If the continuity route (a parallel worker) is more natural for your construction, use it. Close GoalNeg2 (or GoalNeg1), or report the precise obstacle.",
  },
  {
    key: "structural",
    item: "guarded",
    pin: "AHP/round3/guarded/pin/Statement.lean",
    aim: "PROOF, STRUCTURAL. Uniform gaps are impossible (fact 1). The only remaining proof shape is a correlated estimate: the near-singular modes of A come from exterior twist, while D only sees level-zero bonds inside Omega_0 through the jet observation J. Using the identity K_B^-1(K_C - K_B) y = Theta A^-1 D C^-1 y (compile decay-r2/New.lean first), try to prove that J A^-1 Theta is class-uniformly bounded even when A is near-singular, because A's near-null space is invisible to J; then conclude GoalPos2 for small caps. Before investing in the proof, test the claim numerically on the smallest admissible instance with interior curvature plus exterior twist near the crossing: if ||J A^-1 Theta|| blows up, stop and report that as the obstacle (it supports the refutation).",
  },
  {
    key: "s3raw",
    item: "s3-raw",
    pin: "AHP/round3/s3-rest/pin/Statement.lean",
    aim: "S-3 RAW CONSTRAINT. Read AHP/round3/s3-rest/JUDGEMENT.md, pin/PIN.md and r1-prove/NOTES.md. GoalPos2 (normalised constraint) is proved at AHP/round3/s3-rest/r1-prove/Attempt.lean:1268. Prove GoalPos1 (raw constraint) from the same pin, ideally by an exact reduction to GoalPos2 (raw and normalised unit constraints differ by a scalar per level), handling singular-corridor totalisations explicitly. Or prove its negation. Copy the pin and the GoalPos2 proof verbatim as needed.",
  },
];

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["item", "route", "round", "file", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "evidence", "obstacle"],
  properties: {
    item: { type: "string" },
    route: { type: "string" },
    round: { type: "integer" },
    file: { type: "string" },
    exitCode: { type: "integer" },
    closedGoal: { type: "string" },
    mainDeclaration: { type: "string" },
    axiomLine: { type: "string" },
    evidence: { type: "string" },
    obstacle: { type: "string" },
  },
};

const verifySchema = {
  type: "object",
  additionalProperties: false,
  required: ["item", "file", "recompiledExit", "statementMatchesPin", "definitionsMatchPin", "axiomsStandard", "forbiddenTokens", "verdict", "reasons"],
  properties: {
    item: { type: "string" },
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    statementMatchesPin: { type: "boolean" },
    definitionsMatchPin: { type: "boolean" },
    axiomsStandard: { type: "boolean" },
    forbiddenTokens: { type: "array", items: { type: "string" } },
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

const results = await parallel(tracks.map((t) => async () => {
  const history = [];
  let closed = null;
  for (let round = 1; round <= 2 && !closed; round++) {
    const dir = "AHP/round5/" + t.item + "/" + t.key + "-r" + round + "/";
    const att = await retry("attack:" + t.key + ":r" + round, () => agent(
      RULES + "\n\n" + (t.item === "guarded" ? CONTEXT + "\n" : "") + t.aim +
        "\nWork in " + dir + ". Final file " + dir + "Attempt.lean starting with the verbatim pin " + t.pin + ", with #print axioms for the main declaration and every helper. Write " + dir + "NOTES.md. If you cannot close a goal, return closedGoal 'none', your furthest compiled partial result, and the concrete obstacle. Do not weaken any goal." +
        (history.length ? "\nYour earlier round:\n" + JSON.stringify(history) : ""),
      { label: "attack:" + t.key + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
    ));
    let ver = null;
    if (att && att.closedGoal !== "none" && att.exitCode === 0) {
      ver = await retry("verify:" + t.key + ":r" + round, () => agent(
        RULES + "\n\nVERIFY item " + t.item + ". Do not edit the attempt. Copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile that copy with AHP/round3/lean1.sh. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from " + t.pin + ", and the pin's contents appear unchanged in the attempt; (3) every #print axioms line lists only propext, Classical.choice, Quot.sound; (4) no forbidden token. closes-goal only if all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
        { label: "verify:" + t.key + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
      ));
      if (ver && ver.verdict === "closes-goal") closed = { attempt: att, verify: ver };
    }
    history.push({ round: round, attempt: att, verify: ver });
  }
  return { track: t.key, item: t.item, history: history, closed: closed };
}));

phase("Judge");
const judge = await retry("judge", () => agent(
  RULES + "\n\nJUDGE. Write AHP/round5/RESULTS.md in plain words. For the guarded item: status (closed-holds, closed-fails, or open), the verified declarations that settle it (file, name, axiom line), and each track's obstacle. If a refutation closed, say exactly what it shows: whether the failure happens at a point where every inverse in the printed construction exists, or only where some inverse is totalised. For S-3 raw constraint: status and evidence. Do not edit other files.\n" + JSON.stringify(results),
  {
    label: "judge",
    phase: "Judge",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "xhigh",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["guardedStatus", "s3RawStatus", "closedBy", "summary", "stillOpen"],
      properties: {
        guardedStatus: { enum: ["closed-holds", "closed-fails", "open"] },
        s3RawStatus: { enum: ["closed-holds", "closed-fails", "open"] },
        closedBy: { type: "array", items: { type: "string" } },
        summary: { type: "string" },
        stillOpen: { type: "string" },
      },
    },
  },
));

return { results: results, judge: judge };

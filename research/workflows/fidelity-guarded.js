export const meta = {
  name: "fidelity-guarded",
  description: "Dedicated attack on the guarded all-plaquette reading (GuardPencilT / P428Target8SG) by mining the Total proof for uniform estimates and trying several proof routes and one refutation in parallel; plus the S-3 raw-constraint goal. Astra in every role.",
  phases: [
    { title: "Mine", detail: "Extract every uniform lower bound and inverse estimate the Total proof establishes" },
    { title: "Attack", detail: "Three proof routes and one refutation, two rounds each" },
    { title: "Verify", detail: "Independent recompile, statement match, axioms" },
    { title: "Judge", detail: "Closed or open" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. A fresh REPRODUCE.sh passed on 2026-10-21; lean/.lake oleans are ready.",
  "This machine has 16 GB of RAM. Compile ONLY through AHP/round3/lean1.sh <file.lean>, which serialises Lean across all workers and writes <file.lean>.log and <file.lean>.exit. If the call returns before the .exit file exists, wait and poll for it; do not start a second compile of the same file. Never call lake env lean, lake build, REPRODUCE.sh or lake update directly. Keep numerical scripts under 2 GB.",
  "Write only under AHP/round4/<item>/. Do not edit lean/ (including lean/lakefile.toml and any lean/src/BalabanCompact*, lean/src/Compact* files, which belong to another thread), paper/, notes/, expected/, extras/, or other AHP paths. Never run rm outside AHP/round4/<item>/. Never delete AHP/. No git commit or push.",
  "Lean files cannot import AHP files. Copy needed definitions verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const GUARDED = "The open question (read AHP/round3/guarded/JUDGEMENT.md, AHP/round3/guarded/pin/PIN.md and AHP/round2/guarded/JUDGEMENT.md in full): P428Target8SG selAll selAll (D2Cons.lean:70), equivalently GuardPencilT (DrEquiv.lean:99), equivalently GShape CBoundaryResponse (AHP/round2/guarded/r2-prove/Attempt.lean:554, goalPos2_iff_boundary_response). With A = Ginv_all, B = Ginv_in, D = Delta2_in, C = B - D, Theta = A - B, W = range Theta: on the eventual class, does invertibility of K_B y = y + Theta B^-1 y force invertibility of K_C y = y + Theta C^-1 y? Compiled sufficient conditions exist: a zero-return criterion (B^-1(range Theta) inside jetInputZero), and an inverse-relative norm criterion ||K_B^-1 (K_C - K_B)|| < 1. Compiled necessary obstructions: guarded failure forces a non-flat background on the base domain and a nonzero boundary return. Round 3 found a complete in-class single-defect family at m = 1 with positive-energy competitors but no exact spectral separation. The pinned goals are in AHP/round3/guarded/pin/Statement.lean: copy that file verbatim as the start of your attempt and do not change any goal.";

const guardedRoutes = [
  {
    key: "gap",
    dir: "prove",
    aim: "PROOF ROUTE: uniform gap from Total. AdalyFormal.Total.p428Target8Total (TT_F.lean:29) and its proof chain (Mixed, Family, FamilyTorus, M2RightInv, RI6) prove coercivity with constants uniform in the class and the existence of every inverse. Use the mined estimates (MINE.md) to get a class-uniform lower bound on K_B (or on B, G^-1 restricted to the relevant subspace), and a class-uniform upper bound on ||D|| that goes to zero with the smallness cap (D is the second jet, quadratic in the background). Then apply the compiled norm criterion. Thresholds may be chosen as the pinned quantifier order allows: m first, then R, then the cap.",
  },
  {
    key: "decay",
    dir: "prove",
    aim: "PROOF ROUTE: locality. D acts on level-zero plaquettes inside Omega_0 and Theta on the boundary layer. Show the boundary return Theta C^-1 D B^-1 y is zero or small, using decay of B^-1 away from the boundary (Combes-Thomas style for a positive operator with a uniform gap) together with the collar R*M separating the boundary from where D is large, so the return vanishes or is bounded by a factor that is small once R is large. Then apply the zero-return or norm criterion.",
  },
  {
    key: "perturb",
    dir: "prove",
    aim: "PROOF ROUTE: continuity in the background. At flat backgrounds D = 0 so K_C = K_B. Guarded failure forces non-flatness (compiled). Show along the class that ||D|| <= c * alpha0 with c uniform, and that the guard on K_B can be strengthened to a uniform quantitative gap on the eventual class (possibly by first proving the guard implies a gap, using compactness of SU(2) per bond and finite dimension per torus, then uniformity from the Total constants). Conclude K_C invertible once the cap is small.",
  },
  {
    key: "refute",
    dir: "refute",
    aim: "REFUTATION. Build an exact in-class configuration where the full carrier guard holds and the corrected operator is singular, cofinally: for every m above any threshold and then every R above any threshold, with R chosen before every positive cap. Start from round 3's in-class single-defect family (AHP/round3/guarded/r*-refute/) and make it cofinal in m and R. The background must be non-flat on Omega_0. Certify singularity exactly (an explicit kernel vector), not by floating-point roots. If the mined uniform gap from MINE.md makes this impossible, prove that instead and report it as the obstacle.",
  },
];

const mineSchema = {
  type: "object",
  additionalProperties: false,
  required: ["file", "estimates"],
  properties: {
    file: { type: "string" },
    estimates: { type: "array", items: { type: "string" } },
  },
};

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

const judgeSchema = {
  type: "object",
  additionalProperties: false,
  required: ["item", "status", "closedBy", "summary", "stillOpen"],
  properties: {
    item: { type: "string" },
    status: { enum: ["closed-holds", "closed-fails", "partly-closed", "open"] },
    closedBy: { type: "array", items: { type: "string" } },
    summary: { type: "string" },
    stillOpen: { type: "string" },
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

function verifyStep(item, pinFile, att, label) {
  if (!att || att.closedGoal === "none" || att.exitCode !== 0) return Promise.resolve(null);
  return retry(label, () => agent(
    RULES + "\n\nVERIFY item " + item + ". Do not edit the attempt. Copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile that copy with AHP/round3/lean1.sh. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from " + pinFile + ", and the pin file's contents appear unchanged in the attempt; (3) every #print axioms line lists only propext, Classical.choice, Quot.sound; (4) no forbidden token. closes-goal only if all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
    { label: label, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
  ));
}

phase("Mine");
const mine = await retry("mine", () => agent(
  RULES + "\n\nMINE the proof of AdalyFormal.Total.p428Target8Total (lean/src/TT_F.lean:29) and the chain it uses (search with rg for Total, Mixed, FamilyTorus, M2RightInv, RI6, WellDefG, Ginv, IsUnit, coercive, gap, lower bound). List every compiled declaration that gives (a) a class-uniform lower bound or coercivity estimate for G^-1, Ginv, G1inv or a restriction of them; (b) existence of inverses on the class; (c) bounds on Delta2, the second jet, or curvature terms in terms of alpha0; (d) locality or support facts for the inverses or jets. For each: file:line, exact statement, the order in which its constants are chosen, and whether it applies to selAll or only to selIn. Write AHP/round4/guarded/MINE.md. Do not prove anything new.\n" + GUARDED,
  { label: "mine", phase: "Mine", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: mineSchema },
));

const PIN = "AHP/round3/guarded/pin/Statement.lean";

const guardedResults = await parallel(guardedRoutes.map((r) => async () => {
  const history = [];
  let closed = null;
  for (let round = 1; round <= 2 && !closed; round++) {
    const dir = "AHP/round4/guarded/" + r.key + "-r" + round + "/";
    const att = await retry("attack:guarded:" + r.key + ":r" + round, () => agent(
      RULES + "\n\nATTACK the guarded item, route " + r.key + ", round " + round + ".\n" + GUARDED + "\nMined estimates: AHP/round4/guarded/MINE.md.\n" + r.aim +
        "\nWork in " + dir + ". Final file " + dir + "Attempt.lean starting with the verbatim pin, with #print axioms for the main declaration and every helper. Write " + dir + "NOTES.md. If you cannot close a goal, return closedGoal 'none', your furthest compiled partial result, and the concrete obstacle. Do not weaken any goal." +
        (history.length ? "\nYour earlier round:\n" + JSON.stringify(history) : ""),
      { label: "attack:guarded:" + r.key + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
    ));
    const ver = await verifyStep("guarded", PIN, att, "verify:guarded:" + r.key + ":r" + round);
    if (ver && ver.verdict === "closes-goal") closed = { attempt: att, verify: ver };
    history.push({ round: round, attempt: att, verify: ver });
  }
  return { route: r.key, history: history, closed: closed };
}));

const S3PIN = "AHP/round3/s3-rest/pin/Statement.lean";
const s3 = await (async () => {
  const dir = "AHP/round4/s3-raw/";
  const att = await retry("attack:s3-raw", () => agent(
    RULES + "\n\nATTACK S-3 raw constraint. Read AHP/round3/s3-rest/JUDGEMENT.md, pin/PIN.md and r1-prove/NOTES.md. GoalPos2 (normalised constraint) is proved at AHP/round3/s3-rest/r1-prove/Attempt.lean:1268. GoalPos1 (raw constraint) in " + S3PIN + " is open. Prove GoalPos1, ideally by an exact reduction to GoalPos2 (the raw and normalised unit constraints are linked by a scalar per level; see the pin's linked raw/normalised representations), handling the singular-corridor totalisations explicitly. Or prove its negation. Work in " + dir + ". Final file " + dir + "Attempt.lean starting with the verbatim pin, copy the proof of GoalPos2 verbatim as needed. Write " + dir + "NOTES.md.",
    { label: "attack:s3-raw", phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
  ));
  const ver = await verifyStep("s3-raw", S3PIN, att, "verify:s3-raw");
  return { attempt: att, verify: ver };
})();

phase("Judge");
const judge = await retry("judge", () => agent(
  RULES + "\n\nJUDGE. Write AHP/round4/RESULTS.md in plain words. For the guarded item: status, which route closed what, the compiled declarations (file, name, axiom line), and what is still open; list each route's obstacle. For S-3 raw constraint: the same. Do not edit other files.\nMine:\n" + JSON.stringify(mine) + "\nGuarded routes:\n" + JSON.stringify(guardedResults) + "\nS-3 raw:\n" + JSON.stringify(s3),
  { label: "judge", phase: "Judge", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: judgeSchema },
));

return { mine: mine, guarded: guardedResults, s3raw: s3, judge: judge };

export const meta = {
  name: "guarded-allscales",
  description: "Prove CofinalTwistSeparation (round 8) for all scales, which closes GoalNeg2: the guarded all-plaquette reading is false. Two Opus 5.5 max workers on complementary routes, two rounds, Astra verifies.",
  phases: [
    { title: "Prove", detail: "Opus 5.5 max: analytic all-scales route and a perturbation/qualitative route" },
    { title: "Verify", detail: "Astra recompiles and checks against the pinned GoalNeg2" },
    { title: "Report", detail: "Plain summary" },
  ],
};

const COMMON = [
  "GOAL. Close the pinned GoalNeg2 in AHP/round3/guarded/pin/Statement.lean (the guarded all-plaquette reading P428Target8SG selAll selAll is false) with no extra hypotheses. Round 8 compiled the bridge AdalyFormal.Round8.Guarded.SignFree.goalNeg2_of_cofinalTwistSeparation (AHP/round8/guarded-idea/Attempt.lean:2856), so it suffices to prove CofinalTwistSeparation (:2846), or one of its sufficient forms there: CofinalSignChange (:2851, via SignChangeControl :2663) or PencilCertificates (:2811, with TwistPencil :2803). Note the premise only needs INFINITELY MANY dyadic scales q = 2^j and, for each, INFINITELY MANY even R >= 18: you may choose convenient sequences (for example R a multiple of something, or q in a sparse subsequence) if that makes the analysis easier.",
  "READ FIRST, IN FULL: AHP/round8/guarded-idea/IDEA.md (the mechanism, sections 1-6, especially 5 'What remains' and 6.4 vacuum data), AHP/round8/guarded-idea/Attempt.lean appendix (from the round-5 prefix end), AHP/round6/probe/PROBE.md, AHP/round6/RESULTS.md, AHP/round5/RESULTS.md, and the numerics scripts under AHP/round8/guarded-idea/numerics/ and AHP/round6/probe/ (they transcribe the actual operators with Lean line citations).",
  "KNOWN NUMERICS (round 8, mpmath 400-500 digits): separation at every tested instance, q in {1,2,4}, R in {18,20,24,30}, eps down to 1e-170, in both the pre-crossing (A PD) and post-crossing (A indefinite unit) regimes. The leading vacuum coefficient c1(2,R) = -0.0191639341944987 * rho_k^(8R) to 15 digits, c1(4,18) = -0.01796 * rho_k^(16R), with rho_k = (3+T-sqrt((3+T)^2-4))/2, T = 4(1-cos(pi/(4q))) style transverse wave number. The first charged crossing is in character (7,7) for q = 2 (wave numbers -pi/8), (0,0) for q = 1.",
  "WORKSPACE RULES. /home/sebastian/BalabanCoercivityLemma (Lean 4.31, Mathlib, oleans built). Write only under AHP/round9/<route>/. Do not edit lean/ (lakefile and lean/src/BalabanCompact*, Compact* belong to another thread), paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "COMPILING. 16 GB RAM shared with other workers. Compile ONLY with AHP/round3/lean1.sh <file.lean> (shared lock; writes .log and .exit). Run it directly in bash; on timeout, poll for .exit, never relaunch the same file. Never run lake build or REPRODUCE.sh. Lean files cannot import AHP files: start your Attempt.lean with AHP/round8/guarded-idea/Attempt.lean verbatim (it already contains the round-3 pin and the round-5 bridge) and append. Import only frozen lean/src modules. Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque stand-ins; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath available; keep jobs under 3 GB and use \"$BB_CLI\" heavy run -- for anything over a minute. Numerics are evidence only and never replace a proof step.",
  "DELIVERABLES under AHP/round9/<route>/: Attempt.lean (+ .log, .exit), NOTES.md (the argument in plain mathematics, what compiled, what is left), any scripts. If you cannot close GoalNeg2, compile the strongest reduction you can: a theorem 'X -> CofinalTwistSeparation' where X is strictly simpler (finitely many explicit inequalities per instance, or a single analytic lemma), and say exactly what X is. Be strict: never call a conditional result a proof.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const routes = [
  {
    key: "analytic",
    aim: "ROUTE: ANALYTIC, ALL SCALES. Follow IDEA.md section 5's natural route. (1) Vacuum nondegeneracy for every (q,R) in your chosen subsequence: at eps = 0 the twisted carrier has a simple first crossing in an explicit character sector, positive splitting to the partner crossing, and a nonzero first-order correction coefficient c1(q,R). Use the translation symmetry (round 6 closedform-r1 compiled twoSite_exact_symmetry) to reduce to one character sector; in that sector the flat-collar problem is a constant-coefficient tridiagonal (transfer-matrix) recurrence with explicit solutions in powers of rho_k, so the crossing equation, its kernel and c1 can be written in closed form; prove c1 != 0 from the closed form (its sign is irrelevant for separation: IDEA.md shows both signs separate). (2) Perturbation in eps: in finite dimensions, with the sector reduced to a fixed-size matrix analytic in (t, eps), the crossing of A and the crossing of A - D are simple zeros of determinants; a nonzero first-order shift with the partner gap bounded below gives separation for all small eps > 0 at fixed (q,R). Prove whatever form of (2) the bridge needs (SignChangeControl or PencilCertificates may be easier than exact separation). Exponentially small quantities are fine in exact arithmetic: you never need a numerical size, only nonvanishing.",
  },
  {
    key: "qualitative",
    aim: "ROUTE: QUALITATIVE / ANALYTICITY, AVOIDING EXPLICIT ASYMPTOTICS. Look for a proof that never computes c1(q,R). Ideas: (i) at fixed (q,R) the maps (t, eps) -> det A and det(A - D) are real-analytic (polynomial in cos t, sin t and in the background's entries); if they had the same zero set near the crossing for all small eps, an analytic identity would follow which you can refute by evaluating one derivative or one special point (for instance eps-derivative at the vacuum crossing, or a single exact rational instance), so separation follows for all small eps without asymptotics; (ii) the quantifiers let you pick infinitely many scales and radii: find a subsequence (e.g. q = 1 fixed is NOT allowed since the premise needs arbitrarily large j, but check whether a scaling/dilation identity compiled in lean/src for the dilTower family transports one instance's separation to all larger q or R); (iii) the identity theorem for polynomials: a nonzero polynomial in eps has finitely many zeros, so 'not identically zero' suffices for 'nonzero for all small eps'. Combine with whatever exact finite certificate you can produce in Lean (Mathlib's polynomial and determinant machinery; decide or norm_num on rational matrices where sizes allow). Prove CofinalTwistSeparation or a sufficient form.",
  },
];

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["route", "round", "file", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "remainingGap", "evidence"],
  properties: {
    route: { type: "string" },
    round: { type: "integer" },
    file: { type: "string" },
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

const results = await parallel(routes.map((r) => async () => {
  const history = [];
  let closed = null;
  for (let round = 1; round <= 2 && !closed; round++) {
    const dir = "AHP/round9/" + r.key + "-r" + round + "/";
    const att = await retry("prove:" + r.key + ":r" + round, () => agent(
      COMMON + "\n\n" + r.aim + "\n\nRound " + round + ". Work in " + dir + "." +
        (history.length ? "\nYour earlier round (continue from its files; do not redo compiled work):\n" + JSON.stringify(history) : ""),
      { label: "prove:" + r.key + ":r" + round, phase: "Prove", model: "claude-bridge/claude-opus-5-5", reasoningLevel: "max", schema: attemptSchema },
    ));
    let ver = null;
    if (att && att.closedGoal !== "none" && att.exitCode === 0) {
      ver = await retry("verify:" + r.key + ":r" + round, () => agent(
        "Workspace /home/sebastian/BalabanCoercivityLemma. Compile ONLY via AHP/round3/lean1.sh (poll .exit on timeout; never relaunch the same file; never lake build). Write only the files named below. VERIFY: copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile the copy. Check: (1) exit 0; (2) the main declaration's type is exactly GoalNeg2 (or GoalNeg1) from AHP/round3/guarded/pin/Statement.lean, with no extra hypotheses; (3) the pin's text appears unchanged in the attempt; (4) every #print axioms line lists only propext, Classical.choice, Quot.sound; (5) no sorry, admit, axiom declaration, native_decide, unsafe, implemented_by, extern or opaque. closes-goal only if all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ". As your last action, call bb_workflow_result once.\nAttempt report:\n" + JSON.stringify(att),
        { label: "verify:" + r.key + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
      ));
      if (ver && ver.verdict === "closes-goal") closed = { attempt: att, verify: ver };
    }
    history.push({ round: round, attempt: att, verify: ver });
  }
  return { route: r.key, history: history, closed: closed };
}));

phase("Report");
const report = await retry("report", () => agent(
  "Workspace /home/sebastian/BalabanCoercivityLemma. Write AHP/round9/RESULTS.md in plain words: whether the guarded reading is now refuted in Lean (only if a verified attempt proves pinned GoalNeg2 or GoalNeg1 with no extra hypotheses); per route, what compiled and the exact remaining premise; whether the counterexample's failure point has every inverse in the printed construction existing (the carrier A is a unit there; state which other inverses exist or are totalised). Do not edit other files. As your last action, call bb_workflow_result once.\n" + JSON.stringify(results),
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

return { results: results, report: report };

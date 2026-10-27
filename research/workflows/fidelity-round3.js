export const meta = {
  name: "fidelity-round3",
  description: "Round 3: close the rest of (3.156), the touching operators on the four-bond class with proper domains, and the guarded boundary-response question, by a compiled proof or a compiled counterexample. Astra in every role.",
  phases: [
    { title: "Pin", detail: "Fix the exact Lean statements that would close each item, and compile them" },
    { title: "Attack", detail: "One attempt tries to prove, one tries to refute, in parallel" },
    { title: "Verify", detail: "Independent recompile, statement match, axioms, faithfulness" },
    { title: "Judge", detail: "Closed or still open, per item" },
    { title: "Report", detail: "One results file" },
  ],
};

const ROUNDS = 3;

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. A fresh REPRODUCE.sh passed on this machine on 2026-10-21; lean/.lake oleans are ready. Read HANDOFF.md, paper/OPEN_ITEMS.md (sections B, K to N, R, S), AHP/fidelity/STAGE_B_RESULTS.md, AHP/round2/RESULTS.md, and the round-2 files named in your item before starting.",
  "This machine has 16 GB of RAM and about 8 GB free. Compile ONLY through AHP/round3/lean1.sh <file.lean>, which takes a shared lock so one Lean process runs at a time across all workers, and writes <file.lean>.log and <file.lean>.exit. Waiting for the lock is normal. Never call lake env lean, lake build, REPRODUCE.sh, or lake update directly. Keep each numerical script under 2 GB.",
  "Write only under AHP/round3/<item>/. Do not edit lean/ (including lean/lakefile.toml and any lean/src/BalabanCompact*, lean/src/Compact* files, which belong to another thread), paper/, notes/, expected/, extras/, or any other AHP path. Never run rm outside AHP/round3/<item>/. No git commit or push.",
  "Lean files cannot import other AHP files. Copy any definition you need into your file verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins for real definitions. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "Numerical scripts (python3, numpy, scipy) are evidence only. Run long ones through \"$BB_CLI\" heavy run --. Cite the Lean file and line for every operator a script models.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const items = [
  {
    id: "s3-rest",
    title: "S-3 rest: the mass, J and bondEnergy summands of (3.156)",
    brief: "Round 2 proved the first summand: AHP/round2/s3-normalisation/r1-prove/Attempt.lean (namespace AdalyFormal.Round2.S3Pin; goalPos1_proved, goalPos2_proved, firstTerm_eq_printed) shows the frozen firstTerm (ZXG3A.lean:50) equals the first term assembled from printed objects with constant 1, under the inverse guards, for both H/C conventions of p.421. Read its JUDGEMENT.md 'What remains open' item 1 and its PIN.md. Still open: the other summands of the frozen form genForm (ZXG3A.lean, around line 54) and of the frozen InstIneq (ZT5A.lean:56): the mass subtraction a<B,B>, the nonlinear J term, and the left side gamma0 * bondEnergy (RegularUPerturbation.lean:355). Read (3.156), (3.157) and the definitions they use on CMP99b pp.421-428 in sources/corpus/pages and the renders already saved under AHP/round2/s3-normalisation/pin/renders/. Reuse the round-2 dictionary verbatim (copy the definitions you need; you cannot import AHP files). Pin: (a) for each remaining summand a printed counterpart built only from printed objects, with every scale convention cited to a page; (b) the whole printed inequality PrintedInstIneq. Positive goal: the frozen InstIneq is equivalent to PrintedInstIneq with gamma0 rescaled by an explicit positive constant c(ell,k) (or unchanged), at every depth, under the same guards. Negative goal: an admissible configuration at depth k >= 2 and test fields where some summand's ratio to its printed counterpart differs from the others, so no single rescaling of gamma0 and a makes the two inequalities equivalent. If the print is ambiguous for a summand, pin each defensible reading and say which one the pages support.",
  },
  {
    id: "s1-proper",
    title: "S-1 on proper domains: corner-touching operators on the four-bond class",
    brief: "Round 2 showed: corner coverage collapses Omega_0 to empty or the whole torus (AHP/round2/s1-touching/, AHP/round2/s2-nonvacuity/r1-refute goalNeg2_proved), so the round-2 S-1 closure says nothing about proper domains. The four-bond touching class ClassCoupledFour has proper nonempty domains with nonzero test fields (AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean, goalPos1_proved, properFourAt_two) and implies the frozen class (AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean). Pin P428TouchFour: same quantifiers and constants order as P428Target8 (ZT5A.lean:291), class hypothesis ClassCoupledFour (copy verbatim from the round-2 s2 pin), operators Delta and J on plaqCorner Omega_0 (Balaban CMP 102 p.277: plaquettes with at least one corner in the domain), i.e. D1Lit.InstIneqS with the corner selector for both Delta and J, as in the round-2 s1 pin (copy verbatim). List every departure from the print. Positive goal: P428TouchFour. Negative goal: not P428TouchFour, by an explicit in-class configuration that defeats every candidate threshold (structure: not_P428Target8Literal, D1Final.lean:169, and the cofinal slab family of D1Final.lean:139-168). Known facts to use: the touching Delta is -4 at theta = pi on slabs (numerics in AHP/fidelity/s1-touching/), but the class bounds phases by about a0/(sqrt(2) ell^j); a raw-Delta counterexample needed phases up to pi/2; none was found at the cap pi/4. The refuter should look where the corner operators read bonds that ClassCoupledFour constrains weakly: plaquettes with exactly one corner in Omega_0, whose far bonds have neither endpoint in Omega_0 and so are not bounded by the four-bond regularity. The prover should try to reduce to the frozen theorem: show the extra corner plaquettes contribute a nonnegative term, or are dominated, on the four-bond class.",
  },
  {
    id: "guarded",
    title: "Guarded all-plaquette reading: the boundary-response question",
    brief: "Round 2 (AHP/round2/guarded/, read JUDGEMENT.md in full) reduced P428Target8SG selAll selAll (D2Cons.lean:70) and GuardPencilT (DrEquiv.lean:99) to GShape CBoundaryResponse: with A = Ginv_all, B = Ginv_in, D = Delta2_in, C = B - D, Theta = A - B, on W = range Theta, does invertibility of K_B y = y + Theta B^-1 y force invertibility of K_C y = y + Theta C^-1 y, throughout the eventual class? The compiled equivalence is AdalyFormal.Round2.Guarded.R2Prove.goalPos2_iff_boundary_response (AHP/round2/guarded/r2-prove/Attempt.lean:554). Also compiled: a sufficient zero-return criterion (pencil_isUnit_of_no_boundary_return), a necessary nonzero-return obstruction (guarded_failure_forces_boundary_return), a norm criterion (pencil_isUnit_of_feedback_norm_lt_one), and guarded failure forces a non-flat background on the base domain (guarded_failure_forces_nonflat). Pin the goals as round 2 did (reuse its pin verbatim; GoalPos = the headline, GoalNeg = its negation). Positive direction: prove the corrected boundary response is invertible on the eventual class, e.g. by a uniform inverse-relative bound on Theta C^-1 D B^-1 from the class smallness alpha0 and the locality of D (D lives on level-zero plaquettes inside Omega_0, Theta on the boundary layer), or by showing the return vanishes. Negative direction: an exact in-class configuration, with TorusOK, Admissible, coverage and regularity, LambdaOK2, capped smallness and a positive-energy competitor, where the guard holds and the corrected operator is singular, cofinally in m and then R with R chosen before every cap. Round 2 showed the small-torus candidate is outside the class; any candidate must be non-flat on the base domain.",
  },
];

const pinSchema = {
  type: "object",
  additionalProperties: false,
  required: ["item", "statementFile", "exitCode", "positiveGoals", "negativeGoals", "departuresFromPrint", "notes"],
  properties: {
    item: { type: "string" },
    statementFile: { type: "string" },
    exitCode: { type: "integer" },
    positiveGoals: { type: "array", items: { type: "string" } },
    negativeGoals: { type: "array", items: { type: "string" } },
    departuresFromPrint: { type: "array", items: { type: "string" } },
    notes: { type: "string" },
  },
};

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["item", "direction", "round", "file", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "evidence", "obstacle"],
  properties: {
    item: { type: "string" },
    direction: { enum: ["prove", "refute"] },
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
  required: ["item", "file", "recompiledExit", "statementMatchesPin", "definitionsMatchPin", "axiomsStandard", "forbiddenTokens", "faithfulnessConcerns", "verdict", "reasons"],
  properties: {
    item: { type: "string" },
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    statementMatchesPin: { type: "boolean" },
    definitionsMatchPin: { type: "boolean" },
    axiomsStandard: { type: "boolean" },
    forbiddenTokens: { type: "array", items: { type: "string" } },
    faithfulnessConcerns: { type: "array", items: { type: "string" } },
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
    status: { enum: ["closed-holds", "closed-fails", "closed-reduced", "partly-closed", "open"] },
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

function attemptPrompt(it, pin, direction, round, history) {
  const dir = "AHP/round3/" + it.id + "/r" + round + "-" + direction + "/";
  const aim = direction === "prove"
    ? "Prove one of the POSITIVE goals exactly as pinned. Start from the frozen proof of the nearest existing theorem and reuse it; look for a reduction to an already proved statement before building new analysis."
    : "Prove one of the NEGATIVE goals exactly as pinned, by an explicit counterexample. Use numerics first to find a candidate, then formalise it.";
  return RULES +
    "\n\nATTACK item " + it.id + " (" + it.title + "), direction " + direction + ", round " + round + ".\n" + it.brief +
    "\nThe pinned statements are in " + (pin ? pin.statementFile : "AHP/round3/" + it.id + "/pin/Statement.lean") + " and AHP/round3/" + it.id + "/pin/PIN.md. Copy the pinned definitions and goal statements verbatim into your file; do not change them." +
    "\n" + aim +
    "\nWork in " + dir + ". Final file: " + dir + "Attempt.lean, with #print axioms for the main declaration and every helper it uses. Write " + dir + "NOTES.md with what you tried and why it stopped." +
    "\nIf you cannot close a goal, still return: closedGoal 'none', the furthest compiled partial result as mainDeclaration, and the concrete obstacle. Do not weaken a goal to make it compile." +
    (history.length ? "\nEarlier rounds on this item:\n" + JSON.stringify(history) : "");
}

const results = await pipeline(
  items,
  (it) => retry("pin:" + it.id, () => agent(
    RULES + "\n\nPIN item " + it.id + " (" + it.title + ").\n" + it.brief +
      "\nWrite AHP/round3/" + it.id + "/pin/Statement.lean containing every needed definition and each goal as a `def GoalPosN : Prop := ...` or `def GoalNegN : Prop := ...`, plus `#check` lines, and compile it. Each negative goal must be the negation of the corresponding positive goal or a statement that implies that negation. Write AHP/round3/" + it.id + "/pin/PIN.md listing the goals in plain words and every departure from Balaban's print. The goals must be the real open question, not a comparison that is already proved.",
    { label: "pin:" + it.id, phase: "Pin", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: pinSchema },
  )),
  async (pin, it) => {
    const history = [];
    let closed = null;
    for (let round = 1; round <= ROUNDS && !closed; round++) {
      const pair = await parallel(["prove", "refute"].map((direction) => () =>
        retry("attack:" + it.id + ":" + direction + ":r" + round, () => agent(
          attemptPrompt(it, pin, direction, round, history),
          { label: "attack:" + it.id + ":" + direction + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
        )).then(async (att) => {
          if (!att || att.closedGoal === "none" || att.exitCode !== 0) return { attempt: att, verify: null };
          const ver = await retry("verify:" + it.id + ":" + direction + ":r" + round, () => agent(
            RULES + "\n\nVERIFY item " + it.id + ". Do not edit the attempt. Copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile that copy with AHP/round3/lean1.sh; its .log and .exit are your independent evidence. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from AHP/round3/" + it.id + "/pin/Statement.lean, and every copied definition is character-identical to the pin after whitespace normalisation; (3) every #print axioms line lists only propext, Classical.choice, Quot.sound; (4) no forbidden token; (5) faithfulness: read the pinned PIN.md and the printed pages it cites, and list any way the pinned goal fails to say what the item asks. closes-goal only if (1)-(4) all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
            { label: "verify:" + it.id + ":" + direction + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
          ));
          return { attempt: att, verify: ver };
        }),
      ));
      for (const r of pair) {
        if (r && r.verify && r.verify.verdict === "closes-goal") closed = r;
      }
      history.push({ round: round, results: pair });
      log(it.id + " round " + round + (closed ? " closed a goal" : " closed nothing"));
    }
    const judge = await retry("judge:" + it.id, () => agent(
      RULES + "\n\nJUDGE item " + it.id + " (" + it.title + "). Read the pin, every attempt's NOTES.md and VERIFY.md under AHP/round3/" + it.id + "/. Status: closed-holds or closed-fails only if a verified attempt closes a goal that settles the item as pinned; closed-reduced if the item is settled by a compiled equivalence or reduction; partly-closed if some but not all pinned goals were closed; open otherwise. Say in plain words what is now proved and what is still open. Write AHP/round3/" + it.id + "/JUDGEMENT.md.\nPin:\n" + JSON.stringify(pin) + "\nRounds:\n" + JSON.stringify(history),
      { label: "judge:" + it.id, phase: "Judge", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: judgeSchema },
    ));
    return { item: it.id, pin: pin, rounds: history, judge: judge };
  },
);

phase("Report");
const report = await retry("report", () => agent(
  RULES + "\n\nWrite AHP/round3/RESULTS.md in plain words: one section per item with its status, the compiled declarations that settle it (file, name, axiom line), what the pinned goal says compared with Balaban's print, and what is still open. Then one short table. Do not edit any other file.\n" + JSON.stringify(results),
  {
    label: "report",
    phase: "Report",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "high",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["file", "closed", "open"],
      properties: {
        file: { type: "string" },
        closed: { type: "array", items: { type: "string" } },
        open: { type: "array", items: { type: "string" } },
      },
    },
  },
));

return { results: results, report: report };

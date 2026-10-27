export const meta = {
  name: "fidelity-round2",
  description: "Round 2: try to close S-1, S-2 non-vacuity, S-3 and the guarded reading by a compiled proof or a compiled counterexample. Astra in every role.",
  phases: [
    { title: "Pin", detail: "Fix the exact Lean statements that would close each item, and compile them" },
    { title: "Attack", detail: "One attempt tries to prove, one tries to refute, in parallel" },
    { title: "Verify", detail: "Independent recompile, statement match, axioms, faithfulness" },
    { title: "Judge", detail: "Closed or still open, per item" },
    { title: "Report", detail: "One results file" },
  ],
};

const ROUNDS = 2;

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. A fresh REPRODUCE.sh passed on this machine on 2026-10-21; lean/.lake oleans are ready. Read HANDOFF.md, paper/OPEN_ITEMS.md (sections B, K to N, R, S), AHP/fidelity/STAGE_B_RESULTS.md, and the files of your item under AHP/fidelity/<item>/ before starting.",
  "Compile one file at a time with: export PATH=$HOME/.elan/bin:$PATH; cd /home/sebastian/BalabanCoercivityLemma/lean; \"$BB_CLI\" heavy run -- lake env lean <path-to-file> > <same path>.log 2>&1; echo $? > <same path>.exit. Never run lake build, REPRODUCE.sh, or lake update.",
  "Write only under AHP/round2/<item>/. Do not edit lean/ (including lean/lakefile.toml and lean/src/BalabanCompact or lean/src/CompactDictionary, which belong to another thread), paper/, notes/, expected/, extras/, or any other AHP path. Never run rm outside AHP/round2/<item>/. No git commit or push.",
  "Lean files cannot import other AHP files. Copy any definition you need into your file verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins for real definitions. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "Numerical scripts (python3, numpy, scipy) are evidence only. Keep each under 4 GB and run long ones through \"$BB_CLI\" heavy run --. Cite the Lean file and line for every operator a script models.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const items = [
  {
    id: "s2-nonvacuity",
    title: "S-2: does the four-bond touching class contain a proper domain?",
    brief: "Stage B compiled AdalyFormal.AHP.FidelS2Inclusion (AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean): ClassCoupledCorner -> ClassCoupledFour -> ClassCoupled and P428Target8 -> P428Target8Four -> P428Target8Corner. Open: whether ClassCoupledFour (and ClassCoupledCorner) is inhabited at a headline-regime admissible tower with a proper nonempty Omega_0. Numerics in AHP/fidelity/s2-inclusion/ATTACK.md suggest CoversPlaqCorner forces Omega_0 empty or the whole torus. Positive goal: an explicit witness, in the style of Fidelity.S1.shell_slab_nonvacuous (AHP/fidelity/s1-touching/lean/ShellComparison.lean) and D1Final.lean:139-168: TorusOK, Admissible, LambdaOK2, Omega_0 nonempty and not univ, a positive alpha0 under the smallness cap, ClassCoupledFour holds (frozen factor 12), and a nonzero admissible test field. Negative goal: under the headline-regime hypotheses, ClassCoupledFour (respectively ClassCoupledCorner) forces Omega_0 = empty or Omega_0 = univ. Pin both for the four-bond class and, separately, the corner class; closing either class in either direction counts as progress, closing the four-bond class closes the item.",
  },
  {
    id: "s1-touching",
    title: "S-1: Balaban's touching convention throughout",
    brief: "CMP 102 p.277: a domain's bonds are those with at least one endpoint in it; its plaquettes are those with at least one corner in it. Frozen: CubeBond (ZStatementP428.lean:145, both endpoints), plaqIn (ZR2Ops2.lean:74), CurlReads (ZR2A.lean:35), ClassCoupled (ZR6A.lean:124), InstIneq (ZT5A.lean:56), P428Target8 (ZT5A.lean:291). Known: the touching operators with the frozen class are false (not_P428Target8Literal, D1Final.lean:169). Stage B: Fidelity.S1 shell class (stronger than the print) is non-vacuous and implies the frozen class, but its coercivity is undecided. Prior numerics: the touching Delta is -4 at theta = pi on every slab; a new raw-Delta counterexample needs phases up to pi/2; none found at the cap pi/4 that small alpha0 allows. Pin ONE faithful consistent statement P428TouchConsistent: same quantifier order as P428Target8, touching class (TouchBond in the per-cube regularity and curl guards; coverage stated with touching bonds), and operators Delta and J on plaqCorner Omega_0 (D1Lit selectors, InstIneqS). Record every place the pinned statement departs from the print and why. If the faithful class collapses to Omega_0 empty or univ (see the s2 item), say so and pin as the reduced goal the equivalence of P428TouchConsistent with the frozen statement on those towers. Positive goal: P428TouchConsistent (or the shell statement P428Target8Shell from AHP/fidelity/s1-touching/SPEC.md as a weaker fallback, clearly labelled as stronger hypotheses than the print). Negative goal: not P428TouchConsistent, by an explicit in-class configuration at admissible headline parameters for every candidate threshold (follow the structure of not_P428Target8Literal, D1Final.lean). The refuter should search small-phase configurations allowed by the touching class: the class bound phi <= a0/(sqrt(2) ell^j) means candidate counterexamples must live where the class forces phases small, which is where the earlier numerics found nonnegativity; also try configurations whose large phases sit on bonds the touching class does not see.",
  },
  {
    id: "guarded",
    title: "Guarded all-plaquette reading P428Target8SG",
    brief: "P428Target8SG (D2Cons.lean:70) is equivalent to GuardResidualT (GdR5a.lean:54, :114) and reduced to GuardPencilT (DrEquiv.lean:99). full_guard_literal is proved. Stage B (AHP/fidelity/guarded/lean/UthCross.lean, namespace AdalyFormal.FidelityGuarded) proved: Ginv_lit is PSD at theta 0; on the slab family an in-class Uth has non-unit Ginv for some theta < pi; at such points G1invS = Ginv and the guard fails, so that crossing is not a counterexample. GdFam.lean:30 identifies G1inv with Ginv on the whole twist path. Missing step (AHP/attempts/sg-guarded/ and AHP/fidelity/guarded/): IsUnit(Ginv_lit(0)+Shift(t)) -> IsUnit(Ginv_lit(0)+Shift(t)-D) along exterior-only paths. Positive goal: GuardPencilT, then P428Target8SG selAll selAll through the existing equivalences. Negative goal: not P428Target8SG selAll selAll, i.e. an in-class configuration at headline parameters where the guarded quantities are units and the inequality fails, or the second operator is singular while the guard holds. The refuter should look off the flat twist path: non-flat interior links, two-parameter families, and points where Delta2 is nonzero (it vanishes on selIn at the crossing).",
  },
  {
    id: "s3-normalisation",
    title: "S-3: eta and tau-star in the first term of (3.156)",
    brief: "Frozen firstTerm (ZXG3A.lean:50) is eta * <tau* B, (Q G1 Q*)^-1 tau* B>, eta = ell^-k; print (3.156) shows neither eta nor tau*. G1in: ZXR2Wire2.lean:82; C2fullOf: ZXR2Sector.lean:109 with level weight (ell^j)^-1. Stage B proved only raw_level_zero, linear_level_zero, plainH_eq_uniformBody_at_depth_one (AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean). Read sources/corpus/pages CMP99b pp.393-396, 421-428 and the renders for (3.24), (3.119), (3.122), (3.126)-(3.129), (3.136), (3.156), (3.157). Pin in Lean a printed first term PrintedFirstTerm built only from printed objects, with every scale convention cited to a page and line, and the dictionary between printed and Lean objects (unit lattice vs fine lattice, tau*, eta powers, level weights). Positive goal: firstTerm B = c(ell,k) * PrintedFirstTerm B for all admissible B at every depth, with c an explicit positive constant (so the inequality is the same up to rescaling gamma0), or exact equality. Negative goal: an admissible configuration at depth k >= 2 and two test fields B1, B2 with firstTerm B1 / PrintedFirstTerm B1 different from firstTerm B2 / PrintedFirstTerm B2, so no constant rescaling matches. If several readings of the print are defensible, pin each as a separate goal and say which one the pages support; closing the supported reading closes the item.",
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
  const dir = "AHP/round2/" + it.id + "/r" + round + "-" + direction + "/";
  const aim = direction === "prove"
    ? "Prove one of the POSITIVE goals exactly as pinned. Start from the frozen proof of the nearest existing theorem and reuse it; look for a reduction to an already proved statement before building new analysis."
    : "Prove one of the NEGATIVE goals exactly as pinned, by an explicit counterexample. Use numerics first to find a candidate, then formalise it.";
  return RULES +
    "\n\nATTACK item " + it.id + " (" + it.title + "), direction " + direction + ", round " + round + ".\n" + it.brief +
    "\nThe pinned statements are in " + (pin ? pin.statementFile : "AHP/round2/" + it.id + "/pin/Statement.lean") + " and AHP/round2/" + it.id + "/pin/PIN.md. Copy the pinned definitions and goal statements verbatim into your file; do not change them." +
    "\n" + aim +
    "\nWork in " + dir + ". Final file: " + dir + "Attempt.lean, with #print axioms for the main declaration and every helper it uses. Write " + dir + "NOTES.md with what you tried and why it stopped." +
    "\nIf you cannot close a goal, still return: closedGoal 'none', the furthest compiled partial result as mainDeclaration, and the concrete obstacle. Do not weaken a goal to make it compile." +
    (history.length ? "\nEarlier rounds on this item:\n" + JSON.stringify(history) : "");
}

const results = await pipeline(
  items,
  (it) => retry("pin:" + it.id, () => agent(
    RULES + "\n\nPIN item " + it.id + " (" + it.title + ").\n" + it.brief +
      "\nWrite AHP/round2/" + it.id + "/pin/Statement.lean containing every needed definition and each goal as a `def GoalPosN : Prop := ...` or `def GoalNegN : Prop := ...`, plus `#check` lines, and compile it. Each negative goal must be the negation of the corresponding positive goal or a statement that implies that negation. Write AHP/round2/" + it.id + "/pin/PIN.md listing the goals in plain words and every departure from Balaban's print. The goals must be the real open question, not a comparison that is already proved.",
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
            RULES + "\n\nVERIFY item " + it.id + ". Do not edit the attempt. Recompile " + att.file + " yourself into " + att.file.replace(/\.lean$/, ".verify.log") + " and record the exit code. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from AHP/round2/" + it.id + "/pin/Statement.lean, and every copied definition is character-identical to the pin after whitespace normalisation; (3) every #print axioms line lists only propext, Classical.choice, Quot.sound; (4) no forbidden token; (5) faithfulness: read the pinned PIN.md and the printed pages it cites, and list any way the pinned goal fails to say what the item asks. closes-goal only if (1)-(4) all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
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
      RULES + "\n\nJUDGE item " + it.id + " (" + it.title + "). Read the pin, every attempt's NOTES.md and VERIFY.md under AHP/round2/" + it.id + "/. Status: closed-holds or closed-fails only if a verified attempt closes a goal that settles the item as pinned; closed-reduced if the item is settled by a compiled equivalence or reduction; partly-closed if some but not all pinned goals were closed; open otherwise. Say in plain words what is now proved and what is still open. Write AHP/round2/" + it.id + "/JUDGEMENT.md.\nPin:\n" + JSON.stringify(pin) + "\nRounds:\n" + JSON.stringify(history),
      { label: "judge:" + it.id, phase: "Judge", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: judgeSchema },
    ));
    return { item: it.id, pin: pin, rounds: history, judge: judge };
  },
);

phase("Report");
const report = await retry("report", () => agent(
  RULES + "\n\nWrite AHP/round2/RESULTS.md in plain words: one section per item with its status, the compiled declarations that settle it (file, name, axiom line), what the pinned goal says compared with Balaban's print, and what is still open. Then one short table. Do not edit any other file.\n" + JSON.stringify(results),
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

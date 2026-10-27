export const meta = {
  name: "odd-ell-integrate",
  description: "Rerun the decisive counterexample and non-vacuity results at every blocking factor (odd ell included), try the odd-ell sites-only cell, then integrate every accepted AHP result into the Lean tree on branch ahp-integration and rebuild. Astra in every role.",
  phases: [
    { title: "Pin", detail: "Fix the every-ell (odd included) statements in Lean" },
    { title: "Attack", detail: "Prove each pinned statement, two rounds" },
    { title: "Verify", detail: "Independent recompile against the pin" },
    { title: "Integrate", detail: "Add accepted results to the Lean tree on branch ahp-integration, update tables, rebuild" },
    { title: "Audit", detail: "Independent check of the integration branch" },
  ],
};

const MAIN = "/home/sebastian/BalabanCoercivityLemma";
const WT = "/home/sebastian/BalabanCoercivityLemma-integrate";

const RULES = [
  "Main checkout: " + MAIN + " (lean/.lake oleans ready). Read HANDOFF.md, paper/OPEN_ITEMS.md sections B, M, R, S, AHP/fidelity/STAGE_B_RESULTS.md, AHP/round2/RESULTS.md, AHP/round3/RESULTS.md, AHP/round5/RESULTS.md and AHP/round6/RESULTS.md before starting.",
  "This machine has 16 GB of RAM. In the main checkout compile ONLY through AHP/round3/lean1.sh <file.lean>, run directly in your bash tool (not a bb terminal). It serialises Lean across workers and writes <file.lean>.log and <file.lean>.exit. If your bash call times out, do not relaunch: poll for the .exit file. Never call lake env lean, lake build, REPRODUCE.sh or lake update in the main checkout.",
  "Python3 with numpy, scipy and mpmath is available. Keep numerical jobs under 4 GB; run anything over a minute through \"$BB_CLI\" heavy run --. Numerics are evidence only.",
  "In the main checkout write only under AHP/round7/<track>/. Do not edit lean/ (lean/lakefile.toml and lean/src/BalabanCompact*, lean/src/Compact* belong to another thread), paper/, notes/, expected/, extras/, or earlier AHP rounds. Never run rm outside your own directory. No git commit or push in the main checkout.",
  "Lean files cannot import AHP files. Copy needed definitions and proofs verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const tracks = [
  {
    key: "s1-odd",
    title: "Touching-convention counterexample at every blocking factor",
    brief: "AHP/round3/s1-proper/r1-refute/Attempt.lean:354 (Round3.S1Proper.goalNeg1_proved) refutes P428TouchFour (pin AHP/round3/s1-proper/pin/Statement.lean) using ell = 2 only. Balaban's later papers use odd L > 11 (CMP109 p.251). Pin and prove the slice statement for EVERY ell >= 2, in the style of not_literal_every_ell (lean/src/D1PGen.lean:24): for every ell >= 2 and every admissible a (state the range you can handle, ideally every a > 0; at minimum 0 < a < 4 as in D1PGen), the ell-slice of P428TouchFour fails, i.e. there is no m0, then R0, then a0, gamma0 making it hold at that ell. Reuse the general-ell literal family behind D1PGen.lean (read its imports for the general-ell slab, crossing and competitor), and the corner/all-carrier identity, touching-regularity and four-bond coverage lemmas of the round-3 refutation. Copy the round-3 pin verbatim and add the slice definition and goal after it.",
  },
  {
    key: "s2-odd",
    title: "Four-bond touching class has proper domains at every blocking factor",
    brief: "AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean:293 (AdalyFormal.AHP.Round2.S2Nonvacuity.goalPos1_proved) shows the four-bond touching class ClassCoupledFour has proper nonempty admissible domains with nonzero admissible test fields, cofinally in m and R, but only at ell = k = 2 (properFourAt_two). Pin and prove the same witness for every ell >= 2 (odd included): for every ell >= 2, cofinally in m and then R, with the frozen factor 12, every positive cap, TorusOK, Admissible, LambdaOK2, Omega_0 nonempty and not univ, a positive capped alpha0, ClassCoupledFour, and a nonzero admissible test field. Look for general-ell slab witnesses already in lean/src (the general-ell literal family used by D1PGen.lean, and the factor-12 non-vacuity lanes: rg for nonvacuous, NVC, SlabNv). Copy the round-2 pin verbatim and add the every-ell goal after it.",
  },
  {
    key: "s4-odd-sites",
    title: "Sites-only coverage at odd blocking factor (open item S-4)",
    brief: "OPEN_ITEMS S-4 and section M: the sites-only body FamilyTorusSitesConstAt (lean/src/CaT2d.lean:121; site coverage and per-cube regularity kept, plaquette coverage dropped) is false for ell = 2 and for even ell >= 4 with ell | 2(c-1) and 9 ell <= 2(c-1) (lean/src/SoA1.lean, SoA2.lean, SoM3.lean), and undecided for every odd ell. Round 1 of the AHP work (AHP/attempts/s4-odd-sites/, notes, PROSECUTION.md, SOL_VERDICT.md) showed the even-ell constant-step cancellation route cannot work at odd ell. Pin the odd-ell cell as a Lean statement (for a fixed odd ell >= 3, or every odd ell >= 3, and c >= 10, a > 0: FamilyTorusSitesConstAt or its negation, matching the shapes of the even-ell theorems) and attack it in both directions: a refutation by a different staggered or two-step profile at odd ell, or a proof. Best effort: if neither closes, return the obstacle and the furthest compiled partial result.",
  },
];

const pinSchema = {
  type: "object",
  additionalProperties: false,
  required: ["track", "statementFile", "exitCode", "goals", "notes"],
  properties: {
    track: { type: "string" },
    statementFile: { type: "string" },
    exitCode: { type: "integer" },
    goals: { type: "array", items: { type: "string" } },
    notes: { type: "string" },
  },
};

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["track", "round", "file", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "evidence", "obstacle"],
  properties: {
    track: { type: "string" },
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
  required: ["file", "recompiledExit", "statementMatchesPin", "pinUnchanged", "axiomsStandard", "forbiddenTokens", "verdict", "reasons"],
  properties: {
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    statementMatchesPin: { type: "boolean" },
    pinUnchanged: { type: "boolean" },
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

const oddResults = await pipeline(
  tracks,
  (t) => retry("pin:" + t.key, () => agent(
    RULES + "\n\nPIN track " + t.key + " (" + t.title + ").\n" + t.brief +
      "\nWrite AHP/round7/" + t.key + "/pin/Statement.lean with every needed definition and each goal as `def GoalN : Prop := ...`, plus #check lines, and compile it with lean1.sh. Write AHP/round7/" + t.key + "/pin/PIN.md: the goals in plain words, how they strengthen the existing ell = 2 result, and every departure from Balaban's print. The goal must be the real every-ell (or odd-ell) statement, not a restatement of the ell = 2 result.",
    { label: "pin:" + t.key, phase: "Pin", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: pinSchema },
  )),
  async (pin, t) => {
    const history = [];
    let closed = null;
    const pinFile = pin ? pin.statementFile : "AHP/round7/" + t.key + "/pin/Statement.lean";
    for (let round = 1; round <= 2 && !closed; round++) {
      const dir = "AHP/round7/" + t.key + "/r" + round + "/";
      const att = await retry("attack:" + t.key + ":r" + round, () => agent(
        RULES + "\n\nATTACK track " + t.key + " (" + t.title + "), round " + round + ".\n" + t.brief +
          "\nPinned goals: " + pinFile + " and PIN.md beside it. Copy the pin verbatim as the start of " + dir + "Attempt.lean; never change a goal. Add #print axioms for the main declaration and every helper. Write " + dir + "NOTES.md. If you cannot close a goal, return closedGoal 'none', your furthest compiled partial result, and the concrete obstacle." +
          (history.length ? "\nYour earlier round:\n" + JSON.stringify(history) : ""),
        { label: "attack:" + t.key + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
      ));
      let ver = null;
      if (att && att.closedGoal !== "none" && att.exitCode === 0) {
        ver = await retry("verify:" + t.key + ":r" + round, () => agent(
          RULES + "\n\nVERIFY. Do not edit the attempt. Copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile that copy with AHP/round3/lean1.sh. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from " + pinFile + ", with no extra hypotheses; (3) the pin's contents appear unchanged in the attempt; (4) every #print axioms line lists only propext, Classical.choice, Quot.sound; (5) no forbidden token. closes-goal only if all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
          { label: "verify:" + t.key + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
        ));
        if (ver && ver.verdict === "closes-goal") closed = { attempt: att, verify: ver };
      }
      history.push({ round: round, attempt: att, verify: ver });
    }
    return { track: t.key, pin: pin, history: history, closed: closed };
  },
);

const ACCEPTED = [
  "Stage B fidelity comparisons (all accepted, see AHP/fidelity/STAGE_B_RESULTS.md): AHP/fidelity/coverage-row/lean/CoverageRow.lean; AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean; AHP/fidelity/s1-touching/lean/ShellComparison.lean; AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean; AHP/fidelity/sheet-variants/lean/{CollarNonStrict,ReadingB,LambdaScale,GlobalGauge,NormHS,QuantifierOrder}.lean; AHP/fidelity/guarded/lean/UthCross.lean.",
  "Round 2: AHP/round2/s2-nonvacuity/r1-prove/Attempt.lean (goalPos1_proved); AHP/round2/s2-nonvacuity/r1-refute/Attempt.lean (goalNeg2_proved); AHP/round2/s1-touching/r1-prove/Attempt.lean (goalPos1_proved, goalPos2_proved; the corner-coverage collapse).",
  "Round 3: AHP/round3/s1-proper/r1-refute/Attempt.lean (Round3.S1Proper.goalNeg1_proved: the touching-convention refutation).",
  "S-3: AHP/round5/s3-raw/s3raw-r1/Attempt.lean (AdalyFormal.Round3.S3Rest.goalPos1_proved and, in its verbatim prefix, goalPos2_proved). It contains the whole round-3 s3-rest proof, so do NOT also add AHP/round3/s3-rest/r1-prove/Attempt.lean (same names). The round-2 S-3 first-term result AHP/round2/s3-normalisation/r1-prove/Attempt.lean (AdalyFormal.Round2.S3Pin) is a separate module; add it too.",
  "Round 7 (this run): every attempt whose verification verdict is closes-goal, listed in the JSON below.",
  "NOT accepted, do not integrate: anything under AHP/attempts/, AHP/round4/, AHP/round5/guarded/, AHP/round6/, and any attempt without a closes-goal verification. The guarded reading stays open.",
].join("\n");

phase("Integrate");
const integration = await retry("integrate", () => agent(
  RULES.replace("Never call lake env lean, lake build, REPRODUCE.sh or lake update in the main checkout.", "Never call lake env lean, lake build, REPRODUCE.sh or lake update in the main checkout. The integration rules below override this for the integration worktree only.") +
    "\n\nINTEGRATE accepted results into the Lean tree, on the integration worktree only.\n" +
    "Worktree: " + WT + " on local branch ahp-integration, created from main HEAD de2ca59. Its lean/.lake is a copy of the main checkout's and `lake build --no-build` reports all 11321 jobs up to date, so a build there is incremental. It does NOT contain the other thread's lakefile edits or lean/src/Compact* files; do not bring them in. Do not touch the main checkout except to read the AHP files.\n" +
    "Accepted results:\n" + ACCEPTED + "\nRound 7 results:\n" + JSON.stringify(oddResults) +
    "\nSteps, all inside " + WT + ":\n" +
    "1. Copy each accepted file into lean/src/AHP/ as a module with a short descriptive name (e.g. lean/src/AHP/S1TouchingRefutation.lean). Do not change any proof or statement. Strip trailing #print axioms and #check lines from the modules (they move to the Check file). If two modules declare the same fully qualified name, keep them in separate Check files; rename only if unavoidable and record every rename in lean/RENAMES.tsv.\n" +
    "2. Add the modules as roots in lean/lakefile.toml (a new [[lean_lib]] named AHPFidelity with srcDir src, or append to the existing roots, matching how earlier lanes were added; read the existing file). Add one row per module to lean/MODULES.tsv in the existing column format (sha256 of the file, source path in AHP/).\n" +
    "3. Write lean/Check9.lean (and Check10.lean etc. if names clash) with `#print axioms` for every closing declaration and every Stage B declaration, following the style of Check8.lean. Update REPRODUCE.sh only if it enumerates Check files explicitly (read it first). Append the new axiom lines to expected/axioms.expected.txt in the exact order and format REPRODUCE.sh produces, keeping the existing 508 lines unchanged.\n" +
    "4. Add one CLAIMS row per declaration to paper/CLAIMS.tsv (kind LEAN, the module path, the axiom line, a plain one-line statement, and the AHP verification file in the review column), tag fid-*. Add a section T to paper/OPEN_ITEMS.md summarising, in plain words: S-1 (touching convention refuted, totalised-inverse mechanism, every ell if round 7 closed it), S-2 (class inclusion and proper-domain non-vacuity), coverage row (Lean support; row 6 of notes/statement_sheet.tex still to be corrected by the owner, text in AHP/fidelity/coverage-row/ROW6.md), S-3 (exact match with constant 1, both constraint forms), statement-sheet variants, the guarded reading (OPEN, with AHP/round6/RESULTS.md as the record), and S-4 if round 7 changed it. Do not edit paper/paper.tex, paper/paper.pdf or notes/. Add a short refresh paragraph to HANDOFF.md in the style of the existing refresh entries.\n" +
    "5. Rebuild: export PATH=$HOME/.elan/bin:$PATH; cd " + WT + "; nohup env MAX_LEAN=2 LEAN_NUM_THREADS=1 MIN_AVAIL_GB=6 PACKAGES_FROM=" + WT + "/lean/.lake/packages ./REPRODUCE.sh > reproduce.stdout 2>&1 & . Poll reproduce.log every few minutes until it prints ALL CHECKS PASSED or FAIL. If it fails, fix the integration (never a proof) and rerun. The build should be incremental; if it rebuilds the whole tree, let it finish.\n" +
    "6. When ALL CHECKS PASSED, commit on branch ahp-integration in the worktree with a message listing what was added. Do not push. Do not merge into main.\n" +
    "Write " + WT + "/AHP_INTEGRATION.md with what was added, renames, the final reproduce.log summary lines, and the commit hash.",
  {
    label: "integrate",
    phase: "Integrate",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "xhigh",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["commit", "modulesAdded", "declarationsAdded", "reproducePassed", "reproduceSummary", "notes"],
      properties: {
        commit: { type: "string" },
        modulesAdded: { type: "array", items: { type: "string" } },
        declarationsAdded: { type: "integer" },
        reproducePassed: { type: "boolean" },
        reproduceSummary: { type: "string" },
        notes: { type: "string" },
      },
    },
  },
));

phase("Audit");
const audit = await retry("audit", () => agent(
  RULES + "\n\nAUDIT the integration branch in " + WT + " (read-only except for AHP_AUDIT.md there). Check: (1) git diff de2ca59..HEAD touches only lean/src/AHP/*, lean/lakefile.toml (new roots only), lean/MODULES.tsv, lean/RENAMES.tsv, lean/Check9.lean (and later Check files), REPRODUCE.sh (only if Check enumeration required it), expected/axioms.expected.txt (lines appended only; first 508 unchanged), paper/CLAIMS.tsv (rows appended only), paper/OPEN_ITEMS.md (section T appended), HANDOFF.md (paragraph appended), AHP_INTEGRATION.md; no frozen module changed; paper.tex, paper.pdf and notes/ unchanged. (2) Every new module is byte-identical to its AHP source apart from removed #print/#check lines and recorded renames. (3) No forbidden token in new modules; the forbidden-token expected list is unchanged. (4) Run, in the worktree, export PATH=$HOME/.elan/bin:$PATH; SKIP_BUILD=1 PACKAGES_FROM=" + WT + "/lean/.lake/packages ./REPRODUCE.sh and confirm ALL CHECKS PASSED. (5) Every CLAIMS row's declaration appears in a Check file. Write " + WT + "/AHP_AUDIT.md.\nIntegration report:\n" + JSON.stringify(integration),
  {
    label: "audit",
    phase: "Audit",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "high",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["verdict", "reproducePassed", "problems", "summary"],
      properties: {
        verdict: { enum: ["accept", "reject"] },
        reproducePassed: { type: "boolean" },
        problems: { type: "array", items: { type: "string" } },
        summary: { type: "string" },
      },
    },
  },
));

return { odd: oddResults, integration: integration, audit: audit };

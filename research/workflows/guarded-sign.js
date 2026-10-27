export const meta = {
  name: "guarded-sign",
  description: "Settle the one missing fact for the guarded counterexample: the sign of the correction D on the carrier's crossing kernel, for every scale and arbitrarily small curvature. High-precision probe, then exact closed-form and alternative-placement attacks, with an adversarial limits track. Astra in every role.",
  phases: [
    { title: "Probe", detail: "High-precision numerics: sign, scaling in curvature, structure of the crossing mode" },
    { title: "Attack", detail: "Closed-form proof, boundary-placement family, limits" },
    { title: "Verify", detail: "Independent recompile against the pinned GoalNeg2" },
    { title: "Judge", detail: "Closed or open" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. lean/.lake oleans from the 2026-10-21 fresh build are ready.",
  "Compile ONLY through AHP/round3/lean1.sh <file.lean>, run directly in your bash tool (not in a bb terminal). It serialises Lean across workers and writes <file.lean>.log and <file.lean>.exit. If your bash call times out, do not relaunch: poll for the .exit file. Never call lake env lean, lake build, REPRODUCE.sh or lake update directly.",
  "Python3 with numpy, scipy and mpmath is available (no sympy). Keep each numerical job under 8 GB of RAM and run anything longer than a minute through \"$BB_CLI\" heavy run --. Numerics are evidence only; every operator a script models must cite its Lean file and line.",
  "Write only under AHP/round6/<track>/. Do not edit lean/ (including lean/lakefile.toml and any lean/src/BalabanCompact*, lean/src/Compact* files, which belong to another thread), paper/, notes/, expected/, extras/, or earlier AHP rounds. Never run rm outside AHP/round6/<track>/. No git commit or push.",
  "Lean files cannot import AHP files. Copy needed definitions and proofs verbatim. Import only frozen modules from lean/src.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or opaque stand-ins. A result counts only if its #print axioms line lists a subset of propext, Classical.choice, Quot.sound.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop; do not loop.",
].join("\n");

const CONTEXT = [
  "THE QUESTION. The guarded all-plaquette reading is pinned in AHP/round3/guarded/pin/Statement.lean (GoalNeg2 = negation of P428Target8SG selAll selAll). Round 5 compiled a bridge: AHP/round5/guarded/ivt-r2/Attempt.lean:2382, goalNeg2_of_initial_kernel_control, proves GoalNeg2 from the premise",
  "  forall q > 0, forall R even with R >= 18, forall delta > 0, exists eps in (0, delta) with InitialKernelControl q R eps (defined at line 2368):",
  "  A(0) := twistA q R eps 1 0 is PSD and a unit; A(0) - D is PSD, with D := twistD q R eps 1 0; and for every t in (0, pi) at which twistA q R eps 1 t is PSD but not a unit, some kernel vector v of it has 0 < <v, D v>.",
  "Compiled facts to reuse: twistA_pi_negative (A at t = pi has a negative direction, every admissible scale and amplitude); the localized data B and D do not depend on the exterior twist t (AHP/round5/guarded/kernel-r2, exterior independence); first-crossing topology (ivt-r2). Read AHP/round5/RESULTS.md and the NOTES.md of ivt-r1, ivt-r2, kernel-r2, structural-r1, structural-r2 under AHP/round5/guarded/ in full before starting.",
  "What round 5 saw numerically: <v, D v> on the crossing mode is positive but tiny, about 1e-11 at R = 2 and 1e-18 at R = 6, below double-precision error at R = 6. The decay with R suggests D (which lives on level-zero plaquettes inside Omega_0, where the curvature sits) barely overlaps the crossing mode (which lives near the exterior twist). The observed transfer ||J A^-1 Theta|| grows like 1/offset near the crossing, so the crossing mode is visible to the correction.",
  "WHY FINITE CERTIFICATES ARE NOT ENOUGH: the premise quantifies over every q, every even R >= 18 and arbitrarily small eps. Any closure must be parametric in q, R and eps: an exact symbolic reduction (translation symmetry / Fourier sectors in the transverse directions, dilation identities already compiled for the dilTower family, a leading-order expansion in eps), not a numerical sample.",
  "You may also prove a DIFFERENT sufficient premise and its own bridge to GoalNeg2, as long as the final file closes the pinned GoalNeg2 itself. A useful alternative avoids exact kernels: A(t) positive definite for all t in [0, t1] and A(t1) - D not PSD (an explicit vector w with <(A(t1) - D) w, w> < 0), with A(0) - D PSD; then the first singular point of A - D on [0, t1] has A a unit there. Copy the round-5 bridge and the round-3 pin verbatim.",
].join("\n");

const probeSchema = {
  type: "object",
  additionalProperties: false,
  required: ["file", "signPositive", "epsScaling", "rScaling", "crossingSector", "structure", "confidence"],
  properties: {
    file: { type: "string" },
    signPositive: { enum: ["yes", "no", "mixed", "undetermined"] },
    epsScaling: { type: "string" },
    rScaling: { type: "string" },
    crossingSector: { type: "string" },
    structure: { type: "string" },
    confidence: { type: "string" },
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

phase("Probe");
const probe = await retry("probe", () => agent(
  RULES + "\n\n" + CONTEXT + "\n\nPROBE (no Lean proof required). Write AHP/round6/probe/PROBE.md and scripts under AHP/round6/probe/. Using mpmath at 60 or more significant digits (raise precision until results stop changing), transcribe twistA and twistD for the ivt-r2 family exactly from the Lean definitions (cite lines), reduce by the translation symmetry the family actually has (state and justify the reduction), and for several q in {1,2}, R in {18,20,24,30}, and eps in a geometric sequence down to 1e-6: (1) locate the first crossing t_c of A; (2) compute its kernel and <v, D v> with certified-looking stability across precisions; (3) check A(0) PSD and unit, A(0) - D PSD. Report: the sign; the scaling of <v, D v> in eps (power law?) and in R (exponential decay? rate?); which symmetry sector crosses first; whether the crossing kernel is simple; and any closed-form structure (e.g. the crossing mode is a known Fourier mode, t_c is independent of eps at leading order, <v, D v> = eps^p * c(R) * (1 + O(eps)) with c(R) given by an explicit sum). Also test the alternative premise: at t1 slightly below t_c, is A PD and A - D not PSD, with what margins? If the sign is negative or zero anywhere, say so plainly: that kills this counterexample family.",
  { label: "probe", phase: "Probe", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: probeSchema },
));

const PIN = "AHP/round3/guarded/pin/Statement.lean";

const tracks = [
  {
    key: "closedform",
    aim: "CLOSED-FORM PROOF of the round-5 premise (or the alternative premise) for the ivt-r2 family. Use PROBE.md's structure: block-diagonalise A, B, D by the family's exact symmetry in Lean (a unitary/orthogonal change of basis on bondSupp, proved to commute with the operators), reduce the crossing to one explicit small block, compute its kernel in closed form, and prove the sign of <v, D v> at leading order in eps with an explicit remainder bound that is uniform in q and in even R >= 18. Then close GoalNeg2 through the copied bridge.",
  },
  {
    key: "placement",
    aim: "ALTERNATIVE FAMILY. The tiny overlap (1e-18 at R = 6) suggests the interior curvature sits too far from the crossing mode. Design a variant of the dilTower / refute-r1 curved family where the curvature is placed on level-zero plaquettes adjacent to the boundary of Omega_0, next to the exterior twist, so that <v, D v> is of order eps^p with an R-independent constant. Re-establish every class, geometry, LambdaOK2, cap and competitor obligation for the variant (reuse refute-r1's cofinal_in_class_curved_competitor and dil_in_class_nonflat_competitor proofs verbatim where possible), check the sign numerically with mpmath, then prove the sign premise in closed form and close GoalNeg2. Keep the requirement that R is chosen before every cap.",
  },
  {
    key: "limits",
    aim: "ADVERSARIAL LIMITS. Try to show this route cannot work: prove in Lean that <v, D v> <= 0 on the crossing kernel for the ivt-r2 family, or that the crossing kernel is orthogonal to the range seen by D, or that A(0) - D fails to be PSD for small eps, or any other compiled obstruction to InitialKernelControl at cofinal parameters. If instead you find the sign is robustly positive, prove whatever exact partial statement you can (for example the sign at one fixed q, R as an exact identity) and say so. Do not claim a goal unless it is the pinned GoalNeg2 or GoalNeg1 exactly.",
  },
];

const results = await parallel(tracks.map((t) => async () => {
  const history = [];
  let closed = null;
  for (let round = 1; round <= 2 && !closed; round++) {
    const dir = "AHP/round6/" + t.key + "-r" + round + "/";
    const att = await retry("attack:" + t.key + ":r" + round, () => agent(
      RULES + "\n\n" + CONTEXT + "\n\nProbe results: AHP/round6/probe/PROBE.md\n" + JSON.stringify(probe) + "\n\n" + t.aim +
        "\nWork in " + dir + ". Final file " + dir + "Attempt.lean starting with the verbatim pin " + PIN + ", with #print axioms for the main declaration and every helper. Write " + dir + "NOTES.md. If you cannot close GoalNeg2, return closedGoal 'none', your furthest compiled partial result, and the concrete obstacle. Do not weaken any goal." +
        (history.length ? "\nYour earlier round:\n" + JSON.stringify(history) : ""),
      { label: "attack:" + t.key + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
    ));
    let ver = null;
    if (att && att.closedGoal !== "none" && att.exitCode === 0) {
      ver = await retry("verify:" + t.key + ":r" + round, () => agent(
        RULES + "\n\nVERIFY. Do not edit the attempt. Copy " + att.file + " byte-for-byte to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile that copy with AHP/round3/lean1.sh. Check: (1) exit 0; (2) the main declaration's type is exactly the pinned goal " + att.closedGoal + " from " + PIN + "; (3) the pin's contents appear unchanged in the attempt; (4) every #print axioms line lists only propext, Classical.choice, Quot.sound; (5) no forbidden token; (6) the main theorem has no extra hypotheses. closes-goal only if all pass. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nAttempt report:\n" + JSON.stringify(att),
        { label: "verify:" + t.key + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
      ));
      if (ver && ver.verdict === "closes-goal") closed = { attempt: att, verify: ver };
    }
    history.push({ round: round, attempt: att, verify: ver });
  }
  return { track: t.key, history: history, closed: closed };
}));

phase("Judge");
const judge = await retry("judge", () => agent(
  RULES + "\n\nJUDGE. Write AHP/round6/RESULTS.md in plain words: the probe's findings (sign, scaling, structure, confidence); per track, what compiled and the obstacle; the status of the guarded reading (closed-fails only if a verified attempt proves the pinned GoalNeg2 or GoalNeg1 with no extra hypotheses). If it closed, say exactly what the counterexample shows: whether every inverse in the printed construction exists at the failure point, or only the guarded one. If it did not close, say whether the evidence now favours the guarded reading being false, true, or undetermined, and what single fact remains. Do not edit other files.\nProbe:\n" + JSON.stringify(probe) + "\nTracks:\n" + JSON.stringify(results),
  {
    label: "judge",
    phase: "Judge",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "xhigh",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["status", "closedBy", "evidenceFavours", "summary", "stillOpen"],
      properties: {
        status: { enum: ["closed-fails", "closed-holds", "open"] },
        closedBy: { type: "array", items: { type: "string" } },
        evidenceFavours: { enum: ["false", "true", "undetermined"] },
        summary: { type: "string" },
        stillOpen: { type: "string" },
      },
    },
  },
));

return { probe: probe, results: results, judge: judge };

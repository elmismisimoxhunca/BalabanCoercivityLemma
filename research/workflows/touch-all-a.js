export const meta = {
  name: "touch-all-a",
  description: "Extend the touching-convention refutation (round 7, every ell, 0 < a < 4) to every mass a > 0, or find out whether the touching statement holds for large a. Astra: probe, then prove/refute in parallel, verify.",
  phases: [
    { title: "Probe", detail: "Where does a < 4 enter, and what happens for a >= 4" },
    { title: "Attack", detail: "Refute for all a > 0, or prove the a >= 4 slice" },
    { title: "Verify", detail: "Independent recompile against the pin" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma (Lean 4.31, Mathlib, oleans built). The machine has 16 GB RAM, 8 GB per command. Compile ONLY with AHP/round3/lean1.sh <file.lean> (at most 2 Lean jobs machine-wide; writes .log and .exit). Run it directly in bash with a long timeout; on timeout poll for .exit, never relaunch the same file. Never run lake build or REPRODUCE.sh. Keep files compact (copy definitions verbatim; import only frozen lean/src modules).",
  "Write only under AHP/round11/<track>/. Do not edit lean/ (the lakefile and lean/src/BalabanCompact*, Compact* belong to another thread), paper/, notes/, expected/, extras/, earlier AHP rounds, or /home/sebastian/BalabanCoercivityLemma-integrate. Never run rm outside your directory. No git commit or push.",
  "Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque stand-ins; a result counts only if #print axioms lists a subset of propext, Classical.choice, Quot.sound. Python3 + numpy, scipy, mpmath for evidence only (jobs under 2 GB).",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const CONTEXT = [
  "BACKGROUND. AHP/round7/s1-odd/r2/Attempt.lean (pin AHP/round7/s1-odd/pin/Statement.lean, which embeds the round-3 pin AHP/round3/s1-proper/pin/Statement.lean) proves Round7.S1Odd.goal1_proved: for every ell >= 2 and every 0 < a < 4, the ell-slice P428TouchFourAt ell hell a of the touching-convention headline P428TouchFour (four-bond touching class ClassCoupledFour, corner-selected Delta and J) fails. The proof reuses the literal family of lean/src/D1PGen.lean:24 (not_literal_every_ell, also only 0 < a < 4) and exists_nonunit_Ginv (Attempt.lean:397-401): along the exterior twist Uth, the carrier is positive at theta = 0 and has Rayleigh quotient a - 4 at theta = pi on the outward singleton field (Delta = 4 cos theta there), so for a < 4 it becomes singular at some theta < pi; the totalised inverse then makes the full form fail against a positive-energy competitor. The class does not see the exterior bonds, so the twist costs nothing.",
  "QUESTION. Is the ell-slice false for EVERY a > 0? The obstacle is that the mass term a <B,B> can dominate a single-bond -4 direction. Ideas for a refutation at large a: test fields supported on several exterior bonds or plaquettes where the touching operator's negative direction is more negative than -a (e.g. many twisted plaquettes sharing a bond, a staggered or checkerboard exterior twist, larger holonomy patterns); check how the mass term actually enters the frozen carrier (read the Ginv / genForm definitions: is the mass a multiple of the identity on the same space, or weighted?); also consider whether the class's freedom on exterior bonds allows arbitrarily negative Delta directions at all. If no direction can beat a, the touching slice might HOLD for large a (then a positive proof for a >= some a*, via the frozen proof plus a mass-domination argument, would be the outcome, and the paper would state the precise window).",
].join("\n");

const probeSchema = {
  type: "object",
  additionalProperties: false,
  required: ["file", "massRole", "mostNegativeDirection", "prediction", "plan"],
  properties: {
    file: { type: "string" },
    massRole: { type: "string" },
    mostNegativeDirection: { type: "string" },
    prediction: { enum: ["fails-for-all-a", "holds-for-large-a", "threshold-unknown"] },
    plan: { type: "string" },
  },
};

const attemptSchema = {
  type: "object",
  additionalProperties: false,
  required: ["track", "round", "file", "exitCode", "closedGoal", "mainDeclaration", "axiomLine", "remainingGap", "evidence"],
  properties: {
    track: { type: "string" },
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
  required: ["file", "recompiledExit", "statementCorrect", "axiomsStandard", "forbiddenTokens", "verdict", "reasons"],
  properties: {
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    statementCorrect: { type: "boolean" },
    axiomsStandard: { type: "boolean" },
    forbiddenTokens: { type: "array", items: { type: "string" } },
    verdict: { enum: ["accept", "reject"] },
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
  RULES + "\n\n" + CONTEXT + "\n\nPROBE. Read the frozen definitions of the carrier (Ginv, dataS, genFormS / InstIneqS, the mass term with a) and the round-7 proof. Determine exactly how a enters and why a < 4 is needed. Numerically (small admissible slabs, the transcriptions in AHP/round6/probe and AHP/round3/s1-proper/r1-refute/search.py), search exterior-only configurations allowed by ClassCoupledFour for the most negative eigenvalue of the touching (corner-selected) carrier without mass, as a function of the twist pattern. Report whether it can go below -a for every a (unbounded, or growing with the number of twisted exterior bonds per site), or is bounded (then by what). Also check how Balaban treats a in CMP 99 (sources/corpus/pages): is a an arbitrary positive constant in the printed lemma, or fixed (e.g. a = 1)? Write AHP/round11/probe/PROBE.md with the answer and a plan for the attack tracks.",
  { label: "probe", phase: "Probe", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: probeSchema },
));

const PIN = "AHP/round11/pin/Statement.lean";
const tracks = [
  { key: "refute", aim: "REFUTE FOR EVERY a > 0. First write the pin " + PIN + " if it does not exist yet (if both tracks race, the refute track owns it): copy AHP/round7/s1-odd/pin/Statement.lean verbatim and append `def GoalAllA : Prop := ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a → ¬ P428TouchFourAt ell hell a` and `def GoalLargeA : Prop := ∃ a₁ : ℝ, ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), a₁ ≤ a → P428TouchFourAt ell hell a`, compile it. Then prove GoalAllA, using the probe's most negative exterior configuration in place of the single-bond twist; reuse the round-7 proof (class membership of exterior-only twists, competitor, totalised-inverse failure) verbatim where possible. If GoalAllA is out of reach, prove the largest explicit window you can (e.g. 0 < a < c for an explicit c > 4, or every a for ell >= some bound) and say so." },
  { key: "largea", aim: "PROVE OR BOUND THE LARGE-a SLICE. Wait until " + PIN + " exists (poll; the refute track writes it), then try GoalLargeA, or the weaker statement for one fixed large a. Use the frozen proof of p428Target8 and the class inclusion ClassCoupledFour -> ClassCoupled (AHP/fidelity/s2-inclusion, compiled) plus an argument that the extra corner plaquettes' contribution is dominated by the mass term on the four-bond class. If the probe found arbitrarily negative exterior directions, instead prove a compiled obstruction: no a₁ works (i.e. not GoalLargeA), which together with the refute track settles the question." },
];

const results = await parallel(tracks.map((t) => async () => {
  const history = [];
  let accepted = null;
  for (let round = 1; round <= 2 && !accepted; round++) {
    const dir = "AHP/round11/" + t.key + "-r" + round + "/";
    const att = await retry(t.key + ":r" + round, () => agent(
      RULES + "\n\n" + CONTEXT + "\n\nProbe: AHP/round11/probe/PROBE.md\n" + JSON.stringify(probe) + "\n\n" + t.aim + "\nWork in " + dir + ". Final file " + dir + "Attempt.lean must contain the pin " + PIN + " verbatim, then your proof, with #print axioms for every declaration. Write " + dir + "NOTES.md. If you cannot close a goal, return closedGoal 'none' with your furthest compiled result and the exact obstacle." + (history.length ? "\nEarlier round:\n" + JSON.stringify(history) : ""),
      { label: t.key + ":r" + round, phase: "Attack", model: "cpa/gpt-6-astra", reasoningLevel: "xhigh", schema: attemptSchema },
    ));
    let ver = null;
    if (att && att.exitCode === 0 && att.closedGoal && !/^none/i.test(att.closedGoal)) {
      ver = await retry("verify:" + t.key + ":r" + round, () => agent(
        RULES + "\n\nVERIFY. Do not edit the attempt. Copy " + att.file + " to " + att.file.replace(/\.lean$/, ".verify.lean") + " and compile the copy with lean1.sh. Check: exit 0; the pin " + PIN + " appears verbatim; the main declaration " + att.mainDeclaration + " has exactly the type of the claimed goal " + att.closedGoal + " (or, for a partial window, a statement no weaker than the claim, with no extra hypotheses beyond the stated window); every #print axioms line lists only propext, Classical.choice, Quot.sound; no forbidden token. Write " + att.file.replace(/\.lean$/, ".VERIFY.md") + ".\nClaim:\n" + JSON.stringify(att),
        { label: "verify:" + t.key + ":r" + round, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
      ));
      if (ver && ver.verdict === "accept") accepted = { attempt: att, verify: ver };
    }
    history.push({ round: round, attempt: att, verify: ver });
  }
  return { track: t.key, history: history, accepted: accepted };
}));

return { probe: probe, results: results };

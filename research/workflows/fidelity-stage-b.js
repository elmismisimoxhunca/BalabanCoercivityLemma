export const meta = {
  name: "fidelity-stage-b",
  description: "Stage B: write and compile each approved fidelity target from AHP/fidelity/STAGE_B.md, then independently recompile and check it against its decision",
  phases: [
    { title: "Build", detail: "Astra writes the Lean file and compiles it with lake env lean" },
    { title: "Verify", detail: "A second Astra worker recompiles and checks signatures and axioms" },
    { title: "Report", detail: "One results file for all entries" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. The fresh REPRODUCE.sh run on this machine passed on 2026-10-21 (lake build exit 0, 2762 modules, axiom output identical to expected). Oleans in lean/.lake are ready. This is the coordinator's confirmation required by STAGE_B.md.",
  "Your work list entry is in AHP/fidelity/STAGE_B.md. Its linked DECISION.md is the contract: exact signatures, definitions, binders, namespaces, imports. Do not weaken, narrow, or add hypotheses to any signature. If a declaration cannot be proved, leave it out of the file and report it as failed; never replace it with sorry, admit, axiom, native_decide, unsafe, implemented_by, extern, or a weaker statement.",
  "Write only files under the entry's AHP/fidelity/<id>/lean/ directory. Do not edit lean/, the lakefile, lake-manifest.json, paper/, notes/, expected/, extras/, or other AHP files. Never run rm outside that lean/ directory. No git commit or push. Do not run REPRODUCE.sh or lake build.",
  "Compile exactly as STAGE_B.md step 3 says: export PATH=$HOME/.elan/bin:$PATH; cd /home/sebastian/BalabanCoercivityLemma/lean; \"$BB_CLI\" heavy run -- lake env lean ../AHP/fidelity/<id>/lean/<File>.lean > ../AHP/fidelity/<id>/lean/<File>.log 2>&1; echo $? > ../AHP/fidelity/<id>/lean/<File>.exit. While iterating you may compile scratch copies in the same directory, but the final .log and .exit must come from the final file.",
  "Accept an axiom line only if it lists a subset of propext, Classical.choice, Quot.sound, or says the declaration does not depend on any axioms. sorryAx or any other axiom means the declaration failed.",
  "Read the source with rg and sed; frozen declarations may sit in different files than the plan says. Keep each lean process to one file at a time.",
  "As your last action, call bb_workflow_result exactly once with the schema value. If the tool is missing, say so in plain text once and stop; do not loop.",
].join("\n");

const buildSchema = {
  type: "object",
  additionalProperties: false,
  required: ["entry", "file", "exitCode", "proved", "failed", "signaturesChanged", "notes"],
  properties: {
    entry: { type: "string" },
    file: { type: "string" },
    exitCode: { type: "integer" },
    proved: { type: "array", items: { type: "string" } },
    failed: { type: "array", items: { type: "string" } },
    signaturesChanged: { type: "boolean" },
    notes: { type: "string" },
  },
};

const verifySchema = {
  type: "object",
  additionalProperties: false,
  required: ["entry", "file", "recompiledExit", "axiomLines", "missingPrints", "nonStandardAxioms", "signatureMismatches", "forbiddenTokens", "verdict", "reasons"],
  properties: {
    entry: { type: "string" },
    file: { type: "string" },
    recompiledExit: { type: "integer" },
    axiomLines: { type: "array", items: { type: "string" } },
    missingPrints: { type: "array", items: { type: "string" } },
    nonStandardAxioms: { type: "array", items: { type: "string" } },
    signatureMismatches: { type: "array", items: { type: "string" } },
    forbiddenTokens: { type: "array", items: { type: "string" } },
    verdict: { enum: ["accept", "partial", "reject"] },
    reasons: { type: "string" },
  },
};

const entries = [
  { n: 1, key: "coverage-row", file: "AHP/fidelity/coverage-row/lean/CoverageRow.lean" },
  { n: 2, key: "s3-normalisation", file: "AHP/fidelity/s3-normalisation/lean/JetBoundaryComparison.lean" },
  { n: 3, key: "s1-touching", file: "AHP/fidelity/s1-touching/lean/ShellComparison.lean" },
  { n: 4, key: "s2-inclusion", file: "AHP/fidelity/s2-inclusion/lean/ClassInclusion.lean" },
  { n: 5, key: "sheet-q2b", file: "AHP/fidelity/sheet-variants/lean/CollarNonStrict.lean" },
  { n: 6, key: "sheet-q3", file: "AHP/fidelity/sheet-variants/lean/ReadingB.lean" },
  { n: 7, key: "sheet-q4", file: "AHP/fidelity/sheet-variants/lean/LambdaScale.lean" },
  { n: 8, key: "sheet-q6a", file: "AHP/fidelity/sheet-variants/lean/GlobalGauge.lean" },
  { n: 9, key: "sheet-q12", file: "AHP/fidelity/sheet-variants/lean/NormHS.lean" },
  { n: 10, key: "sheet-q13", file: "AHP/fidelity/sheet-variants/lean/QuantifierOrder.lean" },
];

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

const results = await pipeline(
  entries,
  (e) => retry("build:" + e.key, (attempt) => agent(
    RULES + "\n\nBUILD STAGE_B.md entry " + e.n + " (" + e.key + "), file " + e.file + ". Attempt " + attempt + ". If the file or its .log already exists from an earlier attempt, continue from it. Write every listed declaration and every listed #print axioms line, compile, fix errors, and repeat until exit 0 or until a declaration is clearly not provable as stated. Report the final exit code, which declarations compiled with standard axioms, and which failed.",
    { label: "build:" + e.key, phase: "Build", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: buildSchema },
  )),
  (build, e) => retry("verify:" + e.key, (attempt) => agent(
    RULES + "\n\nVERIFY STAGE_B.md entry " + e.n + " (" + e.key + "), file " + e.file + ". Do not edit the .lean file. Recompile it yourself into " + e.file.replace(/\.lean$/, ".verify.log") + " with the same command. Then check: (1) exit code; (2) every #print axioms line required by STAGE_B.md is present in the output; (3) each axiom line lists only standard axioms; (4) each declaration's statement matches its DECISION.md signature exactly, with no added or dropped hypotheses and no weakened conclusion; (5) no forbidden token in the file. accept only if all checks pass for every declaration. partial if some declarations pass and others are missing or failed. Write " + e.file.replace(/\.lean$/, ".VERIFY.md") + ".\nBuilder report:\n" + JSON.stringify(build),
    { label: "verify:" + e.key, phase: "Verify", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: verifySchema },
  )).then((v) => ({ entry: e.key, file: e.file, build: build, verify: v })),
);

phase("Report");
const report = await retry("report", () => agent(
  RULES + "\n\nWrite AHP/fidelity/STAGE_B_RESULTS.md in plain words. One row per entry: file, recompiled exit code, accepted declarations, failed or missing declarations, axiom summary, verdict. Then, per audit item (S-1, S-2, coverage row, S-3, sheet questions), say exactly what is now proved in Lean and what is still open, following the scope limits in STAGE_B.md and each DECISION.md. Note that the guarded target is not in this run. Do not edit any other file.\n" + JSON.stringify(results),
  {
    label: "report",
    phase: "Report",
    model: "cpa/gpt-6-astra",
    reasoningLevel: "high",
    schema: {
      type: "object",
      additionalProperties: false,
      required: ["file", "accepted", "partial", "rejected"],
      properties: {
        file: { type: "string" },
        accepted: { type: "array", items: { type: "string" } },
        partial: { type: "array", items: { type: "string" } },
        rejected: { type: "array", items: { type: "string" } },
      },
    },
  },
));

return { results: results, report: report };

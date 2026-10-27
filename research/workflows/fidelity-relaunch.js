export const meta = {
  name: "fidelity-relaunch",
  description: "Relaunch failed stage A pieces from the files already on disk, retrying each step up to three times",
  phases: [
    { title: "Attack", detail: "Kimi attacks the relaunched target" },
    { title: "Decide", detail: "Astra decides what goes to stage B" },
  ],
};

const RULES = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. Read HANDOFF.md, paper/OPEN_ITEMS.md sections B, K to N, R and S, and notes/statement_sheet.tex before writing.",
  "Do not run lean, lake, or REPRODUCE.sh in this stage. A cold build is running and its oleans are not ready.",
  "Python3 with numpy and scipy is available. Keep each numerical run under 4 GB of RAM and small tori (side at most 8). Run any script expected to take more than one minute through \"$BB_CLI\" heavy run -- python3 <script>.",
  "Write only under AHP/fidelity/<id>/. Scripts go in AHP/fidelity/<id>/numerics/. Never run rm on anything outside AHP/fidelity/<id>/. Never delete AHP/.",
  "Do not edit lean/, paper/, notes/, expected/, extras/, or the lakefile. No git commit or push.",
  "Every operator a script models must cite the Lean file and line it transcribes. A numerical result is evidence, not proof. Do not call anything a theorem.",
  "As your last action, call bb_workflow_result exactly once with the schema value.",
].join("\n");

const designSchema = {
  type: "object",
  additionalProperties: false,
  required: ["id", "prediction", "variantStatement", "numericsRun", "numericsSummary", "leanPlan", "files"],
  properties: {
    id: { type: "string" },
    prediction: { enum: ["holds", "fails", "forms-agree", "reading-only", "already-settled", "unknown"] },
    variantStatement: { type: "string" },
    numericsRun: { type: "boolean" },
    numericsSummary: { type: "string" },
    leanPlan: { type: "string" },
    files: { type: "array", items: { type: "string" } },
  },
};

const attackSchema = {
  type: "object",
  additionalProperties: false,
  required: ["id", "outcome", "defects", "vacuityChecked", "numericsFaithful"],
  properties: {
    id: { type: "string" },
    outcome: { enum: ["stands", "repairable", "wrong"] },
    defects: { type: "array", items: { type: "string" } },
    vacuityChecked: { type: "boolean" },
    numericsFaithful: { enum: ["yes", "no", "not-applicable", "not-checked"] },
  },
};

const decideSchema = {
  type: "object",
  additionalProperties: false,
  required: ["id", "decision", "leanTargets", "reason"],
  properties: {
    id: { type: "string" },
    decision: { enum: ["lean-counterexample", "lean-proof", "lean-comparison", "reading-only", "already-settled", "drop"] },
    leanTargets: { type: "array", items: { type: "string" } },
    reason: { type: "string" },
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
  return null;
}

const ids = args && args.ids ? args.ids : ["sheet-variants"];
const out = await pipeline(
  ids,
  (id) => retry("attack:" + id, () => agent(
    RULES + "\n\nATTACK target " + id + ". The design step wrote its files but never returned a result. Read AHP/fidelity/" + id + "/SPEC.md, RESULT.json if present, and every script it names. Check: does each variant say what it claims about the print; does its hypothesis class admit a proper nonempty Omega_0; does each numerical operator match the cited Lean line; are tolerances honest. Write AHP/fidelity/" + id + "/ATTACK.md.",
    { label: "attack:" + id, phase: "Attack", model: "cpa/kimi-k3", reasoningLevel: "high", schema: attackSchema },
  )),
  (attack, id) => retry("decide:" + id, () => agent(
    RULES + "\n\nDECIDE target " + id + ". Read SPEC.md and ATTACK.md in AHP/fidelity/" + id + "/. Choose what goes to the Lean stage. lean-counterexample or lean-proof only if the variant is faithful and non-vacuous. reading-only if no formal test can settle it. leanTargets lists exact declaration statements for stage B. Write AHP/fidelity/" + id + "/DECISION.md.\nAttack JSON:\n" + JSON.stringify(attack),
    { label: "decide:" + id, phase: "Decide", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: decideSchema },
  )).then((d) => ({ id: id, attack: attack, decision: d })),
);
return out;

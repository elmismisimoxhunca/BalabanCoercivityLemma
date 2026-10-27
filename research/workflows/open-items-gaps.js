export const meta = {
  name: "open-items-gaps",
  description: "Fill the two holes left by open-items-continue: a real residual-open draft and Kimi passes for residual-open and the two-domain lane",
  phases: [
    { title: "Draft", detail: "Grok writes the missing residual-open note" },
    { title: "Prosecute", detail: "Kimi prosecutes residual-open and the two-domain review" },
    { title: "Review", detail: "Sol reviews both against the files on disk" },
  ],
};

const RAM = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma.",
  "16 GB RAM, no swap, no oleans. Do not run lean, lake, elan, or REPRODUCE.sh. Do not download mathlib. Do not run rm. Do not delete AHP/.",
  "Do not edit frozen modules, lakefile.toml, paper/, CLAIMS, OPEN_ITEMS, or notes/statement_sheet.tex.",
  "No sorry, admit, axiom, native_decide, unsafe, implemented_by, or extern.",
  "compiled is false. Do not call any draft a theorem. No git commit or push.",
  "Call bb_workflow_result exactly once with the schema value.",
].join("\n");

const draftSchema = {
  type: "object",
  additionalProperties: false,
  required: ["itemId", "outcome", "summary", "compiled", "frozenFilesEdited"],
  properties: {
    itemId: { type: "string" },
    outcome: { enum: ["drafted-uncompiled", "blocked", "review-only"] },
    summary: { type: "string" },
    compiled: { const: false },
    frozenFilesEdited: { type: "boolean" },
  },
};

const prosecuteSchema = {
  type: "object",
  additionalProperties: false,
  required: ["itemId", "outcome", "defects", "mustNotWrite"],
  properties: {
    itemId: { type: "string" },
    outcome: { enum: ["stands-as-read", "qualified", "refuted", "blocked"] },
    defects: { type: "array", items: { type: "string" } },
    mustNotWrite: { type: "array", items: { type: "string" } },
  },
};

const reviewSchema = {
  type: "object",
  additionalProperties: false,
  required: ["itemId", "verdict", "grade", "disclosures", "paperSentence"],
  properties: {
    itemId: { type: "string" },
    verdict: { enum: ["adopt-with-disclosures", "reject", "owner-decision"] },
    grade: { enum: ["0", "1", "2"] },
    disclosures: { type: "array", items: { type: "string" } },
    paperSentence: { type: "string" },
  },
};

phase("Draft");
let residualDraft = null;
try {
  residualDraft = await agent(
    RAM +
      "\n\nDRAFT item residual-open. The previous draft worker died before writing anything. Write AHP/attempts/residual-open/NOTE.md and AHP/notes/residual-open.md. Classify only, unless a complete sorry-free fragment is actually in reach. Cover: (R-b) p.408 third enlargement is not a clause of IsDCube; Sol's concentric trial was a bounded diagnostic, not a threshold theorem. (R-c) p.408 takes R and M as powers of L; the formal result allows all naturals. Level-0 non-box unions. Corollary 3.6 under the altered class, keeping source a1 apart from formal a0. List the Kimi-owed lanes cube5, mixed12, level0_class, p409_sharp, r_bridge, thin_layer as document debt: no axiom print was run. Do not invent theorems. compiled false. frozenFilesEdited false.",
    {
      label: "draft:residual-open",
      phase: "Draft",
      model: "cpa/grok-4.7-build-fast",
      reasoningLevel: "high",
      schema: draftSchema,
    },
  );
} catch (err) {
  log("failed draft:residual-open: " + String(err).slice(0, 240));
}

phase("Prosecute");
let residualPros = null;
try {
  residualPros = await agent(
    RAM +
      "\n\nPROSECUTE residual-open. Read AHP/notes/residual-open.md and AHP/attempts/residual-open/NOTE.md. Try to refute any sentence that turns a diagnostic into a theorem or moves a1 and a0 together. Write AHP/attempts/residual-open/PROSECUTION.md.\nDraft JSON:\n" +
      JSON.stringify(residualDraft),
    {
      label: "prosecute:residual-open",
      phase: "Prosecute",
      model: "cpa/kimi-k3",
      reasoningLevel: "high",
      schema: prosecuteSchema,
    },
  );
} catch (err) {
  log("failed prosecute:residual-open: " + String(err).slice(0, 240));
}

let twoDomPros = null;
try {
  twoDomPros = await agent(
    RAM +
      "\n\nPROSECUTE two-domain. A review card already exists at AHP/attempts/two-domain/REVIEW.md and AHP/notes/two-domain.md. Sol's earlier SOL_VERDICT.md rejected a false projection objection in that card; do not repeat that objection. Read extras/two_domain/ and the frozen thin-layer predicates the card cites. Write AHP/attempts/two-domain/PROSECUTION.md. Say what must not be written in the paper. Do not copy the modules into lean/src.",
    {
      label: "prosecute:two-domain",
      phase: "Prosecute",
      model: "cpa/kimi-k3",
      reasoningLevel: "high",
      schema: prosecuteSchema,
    },
  );
} catch (err) {
  log("failed prosecute:two-domain: " + String(err).slice(0, 240));
}

phase("Review");
let residualReview = null;
try {
  residualReview = await agent(
    RAM +
      "\n\nSOL REVIEW residual-open. Read the note and the prosecution. Grade 2 only if you also checked IsDCube or the altered level-0 class in the frozen sources. Write AHP/attempts/residual-open/SOL_VERDICT.md, replacing the earlier grade-0 rejection of an empty submission. paperSentence empty if none.\nDraft:\n" +
      JSON.stringify(residualDraft) +
      "\nProsecution:\n" +
      JSON.stringify(residualPros),
    {
      label: "sol:residual-open",
      phase: "Review",
      model: "cpa/gpt-6.1-sol",
      reasoningLevel: "high",
      schema: reviewSchema,
    },
  );
} catch (err) {
  log("failed sol:residual-open: " + String(err).slice(0, 240));
}

let twoDomReview = null;
try {
  twoDomReview = await agent(
    RAM +
      "\n\nSOL REVIEW two-domain again, now that a prosecution file should exist. Read AHP/attempts/two-domain/PROSECUTION.md, REVIEW.md, and extras/two_domain/STATEMENT.md. Your earlier verdict rejected a false projection objection; keep that correction if the prosecution agrees. Do not certify the extras lane as a project theorem. Update AHP/attempts/two-domain/SOL_VERDICT.md. paperSentence empty unless a disclosure sentence is safe.\nProsecution:\n" +
      JSON.stringify(twoDomPros),
    {
      label: "sol:two-domain",
      phase: "Review",
      model: "cpa/gpt-6.1-sol",
      reasoningLevel: "high",
      schema: reviewSchema,
    },
  );
} catch (err) {
  log("failed sol:two-domain: " + String(err).slice(0, 240));
}

return {
  residualDraft: residualDraft,
  residualPros: residualPros,
  residualReview: residualReview,
  twoDomPros: twoDomPros,
  twoDomReview: twoDomReview,
};

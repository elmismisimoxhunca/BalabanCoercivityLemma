export const meta = {
  name: "open-items-continue",
  description: "Continue the open-items attack after the S-2 prosecution result was lost. Sol reviews S-2 from the files already written, then drafts, prosecutes, and reviews the six items that never started.",
  phases: [
    { title: "Review", detail: "Sol reviews the S-2 draft already on disk" },
    { title: "Draft", detail: "Grok drafts one remaining item at a time" },
    { title: "Prosecute", detail: "Kimi tries to refute that draft" },
    { title: "Synthesize", detail: "Status sheet for S-1 through the residual items" },
  ],
};

const RAM = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma. Read HANDOFF.md before writing.",
  "16 GB RAM, no swap, no oleans. Do not run lean, lake, elan, leanc, or REPRODUCE.sh. Do not download mathlib.",
  "Do not edit frozen modules, lean/lakefile.toml, lean/Check*.lean, expected/, paper/, or notes/statement_sheet.tex.",
  "Do not insert sorry, admit, axiom, native_decide, unsafe, implemented_by, or extern.",
  "Write only under AHP/attempts/<id>/ and AHP/notes/<id>.md. Do not delete AHP/. Do not run rm.",
  "No git commit or push. compiled is false. Do not call a draft a theorem of the project tree.",
  "End by calling bb_workflow_result exactly once with the schema value. A missing result fails the call.",
].join("\n");

const draftSchema = {
  type: "object",
  additionalProperties: false,
  required: ["itemId", "outcome", "summary", "filesWritten", "compiled", "frozenFilesEdited"],
  properties: {
    itemId: { type: "string" },
    outcome: { enum: ["drafted-uncompiled", "refuted-on-paper", "reduced", "blocked", "review-only"] },
    summary: { type: "string" },
    filesWritten: { type: "array", items: { type: "string" } },
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

const items = [
  {
    id: "s3-eta-tau",
    title: "S-3 eta and tau-star units",
    brief: "The frozen firstTerm is eta * <tau* B, (Q G1 Q*)^-1 tau* B> with eta = L^-k. Print (3.156) has no eta and no tau*. Confirm or reject, term by term, whether a<B,B>, the J term, and bondEnergy are the same units. Do not edit the paper deviation table.",
  },
  {
    id: "s4-odd-sites",
    title: "S-4 odd L sites-only cell",
    brief: "CMP 109 p.251: L is an odd integer > 11. Sites-only coverage is false for ell=2 and for even ell>=4 with ell|2(c-1) and 9 ell<=2(c-1). Undecided for other even cases and every odd ell. Attack only the odd-ell cell, or write the obstruction. Do not call it true or false without a complete sorry-free argument, and even then it is uncompiled.",
  },
  {
    id: "s5-lighter-coverage",
    title: "S-5 lighter coverage",
    brief: "notes/external_ymx/ puts regularity only on each side-M cube that contains a bond of the active set. Say whether the frozen proof needs a site or plaquette that hypothesis does not cover, and name the lemma. Do not copy the external repository.",
  },
  {
    id: "sg-guarded",
    title: "Guarded all-plaquette reading",
    brief: "P428Target8SG is neither proved nor refuted. It is equivalent to GuardResidualT and reduced to GuardPencilT. full_guard_literal is proved. Draft the missing direction, a counterexample, or a note that pins the remaining pencil. It is not the printed lemma.",
  },
  {
    id: "two-domain",
    title: "Two-domain lane review",
    brief: "Review only. Read extras/two_domain/ LOG.md, READING.md, SCOPE.md, STATEMENT.md, and src. Do not copy modules into lean/src. Write what the headlines say and what must not be written in the paper. No prosecution or Sol review exists yet.",
  },
  {
    id: "residual-open",
    title: "Residual open readings",
    brief: "Classify only, unless a complete sorry-free fragment is actually in reach. R-b: p.408 third enlargement is not a clause of IsDCube. R-c: p.408 takes R and M as powers of L; the formal result allows all naturals. Also open: level-0 non-box unions, and Corollary 3.6 under the altered class with source a1 kept apart from formal a0. List the Kimi-owed lanes (cube5, mixed12, level0_class, p409_sharp, r_bridge, thin_layer) as document debt: no axiom print was run.",
  },
];

phase("Review");
log("Continuing after wfr_3cd19fb8 failed on prosecute:s2. S-1 files stay as they are.");
let s2review = null;
try {
  s2review = await agent(
    RAM +
      "\n\nSOL REVIEW item s2-class-implication. The draft and the prosecution are already written. Read AHP/attempts/s2-class-implication/ClassImplication.lean, AHP/notes/s2-class-implication.md, and AHP/attempts/s2-class-implication/PROSECUTION.md. Do not rewrite the Lean file. Grade 2 only if you also read the frozen ClassCoupled and CubeBond definitions. adopt-with-disclosures only if the note does not exceed the uncompiled text. reject if a rebuild would be required before the implication could be believed. paperSentence empty if none. Write AHP/attempts/s2-class-implication/SOL_VERDICT.md. Do not edit the paper.",
    {
      label: "sol:s2-class-implication",
      phase: "Review",
      model: "cpa/gpt-6.1-sol",
      reasoningLevel: "high",
      schema: reviewSchema,
    },
  );
} catch (err) {
  log("failed sol:s2-class-implication: " + String(err).slice(0, 240));
}

const reviews = [
  {
    id: "s1-touching",
    note: "Already finished in the failed run. Draft outcome reduced. Prosecution qualified. Sol verdict reject. Files under AHP/attempts/s1-touching/.",
  },
  { id: "s2-class-implication", review: s2review },
];

for (let i = 0; i < items.length; i++) {
  const item = items[i];
  phase("Draft");
  let draft = null;
  try {
    draft = await agent(
      RAM +
        "\n\nDRAFT item " +
        item.id +
        " — " +
        item.title +
        "\n" +
        item.brief +
        "\nWrite AHP/attempts/" +
        item.id +
        "/ and AHP/notes/" +
        item.id +
        ".md. If you cannot finish, write the obstruction. frozenFilesEdited must be false. compiled must be false.",
      {
        label: "draft:" + item.id,
        phase: "Draft",
        model: "cpa/grok-4.7-build-fast",
        reasoningLevel: "high",
        schema: draftSchema,
      },
    );
  } catch (err) {
    log("failed draft:" + item.id + ": " + String(err).slice(0, 240));
  }
  phase("Prosecute");
  let prosecution = null;
  try {
    prosecution = await agent(
      RAM +
        "\n\nPROSECUTE item " +
        item.id +
        ". Try to refute the draft. Read the files it names and the frozen definitions. Write AHP/attempts/" +
        item.id +
        "/PROSECUTION.md.\nDraft JSON:\n" +
        JSON.stringify(draft),
      {
        label: "prosecute:" + item.id,
        phase: "Prosecute",
        model: "cpa/kimi-k3",
        reasoningLevel: "high",
        schema: prosecuteSchema,
      },
    );
  } catch (err) {
    log("failed prosecute:" + item.id + ": " + String(err).slice(0, 240));
  }
  phase("Review");
  let review = null;
  try {
    review = await agent(
      RAM +
        "\n\nSOL REVIEW item " +
        item.id +
        ". Grade 0 if you could not check the claim against the source, 1 if only the draft was read, 2 if you also read the frozen definition. Do not edit the paper. Write AHP/attempts/" +
        item.id +
        "/SOL_VERDICT.md.\nDraft:\n" +
        JSON.stringify(draft) +
        "\nProsecution:\n" +
        JSON.stringify(prosecution),
      {
        label: "sol:" + item.id,
        phase: "Review",
        model: "cpa/gpt-6.1-sol",
        reasoningLevel: "high",
        schema: reviewSchema,
      },
    );
  } catch (err) {
    log("failed sol:" + item.id + ": " + String(err).slice(0, 240));
  }
  reviews.push({ id: item.id, draft: draft, prosecution: prosecution, review: review });
  log("finished " + item.id);
}

phase("Synthesize");
let status = null;
try {
  status = await agent(
    RAM +
      "\n\nWrite AHP/STATUS.md and AHP/OWNER_DECISIONS_NEEDED.md from the files under AHP/ plus this JSON. STATUS.md must say the first workflow failed at prosecute:s2, that S-1 was rejected by Sol, and that nothing was compiled. OWNER_DECISIONS_NEEDED.md lists the red placeholders this run must not invent: author block, MSC codes, expert review, D3 and p.409 presentation, title, fresh rebuild, archive SHA and deposit, DOI and licence, declarations wording. Do not fill them in. Do not edit paper/ or lean/.\n" +
      JSON.stringify(reviews),
    {
      label: "synthesize",
      phase: "Synthesize",
      model: "cpa/gpt-6.1-sol",
      reasoningLevel: "high",
      schema: {
        type: "object",
        additionalProperties: false,
        required: ["statusFile", "ownerFile", "adopted", "rejected", "blocked"],
        properties: {
          statusFile: { type: "string" },
          ownerFile: { type: "string" },
          adopted: { type: "array", items: { type: "string" } },
          rejected: { type: "array", items: { type: "string" } },
          blocked: { type: "array", items: { type: "string" } },
        },
      },
    },
  );
} catch (err) {
  log("failed synthesize: " + String(err).slice(0, 240));
}

return { s2review: s2review, reviews: reviews, status: status };

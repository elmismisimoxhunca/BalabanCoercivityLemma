export const meta = {
  name: "open-items-attack",
  description: "Serial attack on the open Balaban coercivity items under a 16GB no-compile limit, with Grok drafting, Kimi prosecuting, and Sol reviewing",
  phases: [
    { title: "Scout", detail: "Read-only map of each open item against the Lean sources" },
    { title: "Draft", detail: "One Grok draft at a time, files only under AHP/" },
    { title: "Prosecute", detail: "Kimi K3 tries to refute each draft" },
    { title: "Review", detail: "GPT 6.1 Sol adopt-or-reject with disclosures" },
    { title: "Synthesize", detail: "Status sheet of what is drafted, blocked, or owner-only" },
  ],
};

const GROK = "cpa/grok-4.7-build-fast";
const KIMI = "cpa/kimi-k3";
const SOL = "cpa/gpt-6.1-sol";

const RAM = [
  "Workspace: /home/sebastian/BalabanCoercivityLemma (git de2ca59, private). Read HANDOFF.md and paper/OPEN_ITEMS.md before writing.",
  "MACHINE LIMIT: 16 GB RAM, no swap, no lean/.lake oleans. Do not run lean, lake, elan, leanc, lake env, REPRODUCE.sh, or any download of mathlib. Do not start a build 'just to check'. One Lean job on this tree needs missing oleans and often 6-8 GB; it will OOM this box.",
  "Do not edit frozen modules, lean/lakefile.toml, lean/Check*.lean, expected/, paper/paper.tex, paper/paper.pdf, paper/OPEN_ITEMS.md, paper/CLAIMS.tsv, or notes/statement_sheet.tex.",
  "Do not insert sorry, admit, axiom, native_decide, unsafe, implemented_by, or extern. An unfinished proof is not a theorem: leave it under AHP/attempts/<id>/ and say so.",
  "Write only under AHP/attempts/<id>/ and AHP/notes/<id>.md. Do not add Lake roots.",
  "No git commit, no push, no submission, no contact with editors or authors. Do not copy prose from the unlicensed Yang-Mills external repository; notes/external_ymx/ may be cited by path.",
  "State only what the Lean type says, including every qualifier. compiled is false for this whole run. Never write that a statement was proved in the project tree.",
].join("\n");

const scoutSchema = {
  type: "object",
  additionalProperties: false,
  required: ["itemId", "relevantFiles", "frozenBoundary", "attack", "obstruction"],
  properties: {
    itemId: { type: "string" },
    relevantFiles: { type: "array", items: { type: "string" } },
    frozenBoundary: { type: "string" },
    attack: { enum: ["new-lemma", "counterexample", "comparison", "review-only", "blocked"] },
    obstruction: { type: "string" },
  },
};

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
    id: "s1-touching",
    title: "S-1 consistent touching reading",
    brief: "Highest priority. CMP 102 p.277 identifies domains with bonds that have at least one endpoint in the domain, and plaquettes with at least one corner. Frozen CubeBond uses both endpoints; Delta and J use plaqIn Omega_0. Known: touching operators together with the both-endpoint class are false (not_P428Target8Literal, not_P428Target8LiteralBoth). NOT tested: operators AND the class (cube bonds, coverage, Lambda) all on the touching convention. Decide, as an uncompiled draft beside the frozen statement: holds (ideally from the frozen theorem plus a comparison), fails (counterexample), or the two forms agree on the relevant fields. Statement-sheet rows 5 and 7 stay open until a rebuild.",
  },
  {
    id: "s2-class-implication",
    brief: "S-2. Prove, if the types allow it, that the frozen class (ClassCoupled with CubeBond = both endpoints) contains the touching-convention class, so the frozen theorem would imply the touching-class version. The coverage clause also uses CubeBond; check that before claiming the implication. Do not edit the frozen class.",
    title: "S-2 class implication",
  },
  {
    id: "s3-eta-tau",
    brief: "S-3. The frozen firstTerm is eta * <tau* B, (Q G1 Q*)^-1 tau* B> with eta = L^-k. The print of (3.156) has no eta and no tau*. A docstring calls this a normalisation (Ingr G1 = eta^-1 iota G1 iota*). Confirm or reject, term by term, that a<B,B>, the J term, and bondEnergy are in the same units. The original lane compute/eta_tau_review_20261020 is not in this package. Do not add a deviation-table row to the paper. Write the unit comparison under AHP/.",
    title: "S-3 eta and tau-star units",
  },
  {
    id: "s4-odd-sites",
    brief: "S-4 plus the remaining sites-only cell. CMP 109 p.251, verified: L is an odd integer > 11. Sites-only coverage (CovSitesF with PerCubeRegularF, plaquette coverage dropped) is false for ell = 2 and for even ell >= 4 with ell | 2(c-1) and 9 ell <= 2(c-1). It is undecided for other even cases and for every odd ell. Attack only the odd-ell cell, or write a precise obstruction. Do not restate settled even-ell refutations as new, and do not call the odd cell true or false without a complete sorry-free argument (still uncompiled).",
    title: "S-4 odd L sites-only cell",
  },
  {
    id: "s5-lighter-coverage",
    brief: "S-5. The external account in notes/external_ymx/ imposes regularity only on each side-M cube that contains a bond of the active set. Test whether the frozen proof uses full collar coverage or would still go through under that weaker hypothesis. Cite notes by path; do not copy the external repository. If the proof needs a site or plaquette the lighter hypothesis does not cover, name the lemma.",
    title: "S-5 lighter coverage",
  },
  {
    id: "sg-guarded",
    brief: "Open mathematics: the invertibility-guarded all-plaquette reading P428Target8SG is neither proved nor refuted. It is equivalent to GuardResidualT and reduced to GuardPencilT. The full-guard variant full_guard_literal is proved. Draft the missing direction or a counterexample, or a note that pins the exact remaining pencil. Do not claim the guarded reading is the printed lemma.",
    title: "Guarded all-plaquette reading",
  },
  {
    id: "two-domain",
    brief: "Review only. extras/two_domain/ has finished sources (famTwoDom_union, famTwoDom_box, famTwoDom_cap, mixedTwoDom, totalTwoDom, target8TwoDom) that are not in lean/ and have no Claude prosecution and no Sol review. Read LOG.md, READING.md, SCOPE.md, STATEMENT.md and the src files. Do not copy them into lean/src or lakefile.toml. Write a gate note: what the headlines say, what is unreviewed, what must not be written in the paper.",
    title: "Two-domain lane review",
  },
  {
    id: "residual-open",
    brief: "Classify, and attempt a bounded fragment only when a complete sorry-free argument is in reach. (R-b) p.408 third enlargement is not a clause of IsDCube; isolated-seed sharpness witnesses need not satisfy it; Sol's concentric trial was a bounded diagnostic, not a threshold theorem. (R-c) On p.408, R and M are powers of L; the formal result allows all naturals. No multi-cube-cover optimum, no exact local-domain window, no j = 0 sharp-collar theorem. Also open: level-0 non-box unions; local analytic use of Corollary 3.6 under the altered class, keeping source a1 apart from formal a0. Do not promote diagnostics to theorems. List Kimi-owed lanes (cube5, mixed12, level0_class, p409_sharp, r_bridge, thin_layer) as document debt: this run did not print axioms.",
    title: "Residual open readings",
  },
];

phase("Scout");
log("16 GB, no swap, no oleans: scouts are read-only; later stages never invoke Lean.");
const limits = budget();
log("budget " + JSON.stringify(limits));

const scouts = await parallel(
  items.map((item) => () =>
    agent(
      RAM +
        "\n\nSCOUT only. Read files. Do not write or edit anything. Do not run shell commands that compile.\nItem " +
        item.id +
        " — " +
        item.title +
        "\n" +
        item.brief +
        "\nReturn relevant Lean and note paths, which files are frozen and must not be edited, the attack shape, and the obstruction if the attack cannot be finished without a build.",
      {
        label: "scout:" + item.id,
        phase: "Scout",
        model: "cpa/grok-4.7-build-fast",
        reasoningLevel: "medium",
        schema: scoutSchema,
      },
    ),
  ),
);

const reviews = [];
for (let i = 0; i < items.length; i++) {
  const item = items[i];
  const scout = scouts[i];
  const scoutText = scout ? JSON.stringify(scout) : "scout returned nothing";

  phase("Draft");
  const draft = await agent(
    RAM +
      "\n\nDRAFT item " +
      item.id +
      " — " +
      item.title +
      "\n" +
      item.brief +
      "\nScout JSON:\n" +
      scoutText +
      "\nWrite the attempt under AHP/attempts/" +
      item.id +
      "/ and a short AHP/notes/" +
      item.id +
      ".md. If the scout says blocked, write the obstruction and do not invent a proof. frozenFilesEdited must be false. compiled must be false.",
    {
      label: "draft:" + item.id,
      phase: "Draft",
      model: "cpa/grok-4.7-build-fast",
      reasoningLevel: "high",
      schema: draftSchema,
    },
  );

  phase("Prosecute");
  const prosecution = await agent(
    RAM +
      "\n\nPROSECUTE item " +
      item.id +
      ". You are the second model family. Try to refute the draft. Read the files it names and the frozen definitions it depends on. Look for a wrong quantifier order, a dropped hypothesis, a both-endpoint versus touching swap, an even-ell fact reused as odd-ell, a diagnostic called a theorem, and any sorry or edit outside AHP/.\nDraft JSON:\n" +
      JSON.stringify(draft) +
      "\nScout JSON:\n" +
      scoutText +
      "\nWrite AHP/attempts/" +
      item.id +
      "/PROSECUTION.md. Do not soften a defect to save the draft.",
    {
      label: "prosecute:" + item.id,
      phase: "Prosecute",
      model: "cpa/kimi-k3",
      reasoningLevel: "high",
      schema: prosecuteSchema,
    },
  );

  phase("Review");
  const review = await agent(
    RAM +
      "\n\nSOL REVIEW item " +
      item.id +
      " — " +
      item.title +
      ". Grade 0 if you could not check the claim against the source text, grade 1 if only this draft was read, grade 2 only if you also read the underlying frozen definition. adopt-with-disclosures is allowed only for a note that does not exceed the uncompiled text. reject if the prosecution refuted it or if it would need a Lean rebuild to be believed. owner-decision if only the owner can close it. paperSentence is the strongest sentence that may later be proposed; empty string if none. Do not edit the paper.\nDraft:\n" +
      JSON.stringify(draft) +
      "\nProsecution:\n" +
      JSON.stringify(prosecution) +
      "\nWrite AHP/attempts/" +
      item.id +
      "/SOL_VERDICT.md.",
    {
      label: "sol:" + item.id,
      phase: "Review",
      model: "cpa/gpt-6.1-sol",
      reasoningLevel: "high",
      schema: reviewSchema,
    },
  );

  reviews.push({
    id: item.id,
    scout: scout,
    draft: draft,
    prosecution: prosecution,
    review: review,
  });
  log("finished " + item.id);
}

phase("Synthesize");
const status = await agent(
  RAM +
    "\n\nWrite AHP/STATUS.md and AHP/OWNER_DECISIONS_NEEDED.md.\nSTATUS.md must list every item with scout attack, draft outcome, prosecution outcome, Sol verdict, files written, and the explicit line that nothing was compiled.\nAlso record the Kimi-owed document debt from OPEN_ITEMS (p409 cube5, mixed12, level0_class, p409_sharp, r_bridge, thin_layer): no axiom print was run, so those gates stay open.\nOWNER_DECISIONS_NEEDED.md lists the red paper placeholders that this run must not invent: author block, MSC codes, expert review, D3 and p.409 presentation, title confirmation, fresh rebuild of the strong form, slim-tree archive SHA and deposit, DOI and licence, declarations wording, and coverage-wording confirmation. Do not fill any of them in.\nDo not edit paper/ or lean/.\nResults JSON:\n" +
    JSON.stringify(reviews),
  {
    label: "synthesize",
    phase: "Synthesize",
    model: "cpa/gpt-6.1-sol",
    reasoningLevel: "xhigh",
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

return { limits: limits, status: status, reviews: reviews };

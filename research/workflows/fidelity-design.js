export const meta = {
  name: "fidelity-design",
  description: "Stage A of closing the statement-fidelity questions without outside experts: pin each variant statement, test it numerically on small tori, and decide whether to build a counterexample or a proof. No Lean compiles in this stage.",
  phases: [
    { title: "Design", detail: "Grok writes the variant statement, a prediction, and numerical tests" },
    { title: "Attack", detail: "Kimi checks faithfulness, vacuity, and the numerics transcription" },
    { title: "Decide", detail: "Astra decides what goes to the Lean stage" },
    { title: "Plan", detail: "One Lean work list for stage B" },
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

const targets = [
  {
    id: "s1-touching",
    brief: "Item 1. Balaban CMP 102 p.277: a region's bonds are those with at least one endpoint in it; its plaquettes those with at least one corner in it. Frozen: CubeBond (ZStatementP428.lean:145, both endpoints), plaqIn (ZR2Ops2.lean:74), CurlReads (ZR2A.lean:35), ClassCoupled (ZR6A.lean:124), CoversOm0c (ZR2A.lean:107). Known: touching operators with the frozen class are false (not_P428Target8Literal, D1Final.lean:169; not_P428Target8LiteralBoth, D2Final.lean). Read AHP/attempts/s1-touching/SOL_VERDICT.md first: the previous variant required corner-plaquette coverage by class cubes inside Omega_0, which forces Omega_0 empty or the whole torus. Do not repeat it. Design a touching class that admits proper nonempty Omega_0, for example by letting class cubes or their regularity reach the one-layer touching shell outside Omega_0. State plainly what you changed relative to the print. Then test on small tori whether the old counterexample configurations still break the touching statement, and whether a new one does. Say whether the touching operators on Omega_0 can be rewritten as frozen operators on some admissible tower (they cannot directly, since Admissible needs unions of M-blocks), or whether a counterexample is more likely.",
  },
  {
    id: "s2-inclusion",
    brief: "Item 2. The uncompiled AHP/attempts/s2-class-implication/ClassImplication.lean claims the frozen class contains the touching class. Read its SOL_VERDICT.md and PROSECUTION.md. Write a repaired copy under AHP/fidelity/s2-inclusion/ that fixes every listed defect and states only what Sol allowed, using the same touching class as target s1-touching where possible. Do not compile. List the exact imports needed so stage B can compile it with lake env lean.",
  },
  {
    id: "s3-normalisation",
    brief: "Item 4. Frozen firstTerm (ZXG3A.lean:50) carries eta and tau*; print (3.156) has neither. G1in is ZXR2Wire2.lean:82; C2fullOf (ZXR2Sector.lean:109) carries a level weight (ell^j)^-1. Read AHP/attempts/s3-eta-tau/ PROSECUTION.md and SOL_VERDICT.md: three readings of the eta placement give three powers. Pin each reading from the printed pages in sources/corpus/pages (CMP99b pp.421-428, (3.24), (3.128), (3.136), (3.156), (3.157)). Then build a small numerical model at a non-flat U and compare the frozen first term with each printed reading. The output should be either: the frozen form equals one reading up to a stated scalar (then a Lean identity is the target), or no reading matches (then a counterexample is the target).",
  },
  {
    id: "guarded",
    brief: "Item 5. P428Target8SG (D2Cons.lean:70), the all-plaquette reading guarded by invertibility, is equivalent to GuardResidualT (GdR5a.lean:54, :114) and reduced to GuardPencilT (DrEquiv.lean:99). full_guard_literal is proved. Read AHP/attempts/sg-guarded/ (note, PROSECUTION.md, SOL_VERDICT.md): the missing implication is IsUnit(Ginv_lit(0)+Shift(t)) -> IsUnit(Ginv_lit(0)+Shift(t)-D) along an exterior-only path. Search numerically on small tori for a configuration in the frozen class where the guarded form is defined but the inequality fails or the second operator is singular. If the search finds nothing, look for a structural reason the implication holds and write it as a proof plan.",
  },
  {
    id: "coverage-row",
    brief: "Item 3, already settled in the repo. OPEN_ITEMS B1 (updated 2026-10-19) says the encoded coverage-free statement granting existence of the inverses is false for every c >= 10, ell >= 2, a > 0, and that the body with both coverage clauses holds (p428Target8NCWDHcov_of_total, CaT1.lean:84; covPlaq_separately_necessary_two, CaT2d.lean:144). Row 6 of notes/statement_sheet.tex still says it is not decided. Verify the cited declarations and the claim against the source text. Find the exact theorem name of the false-for-all-c statement. Write a corrected row 6 text in AHP/fidelity/coverage-row/ROW6.md. Do not edit the sheet. What remains open is only whether Balaban's words 'the conditions are imposed on Omega_0' mean coverage; say so.",
  },
  {
    id: "sheet-variants",
    brief: "Item 6, testable part. For each statement-sheet question that has a formal alternative, write the alternative as a Lean variant and say whether the frozen theorem implies it, it implies the frozen theorem, they are equivalent, or it is likely false. Cover at least: Q2(b) non-strict collar instead of strict; Q3 and Q4 reading B of T_1 (see r_bridge files and OPEN_ITEMS R-a: Sol's readingB_* theorems); Q6(a) one global gauge instead of per-cube gauges; Q12 Hilbert-Schmidt instead of trace-normalised norm (a constant factor, so gamma0 rescales); Q13 the quantifier order, checked against P428Target8Total binder order (TT_F.lean:29). Q1 (periodic l1 distance, dimension 3, tori sides) may be classified as a convention if no variant is reasonable to prove. Numerics only where they help.",
  },
  {
    id: "sheet-reading",
    brief: "Item 6, reading part. Statement-sheet questions Q8 (DelpA, Gp, Wop, DpiFull vs (3.24), G', W of (3.119)), Q10 (chain G^-1 -> G -> G1^-1 -> G1 -> H1 with QG1Q* inverted, vs (3.122), (3.126)-(3.129)) and Q11 (B-tilde variables and C = id - hQ1) are reading questions. For each, put the printed formula (from sources/corpus/pages and the page renders) next to the Lean definition, term by term, with file and line. Where a term can be checked numerically on a small torus (for example that C B-tilde satisfies (QB)(c) = 0 on b0), do it. Report each row as matches, matches with a stated convention, or mismatch.",
  },
];

const results = await pipeline(
  targets,
  async (t) => {
    try {
      return await agent(
        RULES + "\n\nDESIGN target " + t.id + ".\n" + t.brief + "\nWrite AHP/fidelity/" + t.id + "/SPEC.md with the variant statement in Lean text, the prediction, the numerical method and results, and the stage-B Lean plan with imports.",
        { label: "design:" + t.id, phase: "Design", model: "cpa/grok-4.7-build-fast", reasoningLevel: "high", schema: designSchema },
      );
    } catch (err) {
      log("design failed " + t.id + ": " + String(err).slice(0, 200));
      return null;
    }
  },
  async (design, t) => {
    let attack = null;
    try {
      attack = await agent(
        RULES + "\n\nATTACK target " + t.id + ". Read AHP/fidelity/" + t.id + "/SPEC.md and every script it names. Check: does the variant say what it claims about the print; does its hypothesis class admit a proper nonempty Omega_0 (run or write a check if needed); does each numerical operator match the cited Lean line; are the numerical tolerances honest. Write AHP/fidelity/" + t.id + "/ATTACK.md.\nDesign JSON:\n" + JSON.stringify(design),
        { label: "attack:" + t.id, phase: "Attack", model: "cpa/kimi-k3", reasoningLevel: "high", schema: attackSchema },
      );
    } catch (err) {
      log("attack failed " + t.id + ": " + String(err).slice(0, 200));
    }
    return { design: design, attack: attack };
  },
  async (prev, t) => {
    let decision = null;
    try {
      decision = await agent(
        RULES + "\n\nDECIDE target " + t.id + ". Read SPEC.md and ATTACK.md in AHP/fidelity/" + t.id + "/. Choose what goes to the Lean stage. lean-counterexample or lean-proof only if the variant is faithful as stated and non-vacuous. reading-only if no formal test can settle it. leanTargets lists exact declaration statements for stage B. Write AHP/fidelity/" + t.id + "/DECISION.md.\n" + JSON.stringify(prev),
        { label: "decide:" + t.id, phase: "Decide", model: "cpa/gpt-6-astra", reasoningLevel: "high", schema: decideSchema },
      );
    } catch (err) {
      log("decide failed " + t.id + ": " + String(err).slice(0, 200));
    }
    return { id: t.id, design: prev.design, attack: prev.attack, decision: decision };
  },
);

phase("Plan");
let plan = null;
try {
  plan = await agent(
    RULES + "\n\nWrite AHP/fidelity/STAGE_B.md: one ordered Lean work list for stage B, taken only from the DECISION.md files. For each entry: file to write under AHP/fidelity/<id>/lean/, the declarations, frozen imports, expected outcome, and how to check axioms with #print axioms. Mark targets with no decision as not ready. Also write AHP/fidelity/SUMMARY.md in plain words: per item, what was tested, what the numbers showed, and what is still open.\n" + JSON.stringify(results),
    {
      label: "plan",
      phase: "Plan",
      model: "cpa/gpt-6-astra",
      reasoningLevel: "high",
      schema: {
        type: "object",
        additionalProperties: false,
        required: ["stageBFile", "summaryFile", "ready", "notReady"],
        properties: {
          stageBFile: { type: "string" },
          summaryFile: { type: "string" },
          ready: { type: "array", items: { type: "string" } },
          notReady: { type: "array", items: { type: "string" } },
        },
      },
    },
  );
} catch (err) {
  log("plan failed: " + String(err).slice(0, 200));
}

return { results: results, plan: plan };

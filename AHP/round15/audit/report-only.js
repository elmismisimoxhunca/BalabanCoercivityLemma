export const meta = {
  name: "guarded-collar-report",
  description: "Finish only the previously promised round-15 blueprint after timeout; no proof search, compilation or numerics.",
  phases: [{ title: "Blueprint", detail: "Audit retained evidence and write Markdown/leanblueprint closeout" }],
};
phase("Blueprint");
return await agent(
  "This is a documentation-only continuation of the cancelled guarded-collar workflow, not another research round. Read AHP/round15/audit/BLUEPRINT_TASK.md completely and follow that scope. Write only AHP/round15/BLUEPRINT.md and AHP/round15/blueprint/content.tex. Do not compile Lean, run numerical solves, spawn agents, launch workflows, or edit proofs. No unconditional closure was obtained. Use the parent's complete-record audit under AHP/round15/audit/ and the real retained files. Finish with the changed paths, verified node/status counts and unresolved issues.",
  { label: "blueprint-closeout", phase: "Blueprint", model: "cpa/kimi-k3.1-pro", reasoningLevel: "high" }
);

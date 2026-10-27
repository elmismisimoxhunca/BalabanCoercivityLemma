export const meta = {
  name: "guarded-idea",
  description: "One Opus 5.5 worker at max effort looks for a new proof idea for the guarded all-plaquette reading (GuardPencilT / P428Target8SG), tests it, and formalises whatever it can.",
  phases: [
    { title: "Idea", detail: "Find a proof idea that survives the known obstructions, test it, formalise it" },
  ],
};

const PROMPT = [
  "You are looking for a NEW IDEA to prove an open statement in a Lean 4 formalisation of Balaban's coercivity lemma (CMP 99, 1985, p. 428). Earlier agents ruled out the obvious routes. Your job is to find an argument that survives those obstructions, check it, and formalise as much as you can.",
  "",
  "WORKSPACE. /home/sebastian/BalabanCoercivityLemma (Lean 4.31, Mathlib; oleans in lean/.lake are built). Write only under AHP/round8/guarded-idea/. Do not edit lean/ (lean/lakefile.toml and lean/src/BalabanCompact*, lean/src/Compact* belong to another thread), paper/, notes/, expected/, extras/, or earlier AHP rounds. Never run rm outside your directory. No git commit or push. A separate workflow is integrating results on branch ahp-integration in /home/sebastian/BalabanCoercivityLemma-integrate; do not touch it.",
  "",
  "COMPILING. The machine has 16 GB RAM and other workers share it. Compile ONLY with AHP/round3/lean1.sh <file.lean> (it takes a shared lock, runs `lake env lean`, writes <file.lean>.log and <file.lean>.exit). Run it directly in bash; if the call times out, poll for the .exit file instead of relaunching. Never run lake build or REPRODUCE.sh. Lean files cannot import AHP files: copy definitions verbatim; import only frozen modules from lean/src. Never use sorry, admit, axiom, native_decide, unsafe, implemented_by, extern or opaque stand-ins; a result counts only if `#print axioms` lists a subset of propext, Classical.choice, Quot.sound. Python3 with numpy, scipy and mpmath is available for experiments (keep jobs under 4 GB; use \"$BB_CLI\" heavy run -- for anything over a minute).",
  "",
  "THE STATEMENT. Pinned in AHP/round3/guarded/pin/Statement.lean: GoalPos2 = P428Target8SG selAll selAll (lean/src/D2Cons.lean:70), equivalent to GoalPos1 = GuardPencilT (lean/src/DrEquiv.lean:99), equivalent (compiled, AHP/round2/guarded/r2-prove/Attempt.lean:554, goalPos2_iff_boundary_response) to boundary-response invertibility. Notation: A = Ginv for all plaquettes (the carrier), B = Ginv localised to plaquettes inside Omega_0, D = Delta2_in (assembled second-order correction), C = B - D, Theta = A - B, W = range Theta. Question: throughout the eventual class (ell >= 2 and a > 0 fixed; m large, then R large, then the smallness cap alpha0 small, in that order), does IsUnit A force IsUnit (A - D)? Equivalently, on W, does invertibility of K_B y = y + Theta B^-1 y force invertibility of K_C y = y + Theta C^-1 y?",
  "",
  "READ FIRST, IN FULL: HANDOFF.md; paper/OPEN_ITEMS.md sections K, L, N; AHP/round2/guarded/JUDGEMENT.md; AHP/round3/guarded/JUDGEMENT.md and pin/PIN.md; AHP/round4/guarded/MINE.md (419 catalogued estimates from the proof of the main theorem p428Target8Total, lean/src/TT_F.lean:29); AHP/round5/RESULTS.md; AHP/round6/RESULTS.md and AHP/round6/probe/PROBE.md; the NOTES.md files under AHP/round4/guarded/, AHP/round5/guarded/ and AHP/round6/.",
  "",
  "WHAT IS ALREADY KNOWN (do not rediscover; build on it):",
  "1. Compiled sufficient conditions: zero boundary return (B^-1(range Theta) inside the jet-input-zero subspace) gives the result; so does ||K_B^-1 (K_C - K_B)|| < 1. Exact identity (decay-r2, compiled in round5 structural-r1): K_B^-1 (K_C - K_B) y = Theta A^-1 D C^-1 y.",
  "2. No uniform gap exists (round 4 perturbation, round 5): on the flat-interior exterior-twist path Uth, B is constant and D = 0, A is a unit at angle 0 and singular at some angle < pi, all inside the class. So any proof must be correlated: D must be harmless exactly where A is nearly singular, not small in absolute terms.",
  "3. Round 5 numerics: ||J A^-1 Theta|| grows like 1/(distance to the crossing), even with the room condition (R = 18), so the near-null modes of A are visible to the dressed jet observation J. A naive invisibility argument fails.",
  "4. Compiled (round 5 kernel-r2, round 6 placement and limits): B and D do not depend on the exterior field at fixed interior data; D is exactly 0 when the background is flat on bonds within distance three of Omega_1 (correction_zero_of_flat_near_top), and when curvature sits only in outer boundary strips; D annihilates every W-dressed interior-zero input (twistD_kills_interiorInvisible). Guarded failure forces a non-flat background on the base domain and a nonzero boundary return.",
  "5. Round 6 probe (400-500 digit arithmetic): on the curved dilated family with exterior twist, <v, D v> on the first-crossing kernel v of A is positive at moderate curvature eps but NEGATIVE at very small eps (about -1.8e-170 at q = 2, R = 18, eps = 1e-100). So the candidate counterexample fails at small curvature: near the crossing, the correction pushes A - D AWAY from singularity. This is weak evidence for the positive statement.",
  "6. Structural facts that may help: A, B, A - D are symmetric; A and B are PSD at flat backgrounds; the main theorem proves coercivity of the localised form and existence of all localised inverses with constants uniform in the class (MINE.md); D is quadratic in the background's deviation from flat and controlled linearly by 12*M*alpha0 in the localised norms (AC_OL8.psi_classAC, delta2_classAC); Theta(t) = cos(t) Theta(0) + sin(t) Theta(pi/2) along the twist.",
  "",
  "IDEAS WORTH TESTING (not exhaustive; you may find better): (a) a sign or monotonicity argument: if -D is PSD on the near-null modes of A (fact 5 shows <v, D v> < 0 there at small curvature), then A - D >= A on those modes and the singularity cannot appear first in A - D; note that IsUnit A does not by itself give A PD, so check whether the class forces A PD wherever it is a unit, and check the sign of D on A's near-null space across the class; (b) a decomposition W = (part seen by D) + (part where Theta lives), with a Schur complement whose correction term has a definite sign; (c) a homotopy / spectral-flow argument: along any class path from a flat configuration, A - D and A cross singularity together, using that D vanishes when the background is flat near Omega_1 and B, D are independent of the exterior field; (d) finite-dimensional analytic perturbation in alpha0 with the cap chosen last; (e) reformulating GuardPencilT so the quantifier order (cap chosen after m and R) lets you pick alpha0 depending on the instance's own gap, if the pinned order allows it; read the pin's quantifiers carefully before using this.",
  "",
  "METHOD. Think first, at length, about why the statement should be true (or false) structurally. Test any candidate idea numerically on small admissible instances before formalising (reuse the scripts in AHP/round5/guarded/ and AHP/round6/probe/, which transcribe the actual operators with Lean line citations). Then formalise: start AHP/round8/guarded-idea/Attempt.lean with the verbatim pin AHP/round3/guarded/pin/Statement.lean and aim at GoalPos1 or GoalPos2 exactly as pinned. If the full goal is out of reach, formalise the key new lemma and a conditional theorem 'new lemma -> GoalPos2', so the remaining gap is a single clean statement. If your analysis instead finds a genuine counterexample mechanism, pursue GoalNeg2 the same way.",
  "",
  "DELIVERABLES under AHP/round8/guarded-idea/: IDEA.md (the idea in plain mathematical language, why it avoids obstructions 2-5, what is proved, what remains, with the numerical evidence); Attempt.lean with #print axioms for every declaration; its .log and .exit from lean1.sh; any scripts and their outputs. Be strict: do not call a conditional result a proof.",
  "",
  "As your last action, call bb_workflow_result exactly once with the schema value. If that tool is missing, say so once in plain text and stop.",
].join("\n");

const result = await agent(PROMPT, {
  label: "opus-guarded-idea",
  phase: "Idea",
  model: "claude-bridge/claude-opus-5-5",
  reasoningLevel: "max",
  schema: {
    type: "object",
    additionalProperties: false,
    required: ["idea", "status", "closedGoal", "mainDeclaration", "exitCode", "axiomLine", "remainingGap", "evidence"],
    properties: {
      idea: { type: "string" },
      status: { enum: ["closes-goal", "conditional", "idea-only", "counterexample-mechanism", "no-idea"] },
      closedGoal: { type: "string" },
      mainDeclaration: { type: "string" },
      exitCode: { type: "integer" },
      axiomLine: { type: "string" },
      remainingGap: { type: "string" },
      evidence: { type: "string" },
    },
  },
});

return result;

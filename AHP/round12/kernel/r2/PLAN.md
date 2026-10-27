# Kernel R2 — completed proof plan and numerical checks

The original collar-W focus was superseded during R2: the noncancellation track
proved a stronger arbitrary-field collar identity without the unit hypothesis.
`BoundaryDressing.lean` is retained as a compiled, redundant experiment, not an
additional open-gap closure.

The complementary work is:

1. Prove quadratic U(1)-invariant responses are radial on one charged complex
   line. Derive the exact unit-response singleton, with explicit norm factors.
2. Apply that result to the verbatim actual `profileCoupling`,
   `responseGradient`, `crossingKernel`, `KernelLine`, and `responseHull`.
   Obtain `NoResponseCancellation ↔ CurlDetected(generator)` without derivative
   regularity, and a direct conditional bridge to the requested cofinal premise.
3. Prove canonical first-edge localization from a negative trial at pi/2 and
   continuity/positive start, without any isolated-root hypothesis. Combine with
   R1's actual physical trace-coordinate result to obtain the entire original
   `KernelLine` and real nullity two. The physical trial and trace-zero positivity
   remain hypotheses, not theorems about the chosen star.
4. Independently reconstruct the RIGHT star at held-out q=2,R=20 using all 64
   characters and 120/155-digit arithmetic. Check full charged/neutral 9x9 Schur
   spectra, central-zero restrictions, affine pencil/derivative identities,
   physical jets, phase/scale response radiality, residuals, and precision
   stability. These are non-interval numerical evidence, not Lean proofs.
5. Separately test the explicit finite-support right-star half-pi trial, without
   Schur elimination, at q2R20, q4R22, q8R24 and 130 digits. The physical stencil
   gives -1/4; its finite enumeration/frozen-operator join is still missing.
6. Publish independently compiled compact shared copies, audit all axiom records
   and exact copied definitions, and document exact remaining propositions.

No unconditional cofinal premise, its negation, or GoalNeg2 is claimed.

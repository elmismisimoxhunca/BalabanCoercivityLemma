# Boundary conventions and spectral calculations

The supplementary material concerns alternative boundary conventions, inverse-existence assumptions, and finite-dimensional spectral models associated with multiscale coercivity.

## All-plaquette operators

The all-plaquette formulation with all required inverse-existence assumptions is proved. The weaker formulation assuming only existence of the first inverse is formally open and numerically strongly disfavoured.

Finite-matrix calculations alone do not settle this question. The missing ingredients are identification with the physical operators, nonzero area on the same kernel generator, and control over a cofinal range of scales.

## Numerical evidence

Calculations include \(q=1,2,4\) with even \(R=18,\ldots,40\), together with a held-out \(q=1,R=42\) calculation. No result is asserted for \(q=2,R=42\). These are numerical observations, not formal or interval-certified counterexamples.

## Verification scope

The supplementary files include completed and incomplete arguments. They are not all covered by the standard compilation check. A conditional implication does not establish its premises, and numerical agreement does not establish an operator identity.

Compilation evidence applies to the matching source and complete compiler output, not to an isolated axiom print or exit marker. The [verification details](../verification/README.md) describe the checks applied to the registered theorem set.

Numerical caches are not proof certificates. In particular, loading Python pickle data can execute code; inspect or regenerate it before use.

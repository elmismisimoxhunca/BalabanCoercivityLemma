# Coercivity with separate operator and regularity domains

A two-domain formulation distinguishes the domain on which an operator acts from the domain on which the background configuration satisfies regularity assumptions:

\[
\Omega_0^{\mathrm{op}}\subseteq\Omega_0^{\mathrm{cl}}.
\]

The operator tower is admissible with the specified level-zero collar. The regularity tower agrees with it at every positive level. Coverage and local regularity are imposed on the larger domain; the operators and admissible fields are defined on the smaller domain.

This distinction is relevant to Balaban, *Propagators for lattice gauge theories in a background field*, CMP **99** (1985), pp. 394 and 396. The operator domain may be a thinner layer, whereas the regularity conditions are described using a specified block layer. Treating the two as different sets is a mathematical formulation, not a conclusion forced by the shared notation in the text.

## Geometric considerations

Intersecting a regularity set with the operator domain need not preserve the requirement that it meet the level-zero stratum. This can fail for a disconnected union of blocks. The construction for such unions adjoins a separated regular block; it requires a collar threshold of at least 4 in addition to the coercivity threshold. Box and cap formulations have separate statements.

The assumptions retain alignment, periodic distance, site and plaquette coverage, domain inclusion, and agreement of the positive-level towers. No conclusion is asserted below the required collar threshold or when the higher-level domains differ.

## Verification scope

The [formal statements](src/) are supplementary and are not included in the standard compilation check. The recorded verification of the registered theorem set does not certify these files.

# Coordinator notes for round 10

## Priorities for round 2 (written after round 1, 2026-10-23)

1. **Dictionary track: yes, prioritise the neutral H0 J' source recurrence dictionary that `SourceDominance` needs.** Build only what the nonvanishing argument consumes. Full spatial W/Q/T transport is lower priority unless the nonvanishing route requires it.
2. **The q-dilation identity is dropped.** Exact isometry of q-dilated blocks to q = 1 blocks is false: the longitudinal lengths 2Rq, (8R+8)q, 2Rq cannot equal 2R', 8R'+8, 2R' unless q = 1 (dictionary r1). Do not build on it. The numerics only show the normalised constant K is q-independent up to exponentially small tails.
3. **One-character concentration of the crossing kernel needs a spectral exclusion argument, not symmetry alone.** If that is expensive, prefer a premise that tolerates a kernel spread over several characters (full-kernel definiteness), or a route that works sector by sector.
4. **Memory.** The machine has 16 GB and each command is capped at 8 GB. Never compile the 12k-line round-9 file here. Prove premises in compact harnesses that copy definitions verbatim. The coordinator compiles the full concatenation later.
5. **The goal stays the same:** nonvanishing (either sign) of the first-order coupling on the crossing kernel, for infinitely many dyadic q and, for each, infinitely many even R >= 18 of your choosing.

## Relay after round 3 (dictionary -> assembly)

Dictionary r3 compiled (r3/Actual.lean): profileCoupling = vacCoupling(sourceStencil[f]) = 2 * sum localized neutral-curl(H0 vacJet u) * curl(f). With f = responseProfile the coupling equals 2 * sum curl^2, so some profile has nonzero explicit coupling iff that actual neutral curl is nonzero.

Requested of assembly: specialise round-9 limit_Delta2_div_form (with bulk_H_cont, bulk_C2_tendsto, hasDerivAt_corrDeriv, R2 bulkSource_tendsto) to the arbitrary-profile corrDeriv form, so the identity feeds CofinalAnyProfileCoupling. The dictionary track can supply a compact conditional limit-form helper.

Remaining after that: nonzero neutral curl from a nonzero aggregated jet (nonvanishing r3: flat two-site Q/flux obstruction), a nonzero crossing jet, full-kernel definiteness, nested cofinal scales.

# Reviews of early statement comparisons

These notes concern early drafts under `attempts/`, not the current status of the formalisation. See [Results and scope](../RESULTS.md) for later compiled results. The reviews below are mathematical analysis of draft claims, not compilation certificates.

## Findings that matter when reading the drafts

- **Touching conventions:** class inclusion alone does not identify the full touching operator with the original operator. The early corner-coverage proposal also collapses proper nonempty domains. Later touching refutations and non-vacuity results must be read under their own definitions.
- **Class inclusion:** coverage requires product-box geometry, not merely monotonicity of a bond predicate. Different namespaces use different meanings of `ClassCoupledTouch`.
- **Normalization:** the early claim of a mismatch in the second-order correction is unsupported: it omits the level weight in `C2fullOf`. Flat cancellations do not by themselves prove a full non-flat operator identity. See the later [`S3FullComparison.lean`](../lean/src/AHP/S3FullComparison.lean).
- **Odd block factors:** an obstruction to one constant-magnitude construction is not a theorem excluding every variable-magnitude profile or gauge construction.
- **Lighter coverage:** excluding cubes containing one row bond does not exclude cubes containing every active bond. The early advertised uncovered-plaquette refutation is not established by that argument.
- **Guarded all-plaquette formulation:** failure at a single scale does not refute an eventual, cofinal statement. Bare algebraic examples do not establish the corresponding lattice statement, and indefiniteness alone does not establish singularity.
- **Two-domain variant:** the review card’s proposed projection correction is wrong and must not be applied. This does not certify the variant as part of the main theorem; [`extras/two_domain/`](../extras/two_domain/) is outside the default build.

## Drafts and mathematical reviews

The review labels distinguish assessment of a draft from proof of its mathematical statement. Later reports may supersede earlier objections.

| Topic | Draft | Detailed review |
|---|---|---|
| Touching | [Touching.lean](attempts/s1-touching/Touching.lean) | [Review](attempts/s1-touching/SOL_VERDICT.md) |
| Class inclusion | [ClassImplication.lean](attempts/s2-class-implication/ClassImplication.lean) | [Review](attempts/s2-class-implication/SOL_VERDICT.md) |
| Normalization | [Units.lean](attempts/s3-eta-tau/Units.lean) | [Review](attempts/s3-eta-tau/SOL_VERDICT.md) |
| Odd block factors | [OddSites.lean](attempts/s4-odd-sites/OddSites.lean) | [Review](attempts/s4-odd-sites/SOL_VERDICT.md) |
| Lighter coverage | [LighterCoverage.lean](attempts/s5-lighter-coverage/LighterCoverage.lean) | [Review](attempts/s5-lighter-coverage/SOL_VERDICT.md) |
| Guarded formulation | [PencilPin.lean](attempts/sg-guarded/PencilPin.lean) | [Review](attempts/sg-guarded/SOL_VERDICT.md) |
| Two domains | [Initial review card](attempts/two-domain/REVIEW.md) | [Correction](attempts/two-domain/SOL_VERDICT.md) |
| Other source questions | [Note](attempts/residual-open/NOTE.md) | [Review](attempts/residual-open/SOL_VERDICT.md) |

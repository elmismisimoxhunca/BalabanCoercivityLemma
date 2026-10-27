# Dictionary R4 — final hand-off: color selection, not crossing nondegeneracy

**GoalNeg2 and every original cofinal coupling premise remain OPEN. No actual coupling premise has been refuted.**

## Compiled publications

- `R4_ColorSelection.lean`: 299 lines, 22 new declarations, frozen `DrEquiv` only.
- `R4_ColorResponse.lean`: 2185 lines, 61 new declarations, 194 total axiom records. Includes the complete unchanged R3 free-source dictionary.
- Local originals: `dictionary/r4/Color.lean`, `dictionary/r4/Actual.lean`.
- All four paths independently compile with clean exit **0**, only `propext`, `Classical.choice`, `Quot.sound`. The full shared file was additionally recompiled in the recovery continuation. Local/shared bytes match; `dictionary/r4/CHECKS.json` passes, including the R3 byte prefix and four verbatim source fragments.

## Actual-operator results

1. `Color.flatJet_gauge`: the actual flat dressed jet C2(W iE u) is equivariant under **every constant SU(2)** gauge. `ColorResponse.flatH_constant` gives the same covariance for full flat H. This is not full SU(2) symmetry of an exterior-twisted carrier.
2. `Color.flatJet_neutral_zero`: neutral input has zero **full** quadratic jet. `flatJet_charged_neutral`: charged input has neutral jet. `flatJet_single_color_zero`: a charged input in either flip eigenspace has zero full jet.
3. `ColorResponse.vacJet_chargedPart_component`: charged projection preserves every neutral component of the actual physical jet, before aggregation. The neutral and charged projections form an exact orthogonal decomposition.
4. `responseProfile_chargedPart`, `curlDetected_chargedPart_iff`, `profileCoupling_chargedPart`: the full constrained response profile, curl detection, and every free-profile explicit coupling depend only on the charged part. The profile is U(1)-invariant and changes sign under the constant color flip. Opposite flip eigenspaces obey the exact mixed scaling law `responseProfile_mixed`.
5. `ColorObstruction.exists_charged_invisible`: for **every q>0,R**, an explicit nonzero physical charged field has vacJet=0 and zero coupling to **every** profile. It is a single-bond `pauliE1` field at the actual site (4q,0,0). It is **NOT asserted to be a crossing vector**.

Item 5 is a rigorous obstruction to “nonzero plus charged implies jet detection,” not a refutation of the actual crossing-coupling premise. The flip generally changes the twisted background; its eigenspaces cannot be assumed to contain a crossing vector.

## What remains

R3's compiled chain TopJetDetected -> CurlDetected -> positive adaptive coupling remains available, with the known full flat constraint unit visible. Still missing are crossing-specific detection, whole-kernel charged-line containment or a legitimate single-profile definiteness argument on the whole kernel, and nested cofinal dyadic scales/even radii. The exact unproved sufficient statement `Assembly.R3.CofinalAnyPathCurlLine` and its predicates are reproduced in `dictionary/r4/NOTES.md`.

No full spatial W/Q/T covariance, transverse character splitting, block-dimension theorem, crossing spectral exclusion, or cofinal nondegeneracy has been proved here. No canonical q=1 radius dilation isometry is assumed. The arbitrary-profile corrDeriv identification remains assembly R3's result with visible known regularity, not a new unconditional calculus theorem in this file.

**Question for future nonvanishing work:** which smallest actual W/C2 boundary or path identity will let the crossing equation force a nonzero mixed-color jet? A general nonzero charged vector cannot suffice. If abandoning KernelLine, what actual property rules out cancellation among the responses of different kernel directions?

Full mathematics, exact statements, recovery history, limitations and reproduction: `AHP/round10/dictionary/r4/NOTES.md`. No new numerics, large historical compilation, build/REPRODUCE, protected edits, commit, push or deletion.

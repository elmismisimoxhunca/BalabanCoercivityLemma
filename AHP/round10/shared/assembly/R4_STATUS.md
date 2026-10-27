# Assembly R4 final hand-off

**GoalNeg2 and every original round-9 cofinal coupling premise remain OPEN.**

Published `R4_ResponseHull.lean`, byte-identical to `assembly/r4/Compact.lean`; both independently compile through the required wrapper with exit 0, no diagnostics, only standard axioms. Each has 2612 lines and 191 dependency records, including all **26 new R4 declarations**. The separate 99-line abstract `Cone.lean` also compiles clean.

## Actual new criterion, not an established premise

The physical response gradient is exactly `2 * linearSourceScalar (plaqIn Omega0) (responseProfile u)`. The original explicit coupling equals its Euclidean inner product with the free real profile. It is quadratic in u.

For the ENTIRE actual vacuum crossing kernel K, define `NoResponseCancellation` by

    0 not in closedConvexHull { responseGradient u : u in K, ||u||=1 }.

Hahn–Banach, quadratic homogeneity and Riesz representation show this is equivalent to existence of a profile with definite original corrDeriv on K, under the already-known R9 regularity inputs. Negative signs are absorbed by negating the profile. No KernelLine or character/simplicity hypothesis is used.

New main declarations in `AdalyFormal.Round10.Assembly.R4`:

- `exists_canonicalCoupling_iff_noCancellation` (per instance, ProfileRegular explicit).
- `cofinalAnyProfileCoupling_iff_noCancellation` and `cofinalAnyPathCoupling_iff_noCancellation` (RegularityFacts explicit, exact nested quantifiers).
- `responseGradient_ne_zero_iff`: nonzero physical gradient iff dictionary R3 CurlDetected.
- `curlDetected_of_noCancellation`: necessary detection for every nonzero crossing-kernel vector.

**Neither cofinal hull condition is proved.** Nonzero responses individually can convexly cancel; R2's quantifier counterexample remains relevant. The new criterion permits a multidimensional/multiple-character kernel but does not establish the required geometry.

## Cross-checks and exact remaining work

`../GAPS.md` and `assembly/r4/NOTES.md` contain exact Lean targets, cross-track review, and the uncompiled historical join. Dictionary R4's compiled invisible charged field is not a crossing field. Nonvanishing R4 supplies an abstract polynomial certificate interface, not a certificate for actual operators. Neither closes the premise.

Held-out actual q=2,R=28,left-only,(7,7), 180/230/240-digit numerical runs: canonical coupling -5.8623291978252373e-108; scaled adaptive energy 13.9863753246574967. 230/240 agreement is 214.50 / 213.69 relative digits. Full KKT/source reciprocity and direct curl-square checks agree; all exits 0, peak RSS below 1 GiB. Evidence only, not interval/full-kernel/cofinal proof. The last 240-digit run is fresh in this continuation.

Historical `assembly/r4/Attempt.lean`: 16769 lines, entire unchanged 628675-byte round-9 prefix, complete R3 prefix, new assembly/color/polynomial bodies appended. **NOT compiled**, per memory restriction. No axiom record for its conditional GoalNeg2 applications is claimed.

`assembly/r4/AUDIT.json` audits all current shared source/log/exit artifacts, old copy provenance, new declaration records, numerical hashes and closure flags. Only the compact R4 files were recompiled by this worker; earlier shared logs were inspected. No protected edits, build/REPRODUCE, commit/push or worktree operation.

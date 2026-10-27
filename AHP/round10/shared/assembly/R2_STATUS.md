# Assembly r2 hand-off — concrete glue compiled; GoalNeg2 OPEN

## Published compiled files

- `R2_SourceGlue.lean` (1506 lines, sole import frozen DrEquiv), original `assembly/r2/Compact.lean`: independently compiled at both paths, exit 0, no diagnostics. 80 dependency records, including every one of 14 new concrete declarations, all standard axioms.
- `R2_ProfileQuantifiers.lean` (67 lines, sole import frozen D1IVT), original `assembly/r2/ProfileQuantifiers.lean`: independently compiled at both paths, exit 0. Six new declarations, all standard axioms.

## Preferred endpoint

Namespace `AdalyFormal.Round10.Assembly.R2`:

```lean
cofinalAnyProfileCoupling_of_sourceFamily :
  CofinalSourceFamily →
    AdalyFormal.Round9.Guarded.QualitativeR2Joint.CofinalAnyProfileCoupling
```

This combines the nonvanishing track's **R2** finite source-family theorem with the **actual named** round-9 carrier and derivative. A nonzero jet vector may choose a source site; no first-jet domination is required. `exists_profile_coupling_of_sourceColumns` accepts physical source amplitudes satisfying the explicit equations, avoiding an equality to chosen amplitudes.

**CofinalSourceFamily is NOT proved.** Still missing: actual H/source/C2/W column dictionary (including physical normalization), a nonzero actual crossing jet vector, full-kernel containment in one charged complex line or another common-sign argument, and nested cofinal scales/radii. `../GAPS.md` has the exact Lean statements and updated numerical cross-checks.

`canonicalCoupling_of_line` works for any exterior path, consumes actual `corrDeriv_U1` and the new unconditional `corrDeriv_symmetric`, and does not add a soft-regularity premise. `canonicalCoupling_of_kernelSource` is a whole-kernel alternative with explicit coercive-sign and domination hypotheses, not supplied for the actual kernel.

## Caution proved, not just asserted

`ProfileQuantifiers.every_vector_has_profile` and `no_profile_definite` exhibit an exact U(1)-invariant traceless quadratic pencil on two complex coordinates. Every nonzero vector has a positive detecting profile, but no profile is definite on the whole space. Do not exchange these quantifiers after applying free-source controllability. This is an obstruction to that shortcut, not a refutation of an actual premise.

## Independent checks

Actual q=4,R=20,left twist,(15,15), 200/250 digits: c1=−1.3573361033310478e−140, 183.12 relative digits agreement, residual/absolute(c1)=1.66e−103. The fixed-source domination inequality is supported over 336 blocks.

New generalized sources i=2,112,334 at the same geometry: separate hyperbolic-Green calculation versus the full neutral KKT system, 150/190 digits. Maximum 190-digit source discrepancy 3.72e−189, full residual 2.69e−190. Evidence only, no interval certification or cofinal result.

## Assembly and audit

`assembly/r2/Attempt.lean` (13948 lines) preserves the complete 628675-byte round-9 qualitative prefix. It appends these compiled pieces plus two conditional final bridge applications. **The large assembly is not compiled**, per coordinator memory instructions, and no final axiom record is fabricated. `GoalNeg2` remains open.

Dictionary R2's final publication was also reviewed: 88 standard-axiom records, fresh exit 0, exact raw J' stencil and neutral physical scalar sum proved. `DICTIONARY_REVIEW.json` records the audit. Its new bodies are included in the uncompiled full assembly; the actual H* tridiagonal lift remains open. Using a physically aggregated longitudinal jet would avoid needing a transverse Bloch normalization theorem.

`assembly/r2/CHECKS.json`: PASS. All four final compiles verified, copied declarations and shared bodies checked, closure flags explicitly false. Full details: `assembly/r2/NOTES.md`. No protected source or earlier-round edit, no build/REPRODUCE, no commit/push.

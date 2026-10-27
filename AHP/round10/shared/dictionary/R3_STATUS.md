# Dictionary R3: free-profile curl energy and joint physical-jet detection

**GoalNeg2 and every original cofinal coupling premise remain OPEN.**

Published and independently compiled at both local/shared paths:

- `R3_FreeSource.lean` — 1590 lines, 133 standard-axiom records, clean exit 0.
- `R3_JetDetection.lean` — 2491 lines, 220 standard-axiom records, clean exit 0.

`dictionary/r3/Scalar.lean` also compiles clean. All five final compile records pass `dictionary/r3/CHECKS.json`: 52 new dictionary declarations individually printed; only propext, Classical.choice and Quot.sound; no diagnostics/prohibited devices; original/shared bytes equal; copied operator definitions unchanged.

## New exact actual-operator identity

In `Dictionary.FreeSource`, let

\[
r_u(b)=\langle E_3,(i_EH_0C^2_0(W_0i_Eu))(b)\rangle.
\]

`responseProfile` denotes r_u and `profileCoupling q R f u` is the original analytic `vacCoupling` with the exact R2 `profileSourceStencil[f]`. For every q,R,f,u, **without spectral hypotheses**:

\[
\mathrm{profileCoupling}(f,u)=2\sum_{p\in\mathrm{plaqIn}(\Omega_0)}c_{r_u}(p)c_f(p),
\qquad
\mathrm{profileCoupling}(r_u,u)=2\sum_p c_{r_u}(p)^2.
\]

`exists_profile_iff_curlDetected` proves that some real profile couples nontrivially iff this actual constrained lift has nonzero neutral curl on a selected plaquette. `adaptive_pos_iff` provides the explicit positive profile r_u. This bypasses the source-column tridiagonal dictionary for the fully free-profile route; it does not prove the curl is nonzero.

The arbitrary-profile source and explicit coupling are U(1)-invariant; full H0*J'[f] is neutral and its pairing is the exact physical level-one sum. `responseField_Q` and `responseProfile_level_zero` identify the physical neutral projection and zero level-zero rows using only the full flat constraint-unit premise.

## Combined physical-jet hand-off

`R3_JetDetection.lean` includes the final nonvanishing R3 physical-blocking/flux theorem, with duplicate geometry definitions omitted. The new joint theorem is:

```lean
AdalyFormal.Round10.Dictionary.JetDetection.curlDetected_of_topJet
    {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (hN : IsUnit (Dictionary.KKT.N (AnalyticR2.flatData q R)))
    (u : AnalyticR1.TwistSpace q R)
    (hjet : Nonvanishing.DilatedFlux.TopJetDetected hq R u) :
    Dictionary.FreeSource.CurlDetected q R u
```

Here TopJetDetected is exactly the nonzero sum of the normalized physical level-one direction-1 C2(WiEu) coordinates over all even transverse cells at some longitudinal block. `physicalJetAggregate` is definitionally the same aggregate (`topJetDetected_iff`). The proof uses actual QH=1, not a guessed source normalization. The full-flat-N-unit hypothesis stays explicit; round 9 supplies it on the admissible instances.

`adaptive_pos_of_physicalJet` and `exists_profile_of_physicalJet` give strictly positive explicit coupling and an existential nonzero profile from the indexed aggregate condition.

## What remains

1. Prove TopJetDetected (or directly CurlDetected) for a genuine crossing generator.
2. Prove entire-kernel charged-line containment or another common-sign definiteness criterion.
3. Supply nested cofinal scales and radii.

The explicit-form-to-actual-corrDeriv link is assembly R3's `corrDeriv_profile_form`, using visible round-9 regularity premises in its compact harness. This dictionary does not claim that new arbitrary-profile derivative application unconditionally. The regularity itself was already proved in round 9; the crossing jet and whole-kernel claims were not.

Full spatial W/Q/T covariance, character decomposition, spectral exclusion and exact dilation remain unproved here. No canonical q=1 isometry is used. No numerical evidence is substituted for a proof.

Full mathematics, exact remaining cofinal target, next-round question, reproduction and copy/audit details: `AHP/round10/dictionary/r3/NOTES.md`. The coordinator-requested one-line joint hand-off was added to `shared/GAPS.md`; other tracks' Lean sources were not edited.

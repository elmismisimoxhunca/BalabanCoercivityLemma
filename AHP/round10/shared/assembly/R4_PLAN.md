# Assembly R4 — initial plan (superseded)

Final status: `R4_STATUS.md`; exact remaining statements: `../GAPS.md`; complete report: `AHP/round10/assembly/r4/NOTES.md`. Final Compact has 2612 lines and clean local/shared compilations. GoalNeg2 remains OPEN. The text below records the earlier development stage.

## Earlier progress

GoalNeg2 remains OPEN. `assembly/r4/Compact.lean` now compiles (2504 lines, standard axioms): the actual free-profile coupling is the inner product with the exact physical response gradient

`responseGradient u = 2 * linearSourceScalar (plaqIn Omega0) (responseProfile u)`.

Hahn–Banach + Riesz gives an exact per-instance equivalence, without KernelLine or any character decomposition:

`(exists f, CanonicalCoupling q R V (corrDeriv q R f)) <-> NoResponseCancellation q R V`

where NoResponseCancellation says zero is NOT in the closed convex hull of the response gradients of ALL unit vectors in the actual crossing kernel. The known R9 ProfileRegular inputs are explicit in the compact theorem. This is not proved for any actual cofinal family. It identifies the precise extra strength beyond vectorwise jet/curl detection, and permits mixed-character or higher-dimensional kernels if their responses cannot convexly cancel.

I am adding cofinal equivalences and auditing the R4 track results. The cheaper criterion avoids spectral simplicity but still needs actual noncancellation; it does not solve that mathematics.

Independent held-out q=2,R=28,left-only,(7,7),180/230-digit full KKT / curl-energy checks both completed under 2 GiB. Final summary will be in GAPS. No historical large compile attempted.

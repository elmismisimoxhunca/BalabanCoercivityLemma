# Guarded item — perturbation route, round 1

**Pinned goals remain open. `closedGoal: none`.**

This attempt preserves the full round-3 pin as an exact byte prefix. It imports only frozen `DrEquiv`; no AHP module is imported. The question is the pinned formal reading, not the unqualified printed assertion.

## Route and concrete obstruction

A unit at a fixed flat background has a positive, background-dependent gain. A compact parameter set consisting **entirely** of units has a uniform inverse bound. Neither fact gives a uniform bound on the *guarded subset* of a compact family that also contains singular carriers. The guard subset need not be closed.

There is an obstruction in the actual frozen lattice family, not merely in an abstract matrix example:

- On the exterior-twist family `Uth`, the localized carrier `B` is constant, and the localized correction `D` is zero.
- The frozen localized theorem makes the initial flat carrier a unit on sufficiently large NV slab instances.
- The frozen `exists_nonunit_Ginv` provides a singular carrier on the same continuous twist path inside `[0, π]`.
- A positive lower gain uniform over the guarded points would make the unit locus both open and closed along this connected path. That contradicts its unit and non-unit endpoints.
- A positive lower gain uniform for the actual `K_B` responses would also imply a uniform carrier gain. The proof handles the changing spaces `range(A-B)` pointwise; it never identifies their dimensions or interchanges compression and inversion.

The main proposed partial declaration is `AdalyFormal.Round4.Guarded.PerturbR1.nv_guard_no_uniform_response_gap`. It supplies the full actual class, torus, admissibility, Lambda and positive-energy-competitor conditions, at fixed `ell=2`, `a=1`, `k=2`, cofinally large `m,R`, and arbitrarily small positive capped class parameter. For every positive gain `δ`, a guarded unit response on that same finite torus has a nonzero vector `y` with `‖K_B y‖ < δ ‖y‖`.

**This is NOT a negative pinned-goal witness.** Every background used has `D=0`, so `C=B` and `K_C=K_B`. The corrected carrier remains a unit whenever the guard holds. The result attacks the proposed uniform-gap inference, not the original headline or the inverse-relative product route. A product estimate could still exploit cancellations or correlated vanishing even when `‖K_B⁻¹‖` alone is unbounded.

## Small correction, with exact premises

`local_delta_norm_of_strat` converts the genuine localized weighted quadratic estimate into an ordinary operator-norm bound without a depth factor in this direction. It uses symmetry of the actual `Delta2` and the frozen inequality `wnormSq x ≤ ‖x‖²`.

`local_delta_norm_linear` proves

\[
\|P.\mathrm{data}.\Delta_2\|\le 2C_\psi K_2 C_W\,t
\]

from the actual source bound `‖psiD P p‖ ≤ Cψ*t`, the raw second-jet bound and weighted `Wop` bound. These analytic premises remain explicit. This is not a new proof of their uniform class-wide availability, and does not claim an `O(alpha0²)` raw-jet estimate. When supplied by the mined chain, `t=12 M alpha0`.

`pencil_unit_of_gain` gives the actual corrected-carrier unit conclusion when the correction norm is less than a genuine carrier gain. No new premise is inserted into any pinned goal.

## Verification

Final verification pending while the source is being compiled. Only files in this attempt directory are authored. Compilation is exclusively through `AHP/round3/lean1.sh`. No numerical script, reproduction, build, dependency update, protected-source edit, deletion outside the directory, commit or push is performed.

One initial direct wrapper invocation timed out while waiting for the shared lock and left no exit record. Process inspection confirmed it was no longer running; it is not counted as a successful compile. Subsequent source versions use distinct `CheckV*.lean` files in a persistent environment terminal. No duplicate live compile is launched.

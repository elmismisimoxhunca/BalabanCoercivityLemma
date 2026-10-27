
/-!
Round 9, qualitative route: first-order separation at fixed scale and radius, with a free
exterior path and a free interior profile.

At zero curvature the localized correction vanishes, so for small curvature a corrected
crossing can only split off a vacuum crossing.  Two abstract theorems turn zero-curvature
data into a separation at EVERY small positive curvature:
* `first_order_separation`: the vacuum carrier is positive definite just before a crossing
  angle and has a negative direction just after it, the carrier is jointly continuous at
  zero curvature, and the first-order correction is positive definite on the vacuum
  kernel (no angle derivative, no gap constant, no scalar action; pre-crossing sign);
* `perturbative_sign_change`: both signs, under joint differentiability and a scalar
  action on the kernel.
The concrete part allows any continuous exterior path and any bounded interior profile
(round 5 `maskedU`).  Reflecting the profile reflects the curvature, so a coupling of
either sign gives a pre-crossing separation for the profile or for its reflection.  The
remaining premise `CofinalVacuumCoupling` is a statement about zero curvature plus soft
regularity.

Nothing here proves a pinned goal.  The family premises are explicit, unproved
hypotheses on the actual operators; the abstract lemmas are finite-dimensional facts.
-/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)
open AdalyFormal.Round8.Guarded.SignFree (unit_of_definite_complements)
open AdalyFormal.Round5.Guarded.IVTR2 (first_carrier_crossing)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


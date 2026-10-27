import R7Fork.ZT5A
import R7Fork.ZT5B
import R7Fork.ZT5C
import R7Fork.ZT5D2
import R7Fork.ZT5E
import R7Fork.ZT5F
import R7Fork.ZT5G
import R7Fork.ZT5H
import R7Fork.ZT6B

/-!
# TargetContract -- the FROZEN statement (r7).  Defines NOTHING new: `export` re-exports the r6/r7 headline `P428Genuine6` and its named variants.

Source of every name: `ZT5A` (namespace `AdalyFormal.StatementLaneG`).  Statement = CMP99b p.428 "C*Δ_kC is positive definite with a lower bound γ₀ > 0 independent of k and U" (r7: the
single regularity hypothesis is `ClassCoupled` = `CoversOm0p ∧ PerCubeRegular2` with ONE cube-factor binder).

Exported (all `Prop`s / implications; none is proved true — the lemma is NOT proved here):
* `P428Genuine6 ell M R hell a`     headline (side condition `M = ell^m`; `a₀,γ₀` independent of `k,Lu,α₀,S,Λ,U,B̃`; conclusion `InstIneq`)
* `P428Genuine6Print`               `γ₀` may depend on `Lu` (still not on `k,U`);               `P428Genuine6.toPrint : Genuine6 → Print`
* `P428Genuine6Both`                inequality over the both-endpoint class `OnLambda`;          `P428Genuine6.toBoth  : Genuine6 → Both`
* `P428Genuine6AllC`                every cube factor `c ≥ 10` (`a₀,γ₀` may depend on `c`);       `P428Genuine6AllC.toHead : AllC → Genuine6` (instantiate `c = 12`)
* `P428Target6Unif`                 `a₀,γ₀` uniform in `M,R` beyond thresholds;                    `P428Target6Unif.toTarget : Unif → Target6 (the ∀ell∀a∃m₀∀m∃R₀∀R Genuine6 form)`
* `P428Genuine6WD`                  conclusion includes invertibility `WellDefG` (`InstAtWD`);    `P428Genuine6WD.toHead : WD → Genuine6`
* `P428Target6`                     the outer quantification of the headline.
Consumer theorems (use the single-binder coupling): `ClassCoupled.plaq_gauge`, `ClassCoupled.plaqIn_gauge`, `CoercG6At.apply_gauge`, `P428Core6.apply_gauge`, `P428Genuine6.apply_gauge`,
`closedPt_consumes`, `closedPt_headline`, `closedPt_consumes_WD`.

## BINDER TABLE: who chooses each parameter (∀ = the adversary/consumer, ∃ = the prover supplies; "fixed" = pinned by the statement text)
`P428Target6` (outer): ∀ ell ≥ 2 | ∀ a > 0 | ∃ m₀ ≥ 1 (prover) | ∀ m ≥ m₀ (M = ell^m) | ∃ R₀ (prover) | ∀ R ≥ R₀ | then `P428Genuine6 ell (ell^m) R a`.
`P428Genuine6 ell M R hell a`: ell, M, R, a are parameters (the consumer's). Conjunct 1 `SidePow6`: 2 ≤ ell, M = ell^m (m ≥ 1), a > 0.
`P428Core6At .. c` (c = 12 FIXED by the headline; AllC variant: ∀ c ≥ 10 by consumer): ∃ a₀ > 0 (prover) | ∃ γ₀ > 0 (prover; both BEFORE k, Lu, α₀, S, Λ, U, B̃) |
   ∀ k ≥ 1 | ∀ Lu (unit torus extent) | ∀ α₀ > 0 with c·M·α₀ ≤ a₀ |  `CoercG6At`:
   TorusOK ell M Lu (hypothesis) | ∀ S : Tower (scaleUp ell k Lu) with Admissible ell M R k S | ∀ Λ with LambdaOK2 (touching rows, Λ = B(Λ'), RM-collar) | ∀ U : LinkCfg |
   `ClassCoupled ell M c k S α₀ ((ell)^k)⁻¹ U` (one hypothesis: CoversOm0p c ∧ PerCubeRegular2 c, SAME c; η = ell^-k FIXED) | conclusion `InstIneq`: ∀ B̃ on Λ̃, touching support:
   γ₀‖B̃‖² ≤ genForm(gparams ell k Lu hell S U a Λ)(C B̃).  (`a` is the mass parameter, fixed first.)
Variant `Print`: Lu is chosen BEFORE γ₀ (∃ a₀ ∀ Lu ∃ γ₀ ∀ k α₀ ...).  `Unif`: m₁, R₁, a₀, γ₀ chosen before m, R, k, Lu, α₀.
-/
set_option autoImplicit false

namespace TargetContract
export AdalyFormal.StatementLaneG (P428Genuine6 P428Genuine6Print P428Genuine6Both P428Genuine6AllC P428Target6Unif P428Genuine6WD P428Target6
  P428Core6 P428Core6At P428Core6WD P428Core6Applied CoercG6At CoercG6AtWD InstIneq InstAtWD)
end TargetContract

open AdalyFormal.StatementLaneG in
#print axioms P428Genuine6.toPrint
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine6.toBoth
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine6AllC.toHead
open AdalyFormal.StatementLaneG in
#print axioms P428Target6Unif.toTarget
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine6WD.toHead
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine6.apply_gauge
open AdalyFormal.StatementLaneG in
#print axioms closedPt_consumes
open AdalyFormal.StatementLaneG in
#print axioms closedPt_headline
open AdalyFormal.StatementLaneG in
#print axioms px1_not_P428Genuine6
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaq_gauge
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge
#print axioms AdalyFormal.StatementLaneG.CoercG6At.apply_gauge

-- exported definitions
#print axioms AdalyFormal.StatementLaneG.P428Genuine6
#print axioms AdalyFormal.StatementLaneG.P428Genuine6Print
#print axioms AdalyFormal.StatementLaneG.P428Genuine6Both
#print axioms AdalyFormal.StatementLaneG.P428Genuine6AllC
#print axioms AdalyFormal.StatementLaneG.P428Target6Unif
#print axioms AdalyFormal.StatementLaneG.P428Genuine6WD
#print axioms AdalyFormal.StatementLaneG.P428Target6
#print axioms AdalyFormal.StatementLaneG.P428Core6
#print axioms AdalyFormal.StatementLaneG.P428Core6At
#print axioms AdalyFormal.StatementLaneG.P428Core6WD
#print axioms AdalyFormal.StatementLaneG.P428Core6Applied
#print axioms AdalyFormal.StatementLaneG.CoercG6At
#print axioms AdalyFormal.StatementLaneG.CoercG6AtWD
#print axioms AdalyFormal.StatementLaneG.InstIneq
#print axioms AdalyFormal.StatementLaneG.InstAtWD
#print axioms AdalyFormal.StatementLane2.ClassCoupled
#print axioms AdalyFormal.StatementLaneG.P428Core6.apply_gauge
#print axioms AdalyFormal.StatementLaneG.closedPt_consumes_WD

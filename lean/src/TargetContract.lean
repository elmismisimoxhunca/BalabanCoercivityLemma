import ZT5A
import ZT5B
import ZT5C
import ZT5D2
import ZT5E
import ZT5F
import ZT5G
import ZT5H
import ZT6B
import ZR8Class
import R8URC

/-!
# TargetContract -- the FROZEN statement (r8).  Defines NOTHING new: `export` re-exports the headline `P428Genuine8` / `P428Target8` and its named variants.

Source of every name: `ZT5A` (namespace `AdalyFormal.StatementLaneG`).  Statement = CMP99b p.428 "C*Δ_kC is positive definite with a lower bound γ₀ > 0 independent of k and U".

**r8 CHANGE (statement defect 2026-10-12, `compute/u_reads_omega0_20261012`: the r7 headline `P428Target6` is FALSE as typed, `UR6.frozen_P428Target6_false`).**
The ONLY definitional change from r7: the jets of the printed averaging are defined PER COMPONENT (`ZLocJet`): `QlinStepL` (component `c` = Frechet derivative of
component `c`), `QlinCompL` (printed chain (3.15) of local steps), `C2StepL`/`C2CompL` (per-component second derivative + second-order chain rule); used by
`QlinB`, `D2B`, `C2rawB` (`ZXR2Sector`) and `Q1jet`, `C2tilde` (`ZXR2Unit1`).  r7 used `fderiv` of the whole-torus map, which one non-differentiable component
ANYWHERE turns into the junk `0`.  Bridges (every r7 result about the jets transfers on a regular tower): `QlinStepL_eq_QlinStepX`, `QlinCompL_eq_QlinCompX`,
`C2CompL_eq_C2CompX`, `QlinB_eq_r7`, `C2rawB_eq_r7`, `Q1jet_eq_r7`, `C2tilde_eq_r7`.  Headline names renamed `…6 → …8` (text otherwise as r7).

**LOCALITY (kernel theorems, `ZR8*`):** with `LocHyp ell M R k S Λ` (`Admissible`, `1 ≤ k`, `2 ≤ ell`, room `17·ell ≤ R·M`, `LambdaOK2`) and `U = U'` on every bond with
both endpoints in `Ω₀` -- equivalently (`classBond_iff_bothIn`, under `CoversOm0p` and `2 ≤ M`) on every class-constrained bond --
`genForm_congr_outside`, `genC_congr`, `WellDef_congr`, `WellDefG_congr`, `InstIneq_congr`, `InstAtWD_congr`, `InstIneq_congr_class`, `data_congr`, `G1inv_congr`,
`Tfull_congr` (`R D*`, the r6 "attack 1" argument; its own room is `2 ≤ R M`), `DpiFull_congr`.  The headline's `∃ R₀` makes the room condition automatic
(`R ≥ 17` and `M ≥ ell`); at `R·M < 17·ell` locality is NOT established here (not refuted either).
**UR control (`R8URC`):** at the UR lane's slab point (ell = 2, k = 1, M = 2, R = 18), `Ubad = cfg1 (−1)` (in the class: `ur_control_class`) gives the same
`genForm` value as `U = 1` for every `B̃` (`ur_control_genForm`), and `InstIneq`/`WellDefG` at `Ubad` ⇔ at `U = 1`.

Exported (all `Prop`s / implications; none is proved true — the lemma is NOT proved here):
* `P428Genuine8 ell M R hell a`     headline (side condition `M = ell^m`; `a₀,γ₀` independent of `k,Lu,α₀,S,Λ,U,B̃`; conclusion `InstIneq`)
* `P428Genuine8Print`               `γ₀` may depend on `Lu` (still not on `k,U`);               `P428Genuine8.toPrint : Genuine8 → Print`
* `P428Genuine8Both`                inequality over the both-endpoint class `OnLambda`;          `P428Genuine8.toBoth  : Genuine8 → Both`
* `P428Genuine8AllC`                every cube factor `c ≥ 10` (`a₀,γ₀` may depend on `c`);       `P428Genuine8AllC.toHead : AllC → Genuine8` (instantiate `c = 12`)
* `P428Target8Unif`                 `a₀,γ₀` uniform in `M,R` beyond thresholds;                    `P428Target8Unif.toTarget : Unif → Target8`
* `P428Genuine8WD`                  conclusion includes invertibility `WellDefG` (`InstAtWD`);    `P428Genuine8WD.toHead : WD → Genuine8`
* `P428Target8`                     the outer quantification of the headline.
Consumer theorems (use the single-binder coupling): `ClassCoupled.plaq_gauge`, `ClassCoupled.plaqIn_gauge`, `CoercG8At.apply_gauge`, `P428Core8.apply_gauge`, `P428Genuine8.apply_gauge`,
`closedPt_consumes`, `closedPt_headline`, `closedPt_consumes_WD`.

## BINDER TABLE: who chooses each parameter (∀ = the adversary/consumer, ∃ = the prover supplies; "fixed" = pinned by the statement text)
`P428Target8` (outer): ∀ ell ≥ 2 | ∀ a > 0 | ∃ m₀ ≥ 1 (prover) | ∀ m ≥ m₀ (M = ell^m) | ∃ R₀ (prover) | ∀ R ≥ R₀ | then `P428Genuine8 ell (ell^m) R a`.
`P428Genuine8 ell M R hell a`: ell, M, R, a are parameters (the consumer's). Conjunct 1 `SidePow6`: 2 ≤ ell, M = ell^m (m ≥ 1), a > 0.
`P428Core8At .. c` (c = 12 FIXED by the headline; AllC variant: ∀ c ≥ 10 by consumer): ∃ a₀ > 0 (prover) | ∃ γ₀ > 0 (prover; both BEFORE k, Lu, α₀, S, Λ, U, B̃) |
   ∀ k ≥ 1 | ∀ Lu (unit torus extent) | ∀ α₀ > 0 with c·M·α₀ ≤ a₀ |  `CoercG8At`:
   TorusOK ell M Lu (hypothesis) | ∀ S : Tower (scaleUp ell k Lu) with Admissible ell M R k S | ∀ Λ with LambdaOK2 (touching rows, Λ = B(Λ'), RM-collar) | ∀ U : LinkCfg |
   `ClassCoupled ell M c k S α₀ ((ell)^k)⁻¹ U` (one hypothesis: CoversOm0p c ∧ PerCubeRegular2 c, SAME c; η = ell^-k FIXED) | conclusion `InstIneq`: ∀ B̃ on Λ̃, touching support:
   γ₀‖B̃‖² ≤ genForm(gparams ell k Lu hell S U a Λ)(C B̃), every jet inside `genForm`/`C` the r8 LOCAL jet.  (`a` is the mass parameter, fixed first.)
Variant `Print`: Lu is chosen BEFORE γ₀ (∃ a₀ ∀ Lu ∃ γ₀ ∀ k α₀ ...).  `Unif`: m₁, R₁, a₀, γ₀ chosen before m, R, k, Lu, α₀.
-/
set_option autoImplicit false

namespace TargetContract
export AdalyFormal.StatementLaneG (P428Genuine8 P428Genuine8Print P428Genuine8Both P428Genuine8AllC P428Target8Unif P428Genuine8WD P428Target8
  P428Core8 P428Core8At P428Core8WD P428Core8Applied CoercG8At CoercG8AtWD InstIneq InstAtWD)
end TargetContract

open AdalyFormal.StatementLaneG in
#print axioms P428Genuine8.toPrint
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine8.toBoth
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine8AllC.toHead
open AdalyFormal.StatementLaneG in
#print axioms P428Target8Unif.toTarget
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine8WD.toHead
open AdalyFormal.StatementLaneG in
#print axioms P428Genuine8.apply_gauge
open AdalyFormal.StatementLaneG in
#print axioms closedPt_consumes
open AdalyFormal.StatementLaneG in
#print axioms closedPt_headline
open AdalyFormal.StatementLaneG in
#print axioms px1_not_P428Genuine8
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaq_gauge
#print axioms AdalyFormal.StatementLane2.ClassCoupled.plaqIn_gauge
#print axioms AdalyFormal.StatementLaneG.CoercG8At.apply_gauge

-- exported definitions
#print axioms AdalyFormal.StatementLaneG.P428Genuine8
#print axioms AdalyFormal.StatementLaneG.P428Genuine8Print
#print axioms AdalyFormal.StatementLaneG.P428Genuine8Both
#print axioms AdalyFormal.StatementLaneG.P428Genuine8AllC
#print axioms AdalyFormal.StatementLaneG.P428Target8Unif
#print axioms AdalyFormal.StatementLaneG.P428Genuine8WD
#print axioms AdalyFormal.StatementLaneG.P428Target8
#print axioms AdalyFormal.StatementLaneG.P428Core8
#print axioms AdalyFormal.StatementLaneG.P428Core8At
#print axioms AdalyFormal.StatementLaneG.P428Core8WD
#print axioms AdalyFormal.StatementLaneG.P428Core8Applied
#print axioms AdalyFormal.StatementLaneG.CoercG8At
#print axioms AdalyFormal.StatementLaneG.CoercG8AtWD
#print axioms AdalyFormal.StatementLaneG.InstIneq
#print axioms AdalyFormal.StatementLaneG.InstAtWD
#print axioms AdalyFormal.StatementLane2.ClassCoupled
#print axioms AdalyFormal.StatementLaneG.P428Core8.apply_gauge
#print axioms AdalyFormal.StatementLaneG.closedPt_consumes_WD

-- r8: the repair (bridges) and locality
#print axioms AdalyFormal.IngredientFamilyR2.QlinStepL_eq_QlinStepX
#print axioms AdalyFormal.IngredientFamilyR2.QlinCompL_eq_QlinCompX
#print axioms AdalyFormal.IngredientFamilyR2.C2CompL_eq_C2CompX
#print axioms AdalyFormal.IngredientFamilyR2.QlinB_eq_r7
#print axioms AdalyFormal.IngredientFamilyR2.C2rawB_eq_r7
#print axioms AdalyFormal.IngredientFamilyR2.Q1jet_eq_r7
#print axioms AdalyFormal.IngredientFamilyR2.C2tilde_eq_r7
#print axioms AdalyFormal.StatementLaneR8.Tfull_congr
#print axioms AdalyFormal.StatementLaneR8.DpiFull_congr
#print axioms AdalyFormal.StatementLaneR8.data_congr
#print axioms AdalyFormal.StatementLaneR8.G1inv_congr
#print axioms AdalyFormal.StatementLaneR8.genC_congr
#print axioms AdalyFormal.StatementLaneR8.genForm_congr_outside
#print axioms AdalyFormal.StatementLaneR8.WellDef_congr
#print axioms AdalyFormal.StatementLaneR8.WellDefG_congr
#print axioms AdalyFormal.StatementLaneR8.InstIneq_congr
#print axioms AdalyFormal.StatementLaneR8.InstAtWD_congr
#print axioms AdalyFormal.StatementLaneR8.classBond_iff_bothIn
#print axioms AdalyFormal.StatementLaneR8.InstIneq_congr_class
#print axioms AdalyFormal.URLocalityR8.ur_control_genForm
#print axioms AdalyFormal.URLocalityR8.ur_control_instIneq
#print axioms AdalyFormal.URLocalityR8.ur_control_wellDefG
#print axioms AdalyFormal.URLocalityR8.ur_control_class
-- helper congruences cited in REPORT.md
#print axioms AdalyFormal.StatementLaneR8.Cop_congr_rows
#print axioms AdalyFormal.StatementLaneR8.H0_congr_rows
#print axioms AdalyFormal.StatementLaneR8.hLift_congr_rows
#print axioms AdalyFormal.StatementLaneR8.Gp_congr
#print axioms AdalyFormal.StatementLaneR8.NQp_congr
#print axioms AdalyFormal.StatementLaneR8.Qpa_congr
#print axioms AdalyFormal.StatementLaneR8.RImage_congr
#print axioms AdalyFormal.IngredientFamilyR2.QlinB_zero

/-
L5 PROOF — pays the ORIGINAL immutable
`AdalySI1.C1Contract.L5FarPathBridgeTarget` from read-only `deps/C1Target.lean`.
Owned directory: compute/m1_si1_l5_gated/build0/.

The exported theorem `AdalySI1.L5Proof.far_path_bridge` has EXACTLY the target's
type: arbitrary `L`, `ell`, fine edge `c`, explicit coarse alignment `hcell`,
positivity `0 < ell`, per-coordinate divisibility `∀ μ, ell ∣ (L μ + 1)`, every
actual site `x ∈ stepBlockOf c.1 1 ell`, and the target's own literal
`c' : CoarseBond L (1 * ell)`.  The concluded equality is the target's ordered
`List (Fin 3)` equality of `coarseGammaPath 1` staircase values — segment
multiplicities AND the `2,1,0` order — with periodic wrapping handled inside
`Fin (L ν + 1)` arithmetic.  It is NOT an endpoint, holonomy, line-integral,
or partner-bijection statement, and no path is redefined.

Proof route (compute/m1_si1_c3_gated/audit/NEXT.md §3):
1. `pathSite_sub_pathSite_eq`: shifting BOTH endpoints of a coordinate
   `Fin`-difference by the SAME `pathSite` translation leaves the difference
   unchanged, proved in `Fin (L ν + 1)` (moved coordinate: induction on the
   shift count + additive cancellation; transverse coordinate:
   `ReparamCDisjoint.pathSite_apply_ne` with its actual `ν ≠ μ₀` orientation).
2. `coarseGammaPath_one_cPlus_partner_eq_cMinus`: unfold only
   `OneStep124.cPlus`, `OneStep124.partner`, `coarseGammaPath`,
   `coarseStraightSegment`, `coarseCoordSteps`; simplify the transverse
   `Function.update` reads via `2 ≠ 1`, `2 ≠ 0`, `1 ≠ 0`; rewrite the three
   modular differences with step 1.  The `List.replicate` lengths then agree,
   so the ordered append trees are identical.
3. `far_path_bridge` introduces every target premise verbatim and instantiates
   step 2 at the target's literal `c'`; `c'.1.1 = c.1` holds definitionally.

The historical repaired partial
`compute/m1_si1_l18/audit/L5FarTreeAudit.lean` (source SHA-256
`8b0ed795801f4920898d1db9fd7401a35dc2f31ca69c6a77e3c2d7f406a3794d`, exit 0,
standard-only axioms) was INSPECTED and its two helper arguments are
re-derived here against this stage's pinned read-only deps; the historical
file itself is not on this runner's import path and is not imported.
-/
import C1Target
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 1000

namespace AdalySI1.L5Proof

open AdalyFormal.Target.ClayStatement (PeriodicLatticeExtent PeriodicLatticeSite)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath coarseStraightSegment coarseCoordSteps)
open AdalyFormal.Balaban.QOne (pathSite pathSite_zero pathSite_succ)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_ne)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)

variable {L : PeriodicLatticeExtent}

/-- Shifting both endpoints of a coordinate `Fin`-difference by the SAME `pathSite`
translation (one coordinate direction `μ₀`, `k` steps) leaves every coordinatewise
difference unchanged.  The moved-coordinate case is induction on `k` with
`add_sub_add_right_eq_sub` cancellation in `Fin (L ν + 1)`, so periodic wraparound
is handled by the existing periodic arithmetic — no no-wrap Nat assumption; the
transverse case is `pathSite_apply_ne` with its real `ν ≠ μ₀` hypothesis. -/
theorem pathSite_sub_pathSite_eq (y x : PeriodicLatticeSite L) (μ₀ : Fin 3) (k : ℕ) (ν : Fin 3) :
    (pathSite x μ₀ k) ν - (pathSite y μ₀ k) ν = x ν - y ν := by
  by_cases hν : ν = μ₀
  · subst hν
    induction k with
    | zero => simp [pathSite_zero]
    | succ k ih =>
        rw [pathSite_succ, pathSite_succ]
        show (Function.update (pathSite x ν k) ν ((pathSite x ν k) ν + 1)) ν
              - (Function.update (pathSite y ν k) ν ((pathSite y ν k) ν + 1)) ν = x ν - y ν
        rw [Function.update_self, Function.update_self, add_sub_add_right_eq_sub]
        exact ih
  · rw [pathSite_apply_ne x μ₀ ν k hν, pathSite_apply_ne y μ₀ ν k hν]

/-- **L5 helper, equality (i): far-tree translation into the blocked frame.**  At
stride `1`, `coarseGammaPath` based at `OneStep124.cPlus c` running to
`OneStep124.partner c x` is the SAME ordered direction list as `coarseGammaPath`
based at `c.1.1` running to `x`.  Unconditional in `c : CoarseBond L (1 * m)`,
`x`, and `m`: no positivity, divisibility, partner-bijection, or `stepBlockOf`
hypothesis is needed for the LIST equality itself (those stay on the exported
target below for the downstream fitted source application). -/
theorem coarseGammaPath_one_cPlus_partner_eq_cMinus (m : ℕ)
    (c : CoarseBond L (1 * m)) (x : PeriodicLatticeSite L) :
    coarseGammaPath 1 (OneStep124.cPlus c) (OneStep124.partner c x)
      = coarseGammaPath 1 c.1.1 x := by
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  unfold OneStep124.cPlus OneStep124.partner
  unfold coarseGammaPath coarseStraightSegment coarseCoordSteps
  simp only [Function.update_of_ne h21.symm, Function.update_of_ne h20.symm,
    Function.update_of_ne h10.symm,
    pathSite_sub_pathSite_eq c.1.1 x c.2 (m * 1) 2,
    pathSite_sub_pathSite_eq c.1.1 x c.2 (m * 1) 1,
    pathSite_sub_pathSite_eq c.1.1 x c.2 (m * 1) 0]

/-- **THE L5 PAYMENT.**  Inhabitant of the ORIGINAL immutable
`AdalySI1.C1Contract.L5FarPathBridgeTarget`, with every quantifier, direction,
arbitrary extent, positivity, coarse-alignment, per-coordinate divisibility, and
actual `stepBlockOf` premise retained verbatim.  The goal's own literal
`c' : CoarseBond L (1 * ell)` is introduced (not re-typed), the unconditional
helper is instantiated at `m := ell`, `c := c'`, `x := x`, and `c'.1.1` reduces
definitionally to `c.1`, closing the ordered `List (Fin 3)` equality. -/
theorem far_path_bridge : AdalySI1.C1Contract.L5FarPathBridgeTarget := by
  intro L ell c hcell hell hdvd x hx c'
  exact coarseGammaPath_one_cPlus_partner_eq_cMinus ell c' x

#print axioms pathSite_sub_pathSite_eq
#print axioms coarseGammaPath_one_cPlus_partner_eq_cMinus
#print axioms far_path_bridge

run_cmd do
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  for name in [`AdalySI1.L5Proof.pathSite_sub_pathSite_eq,
      `AdalySI1.L5Proof.coarseGammaPath_one_cPlus_partner_eq_cMinus,
      `AdalySI1.L5Proof.far_path_bridge] do
    unless (← Lean.getEnv).contains name do
      throwError "Missing L5 proof declaration: {name}"
    for ax in (← Lean.collectAxioms name) do
      unless allowed.contains ax do
        throwError "L5 proof rejected nonstandard axiom in {name}: {ax}"
  Lean.logInfo "L5_PROOF_ORIGINAL_TARGET_STANDARD_AXIOMS_PASS"

end AdalySI1.L5Proof

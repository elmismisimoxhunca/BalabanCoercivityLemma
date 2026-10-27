/-
Owned SI1 noloop file (compute/m1_si1_noloop/prod/). Imports the frozen `AdalyFormal` package
read-only, plus READ-ONLY hash-verified copies of seven `compute/m1_si1_long/` files (copied into
`prod/deps/` only for `LEAN_PATH` visibility; source hashes checked against
`compute/m1_si1_long/audit/CERTIFICATE_INVENTORY.md`'s live hashes: IngredientDeriv `518a0c11…`,
SI1Assemble `1c9e41cc…`, SI1AssembleDeriv `2f42a3c2…`, ModifiedAverageDeriv `767f9f97…`,
EndpointAvgDeriv `37737850…`, RawAverageDeriv `930e4938…`, ProdAssembleDeriv `06cc3ee0…`; `.olean`
copies taken from `compute/m1_si1_phi2/prod/deps/`'s own already independently-replayed tranche,
themselves hash-verified against the same inventory). None of these seven files is edited. Also
imports THIS SAME workflow's own already-compiled `compute/m1_si1_noloop/phi/RawUbarDerivNoLoop.lean`
(`hasDerivAt_ubarSU2_coe_configMul_noloop`, READY) and, transitively, `NonzeroExpDeriv.lean`, both
reached via `phi/deps`/`phi/attempt4`/`phi/` extra `LEAN_PATH` roots — neither copied nor edited.

## TARGET

Differentiate CMP98 (89)/(63)'s FOUR-FACTOR product `modifiedAverage V0 ell V1 c` at `t = 0` along
`V1 = fun e => su2Exp (t • A e)`, for a GENERALLY NONIDENTITY background `V0`, reusing THIS
workflow's `phi/RawUbarDerivNoLoop.lean` raw-ratio derivative in place of the SUPERSEDED
`compute/m1_si1_phi2/phi/RawUbarDeriv.lean` one. Launch charge for this stage: rebuild
`compute/m1_si1_phi2/prod/ProdFullAssembleDeriv.lean`'s assembly dropping the illegal `hnc1`
(nonanchor loop ≠ 1) hypothesis that `compute/m1_si1_phi2/audit/RESULT.md` found source-false (a
fitted period-4, block-2 nonanchor loop is identically `1` for every background) — identity loops
are now allowed everywhere in the raw-ratio factor's block sum; only the single per-point
`≠ su2NegOne` (`-I` principal-log-chart cut) hypothesis, quantified over the FULL
`stepBlockOf c.1 1 ell` (no `.erase c.1`), survives, exactly matching
`phi/RawUbarDerivNoLoop.lean`'s own `hnc2`.

## Route: reuse only, IDENTICAL product-rule assembly to the superseded prod stage

Same Leibniz-rule assembly as `compute/m1_si1_phi2/prod/ProdFullAssembleDeriv.lean`
(`hABD := (hA.mul hBC).mul hD`, chained through `HasDerivAt.mul`/`.const_mul`/`.mul_const`),
bridged to the closed form via the same `hcongr`/`simp`-only-on-fixed-`M2`-terms discipline, which
avoids the ambient-Matrix-instance diamond that file's own docstring documents (never re-state the
intermediate `HasDerivAt` goal; let its type flow entirely from the combinator application). The
ONLY substantive changes from that file:

1. `hB` is now `hasDerivAt_ubarSU2_coe_configMul_noloop V0 A hah htr ell c hnc2` — no `hnc1`
   argument (removed entirely, matching the launch charge), and no `hell : 0 < ell` argument either
   (the noloop theorem needs neither, so this stage's own theorem drops `hell` too — an unused
   hypothesis would not match this tree's discipline of stating exactly what is needed).
2. The stated closed form's raw-ratio term uses `RawUbarDerivNoLoop.ubarBracket` and sums over the
   FULL `stepBlockOf c.1 1 ell` rather than `.erase c.1`, matching
   `hasDerivAt_ubarSU2_coe_configMul_noloop`'s own conclusion verbatim.

No new differentiability analysis is derived here: every atomic derivative fact
(`hasDerivAt_endpointAvg_inv_coe`, `hasDerivAt_ubarSU2_coe_configMul_noloop`,
`hasDerivAt_endpointAvg_coe`) is reused exactly as compiled; only the product-rule combinators and
the value-level bridge (`groupConj_const_eq`/`coe_mul`/`coe_inv`, then the `t = 0` collapse via
`modifiedAverage_trivialU`'s own ingredients — `endpointAvg_trivialU_right`,
`configMul_trivialU_left`, and background unitarity `hKK`) assemble them. The `t = 0` collapse
argument is IDENTICAL to the superseded file's: it depends only on the FUNCTION VALUES of the three
factors at `t = 0` collapsing to `1`/cancelling by unitarity, never on which set the raw-ratio
factor's DERIVATIVE sums over — so it carries over unchanged despite the `hnc1`/erase-vs-full swap.
-/
import ModifiedAverageDeriv
import EndpointAvgDeriv
import ProdAssembleDeriv
import RawUbarDerivNoLoop

set_option autoImplicit false

open Matrix
attribute [local instance 10000] Matrix.linftyOpNormedRing
attribute [local instance 10000] Matrix.linftyOpNormedAlgebra

namespace AdalySI1Noloop.ProdAssemble

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2NegOne su2Exp_zero su2Log_one
  coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2)
open AdalyFormal.Balaban.UbarTowerCov (loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalySI1.ModifiedAverageDeriv (endpointAvg modifiedAverage configMul cPlus groupConj)
open AdalySI1.EndpointAvgDeriv (hasDerivAt_endpointAvg_coe)
open AdalySI1.ProdAssembleDeriv (hasDerivAt_endpointAvg_inv_coe groupConj_const_eq)
open AdalySI1.RawUbarDerivNoLoop (hasDerivAt_ubarSU2_coe_configMul_noloop)

variable {L : PeriodicLatticeExtent}

/-- **CMP98 (89)/(63)'s full modified-average product rule, over identity-loops-allowed
raw ratio.** Differentiates the actual four-factor `modifiedAverage V0 ell V1 c` at `t = 0` along
`V1 = fun e => su2Exp (t • A e)`, for an arbitrary (generally nonidentity) background `V0` and
arbitrary traceless anti-Hermitian direction `A` — the `compute/m1_si1_noloop` stage's version of
`compute/m1_si1_phi2/prod/ProdFullAssembleDeriv.lean`'s
`hasDerivAt_modifiedAverage_coe_configMul`, rebuilt on the identity-loops-allowed raw ratio
(`phi/RawUbarDerivNoLoop.lean`'s single `hnc2`, no `hnc1`). The derivative slot is left `_`-shaped
in structure only insofar as it is exactly whatever `HasDerivAt.mul`/`.const_mul`/`.mul_const`
compose to from the three already-compiled ingredient derivatives, not a hand-retyped formula. -/
theorem hasDerivAt_modifiedAverage_coe_configMul_noloop
    (V0 : PeriodicLinkConfiguration SU2 L)
    (A : PeriodicLatticeEdge L → M2) (hah : ∀ e, (A e)ᴴ = -(A e))
    (htr : ∀ e, Matrix.trace (A e) = 0) (ell : ℕ) (c : PeriodicLatticeEdge L)
    (hnc2 : ∀ x ∈ stepBlockOf c.1 1 ell, loopVar 1 ell V0 c x ≠ su2NegOne) :
    HasDerivAt (fun t : ℝ => ((modifiedAverage V0 ell (fun e => su2Exp (t • A e)) c : SU2) : M2))
      ((∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf c.1 ell,
            ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A c.1
              (AdalyFormal.Balaban.Q1Real.GammaPath c.1 x) 1)ᴴ
        + ((fderiv ℝ NormedSpace.exp (AdalySI1.RawUbarDerivNoLoop.ubarBracket V0 ell c))
              (∑ x ∈ stepBlockOf c.1 1 ell, ((ell : ℝ) ^ 3)⁻¹ •
                deriv (fun t : ℝ =>
                  su2Log (loopVar 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c x)) 0)
              * ((AdalyFormal.Balaban.UbarTowerCov.coarseBondVar 1 ell V0 c : SU2) : M2)
            + ((su2Exp (AdalySI1.RawUbarDerivNoLoop.ubarBracket V0 ell c) : SU2) : M2)
              * AdalySI1.RawAverageDeriv.holonomyDirDeriv V0 A 1 c.1 (List.replicate ell c.2))
          * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ
        + ((ubarSU2 1 ell V0 c : SU2) : M2)
          * (∑ x ∈ AdalyFormal.Balaban.AdmissibleSubspace.blockOf (cPlus ell c) ell,
              ((ell : ℚ) ^ 3)⁻¹ • AdalySI1.IngredientDeriv.dirDeriv V0 A (cPlus ell c)
                (AdalyFormal.Balaban.Q1Real.GammaPath (cPlus ell c) x) 1)
          * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ) 0 := by
  have hA := hasDerivAt_endpointAvg_inv_coe V0 ell A hah htr c.1
  have hB := hasDerivAt_ubarSU2_coe_configMul_noloop V0 A hah htr ell c hnc2
  have hE2 := hasDerivAt_endpointAvg_coe V0 ell A hah htr (cPlus ell c)
  have hBC := hB.mul_const (((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ)
  have hD := (hE2.const_mul ((ubarSU2 1 ell V0 c : SU2) : M2)).mul_const
    (((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ)
  have hABD := (hA.mul hBC).mul hD
  have hval : (fun t : ℝ => ((modifiedAverage V0 ell (fun e => su2Exp (t • A e)) c : SU2) : M2))
      = fun t => ((((endpointAvg V0 (fun e => su2Exp (t • A e)) ell c.1 : SU2) : M2))ᴴ
          * (((ubarSU2 1 ell (configMul (fun e => su2Exp (t • A e)) V0) c : SU2) : M2)
              * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ))
          * (((ubarSU2 1 ell V0 c : SU2) : M2)
              * ((endpointAvg V0 (fun e => su2Exp (t • A e)) ell (cPlus ell c) : SU2) : M2)
              * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ) := by
    funext t
    show ((modifiedAverage V0 ell (fun e => su2Exp (t • A e)) c : SU2) : M2) = _
    unfold modifiedAverage
    simp only [coe_mul, coe_inv, groupConj_const_eq]
  rw [hval]
  have hzero : (fun e => su2Exp ((0 : ℝ) • A e)) = AdalyFormal.Balaban.CovariantHjMinimizer.trivialU L := by
    funext e; show su2Exp ((0 : ℝ) • A e) = 1
    rw [zero_smul, su2Exp_zero]
  have hKK : ((ubarSU2 1 ell V0 c : SU2) : M2) * ((ubarSU2 1 ell V0 c : SU2) : M2)ᴴ = 1 := by
    have hg : (ubarSU2 1 ell V0 c) * (ubarSU2 1 ell V0 c)⁻¹ = 1 := mul_inv_cancel _
    rw [← coe_inv, ← coe_mul, hg, coe_one]
  have hcongr : ∀ {f : ℝ → M2} {d1 d2 : M2}, d1 = d2 → HasDerivAt f d1 0 → HasDerivAt f d2 0 :=
    fun heq hd => heq ▸ hd
  exact hcongr (by
    simp only [Pi.mul_apply, hzero, AdalySI1.ModifiedAverageDeriv.endpointAvg_trivialU_right,
      AdalySI1.ModifiedAverageDeriv.configMul_trivialU_left, coe_one,
      Matrix.conjTranspose_one, hKK, one_mul, mul_one, mul_add, add_mul]) hABD

#print axioms hasDerivAt_modifiedAverage_coe_configMul_noloop

end AdalySI1Noloop.ProdAssemble

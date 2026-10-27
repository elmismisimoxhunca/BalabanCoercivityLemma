import R7Fork.ZT5E

/-!
# ZT5F -- (8) the goodFam / junk-family exclusion re-run at `k ≥ 1`.

`FormPinned` (ZXG3D1): an ingredient family `I` has THE genuine (3.156) form at every tiled point where the genuine construction is well defined.  r4's
`not_FormPinned_goodFam` refuted this for the junk family `goodFam` at the `k = 0` closed point.  Here the same refutation at EVERY `k ≥ 0` (in particular `k ≥ 1`,
the printed range) via the constant mode: `genForm = 0` on `Bconst` (GU1M, full tower, flat) while the junk form is `≥ ‖B‖² > 0`.
The r5 statement `P428Genuine6` has NO ingredient-family binder: its conclusion is stated about `gparams`/`GenP.genForm`/`GenP.genC` (type-level, `ZT5A`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 8000000

namespace AdalyFormal.StatementLaneG

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem not_FormPinned_goodFam_k (ell : ℕ) (hell2 : 2 ≤ ell) (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ¬ FormPinned (by omega : 0 < ell) a (goodFam ell (by omega : 0 < ell)) := by
  intro hP
  have hell : 0 < ell := by omega
  have hdvd := Ltile_dvd ell hell
  have hN : ∀ μ, 1 ≤ Ltile ell μ := by intro μ; simp only [Ltile]; omega
  set B : BondFnL2 (Ltile ell) := AdalyFormal.GenuineU1.Bconst (Ltile ell) (fun _ => suTwoWitness) with hBdef
  have hW : GenP.WellDef (gparams ell k (Ltile ell) hell (fullTower ell k (Ltile ell)) flatCfg a Set.univ) :=
    AdalyFormal.GenuineU1.PK_wellDef ell k (Ltile ell) hell a Set.univ hN hdvd ha
  have hpin := hP k (Ltile ell) hdvd (fullTower ell k (Ltile ell)) flatCfg Set.univ hW B
  have hge := AdalyFormal.StatementLane3.goodIngr'_form_ge ell hell k (Ltile ell) flatCfg hdvd Set.univ B
  have hgood : goodFam ell hell k (Ltile ell) (fullTower ell k (Ltile ell)) flatCfg Set.univ =
      goodIngr' ell hell k (Ltile ell) flatCfg hdvd Set.univ :=
    goodFam_eq ell hell k (Ltile ell) hdvd _ _ _
  rw [hgood] at hpin
  have hgen : GenP.genForm (gparams ell k (Ltile ell) hell (fullTower ell k (Ltile ell)) flatCfg a Set.univ) B = 0 :=
    AdalyFormal.GenuineU1.genForm_const_zero ell k (Ltile ell) hell a Set.univ hN ha (fun _ => suTwoWitness)
  rw [hgen] at hpin
  rw [hpin] at hge
  have hB0 : B ≠ 0 := by
    intro h
    let e : Bond (Ltile ell) := ((fun _ => ⟨0, by simp only [Ltile]; omega⟩ : PeriodicLatticeSite (Ltile ell)), (0 : Fin 3))
    have := congrArg (fun z : BondFnL2 (Ltile ell) => z.ofLp e) h
    simp [hBdef, AdalyFormal.GenuineU1.Bconst] at this
    exact suTwoWitness_ne_zero this
  have hpos : 0 < ‖B‖ ^ 2 := by have := norm_pos_iff.mpr hB0; positivity
  have hge' : ‖B‖ ^ 2 ≤ 0 := hge
  linarith

#print axioms not_FormPinned_goodFam_k

end AdalyFormal.StatementLaneG

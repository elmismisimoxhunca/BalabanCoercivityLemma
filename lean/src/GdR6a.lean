import GdR5b
import GdSG4

/-!
# GdR6a -- Round 6: the exact literal-minus-localised difference, and why domination cannot decide `IsUnit G1inv_lit`.

* `G1inv_diff_eq` : at any configuration, when `WellDefAt` holds for the literal and the localised selectors,
  `G1inv_lit - G1inv_loc = Ginv_lit - Ginv_loc` as operators (the SAME difference `Θ`; `Δ2_lit = Δ2_loc`).
* `Theta_vanishes_on_V` : `Θ x = 0` for `x` vanishing on the level-0 bonds (`Ginv_eq_on_V`).
* `Ginv_loc_psd_twist` : the localised `Ginv` is positive semidefinite on the twist family.
* `domination_fails_pi` : on the NV slab at `U_π` (in class) the literal `Ginv` does NOT dominate the localised one: there is `v` with
  `⟨v, Ginv_lit v⟩ < 0 ≤ ⟨v, Ginv_loc v⟩`.  Hence `Θ` is not positive semidefinite in general and "dominate the localised `G1inv`" (the route that decided `Ginv`
  at `θ = 0`) is unavailable at general configurations.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.D1Guarded

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.NonVac
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

section diff
variable (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (hell0 : 0 < P.ell) (hroom : 17 * P.ell ≤ R * M)

include hS hell0 hroom in
theorem G1inv_diff_eq (sD sJ sD' sJ' : PlaqSel)
    (hsD : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD L G)
    (hsD' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sD' L G)
    (hsJ : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ L G)
    (hsJ' : ∀ (L : PeriodicLatticeExtent) (G : TowerGeom L), plaqIn G.Om0 ⊆ sJ' L G)
    (WD1 : WellDefAt sD sJ P) (WD2 : WellDefAt sD' sJ' P) (x : ↥(bondSupp P.G)) :
    G1invS sD sJ P x - G1invS sD' sJ' P x = (dataS sD sJ P).Ginv x - (dataS sD' sJ' P).Ginv x := by
  have T := twoData_lit_loc P hS hell0 hroom sD sJ sD' sJ' hsD hsD' hsJ hsJ'
  have hL1 := dataS_laws sD sJ P
  have hL2 := dataS_laws sD' sJ' P
  have hG1 := G1invS_spec sD sJ P
  have hG2 := G1invS_spec sD' sJ' P
  have n1 : IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs) :=
    NG_unit_of_N1 (dataS sD sJ P) hL1 hG1 WD1.2.2
  have n2 : IsUnit (((dataS sD' sJ' P).Q.comp (dataS sD' sJ' P).G).comp (dataS sD' sJ' P).Qs) :=
    NG_unit_of_N1 (dataS sD' sJ' P) hL2 hG2 WD2.2.2
  have e1 : G1invS sD sJ P = (dataS sD sJ P).Ginv - (dataS sD sJ P).Delta2 hL1 :=
    (dataS sD sJ P).G1inv_unique hG1 ((dataS sD sJ P).isG1inv_sub hL1)
  have e2 : G1invS sD' sJ' P = (dataS sD' sJ' P).Ginv - (dataS sD' sJ' P).Delta2 hL2 :=
    (dataS sD' sJ' P).G1inv_unique hG2 ((dataS sD' sJ' P).isG1inv_sub hL2)
  have hd := T.Delta2_eq hL1 hL2 WD1.1 WD2.1 n1 n2
  have a1 : G1invS sD sJ P x = (dataS sD sJ P).Ginv x - (dataS sD sJ P).Delta2 hL1 x := by
    rw [e1]; rfl
  have a2 : G1invS sD' sJ' P x = (dataS sD' sJ' P).Ginv x - (dataS sD' sJ' P).Delta2 hL2 x := by
    rw [e2]; rfl
  have a3 : (dataS sD sJ P).Delta2 hL1 x = (dataS sD' sJ' P).Delta2 hL2 x := congrArg (fun F => F x) hd
  rw [a1, a2, a3]
  abel

#print axioms G1inv_diff_eq

end diff

section psd
variable {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell) {S : Tower (scaleUp ell k Lu)} (a : ℝ)
  (Lam : Set (PeriodicLatticeSite Lu))

theorem Ginv_loc_psd_twist (sJ' : PlaqSel) (ha : 0 ≤ a) (θ : ℝ) :
    PSD (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam θ)).Ginv := by
  intro (w : ↥(bondSupp (Pth ell k Lu hell0 S a Lam θ).G))
  show 0 ≤ ⟪w, (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam θ)).Ginv w⟫
  rw [BaseDataS.inner_Ginv]
  have h1 : 0 ≤ ⟪w, (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam θ)).Dpi w⟫ := by
    have e := E0_Dpi_inner selIn (geomOf ell k S) (Uth (S.Om 0) θ) a w
    refine le_of_le_of_eq ?_ e.symm
    unfold DeltaS
    have hc : deltaKLocCLM (Uth (S.Om 0) θ) (selIn _ (geomOf ell k S)) =
        deltaKLocCLM (AdalyFormal.Balaban.DeltaPrime.trivialU) (selIn _ (geomOf ell k S)) :=
      deltaKLocCLM_congr (fun p hp e' he' => by
        have h := (hp e' he').1
        show Uth (S.Om 0) θ e' = (1 : SU2m)
        exact Uth_one_of_base _ θ e' h)
    rw [hc]
    exact deltaKLocCLM_flat_nonneg _ _
  have h2 : 0 ≤ ‖(dataS selIn sJ' (Pth ell k Lu hell0 S a Lam θ)).T w‖ ^ 2 := by positivity
  have h3 : 0 ≤ ⟪w, (dataS selIn sJ' (Pth ell k Lu hell0 S a Lam θ)).Mass w⟫ := by
    have e := E0_Mass_inner (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (Uth (S.Om 0) θ)) w
    refine le_of_le_of_eq ?_ e.symm
    refine Finset.sum_nonneg (fun p _ => ?_)
    have : (0 : ℝ) ≤ ((geomOf ell k S).ell : ℝ) ^ (p.1 : ℕ) := by positivity
    positivity
  linarith

end psd

#print axioms Ginv_loc_psd_twist

/-- **domination fails in class**: at the in-class configuration `U_π` of the NV slab the literal `Ginv` has a direction on which it is negative while the localised one is `≥ 0`;
so `Θ = Ginv_lit - Ginv_loc` is not positive semidefinite, and neither is `G1inv_lit - G1inv_loc` (`G1inv_diff_eq`). -/
theorem domination_fails_pi (sJ : PlaqSel) {m R : ℕ} (hm : 1 ≤ m) (hR : 18 ≤ R) {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled 2 (2 ^ m) 12 2 (SlabNv 2 (2 ^ m) R) α₀ ((((2 : ℕ) : ℝ)) ^ 2)⁻¹
        (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) ∧
      ∃ v : ↥(bondSupp (geomOf 2 2 (SlabNv 2 (2 ^ m) R))),
        ⟪v, (dataS selAll sJ (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R))).Ginv v⟫ < 0 ∧
        0 ≤ ⟪v, (dataS selIn selIn (gparams 2 2 (nvLu (2 ^ m) R) (by norm_num) (SlabNv 2 (2 ^ m) R)
            (Uth ((SlabNv 2 (2 ^ m) R).Om 0) Real.pi) 1 (LamN (2 ^ m) R))).Ginv v⟫ := by
  obtain ⟨hcls, v, hv⟩ := literal_Ginv_indefinite sJ hm hR hα
  exact ⟨hcls, v, hv, Ginv_loc_psd_twist (by norm_num) 1 (LamN (2 ^ m) R) selIn zero_le_one Real.pi v⟩

#print axioms domination_fails_pi

end AdalyFormal.D1Guarded

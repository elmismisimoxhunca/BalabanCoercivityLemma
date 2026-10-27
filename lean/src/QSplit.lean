import QCircle
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_one)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.DeltaKR85
open HConstruction.SmallNF
open HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open OneStep124

 theorem rot_one_assemble (x a z : ℝ) : RMap (rotElem 1) (assemble x a z) = assemble (-x) a (-z) := by
  convert RMap_rot_assemble 1 x a z using 1 <;> norm_num [rotA, rotB]

 theorem fixed_axis (X : SuTwo) (h : RMap (rotElem 1) X = X) : X = axisCoord X • pauliE2 := by
  have he := h
  rw [← assemble_coordinates X, rot_one_assemble] at he
  have hx := congrArg (fun Y => (transverseCoord Y).re) he
  have hz := congrArg (fun Y => (transverseCoord Y).im) he
  simp only [transverseCoord_assemble] at hx hz
  have hx0 : (transverseCoord X).re = 0 := by linarith
  have hz0 : (transverseCoord X).im = 0 := by linarith
  have hE := assemble_coordinates X
  rw [hx0, hz0] at hE
  simpa [assemble] using hE.symm

 theorem kills_fixed {T : SuTwo →L[ℝ] SuTwo} (hT : T pauliE2 = 0) (X : SuTwo)
    (h : RMap (rotElem 1) X = X) : T X = 0 := by
  rw [fixed_axis X h, map_smul, hT, smul_zero]

 theorem line_axis_fixed (a : CoarseBond witnessL 1 → ℝ)
    (y : PeriodicLatticeSite witnessL) (p : List (Fin 3)) :
    RMap (rotElem 1) (lineIntegral 1 chosenU (fun b => a b • pauliE2) y p) =
      lineIntegral 1 chosenU (fun b => a b • pauliE2) y p := by
  rw [← line_circle]
  simp only [RMap_rot_axis]

 theorem chosen_RMap_axis (e : PeriodicLatticeEdge witnessL) (a : ℝ) :
    RMap (chosenU e) (a • pauliE2) = a • pauliE2 := by
  by_cases he : e = (AdalyFormal.Balaban.AdmissibleSubspace.witnessY, (0 : Fin 3))
  · subst e
    change RMap (nonflatU (1/16) _) _ = _
    rw [nonflatU_at_x_mu, RMap_rot_axis]
  · change RMap (nonflatU (1/16) e) _ = _
    rw [nonflatU_elsewhere _ he, RMap_one]; rfl

 theorem path_RMap_axis (y : PeriodicLatticeSite witnessL) (p : List (Fin 3)) (a : ℝ) :
    RMap (coarsePathHolonomy 1 chosenU y p) (a • pauliE2) = a • pauliE2 := by
  induction p generalizing y with
  | nil => rw [coarsePathHolonomy, RMap_one]; rfl
  | cons d p ih =>
    change RMap (chosenU (y,d) * coarsePathHolonomy 1 chosenU _ p) _ = _
    rw [← AdalyFormal.Balaban.CovariantOperators.RMap_mul_apply, ih, chosen_RMap_axis]

 theorem q124Principal_axis_main (a : CoarseBond witnessL 1 → ℝ)
    (c : CoarseBond witnessL (1*2)) :
    q124Principal 1 2 chosenU (fun b => a b • pauliE2) c =
      unitToCoarseCov 1 2 chosenU (fun b => a b • pauliE2) c := by
  change q124 _ _ _ _ _ _ = _
  unfold q124 term2 term3 term4 term5
  have h1 : ∀ u ∈ unitSitesOf 1 (1*2) c.1.1, ∀ X : SuTwo,
      RMap (rotElem 1) X = X → (Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c u.1 X = 0 := by
    intro u hu X hX
    exact kills_fixed (chosen_E1_axis c u.1 (unit_mem_step c u hu)) X hX
  have h2 : ∀ u ∈ unitSitesOf 1 (1*2) c.1.1, ∀ X : SuTwo,
      RMap (rotElem 1) X = X → (Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c u.1 X = 0 := by
    intro u hu X hX
    exact kills_fixed (chosen_E2_axis c u.1 (unit_mem_step c u hu)) X hX
  have ht2 : ∀ u ∈ unitSitesOf 1 (1*2) c.1.1,
      (Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c u.1
        (lineIntegral 1 chosenU (fun b => a b • pauliE2) c.1.1 (coarseGammaPath 1 c.1.1 u.1)) = 0 := by
    intro u hu; exact h1 u hu _ (line_axis_fixed a _ _)
  have ht3 : ∀ u ∈ unitSitesOf 1 (1*2) c.1.1,
      (Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c u.1
        (RMap (coarsePathHolonomy 1 chosenU c.1.1 (coarseGammaPath 1 c.1.1 u.1))
          (lineIntegral 1 chosenU (fun b => a b • pauliE2) u.1 (List.replicate 2 c.2))) = 0 := by
    intro u hu; apply h1 u hu
    rw [← rmap_commute (path_commute 1 _ _), line_axis_fixed]
  have ht4 : ∀ u ∈ unitSitesOf 1 (1*2) c.1.1,
      (Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c u.1
        (RMap ((Coeff124.ofPrincipalBackground 1 2 chosenU).gbar c)
          (lineIntegral 1 chosenU (fun b => a b • pauliE2) (cPlus c)
            (coarseGammaPath 1 (cPlus c) (partner c u.1)))) = 0 := by
    intro u hu; apply h2 u hu
    rw [← rmap_commute (gbar_commute 1 c), line_axis_fixed]
  have ht5 := kills_fixed (chosen_E3_axis c) _ (line_axis_fixed a c.1.1 (List.replicate 2 c.2))
  rw [Finset.sum_eq_zero ht2, Finset.sum_eq_zero ht3, Finset.sum_eq_zero ht4, ht5]
  simp

 theorem q124Principal_axis_flat (a : CoarseBond witnessL 1 → ℝ)
    (c : CoarseBond witnessL (1*2)) :
    q124Principal 1 2 chosenU (fun b => a b • pauliE2) c =
      unitToCoarseCov 1 2 (fun _ => 1) (fun b => a b • pauliE2) c := by
  rw [q124Principal_axis_main]
  unfold unitToCoarseCov
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · rw [path_RMap_axis]
    have hp : ∀ y p, coarsePathHolonomy 1 (fun _ : PeriodicLatticeEdge witnessL => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) y p = 1 := by
      intro y p
      induction p generalizing y with
      | nil => rfl
      | cons d p ih => simp [coarsePathHolonomy, ih]
    rw [hp, RMap_one]; rfl
  · rfl

#print axioms q124Principal_axis_main
#print axioms q124Principal_axis_flat
end HConstruction.Coeff

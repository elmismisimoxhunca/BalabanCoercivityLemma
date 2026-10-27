import PrincipalActions
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HConstruction.Coeff
open AdalyFormal.Balaban.CovariantOperators (SuTwo RMap RMap_mul_apply RMap_one)
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (witnessL witnessY CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
open AdalyFormal.Balaban.TowerLawCov
open AdalyFormal.Balaban.QjComposite
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarSU2_gauge)
open AdalyFormal.DeltaKR85
open HConstruction.SmallNF
open HConstruction.Circle
open HConstruction.NfRepair.Reproduced
open OneStep124

 theorem rot_commute (s t : ℝ) : Commute (rotElem s) (rotElem t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotElem_coe, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

 theorem chosen_commute (t : ℝ) (e : PeriodicLatticeEdge witnessL) :
    Commute (rotElem t) (chosenU e) := by
  by_cases he : e = (witnessY, (0 : Fin 3))
  · subst e; change Commute _ (nonflatU (1/16) _)
    rw [nonflatU_at_x_mu]; exact rot_commute _ _
  · change Commute _ (nonflatU (1/16) e)
    rw [nonflatU_elsewhere _ he]; exact Commute.one_right _

 theorem path_commute (t : ℝ) (y : PeriodicLatticeSite witnessL) (p : List (Fin 3)) :
    Commute (rotElem t) (coarsePathHolonomy 1 chosenU y p) := by
  induction p generalizing y with
  | nil => exact Commute.one_right _
  | cons d p ih => exact (chosen_commute t (y,d)).mul_right (ih _)

 theorem gbar_commute (t : ℝ) (c : CoarseBond witnessL (1*2)) :
    Commute (rotElem t) ((Coeff124.ofPrincipalBackground 1 2 chosenU).gbar c) := by
  have hfix : coarseGaugeTransform 1 (fun _ => rotElem t) chosenU = chosenU := by
    funext e
    change rotElem t * chosenU e * (rotElem t)⁻¹ = chosenU e
    rw [(chosen_commute t e).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h := ubarSU2_gauge 1 2 (fun _ => rotElem t) chosenU (c.1.1,c.2)
  rw [hfix] at h
  change _ = rotElem t * _ * (rotElem t)⁻¹ at h
  have hh := congrArg (fun g => g * rotElem t) h
  change rotElem t * ubarSU2 1 2 chosenU (c.1.1,c.2) = ubarSU2 1 2 chosenU (c.1.1,c.2) * rotElem t
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh.symm

 theorem rmap_commute {g h : Matrix.specialUnitaryGroup (Fin 2) ℂ} (hc : Commute g h) (X : SuTwo) :
    RMap h (RMap g X) = RMap g (RMap h X) := by
  rw [RMap_mul_apply, RMap_mul_apply, hc.eq]

 theorem line_circle (t : ℝ) (A : CoarseBond witnessL 1 → SuTwo)
    (y : PeriodicLatticeSite witnessL) (p : List (Fin 3)) :
    lineIntegral 1 chosenU (fun b => RMap (rotElem t) (A b)) y p =
      RMap (rotElem t) (lineIntegral 1 chosenU A y p) := by
  induction p generalizing y with
  | nil => simp
  | cons d p ih =>
    simp only [lineIntegral_cons, ih, map_add]
    rw [rmap_commute (chosen_commute t (y,d))]
    congr 1
    split_ifs <;> simp

 theorem main_circle (t : ℝ) (A : CoarseBond witnessL 1 → SuTwo)
    (c : CoarseBond witnessL (1*2)) :
    unitToCoarseCov 1 2 chosenU (fun b => RMap (rotElem t) (A b)) c =
      RMap (rotElem t) (unitToCoarseCov 1 2 chosenU A c) := by
  unfold unitToCoarseCov
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact rmap_commute (path_commute t _ _) _
  · simp

 theorem E1_circle (t : ℝ) (c : CoarseBond witnessL (1*2))
    (u : {z : PeriodicLatticeSite witnessL // z ∈ CoarseLattice witnessL 1})
    (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) (X : SuTwo) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c u.1 (RMap (rotElem t) X) =
      RMap (rotElem t) ((Coeff124.ofPrincipalBackground 1 2 chosenU).E1 c u.1 X) :=
  (principal_E1_action c u.1 (unit_mem_step c u hu)).circle t X
 theorem E2_circle (t : ℝ) (c : CoarseBond witnessL (1*2))
    (u : {z : PeriodicLatticeSite witnessL // z ∈ CoarseLattice witnessL 1})
    (hu : u ∈ unitSitesOf 1 (1*2) c.1.1) (X : SuTwo) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c u.1 (RMap (rotElem t) X) =
      RMap (rotElem t) ((Coeff124.ofPrincipalBackground 1 2 chosenU).E2 c u.1 X) :=
  (principal_E2_action c u.1 (unit_mem_step c u hu)).circle t X
 theorem E3_circle (t : ℝ) (c : CoarseBond witnessL (1*2)) (X : SuTwo) :
    (Coeff124.ofPrincipalBackground 1 2 chosenU).E3 c (RMap (rotElem t) X) =
      RMap (rotElem t) ((Coeff124.ofPrincipalBackground 1 2 chosenU).E3 c X) :=
  (principal_E3_action c).circle t X

 theorem q124Principal_circle (t : ℝ) (A : CoarseBond witnessL 1 → SuTwo)
    (c : CoarseBond witnessL (1*2)) :
    q124Principal 1 2 chosenU (fun b => RMap (rotElem t) (A b)) c =
      RMap (rotElem t) (q124Principal 1 2 chosenU A c) := by
  let K := Coeff124.ofPrincipalBackground 1 2 chosenU
  let A' := fun b => RMap (rotElem t) (A b)
  have h2 : term2 1 2 chosenU K A' c = RMap (rotElem t) (term2 1 2 chosenU K A c) := by
    unfold term2 A'
    simp only [line_circle, map_smul, map_sum]
    apply congrArg (fun X : SuTwo => (1/(2:ℝ)^4) • X)
    exact Finset.sum_congr rfl (fun u hu => E1_circle t c u hu _)
  have h3 : term3 1 2 chosenU K A' c = RMap (rotElem t) (term3 1 2 chosenU K A c) := by
    unfold term3 A'
    simp only [line_circle, map_smul, map_sum]
    apply congrArg (fun X : SuTwo => (1/(2:ℝ)^4) • X)
    apply Finset.sum_congr rfl
    intro u hu
    rw [rmap_commute (path_commute t _ _)]
    exact E1_circle t c u hu _
  have h4 : term4 1 2 chosenU K A' c = RMap (rotElem t) (term4 1 2 chosenU K A c) := by
    unfold term4 A'
    simp only [line_circle, map_neg, map_smul, map_sum]
    apply congrArg (fun X : SuTwo => -((1/(2:ℝ)^4) • X))
    apply Finset.sum_congr rfl
    intro u hu
    rw [rmap_commute (gbar_commute t c)]
    exact E2_circle t c u hu _
  have h5 : term5 1 2 chosenU K A' c = RMap (rotElem t) (term5 1 2 chosenU K A c) := by
    unfold term5 A'
    rw [line_circle, E3_circle, map_smul]
  change q124 _ _ _ K A' c = RMap _ (q124 _ _ _ K A c)
  unfold q124
  rw [h2, h3, h4, h5]
  simp only [A', main_circle, map_add]

#print axioms rot_commute
#print axioms gbar_commute
#print axioms q124Principal_circle
end HConstruction.Coeff

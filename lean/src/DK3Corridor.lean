import DK3Carrier
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace HConstruction.DK3
open HConstruction.Carrier HConstruction.Covariance
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.QcEquation (blockCorner)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.StridedAveraging (mem_coarseLattice_one)
open AdalyFormal.Balaban.ThirdLevelArrows (unitSitesOf)
attribute [local irreducible] blockOf CoarseLattice staircasePath axisSegment unitCoordinates unitSitesOf

/-- Source-supported lift on all 16^3 next-scale blocks; coefficient FOUR. -/
def corridorLift : W →L[ℝ] K := LinearMap.toContinuousLinearMap
  { toFun := fun v => unitCoordinates.symm (fun b =>
      if Crossing b then (4:ℝ) • cfl2Equiv 2 v (outputOf b) else 0)
    map_add' := by
      intro v w
      apply unitCoordinates.injective
      funext b
      simp only [LinearEquiv.apply_symm_apply,map_add,Pi.add_apply]
      by_cases h : Crossing b <;> simp only [h,if_true,if_false,smul_add,add_zero]
    map_smul' := by
      intro r v
      apply unitCoordinates.injective
      funext b
      simp only [LinearEquiv.apply_symm_apply,map_smul,Pi.smul_apply]
      by_cases h : Crossing b
      · simp only [h,if_true]; exact smul_comm _ _ _
      · simp only [h,if_false,smul_zero] }

theorem corridorLift_apply (v : W) (b : Bond unitL) :
    unitCoordinates (corridorLift v) b =
      if Crossing b then (4:ℝ) • cfl2Equiv 2 v (outputOf b) else 0 :=
  congrFun (unitCoordinates.apply_symm_apply _) b

theorem corridorLift_axial (v : W) : corridorLift v ∈ axialSpace := by
  intro y hy x hx b hb
  rw [corridorLift_apply,if_neg (crossing_off_axial y hy x hx b hb)]

theorem outputOf_corner (x : US) (c : CoarseBond unitL 2)
    (h : blockCorner 2 x = c.1.1) : outputOf (x,c.2) = c := by
  apply Prod.ext
  · exact Subtype.ext h
  · rfl

theorem corridor_line (v : W) (c : CoarseBond unitL 2) (x : US) (hx : x ∈ blockOf c.1.1 2) :
    unitCoordinates (corridorLift v) (x,c.2) +
      unitCoordinates (corridorLift v) (periodicLatticeShift x c.2,c.2) =
      if Transverse x c.2 then (4:ℝ) • cfl2Equiv 2 v c else 0 := by
  have hu : (⟨x,mem_coarseLattice_one x⟩ : {z : US // z ∈ CoarseLattice unitL 1}) ∈
      unitSitesOf 1 2 c.1.1 := by
    simp only [unitSitesOf,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hx
  have hh := GeneralSection.hit_geometry unit_even c ⟨x,mem_coarseLattice_one x⟩ hu
  change (((x c.2).val%2=1 ∧ blockCorner 2 x=c.1.1 ∧
    ¬ ((periodicLatticeShift x c.2) c.2).val%2=1) ∨
    (¬ (x c.2).val%2=1 ∧ ((periodicLatticeShift x c.2) c.2).val%2=1 ∧
      blockCorner 2 (periodicLatticeShift x c.2)=c.1.1)) at hh
  rw [corridorLift_apply,corridorLift_apply]
  by_cases ht : Transverse x c.2
  · have ht' := (transverse_shift x c.2).mpr ht
    rw [if_pos ht]
    rcases hh with ⟨h0,hc,h1⟩|⟨h0,h1,hc⟩
    · rw [if_pos (show Crossing (x,c.2) from ⟨h0,ht⟩),
        if_neg (show ¬ Crossing (periodicLatticeShift x c.2,c.2) from fun h => h1 h.1),add_zero,
        outputOf_corner x c hc]
    · rw [if_neg (show ¬ Crossing (x,c.2) from fun h => h0 h.1),
        if_pos (show Crossing (periodicLatticeShift x c.2,c.2) from ⟨h1,ht'⟩),zero_add,
        outputOf_corner _ c hc]
  · have ht' : ¬ Transverse (periodicLatticeShift x c.2) c.2 := fun h => ht ((transverse_shift x c.2).mp h)
    rw [if_neg ht,if_neg (show ¬ Crossing (x,c.2) from fun h => ht h.2),
      if_neg (show ¬ Crossing (periodicLatticeShift x c.2,c.2) from fun h => ht' h.2),add_zero]

theorem rawLinear_corridorLift (v : W) : rawLinear (corridorLift v) = v := by
  apply (cfl2Equiv 2).injective
  funext c
  rw [rawLinear_sum,Finset.sum_congr rfl (fun x hx => corridor_line v c x hx)]
  rw [← Finset.sum_filter,transverse_filter]
  have hn : c.1.1 ∉ ({(crossingBond c).1} : Finset US) := by
    simp only [Finset.mem_singleton]
    exact (crossing_ne_center c).symm
  rw [Finset.sum_insert hn,Finset.sum_singleton]
  module

/-- Read each distinguished crossing, in the inverse normalization. -/
def crossingRead (D : K) : W := (cfl2Equiv 2).symm
  (fun c => (1/4:ℝ) • unitCoordinates D (crossingBond c))

theorem supported_reconstruct (D : K)
    (hs : ∀ b : Bond unitL, ¬ Crossing b → unitCoordinates D b = 0) :
    corridorLift (crossingRead D) = D := by
  apply unitCoordinates.injective
  funext b
  rw [corridorLift_apply]
  by_cases hb : Crossing b
  · rw [if_pos hb]
    simp only [crossingRead,LinearEquiv.apply_symm_apply,crossing_output b hb,smul_smul]
    norm_num
  · rw [if_neg hb,hs b hb]

theorem corridor_unique (D : K) (v : W)
    (hs : ∀ b : Bond unitL, ¬ Crossing b → unitCoordinates D b = 0)
    (hq : rawLinear D = v) : D = corridorLift v := by
  have hr := supported_reconstruct D hs
  have hc : crossingRead D = v := by rw [← rawLinear_corridorLift (crossingRead D),hr,hq]
  rw [← hc,hr]

/-- A non-distinguished crossing. Its value survives removal of next-Q. -/
def testSite : US := fun μ => if μ = 0 ∨ μ = 1 then 1 else 0
def testBond : Bond unitL := (testSite,0)
theorem test_last : (testBond.1 testBond.2).val%2 = 1 := by norm_num [testBond,testSite]
theorem test_not_crossing : ¬ Crossing testBond := by
  intro h
  have hh := h.2 1 (by decide)
  norm_num [testBond,testSite] at hh

def freeTest : K := unitCoordinates.symm (fun b => if b = testBond then suTwoWitness else 0)
def coarseTest : K := freeTest - corridorLift (rawLinear freeTest)

theorem freeTest_axial : freeTest ∈ axialSpace := by
  intro y hy x hx b hb
  have hn : b ≠ testBond := by
    intro h
    have hh := axial_even y hy x hx b hb
    rw [h,test_last] at hh
    omega
  change unitCoordinates (unitCoordinates.symm _) b = 0
  rw [LinearEquiv.apply_symm_apply,if_neg hn]

theorem coarseTest_axial : coarseTest ∈ axialSpace :=
  axialSpace.sub_mem freeTest_axial (corridorLift_axial _)

theorem coarseTest_raw : rawLinear coarseTest = 0 := by
  simp only [coarseTest,map_sub,rawLinear_corridorLift,sub_self]

theorem coarseTest_nonzero : coarseTest ≠ 0 := by
  intro h
  have hh := congrArg (fun D => unitCoordinates D testBond) h
  simp only [coarseTest,map_sub,Pi.sub_apply,corridorLift_apply,if_neg test_not_crossing,
    sub_zero,freeTest,LinearEquiv.apply_symm_apply,map_zero,Pi.zero_apply] at hh
  exact suTwoWitness_ne_zero hh
end HConstruction.DK3

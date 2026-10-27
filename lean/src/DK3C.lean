import DK3Objects

set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace HConstruction.DK3
open HConstruction.Carrier
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice blockOf staircasePath)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)

attribute [local irreducible] blockOf CoarseLattice staircasePath unitCoordinates

/-- The actual union of the already-certified LOCAL axial trees. -/
def Axial (b : Bond unitL) : Prop :=
  ∃ y ∈ CoarseLattice unitL 2, ∃ x ∈ blockOf y 2, b ∈ staircasePath y x

/-- CMP99b p.428's reduced bond set, at Lambda = the whole periodic unit torus. -/
def Independent (b : Bond unitL) : Prop := ¬ Axial b ∧ ¬ Crossing b

/-- Zero-extension model of fields on Independent, not the constrained B-space.
The inherited L2 norm counts ONLY independent bonds. No Q constraint is imposed. -/
def reducedSpace : Submodule ℝ K where
  carrier := {B | ∀ b, ¬ Independent b → unitCoordinates B b = 0}
  zero_mem' := by simp
  add_mem' := by
    intro B D hB hD b hb
    simp only [map_add, Pi.add_apply, hB b hb, hD b hb, add_zero]
  smul_mem' := by
    intro r B hB b hb
    simp only [map_smul, Pi.smul_apply, hB b hb, smul_zero]

abbrev Reduced := reducedSpace

/-- All assignments on the paper's reduced bond set are allowed: there is no
hidden next-Q or other constraint in Reduced. -/
def freeExtend (f : {b : Bond unitL // Independent b} → SuTwo) : Reduced :=
  ⟨unitCoordinates.symm (fun b => if h : Independent b then f ⟨b,h⟩ else 0), by
    intro b hb
    rw [LinearEquiv.apply_symm_apply, dif_neg hb]⟩

def freeCoordinates : Reduced ≃ₗ[ℝ] ({b : Bond unitL // Independent b} → SuTwo) where
  toFun B b := unitCoordinates (B : K) b
  invFun := freeExtend
  left_inv B := by
    apply Subtype.ext
    apply unitCoordinates.injective
    funext b
    change unitCoordinates (unitCoordinates.symm _) b = _
    rw [LinearEquiv.apply_symm_apply]
    split_ifs with hb
    · rfl
    · exact (B.property b hb).symm
  right_inv f := by
    funext b
    change unitCoordinates (unitCoordinates.symm _) b = _
    rw [LinearEquiv.apply_symm_apply, dif_pos b.property]
  map_add' B D := by ext b; simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' r B := by ext b; simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]

/-- Coordinate restriction, followed by zero extension (not reconstruction). -/
def erase : K →L[ℝ] K := LinearMap.toContinuousLinearMap
  { toFun := fun B => unitCoordinates.symm (fun b => if Independent b then unitCoordinates B b else 0)
    map_add' := by
      intro B D
      apply unitCoordinates.injective
      funext b
      simp only [LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
      split_ifs <;> simp
    map_smul' := by
      intro r B
      apply unitCoordinates.injective
      funext b
      simp only [LinearEquiv.apply_symm_apply, map_smul, Pi.smul_apply]
      split_ifs <;> simp }

theorem erase_apply (B : K) (b : Bond unitL) :
    unitCoordinates (erase B) b = if Independent b then unitCoordinates B b else 0 :=
  congrFun (unitCoordinates.apply_symm_apply _) b

theorem erase_mem (B : K) : erase B ∈ reducedSpace := by
  intro b hb
  rw [erase_apply, if_neg hb]

def restriction : K →L[ℝ] Reduced :=
  LinearMap.toContinuousLinearMap (erase.toLinearMap.codRestrict reducedSpace erase_mem)

theorem restriction_apply (B : K) : (restriction B : K) = erase B := rfl

theorem reduced_axial (B : Reduced) : (B : K) ∈ axialSpace := by
  intro y hy x hx b hb
  exact B.property b (fun hi => hi.1 ⟨y,hy,x,hx,hb⟩)

theorem reduced_crossing_zero (B : Reduced) (b : Bond unitL) (hb : Crossing b) :
    unitCoordinates (B : K) b = 0 := B.property b (fun hi => hi.2 hb)

theorem restriction_subtype (B : Reduced) : restriction B = B := by
  apply Subtype.ext
  apply unitCoordinates.injective
  funext b
  rw [restriction_apply, erase_apply]
  split_ifs with hb
  · rfl
  · exact (B.property b hb).symm

/-- Full L2 inner product transported along the existing bond bijection. -/
theorem inner_coordinates (B D : K) :
    (inner ℝ B D : ℝ) = ∑ b : Bond unitL,
      inner ℝ (unitCoordinates B b) (unitCoordinates D b) := by
  unfold unitCoordinates
  exact PiLp.inner_apply B D

theorem norm_sq_coordinates (B : K) :
    ‖B‖^2 = ∑ b : Bond unitL, ‖unitCoordinates B b‖^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coordinates]
  exact Finset.sum_congr rfl (fun _ _ => real_inner_self_eq_norm_sq _)

/-- Explicitly verifies that the Reduced norm is the ordinary independent-coordinate L2 norm. -/
theorem reduced_norm_sq (B : Reduced) :
    ‖B‖^2 = ∑ b : {b : Bond unitL // Independent b}, ‖unitCoordinates (B : K) b‖^2 := by
  classical
  change ‖(B : K)‖^2 = _
  rw [norm_sq_coordinates]
  apply Finset.sum_congr_set {b | Independent b} _ _ (fun _ _ => rfl)
  intro b hb
  rw [B.property b hb, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Erasing dependent coordinates can only decrease the L2 norm. -/
theorem restriction_norm_sq_le (B : K) : ‖restriction B‖^2 ≤ ‖B‖^2 := by
  change ‖erase B‖^2 ≤ ‖B‖^2
  rw [norm_sq_coordinates, norm_sq_coordinates]
  apply Finset.sum_le_sum
  intro b _
  rw [erase_apply]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg ‖unitCoordinates B b‖

/-- Genuine connecting-bond reconstruction, not the quadratic D2 lift.
It copies free coordinates and solves Q B = 0 by a crossing-supported correction.
Invertibility on the newly intersected DK3 interval is proved in DK3Objects. -/
def C (t : ℝ) : Reduced →L[ℝ] K :=
  reducedSpace.subtypeL - (Unit.localLift t).comp ((nativeRawQ t).comp reducedSpace.subtypeL)

theorem C_apply (t : ℝ) (B : Reduced) :
    C t B = (B : K) - Unit.localLift t (nativeRawQ t B) := rfl

theorem C_independent (t : ℝ) (B : Reduced) (b : Bond unitL) (hb : Independent b) :
    unitCoordinates (C t B) b = unitCoordinates (B : K) b := by
  rw [C_apply, map_sub, Pi.sub_apply, Unit.localLift_support t _ b hb.2, sub_zero]

theorem C_axial (t : ℝ) (B : Reduced) : C t B ∈ axialSpace := by
  apply axialSpace.sub_mem (reduced_axial B)
  exact corridorLift_axial _

/-- The restriction is a left inverse even for the totalized C outside the interval. -/
theorem restriction_C (t : ℝ) (B : Reduced) : restriction (C t B) = B := by
  apply Subtype.ext
  apply unitCoordinates.injective
  funext b
  rw [restriction_apply, erase_apply]
  split_ifs with hb
  · exact C_independent t B b hb
  · exact (B.property b hb).symm

theorem C_injective (t : ℝ) : Function.Injective (C t) :=
  Function.LeftInverse.injective (restriction_C t)

theorem C_norm_sq_lower (t : ℝ) (B : Reduced) : ‖B‖^2 ≤ ‖C t B‖^2 := by
  have h := restriction_norm_sq_le (C t B)
  rw [restriction_C] at h
  exact h

/-- NO extra invertibility hypothesis or smaller time interval. -/
theorem C_kernel (t : ℝ) (ht : |t| ≤ interval) (B : Reduced) :
    nativeRawQ t (C t B) = 0 := by
  have hg := object_gates t ht
  rw [C_apply, ← hg.2.2, map_sub]
  have h := congrArg (fun T : W →L[ℝ] W => T (Unit.rawQ t B)) (Unit.localLift_right t hg.1)
  change Unit.rawQ t (Unit.localLift t (Unit.rawQ t B)) = Unit.rawQ t B at h
  rw [h, sub_self]

theorem C_mem_domain (t : ℝ) (ht : |t| ≤ interval) (B : Reduced) :
    C t B ∈ domain t := by
  refine ⟨?_,C_axial t B,C_kernel t ht B⟩
  intro b hb
  simp only [Finset.mem_univ, not_true_eq_false, or_self] at hb

/-- Every axial B differs from its independent-coordinate restriction only on b0. -/
theorem difference_supported (B : K) (hB : B ∈ axialSpace) :
    ∀ b : Bond unitL, ¬ Crossing b → unitCoordinates (B - erase B) b = 0 := by
  intro b hb
  rw [map_sub, Pi.sub_apply, erase_apply]
  by_cases ha : Axial b
  · obtain ⟨y,hy,x,hx,hbax⟩ := ha
    rw [hB y hy x hx b hbax]
    split_ifs <;> simp
  · rw [if_pos ⟨ha,hb⟩, sub_self]

/-- Unique reconstruction for the ACTUAL native Q constraint; not a chosen
abstract isomorphism, and not inclusion of the old constrained space. -/
theorem C_restriction (t : ℝ) (ht : |t| ≤ interval)
    (B : K) (hB : B ∈ domain t) : C t (restriction B) = B := by
  have hg := object_gates t ht
  have hq : Unit.rawQ t B = 0 := by rw [hg.2.2]; exact hB.2.2
  have hh := Unit.localLift_unique t hg.1 (B - erase B) (-Unit.rawQ t (erase B))
    (difference_supported B hB.2.1) (by rw [map_sub,hq,zero_sub])
  rw [map_neg] at hh
  rw [C_apply, restriction_apply, ← hg.2.2]
  calc
    erase B - Unit.localLift t (Unit.rawQ t (erase B)) = erase B + (B - erase B) := by rw [hh]; rfl
    _ = B := by abel

/-- The two defining properties in the source uniquely determine C.
This also identifies any bondwise construction satisfying them with this global solve. -/
theorem C_characterization (t : ℝ) (ht : |t| ≤ interval) (Bt : Reduced) (B : K) :
    C t Bt = B ↔ B ∈ domain t ∧
      ∀ b, Independent b → unitCoordinates B b = unitCoordinates (Bt : K) b := by
  constructor
  · rintro rfl
    exact ⟨C_mem_domain t ht Bt, C_independent t Bt⟩
  · rintro ⟨hB,hcoords⟩
    have hr : restriction B = Bt := by
      apply Subtype.ext
      apply unitCoordinates.injective
      funext b
      rw [restriction_apply, erase_apply]
      split_ifs with hb
      · exact hcoords b hb
      · exact (Bt.property b hb).symm
    rw [← hr]
    exact C_restriction t ht B hB

/-- Exact range identification at Lambda=univ, with no boundary convention ambiguity. -/
theorem range_C (t : ℝ) (ht : |t| ≤ interval) :
    LinearMap.range (C t).toLinearMap = domain t := by
  ext B
  constructor
  · rintro ⟨Bt,rfl⟩
    exact C_mem_domain t ht Bt
  · intro hB
    exact ⟨restriction B, C_restriction t ht B hB⟩

/-- Explicit free coordinate on side32; no dimension-only nonemptiness. -/
def independentTest : Reduced := ⟨freeTest, by
  intro b hb
  change unitCoordinates (unitCoordinates.symm _) b = 0
  rw [LinearEquiv.apply_symm_apply]
  apply if_neg
  intro he
  subst b
  apply hb
  refine ⟨?_,test_not_crossing⟩
  rintro ⟨y,hy,x,hx,hbax⟩
  have h := axial_even y hy x hx testBond hbax
  rw [test_last] at h
  omega⟩

theorem independentTest_nonzero : independentTest ≠ 0 := by
  intro h
  have hh := congrArg (fun D : Reduced => unitCoordinates (D:K) testBond) h
  change unitCoordinates freeTest testBond = unitCoordinates 0 testBond at hh
  rw [map_zero,Pi.zero_apply] at hh
  simp only [freeTest,LinearEquiv.apply_symm_apply] at hh
  exact AdalyFormal.Balaban.CovariantOperators.suTwoWitness_ne_zero hh

theorem domain_nonzero (t : ℝ) (ht : |t| ≤ interval) : domain t ≠ ⊥ := by
  intro h
  have hm := C_mem_domain t ht independentTest
  rw [h,Submodule.mem_bot] at hm
  have hz := restriction_C t independentTest
  rw [hm,map_zero] at hz
  exact independentTest_nonzero hz.symm

end HConstruction.DK3

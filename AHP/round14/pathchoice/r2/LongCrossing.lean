import DrEquiv
import DrPath3

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                              
abbrev PlaqSel : Type := ∀ (L : PeriodicLatticeExtent), TowerGeom L → Set (PeriodicLatticePlaquette L)
def selIn : PlaqSel := fun _ G => plaqIn G.Om0
def selAll : PlaqSel := fun _ _ => Set.univ
section Selectors
variable (sD sJ : PlaqSel)

noncomputable def DeltaS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  AdalyFormal.StatementLaneR6.deltaKLocCLM U (sD L G)
noncomputable def DpiFullS {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) : BondFnL2 L →L[ℝ] BondFnL2 L :=
  (ContinuousLinearMap.adjoint (Wop G U a)).comp ((DeltaS sD G U).comp (Wop G U a))
theorem DpiFullS_symm {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (a : ℝ) (x y : BondFnL2 L) :
    ⟪DpiFullS sD G U a x, y⟫ = ⟪x, DpiFullS sD G U a y⟫ := by
  simp only [DpiFullS, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  exact AdalyFormal.StatementLaneR6.deltaKLocCLM_symm U _ _ _
section Ops
variable (P : IngrBParams)

noncomputable def JfS : BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1 (sJ _ P.G) P.U b))
noncomputable def dataS : BaseDataS ↥(bondSupp P.G) (SiteL2 (scaleUp P.ell P.k P.Lu)) (FSp P.G) :=
  { baseData P.G P.U P.a P.sector (JfS sJ P) with
    Dpi := (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) }
theorem dataS_laws : (dataS sD sJ P).Laws := by
  refine ⟨fun x y => ?_, P.data_laws.C2_quad⟩
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ = ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _
noncomputable def G1invS : ↥(bondSupp P.G) →L[ℝ] ↥(bondSupp P.G) :=
  Classical.choose ((dataS sD sJ P).exists_G1inv (dataS_laws sD sJ P))
noncomputable def H1inS : BondFnL2 P.Lu →L[ℝ] BondFnL2 (scaleUp P.ell P.k P.Lu) :=
  (iE P.G).comp (((dataS sD sJ P).H1 (G1invS sD sJ P)).comp (ContinuousLinearMap.adjoint P.tau))
end Ops

namespace GenS
variable (P : IngrBParams)

noncomputable def NmatS : FSp P.G →L[ℝ] FSp P.G :=
  ((dataS sD sJ P).Q.comp ((dataS sD sJ P).G1 (G1invS sD sJ P))).comp (dataS sD sJ P).Qs
noncomputable def firstTermS (B : BondFnL2 P.Lu) : ℝ :=
  P.eta * ⟪ContinuousLinearMap.adjoint P.tau B, Ring.inverse (NmatS sD sJ P) (ContinuousLinearMap.adjoint P.tau B)⟫
noncomputable def genFormS (B : BondFnL2 P.Lu) : ℝ :=
  firstTermS sD sJ P B - P.a * ⟪B, B⟫ - 2 * ⟪H1inS sD sJ P (P.D2in B), JfS sJ P⟫
end GenS

def InstIneqS (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  ∀ (Bt : Bond Lu → SuTwo), OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
    γ₀ * bondEnergy Bt ≤
      GenS.genFormS sD sJ (gparams ell k Lu hell S U a Lam)
        (WithLp.toLp 2 (GenP.genC (gparams ell k Lu hell S U a Lam) Bt))
end Selectors

                                                   
def InstIneqSG (sD sJ : PlaqSel) (ell k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent) (γ₀ : ℝ)
    (S : Tower (scaleUp ell k Lu)) (Lam : Set (PeriodicLatticeSite Lu)) (U : LinkCfg (scaleUp ell k Lu)) : Prop :=
  IsUnit (dataS sD sJ (gparams ell k Lu hell S U a Lam)).Ginv → InstIneqS sD sJ ell k hell a Lu γ₀ S Lam U
def CoercG8AtSG (sD sJ : PlaqSel) (ell M R k : ℕ) (hell : 0 < ell) (a : ℝ) (Lu : PeriodicLatticeExtent)
    (c : ℕ) (α₀ γ₀ : ℝ) : Prop :=
  TorusOK ell M Lu →
  ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell M R k S →
  ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell M R k S Lam →
  ∀ (U : LinkCfg (scaleUp ell k Lu)),
    ClassCoupled ell M c k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
    InstIneqSG sD sJ ell k hell a Lu γ₀ S Lam U
def P428Target8SG (sD sJ : PlaqSel) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      SidePow6 ell (ell ^ m) a ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
        ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * (ell ^ m : ℕ) * α₀ ≤ a₀ →
          CoercG8AtSG sD sJ ell (ell ^ m) R k (by omega) a Lu 12 α₀ γ₀
def GShape (C : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop) : Prop :=
  ∀ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a →
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ → (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀ →
        TorusOK ell (ell ^ m) Lu → ∀ (S : Tower (scaleUp ell k Lu)), Admissible ell (ell ^ m) R k S →
        ∀ (Lam : Set (PeriodicLatticeSite Lu)), LambdaOK2 ell (ell ^ m) R k S Lam →
        ∀ (U : LinkCfg (scaleUp ell k Lu)), ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        (∃ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt) →
        IsUnit (dataS selAll selAll (gparams ell k Lu (by omega) S U a Lam)).Ginv →
        C ell k Lu (by omega) S U a Lam
def CPen : ∀ (ell k : ℕ) (Lu : PeriodicLatticeExtent) (_ : 0 < ell) (_ : Tower (scaleUp ell k Lu))
    (_ : LinkCfg (scaleUp ell k Lu)) (_ : ℝ) (_ : Set (PeriodicLatticeSite Lu)), Prop :=
  fun ell k Lu h S U a Lam =>
    IsUnit ((dataS selAll selAll (gparams ell k Lu h S U a Lam)).Ginv -
      (dataS selIn selIn (gparams ell k Lu h S U a Lam)).Delta2 (dataS_laws selIn selIn (gparams ell k Lu h S U a Lam)))
def GuardPencilT : Prop := GShape CPen
def GoalPos1 : Prop := GuardPencilT
def GoalNeg1 : Prop := ¬ GoalPos1
def GoalPos2 : Prop := P428Target8SG selAll selAll
def GoalNeg2 : Prop := ¬ GoalPos2
theorem goalPos2_iff_goalPos1 : GoalPos2 ↔ GoalPos1 := by
  exact AdalyFormal.D1Residual.P428Target8SG_iff_pencilT
theorem goalNeg1_iff_goalNeg2 : GoalNeg1 ↔ GoalNeg2 :=
  not_congr goalPos2_iff_goalPos1.symm
def CofinalPencilFailure : Prop :=
  ∃ (ell : ℕ) (hell : 2 ≤ ell) (a : ℝ), 0 < a ∧
    ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ 1 ≤ m ∧
      ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧
        ∀ a₀ : ℝ, 0 < a₀ →
          ∃ (k : ℕ) (_ : 1 ≤ k) (Lu : PeriodicLatticeExtent) (α₀ : ℝ)
            (_ : 0 < α₀) (_ : (12 : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀)
            (_ : TorusOK ell (ell ^ m) Lu)
            (S : Tower (scaleUp ell k Lu)) (_ : Admissible ell (ell ^ m) R k S)
            (Lam : Set (PeriodicLatticeSite Lu)) (_ : LambdaOK2 ell (ell ^ m) R k S Lam)
            (U : LinkCfg (scaleUp ell k Lu))
            (_ : ClassCoupled ell (ell ^ m) 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U)
            (Bt : Bond Lu → SuTwo),
            OnLambdaTildeIn Lam ell Bt ∧ OnLambdaT Lam Bt ∧ 0 < bondEnergy Bt ∧
            IsUnit (dataS selAll selAll (gparams ell k Lu (by omega) S U a Lam)).Ginv ∧
            ¬ CPen ell k Lu (by omega) S U a Lam
theorem cofinalPencilFailure_implies_goalNeg1 (h : CofinalPencilFailure) : GoalNeg1 := by
  intro hp
  obtain ⟨ell, hell, a, ha, hmfail⟩ := h
  obtain ⟨m₀, _, hmpos⟩ := hp ell hell a ha
  obtain ⟨m, hm, _, hRfail⟩ := hmfail m₀
  obtain ⟨R₀, hRpos⟩ := hmpos m hm
  obtain ⟨R, hR, hafail⟩ := hRfail R₀
  obtain ⟨a₀, ha₀, hapos⟩ := hRpos R hR
  obtain ⟨k, hk, Lu, α₀, hα, hsmall, hT, S, hS, Lam, hL, U, hU,
    Bt, hBt1, hBt2, hE, hu, hnu⟩ := hafail a₀ ha₀
  exact hnu (hapos k hk Lu α₀ hα hsmall hT S hS Lam hL U hU ⟨Bt, hBt1, hBt2, hE⟩ hu)
theorem cofinalPencilFailure_implies_goalNeg2 (h : CofinalPencilFailure) : GoalNeg2 :=
  goalNeg1_iff_goalNeg2.mp (cofinalPencilFailure_implies_goalNeg1 h)
end AdalyFormal.Round2.Guarded.Pin

   
                                                                                
                                                                            
                                                                                
                                                                                
                                                                             
                                                                              
  
namespace AdalyFormal.Round2.Guarded.R2Prove

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

end Algebra

section Concrete
variable (P : IngrBParams)

end Concrete

end AdalyFormal.Round2.Guarded.R2Prove

                                                                            
namespace AdalyFormal.Round3.Guarded.RefuteR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC
  (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')

                                                                        
theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y :=
  Finset.single_le_sum (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round3.Guarded.RefuteR3

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round3.Guarded.RefuteR2
open AdalyFormal.NonVac (clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                                           
                                                                                   
end AdalyFormal.Round3.Guarded.RefuteR3

   
                                                                               
                                                                          
  
namespace AdalyFormal.Round4.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self'
  clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.AdmissibleSubspace
  (Bond blockOf CoarseLattice mem_blockOf mem_CoarseLattice staircasePath)
open AdalyFormal.Balaban.FullReparamC
  (freeBond freeBond_not_mem_staircase freeBond_not_dropped freeBond_coord_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

def dilLu (q R : ℕ) : PeriodicLatticeExtent :=
  fun μ => if μ = 0 then 6 * (R * q) + 8 * q - 1 else 4 * q - 1
def dilTower (q R : ℕ) : Tower (scaleUp 2 1 (dilLu q R)) where
  Om j := if j = 0 then {x | 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q}
    else if j = 1 then {x | 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q}
    else ∅
def dilLam (q R : ℕ) : Set (PeriodicLatticeSite (dilLu q R)) :=
  {x | 3 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 3 * (R * q) + 6 * q}
theorem dil_unit_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    dilLu q R μ + 1 = if μ = 0 then 6 * (R * q) + 8 * q else 4 * q := by
  by_cases h : μ = 0 <;> simp [dilLu, h] <;> omega
theorem dil_fine_size {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    scaleUp 2 1 (dilLu q R) μ + 1 = if μ = 0 then 12 * (R * q) + 16 * q else 8 * q := by
  simp only [scaleUp, dil_unit_size hq]
  by_cases h : μ = 0 <;> simp [h] <;> omega
theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h
theorem dil_torus {q : ℕ} (hq : 0 < q) (R : ℕ) : TorusOK 2 (2*q) (dilLu q R) := by
  have hd : ∀ μ : Fin 3, 2*q ∣ dilLu q R μ + 1 := by
    intro μ
    rw [dil_unit_size hq]
    by_cases h : μ = 0
    · rw [if_pos h]; exact ⟨3*R+4, by ring⟩
    · rw [if_neg h]; exact ⟨2, by ring⟩
  refine ⟨fun μ => dvd_trans (dvd_mul_right 2 q) (hd μ), ?_, hd⟩
  intro μ
  rw [dil_unit_size hq]
  split_ifs <;> omega
theorem dil_admissible {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    Admissible 2 (2*q) R 1 (dilTower q R) := by
  have hp : 4*q ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by ring⟩
  have hq' : 4*q ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by ring⟩
  have hlo : 2*q ∣ 4*q := ⟨2, by ring⟩
  have hhi : 2*q ∣ 12*(R*q)+12*q := ⟨6*R+6, by ring⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    by_cases h0 : j = 0
    · subst j
      change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q
      omega
    · simp [dilTower, h0] at hx
  · intro j hj
    simp [dilTower, show j ≠ 0 by omega, show j ≠ 1 by omega]
  · intro j hj μ
    rw [dil_fine_size hq]
    interval_cases j <;> by_cases hμ : μ = 0 <;> simp only [bigSide, pow_zero, pow_one, mul_one, hμ, ↓reduceIte]
    · exact ⟨6*R+8, by ring⟩
    · exact ⟨4, by ring⟩
    · exact ⟨3*R+4, by ring⟩
    · exact ⟨2, by ring⟩
  · intro j hj x hx y hy
    interval_cases j
    · change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change 4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q
      apply iv_block (by omega : 0 < 2*q) hlo hhi _ hx
      simpa [bigSide] using hy 0
    · change (2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val < 10*(R*q)+12*q) at hx
      change 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      apply iv_block (by omega : 0 < 4*q) hp hq' _ hx
      simpa [bigSide, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy 0
  · intro j hj x hx y hy
    interval_cases j
    · change ¬ (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hxb := dil_fine_bound hq R x
      have hpd := zero_coord_le_pdist x y
      simp only [dil_fine_size hq, ↓reduceIte] at hpd
      have hcoord : 2*(R*q) < pcd (12*(R*q)+16*q) (x 0).val (y 0).val := by
        unfold pcd; split_ifs <;> omega
      have heq : R * bigSide (2*q) 2 0 = 2*(R*q) := by simp [bigSide]; ring
      rw [heq]; exact lt_of_lt_of_le hcoord hpd
    · simp [dilTower] at hy
  · intro x
    change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) ↔ _
    have hrm : R*(2*q) = 2*(R*q) := by ring
    constructor
    · intro hx
      let v := if (x 0).val < 2*(R*q)+4*q then 2*(R*q)+4*q
        else if (x 0).val < 10*(R*q)+12*q then (x 0).val else 10*(R*q)+12*q-1
      have hv : v < scaleUp 2 1 (dilLu q R) 0 + 1 := by
        rw [dil_fine_size hq, if_pos rfl]
        dsimp [v]; split_ifs <;> omega
      refine ⟨Function.update x 0 ⟨v, hv⟩, ?_, x, fun μ => rfl, ?_⟩
      · change 2*(R*q)+4*q ≤ v ∧ v < 10*(R*q)+12*q
        dsimp [v]; split_ifs <;> omega
      · unfold pdist
        rw [Finset.sum_eq_single (0 : Fin 3)]
        · simp only [Function.update_self, dil_fine_size hq, ↓reduceIte, hrm]
          have hc := pcd_clamp (N := 12*(R*q)+16*q) (a := (x 0).val)
            (lo := 2*(R*q)+4*q) (hi := 10*(R*q)+12*q) (D := 2*(R*q))
            (by omega) (by omega) (dil_fine_bound hq R x) (by omega)
          simpa [v] using hc
        · intro μ _ hμ; rw [Function.update_of_ne hμ, pcd_self']
        · intro h; exact (h (Finset.mem_univ _)).elim
    · rintro ⟨y, hy, z, hz, hd⟩
      change (2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q) at hy
      have hcoord := le_trans (zero_coord_le_pdist z y) hd
      simp only [dil_fine_size hq, ↓reduceIte, hrm] at hcoord
      have hn := pcd_near (dil_fine_bound hq R z) hy
        (show 2*(R*q) ≤ 2*(R*q)+4*q by omega)
        (show 10*(R*q)+12*q+2*(R*q) ≤ 12*(R*q)+16*q by omega) hcoord
      have hzmem : 4*q ≤ (z 0).val ∧ (z 0).val < 12*(R*q)+12*q := by omega
      exact iv_block (by omega : 0 < 2*q) hlo hhi (hz 0).symm hzmem
def dilEmb {q : ℕ} (hq : 0 < q) (R : ℕ) (y : PeriodicLatticeSite (dilLu q R)) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨2 * (y μ).val, by
    have h := (y μ).isLt
    simp only [dil_unit_size hq] at h
    rw [dil_fine_size hq]
    split_ifs at * <;> omega⟩
theorem dil_lambda {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    LambdaOK2 2 (2*q) R 1 (dilTower q R) (dilLam q R) := by
  have hp : 2*q ∣ 3*(R*q)+4*q := by obtain ⟨t, rfl⟩ := hR; exact ⟨3*t+2, by ring⟩
  have hq' : 2*q ∣ 3*(R*q)+6*q := by obtain ⟨t, rfl⟩ := hR; exact ⟨3*t+3, by ring⟩
  have hblock : BlockClosed (2*q) (dilLam q R) := by
    intro x hx y hy; exact iv_block (by omega) hp hq' (hy 0) hx
  have hblock2 : BlockClosed 2 (dilLam q R) := by
    intro x hx y hy
    exact iv_block (by omega) (dvd_trans (dvd_mul_right 2 q) hp)
      (dvd_trans (dvd_mul_right 2 q) hq') (hy 0) hx
  refine ⟨⟨hblock, dilEmb hq R, fun y μ => rfl, ?_, ?_⟩, ?_⟩
  · intro y hy
    change 2*(R*q)+4*q ≤ 2*(y 0).val ∧ 2*(y 0).val < 10*(R*q)+12*q
    change (3*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 3*(R*q)+6*q) at hy
    omega
  · intro y hy z hz
    change (3*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 3*(R*q)+6*q) at hy
    change ¬ (2*(R*q)+4*q ≤ 2*(z 0).val ∧ 2*(z 0).val < 10*(R*q)+12*q) at hz
    have hzb := (z 0).isLt
    simp only [dil_unit_size hq, ↓reduceIte] at hzb
    have hcoord : 2*(R*q) < pcd (6*(R*q)+8*q) (y 0).val (z 0).val := by
      unfold pcd; split_ifs <;> omega
    have hpd := zero_coord_le_pdist y z
    simp only [dil_unit_size hq, ↓reduceIte] at hpd
    have hrm : R*(2*q) = 2*(R*q) := by ring
    rw [hrm]; exact lt_of_lt_of_le hcoord hpd
  · intro x hx
    let y : PeriodicLatticeSite (dilLu q R) := fun μ =>
      ⟨2*((x μ).val/2), lt_of_le_of_lt (Nat.mul_div_le _ _) (x μ).isLt⟩
    have hy : ∀ μ, (y μ).val = 2*((x μ).val/2) := fun μ => rfl
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_CoarseLattice]; intro μ; rw [hy]; omega
    · intro z hz
      apply hblock2 x hx z
      rw [mem_blockOf] at hz
      intro μ; have hh := hz μ; rw [hy] at hh; omega
    · rw [mem_blockOf]; intro μ; rw [hy]; omega
def dilSeed {q : ℕ} (hq : 0 < q) (R : ℕ) : PeriodicLatticeSite (dilLu q R) :=
  fun μ => ⟨if μ = 0 then 3*(R*q)+4*q else 0, by
    rw [dil_unit_size hq]; split_ifs <;> omega⟩
noncomputable def dilBt {q : ℕ} (hq : 0 < q) (R : ℕ) : Bond (dilLu q R) → SuTwo :=
  Pi.single (freeBond 2 (dilSeed hq R)) suTwoWitness
theorem dil_competitor {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) :
    OnLambdaTildeIn (dilLam q R) 2 (dilBt hq R) ∧
      OnLambdaT (dilLam q R) (dilBt hq R) ∧ 0 < bondEnergy (dilBt hq R) := by
  have hdvd := (dil_torus hq R).1
  have hy : dilSeed hq R ∈ CoarseLattice (dilLu q R) 2 := by
    rw [mem_CoarseLattice]; intro μ
    by_cases hμ : μ = 0
    · subst μ
      change (3*(R*q)+4*q) % 2 = 0
      apply Nat.mod_eq_zero_of_dvd
      obtain ⟨t, rfl⟩ := hR
      exact ⟨3*t*q+2*q, by ring⟩
    · simp [dilSeed, hμ]
  have hoff : ∀ b, b ≠ freeBond 2 (dilSeed hq R) → dilBt hq R b = 0 :=
    fun b hb => Pi.single_eq_of_ne hb _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy' x hx b hb
    apply hoff; rintro rfl
    exact freeBond_not_mem_staircase (by norm_num) hdvd (dilSeed hq R) hy y hy'.1 x hx hb
  · intro b hb
    apply hoff; rintro rfl
    obtain ⟨c, _, hc⟩ := hb
    exact freeBond_not_dropped (by norm_num) hdvd (dilSeed hq R) hy ⟨c, hc⟩
  · intro b hb
    by_cases hbe : b = freeBond 2 (dilSeed hq R)
    · exfalso; apply hb; subst b; left
      have hfit : ((dilSeed hq R) 0).val + 2 ≤ dilLu q R 0 + 1 := by
        simp only [dilSeed, ↓reduceIte, dil_unit_size hq]; omega
      have hc := freeBond_coord_zero (dilSeed hq R) hfit (by norm_num : 2 ≤ 2)
      change 3*(R*q)+4*q ≤ _ ∧ _ < 3*(R*q)+6*q
      simp only [dilSeed, ↓reduceIte] at hc
      omega
    · exact hoff b hbe
  · have hne : 0 < ‖dilBt hq R (freeBond 2 (dilSeed hq R))‖ ^ 2 := by
      have hsingle : dilBt hq R (freeBond 2 (dilSeed hq R)) = suTwoWitness := Pi.single_eq_same _ _
      rw [hsingle]; have := suTwoWitness_ne_zero; positivity
    have hs := Finset.single_le_sum (f := fun b : Bond (dilLu q R) => ‖dilBt hq R b‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (freeBond 2 (dilSeed hq R)))
    exact lt_of_lt_of_le hne hs
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.NonVac (clamp1D coord_box_sub coord_box_in isClassCube_of)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                                    
theorem dil_box {q R s t : ℕ} (hq : 0 < q) (hqs : q ≤ s) (ht : s ∣ t)
    (hfit : t + 12*s ≤ 12*(R*q)+16*q) :
    ∃ z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), GridCorner s z ∧
      ∀ y, y ∈ siteBox z (12*s) ↔ t ≤ (y 0).val ∧ (y 0).val < t + 12*s := by
  let z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun μ =>
    ⟨if μ = 0 then t else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩
  have hz0 : (z 0).val = t := by simp [z]
  refine ⟨z, ?_, ?_⟩
  · intro μ
    by_cases hμ : μ = 0
    · subst μ; simpa [hz0] using Nat.mod_eq_zero_of_dvd ht
    · simp [z, hμ]
  · intro y
    constructor
    · intro hy
      have hy0 := hy 0
      simp only [dil_fine_size hq, ↓reduceIte, hz0] at hy0
      exact coord_box_sub hfit (dil_fine_bound hq R y) hy0
    · intro hy μ
      by_cases hμ : μ = 0
      · subst μ
        simp only [dil_fine_size hq, ↓reduceIte, hz0]
        exact coord_box_in hfit hy.1 hy.2
      · have hz : (z μ).val = 0 := by simp [z, hμ]
        simp only [dil_fine_size hq, if_neg hμ, hz]
        have hm := Nat.mod_lt ((y μ).val + 8*q - 0) (by omega : 0 < 8*q)
        omega
theorem dil_region_cube {q R j lo hi v w : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hj : j ≤ 1)
    (hlo : bigSide (2*q) 2 j ∣ lo) (hhi : bigSide (2*q) 2 j ∣ hi)
    (hwid : lo + 12*bigSide (2*q) 2 j ≤ hi) (hhiN : hi ≤ 12*(R*q)+16*q)
    (hvlo : lo ≤ v) (hvw : v ≤ w) (hw1 : w ≤ v + 1) (hwhi : w < hi)
    (hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      lo ≤ (y 0).val → (y 0).val < hi →
      y ∈ towerBj (dilTower q R) j ∪ towerBj (dilTower q R) (j+1))
    (hwit : ∃ u, v ≤ u ∧ u ≤ w ∧ ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      (y 0).val = u → y ∈ towerBj (dilTower q R) j) :
    ∃ sites, IsClassCube 2 (2*q) 12 1 (dilTower q R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        v ≤ (y 0).val → (y 0).val ≤ w → y ∈ sites := by
  have hs : 0 < bigSide (2*q) 2 j := by dsimp [bigSide]; positivity
  have hqs : q ≤ bigSide (2*q) 2 j := by interval_cases j <;> simp [bigSide] <;> omega
  obtain ⟨t, ht, hlot, hthi, htv, hwt⟩ := clamp1D hs hlo hhi hwid hvlo hvw hw1 hwhi
  obtain ⟨z, hz, hbox⟩ := dil_box hq hqs ht (by omega : t + 12*bigSide (2*q) 2 j ≤ 12*(R*q)+16*q)
  refine ⟨siteBox z (12*bigSide (2*q) 2 j), isClassCube_of (dil_admissible hq hR).1
    ⟨hj, ⟨z, hz, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro y hy
    have := (hbox y).mp hy
    exact hreg y (by omega) (by omega)
  · obtain ⟨u, hvu, huw, hu⟩ := hwit
    let y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun μ =>
      ⟨if μ = 0 then u else 0, by rw [dil_fine_size hq]; split_ifs <;> omega⟩
    have hy : (y 0).val = u := by simp [y]
    exact ⟨y, (hbox y).mpr (by rw [hy]; omega), hu y hy⟩
  · intro y hy1 hy2
    exact (hbox y).mpr (by omega)
theorem dil_cube_neighborhood {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hx : x ∈ (dilTower q R).Om 0) :
    ∃ sites j, IsClassCube 2 (2*q) 12 1 (dilTower q R) sites j ∧
      ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        (x 0).val ≤ (y 0).val → (y 0).val ≤ (x 0).val + 1 →
        y ∈ (dilTower q R).Om 0 → y ∈ sites := by
  change (4*q ≤ (x 0).val ∧ (x 0).val < 12*(R*q)+12*q) at hx
  have hRq : 6*q ≤ R*q := Nat.mul_le_mul_right q hR6
  have hp : bigSide (2*q) 2 1 ∣ 2*(R*q)+4*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨t+1, by simp [bigSide]; ring⟩
  have hq' : bigSide (2*q) 2 1 ∣ 10*(R*q)+12*q := by
    obtain ⟨t, rfl⟩ := hR; exact ⟨5*t+3, by simp [bigSide]; ring⟩
  by_cases hcore : 2*(R*q)+4*q ≤ (x 0).val ∧ (x 0).val+1 < 10*(R*q)+12*q
  · obtain ⟨sites, hc, hall⟩ := dil_region_cube (j := 1) (lo := 2*(R*q)+4*q)
      (hi := 10*(R*q)+12*q) (v := (x 0).val) (w := (x 0).val+1)
      hq hR (by omega) hp hq' (by dsimp [bigSide]; omega) (by omega)
      hcore.1 (by omega) le_rfl hcore.2
      (by intro y hy1 hy2; left; simp [towerBj, dilTower]; omega)
      ⟨(x 0).val, le_rfl, by omega, by intro y hy; simp [towerBj, dilTower]; omega⟩
    exact ⟨sites, 1, hc, fun y hy1 hy2 _ => hall y hy1 hy2⟩
  · have hreg : ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        4*q ≤ (y 0).val → (y 0).val < 12*(R*q)+12*q →
        y ∈ towerBj (dilTower q R) 0 ∪ towerBj (dilTower q R) 1 := by
      intro y hy1 hy2
      by_cases h : 2*(R*q)+4*q ≤ (y 0).val ∧ (y 0).val < 10*(R*q)+12*q
      · right; simpa [towerBj, dilTower] using h
      · left; simp [towerBj, dilTower]; omega
    have hwit : ∃ u, (x 0).val ≤ u ∧ u ≤ min ((x 0).val+1) (12*(R*q)+12*q-1) ∧
        ∀ y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), (y 0).val = u →
          y ∈ towerBj (dilTower q R) 0 := by
      by_cases hleft : (x 0).val < 2*(R*q)+4*q
      · refine ⟨(x 0).val, le_rfl, by omega, ?_⟩
        intro y hy; simp [towerBj, dilTower]; omega
      · refine ⟨max (x 0).val (10*(R*q)+12*q), by omega, by omega, ?_⟩
        intro y hy; simp [towerBj, dilTower]; omega
    have hlo : bigSide (2*q) 2 0 ∣ 4*q := ⟨2, by simp [bigSide]; ring⟩
    have hhi : bigSide (2*q) 2 0 ∣ 12*(R*q)+12*q := ⟨6*R+6, by simp [bigSide]; ring⟩
    obtain ⟨sites, hc, hall⟩ := dil_region_cube (j := 0) (lo := 4*q)
      (hi := 12*(R*q)+12*q) (v := (x 0).val) (w := min ((x 0).val+1) (12*(R*q)+12*q-1))
      hq hR (by omega) hlo hhi
      (by dsimp [bigSide]; omega) (by omega) hx.1 (by omega) (by omega) (by omega)
      hreg hwit
    refine ⟨sites, 0, hc, ?_⟩
    intro y hy1 hy2 hy
    change (4*q ≤ (y 0).val ∧ (y 0).val < 12*(R*q)+12*q) at hy
    exact hall y hy1 (by omega)
theorem dil_shift_zero {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (μ : Fin 3) :
    ((periodicLatticeShift x μ) 0).val =
      if μ = 0 then ((x 0).val+1) % (12*(R*q)+16*q) else (x 0).val := by
  by_cases h : μ = 0
  · subst μ
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one',
      dil_fine_size hq, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 12*(R*q)+16*q)]
  · simp [periodicLatticeShift, Function.update_of_ne (Ne.symm h), h]
theorem dil_coverage {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR6 : 6 ≤ R) :
    CoversOm0p 2 (2*q) 12 1 (dilTower q R) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨sites, j, hc, hall⟩ := dil_cube_neighborhood hq hR hR6 x hx
    exact ⟨sites, j, hc, hall x le_rfl (by omega) hx⟩
  · intro p hp
    have hmem : ∀ e : PeriodicLatticeEdge (scaleUp 2 1 (dilLu q R)),
        e ∈ periodicPlaquetteBoundaryEdges p ↔
        e = (p.1, p.2.1.1) ∨ e = (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) ∨
        e = (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) ∨ e = (p.1, p.2.1.2) := by
      intro e; simp [periodicPlaquetteBoundaryEdges]
    have hx := (hp _ ((hmem _).mpr (Or.inl rfl))).1
    obtain ⟨sites, j, hc, hall⟩ := dil_cube_neighborhood hq hR hR6 p.1 hx
    have hxb : (p.1 0).val+2 < 12*(R*q)+16*q := by
      change (4*q ≤ (p.1 0).val ∧ (p.1 0).val < 12*(R*q)+12*q) at hx; omega
    have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
    have ha (μ : Fin 3) :
        (p.1 0).val ≤ ((periodicLatticeShift p.1 μ) 0).val ∧
        ((periodicLatticeShift p.1 μ) 0).val ≤ (p.1 0).val+1 := by
      rw [dil_shift_zero hq]; split_ifs
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · omega
    have hab (μ ν : Fin 3) (hne : μ ≠ ν) :
        (p.1 0).val ≤ ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ∧
        ((periodicLatticeShift (periodicLatticeShift p.1 μ) ν) 0).val ≤ (p.1 0).val+1 := by
      rw [dil_shift_zero hq, dil_shift_zero hq]
      split_ifs <;> simp_all only [Nat.mod_eq_of_lt (by omega : (p.1 0).val+1 < 12*(R*q)+16*q)] <;> omega
    refine ⟨sites, j, hc, ?_⟩
    intro e he
    obtain ⟨h1, h2⟩ := hp e he
    rcases (hmem e).mp he with rfl | rfl | rfl | rfl
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne).1 (hab _ _ hne).2 h2⟩
    · exact ⟨hall _ (ha _).1 (ha _).2 h1, hall _ (hab _ _ hne.symm).1 (hab _ _ hne.symm).2 h2⟩
    · exact ⟨hall p.1 le_rfl (Nat.le_succ _) h1, hall _ (ha _).1 (ha _).2 h2⟩
def dilPattern (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : Prop :=
  (e.1 0).val = 2*(R*q)+4*q ∧ (e.1 1).val % 2 = 0 ∧ (e.1 2).val % 2 = 0 ∧ e.2 = 1
open Classical in
noncomputable def dilU (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e
    else Ug (if dilPattern q R e then ε else 0)
theorem dil_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α ε : ℝ} (hα : 0 < α)
    (hε : |ε| ≤ α/80) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (dilU q R ε V) := by
  classical
  let χ : Bond (scaleUp 2 1 (dilLu q R)) → ℝ := fun e => if dilPattern q R e then 2*ε else 0
  have hχ : ∀ e, |χ e| ≤ α * (((2 : ℝ)^1)⁻¹)^2/10 := by
    intro e; dsimp [χ]; split_ifs
    · rw [abs_mul]; norm_num; linarith
    · norm_num; positivity
  apply perCubeRegular2_congr (dil_admissible hq hR).1 (U := Ufield (((2 : ℝ)^1)⁻¹) χ)
  · intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he.1
    simp only [dilU, if_neg hz, Ufield, χ]
    split_ifs <;> congr 1 <;> norm_num
    ring
  · exact ufield_perCubeRegular2 (by norm_num) (by omega) (by norm_num) _ hα χ hχ
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round4.Guarded.RefuteR1

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                                             
                                                                                                                                  
                                                                                 
end AdalyFormal.Round4.Guarded.RefuteR1

   
                                                                      
                                                                               
  
namespace AdalyFormal.Round5.Guarded.IVTR1

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

                                                                             
                                                                                 
end Abstract

                                                              
noncomputable def twistU (q R : ℕ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  dilU q R ε (AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t)
noncomputable def twistP (q R : ℕ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (twistU q R ε t) a (dilLam q R)
noncomputable def twistA (q R : ℕ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (twistP q R ε a t)).Ginv
noncomputable def twistD (q R : ℕ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (twistP q R ε a t)).Delta2 (dataS_laws selIn selIn _)
section ExteriorPath
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} (hell0 : 0 < ell)
  {S : Tower (scaleUp ell k Lu)} (hS : Admissible ell M R k S)
  (hell : 2 ≤ ell) (hroom : 17 * ell ≤ R * M) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
  (U : ℝ → Cfg (scaleUp ell k Lu))
  (hUU : ∀ (t : ℝ) (e : Bond (scaleUp ell k Lu)),
    e ∉ AdalyFormal.D1Literal.Zb (S.Om 0) → U t e = U 0 e)
include hS hell hroom hUU in
/-- The proof is the frozen DrPath1.Ginv_lit_path proof with the pin's
verbatim selector definitions and qualified frozen locality references. -/
theorem exterior_carrier_path (sJ : PlaqSel) (t : ℝ) :
    (dataS selAll sJ (gparams ell k Lu hell0 S (U t) a Lam)).Ginv =
      (dataS selAll sJ (gparams ell k Lu hell0 S (U 0) a Lam)).Ginv +
      (pE (geomOf ell k S)).comp (((ContinuousLinearMap.adjoint (Wop (geomOf ell k S) (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop (geomOf ell k S) (U 0) a))).comp (iE (geomOf ell k S))) := by
  have hBoth : ∀ e : Bond (scaleUp ell k Lu), BothIn (S.Om 0) e → U t e = U 0 e :=
    fun e he => hUU t e (fun hz => hz.1 he.1)
  have hW := AdalyFormal.D1Literal.Wop_congr_Z hS hell hroom (hUU t) a
  have hT := AdalyFormal.StatementLaneR8.Tfull_congr hS hell hroom hBoth
  have hsec := AdalyFormal.StatementLaneR8.sector_congr hS hell hroom hBoth
  unfold BaseDataS.Ginv dataS
  simp only [gparams, IngrBParams.G, IngrBParams.sector, baseData, DpiFullS, DeltaS, selAll, hW, hT, hsec]
  ext1 y
  simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  abel
end ExteriorPath

                                                                        
                                                               
end AdalyFormal.Round5.Guarded.IVTR1

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open Set
open AdalyFormal.D1Literal (PSD)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

                                                                        
                                                                           
                                                                       
theorem first_carrier_crossing
    (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫)
    (hp0 : PSD (A 0)) (hu0 : IsUnit (A 0))
    (T : ℝ) (hT : 0 < T) (z : E) (hz : ⟪z, A T z⟫ < 0) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧ PSD (A t) ∧ ¬ IsUnit (A t) ∧
      (∀ s : ℝ, 0 ≤ s → s < t → PSD (A s) ∧ IsUnit (A s)) ∧
      ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
  obtain ⟨r, hr0, hrT, hrnu⟩ :=
    AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 T hT z hz
  let K : Set ℝ := Icc 0 r ∩ {t | ¬ IsUnit (A t)}
  have hcl : IsClosed {t : ℝ | ¬ IsUnit (A t)} := by
    exact (Units.isOpen.preimage hc).isClosed_compl
  have hK : IsCompact K := isCompact_Icc.inter_right hcl
  have hrK : r ∈ K := ⟨⟨hr0, le_rfl⟩, hrnu⟩
  obtain ⟨t, htK, htmin⟩ := hK.exists_isLeast ⟨r, hrK⟩
  have htpos : 0 < t := by
    refine lt_of_le_of_ne htK.1.1 ?_
    intro ht
    exact htK.2 (ht ▸ hu0)
  have htT : t < T := lt_of_le_of_lt htK.1.2 hrT
  have hguard : ∀ s : ℝ, 0 ≤ s → s < t → IsUnit (A s) := by
    intro s hs0 hst
    by_contra hnu
    have hsK : s ∈ K := ⟨⟨hs0, le_trans hst.le htK.1.2⟩, hnu⟩
    exact (not_lt_of_ge (htmin hsK)) hst
  have hpsd : ∀ s : ℝ, 0 ≤ s → s ≤ t → PSD (A s) := by
    intro s hs0 hst w
    by_contra hneg
    have hw : ⟪w, A s w⟫ < 0 := lt_of_not_ge hneg
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h | h
      · exact h
      · subst s
        exact False.elim ((not_lt_of_ge (hp0 w)) hw)
    obtain ⟨u, hu0, hus, hnu⟩ :=
      AdalyFormal.D1Literal.exists_nonunit_path A hc hs hp0 s hspos w hw
    exact hnu (hguard u hu0 (lt_of_lt_of_le hus hst))
  have hni : ¬ Function.Injective (A t) := by
    intro hi
    apply htK.2
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := (A t).toLinearMap)).mp hi⟩
  have hk : ∃ v : E, v ≠ 0 ∧ A t v = 0 := by
    by_contra h
    apply hni
    apply (injective_iff_map_eq_zero (A t)).mpr
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  exact ⟨t, htpos, htT, hpsd t htpos.le le_rfl, htK.2,
    fun s hs0 hst => ⟨hpsd s hs0 hst.le, hguard s hs0 hst⟩, hk⟩
end Abstract
end AdalyFormal.Round5.Guarded.IVTR2


namespace AdalyFormal.Round5.Guarded.IVTR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

                                                                          
                                                                               
open Classical in
noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)
theorem masked_regular {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) {α : ℝ} (hα : 0 < α)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hf : ∀ e, |f e| ≤ α/80)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    PerCubeRegular2 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹ (maskedU q R f V) := by
  classical
  let χ : Bond (scaleUp 2 1 (dilLu q R)) → ℝ := fun e => 2*f e
  have hχ : ∀ e, |χ e| ≤ α * (((2 : ℝ)^1)⁻¹)^2/10 := by
    intro e
    dsimp [χ]
    rw [abs_mul]
    norm_num
    linarith [hf e]
  apply perCubeRegular2_congr (dil_admissible hq hR).1 (U := Ufield (((2 : ℝ)^1)⁻¹) χ)
  · intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := fun h => h.1 he.1
    simp only [maskedU, if_neg hz, Ufield, χ]
    congr 1
    norm_num
    ring
  · exact ufield_perCubeRegular2 (by norm_num) (by omega) (by norm_num) _ hα χ hχ
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal (BdPt sing P1 P2)

                                                                
def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩
theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
  have hv : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
    rw [hv]; omega
  · change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_pos rfl, hv, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro z ν hν
    change (4*q ≤ _ ∧ _ < 12*(R*q)+12*q) ↔ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
    rw [dil_shift_zero hq R, if_neg hν]
  · intro ν heq
    have hn : 1 < scaleUp 2 1 (dilLu q R) ν + 1 := by
      rw [dil_fine_size hq]; split_ifs <;> omega
    have hh := congrArg (fun y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) => (y ν).val) heq
    simp only [periodicLatticeShift, Function.update_self, Fin.val_add, Fin.val_one'] at hh
    rw [Nat.mod_eq_of_lt hn] at hh
    have hw := ((rightSite hq R) ν).isLt
    rcases Nat.lt_or_ge (((rightSite hq R) ν).val+1) (scaleUp 2 1 (dilLu q R) ν+1) with h | h
    · rw [Nat.mod_eq_of_lt h] at hh; omega
    · have he : ((rightSite hq R) ν).val+1 = scaleUp 2 1 (dilLu q R) ν+1 := by omega
      rw [he, Nat.mod_self] at hh; omega
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.D1Literal (PSD)

                                                                         
end AdalyFormal.Round5.Guarded.IVTR2

   
                              

                                                                               
                                                                              
                                                                          
                                                                              
                                                                             
                                                                           
                                                                          
                                                               

                                                                     
                                                                      
  
namespace AdalyFormal.Round8.Guarded.SignFree

open scoped RealInnerProductSpace
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

                                                                              
                                                                              
                                                                               
                                       
end Abstract

                                                                           
                                                                           
                                                                           
                                                                              
                                                                           
                                                                           
                                                                               
section Certificates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem unit_of_definite_complements (X : E →L[ℝ] E)
    (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (U V : Submodule ℝ E)
    (hU : ∀ x ∈ U, x ≠ 0 → ⟪x, X x⟫ < 0)
    (hV : ∀ x ∈ V, x ≠ 0 → 0 < ⟪x, X x⟫)
    (hdim : Module.finrank ℝ E ≤ Module.finrank ℝ U + Module.finrank ℝ V) :
    IsUnit X := by
  have hinj : Function.Injective X := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have hxU : x ∉ U := by
      intro hm
      have h := hU x hm hx0
      rw [hx, inner_zero_right] at h
      exact lt_irrefl 0 h
    let U' : Submodule ℝ E := U ⊔ Submodule.span ℝ {x}
    have hneg : ∀ y ∈ U', ⟪y, X y⟫ ≤ 0 := by
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hcross : ⟪c • x, X u⟫ = 0 := by
        rw [real_inner_smul_left, ← hs x u, hx, inner_zero_left, mul_zero]
      have heq : ⟪u + c • x, X (u + c • x)⟫ = ⟪u, X u⟫ := by
        rw [map_add, map_smul, hx, smul_zero, add_zero, inner_add_left, hcross, add_zero]
      rw [heq]
      by_cases hu0 : u = 0
      · rw [hu0, map_zero, inner_zero_right]
      · exact (hU u hu hu0).le
    have hlt : U < U' := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, x, Submodule.mem_sup_right (Submodule.mem_span_singleton_self x), hxU⟩
    have hrk : Module.finrank ℝ U < Module.finrank ℝ U' := Submodule.finrank_lt_finrank_of_lt hlt
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U' V
    have hle : Module.finrank ℝ ↥(U' ⊔ V) ≤ Module.finrank ℝ E := Submodule.finrank_le _
    have hpos : Module.finrank ℝ ↥(U' ⊓ V) ≠ 0 := by omega
    have hne : U' ⊓ V ≠ ⊥ := fun h => hpos (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hneg y (Submodule.mem_inf.mp hy).1
    have h2 := hV y (Submodule.mem_inf.mp hy).2 hy0
    linarith
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : E →ₗ[ℝ] E))).mp hinj⟩
end Certificates

                                                                          
                                                                           
def TwistSeparation (q R : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (twistA q R ε 1 t) ∧ ¬ IsUnit (twistA q R ε 1 t - twistD q R ε 1 t)
def CofinalTwistSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ TwistSeparation (2^j) R ε
theorem goalNeg2_of_cofinalTwistSeparation (h : CofinalTwistSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have heps : |ε| ≤ α/80 := by rw [abs_of_pos hε0]; dsimp [α]; linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (twistU q R ε t) :=
    ⟨dil_coverage hq hR (by omega), dil_regular hq hR hα heps _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    twistU q R ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩
theorem not_cofinalTwistSeparation_of_goalPos1 (h : GoalPos1) : ¬ CofinalTwistSeparation :=
  fun h' => goalNeg2_of_cofinalTwistSeparation h' (goalPos2_iff_goalPos1.mpr h)
end AdalyFormal.Round8.Guarded.SignFree

   
                                                                                         
                                          

                                                                                       
                                                                                         
                                                         
                                                                                          
                                                                                        
                                                                                   
                                                                                     
                                                                                    
                       
                                                                                      
                                                                                     
                                                                                       
                                                                                       
           

                                                                              
                                                                                     
  
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)
open AdalyFormal.Round8.Guarded.SignFree (unit_of_definite_complements)
open AdalyFormal.Round5.Guarded.IVTR2 (first_carrier_crossing)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_op_le (N : E →L[ℝ] E) (u y : E) : |⟪u, N y⟫| ≤ ‖N‖ * ‖u‖ * ‖y‖ := by
  calc |⟪u, N y⟫| ≤ ‖u‖ * ‖N y‖ := abs_real_inner_le_norm u (N y)
    _ ≤ ‖u‖ * (‖N‖ * ‖y‖) := mul_le_mul_of_nonneg_left (N.le_opNorm y) (norm_nonneg u)
    _ = ‖N‖ * ‖u‖ * ‖y‖ := by ring
omit [FiniteDimensional ℝ E] in
theorem perp_lower (A0 X : E →L[ℝ] E) (K : Submodule ℝ E) {g δ : ℝ}
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A0 y⟫) (hδ : ‖X - A0‖ ≤ δ) :
    ∀ y ∈ Kᗮ, (g - δ) * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  intro y hy
  have h1 := hgap y hy
  have h2 := (abs_le.mp (abs_inner_op_le (X - A0) y y)).1
  have h3 : ⟪y, X y⟫ = ⟪y, A0 y⟫ + ⟪y, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right]; ring
  have h4 : ‖X - A0‖ * ‖y‖ * ‖y‖ ≤ δ * ‖y‖ ^ 2 := by
    have hy0 : 0 ≤ ‖y‖ * ‖y‖ := mul_nonneg (norm_nonneg y) (norm_nonneg y)
    calc ‖X - A0‖ * ‖y‖ * ‖y‖ = ‖X - A0‖ * (‖y‖ * ‖y‖) := by ring
      _ ≤ δ * (‖y‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ hy0
      _ = δ * ‖y‖ ^ 2 := by ring
  rw [h3]
  linarith
omit [FiniteDimensional ℝ E] in
theorem cross_upper (A0 X : E →L[ℝ] E) (hs0 : ∀ x y, ⟪A0 x, y⟫ = ⟪x, A0 y⟫)
    (K : Submodule ℝ E) (hker : ∀ u ∈ K, A0 u = 0) {δ : ℝ} (hδ : ‖X - A0‖ ≤ δ) :
    ∀ u ∈ K, ∀ y : E, |⟪u, X y⟫| ≤ δ * ‖u‖ * ‖y‖ := by
  intro u hu y
  have h0 : ⟪u, A0 y⟫ = 0 := by rw [← hs0, hker u hu, inner_zero_left]
  have h3 : ⟪u, X y⟫ = ⟪u, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right, h0, sub_zero]
  rw [h3]
  have huy : 0 ≤ ‖u‖ * ‖y‖ := mul_nonneg (norm_nonneg u) (norm_nonneg y)
  calc |⟪u, (X - A0) y⟫| ≤ ‖X - A0‖ * ‖u‖ * ‖y‖ := abs_inner_op_le _ _ _
    _ = ‖X - A0‖ * (‖u‖ * ‖y‖) := by ring
    _ ≤ δ * (‖u‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ huy
    _ = δ * ‖u‖ * ‖y‖ := by ring
theorem expansion_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (Fe : F) (h0 : f 0 = 0) (h : HasDerivAt f Fe 0) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r → ‖f ε - ε • Fe‖ ≤ η * |ε| := by
  intro η hη
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε hε => ?_⟩
  have hd : dist ε 0 < r := by rw [Real.dist_eq, sub_zero]; exact hε
  have hb := hball hd
  simp only [zero_add, h0, sub_zero, Real.norm_eq_abs] at hb
  exact hb
theorem unit_of_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  refine unit_of_definite_complements X hs ⊥ ⊤ ?_ (fun x _ hx0 => hpos x hx0) ?_
  · intro x hx hx0
    exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
  · simp
omit [FiniteDimensional ℝ E] in
theorem psd_of_pos (X : E →L[ℝ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro x
  by_cases hx : x = 0
  · rw [hx, inner_zero_left]
  · exact (hpos x hx).le
omit [FiniteDimensional ℝ E] in
/-- Positive semidefiniteness at an angle that is a limit of positive definite angles. -/
theorem psd_of_pd_before (F : ℝ → E →L[ℝ] E) (hc : Continuous F) (ts : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, F t₀ x⟫) : PSD (F ts) := by
  intro x
  by_contra hneg
  have hx : ⟪x, F ts x⟫ < 0 := lt_of_not_ge hneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hcont : Continuous fun t => ⟪x, F t x⟫ :=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hev : ∀ᶠ t in nhds ts, ⟪x, F t x⟫ < 0 :=
    Filter.Tendsto.eventually (hcont.tendsto ts) (gt_mem_nhds hx)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨t₀, h1, h2, h3⟩ := h η hη
  have hd : dist t₀ ts < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h4 := hball hd
  have h5 := h3 x hx0
  linarith
theorem exists_gap_of_psd (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (K : Submodule ℝ E) (hK : ∀ v, X v = 0 → v ∈ K) :
    ∃ g : ℝ, 0 < g ∧ ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ y ∈ Kᗮ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E) := by
    intro y hy hy0
    refine ⟨?_, Submodule.smul_mem _ _ hy⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hy0).ne']
  by_cases hne : (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)).Nonempty
  · have hS : IsCompact (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (isCompact_sphere (0 : E) 1).inter_right (Submodule.isClosed_orthogonal K)
    have hcont : ContinuousOn (fun y => ⟪y, X y⟫) (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (continuous_id.inner X.continuous).continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hcont
    have hy₀n : ‖y₀‖ = 1 := mem_sphere_zero_iff_norm.mp hy₀.1
    have hy₀K : y₀ ∈ Kᗮ := hy₀.2
    refine ⟨⟪y₀, X y₀⟫, ?_, ?_⟩
    · rcases (hp y₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have hX0 : X y₀ = 0 := psd_kernel X hs hp y₀ h.symm
        have h0 : ⟪y₀, y₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (hK y₀ hX0) hy₀K
        have hy0 : y₀ = 0 := inner_self_eq_zero.mp h0
        rw [hy0, norm_zero] at hy₀n
        exact zero_ne_one hy₀n
    · intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        simp
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have h1 : ⟪y₀, X y₀⟫ ≤ ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ :=
          isMinOn_iff.mp hmin _ (hunit y hy hy0)
        have h2 : ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ = (‖y‖ ^ 2)⁻¹ * ⟪y, X y⟫ := by
          rw [map_smul, real_inner_smul_left, real_inner_smul_right]
          ring
        rw [h2, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hyn 2)] at h1
        exact h1
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      simp
    · exact absurd ⟨_, hunit y hy hy0⟩ hne
theorem quad_pos {a b g U Y : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g) (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hne : U ≠ 0 ∨ Y ≠ 0) : 0 < a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2 := by
  have hQ : a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) =
      (a * U - b * Y) ^ 2 + (a * g - b ^ 2) * Y ^ 2 := by ring
  have hm : 0 < a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) := by
    rw [hQ]
    by_cases hY0 : Y = 0
    · have hU0 : U ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd hY0 h
      have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
      subst hY0
      have h1 : 0 < (a * U) ^ 2 := pow_pos (mul_pos ha hUp) 2
      have e : (a * U - b * 0) ^ 2 + (a * g - b ^ 2) * 0 ^ 2 = (a * U) ^ 2 := by ring
      rw [e]
      exact h1
    · have hYp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
      have h1 : 0 < (a * g - b ^ 2) * Y ^ 2 := mul_pos (by linarith) (pow_pos hYp 2)
      linarith [sq_nonneg (a * U - b * Y)]
  by_contra hcon
  have h2 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  rw [mul_zero] at h2
  linarith
theorem pos_of_psd_add (A₀ C De R : E →L[ℝ] E) (K : Submodule ℝ E)
    (hs0 : ∀ x y, ⟪A₀ x, y⟫ = ⟪x, A₀ y⟫) (hsC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫)
    (hker : ∀ u ∈ K, A₀ u = 0) {g c δ ε μ κ : ℝ} (hg : 0 < g) (hc : 0 < c)
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A₀ y⟫)
    (hDe : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c)
    (hC : PSD C) (hδ : ‖C - A₀‖ ≤ δ) (hδg : δ ≤ g / 2) (hκδ : κ * δ ≤ 1)
    (hε : 0 < ε) (hκε : κ * ε ≤ 1) (hμ : μ ≤ c / 4) (hR : ‖R‖ ≤ μ * ε) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, (C + ε • De + R) x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hd0 : 0 ≤ ‖De‖ := norm_nonneg _
  have hU0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hμε0 : 0 ≤ μ * ε := le_trans (norm_nonneg _) hR
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  have hκpos : 0 < κ := by
    by_contra hk
    have h1 := mul_le_mul_of_nonneg_right (not_lt.mp hk) (le_of_lt (half_pos hg))
    rw [zero_mul] at h1
    linarith
  have hκε0 : 0 ≤ κ * ε := (mul_pos hκpos hε).le
  -- expansions
  have hC1 : ⟪u + y, C (u + y)⟫ = ⟪u, C u⟫ + 2 * ⟪u, C y⟫ + ⟪y, C y⟫ := by
    have hsym : ⟪y, C u⟫ = ⟪u, C y⟫ := by rw [← hsC y u, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]
    ring
  have hD1 : ⟪u + y, De (u + y)⟫ = ⟪u, De u⟫ + ⟪u, De y⟫ + ⟪y, De u⟫ + ⟪y, De y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have hQ : ⟪u + y, (C + ε • De + R) (u + y)⟫ =
      ⟪u + y, C (u + y)⟫ + ε * ⟪u + y, De (u + y)⟫ + ⟪u + y, R (u + y)⟫ := by
    simp only [add_apply, smul_apply, inner_add_right, real_inner_smul_right]
  -- the bounds
  have hCnn : 0 ≤ ⟪u + y, C (u + y)⟫ := hC _
  have hCu : 0 ≤ ⟪u, C u⟫ := hC u
  have hCuy := (abs_le.mp (cross_upper A₀ C hs0 K hker hδ u hu y)).1
  have hCy := perp_lower A₀ C K hgap hδ y hy
  have hDu := hDe u hu
  have hDuy := (abs_le.mp (abs_inner_op_le De u y)).1
  have hDyu := (abs_le.mp (abs_inner_op_le De y u)).1
  have hDy := (abs_le.mp (abs_inner_op_le De y y)).1
  have hRx : -(μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2))) ≤ ⟪u + y, R (u + y)⟫ := by
    have h1 := (abs_le.mp (abs_inner_op_le R (u + y) (u + y))).1
    have hx0 : 0 ≤ ‖u + y‖ := norm_nonneg _
    have hxn : ‖u + y‖ ≤ ‖u‖ + ‖y‖ := norm_add_le u y
    have h3a : ‖u + y‖ * ‖u + y‖ ≤ (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) :=
      mul_le_mul hxn hxn hx0 (by linarith)
    have e3 : 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) - (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) = (‖u‖ - ‖y‖) ^ 2 := by
      ring
    have h3 : ‖u + y‖ * ‖u + y‖ ≤ 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) := by
      linarith [sq_nonneg (‖u‖ - ‖y‖)]
    have h4 : ‖R‖ * ‖u + y‖ * ‖u + y‖ ≤ μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by
      calc ‖R‖ * ‖u + y‖ * ‖u + y‖ = ‖R‖ * (‖u + y‖ * ‖u + y‖) := by ring
        _ ≤ (μ * ε) * (‖u + y‖ * ‖u + y‖) :=
          mul_le_mul_of_nonneg_right hR (mul_nonneg hx0 hx0)
        _ ≤ (μ * ε) * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 hμε0
        _ = μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by ring
    linarith
  -- a fraction `κ ε` of the form of `C` absorbs the cross terms
  have hw1 : κ * ε * ⟪u + y, C (u + y)⟫ ≤ ⟪u + y, C (u + y)⟫ := by
    have h1 := mul_nonneg (sub_nonneg.mpr hκε) hCnn
    have e : (1 - κ * ε) * ⟪u + y, C (u + y)⟫ =
        ⟪u + y, C (u + y)⟫ - κ * ε * ⟪u + y, C (u + y)⟫ := by ring
    linarith
  have e5 : κ * ε * ⟪u + y, C (u + y)⟫ =
      κ * ε * ⟪u, C u⟫ + 2 * (κ * ε * ⟪u, C y⟫) + κ * ε * ⟪y, C y⟫ := by
    rw [hC1]
    ring
  have e6 : ε * ⟪u + y, De (u + y)⟫ =
      ε * ⟪u, De u⟫ + ε * ⟪u, De y⟫ + ε * ⟪y, De u⟫ + ε * ⟪y, De y⟫ := by
    rw [hD1]
    ring
  have h5a := mul_le_mul_of_nonneg_left hCuy hκε0
  have h5b := mul_le_mul_of_nonneg_left hCy hκε0
  have h5c := mul_nonneg hκε0 hCu
  have h6a := mul_le_mul_of_nonneg_left hDu hε.le
  have h6b := mul_le_mul_of_nonneg_left hDuy hε.le
  have h6c := mul_le_mul_of_nonneg_left hDyu hε.le
  have h6d := mul_le_mul_of_nonneg_left hDy hε.le
  -- the reduced two-variable form is positive
  have hbr : 0 < (c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2 := by
    have ha' : c / 2 ≤ c - 2 * μ := by linarith
    have hgd : κ * (g / 2) ≤ κ * (g - δ) := mul_le_mul_of_nonneg_left (by linarith) hκpos.le
    have hg' : c / 2 + 4 * (‖De‖ + 1) ^ 2 / c ≤ κ * (g - δ) - ‖De‖ - 2 * μ := by linarith
    have hprod : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) ≤
        (c - 2 * μ) * (κ * (g - δ) - ‖De‖ - 2 * μ) :=
      mul_le_mul ha' hg' (by linarith) (by linarith)
    have hcc : c / 2 * (4 * (‖De‖ + 1) ^ 2 / c) = 2 * (‖De‖ + 1) ^ 2 := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero two_ne_zero hc.ne')]
      ring
    have hval : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) =
        c ^ 2 / 4 + 2 * (‖De‖ + 1) ^ 2 := by
      rw [mul_add, hcc]
      ring
    have hb0 : 0 ≤ κ * δ + ‖De‖ := by
      have := mul_nonneg hκpos.le hδ0
      linarith
    have hb1 : κ * δ + ‖De‖ ≤ 1 + ‖De‖ := by linarith
    have hbsq : (κ * δ + ‖De‖) * (κ * δ + ‖De‖) ≤ (1 + ‖De‖) * (1 + ‖De‖) :=
      mul_le_mul hb1 hb1 hb0 (by linarith)
    have hd1 : 0 < (1 + ‖De‖) * (1 + ‖De‖) := by positivity
    have hc2 : 0 ≤ c ^ 2 / 4 := by positivity
    have e7 : (‖De‖ + 1) ^ 2 = (1 + ‖De‖) * (1 + ‖De‖) := by ring
    have e8 : (κ * δ + ‖De‖) ^ 2 = (κ * δ + ‖De‖) * (κ * δ + ‖De‖) := by ring
    refine quad_pos (by linarith) ?_ hU0 hY0 ?_
    · rw [e8]
      linarith [hbsq, hprod, hval, hd1, hc2, e7]
    · by_contra hcon
      apply hx
      have h1 : ‖u‖ = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h2 : ‖y‖ = 0 := by
        by_contra h
        exact hcon (Or.inr h)
      rw [norm_eq_zero.mp h1, norm_eq_zero.mp h2, add_zero]
  have hfin : ε * ((c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2) ≤ ⟪u + y, (C + ε • De + R) (u + y)⟫ := by
    rw [hQ]
    linarith
  have := mul_pos hε hbr
  linarith
omit [FiniteDimensional ℝ E] in
/-- The metric form of joint continuity at a point of zero curvature. -/
theorem metric_of_continuousAt {F : Type*} [SeminormedAddCommGroup F] (f : ℝ → ℝ → F) (t : ℝ)
    (h : ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (0, t)) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
      ‖f ε s - f 0 t‖ < δ := by
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp h δ hδ
  refine ⟨r, hr, fun ε s hε hs => ?_⟩
  have hd : dist ((ε, s) : ℝ × ℝ) (0, t) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hε hs
  have h1 := hball hd
  simp only [dist_eq_norm] at h1
  exact h1
theorem first_order_separation
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hcA : ∀ ε, Continuous (A ε)) (ts : ℝ)
    (hjoint : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖A ε s - A 0 t‖ < δ)
    (hbefore : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, A 0 t₀ x⟫)
    (hafter : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w : E, ⟪w, A 0 t₁ w⟫ < 0)
    (c : ℝ) (De : E →L[ℝ] E) (hc : 0 < c)
    (hDe : ∀ u : E, A 0 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hDexp : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖D ε - ε • De‖ ≤ μ * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t : ℝ, IsUnit (A ε t) ∧ ¬ IsUnit (A ε t - D ε) := by
  have hsC : ∀ ε t x y, ⟪(A ε t - D ε) x, y⟫ = ⟪x, (A ε t - D ε) y⟫ := by
    intro ε t x y
    simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  -- the vacuum carrier at `ts`: positive semidefinite, with a gap off its kernel
  have hpsd : PSD (A 0 ts) := psd_of_pd_before (A 0) (hcA 0) ts hbefore
  obtain ⟨K, hK_def⟩ : ∃ K : Submodule ℝ E, K = LinearMap.ker (A 0 ts : E →ₗ[ℝ] E) := ⟨_, rfl⟩
  have hmemK : ∀ v, v ∈ K ↔ A 0 ts v = 0 := by
    intro v
    rw [hK_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have hker : ∀ u ∈ K, A 0 ts u = 0 := fun u hu => (hmemK u).mp hu
  obtain ⟨g, hg, hgap⟩ := exists_gap_of_psd (A 0 ts) (hsA 0 ts) hpsd K
    (fun v hv => (hmemK v).mpr hv)
  have hDeK : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ :=
    fun u hu => hDe u (hker u hu)
  -- constants
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    rw [hκ_def]
    exact mul_pos (div_pos two_pos hg) (by linarith [norm_nonneg De])
  have hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by
    have h2g : 2 / g * (g / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 g, div_self (mul_ne_zero hg.ne' two_ne_zero)]
    rw [hκ_def]
    calc 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) * (g / 2)
        = (2 / g * (g / 2)) * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := by ring
      _ = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by rw [h2g, one_mul]
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ δ₀ : ℝ, δ₀ = min (g / 2) (1 / κ) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀_def]; exact lt_min (half_pos hg) (one_div_pos.mpr hκpos)
  have hδ₀g : δ₀ ≤ g / 2 := by rw [hδ₀_def]; exact min_le_left _ _
  have hκδ₀ : κ * δ₀ ≤ 1 := by
    have h := min_le_right (g / 2) (1 / κ)
    rw [← hδ₀_def] at h
    calc κ * δ₀ ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left h hκpos.le
      _ = 1 := mul_one_div_cancel hκpos.ne'
  -- the window, the correction size and the endpoints
  obtain ⟨η₀, hη₀, hjoint⟩ := hjoint
  obtain ⟨r₁, hr₁, hA1⟩ := hjoint ts (by simp [hη₀]) (δ₀ / 2) (half_pos hδ₀)
  obtain ⟨r₂, hr₂, hD2⟩ := hDexp (c / 4) (by linarith)
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min r₁ η₀ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact lt_min hr₁ hη₀
  have hρ1 : ρ ≤ r₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρ2 : ρ ≤ η₀ := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨t₀, ht₀a, ht₀b, hpd₀⟩ := hbefore ρ hρ
  obtain ⟨t₁, ht₁a, ht₁b, w, hw⟩ := hafter ρ hρ
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A 0 t₀) (hsA 0 t₀) (psd_of_pos _ hpd₀)
    (unit_of_pos _ (hsA 0 t₀) hpd₀)
  obtain ⟨r₃, hr₃, hA3⟩ := hjoint t₀ (by rw [abs_lt]; constructor <;> linarith) (m / 2)
    (half_pos hm)
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = -⟪w, A 0 t₁ w⟫ := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; linarith
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = ‖w‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hW_def]; positivity
  have hwW : ‖w‖ * ‖w‖ ≤ W := by
    rw [hW_def]
    have e : ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
    rw [e]
    linarith
  obtain ⟨r₄, hr₄, hA4⟩ := hjoint t₁ (by rw [abs_lt]; constructor <;> linarith) (ν / (2 * W))
    (div_pos hν (by linarith))
  obtain ⟨Dc, hDc_def⟩ : ∃ Dc : ℝ, Dc = ‖De‖ + c / 4 + 1 := ⟨_, rfl⟩
  have hDc : 0 < Dc := by rw [hDc_def]; linarith [norm_nonneg De]
  have hDsmall : ∀ ε : ℝ, 0 < ε → ε < r₂ → ‖D ε‖ ≤ Dc * ε := by
    intro ε hε hεr
    have h1 := hD2 ε hε hεr
    have h2 : ‖D ε‖ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := by
      calc ‖D ε‖ = ‖(D ε - ε • De) + ε • De‖ := by rw [sub_add_cancel]
        _ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
    rw [hDc_def]
    linarith
  have h2Dc : 0 < 2 * Dc := by linarith
  have h2WDc : 0 < 2 * W * Dc := mul_pos (mul_pos two_pos hW) hDc
  refine ⟨min (min (min r₁ r₂) (min r₃ r₄))
      (min (min (1 / κ) (δ₀ / (2 * Dc))) (min (m / (2 * Dc)) (ν / (2 * W * Dc)))), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄))
      (lt_min (lt_min (one_div_pos.mpr hκpos) (div_pos hδ₀ h2Dc))
        (lt_min (div_pos hm h2Dc) (div_pos hν h2WDc)))
  intro ε hε hε₀
  have e1 : ε < r₁ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e2 : ε < r₂ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e3 : ε < r₃ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e4 : ε < r₄ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have e5 : ε < 1 / κ := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e6 : ε < δ₀ / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e7 : ε < m / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e8 : ε < ν / (2 * W * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεabs : |ε| = ε := abs_of_pos hε
  have hDε := hDsmall ε hε e2
  have hDε1 : ‖D ε‖ < δ₀ / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e6
    linarith
  have hDε2 : ‖D ε‖ < m / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e7
    linarith
  have hDε3 : ‖D ε‖ * (2 * W) < ν := by
    have h := (lt_div_iff₀ h2WDc).mp e8
    have h' := mul_le_mul_of_nonneg_right hDε (by linarith : (0 : ℝ) ≤ 2 * W)
    linarith
  have hκε : κ * ε ≤ 1 := by
    have h := (lt_div_iff₀ hκpos).mp e5
    linarith
  -- the corrected carrier is positive definite at `t₀`
  have hC0 : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε t₀ - D ε) x⟫ := by
    intro x hx
    have h1 := hmc x
    have h2 : ‖A ε t₀ - A 0 t₀‖ < m / 2 := hA3 ε t₀ (by rw [hεabs]; exact e3) (by simp [hr₃])
    have hxx : 0 < ‖x‖ * ‖x‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hx)
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₀ - A 0 t₀) x x)).1
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) x x)).2
    have e : ⟪x, (A ε t₀ - D ε) x⟫ = ⟪x, A 0 t₀ x⟫ + ⟪x, (A ε t₀ - A 0 t₀) x⟫ - ⟪x, D ε x⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    have h5 := mul_lt_mul_of_pos_right h2 hxx
    have h6 := mul_lt_mul_of_pos_right hDε2 hxx
    have e' : ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    rw [e]
    rw [e'] at h1
    linarith
  -- and has a negative direction at `t₁`
  have hC1 : ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
    have h2 : ‖A ε t₁ - A 0 t₁‖ < ν / (2 * W) := hA4 ε t₁ (by rw [hεabs]; exact e4) (by simp [hr₄])
    have h2' : ‖A ε t₁ - A 0 t₁‖ * (2 * W) < ν := (lt_div_iff₀ (by linarith)).mp h2
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₁ - A 0 t₁) w w)).2
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) w w)).1
    have h5 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (A ε t₁ - A 0 t₁))
    have h6 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (D ε))
    have e : ⟪w, (A ε t₁ - D ε) w⟫ = ⟪w, A 0 t₁ w⟫ + ⟪w, (A ε t₁ - A 0 t₁) w⟫ - ⟪w, D ε w⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    rw [e]
    linarith
  -- the first singular corrected carrier on the window
  have hF : Continuous fun s : ℝ => A ε (t₀ + s) - D ε :=
    ((hcA ε).comp (continuous_const.add continuous_id)).sub continuous_const
  have hT : t₀ + (t₁ - t₀) = t₁ := by ring
  obtain ⟨s, hs0, hsT, hpsdF, hnuF, -, -⟩ := first_carrier_crossing
    (fun s : ℝ => A ε (t₀ + s) - D ε) hF (fun s x y => hsC ε (t₀ + s) x y)
    (by simpa only [add_zero] using psd_of_pos _ hC0)
    (by simpa only [add_zero] using unit_of_pos _ (hsC ε t₀) hC0)
    (t₁ - t₀) (by linarith) w (by simpa only [hT] using hC1)
  have hwin : ‖A ε (t₀ + s) - A 0 ts‖ < δ₀ / 2 := hA1 ε (t₀ + s) (by rw [hεabs]; exact e1)
    (by rw [abs_lt]; constructor <;> linarith)
  have hCδ : ‖(A ε (t₀ + s) - D ε) - A 0 ts‖ ≤ δ₀ := by
    have e : (A ε (t₀ + s) - D ε) - A 0 ts = (A ε (t₀ + s) - A 0 ts) - D ε := by abel
    rw [e]
    calc ‖(A ε (t₀ + s) - A 0 ts) - D ε‖ ≤ ‖A ε (t₀ + s) - A 0 ts‖ + ‖D ε‖ := norm_sub_le _ _
      _ ≤ δ₀ := by linarith
  have hpd := pos_of_psd_add (A 0 ts) (A ε (t₀ + s) - D ε) De (D ε - ε • De)
    K (hsA 0 ts) (hsC ε (t₀ + s)) hker hg hc hgap hDeK hκ hpsdF hCδ
    hδ₀g hκδ₀ hε hκε le_rfl (hD2 ε hε e2)
  have hAeq : (A ε (t₀ + s) - D ε) + ε • De + (D ε - ε • De) = A ε (t₀ + s) := by abel
  refine ⟨t₀ + s, unit_of_pos _ (hsA ε (t₀ + s)) (fun x hx => ?_), hnuF⟩
  have h := hpd x hx
  rwa [hAeq] at h
end Abstract

end AdalyFormal.Round9.Guarded.Qualitative

                                                                                  

                                                                                         
                                                                                         
                                                                                         
                                                                                     
                                                                                       
                             
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

                                                                                       
                             
noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)
noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv
noncomputable def pathD (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (pathP q R V f ε a t)).Delta2 (dataS_laws selIn selIn _)
theorem path_agrees (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε s t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    pathU q R V f ε s e = pathU q R V f ε t e := by
  classical
  simp only [pathU, maskedU, if_neg he]
theorem path_cont (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    AdalyFormal.D1Literal.ContFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact continuous_const
theorem pathA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) :
    Continuous (pathA q R V f ε a) := by
  let G := geomOf 2 1 (dilTower q R)
  let U := pathU q R V f ε
  have h : pathA q R V f ε a = fun t => pathA q R V f ε a 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) a))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) U (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (path_cont q R hV f ε) _
  refine continuous_const.add
    (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const
    (Continuous.clm_comp (hd.sub continuous_const) continuous_const)
theorem path_data_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    dataS selIn selIn (pathP q R V f ε a t) = dataS selIn selIn (pathP q R V f ε a 0) := by
  change (pathP q R V f ε a t).data = (pathP q R V f ε a 0).data
  exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
    (by norm_num) hroom (pathU q R V f ε 0) (pathU q R V f ε t) a (dilLam q R)
    (fun e he => path_agrees q R V f ε 0 t e (fun hz => hz.1 he.1))
theorem pathD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V f ε a t = pathD q R V f ε a 0 := by
  have hd := path_data_constant hq hR hroom V f ε a t
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _
theorem pathD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (a t : ℝ) : pathD q R V f 0 a t = 0 := by
  classical
  let P := pathP q R V f 0 a t
  have hflat : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := by
    intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) :=
      fun h => h.1 he
    change pathU q R V f 0 t e = 1
    simp only [pathU, maskedU, zero_mul, AdalyFormal.StatementLane2.Ug_zero, ite_eq_right_iff]
    intro h
    exact (hz h).elim
  have hg := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    selIn P selIn (dil_admissible hq hR) (by norm_num [P, pathP, gparams]) h3 hflat
  have hid := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hh : (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn P).Ginv := hid.symm.trans hg
  exact sub_eq_self.mp hh
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t
def PathSeparation (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (pathA q R V f ε 1 t) ∧ ¬ IsUnit (pathA q R V f ε 1 t - pathD q R V f ε 1 t)
def CofinalPathSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PathSeparation (2^j) R V f ε
theorem goalNeg2_of_cofinalPathSeparation (h : CofinalPathSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, V, -, f, hf1, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have hmask : ∀ e, |ε * f e| ≤ α/80 := by
    intro e
    rw [abs_mul, abs_of_pos hε0]
    have h1 := hf1 e
    have h2 : ε * |f e| ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε0.le
    dsimp [α]
    linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (pathU q R V f ε t) :=
    ⟨dil_coverage hq hR (by omega), masked_regular hq hR hα (fun e => ε * f e) hmask _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    pathU q R V f ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩
end AdalyFormal.Round9.Guarded.Qualitative

                                                                            

                                                                                    
                                                                                    
                                                                                     
                                                                              
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

                                                                           
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t
theorem pathU_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    pathU q R V f 0 t = pathU q R V (fun _ => 0) 0 t := by
  unfold pathU
  congr 1
  funext e
  simp
theorem pathA_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    pathA q R V f 0 a t = vacA q R V a t := by
  unfold vacA pathA pathP
  rw [pathU_zero]
theorem pathU_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    pathU q R V (fun e => -f e) ε t = pathU q R V f (-ε) t := by
  unfold pathU
  congr 1
  funext e
  simp
theorem pathA_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathA q R V (fun e => -f e) ε a t = pathA q R V f (-ε) a t := by
  unfold pathA pathP
  rw [pathU_neg]
theorem pathD_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V (fun e => -f e) ε a t = pathD q R V f (-ε) a t := by
  have hd : dataS selIn selIn (pathP q R V (fun e => -f e) ε a t) =
      dataS selIn selIn (pathP q R V f (-ε) a t) := by
    unfold pathP
    rw [pathU_neg]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _
def VacuumCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0) ∧
    (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ →
      ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 ∧
    0 < c ∧ ((∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))
theorem eventually_pathSeparation_pos {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hbef : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫)
    (haft : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)
    (hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ)
    (hDx : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖pathD q R V f ε 1 0 - ε • De‖ ≤ μ * ε)
    (hc : 0 < c) (hpos : ∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  have hbef' : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, pathA q R V f 0 1 t₀ x⟫ := by
    intro η hη
    obtain ⟨t₀, h1, h2, h3⟩ := hbef η hη
    exact ⟨t₀, h1, h2, fun x hx => by rw [pathA_zero]; exact h3 x hx⟩
  have haft' : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧
      ∃ w, ⟪w, pathA q R V f 0 1 t₁ w⟫ < 0 := by
    intro η hη
    obtain ⟨t₁, h1, h2, w, hw⟩ := haft η hη
    exact ⟨t₁, h1, h2, w, by rw [pathA_zero]; exact hw⟩
  have hpos' : ∀ u, pathA q R V f 0 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ := by
    intro u hu
    rw [pathA_zero] at hu
    exact hpos u hu
  obtain ⟨ε₀, hε₀, hall⟩ := first_order_separation (fun ε t => pathA q R V f ε 1 t)
    (fun ε => pathD q R V f ε 1 0) hsA hsD (fun ε => pathA_continuous hq hR hroom hV f ε 1)
    ts hj hbef' haft' c De hc hpos' hDx
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hall ε hε hεε
  exact ⟨t, hu, by rwa [pathD_constant hq hR hroom V f ε 1 t]⟩
theorem eventually_pathSeparation_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : VacuumCoupling q R V f) :
    ∃ f' : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f' e| = |f e|) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f' ε := by
  obtain ⟨ts, c, De, hbef, haft, ⟨η₀, hη₀, hjoint⟩, hD, hc, hsign⟩ := h
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨η₀, hη₀, fun t ht => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t (hjoint t ht)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) hD
  rcases hsign with hpos | hneg
  · refine ⟨f, fun e => rfl, ?_⟩
    refine eventually_pathSeparation_pos hq hR hroom hV f ts c De hbef haft hj ?_ hc hpos
    intro μ hμ
    obtain ⟨r, hr, hb⟩ := hDx μ hμ
    refine ⟨r, hr, fun ε hε hεr => ?_⟩
    have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
    rw [abs_of_pos hε] at h1
    exact h1
  · refine ⟨fun e => -f e, fun e => abs_neg (f e), ?_⟩
    have hj' : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
        ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V (fun e => -f e) ε 1 s - pathA q R V (fun e => -f e) 0 1 t‖ < δ := by
      obtain ⟨η₁, hη₁, hj1⟩ := hj
      refine ⟨η₁, hη₁, fun t ht δ hδ => ?_⟩
      obtain ⟨r, hr, hb⟩ := hj1 t ht δ hδ
      refine ⟨r, hr, fun ε s hε hs => ?_⟩
      rw [pathA_neg, pathA_neg, neg_zero]
      exact hb (-ε) s (by rwa [abs_neg]) hs
    have hDx' : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
        ‖pathD q R V (fun e => -f e) ε 1 0 - ε • (-De)‖ ≤ μ * ε := by
      intro μ hμ
      obtain ⟨r, hr, hb⟩ := hDx μ hμ
      refine ⟨r, hr, fun ε hε hεr => ?_⟩
      have h1 := hb (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hεr)
      rw [abs_neg, abs_of_pos hε] at h1
      have e2 : ε • (-De) = (-ε) • De := by
        rw [smul_neg]
        exact (neg_smul ε De).symm
      rw [pathD_neg, e2]
      exact h1
    refine eventually_pathSeparation_pos hq hR hroom hV (fun e => -f e) ts c (-De) hbef haft
      hj' hDx' hc ?_
    intro u hu
    have h1 := hneg u hu
    have e : ⟪u, (-De) u⟫ = -⟪u, De u⟫ := by
      show ⟪u, -(De u)⟫ = -⟪u, De u⟫
      exact inner_neg_right u (De u)
    rw [e]
    exact h1
def CofinalVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      VacuumCoupling (2^j) R V f
theorem cofinalPathSeparation_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨f', hf', ε₀, hε₀, hall⟩ := eventually_pathSeparation_of_coupling hq hR hroom hV hv
  refine ⟨R, hRR, hR, hR18, V, hV, f', fun e => by rw [hf']; exact hf e, fun δ hδ => ?_⟩
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩
theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalVacuumCoupling h)
end AdalyFormal.Round9.Guarded.Qualitative

   
                                                                                            
                                                                                 

                                                                                            
                                                                                            
                                                                                               
                                                                                             
                                                                                               
                                                       
                                                                                          
                                                                                          
                                                                                             
                                                                                              
                                                                                     
                                                                                           
                                                                                     
                                                                                            
                                                                                      
                                                                                            
                                                                                           
                                                                                        

                                                                                       
                                                                                          
          
  
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace ComplexConjugate
open Set Filter Topology
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)

                                                                       

                                                                                 
def AnM (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (θ₀ : ℝ) (i j : Fin 2), AnalyticAt ℝ (fun θ => f θ i j) θ₀
theorem anM_const (M : Matrix (Fin 2) (Fin 2) ℂ) : AnM (fun _ => M) :=
  fun _ _ _ => analyticAt_const
def AnR (g : ℝ → ℝ) : Prop := ∀ θ₀ : ℝ, AnalyticAt ℝ g θ₀
theorem anR_const (c : ℝ) : AnR (fun _ => c) := fun _ => analyticAt_const
theorem AnR.add {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ + g θ) :=
  fun θ₀ => (hf θ₀).fun_add (hg θ₀)
theorem AnR.sub {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ - g θ) :=
  fun θ₀ => (hf θ₀).fun_sub (hg θ₀)
theorem AnR.mul {f g : ℝ → ℝ} (hf : AnR f) (hg : AnR g) : AnR (fun θ => f θ * g θ) :=
  fun θ₀ => (hf θ₀).fun_mul (hg θ₀)
theorem AnR.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, AnR (f i)) :
    AnR (fun θ => ∑ i ∈ s, f i θ) :=
  fun θ₀ => Finset.analyticAt_fun_sum s (fun i hi => h i hi θ₀)
theorem AnM.add {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ + g θ) := by
  intro θ₀ i j
  simp only [Matrix.add_apply]
  exact (hf θ₀ i j).fun_add (hg θ₀ i j)
theorem AnM.sub {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ - g θ) := by
  intro θ₀ i j
  simp only [Matrix.sub_apply]
  exact (hf θ₀ i j).fun_sub (hg θ₀ i j)
theorem AnM.neg {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) : AnM (fun θ => -f θ) := by
  intro θ₀ i j
  simp only [Matrix.neg_apply]
  exact (hf θ₀ i j).fun_neg
theorem AnM.mul {f g : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g) :
    AnM (fun θ => f θ * g θ) := by
  intro θ₀ i j
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun k _ => (hf θ₀ i k).fun_mul (hg θ₀ k j))
theorem AnM.smul {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (c : ℂ) :
    AnM (fun θ => c • f θ) := by
  intro θ₀ i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.fun_mul (hf θ₀ i j)
theorem AnM.star {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnM (fun θ => star (f θ)) := by
  intro θ₀ i j
  simp only [Matrix.star_apply]
  have h1 : AnalyticAt ℝ (fun θ => f θ j i) θ₀ := hf θ₀ j i
  have h2 : AnalyticAt ℝ (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((fun θ => f θ j i) θ₀) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => f θ j i) h2 h1
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]
theorem AnM.trace_re {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) :
    AnR (fun θ => (Matrix.trace (f θ)).re) := by
  intro θ₀
  have htr : AnalyticAt ℝ (fun θ => Matrix.trace (f θ)) θ₀ := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.analyticAt_fun_sum _ (fun i _ => hf θ₀ i i)
  have h2 : AnalyticAt ℝ (Complex.reCLM : ℂ →L[ℝ] ℝ) ((fun θ => Matrix.trace (f θ)) θ₀) :=
    (Complex.reCLM : ℂ →L[ℝ] ℝ).analyticAt _
  have h := AnalyticAt.comp (f := fun θ => Matrix.trace (f θ)) h2 htr
  refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
  simp [Function.comp]
theorem AnM.tr_re3 {f g h : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hf : AnM f) (hg : AnM g)
    (hh : AnM h) : AnR (fun θ => (Matrix.trace (f θ * g θ * h θ)).re) :=
  ((hf.mul hg).mul hh).trace_re
theorem analyticAt_exp_I (s : ℝ) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ : ℝ => Complex.exp (s * θ * Complex.I)) θ₀ := by
  have hlin : AnalyticAt ℝ (fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀ := by
    have h1 : AnalyticAt ℝ (fun θ : ℝ => ((θ : ℂ))) θ₀ :=
      (Complex.ofRealCLM.analyticAt θ₀).congr (Filter.Eventually.of_forall (fun θ => rfl))
    exact (analyticAt_const.fun_mul h1).fun_mul analyticAt_const
  have hexp : AnalyticAt ℝ Complex.exp ((fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) θ₀) :=
    (analyticAt_cexp (z := (s : ℂ) * (θ₀ : ℂ) * Complex.I)).restrictScalars
  exact AnalyticAt.comp (f := fun θ : ℝ => (s : ℂ) * (θ : ℂ) * Complex.I) hexp hlin
section Gram
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

                                                                              
noncomputable def gramDet (A : E →L[ℝ] E) : ℝ :=
  Matrix.det (Matrix.of fun i j =>
    ⟪stdOrthonormalBasis ℝ E i, A (stdOrthonormalBasis ℝ E j)⟫)
theorem gramDet_eq (A : E →L[ℝ] E) : gramDet A = LinearMap.det (A : E →ₗ[ℝ] E) := by
  rw [← LinearMap.det_toMatrix (stdOrthonormalBasis ℝ E).toBasis]
  unfold gramDet
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  rfl
theorem isUnit_iff_gramDet (A : E →L[ℝ] E) : IsUnit A ↔ gramDet A ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det,
    gramDet_eq, isUnit_iff_ne_zero]
theorem analyticAt_gramDet {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀) (θ₀ : ℝ) :
    AnalyticAt ℝ (fun θ => gramDet (A θ)) θ₀ := by
  unfold gramDet
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ (fun σ _ => ?_)
  refine analyticAt_const.fun_mul ?_
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  simp only [Matrix.of_apply]
  exact h _ _ θ₀
theorem isUnit_punctured {A : ℝ → E →L[ℝ] E}
    (h : ∀ (x y : E) (θ₀ : ℝ), AnalyticAt ℝ (fun θ => ⟪x, A θ y⟫) θ₀)
    {t₀ : ℝ} (hu : IsUnit (A t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s) := by
  set g : ℝ → ℝ := fun θ => gramDet (A θ) with hgdef
  have hg : AnalyticOnNhd ℝ g Set.univ := fun θ _ => analyticAt_gramDet h θ
  rcases (hg t (Set.mem_univ t)).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ t) h0 (Set.mem_univ t₀)
    exact ((isUnit_iff_gramDet _).mp hu) hz
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨η, hη, hb⟩ := hne
    refine ⟨η, hη, fun s hs hst => (isUnit_iff_gramDet _).mpr (hb ?_ hs)⟩
    rw [Real.dist_eq]
    exact hst
end Gram

                                                                

section Edge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_le_opNorm (N : E →L[ℝ] E) (x : E) : |⟪x, N x⟫| ≤ ‖N‖ * ‖x‖ ^ 2 := by
  calc |⟪x, N x⟫| ≤ ‖x‖ * ‖N x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖N‖ * ‖x‖) := by gcongr; exact N.le_opNorm x
    _ = ‖N‖ * ‖x‖ ^ 2 := by ring
theorem pos_of_psd_unit (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (hu : IsUnit X) (x : E) (hx : x ≠ 0) : 0 < ⟪x, X x⟫ := by
  rcases (hp x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hk := psd_kernel X hs hp x h.symm
    have hinj : Function.Injective X := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
    exact hx (hinj (by rw [hk, map_zero]))
theorem unit_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  have hi : Function.Injective X := (injective_iff_map_eq_zero X).mpr (by
    intro v hv
    by_contra hn
    have h := hpd v hn
    rw [hv, inner_zero_right] at h
    exact (lt_irrefl 0) h)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective (f := (show E →ₗ[ℝ] E from X))).mp hi⟩
omit [FiniteDimensional ℝ E] in
theorem psd_of_pd (X : E →L[ℝ] E) (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro v
  by_cases hv : v = 0
  · rw [hv]; simp
  · exact (hpd v hv).le
theorem eventually_pd {A : ℝ → E →L[ℝ] E} (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) (t₀ : ℝ)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - t₀| < δ → ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A t₀) (hs t₀) (psd_of_pd _ hpd) (unit_of_pd _ hpd)
  have hct : ContinuousAt A t₀ := hc.continuousAt
  rw [Metric.continuousAt_iff] at hct
  obtain ⟨δ, hδ, hb⟩ := hct (m / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs' x hx => ?_⟩
  have hd : dist (A s) (A t₀) < m / 2 := hb (by rw [Real.dist_eq]; exact hs')
  rw [dist_eq_norm] at hd
  have h1 := hmc x
  have h2 := abs_inner_le_opNorm (A s - A t₀) x
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have e : ⟪x, A s x⟫ = ⟪x, A t₀ x⟫ + ⟪x, (A s - A t₀) x⟫ := by
    rw [show (A s - A t₀) x = A s x - A t₀ x from rfl, inner_sub_right]; ring
  have h3 : ‖A s - A t₀‖ * ‖x‖ ^ 2 ≤ m / 2 * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hd.le hx2.le
  rw [e]
  have := (abs_le.mp h2).1
  nlinarith
noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}
theorem psdEdge_spec (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0)
    (hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (A s)) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ - η < s ∧ s < psdEdge A t₀ t₁ ∧
        ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)} with hS
  have hts' : psdEdge A t₀ t₁ = sSup S := rfl
  set ts := psdEdge A t₀ t₁ with hts
  have hpsd0 : PSD (A t₀) := psd_of_pd _ hpd
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01.le⟩, fun s hs' => by
    rw [le_antisymm hs'.2 hs'.1]; exact hpsd0⟩
  have hne : S.Nonempty := ⟨t₀, h0S⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hts0 : t₀ ≤ ts := by rw [hts']; exact le_csSup hbdd h0S
  have hts1 : ts ≤ t₁ := by rw [hts']; exact csSup_le hne (fun t ht => ht.1.2)
  obtain ⟨δ, hδ, hpdn⟩ := eventually_pd hc hs t₀ hpd
  have hδS : min (t₀ + δ / 2) t₁ ∈ S := by
    refine ⟨⟨le_min (by linarith) h01.le, min_le_right _ _⟩, fun s hs' => ?_⟩
    have hs1 : s ≤ t₀ + δ / 2 := le_trans hs'.2 (min_le_left _ _)
    exact psd_of_pd _ (hpdn s (by rw [abs_lt]; constructor <;> linarith [hs'.1]))
  have hts0' : t₀ < ts := by
    have h1 : t₀ < min (t₀ + δ / 2) t₁ := lt_min (by linarith) h01
    have h2 : min (t₀ + δ / 2) t₁ ≤ ts := by rw [hts']; exact le_csSup hbdd hδS
    linarith
  have hlt : ∀ s, t₀ ≤ s → s < ts → PSD (A s) := by
    intro s hs0 hs1
    rw [hts'] at hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hpsd_ts : PSD (A ts) := by
    intro v
    have hsub : Ico t₀ ts ⊆ {s : ℝ | 0 ≤ ⟪v, A s v⟫} := fun s hs' => hlt s hs'.1 hs'.2 v
    have hcl : IsClosed {s : ℝ | 0 ≤ ⟪v, A s v⟫} := isClosed_le continuous_const (by fun_prop)
    have hcs := hcl.closure_subset_iff.mpr hsub
    exact hcs (by rw [closure_Ico hts0'.ne]; exact ⟨hts0, le_rfl⟩)
  have hle : ∀ s, t₀ ≤ s → s ≤ ts → PSD (A s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have hts1' : ts < t₁ := by
    rcases hts1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts w
      rw [h] at this
      linarith
  have haft : ∀ η : ℝ, 0 < η → ∃ s, ts < s ∧ s < ts + η ∧ ∃ v, ⟪v, A s v⟫ < 0 := by
    intro η hη
    set t' := min (ts + η / 2) t₁ with ht'
    have ht'1 : ts < t' := lt_min (by linarith) hts1'
    have hnot : t' ∉ S := by
      intro h
      have : t' ≤ ts := by rw [hts']; exact le_csSup hbdd h
      linarith
    have hnall : ¬ ∀ s ∈ Icc t₀ t', PSD (A s) := fun hall =>
      hnot ⟨⟨by linarith, min_le_right _ _⟩, hall⟩
    push Not at hnall
    obtain ⟨s, hs', hns⟩ := hnall
    have hsts : ts < s := by
      by_contra hcon
      push Not at hcon
      exact hns (hle s hs'.1 hcon)
    have hst' : s < ts + η := lt_of_le_of_lt (le_trans hs'.2 (min_le_left _ _)) (by linarith)
    unfold PSD at hns
    push Not at hns
    exact ⟨s, hsts, hst', hns⟩
  have hnu : ¬ IsUnit (A ts) := by
    intro hu
    have hpdts : ∀ x, x ≠ 0 → 0 < ⟪x, A ts x⟫ := fun x hx =>
      pos_of_psd_unit _ (hs ts) hpsd_ts hu x hx
    obtain ⟨δ', hδ', hb⟩ := eventually_pd hc hs ts hpdts
    obtain ⟨s, h1, h2, v, hv⟩ := haft δ' hδ'
    have hsd := hb s (by rw [abs_lt]; constructor <;> linarith)
    by_cases hv0 : v = 0
    · rw [hv0] at hv; simp at hv
    · linarith [hsd v hv0]
  have hbef : ∀ η : ℝ, 0 < η → ∃ s, ts - η < s ∧ s < ts ∧ ∀ x, x ≠ 0 → 0 < ⟪x, A s x⟫ := by
    intro η hη
    obtain ⟨η', hη', hiso'⟩ := hiso ts
    set r := min (min η η') (ts - t₀) with hr
    have hr0 : 0 < r := lt_min (lt_min hη hη') (by linarith)
    have hr1 : r ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr2 : r ≤ η' := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr3 : r ≤ ts - t₀ := min_le_right _ _
    refine ⟨ts - r / 2, by linarith, by linarith, fun x hx => ?_⟩
    have hu := hiso' (ts - r / 2) (by intro h; linarith)
      (by rw [abs_lt]; constructor <;> linarith)
    exact pos_of_psd_unit _ (hs _) (hle _ (by linarith) (by linarith)) hu x hx
  exact ⟨hts0', hts1', hpsd_ts, hnu, hle, hbef, haft⟩
end Edge

end AdalyFormal.Round9.Guarded.QualitativeR2

                                                              

                                                                                        
                                                                                       
                                                                                      
                                                                                           
                                                                                         
                                      
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant suTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent}

                                                                                       
def AnFam (U : ℝ → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, AnM fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
section
variable {U : ℝ → PeriodicLinkConfiguration SU2m L} (hU : AnFam U)
include hU

theorem an_inv_coe (e : PeriodicLatticeEdge L) :
    AnM fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => (((U θ e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (hU e).star
theorem an_holonomyElem (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U θ (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U θ (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    rfl
  rw [this]
  exact (((hU _).mul (hU _)).mul (an_inv_coe hU _)).mul (an_inv_coe hU _)
theorem an_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    AnM fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((holonomyElemInv (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => star ((holonomyElem (U θ) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ; rfl
  rw [this]
  exact (an_holonomyElem hU p).star
theorem an_reHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => reHolonomy (U θ) p := by
  unfold reHolonomy
  exact ((an_holonomyElem hU p).add (an_holonomyElemInv hU p)).smul _
theorem an_imHolonomy (p : PeriodicLatticePlaquette L) : AnM fun θ => imHolonomy (U θ) p := by
  unfold imHolonomy
  exact ((an_holonomyElem hU p).sub (an_holonomyElemInv hU p)).smul _
theorem an_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    AnM fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun θ => ((RMap (U θ e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext θ
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U θ e) X
  rw [this]
  exact ((hU e).mul (anM_const _)).mul (hU e).star
theorem an_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => curlMatLM (U θ) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((anM_const _).add (an_RMap hU _ _)).sub (an_RMap hU _ _)).sub (anM_const _)
theorem an_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a1LM (U θ) p A := by
  show AnM fun θ =>
    -(bondMatRLM (U θ (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (an_RMap hU _ _).neg
theorem an_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    AnM fun θ => a4LM (U θ) p A := by
  show AnM fun θ =>
    bondMatRLM (U θ (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact an_RMap hU _ _
theorem an_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    AnR fun θ => bilPlaq (U θ) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : ℝ → Matrix (Fin 2) (Fin 2) ℂ}, AnM f → AnM fun θ => smulILM (f θ) := by
    intro f hf
    exact hf.smul Complex.I
  have b1A : AnM fun θ => b1LM (U θ) p A := hI (an_a1 hU p A)
  have b4B : AnM fun θ => b4LM (U θ) p B := hI (an_a4 hU p B)
  have hre := an_reHolonomy hU p
  have him := an_imHolonomy hU p
  have hcA : AnM fun θ => smulILM (curlMatLM (U θ) p A) := hI (an_curlMat hU p A)
  have hcB : AnM fun θ => smulILM (curlMatLM (U θ) p B) := hI (an_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), AnM fun _ : ℝ => M := fun M => anM_const M
  exact ((((((AnM.tr_re3 hcA hcB (hre.sub (k 1))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) (k _) him).sub (AnM.tr_re3 (k _) b1A him))).add
    ((AnM.tr_re3 (hI b1A) b4B him).sub (AnM.tr_re3 (hI b4B) b1A him))).add
    ((AnM.tr_re3 (k _) (k _) him).sub (AnM.tr_re3 (k _) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))).add
    ((AnM.tr_re3 (k _) b4B him).sub (AnM.tr_re3 (hI b4B) (k _) him))
open Classical in
theorem an_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    AnR fun θ => deltaPrimeBilNormLoc (U θ) P A B := by
  have h : ∀ A B : Bond L → SuTwo, AnR fun θ => deltaPrimeBilRawLoc (U θ) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact AnR.sum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact an_bilPlaq hU p A B
      · simp only [hp, if_false]; exact anR_const 0)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact (anR_const _).mul ((anR_const _).mul ((h A B).add (h B A)))
open Classical in
theorem an_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U θ) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine AnR.sum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show AnR fun θ => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U θ) (WithLp.ofLp x) p) (curlValueCovariant (U θ) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    exact (anR_const _).mul
      ((an_curlMat hU p (WithLp.ofLp x)).mul (an_curlMat hU p (WithLp.ofLp y))).trace_re
  · simp only [hp, if_false, inner_zero_left]
    exact anR_const 0
theorem an_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    AnR fun θ => (inner ℝ x (deltaKLocCLM (U θ) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (an_curlInner hU P x y).add (an_deltaPrimeBil hU P _ _)
end

                                                          
theorem anM_uMat : AnM fun θ => AdalyFormal.D1Literal.uMat θ := by
  intro θ₀ i j
  fin_cases i <;> fin_cases j
  · refine (analyticAt_exp_I 1 θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · simp only [AdalyFormal.D1Literal.uMat]
    simp
    exact analyticAt_const
  · refine (analyticAt_exp_I (-1) θ₀).congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [AdalyFormal.D1Literal.uMat]
section Param
variable {Y : Type*} [TopologicalSpace Y]

                                                                                          
                                                        
def ContFamY (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
include hU

theorem contY_inv_coe (e : PeriodicLatticeEdge L) :
    Continuous fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => (((U y e)⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (hU e).star
theorem contY_holonomyElem (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y (p.1, p.2.1.1) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U y (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ : SU2m) :
          Matrix (Fin 2) (Fin 2) ℂ) *
        (((U y (p.1, p.2.1.2))⁻¹ : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    rfl
  rw [this]
  exact (((hU _).matrix_mul (hU _)).matrix_mul (contY_inv_coe hU _)).matrix_mul
    (contY_inv_coe hU _)
theorem contY_holonomyElemInv (p : PeriodicLatticePlaquette L) :
    Continuous fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((holonomyElemInv (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => star ((holonomyElem (U y) p : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y; rfl
  rw [this]
  exact (contY_holonomyElem hU p).star
theorem contY_reHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => reHolonomy (U y) p := by
  unfold reHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).add (contY_holonomyElemInv hU p))
theorem contY_imHolonomy (p : PeriodicLatticePlaquette L) :
    Continuous fun y => imHolonomy (U y) p := by
  unfold imHolonomy
  exact continuous_const.smul ((contY_holonomyElem hU p).sub (contY_holonomyElemInv hU p))
theorem contY_RMap (e : PeriodicLatticeEdge L) (X : SuTwo) :
    Continuous fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have : (fun y => ((RMap (U y e) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun y => ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((U y e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext y
    exact AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply (U y e) X
  rw [this]
  exact ((hU e).matrix_mul continuous_const).matrix_mul (hU e).star
theorem contY_curlMat (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => curlMatLM (U y) p A := by
  simp only [curlMatLM_apply]
  unfold curlValueCovariant
  simp only [Submodule.coe_add, Submodule.coe_sub]
  exact (((continuous_const.add (contY_RMap hU _ _)).sub (contY_RMap hU _ _)).sub
    continuous_const)
theorem contY_a1 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a1LM (U y) p A := by
  show Continuous fun y =>
    -(bondMatRLM (U y (p.1, p.2.1.2)) (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) A)
  simp only [bondMatRLM_apply]
  exact (contY_RMap hU _ _).neg
theorem contY_a4 (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    Continuous fun y => a4LM (U y) p A := by
  show Continuous fun y =>
    bondMatRLM (U y (p.1, p.2.1.1)) (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) A
  simp only [bondMatRLM_apply]
  exact contY_RMap hU _ _
omit hU in
theorem contY_tr_re3 {f g h : Y → Matrix (Fin 2) (Fin 2) ℂ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    Continuous fun y => (Matrix.trace (f y * g y * h y)).re :=
  Complex.continuous_re.comp (((hf.matrix_mul hg).matrix_mul hh).matrix_trace)
theorem contY_bilPlaq (p : PeriodicLatticePlaquette L) (A B : Bond L → SuTwo) :
    Continuous fun y => bilPlaq (U y) p A B := by
  simp only [bilPlaq_atoms]
  have hI : ∀ {f : Y → Matrix (Fin 2) (Fin 2) ℂ}, Continuous f →
      Continuous fun y => smulILM (f y) := by
    intro f hf
    exact continuous_const.smul hf
  have b1A : Continuous fun y => b1LM (U y) p A := hI (contY_a1 hU p A)
  have b4B : Continuous fun y => b4LM (U y) p B := hI (contY_a4 hU p B)
  have hre := contY_reHolonomy hU p
  have him := contY_imHolonomy hU p
  have hcA : Continuous fun y => smulILM (curlMatLM (U y) p A) := hI (contY_curlMat hU p A)
  have hcB : Continuous fun y => smulILM (curlMatLM (U y) p B) := hI (contY_curlMat hU p B)
  have k : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ), Continuous fun _ : Y => M :=
    fun M => continuous_const
  refine ((((((contY_tr_re3 hcA hcB (hre.sub (k 1))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) (k _) him).sub (contY_tr_re3 (k _) b1A him))).add
    ((contY_tr_re3 (hI b1A) b4B him).sub (contY_tr_re3 (hI b4B) b1A him))).add
    ((contY_tr_re3 (k _) (k _) him).sub (contY_tr_re3 (k _) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))).add
    ((contY_tr_re3 (k _) b4B him).sub (contY_tr_re3 (hI b4B) (k _) him))
open Classical in
theorem contY_deltaPrimeBil (P : Set (PeriodicLatticePlaquette L)) (A B : Bond L → SuTwo) :
    Continuous fun y => deltaPrimeBilNormLoc (U y) P A B := by
  have h : ∀ A B : Bond L → SuTwo, Continuous fun y => deltaPrimeBilRawLoc (U y) P A B := by
    intro A B
    simp only [deltaPrimeBilRawLoc_apply]
    exact continuous_finsetSum _ (fun p _ => by
      by_cases hp : p ∈ P
      · simp only [hp, if_true]; exact contY_bilPlaq hU p A B
      · simp only [hp, if_false]; exact continuous_const)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  exact continuous_const.mul (continuous_const.mul ((h A B).add (h B A)))
open Classical in
theorem contY_curlInner (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w =>
      (inner ℝ (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) x))
        (plaqMask P (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 (U w) y)) : ℝ) := by
  simp only [PiLp.inner_apply]
  refine continuous_finsetSum _ (fun p _ => ?_)
  simp only [plaqMask_apply]
  by_cases hp : p ∈ P
  · simp only [hp, if_true]
    show Continuous fun w => AdalyFormal.Balaban.SuTwoInner.hsInner
      (curlValueCovariant (U w) (WithLp.ofLp x) p) (curlValueCovariant (U w) (WithLp.ofLp y) p)
    unfold AdalyFormal.Balaban.SuTwoInner.hsInner
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    exact ((contY_curlMat hU p (WithLp.ofLp x)).matrix_mul
      (contY_curlMat hU p (WithLp.ofLp y))).matrix_trace
  · simp only [hp, if_false, inner_zero_left]
    exact continuous_const
theorem contY_inner_delta (P : Set (PeriodicLatticePlaquette L)) (x y : BondFnL2 L) :
    Continuous fun w => (inner ℝ x (deltaKLocCLM (U w) P y) : ℝ) := by
  simp only [inner_deltaKLocCLM]
  exact (contY_curlInner hU P x y).add (contY_deltaPrimeBil hU P _ _)
end

theorem contY_deltaKLocCLM {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamY U)
    (P : Set (PeriodicLatticePlaquette L)) : Continuous fun w => deltaKLocCLM (U w) P :=
  AdalyFormal.D1Literal.continuous_clm_of_inner (fun x y => contY_inner_delta hU P x y)
end Param

end AdalyFormal.Round9.Guarded.QualitativeR2

                                                                                

                                                                                       
                                                                                   
                                                                                    
                                                                                          
                                                                                              
                                                                                           
                                                                                            
                                                                         
                                                                                             
                                                                                               
                                                                                          
                                                                                   
                                                                                          
                                                          
                                                                                          
                                                                                     
                                                                                          
                                                                
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

                                            

                                                                                                
theorem pathU_anFam (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : AnFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact anM_const _
theorem uthPath_zero (q R : ℕ) : uthPath q R 0 = fun _ => 1 :=
  AdalyFormal.D1Literal.Uth_zero _
theorem pathA_anR {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ)
    (x y : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    AnR (fun t => ⟪x, pathA q R V f ε a t y⟫) := by
  have h : ∀ t, pathA q R V f ε a t = pathA q R V f ε a 0 +
      (pE (geomOf 2 1 (dilTower q R))).comp (((ContinuousLinearMap.adjoint
        (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ)).comp
          (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a))).comp
        (iE (geomOf 2 1 (dilTower q R)))) :=
    fun t => exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) (pathU q R V f ε) (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  have he : ∀ t, ⟪x, pathA q R V f ε a t y⟫ = ⟪x, pathA q R V f ε a 0 y⟫ +
      (⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε t) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫ -
        ⟪Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a (iE (geomOf 2 1 (dilTower q R)) x),
          AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f ε 0) Set.univ
            (Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) a
              (iE (geomOf 2 1 (dilTower q R)) y))⟫) := by
    intro t
    rw [h t]
    simp only [add_apply, ContinuousLinearMap.comp_apply, inner_add_right, pE_inner_right,
      ContinuousLinearMap.adjoint_inner_right, sub_apply, inner_sub_right]
  rw [funext he]
  exact (anR_const _).add
    ((an_inner_delta (pathU_anFam q R hV f ε) Set.univ _ _).sub (anR_const _))
theorem pathA_isolated {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hV : AnFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) {t₀ : ℝ}
    (hu : IsUnit (pathA q R V f ε a t₀)) (t : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (pathA q R V f ε a s) :=
  isUnit_punctured (fun x y θ₀ => pathA_anR hq hR hroom hV f ε a x y θ₀) hu t
theorem inner_Ginv_dataS (sD sJ : PlaqSel) (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS sD sJ P).Ginv x⟫ =
      ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G)
        (Wop P.G P.U P.a (iE P.G x))⟫ + ‖(dataS sD sJ P).T x‖ ^ 2 +
      ⟪x, (dataS sD sJ P).Mass x⟫ := by
  have hD : ⟪x, (dataS sD sJ P).Dpi x⟫ = ⟪Wop P.G P.U P.a (iE P.G x),
      AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (sD _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    show ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x⟫ = _
    simp only [ContinuousLinearMap.comp_apply, DpiFullS, DeltaS]
    rw [pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  rw [BaseDataS.inner_Ginv, hD]
theorem flat_delta_le_univ {L : PeriodicLatticeExtent} (P : Set (PeriodicLatticePlaquette L))
    (y : BondFnL2 L) :
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) P y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM (fun _ => 1) Set.univ y⟫ := by
  have h1 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU P _ _
  have h2 : AdalyFormal.StatementLaneR6.deltaPrimeBilL2NormLoc
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y y = 0 :=
    AdalyFormal.StatementLaneR6.deltaPrimeBilNormLoc_trivialU Set.univ _ _
  change ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) P y⟫ ≤
    ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (AdalyFormal.Balaban.DeltaPrime.trivialU (L := L)) Set.univ y⟫
  rw [AdalyFormal.StatementLaneR6.inner_deltaKLocCLM,
    AdalyFormal.StatementLaneR6.inner_deltaKLocCLM, h1, h2, add_zero, add_zero,
    AdalyFormal.StatementLaneR6.plaqMask_univ]
  simp only [PiLp.inner_apply, AdalyFormal.StatementLaneR6.plaqMask_apply]
  refine Finset.sum_le_sum (fun p _ => ?_)
  by_cases hp : p ∈ P
  · simp only [hp, if_true, le_refl]
  · simp only [hp, if_false, inner_zero_left]
    exact real_inner_self_nonneg
theorem mass_nonneg_dataS (sD sJ : PlaqSel) (P : IngrBParams) (ha : 0 ≤ P.a)
    (x : ↥(bondSupp P.G)) : 0 ≤ ⟪x, (dataS sD sJ P).Mass x⟫ := by
  show 0 ≤ ⟪x, ((pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G))) x⟫
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pE_inner_right,
    inner_MassFull]
  refine Finset.sum_nonneg (fun p _ => ?_)
  have h1 : (0 : ℝ) ≤ (P.G.ell : ℝ) ^ (p.1 : ℕ) := pow_nonneg (Nat.cast_nonneg _) _
  exact mul_nonneg (mul_nonneg ha h1) (sq_nonneg _)
theorem Ginv_loc_psd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a) :
    PSD (dataS selIn selIn P).Ginv := by
  intro x
  rw [inner_Ginv_dataS]
  have h1 : 0 ≤ ⟪Wop P.G P.U P.a (iE P.G x), AdalyFormal.StatementLaneR6.deltaKLocCLM P.U
      (selIn _ P.G) (Wop P.G P.U P.a (iE P.G x))⟫ := by
    generalize Wop P.G P.U P.a (iE P.G x) = y
    rw [hU]
    exact AdalyFormal.StatementLaneR6.deltaKLocCLM_flat_nonneg _ y
  have h2 := mass_nonneg_dataS selIn selIn P ha x
  have h3 := sq_nonneg ‖(dataS selIn selIn P).T x‖
  linarith
theorem Ginv_loc_le_all_flat (P : IngrBParams) (hU : P.U = fun _ => 1)
    (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤ ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  rw [inner_Ginv_dataS, inner_Ginv_dataS]
  have hT : (dataS selIn selIn P).T = (dataS selAll selAll P).T := rfl
  have hM : (dataS selIn selIn P).Mass = (dataS selAll selAll P).Mass := rfl
  rw [hT, hM]
  have key : ∀ y, ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selIn _ P.G) y⟫ ≤
      ⟪y, AdalyFormal.StatementLaneR6.deltaKLocCLM P.U (selAll _ P.G) y⟫ := by
    intro y
    rw [hU]
    exact flat_delta_le_univ _ y
  linarith [key (Wop P.G P.U P.a (iE P.G x))]
theorem Ginv_all_pd_flat (P : IngrBParams) (hU : P.U = fun _ => 1) (ha : 0 ≤ P.a)
    (hu : IsUnit (dataS selIn selIn P).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  intro x hx
  have h1 := pos_of_psd_unit _ ((dataS selIn selIn P).Ginv_symm (dataS_laws selIn selIn P))
    (Ginv_loc_psd_flat P hU ha) hu x hx
  exact lt_of_lt_of_le h1 (Ginv_loc_le_all_flat P hU x)
noncomputable def flatP (q R : ℕ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)
theorem pathU_flat_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R V f 0 0 = fun _ => 1 := by
  classical
  funext e
  simp only [pathU, maskedU, hV0, zero_mul, Ug_zero, ite_self]
theorem vacA_zero_flat (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) : vacA q R V 1 0 = (dataS selAll selAll (flatP q R)).Ginv := by
  unfold vacA pathA pathP flatP
  rw [pathU_flat_base q R hV0 (fun _ => 0)]
theorem vacA_pd_zero {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv) :
    ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫ := by
  rw [vacA_zero_flat q R hV0]
  exact Ginv_all_pd_flat (flatP q R) rfl zero_le_one hloc
noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi
def VacuumCrossesAt (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (ts : ℝ) : Prop :=
  0 < ts ∧ ts < Real.pi ∧ PSD (vacA q R V 1 ts) ∧ ¬ IsUnit (vacA q R V 1 ts) ∧
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)
theorem vacuum_crossing {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hpd0 : ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 0 x⟫)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0) :
    VacuumCrossesAt q R V (vacEdge q R V) := by
  obtain ⟨w, hw⟩ := hneg
  have hc : Continuous (vacA q R V 1) := pathA_continuous hq hR hroom hVc (fun _ => 0) 0 1
  have hs : ∀ t x y, ⟪vacA q R V 1 t x, y⟫ = ⟪x, vacA q R V 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (dataS_laws selAll selAll _) x y
  have hiso : ∀ t, ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ t → |s - t| < η → IsUnit (vacA q R V 1 s) :=
    fun t => pathA_isolated hq hR hroom hVa (fun _ => 0) 0 1 (t₀ := 0) (unit_of_pd _ hpd0) t
  obtain ⟨h1, h2, h3, h4, -, h6, h7⟩ :=
    psdEdge_spec (vacA q R V 1) hc hs Real.pi_pos hpd0 w hw hiso
  exact ⟨h1, h2, h3, h4, h6, h7⟩
theorem uMat_continuous' : Continuous fun θ : ℝ => AdalyFormal.D1Literal.uMat θ := by
  unfold AdalyFormal.D1Literal.uMat
  refine continuous_matrix (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop
theorem Ug_coe_uMat (t : ℝ) :
    ((Ug t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      AdalyFormal.D1Literal.uMat t := by
  show NormedSpace.exp (Xm t) = _
  have hX : Xm t = Matrix.diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xm, sig, Matrix.diagonal]
  rw [hX, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.diagonal, ← Complex.exp_eq_exp_ℂ]
theorem pathU_contFamY (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFamY (fun p : ℝ × ℝ => pathU q R V f p.1 p.2) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact (hV e).comp continuous_snd
  · simp only [pathU, maskedU, if_neg he, Ug_coe_uMat]
    exact uMat_continuous'.comp (continuous_fst.mul continuous_const)
theorem pathA_jointly_continuousAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (hA0 : ContinuousAt (fun ε : ℝ => pathA q R V f ε 1 0) 0)
    (hW0 : ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) 0)
    (t : ℝ) : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  let G := geomOf 2 1 (dilTower q R)
  let Wf : ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun ε => Wop G (pathU q R V f ε 0) 1
  let Δf : ℝ × ℝ → BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ] BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
    fun p => AdalyFormal.StatementLaneR6.deltaKLocCLM (pathU q R V f p.1 p.2) Set.univ
  have hpath : ∀ p : ℝ × ℝ, pathA q R V f p.1 1 p.2 = pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) := fun p =>
    exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      1 (dilLam q R) (pathU q R V f p.1) (fun s e he => path_agrees q R V f p.1 s 0 e he)
      selAll p.2
  rw [show (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) = fun p => pathA q R V f p.1 1 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wf p.1)).comp
        ((Δf p - Δf (p.1, 0)).comp (Wf p.1))).comp (iE G)) from funext hpath]
  have hΔ : Continuous Δf := contY_deltaKLocCLM (pathU_contFamY q R hV f) _
  have hA : ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 0) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hA0 continuousAt_fst
  have hW : ContinuousAt (fun p : ℝ × ℝ => Wf p.1) (0, t) :=
    ContinuousAt.comp (f := Prod.fst) (x := ((0 : ℝ), t)) hW0 continuousAt_fst
  have hadj : Continuous (fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => ContinuousLinearMap.adjoint M) :=
    (ContinuousLinearMap.adjoint : (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R))) ≃ₗᵢ⋆[ℝ] (BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)))).continuous
  have hWa : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.adjoint (Wf p.1)) (0, t) :=
    hadj.continuousAt.comp hW
  have hD : ContinuousAt (fun p : ℝ × ℝ => Δf p - Δf (p.1, 0)) (0, t) :=
    hΔ.continuousAt.sub ((hΔ.comp (continuous_fst.prodMk continuous_const)).continuousAt)
  have hmid : ContinuousAt (fun p : ℝ × ℝ => (ContinuousLinearMap.adjoint (Wf p.1)).comp
      ((Δf p - Δf (p.1, 0)).comp (Wf p.1))) (0, t) := hWa.clm_comp (hD.clm_comp hW)
  have hout : Continuous fun M : BondFnL2 (scaleUp 2 1 (dilLu q R)) →L[ℝ]
      BondFnL2 (scaleUp 2 1 (dilLu q R)) => (pE G).comp (M.comp (iE G)) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  exact hA.add (hout.continuousAt.comp hmid)
noncomputable def bulkU (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (fun _ => 1)
noncomputable def bulkP (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkU q R f ε) 1 (dilLam q R)
noncomputable def bulkA (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (bulkP q R f ε)).Ginv
noncomputable def bulkD (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (bulkP q R f ε)).Delta2 (dataS_laws selIn selIn _)
def InteriorSoft (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ContinuousAt (fun ε : ℝ => bulkA q R f ε) 0 ∧
  ContinuousAt (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1) 0 ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) De 0
theorem pathU_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathU q R V f ε 0 = bulkU q R f ε := by
  unfold pathU bulkU
  rw [hV0]
theorem pathA_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathA q R V f ε 1 0 = bulkA q R f ε := by
  unfold pathA pathP bulkA bulkP
  rw [pathU_base q R hV0 f ε]
theorem pathD_base (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    pathD q R V f ε 1 0 = bulkD q R f ε := by
  have hd : dataS selIn selIn (pathP q R V f ε 1 0) = dataS selIn selIn (bulkP q R f ε) := by
    unfold pathP bulkP
    rw [pathU_base q R hV0 f ε]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _
theorem joint_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (t : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t) := by
  obtain ⟨hA, hW, -⟩ := hs
  refine pathA_jointly_continuousAt hq hR hroom hVc f ?_ ?_ t
  · rw [show (fun ε : ℝ => pathA q R V f ε 1 0) = fun ε => bulkA q R f ε
      from funext (pathA_base q R hV0 f)]
    exact hA
  · rw [show (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (pathU q R V f ε 0) 1) =
        fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkU q R f ε) 1
      from funext (fun ε => by rw [pathU_base q R hV0 f ε])]
    exact hW
theorem deriv_of_soft {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV0 : V 0 = fun _ => 1) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) : HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 := by
  rw [show (fun ε : ℝ => pathD q R V f ε 1 0) = fun ε => bulkD q R f ε
    from funext (pathD_base q R hV0 f)]
  exact hs.2.2
def CanonicalCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ((∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))
theorem vacuumCoupling_of_soft {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hroom : 17*2 ≤ R*(2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} (hVc : AdalyFormal.D1Literal.ContFam V)
    (hVa : AnFam V) (hV0 : V 0 = fun _ => 1)
    (hloc : IsUnit (dataS selIn selIn (flatP q R)).Ginv)
    (hneg : ∃ w, ⟪w, vacA q R V 1 Real.pi w⟫ < 0)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    (hs : InteriorSoft q R f De) (hc : CanonicalCoupling q R V De) : VacuumCoupling q R V f := by
  obtain ⟨-, -, -, -, hbef, haft⟩ :=
    vacuum_crossing hq hR hroom hVc hVa (vacA_pd_zero hV0 hloc) hneg
  obtain ⟨c, hc0, hsign⟩ := hc
  exact ⟨vacEdge q R V, c, De, hbef, haft,
    ⟨1, one_pos, fun t _ => joint_of_soft hq hR hroom hVc hV0 hs t⟩,
    deriv_of_soft hV0 hs, hc0, hsign⟩
end AdalyFormal.Round9.Guarded.QualitativeR2

                                                                            

                                                                                             
                                                                                           
                                                                                               
                                                                                                
                                                                                             
                                                                                         
                                                                                         
                                                                                                
                                                          
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL adBL adSL adBL_apply iE_adEL pE_adBL adjoint_intertwine
  bondEqv_gauge deltaKLocCLM_gauge)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

                                                       

                                                                                                
theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]
theorem flipMat_mem :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Matrix.det_fin_two]
noncomputable def flipElt : Matrix.specialUnitaryGroup (Fin 2) ℂ := ⟨!![0, 1; -1, 0], flipMat_mem⟩
noncomputable def flipGauge {L : PeriodicLatticeExtent} : GaugeFn L := fun _ => flipElt
end AdalyFormal.Round9.Guarded.QualitativeR2

                                                                                     

                                                                                  
                                                                                             
                                                                                                
                                                                                       
                                                                                       
                                                                                       
                                                                        
namespace AdalyFormal.Round9.Guarded.QualitativeR2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

                                                                       
noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α
theorem uθ_comm (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s =
      AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ α := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat α * AdalyFormal.D1Literal.uMat s =
    AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
theorem uθ_conj (α s : ℝ) :
    AdalyFormal.D1Literal.uθ α * AdalyFormal.D1Literal.uθ s * (AdalyFormal.D1Literal.uθ α)⁻¹ =
      AdalyFormal.D1Literal.uθ s := by
  rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
theorem Ug_eq_uθ (s : ℝ) : Ug s = AdalyFormal.D1Literal.uθ s :=
  Subtype.ext (Ug_coe_uMat s)
theorem rot_maskedU (q R : ℕ) (α : ℝ) (g : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    periodicGaugeTransform (rotGauge α) (maskedU q R g V) =
      maskedU q R g (periodicGaugeTransform (rotGauge α) V) := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [periodicGaugeTransform, maskedU, if_pos he, rotGauge]
  · simp only [periodicGaugeTransform, maskedU, if_neg he, rotGauge, Ug_eq_uθ]
    exact uθ_conj α (g e)
theorem rot_trivial (L : PeriodicLatticeExtent) (α : ℝ) :
    periodicGaugeTransform (rotGauge (L := L) α)
      (fun _ => (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)) = fun _ => 1 := by
  funext e
  show AdalyFormal.D1Literal.uθ α * 1 * (AdalyFormal.D1Literal.uθ α)⁻¹ = 1
  rw [mul_one, mul_inv_cancel]
end AdalyFormal.Round9.Guarded.QualitativeR2

   
                                                                

                                                                                   
                                                                                    
                                                                                    
                                                                                 
                                                                             
                                                                                     
                                                                                   
                                                                                     
                                                                                       
                                                                                   

                                                                                     
                                                                                      
                                                                          
                                                                             
                                                                                         

                                                                         
                                                                                        
                 
  
namespace AdalyFormal.Round9.Guarded.AnalyticR1

open scoped RealInnerProductSpace Topology
open Set Filter
open AdalyFormal.D1Literal (PSD psd_coercive psd_kernel)

section PathLemma
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

                                                                                    
                                                                                 
                                                     
end PathLemma

section Schur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

                                                                                  
                                                                          
end Schur

section Perturbation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

end Perturbation

section Main
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

                                                                                   
                                                                             
end Main

section MainTheorem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

                                                                                  
                                                                                 
                                                                                
                                                                              
                                                                                
                                                            
end MainTheorem

section Instantiation

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                              

                                                                                    
                                                                                      
                                                                                
                                                                                 
                         

                                                                         
abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))
noncomputable def extP (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (dilU q R ε V) 1 (dilLam q R)
noncomputable def extA (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selAll selAll (extP q R ε V)).Ginv
noncomputable def extD (q R : ℕ) (ε : ℝ) (V : LinkCfg (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →L[ℝ] TwistSpace q R :=
  (dataS selIn selIn (extP q R ε V)).Delta2 (dataS_laws selIn selIn _)
end Instantiation

                                                                 

                                                                              
                                                                                        
                                                                                        
                                                                          
section JointContinuity

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.StatementLaneR6
open AdalyFormal.D1Literal (SU2m)

variable {L : PeriodicLatticeExtent} {Y : Type*} [TopologicalSpace Y]

                                                                                          
                                                        
def ContFamT (U : Y → PeriodicLinkConfiguration SU2m L) : Prop :=
  ∀ e : PeriodicLatticeEdge L, Continuous fun θ => ((U θ e : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
section
variable {U : Y → PeriodicLinkConfiguration SU2m L} (hU : ContFamT U)
include hU

end

end JointContinuity

                                     

                                                                                         
                                                                                        
                                                                                    
                                                                                          
                                                                                           
                                                       
section InteriorFamily

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)

def InteriorRegularity (q R : ℕ) (D₁ : TwistSpace q R →L[ℝ] TwistSpace q R) : Prop :=
  Tendsto (fun ε : ℝ => extA q R ε 1) (𝓝[>] 0) (𝓝 (extA q R 0 1)) ∧
  Tendsto (fun ε : ℝ => Wop (geomOf 2 1 (dilTower q R)) (dilU q R ε 1) 1) (𝓝[>] 0)
    (𝓝 (Wop (geomOf 2 1 (dilTower q R)) (dilU q R 0 1) 1)) ∧
  Tendsto (fun ε : ℝ => ε⁻¹ • extD q R ε 1) (𝓝[>] 0) (𝓝 D₁)
def InteriorSoft : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∃ D₁ : TwistSpace q R →L[ℝ] TwistSpace q R, InteriorRegularity q R D₁
end InteriorFamily

end AdalyFormal.Round9.Guarded.AnalyticR1

   
                                                                          

                                                                                      
                                                                                             
                                                                                            
                                                                                           
                                                                                          
         
                                                                                     
                                                                                  
                                                                                         
                                                                                       
                                                                                 
                                                                                         
                                                                                          
                                                                                          
                                                                                    
                                                                                      

                                                                                  
                                                                             
                                                                                      
                                                                                          
  
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                        
section Topo

theorem tendsto_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} {l : Filter α} {g : α → E} {g₀ : E}
    (h : ∀ w : E, Tendsto (fun a => ⟪w, g a⟫) l (𝓝 ⟪w, g₀⟫)) : Tendsto g l (𝓝 g₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ x : E, x = ∑ i, ⟪b i, x⟫ • b i := fun x => (b.sum_repr' x).symm
  rw [e g₀]
  have hg : g = fun a => ∑ i, ⟪b i, g a⟫ • b i := funext fun a => e (g a)
  rw [hg]
  exact tendsto_finsetSum _ (fun i _ => (h (b i)).smul_const (b i))
theorem tendsto_clm_of_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x, Tendsto (fun a => f a x) l (𝓝 (f₀ x))) : Tendsto f l (𝓝 f₀) := by
  let b := stdOrthonormalBasis ℝ E
  have e : ∀ g : E →L[ℝ] F, g = ∑ i, (innerSL ℝ (b i)).smulRight (g (b i)) := by
    intro g
    ext x
    have hx : x = ∑ i, ⟪b i, x⟫ • b i := (b.sum_repr' x).symm
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul]
  rw [e f₀]
  have hf : f = fun a => ∑ i, (innerSL ℝ (b i)).smulRight (f a (b i)) := funext fun a => e (f a)
  rw [hf]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact ((ContinuousLinearMap.smulRightL ℝ E F (innerSL ℝ (b i))).continuous.tendsto _).comp (h (b i))
theorem tendsto_clm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {α : Type*} {l : Filter α} {f : α → E →L[ℝ] F} {f₀ : E →L[ℝ] F}
    (h : ∀ x y, Tendsto (fun a => ⟪y, f a x⟫) l (𝓝 ⟪y, f₀ x⟫)) : Tendsto f l (𝓝 f₀) :=
  tendsto_clm_of_apply (fun x => tendsto_of_inner (fun y => h x y))
end Topo

                                  
section SuTwoFields

open AdalyFormal.Balaban.CovariantOperators (SuTwo)

theorem inner_suTwo (X Y : SuTwo) :
    ⟪X, Y⟫ = -(1 / 2 : ℝ) * (Matrix.trace ((X : Matrix (Fin 2) (Fin 2) ℂ) *
      (Y : Matrix (Fin 2) (Fin 2) ℂ))).re := rfl
theorem tendsto_suTwo_of_coe {α : Type*} {l : Filter α} {g : α → SuTwo} {g₀ : SuTwo}
    (h : Tendsto (fun a => ((g a : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((g₀ : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [inner_suTwo]
  have hc : Continuous fun Y : Matrix (Fin 2) (Fin 2) ℂ =>
      -(1 / 2 : ℝ) * (Matrix.trace ((w : Matrix (Fin 2) (Fin 2) ℂ) * Y)).re :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_const.matrix_mul continuous_id).matrix_trace))
  exact (hc.tendsto _).comp h
theorem continuous_suTwo_of_coe {X : Type*} [TopologicalSpace X] {g : X → SuTwo}
    (h : Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) : Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_suTwo_of_coe (h.tendsto x)
theorem tendsto_piLp_suTwo {ι : Type*} [Fintype ι] {α : Type*} {l : Filter α}
    {g : α → PiLp 2 (fun _ : ι => SuTwo)} {g₀ : PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Tendsto (fun a => ((WithLp.ofLp (g a) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) l
      (𝓝 ((WithLp.ofLp g₀ i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ))) : Tendsto g l (𝓝 g₀) := by
  apply tendsto_of_inner
  intro w
  simp only [PiLp.inner_apply]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  have hi := tendsto_suTwo_of_coe (h i)
  exact ((continuous_const.inner continuous_id).tendsto _).comp hi
theorem continuous_piLp_suTwo {ι : Type*} [Fintype ι] {X : Type*} [TopologicalSpace X]
    {g : X → PiLp 2 (fun _ : ι => SuTwo)}
    (h : ∀ i, Continuous fun x => ((WithLp.ofLp (g x) i : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous g :=
  continuous_iff_continuousAt.mpr fun x => tendsto_piLp_suTwo (fun i => (h i).tendsto x)
theorem continuous_coe_suTwo {X : Type*} [TopologicalSpace X] {g : X → SuTwo} (h : Continuous g) :
    Continuous fun x => ((g x : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) :=
  continuous_subtype_val.comp h
end SuTwoFields

                                                                                  
section Family

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal (ContFam SU2m)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy)
open AdalyFormal.Balaban.QjComposite (stepAverage)

variable {L : PeriodicLatticeExtent}

theorem cont_coarsePathHolonomy {V : ℝ → Cfg L} (hV : ContFam V) (s : ℕ) (p : List (Fin 3)) :
    ∀ y, Continuous fun ε => ((coarsePathHolonomy s (V ε) y p : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
  induction p with
  | nil =>
    intro y
    exact continuous_const
  | cons μ rest ih =>
    intro y
    show Continuous fun ε => (((V ε (y, μ)) * coarsePathHolonomy s (V ε)
      (AdalyFormal.Balaban.CoarseCurl.coarseShift y s μ) rest : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)
    exact (hV _).matrix_mul (ih _)
theorem cont_RMap_coe {X : Type*} [TopologicalSpace X] {g : X → SU2m}
    (hg : Continuous fun ε => ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ)) {Y : X → SuTwo}
    (hY : Continuous fun ε => ((Y ε : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) :
    Continuous fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have e : (fun ε => ((RMap (g ε) (Y ε) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun ε => (g ε : Matrix (Fin 2) (Fin 2) ℂ) * (Y ε : Matrix (Fin 2) (Fin 2) ℂ) *
        star ((g ε : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext ε
    exact RMap_coe_apply _ _
  rw [e]
  exact (hg.matrix_mul hY).matrix_mul hg.star
theorem cont_gradL2 {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradL2 (V ε) := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun b => ?_)
  show Continuous fun ε => ((gradValueCovariant (V ε) (WithLp.ofLp f) b : SuTwo) :
    Matrix (Fin 2) (Fin 2) ℂ)
  unfold gradValueCovariant
  simp only [Submodule.coe_sub]
  exact (cont_RMap_coe (hV b) continuous_const).sub continuous_const
theorem cont_adjoint {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    Continuous fun M : E →L[ℝ] F => ContinuousLinearMap.adjoint M :=
  (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] (F →L[ℝ] E)).continuous
theorem cont_gradAdj {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => gradAdj (V ε) :=
  cont_adjoint.comp (cont_gradL2 hV)
theorem cont_lapFull {V : ℝ → Cfg L} (hV : ContFam V) : Continuous fun ε => lapFull (V ε) :=
  (cont_gradAdj hV).clm_comp (cont_gradL2 hV)
theorem Qcomposite_one' (bg : ℕ → Cfg L) (ell : ℕ) (lam : PeriodicLatticeSite L → SuTwo) :
    AdalyFormal.Balaban.QjComposite.Qcomposite bg ell 1 lam = stepAverage (ell ^ 0) (bg 0) ell lam :=
  rfl
theorem bgTower_zero' (G : TowerGeom L) (U : Cfg L) : bgTower G U 0 = U := rfl
theorem cont_Qlev {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) {j : ℕ} (hj : j ≤ 1)
    (y : PeriodicLatticeSite L) : Continuous fun ε => Qlev G (V ε) j y := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_suTwo_of_coe ?_
  simp only [Qlev_apply]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · simp only [AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
    exact continuous_const
  · simp only [Qcomposite_one', bgTower_zero', stepAverage, Submodule.coe_smul, Submodule.coe_sum]
    exact continuous_const.smul (continuous_finsetSum _ (fun x _ =>
      cont_RMap_coe (cont_coarsePathHolonomy hV _ _ _) continuous_const))
theorem cont_Qpa {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => Qpa G (V ε) a := by
  classical
  unfold Qpa
  refine continuous_finsetSum _ (fun j hj => continuous_finsetSum _ (fun y _ => ?_))
  have hj1 : j ≤ 1 := by rw [Finset.mem_range] at hj; omega
  by_cases hy : y ∈ G.Lam j
  · simp only [hy, if_true]
    exact continuous_const.smul ((cont_adjoint.comp (cont_Qlev hV G hj1 y)).clm_comp
      (cont_Qlev hV G hj1 y))
  · simp only [hy, if_false]
    exact continuous_const
theorem cont_DelpA {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => DelpA G (V ε) a := by
  unfold DelpA
  exact (continuous_const.clm_comp ((cont_lapFull hV).add (cont_Qpa hV G hk a))).clm_comp
    continuous_const
open AdalyFormal.M1Site in
theorem cont_LP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => LP G (V ε) a := by
  unfold LP
  exact (cont_DelpA hV G hk a).add continuous_const
open AdalyFormal.M1Site in
theorem cont_QpP {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) :
    Continuous fun ε => QpP G (V ε) a := by
  refine continuous_clm_apply.mpr (fun f => ?_)
  refine continuous_piLp_suTwo (fun p => ?_)
  cases p with
  | inl q =>
    have hj : q.1.1.val ≤ 1 := by have := q.1.1.isLt; omega
    simp only [QpP_inl, Submodule.coe_smul]
    exact continuous_const.smul (continuous_coe_suTwo
      ((cont_Qlev hV G hj _).clm_apply continuous_const))
  | inr x =>
    simp only [QpP_inr]
    exact continuous_const
end Family

                                                                                                    

                                                                                             
                                                                                                      
                                                                          
section Gauge

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Site
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.D1Literal (ContFam SU2m)

variable {L : PeriodicLatticeExtent}

                  
noncomputable def Gam (G : TowerGeom L) (U : Cfg L) (a : ℝ) : YP G →L[ℝ] YP G :=
  ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a
theorem Rproj_formula (G : TowerGeom L) (U : Cfg L) (a : ℝ) (hw : ∀ j, 0 < wq G a j)
    (hu : IsUnit (LP G U a)) (hΓ : IsUnit (Gam G U a)) :
    Rproj G U = 1 - Xop G U a ∘L (Ring.inverse (Gam G U a) ∘L
      ContinuousLinearMap.adjoint (Xop G U a)) := by
  have hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop G U a) ∘L Xop G U a)
      (Ring.inverse (Gam G U a) u) = u := by
    intro u
    have h := Ring.mul_inverse_cancel _ hΓ
    exact congrArg (fun T : YP G →L[ℝ] YP G => T u) h
  ext1 v
  rw [Rproj_eq_strat G U a hw hu _ hG1 v]
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
theorem continuousAt_inverse_comp {X : Type*} [TopologicalSpace X] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : X → E →L[ℝ] E} {x₀ : X} (hf : ContinuousAt f x₀) (hu : IsUnit (f x₀)) :
    ContinuousAt (fun x => Ring.inverse (f x)) x₀ := by
  have h1 := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp hf
theorem continuousAt_clm_comp {X : Type*} [TopologicalSpace X] {E F G' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] {g : X → F →L[ℝ] G'} {f : X → E →L[ℝ] F} {x₀ : X}
    (hg : ContinuousAt g x₀) (hf : ContinuousAt f x₀) :
    ContinuousAt (fun x => (g x).comp (f x)) x₀ := by
  have hc : Continuous (fun p : (F →L[ℝ] G') × (E →L[ℝ] F) => p.1.comp p.2) :=
    continuous_fst.clm_comp continuous_snd
  exact (hc.tendsto (g x₀, f x₀)).comp (hg.prodMk_nhds hf)
section
variable {V : ℝ → Cfg L} (hV : ContFam V) (G : TowerGeom L) (hk : G.k = 1) (a : ℝ) {ε₀ : ℝ}
  (hu : IsUnit (LP G (V ε₀) a))
include hV hk hu

theorem continuousAt_LinvP : ContinuousAt (fun ε => LinvP G (V ε) a) ε₀ :=
  continuousAt_inverse_comp (cont_LP hV G hk a).continuousAt hu
theorem continuousAt_Xop : ContinuousAt (fun ε => Xop G (V ε) a) ε₀ :=
  continuousAt_clm_comp (continuousAt_LinvP hV G hk a hu)
    (cont_adjoint.comp (cont_QpP hV G hk a)).continuousAt
theorem continuousAt_Gam : ContinuousAt (fun ε => Gam G (V ε) a) ε₀ :=
  continuousAt_clm_comp (cont_adjoint.continuousAt.comp (continuousAt_Xop hV G hk a hu))
    (continuousAt_Xop hV G hk a hu)
variable (hw : ∀ j, 0 < wq G a j) (hΓ : IsUnit (Gam G (V ε₀) a))
include hw hΓ

theorem continuousAt_Rproj : ContinuousAt (fun ε => Rproj G (V ε)) ε₀ := by
  have hX := continuousAt_Xop hV G hk a hu
  have hGc := continuousAt_Gam hV G hk a hu
  have hGi := continuousAt_inverse_comp hGc hΓ
  have hF : ContinuousAt (fun ε => (1 : SiteL2 L →L[ℝ] SiteL2 L) - Xop G (V ε) a ∘L
      (Ring.inverse (Gam G (V ε) a) ∘L ContinuousLinearMap.adjoint (Xop G (V ε) a))) ε₀ :=
    continuousAt_const.sub (continuousAt_clm_comp hX
      (continuousAt_clm_comp hGi (cont_adjoint.continuousAt.comp hX)))
  have h1 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (LP G (V ε) a) :=
    ((cont_LP hV G hk a).tendsto ε₀).eventually
      ((Units.isOpen (R := SiteL2 L →L[ℝ] SiteL2 L)).mem_nhds hu)
  have h2 : ∀ᶠ ε in 𝓝 ε₀, IsUnit (Gam G (V ε) a) :=
    hGc.eventually ((Units.isOpen (R := YP G →L[ℝ] YP G)).mem_nhds hΓ)
  refine hF.congr ?_
  filter_upwards [h1, h2] with ε hε1 hε2
  exact (Rproj_formula G (V ε) a hw hε1 hε2).symm
theorem continuousAt_Tfull : ContinuousAt (fun ε => Tfull G (V ε)) ε₀ :=
  continuousAt_clm_comp (continuousAt_Rproj hV G hk a hu hw hΓ) (cont_gradAdj hV).continuousAt
theorem continuousAt_Wop : ContinuousAt (fun ε => Wop G (V ε) a) ε₀ := by
  have hR := continuousAt_Rproj hV G hk a hu hw hΓ
  have hL := continuousAt_LinvP hV G hk a hu
  unfold Wop
  exact continuousAt_const.sub (continuousAt_clm_comp (cont_gradL2 hV).continuousAt
    (continuousAt_clm_comp (continuousAt_clm_comp hL continuousAt_const)
      (continuousAt_clm_comp hR (cont_gradAdj hV).continuousAt)))
end

end Gauge

                                                                                              
                                                                                
section DirichletUnit

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap gradValueCovariant)
open AdalyFormal.Balaban.SuTwoInner (hsInner hsInner_RMap hsInner_self_nonneg hsInner_self_eq_zero)

open Fin.NatCast

variable {L : PeriodicLatticeExtent}

theorem ajSeq_pos {a : ℝ} (ha : 0 < a) {ell : ℕ} (hell : 2 ≤ ell) (j : ℕ) : 0 < ajSeq a ell j := by
  unfold ajSeq
  split_ifs with h
  · exact ha
  · unfold AdalyFormal.Balaban.ConstantA.aSeq
    have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
    have hpos : (0 : ℝ) < (ell : ℝ) * ell := by positivity
    have hd : 0 < a / ((ell : ℝ) * ell) := by positivity
    have h4 : (4 : ℝ) ≤ (ell : ℝ) * ell := by nlinarith
    have hda : a / ((ell : ℝ) * ell) < a := by
      rw [div_lt_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left h4 ha.le]
    exact AdalyFormal.Balaban.ConstantA.aSeqAux_pos a _ ha hd hda _
theorem Qpa_nonneg (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    0 ≤ ⟪f, Qpa G U a f⟫ := by
  rw [inner_Qpa]
  refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun y _ => ?_))
  split_ifs
  · exact mul_nonneg (mul_nonneg (ajSeq_pos ha hell j).le (pow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _)
  · exact le_rfl
theorem delpA_inner_ge (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (f : SiteL2 L) :
    ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 + ‖f - siteMask G.Om0 f‖ ^ 2 ≤ ⟪f, (DelpA G U a + (1 - siteMask G.Om0)) f⟫ := by
  set m := siteMask G.Om0 with hm
  have hsym : ∀ u v : SiteL2 L, ⟪m u, v⟫ = ⟪u, m v⟫ := fun u v => siteMask_symm _ u v
  have hidem : ∀ u : SiteL2 L, m (m u) = m u := fun u => siteMask_idem _ u
  have e1 : ⟪f, DelpA G U a f⟫ = ⟪m f, lapFull U (m f)⟫ + ⟪m f, Qpa G U a (m f)⟫ := by
    unfold DelpA
    simp only [ContinuousLinearMap.comp_apply, add_apply]
    rw [← hsym, inner_add_right]
  have e2 : ⟪f, ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫ = ‖f - m f‖ ^ 2 := by
    simp only [sub_apply, one_apply_eq_self]
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪m f, f - m f⟫ = 0 := by
      rw [inner_sub_right]
      have a1 : ⟪m f, m f⟫ = ⟪f, m f⟫ := by rw [hsym, hidem]
      have a2 : ⟪m f, f⟫ = ⟪f, m f⟫ := real_inner_comm _ _
      rw [a1, a2, sub_self]
    have hdec : f = (f - m f) + m f := by abel
    calc ⟪f, f - m f⟫ = ⟪(f - m f) + m f, f - m f⟫ := by rw [← hdec]
      _ = ⟪f - m f, f - m f⟫ := by rw [inner_add_left, h0, add_zero]
  have e3 : ⟪m f, lapFull U (m f)⟫ = ‖gradL2 U (m f)‖ ^ 2 := by
    unfold lapFull gradAdj
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  have e4 := Qpa_nonneg G U ha hell (m f)
  show _ ≤ ⟪f, DelpA G U a f + ((1 : SiteL2 L →L[ℝ] SiteL2 L) - m) f⟫
  rw [inner_add_right, e1, e2, e3]
  linarith
theorem covConst_norm (U : Cfg L) (f : SiteL2 L) (h : gradL2 U f = 0) (x y : PeriodicLatticeSite L) :
    hsInner (f x) (f x) = hsInner (f y) (f y) := by
  have hb : ∀ b : AdalyFormal.Balaban.AdmissibleSubspace.Bond L, RMap (U b) (f (periodicLatticeShift b.1 b.2)) = f b.1 := by
    intro b
    have := congrFun (congrArg WithLp.ofLp h) b
    rw [gradL2_apply] at this
    simp only [gradValueCovariant] at this
    exact sub_eq_zero.mp this
  have hstep : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3), hsInner (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)) = hsInner (f z) (f z) := by
    intro z μ
    have := hb (z, μ)
    simp only [] at this
    rw [← hsInner_RMap (U (z, μ)) (f (periodicLatticeShift z μ)) (f (periodicLatticeShift z μ)), this]
  have hiter : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (j : ℕ),
      hsInner (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) (f (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1))))) = hsInner (f z) (f z) := by
    intro z μ j
    induction j with
    | zero => simp
    | succ j ih =>
      have : Function.update z μ (z μ + (Nat.cast (j + 1) : Fin (L μ + 1))) =
          periodicLatticeShift (Function.update z μ (z μ + (Nat.cast j : Fin (L μ + 1)))) μ := by
        unfold periodicLatticeShift
        rw [Function.update_self, Function.update_idem]
        congr 1
        rw [Nat.cast_succ]
        abel
      rw [this, hstep, ih]
  have hupd : ∀ (z : PeriodicLatticeSite L) (μ : Fin 3) (v : Fin (L μ + 1)),
      hsInner (f (Function.update z μ v)) (f (Function.update z μ v)) = hsInner (f z) (f z) := by
    intro z μ v
    have := hiter z μ (v - z μ).val
    rw [Fin.cast_val_eq_self, add_sub_cancel] at this
    exact this
  have hall : ∀ z w : PeriodicLatticeSite L, hsInner (f w) (f w) = hsInner (f z) (f z) := by
    intro z w
    have hw : w = Function.update (Function.update (Function.update z 0 (w 0)) 1 (w 1)) 2 (w 2) := by
      funext ν
      fin_cases ν <;> simp [Function.update]
    rw [hw, hupd, hupd, hupd]
  exact (hall x y).symm
theorem delpA_unit (G : TowerGeom L) (U : Cfg L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell)
    (hout : ∃ x : PeriodicLatticeSite L, x ∉ G.Om0) :
    IsUnit (DelpA G U a + (1 - siteMask G.Om0)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set X : SiteL2 L →L[ℝ] SiteL2 L := DelpA G U a + (1 - siteMask G.Om0) with hX
  have hinj : Function.Injective X := by
    refine (injective_iff_map_eq_zero X).mpr (fun f hf => ?_)
    have h1 := delpA_inner_ge G U ha hell f
    rw [hf, inner_zero_right] at h1
    have hs1 := sq_nonneg ‖gradL2 U (siteMask G.Om0 f)‖
    have hs2 := sq_nonneg ‖f - siteMask G.Om0 f‖
    have hD : ‖gradL2 U (siteMask G.Om0 f)‖ ^ 2 = 0 := by linarith
    have hR : ‖f - siteMask G.Om0 f‖ ^ 2 = 0 := by linarith
    have hfm : f = siteMask G.Om0 f :=
      sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hR))
    have hDm : gradL2 U (siteMask G.Om0 f) = 0 := norm_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp hD)
    have hDf : gradL2 U f = 0 := by rw [← hfm] at hDm; exact hDm
    obtain ⟨x0, hx0⟩ := hout
    have hx0f : f x0 = 0 := by
      have : (siteMask G.Om0 f) x0 = 0 := by rw [siteMask_apply, if_neg hx0]
      rw [← hfm] at this; exact this
    ext x
    have := covConst_norm U f hDf x x0
    rw [hx0f] at this
    have h0 : hsInner (f x) (f x) = 0 := by
      rw [this]; exact AdalyFormal.Balaban.DeltaKU.hsInner_zero_right _
    have := hsInner_self_eq_zero h0
    simp [this]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (X : SiteL2 L →ₗ[ℝ] SiteL2 L))).mp hinj⟩
theorem wq_pos (G : TowerGeom L) {a : ℝ} (ha : 0 < a) (hell : 2 ≤ G.ell) (j : ℕ) :
    0 < AdalyFormal.M1Site.wq G a j := by
  unfold AdalyFormal.M1Site.wq
  have : (0 : ℝ) < G.ell := by exact_mod_cast (by omega : 0 < G.ell)
  exact mul_pos (ajSeq_pos ha hell j) (pow_pos this j)
end DirichletUnit

end AdalyFormal.Round9.Guarded.AnalyticR2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                        

                                                                                                 
                                                                                                  
                                                                                                  
                                                                                                  
                                                                                                  
                                                            
section Jets

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

variable {L : PeriodicLatticeExtent}

def SmoothAt0 (V : ℝ → PeriodicLinkConfiguration SU2 L) : Prop :=
  ∀ b, ContDiffAt ℝ ⊤ (fun ε => ((V ε b : SU2) : M2)) 0
section Fam
variable (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)

include hV in
theorem SG_V0 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => V q.1 b) := by
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((V q.1 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun ε : ℝ => ((V ε b : SU2) : M2)) (f := fun q : ℝ × XS L => q.1)
    (0 : ℝ × XS L) (hV b) contDiffAt_fst
theorem SG_V1 (b : PeriodicLatticeEdge L) : SG (fun q : ℝ × XS L => expCfgX q.2 b) := by
  have h : ContDiffAt ℝ ⊤ (fun a : XS L => ((expCfgX a b : SU2) : M2)) 0 := SG_expCfgX b
  show ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => ((expCfgX q.2 b : SU2) : M2)) 0
  exact ContDiffAt.comp (g := fun a : XS L => ((expCfgX a b : SU2) : M2)) (f := fun q : ℝ × XS L => q.2)
    (0 : ℝ × XS L) h contDiffAt_snd
include hV in
theorem SG_prod (b : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => expCfgX q.2 b * V q.1 b) :=
  (SG_V1 b).mul (SG_V0 V hV b)
theorem SG_loopVar_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) :
    SG (fun q => loopVar s ell (W q) c x) := by
  unfold loopVar gammaVarStrided coarseBondVar
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  exact (((h _ _).mul (h _ _)).mul (h _ _).inv).mul (h _ _).inv
theorem SG_sbg_fam (s ell : ℕ) (W : ℝ × XS L → PeriodicLinkConfiguration SU2 L)
    (hW : ∀ b, SG (fun q => W q b)) (c : PeriodicLatticeEdge L)
    (hreg : ∀ x ∈ stepBlockOf c.1 s ell, ((loopVar s ell (W 0) c x : SU2) : M2) ∈ LogReg) :
    SG (fun q => stridedBlockedGauge su2LogExp s ell (W q) c) := by
  unfold stridedBlockedGauge
  have h := fun (p : List (Fin 3)) (y : PeriodicLatticeSite L) => SG.hol s W hW p y
  refine SG.mul ?_ (by unfold coarseBondVar; exact h _ _)
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf c.1 s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => loopVar s ell (W q) c x) (fun x _ => SG_loopVar_fam s ell W hW c x)
    (fun x hx => hreg x hx)
  simpa [su2LogExp_log, su2LogExp_exp] using this
include hV in
theorem SG_rProd_fam (s : ℕ) (y : PeriodicLatticeSite L) (p : List (Fin 3)) :
    SG (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p) := by
  have h1 := SG.hol (E := ℝ × XS L) s (fun q => fun b => expCfgX q.2 b * V q.1 b)
    (fun b => SG_prod V hV b) p y
  have h2 := SG.hol (E := ℝ × XS L) s (fun q => V q.1) (fun b => SG_V0 V hV b) p y
  have e : (fun q : ℝ × XS L => rProd s (V q.1) (expCfgX q.2) y p)
      = fun q => coarsePathHolonomy s (fun b => expCfgX q.2 b * V q.1 b) y p *
          (coarsePathHolonomy s (V q.1) y p)⁻¹ := by
    funext q
    exact rProd_eq s (V q.1) (expCfgX q.2) y p
  rw [e]
  exact SG.mul_inv h1 h2
include hV in
theorem SG_su2Exp_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (sBlock s ell (V q.1) (expCfgX q.2) y)) := by
  unfold sBlock
  exact SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
include hV in
theorem SG_su2Exp_neg_sBlock_fam (s ell : ℕ) (y : PeriodicLatticeSite L) :
    SG (fun q : ℝ × XS L => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) y))) := by
  have := SG_su2Exp_sum_log (E := ℝ × XS L) (stepBlockOf y s ell) (-((ell : ℚ) ^ 3)⁻¹)
    (fun x q => rProd s (V q.1) (expCfgX q.2) y (coarseGammaPath s y x))
    (fun x _ => SG_rProd_fam V hV s y _)
    (fun x _ => by
      show ((rProd s (V 0) (expCfgX (0 : XS L)) y _ : SU2) : M2) ∈ LogReg
      rw [rProd_expCfgX_zero]; exact one_mem_LogReg)
  unfold sBlock
  simpa [neg_smul, Finset.sum_neg_distrib] using this
include hV in
/-- The raw one-step averaging is jointly smooth in (curvature, field) at `(0, 0)`. -/
theorem SG_rawStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    SG (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c) := by
  have e : (fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      = fun q => su2Exp (-(sBlock s ell (V q.1) (expCfgX q.2) c.1))
        * stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c
        * su2Exp (sBlock s ell (V q.1) (expCfgX q.2) (cPlusS s ell c))
        * (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹ := by
    funext q; exact rawStep_simp s ell (V q.1) (expCfgX q.2) c
  unfold SG; rw [e]
  have h1 := SG_su2Exp_neg_sBlock_fam V hV s ell c.1
  have h2 : SG (fun q : ℝ × XS L =>
      stridedBlockedGauge su2LogExp s ell (fun b => expCfgX q.2 b * V q.1 b) c) := by
    refine SG_sbg_fam s ell (fun q => fun b => expCfgX q.2 b * V q.1 b) (fun b => SG_prod V hV b) c ?_
    intro x hx
    have e0 : (fun b => expCfgX (0 : XS L) b * V 0 b) = V 0 := by
      funext b; rw [expCfgX_zero]; exact one_mul _
    show ((loopVar s ell (fun b => expCfgX ((0 : ℝ × XS L).2) b * V ((0 : ℝ × XS L).1) b) c x : SU2) : M2)
      ∈ LogReg
    rw [show ((0 : ℝ × XS L).2) = (0 : XS L) from rfl, show ((0 : ℝ × XS L).1) = (0 : ℝ) from rfl, e0]
    exact hreg c x hx
  have h3 := SG_su2Exp_sBlock_fam V hV s ell (cPlusS s ell c)
  have h4 : SG (fun q : ℝ × XS L => (stridedBlockedGauge su2LogExp s ell (V q.1) c)⁻¹) := by
    refine SG.inv (SG_sbg_fam s ell (fun q => V q.1) (fun b => SG_V0 V hV b) c ?_)
    intro x hx
    exact hreg c x hx
  exact (((h1.mul h2).mul h3).mul h4)
include hV in
theorem contDiffAt_qStep_fam (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun q : ℝ × XS L => su2Log (rawStep s ell (V q.1) (expCfgX q.2) c)) 0 :=
    AdalyFormal.Balaban.SmoothLog.su2Log_comp_contDiffAt
      (G := fun q : ℝ × XS L => rawStep s ell (V q.1) (expCfgX q.2) c)
      (SG_rawStep_fam V hV s ell hreg c) (rawStep_expCfgX_zero s ell (V 0) c)
  exact fromM2L.contDiff.contDiffAt.comp (0 : ℝ × XS L) h1
include hV in
/-- First jet: continuity in the curvature of the field derivative at the zero field. -/
theorem continuousAt_fderiv_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (qStepComp s ell (V ε) c) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L => qStepX s ell (V ε) a c)
      ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) => qStepX s ell (V ε) a c)
      (g := fun _ : ℝ => (0 : XS L)) h contDiffAt_const (by simp)
  exact h2.continuousAt
include hV in
/-- Second jet: continuity in the curvature of the second field derivative at the zero field. -/
theorem continuousAt_fderiv2_qStep (s ell : ℕ) (hreg : RegBg s ell (V 0)) (c : PeriodicLatticeEdge L) :
    ContinuousAt (fun ε => fderiv ℝ (fderiv ℝ (qStepComp s ell (V ε) c)) 0) 0 := by
  have h := contDiffAt_qStep_fam V hV s ell hreg c
  have hl : ContDiffAt ℝ ⊤ (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))
      ((0 : ℝ × XS L), (0 : XS L)) :=
    (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hΦ' : ContDiffAt ℝ ⊤ ((fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c) ∘
      (fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L))) ((0 : ℝ × XS L), (0 : XS L)) :=
    ContDiffAt.comp (g := fun q : ℝ × XS L => qStepX s ell (V q.1) q.2 c)
      (f := fun z : (ℝ × XS L) × XS L => ((z.1.1, z.2) : ℝ × XS L)) ((0 : ℝ × XS L), (0 : XS L)) h hl
  have hΦ : ContDiffAt ℝ ⊤ (Function.uncurry fun (x : ℝ × XS L) (b : XS L) =>
      qStepX s ell (V x.1) b c) ((0 : ℝ × XS L), (fun x : ℝ × XS L => x.2) 0) := hΦ'
  have hΨ : ContDiffAt ℝ ⊤ (fun x : ℝ × XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V x.1) b c) x.2) 0 :=
    ContDiffAt.fderiv (f := fun (x : ℝ × XS L) (b : XS L) => qStepX s ell (V x.1) b c)
      (g := fun x : ℝ × XS L => x.2) hΦ contDiffAt_snd (by simp)
  have h2 : ContDiffAt ℝ 0 (fun ε : ℝ => fderiv ℝ (fun a : XS L =>
      fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a) ((fun _ : ℝ => (0 : XS L)) ε)) 0 :=
    ContDiffAt.fderiv (f := fun (ε : ℝ) (a : XS L) =>
        fderiv ℝ (fun b : XS L => qStepX s ell (V ε) b c) a)
      (g := fun _ : ℝ => (0 : XS L)) hΨ contDiffAt_const (by simp)
  exact h2.continuousAt
end Fam

end Jets

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                   

                                                                                               
                                                                                                
                                                                                                 
                                                                                            
                                                                                              
                                              
section Assembly

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (ContFam)

variable {L : PeriodicLatticeExtent}

theorem tendsto_clm_apply₂ {α : Type*} {l : Filter α} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α → E →L[ℝ] F} {x : α → E}
    {f₀ : E →L[ℝ] F} {x₀ : E} (hf : Tendsto f l (𝓝 f₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => f a (x a)) l (𝓝 (f₀ x₀)) :=
  ((continuous_fst.clm_apply continuous_snd).tendsto (f₀, x₀)).comp (hf.prodMk_nhds hx)
noncomputable def suCoordL : BondFnL2 L →L[ℝ] XS L := LinearMap.toContinuousLinearMap suCoord
theorem QfullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (QfullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (QlinB G U p.1 A)) p.2.1 := rfl
theorem C2fullOf_apply (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (p : BIdx G) :
    WithLp.ofLp (C2fullOf G U A) p
      = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G U p.1 A)) p.2.1 := rfl
theorem QlinB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (QlinB G U 1 A) c : SuTwo) : M2) =
      toM2 (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c) 0 (suCoord A)) := rfl
theorem C2rawB_zero' (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) : C2rawB G U 0 A = 0 := by
  refine PiLp.ext (fun b => ?_)
  apply Subtype.ext
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 0 (suCoord A) (suCoord A))) b : M2) = 0
  simp [D2CompL, suCoordInv]
theorem C2rawB_one_coe (G : TowerGeom L) (U : Cfg L) (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    ((WithLp.ofLp (C2rawB G U 1 A) c : SuTwo) : M2) =
      (1 / 2 : ℝ) • toM2 (fderiv ℝ (fderiv ℝ (qStepComp (G.ell ^ 0) G.ell U c)) 0
        (suCoord A) (suCoord A)) := by
  show (((1 / 2 : ℝ) • suCoordInv (D2CompL G.ell (bgTower G U) 1 (suCoord A) (suCoord A))) c : M2) = _
  simp only [D2CompL, LinearMap.mk₂_apply, QlinCompL_zero, ContinuousLinearMap.id_apply]
  simp [D2StepL_apply, suCoordInv]
  rfl
section BondSector
variable (V : ℝ → Cfg L) (hV : SmoothAt0 V)
  (G : TowerGeom L) (hk : G.k = 1) (hreg : RegBg (G.ell ^ 0) G.ell (V 0))

include hV hreg in
theorem tendsto_QlinB1_coe (A : BondFnL2 L) (c : PeriodicLatticeEdge L) :
    Tendsto (fun ε => ((WithLp.ofLp (QlinB G (V ε) 1 A) c : SuTwo) : M2)) (𝓝 0)
      (𝓝 ((WithLp.ofLp (QlinB G (V 0) 1 A) c : SuTwo) : M2)) := by
  simp only [QlinB_one_coe]
  have h := continuousAt_fderiv_qStep V hV (G.ell ^ 0) G.ell hreg c
  exact (toM2L.continuous.tendsto _).comp (tendsto_clm_apply₂ h tendsto_const_nhds)
include hV hreg hk in
theorem continuousAt_QfullOf : ContinuousAt (fun ε => QfullOf G (V ε)) 0 := by
  refine tendsto_clm_of_apply (fun A => tendsto_piLp_suTwo (fun p => ?_))
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [QfullOf_apply, QlinB_zero]
    exact tendsto_const_nhds
  · simp only [QfullOf_apply, Submodule.coe_smul]
    exact (tendsto_QlinB1_coe V hV G hreg A r.1).const_smul _
include hV hreg hk in
theorem tendsto_C2fullOf {X : ℝ → BondFnL2 L} {X₀ : BondFnL2 L} (hX : Tendsto X (𝓝 0) (𝓝 X₀)) :
    Tendsto (fun ε => C2fullOf G (V ε) (X ε)) (𝓝 0) (𝓝 (C2fullOf G (V 0) X₀)) := by
  refine tendsto_piLp_suTwo (fun p => ?_)
  obtain ⟨⟨j, hj⟩, r⟩ := p
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · simp only [C2fullOf_apply, C2rawB_zero']
    exact tendsto_const_nhds
  · simp only [C2fullOf_apply, Submodule.coe_smul, C2rawB_one_coe]
    have h2 := continuousAt_fderiv2_qStep V hV (G.ell ^ 0) G.ell hreg r.1
    have hs : Tendsto (fun ε => suCoord (X ε)) (𝓝 0) (𝓝 (suCoord X₀)) :=
      ((suCoordL (L := L)).continuous.tendsto _).comp hX
    exact (((toM2L.continuous.tendsto _).comp
      (tendsto_clm_apply₂ (tendsto_clm_apply₂ h2 hs) hs)).const_smul _).const_smul _
end BondSector

noncomputable def dataFam (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) :
    ℝ → BaseDataS ↥(bondSupp (geomOf ell k S)) (SiteL2 (scaleUp ell k Lu)) (FSp (geomOf ell k S)) :=
  fun ε => dataS sD sJ (gparams ell k Lu hell S (V ε) a Lam)
theorem Ginv_dataFam_eq (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (ε : ℝ) :
    (dataFam sD sJ hell S V a Lam ε).Ginv =
      (pE (geomOf ell k S)).comp ((DpiFullS sD (geomOf ell k S) (V ε) a).comp (iE (geomOf ell k S)))
      + (ContinuousLinearMap.adjoint ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))).comp
          ((Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S)))
      + (pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
          (bondSectorOf (geomOf ell k S) (V ε))).comp (iE (geomOf ell k S))) := rfl
theorem continuousAt_Ginv_dataS (sD sJ : PlaqSel) {ell k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell : 0 < ell) (S : Tower (scaleUp ell k Lu)) (V : ℝ → Cfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (hVc : ContFam V)
    (hW : ContinuousAt (fun ε => Wop (geomOf ell k S) (V ε) a) 0)
    (hT : ContinuousAt (fun ε => Tfull (geomOf ell k S) (V ε)) 0)
    (hQ : ContinuousAt (fun ε => QfullOf (geomOf ell k S) (V ε)) 0) :
    ContinuousAt (fun ε => (dataFam sD sJ hell S V a Lam ε).Ginv) 0 := by
  simp only [Ginv_dataFam_eq]
  have hΔ : ContinuousAt (fun ε => DeltaS sD (geomOf ell k S) (V ε)) 0 :=
    (AdalyFormal.D1Literal.cont_deltaKLocCLM hVc (sD _ (geomOf ell k S))).continuousAt
  have hDpi : ContinuousAt (fun ε => DpiFullS sD (geomOf ell k S) (V ε) a) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hW) (continuousAt_clm_comp hΔ hW)
  have hTi : ContinuousAt (fun ε => (Tfull (geomOf ell k S) (V ε)).comp (iE (geomOf ell k S))) 0 :=
    continuousAt_clm_comp hT continuousAt_const
  have hM : ContinuousAt (fun ε => MassFull (geomOf ell k S) a (bondSectorOf (geomOf ell k S) (V ε))) 0 :=
    continuousAt_clm_comp (cont_adjoint.continuousAt.comp hQ)
      (continuousAt_clm_comp continuousAt_const hQ)
  refine ((continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hDpi continuousAt_const)).add
    (continuousAt_clm_comp (cont_adjoint.continuousAt.comp hTi) hTi)).add ?_
  exact continuousAt_clm_comp continuousAt_const (continuousAt_clm_comp hM continuousAt_const)
theorem continuousAt_H {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hGinv : ContinuousAt (fun ε => (D ε).Ginv) 0)
    (hQ : ContinuousAt (fun ε => (D ε).Q) 0) (hQs : ContinuousAt (fun ε => (D ε).Qs) 0)
    (hu : IsUnit (D 0).Ginv) (hN : IsUnit (((D 0).Q.comp (D 0).G).comp (D 0).Qs)) :
    ContinuousAt (fun ε => (D ε).H) 0 := by
  have hG : ContinuousAt (fun ε => (D ε).G) 0 := continuousAt_inverse_comp hGinv hu
  have hNc : ContinuousAt (fun ε => ((D ε).Q.comp (D ε).G).comp (D ε).Qs) 0 :=
    continuousAt_clm_comp (continuousAt_clm_comp hQ hG) hQs
  exact continuousAt_clm_comp (continuousAt_clm_comp hG hQs) (continuousAt_inverse_comp hNc hN)
theorem inner_polarization {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫) (x y : E) :
    ⟪y, M x⟫ = (⟪x + y, M (x + y)⟫ - ⟪x - y, M (x - y)⟫) / 4 := by
  have h1 : ⟪x, M y⟫ = ⟪y, M x⟫ := by rw [← hM, real_inner_comm]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, h1]
  ring
theorem tendsto_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) (A : E) :
    Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 (2 * ⟪(D 0).H ((D 0).C2 A), J'⟫)) := by
  have e : ∀ ε : ℝ, ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫
      = 2 * ⟪(D ε).H ((D ε).C2 A), ε⁻¹ • (D ε).J⟫ := by
    intro ε
    rw [smul_apply, real_inner_smul_right, ((D ε).Delta2_spec (hL ε)).2 A,
      real_inner_smul_right]
    ring
  simp only [e]
  have hHC : Tendsto (fun ε => (D ε).H ((D ε).C2 A)) (𝓝[≠] 0) (𝓝 ((D 0).H ((D 0).C2 A))) :=
    tendsto_clm_apply₂ (hH.tendsto.mono_left nhdsWithin_le_nhds)
      ((hC2 A).mono_left nhdsWithin_le_nhds)
  exact (Filter.Tendsto.inner (𝕜 := ℝ) hHC hJ).const_mul (2 : ℝ)
theorem tendsto_Delta2_div {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J')) :
    ∃ D₁ : E →L[ℝ] E, Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨β, hβ⟩ := (hL 0).C2_quad
  let β1 : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => 2 * ⟪(D 0).H (β x y), J'⟫)
    (fun x1 x2 y => by simp only [map_add, LinearMap.add_apply, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left, smul_eq_mul]; ring)
    (fun x y1 y2 => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, real_inner_smul_left, smul_eq_mul]; ring)
  refine ⟨symmOp β1, ?_⟩
  have hdiag : ∀ A, Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[≠] 0)
      (𝓝 ⟪A, symmOp β1 A⟫) := by
    intro A
    rw [inner_symmOp_diag]
    have e2 : β1 A A = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
      simp only [β1, LinearMap.mk₂_apply, hβ A]
    rw [e2]
    exact tendsto_Delta2_div_form D hL hH hC2 J' hJ A
  have hsym : ∀ ε : ℝ, ∀ x y, ⟪(ε⁻¹ • (D ε).Delta2 (hL ε)) x, y⟫ = ⟪x, (ε⁻¹ • (D ε).Delta2 (hL ε)) y⟫ := by
    intro ε x y
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
      ((D ε).Delta2_spec (hL ε)).1 x y]
  apply tendsto_clm_of_inner
  intro x y
  have e1 : ∀ ε : ℝ, ⟪y, (ε⁻¹ • (D ε).Delta2 (hL ε)) x⟫ =
      (⟪x + y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x + y)⟫ - ⟪x - y, (ε⁻¹ • (D ε).Delta2 (hL ε)) (x - y)⟫) / 4 :=
    fun ε => inner_polarization _ (hsym ε) x y
  rw [inner_polarization (symmOp β1) (symmOp_symm β1) x y]
  simp only [e1]
  exact ((hdiag (x + y)).sub (hdiag (x - y))).div_const 4
theorem limit_Delta2_div_form {E S F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (D : ℝ → BaseDataS E S F) (hL : ∀ ε, (D ε).Laws)
    (hH : ContinuousAt (fun ε => (D ε).H) 0)
    (hC2 : ∀ A, Tendsto (fun ε => (D ε).C2 A) (𝓝 0) (𝓝 ((D 0).C2 A)))
    (J' : E) (hJ : Tendsto (fun ε => ε⁻¹ • (D ε).J) (𝓝[≠] 0) (𝓝 J'))
    (D₁ : E →L[ℝ] E) (hD₁ : Tendsto (fun ε => ε⁻¹ • (D ε).Delta2 (hL ε)) (𝓝[>] 0) (𝓝 D₁)) (A : E) :
    ⟪A, D₁ A⟫ = 2 * ⟪(D 0).H ((D 0).C2 A), J'⟫ := by
  have h1 : Tendsto (fun ε => ⟪A, (ε⁻¹ • (D ε).Delta2 (hL ε)) A⟫) (𝓝[>] 0) (𝓝 ⟪A, D₁ A⟫) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_clm_apply₂ hD₁ tendsto_const_nhds))
  have h2 := (tendsto_Delta2_div_form D hL hH hC2 J' hJ A).mono_left
    (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))
  exact tendsto_nhds_unique h1 h2
end Assembly

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                          

                                                                                              
                                                                                                
                                                                                    
section SourceSmooth

open scoped Matrix Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (SG SG.mul SG.inv conjTR conjTR_apply)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.DeltaPrime (holonomyElem holonomyElemInv imHolonomy)
open AdalyFormal.Balaban.SourceJ (piProj DstarDir)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo conjByAmbient)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.IngredientFamily (JSU2Loc JfieldLoc FnuMuLoc)

variable {L : PeriodicLatticeExtent} (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
include hV

theorem SG_holonomyElem (p : PeriodicLatticePlaquette L) :
    SG (fun ε => holonomyElem (V ε) p) := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have e : (fun ε => holonomyElem (V ε) p) = fun ε =>
      V ε (p.1, p.2.1.1) * V ε (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) *
        (V ε (periodicLatticeShift p.1 p.2.1.2, p.2.1.1))⁻¹ * (V ε (p.1, p.2.1.2))⁻¹ := by
    funext ε; rfl
  rw [e]
  exact (((hS _).mul (hS _)).mul (hS _).inv).mul (hS _).inv
theorem cd_imHolonomy (p : PeriodicLatticePlaquette L) :
    ContDiffAt ℝ ⊤ (fun ε => imHolonomy (V ε) p) 0 := by
  have h1 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElem (V ε) p : SU2) : M2)) 0 := SG_holonomyElem V hV p
  have h2 : ContDiffAt ℝ ⊤ (fun ε => ((holonomyElemInv (V ε) p : SU2) : M2)) 0 :=
    (SG_holonomyElem V hV p).inv
  exact (h1.sub h2).const_smul _
omit hV in
theorem cd_piProj {f : ℝ → M2} (hf : ContDiffAt ℝ ⊤ f 0) :
    ContDiffAt ℝ ⊤ (fun ε => piProj (f ε)) 0 := by
  have htr : ContDiffAt ℝ ⊤ (fun ε => Matrix.trace (f ε)) 0 :=
    (((Matrix.traceLinearMap (Fin 2) ℝ ℂ).toContinuousLinearMap).contDiff.contDiffAt).comp 0 hf
  simp only [piProj]
  exact hf.sub ((htr.div_const 2).smul contDiffAt_const)
theorem cd_FnuMuLoc (P : Set (PeriodicLatticePlaquette L)) (ν μ : Fin 3) (y : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => FnuMuLoc P (V ε) ν μ y) 0 := by
  classical
  unfold FnuMuLoc
  by_cases hlt : ν < μ
  · simp only [dif_pos hlt]
    by_cases hp : (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) ∈ P
    · simp only [if_pos hp]
      exact cd_piProj (cd_imHolonomy V hV _)
    · simp only [if_neg hp]
      exact contDiffAt_const
  · simp only [dif_neg hlt]
    by_cases hgt : μ < ν
    · simp only [dif_pos hgt]
      by_cases hp : (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) ∈ P
      · simp only [if_pos hp]
        exact (cd_piProj (cd_imHolonomy V hV _)).neg
      · simp only [if_neg hp]
        exact contDiffAt_const
    · simp only [dif_neg hgt]
      exact contDiffAt_const
theorem cd_DstarDir (ν : Fin 3) {Gf : ℝ → PeriodicLatticeSite L → M2}
    (hG : ∀ y, ContDiffAt ℝ ⊤ (fun ε => Gf ε y) 0) (x : PeriodicLatticeSite L) :
    ContDiffAt ℝ ⊤ (fun ε => DstarDir (V ε) ν (Gf ε) x) 0 := by
  have hS : ∀ b, SG (fun ε => V ε b) := hV
  have hg : ContDiffAt ℝ ⊤ (fun ε => (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2)) 0 :=
    (hS _).inv
  have hgH : ContDiffAt ℝ ⊤ (fun ε => ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ) 0 :=
    conjTR.contDiff.contDiffAt.comp 0 hg
  have e : (fun ε => DstarDir (V ε) ν (Gf ε) x) = fun ε =>
      (((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2) * Gf ε (periodicLatticeShiftBack x ν) *
        ((((V ε (periodicLatticeShiftBack x ν, ν))⁻¹ : SU2) : M2))ᴴ - Gf ε x := by
    funext ε; rfl
  rw [e]
  exact ((hg.mul (hG _)).mul hgH).sub (hG x)
theorem cd_JfieldLoc (P : Set (PeriodicLatticePlaquette L)) (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ContDiffAt ℝ ⊤ (fun ε => JfieldLoc P (V ε) x μ) 0 := by
  classical
  unfold JfieldLoc
  refine ContDiffAt.sum (fun ν _ => ?_)
  by_cases h : ν = μ
  · simp only [if_pos h]
    exact contDiffAt_const
  · simp only [if_neg h]
    exact cd_DstarDir V hV ν (fun y => cd_FnuMuLoc V hV P ν μ y) x
theorem cd_JSU2Loc (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L) :
    ContDiffAt ℝ ⊤ (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) 0 := by
  have e : (fun ε => ((JSU2Loc 1 P (V ε) b : SuTwo) : M2)) = fun ε =>
      ((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (V ε) b.1 b.2 := by
    funext ε; rfl
  rw [e]
  exact (cd_JfieldLoc V hV P b.1 b.2).const_smul _
theorem source_slope (P : Set (PeriodicLatticePlaquette L)) (b : PeriodicLatticeEdge L)
    (h0 : ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0) :
    ∃ d : M2, d ∈ suTwo ∧
      Tendsto (fun t : ℝ => t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) (𝓝[≠] 0) (𝓝 d) := by
  have hc := cd_JSU2Loc V hV P b
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  have ht := hd.tendsto_slope_zero
  simp only [zero_add, h0, sub_zero] at ht
  refine ⟨_, ?_, ht⟩
  have hcl : IsClosed (suTwo : Set M2) := Submodule.closed_of_finiteDimensional _
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall (fun t => ?_))
  exact suTwo.smul_mem _ (JSU2Loc 1 P (V t) b).2
end SourceSmooth

section Source

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo suTwo BondFnL2)
open AdalyFormal.IngredientFamily (JSU2Loc)

variable {L : PeriodicLatticeExtent}

                                                                                           
theorem exists_source_derivative (V : ℝ → PeriodicLinkConfiguration SU2 L) (hV : SmoothAt0 V)
    (hV0 : V 0 = fun _ => 1) (P : Set (PeriodicLatticePlaquette L)) :
    ∃ J' : BondFnL2 L, Tendsto (fun ε : ℝ =>
      ε⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V ε) b)) : BondFnL2 L)) (𝓝[≠] 0) (𝓝 J') := by
  have h0 : ∀ b, ((JSU2Loc 1 P (V 0) b : SuTwo) : M2) = 0 := by
    intro b
    rw [hV0]
    have := AdalyFormal.IngredientFamily.JSU2Loc_trivial (L := L) 1 P b
    exact congrArg Subtype.val this
  choose d hd hlim using fun b => source_slope V hV P b (h0 b)
  refine ⟨WithLp.toLp 2 (fun b => -(⟨d b, hd b⟩ : SuTwo)), tendsto_piLp_suTwo (fun b => ?_)⟩
  have e : ∀ t : ℝ, ((WithLp.ofLp (t⁻¹ • (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (V t) b)) :
      BondFnL2 L)) b : SuTwo) : M2) = -(t⁻¹ • ((JSU2Loc 1 P (V t) b : SuTwo) : M2)) := by
    intro t
    simp only [PiLp.smul_apply, Submodule.coe_smul, Submodule.coe_neg, smul_neg]
  simp only [e]
  show Tendsto _ _ (𝓝 (-(d b)))
  exact (hlim b).neg
end Source

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                               

                                                                                          
                                                                                        
                                                                                            
                                                                                                 
                                              
section DilFamily

open scoped Matrix.Norms.Frobenius
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2 (Ug Xm sig Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem contDiff_Xm : ContDiff ℝ ⊤ (fun t : ℝ => Xm t) := by
  have e : (fun t : ℝ => Xm t) = fun t => t • (Complex.I • sig) := by
    funext t
    ext i j
    simp [Xm, Matrix.smul_apply, Complex.real_smul, mul_assoc]
  rw [e]
  exact contDiff_id.smul contDiff_const
theorem contDiffAt_Ug (t₀ : ℝ) : ContDiffAt ℝ ⊤ (fun t : ℝ => ((Ug t : SU2) : M2)) t₀ :=
  (NormedSpace.exp_analytic (Xm t₀)).contDiffAt.comp t₀ contDiff_Xm.contDiffAt
end DilFamily

section DilUnits

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLane2 (Ug Ug_zero)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilPattern dilU)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

theorem dilU_zero (q R : ℕ) : dilU q R 0 1 = fun _ => 1 := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [dilU, if_pos he]
    rfl
  · simp only [dilU, if_neg he, ite_self, Ug_zero]
theorem dil_G_k (q R : ℕ) : (geomOf 2 1 (dilTower q R)).k = 1 := rfl
theorem dil_out_site (q R : ℕ) (hq : 0 < q) :
    ∃ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)), x ∉ (geomOf 2 1 (dilTower q R)).Om0 := by
  refine ⟨fun _ => 0, ?_⟩
  show ¬ (4 * q ≤ ((0 : Fin _) : ℕ) ∧ _)
  simp only [Fin.val_zero]
  omega
theorem dil_LP_unit (q R : ℕ) (hq : 0 < q) (U : Cfg (scaleUp 2 1 (dilLu q R))) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) U 1) :=
  delpA_unit (geomOf 2 1 (dilTower q R)) U one_pos (le_refl 2) (dil_out_site q R hq)
theorem dil_wq_pos (q R : ℕ) (j : ℕ) : 0 < AdalyFormal.M1Site.wq (geomOf 2 1 (dilTower q R)) 1 j :=
  wq_pos (geomOf 2 1 (dilTower q R)) one_pos (le_refl 2) j
theorem bgTower_one {L : PeriodicLatticeExtent} (G : TowerGeom L) (i : ℕ) :
    bgTower G (fun _ => 1) i = fun _ => 1 :=
  AdalyFormal.SliceCoerc.ubarTower_trivial G.ell i
theorem dil_Gam_unit {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1) := by
  obtain ⟨Gi, h1, h2⟩ := AdalyFormal.M1Site.exists_Gami_strat 2 1 (le_refl 2)
    (AdalyFormal.M1Site.hdvd_of_admissible hS) (AdalyFormal.M1Site.properTower_geomOf (by norm_num) hS)
    (fun _ => 1) 1 one_pos 0 le_rfl (by norm_num)
    (fun j _ y _ b _ => by simp)
    (fun j _ y _ i _ z _ _ μ _ => by rw [bgTower_one]; simp)
  refine ⟨⟨Gam (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1, Gi, ?_, ?_⟩, rfl⟩
  · ext1 u; exact h1 u
  · ext1 u; exact h2 u
theorem delW_zero (ell k : ℕ) (hell : 0 < ell) : AdalyFormal.W6.delW ell k (fun _ => 0) = 0 := by
  unfold AdalyFormal.W6.delW AdalyFormal.W6.SS
  simp [AdalyFormal.BondComposite.thetaOf_zero ell hell]
theorem dil_Qs_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R) (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (trivialU (scaleUp 2 1 (dilLu q R))) 1 (dilLam q R)).data.Qs :=
  AdalyFormal.W6.qs_injective_strat (by norm_num) (le_refl 2) hS (by omega) (by omega)
    (trivialU _) 1 (dilLam q R) (fun _ => 0) (AdalyFormal.W6.regTower_triv (by norm_num))
    (AdalyFormal.W6.towerClass_triv (by norm_num)) (fun _ _ => le_rfl)
    (fun _ _ => AdalyFormal.W6.rhoOf_zero_lt 2) (by rw [delW_zero 2 1 (by norm_num)]; norm_num)
end DilUnits

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                              

                                                                                              
                                                                                                 
                                                                                               
                                                                                            
                                                                                                 
                                                                                            
                                                                                          
                                              
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

                                                                                       

theorem siteMask_eq_self_of_supp' {L : PeriodicLatticeExtent} (S : Set (PeriodicLatticeSite L))
    (ξ : SiteL2 L) (h : ∀ x, x ∉ S → ξ x = 0) : siteMask S ξ = ξ := by
  classical
  ext x
  rw [siteMask_apply]
  by_cases hx : x ∈ S
  · rw [if_pos hx]
  · rw [if_neg hx, h x hx]
theorem lapDir_eq_mask_lap' {L : PeriodicLatticeExtent} (G : TowerGeom L) (U : Cfg L) (ξ : SiteL2 L)
    (h : ∀ x, x ∉ G.Om0 → ξ x = 0) : lapDir G U ξ = siteMask G.Om0 (lapFull U ξ) := by
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply]
  rw [siteMask_eq_self_of_supp' _ _ h]
theorem final_step' {L : PeriodicLatticeExtent} (G : TowerGeom L) (ξ : SiteL2 L)
    (hξ : ξ ∈ NQp G (flatCfg : Cfg L))
    (hT : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) = 0) :
    gradL2 (flatCfg : Cfg L) ξ = 0 := by
  have hsupp := hξ.1
  have hlap := lapDir_eq_mask_lap' G flatCfg ξ hsupp
  have hmem : lapDir G (flatCfg : Cfg L) ξ ∈ RImage G (flatCfg : Cfg L) :=
    Submodule.mem_map.mpr ⟨ξ, hξ, rfl⟩
  have hR : Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) = 0 := by
    have : Tfull G (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) ξ) =
        Rproj G (flatCfg : Cfg L) (lapFull (flatCfg : Cfg L) ξ) := rfl
    rw [← this]; exact hT
  have horth : lapFull (flatCfg : Cfg L) ξ ∈ (RImage G (flatCfg : Cfg L))ᗮ := by
    have := hR
    unfold Rproj at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp this
  have h1 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp horth _ hmem
  have h2 : ⟪lapDir G (flatCfg : Cfg L) ξ, lapFull (flatCfg : Cfg L) ξ⟫ =
      ‖lapDir G (flatCfg : Cfg L) ξ‖ ^ 2 := by
    have e : ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
        = ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ),
            siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)⟫ := by
      calc ⟪siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ), lapFull (flatCfg : Cfg L) ξ⟫
          = ⟪siteMask G.Om0 (siteMask G.Om0 (lapFull (flatCfg : Cfg L) ξ)),
              lapFull (flatCfg : Cfg L) ξ⟫ := by rw [siteMask_idem]
        _ = _ := siteMask_symm _ _ _
    rw [hlap, e, real_inner_self_eq_norm_sq]
  have h3 : lapDir G (flatCfg : Cfg L) ξ = 0 := by
    rw [h2] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have h4 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = 0 := by
    have : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ⟪siteMask G.Om0 ξ, lapFull (flatCfg : Cfg L) ξ⟫ := by
      rw [siteMask_eq_self_of_supp' _ _ hsupp]
    rw [this, siteMask_symm, ← hlap, h3, inner_zero_right]
  have h5 : ⟪ξ, lapFull (flatCfg : Cfg L) ξ⟫ = ‖gradL2 (flatCfg : Cfg L) ξ‖ ^ 2 := by
    simp only [lapFull, ContinuousLinearMap.comp_apply, gradAdj, ContinuousLinearMap.adjoint_inner_right]
    rw [real_inner_self_eq_norm_sq]
  rw [h5] at h4
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
variable {q R : ℕ}

theorem dsize0 (hq : 0 < q) : scaleUp 2 1 (dilLu q R) 0 + 1 = 12 * (R * q) + 16 * q := by
  have h := dil_fine_size hq R 0
  simpa using h
theorem dsizeT (hq : 0 < q) {μ : Fin 3} (hμ : μ ≠ 0) : scaleUp 2 1 (dilLu q R) μ + 1 = 8 * q := by
  rw [dil_fine_size hq R μ, if_neg hμ]
theorem x0_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h1 := (x 0).isLt
  have h2 := dsize0 (R := R) hq
  omega
theorem xT_lt (hq : 0 < q) (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    (x μ).val < 8 * q := by
  have h1 := (x μ).isLt
  have h2 := dsizeT (R := R) hq hμ
  omega
theorem mem_Om0 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 0 ↔ 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q := Iff.rfl
theorem mem_Om1 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∈ (dilTower q R).Om 1 ↔
      2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := Iff.rfl
theorem not_mem_Om2 (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    x ∉ (dilTower q R).Om 2 := by
  simp [dilTower]
theorem shift_coord_ne {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) {μ ν : Fin 3}
    (h : ν ≠ μ) : (periodicLatticeShift x μ) ν = x ν := by
  unfold periodicLatticeShift
  rw [Function.update_of_ne h]
theorem shift_self_coord {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L) (μ : Fin 3) :
    (periodicLatticeShift x μ) μ = x μ + 1 := by
  unfold periodicLatticeShift
  rw [Function.update_self]
theorem shift0_val_lt {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 < L 0 + 1) : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := by
  rw [shift_self_coord, Fin.val_add_one, if_neg]
  intro hc
  rw [hc, Fin.val_last] at h
  omega
theorem shift0_val_last {L : PeriodicLatticeExtent} (x : PeriodicLatticeSite L)
    (h : (x 0).val + 1 = L 0 + 1) : ((periodicLatticeShift x 0) 0).val = 0 := by
  rw [shift_self_coord, Fin.val_add_one, if_pos]
  ext
  rw [Fin.val_last]
  omega
section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

theorem OmGe1_mem {x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))}
    (h : OmGe (geomOf 2 1 (dilTower q R)) 1 x) : x ∈ (dilTower q R).Om 1 := by
  obtain ⟨i, hi1, hik, y, hy, hxy⟩ := h
  have hi : i = 1 := by
    have : i ≤ 1 := hik
    omega
  subst hi
  obtain ⟨hdiv, hyOm, -⟩ := hy
  rw [mem_Om1] at hyOm ⊢
  have h0 := hxy 0
  have hd := hdiv 0
  have hell : (geomOf 2 1 (dilTower q R)).ell = 2 := rfl
  simp only [pow_one, hell] at hd h0
  have hb : 2 ∣ 10 * (R * q) + 12 * q := ⟨5 * (R * q) + 6 * q, by ring⟩
  omega
include hsupp hQ in
theorem A_zero_off {b : Bond (scaleUp 2 1 (dilLu q R))} (h1 : b.1 ∉ (dilTower q R).Om 1)
    (h2 : periodicLatticeShift b.1 b.2 ∉ (dilTower q R).Om 1) : A b = 0 := by
  by_cases hb : b ∈ bondsOm0 (geomOf 2 1 (dilTower q R))
  · have hL : b ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 := by
      refine ⟨?_, ?_⟩
      · rcases hb with hb | hb
        · exact Or.inl ⟨fun μ => by simp, hb, h1⟩
        · exact Or.inr ⟨fun μ => by simp, hb, h2⟩
      · rintro (h | h)
        · exact h1 (OmGe1_mem h)
        · exact h2 (OmGe1_mem h)
    have h := congrArg (fun v : FSp (geomOf 2 1 (dilTower q R)) => WithLp.ofLp v ⟨0, ⟨b, hL⟩⟩) hQ
    have h' : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) ⟨0, ⟨b, hL⟩⟩ = A b := by
      rw [QfullOf_apply]
      show (((geomOf 2 1 (dilTower q R)).ell : ℝ) ^ 0)⁻¹ •
        (WithLp.ofLp (QlinB (geomOf 2 1 (dilTower q R)) flatCfg 0 A)) b = A b
      rw [QlinB_zero, pow_zero, inv_one, one_smul]
    simp only at h
    rw [h'] at h
    exact h
  · exact hsupp b hb
def sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  Function.update z 0 ((u : ℕ) : Fin (scaleUp 2 1 (dilLu q R) 0 + 1))
omit hq A in
theorem sitex_val (hq : 0 < q) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {u : ℕ}
    (hu : u < 12 * (R * q) + 16 * q) : ((sitex z u) 0).val = u := by
  unfold sitex
  rw [Function.update_self, Fin.val_natCast, dsize0 hq]
  exact Nat.mod_eq_of_lt hu
omit A in
theorem sitex_coord (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {ν : Fin 3}
    (hν : ν ≠ 0) : (sitex z u) ν = z ν := by
  unfold sitex
  rw [Function.update_of_ne hν]
omit A in
theorem sitex_self (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : sitex z (z 0).val = z := by
  unfold sitex
  rw [Fin.cast_val_eq_self, Function.update_eq_self]
omit A in
theorem sitex_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u v : ℕ) :
    sitex (sitex z v) u = sitex z u := by
  unfold sitex
  rw [Function.update_idem]
omit A in
theorem shift_sitex0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    periodicLatticeShift (sitex z u) 0 = sitex z (u + 1) := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem, Function.update_self, Nat.cast_succ]
omit A in
theorem shift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) {μ : Fin 3}
    (hμ : μ ≠ 0) : periodicLatticeShift (sitex z u) μ = sitex (periodicLatticeShift z μ) u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_of_ne hμ, Function.update_comm (Ne.symm hμ)]
omit A in
theorem sitex_of_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (u : ℕ) :
    sitex (periodicLatticeShift z 0) u = sitex z u := by
  unfold periodicLatticeShift sitex
  rw [Function.update_idem]
noncomputable def xi (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  ∑ u ∈ Finset.range (z 0).val, A (sitex z u, 0)
include hq in
/-- longitudinal step. -/
theorem xi_shift0 (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val + 1 < 12 * (R * q) + 16 * q) :
    xi A (periodicLatticeShift z 0) = xi A z + A (z, 0) := by
  unfold xi
  have hz : ((periodicLatticeShift z 0) 0).val = (z 0).val + 1 :=
    shift0_val_lt z (by have h2 := dsize0 (R := R) hq; omega)
  rw [hz, Finset.sum_range_succ]
  simp only [sitex_of_shift0]
  rw [sitex_self]
include hq hR hsupp hQ in
/-- the plaquette identity in the `(0, μ)` plane, from curl-freeness or vanishing of all bonds. -/
theorem trans_step
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (w : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (hw : (w 0).val + 1 < 12 * (R * q) + 16 * q) :
    A (periodicLatticeShift w μ, 0) - A (w, 0) = A (periodicLatticeShift w 0, μ) - A (w, μ) := by
  classical
  have h0μ : (0 : Fin 3) < μ := by
    rcases Fin.pos_iff_ne_zero.mpr hμ with h
    exact h
  have hw0 : ((periodicLatticeShift w 0) 0).val = (w 0).val + 1 :=
    shift0_val_lt w (by have h2 := dsize0 (R := R) hq; omega)
  have hwμ : (periodicLatticeShift w μ) 0 = w 0 := shift_coord_ne w (Ne.symm hμ)
  have hw0μ : ((periodicLatticeShift (periodicLatticeShift w 0) μ) 0).val = (w 0).val + 1 := by
    rw [shift_coord_ne _ (Ne.symm hμ), hw0]
  have hwμ0 : ((periodicLatticeShift (periodicLatticeShift w μ) 0) 0).val = (w 0).val + 1 := by
    rw [shift0_val_lt _ (by have h2 := dsize0 (R := R) hq; rw [hwμ]; omega), hwμ]
  by_cases hin : 4 * q ≤ (w 0).val ∧ (w 0).val + 1 < 12 * (R * q) + 12 * q
  · let p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)) := (w, ⟨(0, μ), h0μ⟩)
    have hp : p ∈ plaqIn ((dilTower q R).Om 0) := by
      intro e he
      simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton, p] at he
      rcases he with rfl | rfl | rfl | rfl
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
      · refine ⟨(mem_Om0 _).mpr ⟨?_, ?_⟩, (mem_Om0 _).mpr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    have hc := hcurl p hp
    simp only [curlValueCovariant, p, flatCfg, RMap_one, LinearMap.id_apply] at hc
    have e : A (periodicLatticeShift w μ, 0) - A (w, 0) - (A (periodicLatticeShift w 0, μ) - A (w, μ)) = 0 := by
      rw [← neg_eq_zero, ← hc]; abel
    exact sub_eq_zero.mp e
  · have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
    have hR1 : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
        ((x 0).val = (w 0).val ∨ (x 0).val = (w 0).val + 1) → x ∉ (dilTower q R).Om 1 := by
      intro x hx hxm
      rw [mem_Om1] at hxm
      rcases hx with hx | hx <;> rw [hx] at hxm <;>
        (by_cases h4 : 4 * q ≤ (w 0).val
         · have h5 : ¬ ((w 0).val + 1 < 12 * (R * q) + 12 * q) := fun h => hin ⟨h4, h⟩
           omega
         · omega)
    have z1 := A_zero_off A hsupp hQ (b := (w, 0)) (hR1 w (Or.inl rfl)) (hR1 _ (Or.inr hw0))
    have z2 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w 0, μ)) (hR1 _ (Or.inr hw0))
      (hR1 _ (Or.inr hw0μ))
    have z3 := A_zero_off A hsupp hQ (b := (periodicLatticeShift w μ, 0))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ]))) (hR1 _ (Or.inr hwμ0))
    have z4 := A_zero_off A hsupp hQ (b := (w, μ)) (hR1 w (Or.inl rfl))
      (hR1 (periodicLatticeShift w μ) (Or.inl (by rw [hwμ])))
    rw [z1, z2, z3, z4]
include hq hR hsupp hQ in
/-- transverse step. -/
theorem xi_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    xi A (periodicLatticeShift z μ) = xi A z + (A (z, μ) - A (sitex z 0, μ)) := by
  unfold xi
  rw [shift_coord_ne z (Ne.symm hμ)]
  have hz := x0_lt hq z
  have e : ∀ u ∈ Finset.range (z 0).val, A (sitex (periodicLatticeShift z μ) u, 0)
      = A (sitex z u, 0) + (A (sitex z (u + 1), μ) - A (sitex z u, μ)) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hval : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
    have ht := trans_step hq hR A hsupp hQ hcurl (sitex z u) hμ (by rw [hval]; omega)
    rw [shift_sitex z u hμ, shift_sitex0] at ht
    rw [← sub_eq_iff_eq_add', ht]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub (fun u => A (sitex z u, μ)),
    sitex_self]
include hq hsupp hQ in
theorem xi_left (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : (z 0).val < 2 * (R * q) + 4 * q) : xi A z = 0 := by
  unfold xi
  refine Finset.sum_eq_zero (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hz := x0_lt hq z
  have hv : ((sitex z u) 0).val = u := sitex_val hq z (by omega)
  refine A_zero_off A hsupp hQ ?_ ?_
  · rw [mem_Om1, hv]; omega
  · rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
include hq hsupp hQ in
/-- beyond the right edge of `Ω₁` the potential equals its value at the right edge. -/
theorem xi_right (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (h : 10 * (R * q) + 12 * q ≤ (z 0).val) :
    xi A z = xi A (sitex z (10 * (R * q) + 12 * q)) := by
  have hz := x0_lt hq z
  have key : ∀ n, 10 * (R * q) + 12 * q + n < 12 * (R * q) + 16 * q →
      xi A (sitex z (10 * (R * q) + 12 * q + n)) = xi A (sitex z (10 * (R * q) + 12 * q)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have hv : ((sitex z (10 * (R * q) + 12 * q + n)) 0).val = 10 * (R * q) + 12 * q + n :=
        sitex_val hq z (by omega)
      rw [← ih (by omega)]
      have e := xi_shift0 hq A (sitex z (10 * (R * q) + 12 * q + n)) (by rw [hv]; omega)
      rw [shift_sitex0] at e
      rw [show 10 * (R * q) + 12 * q + (n + 1) = 10 * (R * q) + 12 * q + n + 1 by ring, e]
      have h0 : A (sitex z (10 * (R * q) + 12 * q + n), 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show sitex z _ ∉ _
          rw [mem_Om1, hv]; omega
        · show periodicLatticeShift (sitex z _) 0 ∉ _
          rw [mem_Om1, shift_sitex0, sitex_val hq z (by omega)]; omega
      rw [h0, add_zero]
  have hk := key ((z 0).val - (10 * (R * q) + 12 * q)) (by omega)
  rw [Nat.add_sub_cancel' h, sitex_self] at hk
  exact hk
noncomputable def Iv (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : SuTwo :=
  xi A (sitex z (10 * (R * q) + 12 * q))
include hq hR hsupp hQ in
theorem Iv_shiftT
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0) :
    Iv A (periodicLatticeShift z μ) = Iv A z := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  unfold Iv
  rw [← shift_sitex z _ hμ, xi_shiftT hq hR A hsupp hQ hcurl _ hμ]
  have hv : ((sitex z (10 * (R * q) + 12 * q)) 0).val = 10 * (R * q) + 12 * q :=
    sitex_val hq z (by omega)
  have e1 : A (sitex z (10 * (R * q) + 12 * q), μ) = 0 := by
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z _ ∉ _
      rw [mem_Om1, hv]; omega
    · show periodicLatticeShift (sitex z _) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv]; omega
  have e2 : A (sitex (sitex z (10 * (R * q) + 12 * q)) 0, μ) = 0 := by
    rw [sitex_sitex]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    refine A_zero_off A hsupp hQ ?_ ?_
    · show sitex z 0 ∉ _
      rw [mem_Om1, hv0]; omega
    · show periodicLatticeShift (sitex z 0) μ ∉ _
      rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
  rw [e1, e2, sub_zero, add_zero]
omit hq hR A in
theorem update_shift_succ {L : PeriodicLatticeExtent} (w : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) :
    Function.update w μ (w μ + ((n + 1 : ℕ) : Fin (L μ + 1))) =
      periodicLatticeShift (Function.update w μ (w μ + ((n : ℕ) : Fin (L μ + 1)))) μ := by
  unfold periodicLatticeShift
  rw [Function.update_idem, Function.update_self, Nat.cast_succ, add_assoc]
include hq hR hsupp hQ in
theorem Iv_update
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) {μ : Fin 3} (hμ : μ ≠ 0)
    (v : Fin (scaleUp 2 1 (dilLu q R) μ + 1)) :
    Iv A (Function.update z μ v) = Iv A z := by
  have hn : ∀ n : ℕ, Iv A (Function.update z μ (z μ + ((n : ℕ) : Fin _))) = Iv A z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [update_shift_succ, Iv_shiftT hq hR A hsupp hQ hcurl _ hμ, ih]
  have h := hn (v - z μ).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h
omit hq hR A in
theorem Iv_update0 (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (v : Fin (scaleUp 2 1 (dilLu q R) 0 + 1)) : Iv A (Function.update z 0 v) = Iv A z := by
  unfold Iv sitex
  rw [Function.update_idem]
include hq hR hsupp hQ in
theorem Iv_const
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) : Iv A z = Iv A (fun _ => 0) := by
  have e : (fun _ => (0 : Fin _) : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) =
      Function.update (Function.update (Function.update z 0 0) 1 0) 2 0 := by
    funext ν
    fin_cases ν <;> simp [Function.update] <;> rfl
  rw [e, Iv_update hq hR A hsupp hQ hcurl _ (by decide), Iv_update hq hR A hsupp hQ hcurl _ (by decide),
    Iv_update0]
omit hq hR A in
theorem coarseShift_sitex (z : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (t : ℕ) :
    coarseShift (sitex z t) 2 0 = sitex z (t + 2) := by
  show periodicLatticeShift (periodicLatticeShift (sitex z t) 0) 0 = _
  rw [shift_sitex0, shift_sitex0]
include hq hR hQ in
/-- one level-1 row along direction `0`: the block sums of the potential agree. -/
theorem row_step (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)))
    (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) (hy0 : 2 ∣ (y 0).val)
    (hlo : 2 * (R * q) + 4 * q ≤ (y 0).val + 2) (hhi : (y 0).val + 2 ≤ 10 * (R * q) + 12 * q) :
    ∑ w ∈ stepBlockOf (coarseShift y 2 0) 1 2, xi A w = ∑ w ∈ stepBlockOf y 1 2, xi A w := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hy0' : ((periodicLatticeShift y 0) 0).val = (y 0).val + 1 := shift0_val_lt y (by omega)
  have hcs0 : ((coarseShift y 2 0) 0).val = (y 0).val + 2 := by
    show ((periodicLatticeShift (periodicLatticeShift y 0) 0) 0).val = _
    rw [shift0_val_lt _ (by rw [hy0']; omega), hy0']
  have hcsT : ∀ ν : Fin 3, ν ≠ 0 → (coarseShift y 2 0) ν = y ν := by
    intro ν hν
    show (periodicLatticeShift (periodicLatticeShift y 0) 0) ν = y ν
    rw [shift_coord_ne _ hν, shift_coord_ne _ hν]
  have hc : (y, (0 : Fin 3)) ∈ bondsLam (geomOf 2 1 (dilTower q R)) 1 := by
    refine ⟨?_, ?_⟩
    · by_cases hya : 2 * (R * q) + 4 * q ≤ (y 0).val
      · left
        show y ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨hya, by omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ (y μ).val
        fin_cases μ
        · simpa using hy0
        · simpa using hy1
        · simpa using hy2
      · right
        have e1 : coarseShift (y, (0 : Fin 3)).1 ((geomOf 2 1 (dilTower q R)).ell ^ 1) (y, (0 : Fin 3)).2 =
            coarseShift y 2 0 := rfl
        rw [e1]
        show coarseShift y 2 0 ∈ (geomOf 2 1 (dilTower q R)).Lam 1
        refine ⟨fun μ => ?_, (mem_Om1 _).mpr ⟨by rw [hcs0]; omega, by rw [hcs0]; omega⟩, not_mem_Om2 _⟩
        show 2 ^ 1 ∣ ((coarseShift y 2 0) μ).val
        fin_cases μ
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 0).val
          rw [hcs0]; simpa using (Nat.dvd_add hy0 (dvd_refl 2))
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 1).val
          rw [hcsT 1 (by decide)]; simpa using hy1
        · show 2 ^ 1 ∣ ((coarseShift y 2 0) 2).val
          rw [hcsT 2 (by decide)]; simpa using hy2
    · rintro (h | h) <;>
        exact not_OmGe_of_lt (G := geomOf 2 1 (dilTower q R)) (lt_of_eq_of_lt (dil_G_k q R) (by norm_num)) _ h
  let p : BIdx (geomOf 2 1 (dilTower q R)) := ⟨1, ⟨(y, 0), hc⟩⟩
  have hrow : WithLp.ofLp (QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A) p = 0 := by
    rw [hQ]; rfl
  have hQrow := AdalyFormal.W6.Qflat_row (ell := 2) (k := 1) (Lu := dilLu q R) (S := dilTower q R)
    (by norm_num) A p
  have hline : AdalyFormal.Balaban.LineIntegralCovariant.lineCoarseRestrictSuTwo (2 ^ (p.1 : ℕ))
      (WithLp.ofLp A) (AdalyFormal.W6.rowCB (by norm_num) p) = 0 := by
    rw [← hQrow]; exact hrow
  have hline' : (1 / ((2 : ℕ) : ℝ) ^ 4) • ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2,
      A (pathSite x 0 i, 0) = 0 := hline
  have hsum : ∑ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) = 0 := by
    rcases smul_eq_zero.mp hline' with h | h
    · norm_num at h
    · exact h
  have hpt : ∀ x ∈ blockOf y 2, ∑ i ∈ Finset.range 2, A (pathSite x 0 i, 0) =
      xi A (coarseShift x 2 0) - xi A x := by
    intro x hx
    have hxb := (mem_blockOf.mp hx) 0
    have hx0 : (x 0).val + 1 < 12 * (R * q) + 16 * q := by omega
    have hsx : ((periodicLatticeShift x 0) 0).val = (x 0).val + 1 := shift0_val_lt x (by omega)
    have e1 := xi_shift0 hq A x hx0
    have e2 := xi_shift0 hq A (periodicLatticeShift x 0) (by rw [hsx]; omega)
    show _ = xi A (periodicLatticeShift (periodicLatticeShift x 0) 0) - xi A x
    rw [e2, e1, Finset.sum_range_succ, Finset.sum_range_one]
    show A (x, 0) + A (periodicLatticeShift x 0, 0) = _
    abel
  have hfit : ∀ ν : Fin 3, (y ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; omega
    · have := xT_lt hq y hν
      have h8 := dsizeT (R := R) hq hν
      have hev : 2 ∣ (y ν).val := by
        fin_cases ν
        · exact absurd rfl hν
        · exact hy1
        · exact hy2
      omega
  have hfit' : ∀ ν : Fin 3, ((coarseShift y 2 0) ν).val + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hcs0]; omega
    · rw [hcsT ν hν]; exact hfit ν
  have hshift := AdalyFormal.CurvBlock.block_sum_shift 1 2 2 0 hfit hfit' (xi A)
  rw [← hshift]
  rw [AdalyFormal.Balaban.QjComposite.stepBlockOf_one] at *
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib] at hsum
  exact sub_eq_zero.mp hsum
include hq hR hsupp hQ in
/-- the block sums vanish along the whole longitudinal chain of blocks. -/
theorem chain_zero (y : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) (hy1 : 2 ∣ (y 1).val) (hy2 : 2 ∣ (y 2).val) :
    ∀ m : ℕ, 2 * m ≤ 8 * (R * q) + 8 * q + 2 →
      ∑ w ∈ stepBlockOf (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 1 2, xi A w = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  intro m
  induction m with
  | zero =>
    intro _
    refine Finset.sum_eq_zero (fun w hw => ?_)
    have hb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * 0)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * 0 :=
      sitex_val hq y (by omega)
    rw [hv] at hb
    exact xi_left hq A hsupp hQ w (by omega)
  | succ m ih =>
    intro hm
    have hv : ((sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m :=
      sitex_val hq y (by omega)
    have e : sitex y (2 * (R * q) + 4 * q - 2 + 2 * (m + 1)) =
        coarseShift (sitex y (2 * (R * q) + 4 * q - 2 + 2 * m)) 2 0 := by
      rw [coarseShift_sitex]
      congr 1
    rw [e, row_step hq hR A hQ _ (by rw [sitex_coord _ _ (by decide)]; exact hy1)
      (by rw [sitex_coord _ _ (by decide)]; exact hy2) (by rw [hv]; omega) (by rw [hv]; omega)
      (by rw [hv]; omega)]
    exact ih (by omega)
include hq hR hsupp hQ in
theorem Iv_zero
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    Iv A (fun _ => 0) = 0 := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  let y0 : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) := fun _ => 0
  have hb := chain_zero hq hR A hsupp hQ y0 (by simp [y0]) (by simp [y0])
    (4 * (R * q) + 4 * q + 1) (by omega)
  have hv : ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 0).val =
      10 * (R * q) + 12 * q := by
    rw [sitex_val hq y0 (by omega)]; omega
  have e : ∀ w ∈ stepBlockOf (sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) 1 2,
      xi A w = Iv A (fun _ => 0) := by
    intro w hw
    have hwb := ((AdalyFormal.Balaban.QjComposite.mem_stepBlockOf).mp hw) 0
    rw [hv] at hwb
    rw [xi_right hq A hsupp hQ w (by omega)]
    exact Iv_const hq hR A hsupp hQ hcurl w
  have hfit : ∀ ν : Fin 3, ((sitex y0 (2 * (R * q) + 4 * q - 2 + 2 * (4 * (R * q) + 4 * q + 1))) ν).val
      + 1 * 2 ≤ scaleUp 2 1 (dilLu q R) ν + 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν; rw [hv]; omega
    · rw [sitex_coord _ _ hν]
      have h8 := dsizeT (R := R) hq hν
      show ((0 : Fin _) : ℕ) + 1 * 2 ≤ _
      simp only [Fin.val_zero]
      omega
  rw [Finset.sum_congr rfl e, Finset.sum_const,
    AdalyFormal.Balaban.QjComposite.card_stepBlockOf _ 1 2 one_pos hfit] at hb
  have h8 : (8 : ℝ) • Iv A (fun _ => 0) = 0 := by
    rw [show (8 : ℝ) = ((2 ^ 3 : ℕ) : ℝ) by norm_num, Nat.cast_smul_eq_nsmul]
    exact hb
  rcases smul_eq_zero.mp h8 with h | h
  · norm_num at h
  · exact h
include hq hR hsupp hQ in
theorem xi_mem_NQp
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    (WithLp.toLp 2 (xi A) : SiteL2 (scaleUp 2 1 (dilLu q R))) ∈
      NQp (geomOf 2 1 (dilTower q R)) flatCfg := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  have hzero : ∀ x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)),
      ¬ ((dilTower q R).Om 1 x) → xi A x = 0 := by
    intro x hx
    have hx' : ¬ (2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q) := hx
    by_cases h : (x 0).val < 2 * (R * q) + 4 * q
    · exact xi_left hq A hsupp hQ x h
    · rw [xi_right hq A hsupp hQ x (by omega)]
      show Iv A x = 0
      rw [Iv_const hq hR A hsupp hQ hcurl x, Iv_zero hq hR A hsupp hQ hcurl]
  refine ⟨fun x hx => ?_, fun j hj y hy => ?_⟩
  · show xi A x = 0
    refine hzero x (fun h1 => hx ?_)
    have h1' : 2 * (R * q) + 4 * q ≤ (x 0).val ∧ (x 0).val < 10 * (R * q) + 12 * q := h1
    show 4 * q ≤ (x 0).val ∧ (x 0).val < 12 * (R * q) + 12 * q
    omega
  · have hj1 : j = 0 ∨ j = 1 := by
      have : j ≤ 1 := hj
      omega
    rcases hj1 with rfl | rfl
    · rw [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero]
      show xi A y = 0
      exact hzero y hy.2.2
    · rw [Qlev_apply, Qcomposite_one', bgTower_zero']
      show stepAverage (2 ^ 0) (trivialU _) 2 (xi A) y = 0
      rw [AdalyFormal.Balaban.QjComposite.stepAverage_trivialU, pow_zero]
      obtain ⟨hdiv, hy1, -⟩ := hy
      have hy1' : 2 * (R * q) + 4 * q ≤ (y 0).val ∧ (y 0).val < 10 * (R * q) + 12 * q := hy1
      have hd0 : 2 ∣ (y 0).val := by simpa using hdiv 0
      have hd1 : 2 ∣ (y 1).val := by simpa using hdiv 1
      have hd2 : 2 ∣ (y 2).val := by simpa using hdiv 2
      obtain ⟨m, hm⟩ : ∃ m, (y 0).val = 2 * (R * q) + 4 * q - 2 + 2 * m := by
        obtain ⟨t, ht⟩ := hd0
        refine ⟨t - (R * q) - 2 * q + 1, ?_⟩
        omega
      have hc := chain_zero hq hR A hsupp hQ y hd1 hd2 m (by omega)
      rw [← hm, sitex_self] at hc
      rw [hc, smul_zero]
include hq hR hsupp hQ in
theorem A_eq_grad
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0) :
    A = gradL2 flatCfg (WithLp.toLp 2 (xi A)) := by
  have hRq : 1 ≤ R * q := Nat.mul_pos (by omega) hq
  have hN := dsize0 (R := R) hq
  refine PiLp.ext (fun e => ?_)
  obtain ⟨z, μ⟩ := e
  show A (z, μ) = gradValueCovariant flatCfg (xi A) (z, μ)
  simp only [gradValueCovariant, flatCfg, RMap_one, LinearMap.id_apply]
  have hz := x0_lt hq z
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hz1 : (z 0).val + 1 < 12 * (R * q) + 16 * q
    · rw [xi_shift0 hq A z hz1]; abel
    · have hzl : (z 0).val + 1 = scaleUp 2 1 (dilLu q R) 0 + 1 := by omega
      have h0 : ((periodicLatticeShift z 0) 0).val = 0 := shift0_val_last z hzl
      have e1 : xi A (periodicLatticeShift z 0) = 0 := xi_left hq A hsupp hQ _ (by rw [h0]; omega)
      have e2 : xi A z = 0 := by
        rw [xi_right hq A hsupp hQ z (by omega)]
        show Iv A z = 0
        rw [Iv_const hq hR A hsupp hQ hcurl z, Iv_zero hq hR A hsupp hQ hcurl]
      have e3 : A (z, 0) = 0 := by
        refine A_zero_off A hsupp hQ ?_ ?_
        · show z ∉ _
          rw [mem_Om1]; omega
        · show periodicLatticeShift z 0 ∉ _
          rw [mem_Om1, h0]; omega
      rw [e1, e2, e3, sub_zero]
  · rw [xi_shiftT hq hR A hsupp hQ hcurl z hμ]
    have hv0 : ((sitex z 0) 0).val = 0 := sitex_val hq z (by omega)
    have e3 : A (sitex z 0, μ) = 0 := by
      refine A_zero_off A hsupp hQ ?_ ?_
      · show sitex z 0 ∉ _
        rw [mem_Om1, hv0]; omega
      · show periodicLatticeShift (sitex z 0) μ ∉ _
        rw [mem_Om1, shift_coord_ne _ (Ne.symm hμ), hv0]; omega
    rw [e3]; abel
include hq hR hsupp hQ in
/-- **The flat kernel of the dilated tower is trivial.** -/
theorem dil_flat_kernel
    (hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0), curlValueCovariant flatCfg (WithLp.ofLp A) p = 0)
    (hT : Tfull (geomOf 2 1 (dilTower q R)) flatCfg A = 0) : A = 0 := by
  have hg := A_eq_grad hq hR A hsupp hQ hcurl
  have hmem := xi_mem_NQp hq hR A hsupp hQ hcurl
  rw [hg] at hT ⊢
  exact final_step' _ _ hmem hT
end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                       
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

                                                                                              
                                                                              
theorem flat_ginv_form_in (P : IngrBParams) (hU : P.U = flatCfg) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selIn selIn P).Ginv x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2
      + ‖Tfull P.G P.U (iE P.G x)‖ ^ 2
      + ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
  rw [BaseDataS.inner_Ginv]
  have hD : ⟪x, (dataS selIn selIn P).Dpi x⟫ =
      ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Dpi x⟫ = ⟪iE P.G x, DpiFull P.G P.U P.a (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (DpiFull P.G P.U P.a (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, hU]
    exact AdalyFormal.StatementLaneG.inner_DpiFull_flat P.G P.a (iE P.G x)
  have hM : ⟪x, (dataS selIn selIn P).Mass x⟫ =
      ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 := by
    have : ⟪x, (dataS selIn selIn P).Mass x⟫ = ⟪iE P.G x, MassFull P.G P.a P.sector (iE P.G x)⟫ := by
      show ⟪x, (pE P.G) (MassFull P.G P.a P.sector (iE P.G x))⟫ = _
      rw [pE_inner_right]
    rw [this, inner_MassFull]
    rfl
  rw [hD, hM]
  rfl
theorem dil_flat_pos {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv x⟫ := by
  set P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R) with hP
  have hform := flat_ginv_form_in P rfl x
  have t1 := sq_nonneg ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖
  have t2 := sq_nonneg ‖Tfull P.G P.U (iE P.G x)‖
  have hell : (0 : ℝ) < P.ell := by show (0 : ℝ) < (2 : ℕ); norm_num
  have t3 : 0 ≤ ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 :=
    Finset.sum_nonneg (fun p _ => by
      have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
      positivity)
  rcases (add_nonneg (add_nonneg t1 t2) t3).lt_or_eq with h | h
  · rw [hform]; exact h
  · exfalso
    apply hx
    have h1 : ‖plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x))‖ ^ 2 = 0 := by
      linarith
    have h2 : ‖Tfull P.G P.U (iE P.G x)‖ ^ 2 = 0 := by linarith
    have h3 : ∑ p : BIdx P.G, P.a * (P.ell : ℝ) ^ (p.1 : ℕ) * ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
      linarith
    have hm : plaqMask (plaqIn P.G.Om0) (curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x)) = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
    have hT : Tfull P.G P.U (iE P.G x) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg (iE P.G x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity)).mp h3
      refine PiLp.ext (fun p => ?_)
      have h1 := hz p (Finset.mem_univ p)
      have hp : 0 < P.a * (P.ell : ℝ) ^ (p.1 : ℕ) := by
        have : (0 : ℝ) < P.a := by show (0 : ℝ) < 1; norm_num
        positivity
      have h2 : ‖P.sector.Qfull (iE P.G x) p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact absurd h hp.ne'
        · exact h
      have := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
      exact this
    have hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → (iE P.G x) b = 0 :=
      fun b hb => x.2 b hb
    have hcurl : ∀ p ∈ plaqIn ((dilTower q R).Om 0),
        curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x)) p = 0 := by
      intro p hp
      have h := congrArg (fun v : AdalyFormal.Balaban.CovariantHjMinimizer.PlaqFnL2 P.Lf => WithLp.ofLp v p) hm
      simp only [plaqMask_apply, PiLp.zero_apply] at h
      rw [if_pos (show p ∈ plaqIn P.G.Om0 from hp)] at h
      have e : curlCovariantCLM_L2 (flatCfg : Cfg P.Lf) (iE P.G x) =
          WithLp.toLp 2 (curlValueCovariant flatCfg (WithLp.ofLp (iE P.G x))) :=
        curlCovariantCLM_L2_toLp _ _
      rw [e] at h
      exact h
    have hA := dil_flat_kernel hq hR (iE P.G x) hsupp hQ hcurl hT
    exact Subtype.ext hA
theorem dil_flat_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv := by
  set M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
    (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R))).Ginv with hMdef
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have := dil_flat_pos hq hR x hne
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  exact (ContinuousLinearMap.isUnit_iff_bijective).mpr
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (M : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →ₗ[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))))).mp hinj⟩
end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

section Final

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace extP extA extD InteriorRegularity InteriorSoft)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

                                 
noncomputable abbrev dilV (q R : ℕ) : ℝ → Cfg (scaleUp 2 1 (dilLu q R)) := fun ε => dilU q R ε 1
theorem dataFam_dil_zero (sD sJ : PlaqSel) (q R : ℕ) :
    dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (dilU q R 0 1) 1 (dilLam q R)) = _
  rw [dilU_zero]
theorem dil_B0_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  exact dil_flat_unit hq hR
theorem dil_B0_psd {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    AdalyFormal.D1Literal.PSD
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Ginv := by
  rw [dataFam_dil_zero]
  intro v
  by_cases hv : v = 0
  · rw [hv, inner_zero_left]
  · exact (dil_flat_pos hq hR v hv).le
theorem dil_Qs0_inj {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    Function.Injective
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs := by
  rw [dataFam_dil_zero]
  exact dil_Qs_inj hq hR16 hS
theorem dil_N0_unit {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) :
    IsUnit (((dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Q.comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).G).comp
      (dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0).Qs) := by
  set D0 := dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (dilV q R) 1 (dilLam q R) 0
  have hL : D0.Laws := dataS_laws selIn selIn _
  obtain ⟨m, hm, hmc⟩ := AdalyFormal.D1Literal.psd_coercive D0.Ginv (D0.Ginv_symm hL)
    (dil_B0_psd hq (by omega)) (dil_B0_unit hq (by omega))
  exact isUnit_Q_inv_Qs (D0.Ginv_symm hL) hm hmc D0.Q_adj (dil_Qs0_inj hq hR16 hS)
section DilCont
variable {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))

end DilCont

                                                                                                 
                                                                                                   
                             
end Final

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                  
section Close

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU dil_admissible)
open AdalyFormal.Round5.Guarded.IVTR1 (twistU twistP twistA twistD)
open AdalyFormal.Round8.Guarded.SignFree (CofinalTwistSeparation goalNeg2_of_cofinalTwistSeparation
  not_cofinalTwistSeparation_of_goalPos1)
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                                                     
noncomputable abbrev flatData (q R : ℕ) :=
  dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1 (dilLam q R))
noncomputable def vacCoupling (q R : ℕ) (J' : TwistSpace q R) (v : TwistSpace q R) : ℝ :=
  2 * ⟪(flatData q R).H (C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))), J'⟫
end Close

end AdalyFormal.Round9.Guarded.AnalyticR2


set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000

namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint

open scoped RealInnerProductSpace
open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.D1Literal (PSD)

                                                                                 

section BulkFamily

open scoped Matrix.Norms.Frobenius

                                                                                       
                                            
noncomputable abbrev bulkV (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun ε => QualitativeR2.bulkU q R f ε
theorem bulkU_link_contDiff (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R))) :
    ContDiff ℝ ⊤ (fun ε : ℝ => ((QualitativeR2.bulkU q R f ε e : SU2) : M2)) := by
  classical
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [QualitativeR2.bulkU, maskedU, if_pos he]
    exact contDiff_const
  · simp only [QualitativeR2.bulkU, maskedU, if_neg he]
    have hl : ContDiff ℝ ⊤ (fun ε : ℝ => ε * f e) := contDiff_id.mul contDiff_const
    refine contDiff_iff_contDiffAt.mpr (fun ε => ?_)
    have h := (AnalyticR2.contDiffAt_Ug (ε * f e)).comp ε hl.contDiffAt
    exact h
theorem bulkV_smooth (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.SmoothAt0 (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).contDiffAt
theorem bulkV_contFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AdalyFormal.D1Literal.ContFam (bulkV q R f) :=
  fun e => (bulkU_link_contDiff q R f e).continuous
end BulkFamily

theorem bulkU_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.bulkU q R f 0 = fun _ => 1 := by
  classical
  funext e
  simp only [QualitativeR2.bulkU, maskedU, zero_mul, Ug_zero, ite_self]
theorem bulk_dataFam_zero (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      dataS sD sJ (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (fun _ => 1) 1
        (dilLam q R)) := by
  show dataS sD sJ (gparams 2 1 (dilLu q R) _ (dilTower q R) (QualitativeR2.bulkU q R f 0) 1
    (dilLam q R)) = _
  rw [bulkU_zero]
theorem bulk_dataFam_zero_eq (sD sJ : PlaqSel) (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1 (dilLam q R) 0 =
      AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R) (AnalyticR2.dilV q R) 1
        (dilLam q R) 0 := by
  rw [bulk_dataFam_zero, AnalyticR2.dataFam_dil_zero]
theorem bulkD_eq_dataFam (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    QualitativeR2.bulkD q R f ε =
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
        (dilLam q R) ε).Delta2 (dataS_laws selIn selIn _) := rfl
theorem bulk_LP0 {q R : ℕ} (hq : 0 < q) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AdalyFormal.M1Site.LP (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) :=
  AnalyticR2.dil_LP_unit q R hq _
theorem bulk_Gam0 {q R : ℕ} (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsUnit (AnalyticR2.Gam (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact AnalyticR2.dil_Gam_unit hS
theorem bulk_reg0 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    RegBg ((geomOf 2 1 (dilTower q R)).ell ^ 0) (geomOf 2 1 (dilTower q R)).ell (bulkV q R f 0) := by
  rw [show bulkV q R f 0 = fun _ => 1 from bulkU_zero q R f]
  exact RegBg_flat _ _
theorem bulk_W_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1) 0 :=
  AnalyticR2.continuousAt_Wop (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)
theorem bulk_T_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => Tfull (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_Tfull (bulkV_contFam q R f) (geomOf 2 1 (dilTower q R)) rfl 1
    (bulk_LP0 hq f) (AnalyticR2.dil_wq_pos q R) (bulk_Gam0 hS f)
theorem bulk_Q_cont (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)) 0 :=
  AnalyticR2.continuousAt_QfullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f)
theorem bulk_carrier_cont {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (sD sJ : PlaqSel) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam sD sJ (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0 :=
  AnalyticR2.continuousAt_Ginv_dataS sD sJ (by norm_num) (dilTower q R) (bulkV q R f) 1
    (dilLam q R) (bulkV_contFam q R f) (bulk_W_cont hq hS f) (bulk_T_cont hq hS f)
    (bulk_Q_cont q R f)
theorem bulk_H_cont {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).H) 0 := by
  have hQc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Q) 0 := by
    show ContinuousAt (fun ε => (QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
      (iE (geomOf 2 1 (dilTower q R)))) 0
    exact AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const
  have hQsc : ContinuousAt (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2)
      (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Qs) 0 := by
    show ContinuousAt (fun ε => ContinuousLinearMap.adjoint
      ((QfullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)).comp
        (iE (geomOf 2 1 (dilTower q R))))) 0
    exact AnalyticR2.cont_adjoint.continuousAt.comp
      (AnalyticR2.continuousAt_clm_comp (bulk_Q_cont q R f) continuousAt_const)
  have hB0 : IsUnit (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Ginv := by
    rw [bulk_dataFam_zero]
    exact AnalyticR2.dil_flat_unit hq (by omega)
  have hN0 : IsUnit (((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) 0).Q.comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).G).comp
      (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).Qs) := by
    rw [bulk_dataFam_zero_eq]
    exact AnalyticR2.dil_N0_unit hq hR16 hS
  exact AnalyticR2.continuousAt_H
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (bulk_carrier_cont hq hS f selIn selIn) hQc hQsc hB0 hN0
theorem bulk_C2_tendsto {q R : ℕ} (hq : 0 < q) (hS : Admissible 2 (2 * q) R 1 (dilTower q R))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (A : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) :
    Tendsto (fun ε => (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
      (bulkV q R f) 1 (dilLam q R) ε).C2 A) (𝓝 0)
      (𝓝 ((AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) 0).C2 A)) := by
  show Tendsto (fun ε => C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f ε)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f ε) 1 (iE (geomOf 2 1 (dilTower q R)) A))) (𝓝 0)
    (𝓝 (C2fullOf (geomOf 2 1 (dilTower q R)) (bulkV q R f 0)
      (Wop (geomOf 2 1 (dilTower q R)) (bulkV q R f 0) 1 (iE (geomOf 2 1 (dilTower q R)) A))))
  exact AnalyticR2.tendsto_C2fullOf (bulkV q R f) (bulkV_smooth q R f) (geomOf 2 1 (dilTower q R))
    rfl (bulk_reg0 q R f) (AnalyticR2.tendsto_clm_apply₂ (bulk_W_cont hq hS f) tendsto_const_nhds)
theorem bulk_J_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ J' : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε => ε⁻¹ • (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R)
        (bulkV q R f) 1 (dilLam q R) ε).J) (𝓝[≠] 0) (𝓝 J') := by
  obtain ⟨J', hJ'⟩ := AnalyticR2.exists_source_derivative (bulkV q R f) (bulkV_smooth q R f)
    (bulkU_zero q R f) (plaqIn (geomOf 2 1 (dilTower q R)).Om0)
  refine ⟨pE (geomOf 2 1 (dilTower q R)) J', ?_⟩
  show Tendsto (fun ε : ℝ => ε⁻¹ • pE (geomOf 2 1 (dilTower q R))
      (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
        (plaqIn (geomOf 2 1 (dilTower q R)).Om0) (bulkV q R f ε) b)))) (𝓝[≠] 0)
    (𝓝 (pE (geomOf 2 1 (dilTower q R)) J'))
  simp only [← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp hJ'
theorem bulk_exists_D1 {q R : ℕ} (hq : 0 < q) (hR16 : 16 ≤ R)
    (hS : Admissible 2 (2 * q) R 1 (dilTower q R)) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ D₁ : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      Tendsto (fun ε : ℝ => ε⁻¹ • QualitativeR2.bulkD q R f ε) (𝓝[≠] 0) (𝓝 D₁) := by
  obtain ⟨J', hJ⟩ := bulk_J_tendsto q R f
  obtain ⟨D₁, hD₁⟩ := AnalyticR2.tendsto_Delta2_div
    (AnalyticR2.dataFam selIn selIn (by norm_num : 0 < 2) (dilTower q R) (bulkV q R f) 1
      (dilLam q R))
    (fun ε => dataS_laws selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (bulkV q R f ε) 1 (dilLam q R)))
    (bulk_H_cont hq hR16 hS f) (bulk_C2_tendsto hq hS f) J' hJ
  refine ⟨D₁, ?_⟩
  simp only [bulkD_eq_dataFam]
  exact hD₁
theorem bulkD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : QualitativeR2.bulkD q R f 0 = 0 := by
  rw [← QualitativeR2.pathD_base q R (QualitativeR2.uthPath_zero q R) f 0]
  exact pathD_zero hq hR h3 (uthPath q R) f 1 0
theorem bulk_hasDerivAt {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ∃ De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) De 0 := by
  obtain ⟨D₁, hD₁⟩ := bulk_exists_D1 hq hR16 (dil_admissible hq hR) f
  have hq1 : 1 ≤ q := hq
  have h3 : 3 ≤ R * (2*q) := by nlinarith
  have h0 := bulkD_zero hq hR h3 f
  refine ⟨D₁, (hasDerivAt_iff_tendsto_slope_zero (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε)
    (f' := D₁) (x := 0)).mpr ?_⟩
  refine hD₁.congr' (Filter.Eventually.of_forall (fun t => ?_))
  simp only [zero_add, h0, sub_zero]
noncomputable def corrDeriv (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  deriv (fun ε : ℝ => QualitativeR2.bulkD q R f ε) 0
theorem hasDerivAt_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) 0 := by
  obtain ⟨De, h⟩ := bulk_hasDerivAt hq hR hR16 f
  have e : corrDeriv q R f = De :=
    HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (f' := De) (x := 0) h
  rw [e]
  exact h
theorem interiorSoft_corrDeriv {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    QualitativeR2.InteriorSoft q R f (corrDeriv q R f) := by
  have hS := dil_admissible hq hR
  refine ⟨?_, bulk_W_cont hq hS f, hasDerivAt_corrDeriv hq hR hR16 f⟩
  show ContinuousAt (fun ε => (AnalyticR2.dataFam selAll selAll (by norm_num : 0 < 2)
    (dilTower q R) (bulkV q R f) 1 (dilLam q R) ε).Ginv) 0
  exact bulk_carrier_cont hq hS f selAll selAll
theorem flat_loc_unit {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) :
    IsUnit (dataS selIn selIn (QualitativeR2.flatP q R)).Ginv :=
  AnalyticR2.dil_flat_unit hq hR
theorem bulkU_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkU q R (fun e => c * f e) ε = QualitativeR2.bulkU q R f (c * ε) := by
  unfold QualitativeR2.bulkU
  congr 1
  funext e
  ring
theorem bulkD_smul (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c ε : ℝ) :
    QualitativeR2.bulkD q R (fun e => c * f e) ε = QualitativeR2.bulkD q R f (c * ε) := by
  have hd : dataS selIn selIn (QualitativeR2.bulkP q R (fun e => c * f e) ε) =
      dataS selIn selIn (QualitativeR2.bulkP q R f (c * ε)) := by
    unfold QualitativeR2.bulkP
    rw [bulkU_smul]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _
theorem corrDeriv_smul {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR16 : 16 ≤ R)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ) :
    corrDeriv q R (fun e => c * f e) = c • corrDeriv q R f := by
  have h1 := hasDerivAt_corrDeriv hq hR hR16 f
  have hl : HasDerivAt (fun ε : ℝ => c * ε) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have h1' : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f ε) (corrDeriv q R f) (c * 0) := by
    rw [mul_zero]
    exact h1
  have h2 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R f (c * ε)) (c • corrDeriv q R f) 0 :=
    HasDerivAt.scomp (g₁ := fun ε : ℝ => QualitativeR2.bulkD q R f ε) (h := fun ε : ℝ => c * ε)
      0 h1' hl
  have e : (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε) =
      fun ε => QualitativeR2.bulkD q R f (c * ε) := funext (bulkD_smul q R f c)
  have h3 : HasDerivAt (fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
      (c • corrDeriv q R f) 0 := by
    rw [e]
    exact h2
  exact HasDerivAt.deriv (f := fun ε : ℝ => QualitativeR2.bulkD q R (fun e => c * f e) ε)
    (f' := c • corrDeriv q R f) (x := 0) h3
theorem canonicalCoupling_smul {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R)))}
    {c : ℝ} (hc : c ≠ 0) (h : QualitativeR2.CanonicalCoupling q R V De) :
    QualitativeR2.CanonicalCoupling q R V (c • De) := by
  obtain ⟨c₀, hc₀, hs⟩ := h
  have e : ∀ u, ⟪u, (c • De) u⟫ = c * ⟪u, De u⟫ := fun u => by
    rw [smul_apply, real_inner_smul_right]
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hc' : 0 ≤ -c := by linarith
    refine ⟨(-c) * c₀, mul_pos (neg_pos.mpr hneg) hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hc'
      rw [e]
      nlinarith [h1]
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hc'
      rw [e]
      nlinarith [h1]
  · refine ⟨c * c₀, mul_pos hpos hc₀, ?_⟩
    rcases hs with hp | hn
    · refine Or.inl (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hp u hu) hpos.le
      rw [e]
      nlinarith [h1]
    · refine Or.inr (fun u hu => ?_)
      have h1 := mul_le_mul_of_nonneg_left (hn u hu) hpos.le
      rw [e]
      nlinarith [h1]
theorem exists_profile_scale {L : PeriodicLatticeExtent} (f : Bond L → ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ e, |c * f e| ≤ 1 := by
  have hs0 : 0 ≤ ∑ e, |f e| := Finset.sum_nonneg (fun e _ => abs_nonneg (f e))
  have hpos : (0 : ℝ) < 1 + ∑ e, |f e| := by linarith
  refine ⟨1 / (1 + ∑ e, |f e|), one_div_pos.mpr hpos, fun e => ?_⟩
  have h1 : |f e| ≤ ∑ e, |f e| :=
    Finset.single_le_sum (f := fun e => |f e|) (fun e _ => abs_nonneg (f e)) (Finset.mem_univ e)
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hpos), one_div, inv_mul_le_iff₀ hpos]
  linarith
def CofinalAnyPathCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
      QualitativeR2.AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ,
        QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R f)
theorem cofinalVacuumCoupling_of_anyPath (h : CofinalAnyPathCoupling) : CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, f, hc⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨c, hcpos, hcb⟩ := exists_profile_scale f
  have hc' : QualitativeR2.CanonicalCoupling (2^j) R V (corrDeriv (2^j) R (fun e => c * f e)) := by
    rw [corrDeriv_smul hq hR (by omega) f c]
    exact canonicalCoupling_smul hcpos.ne' hc
  exact ⟨R, hRR, hR, hR18, V, hVc, fun e => c * f e, hcb,
    QualitativeR2.vacuumCoupling_of_soft hq hR hroom hVc hVa hV0 (flat_loc_unit hq (by omega))
      hneg (interiorSoft_corrDeriv hq hR (by omega) _) hc'⟩
theorem goalNeg2_of_cofinalAnyPathCoupling (h : CofinalAnyPathCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_anyPath h)
end AdalyFormal.Round9.Guarded.QualitativeR2Joint

namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.D1Literal

open Classical
theorem half_rotation_matrix : (uθ (Real.pi / 2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I, 0; 0, -Complex.I] := by
  change uMat (Real.pi / 2) = _
  simp only [uMat, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [show -((Real.pi : ℂ) / 2 * Complex.I) = -Real.pi / 2 * Complex.I by ring,
    Complex.exp_neg_pi_div_two_mul_I]
end AdalyFormal.Round10.Dictionary

                                                                                      
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.PhaseSource
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily
open AdalyFormal.D1Literal (uθ uMat)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}

theorem phase_zero : uθ 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uθ, uMat]
theorem phase_mul (a b : ℝ) : uθ a * uθ b = uθ (a + b) := by
  apply Subtype.ext
  show uMat a * uMat b = uMat (a + b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, add_mul, Complex.exp_add]
  all_goals ring
theorem phase_inv (a : ℝ) : (uθ a)⁻¹ = uθ (-a) := by
  apply mul_left_cancel (a := uθ a)
  rw [mul_inv_cancel, phase_mul, add_neg_cancel, phase_zero]
def phase (f : Bond L → ℝ) : Cfg L := fun b => uθ (f b)
def circulation (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) : ℝ :=
  f (p.1, p.2.1.1) + f (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) -
    f (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) - f (p.1, p.2.1.2)
theorem holonomy_phase (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    holonomyElem (phase f) p = uθ (circulation f p) := by
  simp [holonomyElem, periodicPlaquetteHolonomy, phase, phase_inv, phase_mul, circulation,
    sub_eq_add_neg]
def hermDiag (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(r : ℂ), 0; 0, -(r : ℂ)]
theorem hermDiag_zero : hermDiag 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag]
theorem im_phase (f : Bond L → ℝ) (p : PeriodicLatticePlaquette L) :
    imHolonomy (phase f) p = hermDiag (Real.sin (circulation f p)) := by
  rw [imHolonomy, holonomyElemInv, holonomy_phase, phase_inv]
  change (1 / (2 * Complex.I) : ℂ) • (uMat (circulation f p) - uMat (-circulation f p)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermDiag, uMat, Matrix.smul_apply, ← neg_mul, Complex.exp_mul_I]
  all_goals ring_nf; simp [Complex.I_sq]
theorem hermDiag_trace (r : ℝ) : Matrix.trace (hermDiag r) = 0 := by
  simp [hermDiag, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
theorem hermDiag_neg (r : ℝ) : -hermDiag r = hermDiag (-r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag]
theorem hermDiag_sub (r s : ℝ) : hermDiag r - hermDiag s = hermDiag (r - s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag, sub_eq_add_neg, add_comm]
theorem conj_phase_hermDiag (t r : ℝ) : conjByAmbient (uθ t)⁻¹ (hermDiag r) = hermDiag r := by
  rw [phase_inv]
  simp only [conjByAmbient_apply]
  change uMat (-t) * hermDiag r * (uMat (-t))ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, hermDiag, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, ← Complex.exp_conj, Complex.exp_neg]
  all_goals field_simp
def oriented (P : Set (PeriodicLatticePlaquette L)) (g : PeriodicLatticePlaquette L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) : ℝ := by
  classical
  exact if h : ν < μ then (if (x, ⟨(ν, μ), h⟩) ∈ P then g (x, ⟨(ν, μ), h⟩) else 0)
    else if h' : μ < ν then (if (x, ⟨(μ, ν), h'⟩) ∈ P then -g (x, ⟨(μ, ν), h'⟩) else 0)
    else 0
def scalarDiv (g : Fin 3 → Fin 3 → PeriodicLatticeSite L → ℝ) (b : Bond L) : ℝ :=
  ∑ ν : Fin 3, if ν = b.2 then 0 else g ν b.2 (periodicLatticeShiftBack b.1 ν) - g ν b.2 b.1
def sourceScalar (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) : ℝ :=
  scalarDiv (oriented P (fun p => Real.sin (circulation f p))) b
def linearSourceScalar (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) : ℝ :=
  scalarDiv (oriented P (circulation f)) b
theorem FnuMuLoc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) :
    FnuMuLoc P (phase f) ν μ x = hermDiag (oriented P (fun p => Real.sin (circulation f p)) ν μ x) := by
  classical
  have hh (p : PeriodicLatticePlaquette L) : piProj (imHolonomy (phase f) p) =
      hermDiag (Real.sin (circulation f p)) := by
    rw [im_phase, piProj_eq_self_of_trace_zero (hermDiag_trace _)]
  unfold FnuMuLoc oriented
  split_ifs <;> simp only [hh, hermDiag_neg, hermDiag_zero]
theorem DstarDir_phase (f : Bond L → ℝ) (ν : Fin 3) (g : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) :
    DstarDir (phase f) ν (fun y => hermDiag (g y)) x =
      hermDiag (g (periodicLatticeShiftBack x ν) - g x) := by
  unfold DstarDir phase
  rw [conj_phase_hermDiag, hermDiag_sub]
theorem hermDiag_sum {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    hermDiag (∑ i, g i) = ∑ i, hermDiag (g i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermDiag, Matrix.sum_apply]
theorem JfieldLoc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (b : Bond L) : JfieldLoc P (phase f) b.1 b.2 = hermDiag (sourceScalar P f b) := by
  unfold JfieldLoc sourceScalar scalarDiv
  simp_rw [FnuMuLoc_phase, DstarDir_phase]
  rw [hermDiag_sum]
  apply Finset.sum_congr rfl
  intro ν _
  split_ifs <;> simp [hermDiag_zero]
theorem JSU2Loc_phase (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) :
    -(JSU2Loc 1 P (phase f) b) = sourceScalar P f b • pauliE3 := by
  apply Subtype.ext
  change -(((-Complex.I) * (((1 : ℝ)⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc P (phase f) b.1 b.2) = _
  rw [JfieldLoc_phase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermDiag, pauliE3, suTwoWitness, suTwoWitnessVal, mul_comm]
theorem circulation_smul (f : Bond L → ℝ) (t : ℝ) (p : PeriodicLatticePlaquette L) :
    circulation (fun b => t * f b) p = t * circulation f p := by
  unfold circulation
  ring
theorem oriented_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ)
    (ν μ : Fin 3) (x : PeriodicLatticeSite L) :
    HasDerivAt (fun t : ℝ => oriented P (fun p => Real.sin (circulation (fun b => t * f b) p)) ν μ x)
      (oriented P (circulation f) ν μ x) 0 := by
  classical
  have hs (p : PeriodicLatticePlaquette L) :
      HasDerivAt (fun t : ℝ => Real.sin (circulation (fun b => t * f b) p)) (circulation f p) 0 := by
    simp_rw [circulation_smul]
    convert (((hasDerivAt_id (0 : ℝ)).mul_const (circulation f p)).sin) using 1 <;> simp
  unfold oriented
  split_ifs
  · exact hs _
  · exact hasDerivAt_const _ _
  · exact (hs _).neg
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
theorem sourceScalar_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (b : Bond L) :
    HasDerivAt (fun t : ℝ => sourceScalar P (fun b => t * f b) b) (linearSourceScalar P f b) 0 := by
  classical
  unfold sourceScalar linearSourceScalar scalarDiv
  apply HasDerivAt.fun_sum
  intro ν _
  by_cases h : ν = b.2
  · simp only [h, if_true]
    exact hasDerivAt_const _ _
  · simp only [h, if_false]
    exact (oriented_hasDerivAt P f ν b.2 _).sub (oriented_hasDerivAt P f ν b.2 _)
def sourceLinear (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : BondFnL2 L :=
  WithLp.toLp 2 (fun b => linearSourceScalar P f b • pauliE3)
theorem sourceField_hasDerivAt (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => t * f b)) b)) : BondFnL2 L))
      (sourceLinear P f) 0 := by
  simp_rw [JSU2Loc_phase]
  have hp : HasDerivAt (fun t : ℝ => fun b : Bond L => sourceScalar P (fun b => t * f b) b • pauliE3)
      (fun b : Bond L => linearSourceScalar P f b • pauliE3) 0 :=
    hasDerivAt_pi.mpr (fun b => (sourceScalar_hasDerivAt P f b).smul_const pauliE3)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Bond L => SuTwo)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hp
theorem sourceField_zero (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => (0 : ℝ) * f b)) b)) : BondFnL2 L) = 0 := by
  have hu : phase (fun b => (0 : ℝ) * f b) = (fun _ => 1) := by
    funext b
    simp only [phase, zero_mul, phase_zero]
  rw [hu]
  apply PiLp.ext
  intro b
  exact neg_eq_zero.mpr (JSU2Loc_trivial 1 P b)
theorem tendsto_div_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (h0 : f 0 = 0) (hd : HasDerivAt f v 0) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ • f t) (nhdsWithin 0 {0}ᶜ) (nhds v) := by
  have ht := hd.tendsto_slope_zero
  simpa only [zero_add, h0, sub_zero] using ht
theorem sourceField_tendsto (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ •
      (WithLp.toLp 2 (fun b => -(JSU2Loc 1 P (phase (fun b => t * f b)) b)) : BondFnL2 L))
      (nhdsWithin 0 {0}ᶜ) (nhds (sourceLinear P f)) :=
  tendsto_div_of_hasDerivAt_zero _ _ (sourceField_zero P f) (sourceField_hasDerivAt P f)
end AdalyFormal.Round10.Dictionary.PhaseSource

                                                                                  
                                                                                
                                                                                     
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.KKT
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

                                                              
def N (D : BaseDataS E S F) : F →L[ℝ] F := (D.Q.comp D.G).comp D.Qs
end AdalyFormal.Round10.Dictionary.KKT

                                                                                
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Source
open scoped RealInnerProductSpace Topology
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal (uθ)

                                                                           
theorem flatH_U1 (q R : ℕ) (α : ℝ) (z : FSp (geomOf 2 1 (dilTower q R))) :
    (flatData q R).H (adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) z) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).H z) := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  exact h.H z
def neutralCoord (X : SuTwo) : ℝ := ⟪pauliE3, X⟫
theorem half_fixed_offdiag (X : SuTwo) (h : RMap (uθ (Real.pi / 2)) X = X) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
  have hentry : ((RMap (uθ (Real.pi / 2)) X : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
      -(X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
    rw [RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, mul_assoc]
    ring_nf
    simp [Complex.I_sq]
  rw [h] at hentry
  linear_combination (1 / 2 : ℂ) * hentry
theorem neutral_of_half_fixed (X : SuTwo) (h : RMap (uθ (Real.pi / 2)) X = X) :
    X = neutralCoord X • pauliE3 := by
  have hd := suTwo_decompose X
  rw [half_fixed_offdiag X h] at hd
  simp only [Complex.zero_im, Complex.zero_re, zero_smul, zero_add] at hd
  have hc : neutralCoord X = ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im := by
    unfold neutralCoord
    conv_lhs => rw [hd]
    rw [inner_smul_right]
    change _ * hsInner pauliE3 pauliE3 = _
    rw [hsInner_e3_e3, mul_one]
  rw [hc]
  exact hd
abbrev vacJet (q R : ℕ) (v : TwistSpace q R) : FSp (geomOf 2 1 (dilTower q R)) :=
  C2fullOf (geomOf 2 1 (dilTower q R)) (fun _ => 1)
    (Wop (geomOf 2 1 (dilTower q R)) (fun _ => 1) 1 (iE (geomOf 2 1 (dilTower q R)) v))
def interiorProfile (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ := by
  classical
  exact if b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then 0 else f b
theorem bulkU_phase (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    bulkU q R f ε = PhaseSource.phase (fun b => ε * interiorProfile q R f b) := by
  classical
  funext b
  unfold bulkU AdalyFormal.Round5.Guarded.IVTR2.maskedU PhaseSource.phase interiorProfile
  by_cases hb : b ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [hb, if_true, mul_zero, PhaseSource.phase_zero]
  · simp only [hb, if_false, Ug_eq_uθ]
def profileSourceStencil (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : TwistSpace q R :=
  pE (geomOf 2 1 (dilTower q R))
    (PhaseSource.sourceLinear (plaqIn ((dilTower q R).Om 0)) (interiorProfile q R f))
theorem bulkSource_tendsto (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (dataS selIn selIn (bulkP q R f ε)).J)
      (𝓝[≠] 0) (𝓝 (profileSourceStencil q R f)) := by
  show Tendsto (fun ε : ℝ => ε⁻¹ • pE (geomOf 2 1 (dilTower q R))
    (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
      (plaqIn ((dilTower q R).Om 0)) (bulkU q R f ε) b)))) (𝓝[≠] 0)
    (𝓝 (profileSourceStencil q R f))
  simp only [bulkU_phase, ← map_smul]
  exact ((pE (geomOf 2 1 (dilTower q R))).continuous.tendsto _).comp
    (PhaseSource.sourceField_tendsto (plaqIn ((dilTower q R).Om 0)) (interiorProfile q R f))
theorem bulkSource_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    (dataS selIn selIn (bulkP q R f 0)).J = 0 := by
  have hu : bulkU q R f 0 = (fun _ => 1) := by
    rw [bulkU_phase]
    funext b
    exact (by simp only [PhaseSource.phase, zero_mul, PhaseSource.phase_zero])
  change pE (geomOf 2 1 (dilTower q R)) (WithLp.toLp 2 (fun b =>
    -(AdalyFormal.IngredientFamily.JSU2Loc 1 (plaqIn ((dilTower q R).Om 0)) (bulkU q R f 0) b))) = 0
  rw [hu]
  have hz : (WithLp.toLp 2 (fun b => -(AdalyFormal.IngredientFamily.JSU2Loc 1
      (plaqIn ((dilTower q R).Om 0)) (fun _ => 1) b)) : BondFnL2 (scaleUp 2 1 (dilLu q R))) = 0 := by
    apply PiLp.ext
    intro b
    exact neg_eq_zero.mpr (AdalyFormal.IngredientFamily.JSU2Loc_trivial 1 _ b)
  rw [hz, map_zero]
end AdalyFormal.Round10.Dictionary.Source

namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AdalyFormal.Round10.Dictionary


namespace AdalyFormal.Round10.Dictionary.Actual
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)

open Classical
end AdalyFormal.Round10.Dictionary.Actual


   
                                                                       
                                                                                  
                                                                             
  
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing

open Finset

                                 
def left (a : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else a (j - 1)
end AdalyFormal.Round10.Nonvanishing


open Filter
open scoped Topology

namespace AdalyFormal.Round10.Assembly

                                                                             
                                                                 
end AdalyFormal.Round10.Assembly


   
                                                                               
                                                                            
                                                                          
  
set_option autoImplicit false

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

                                                                
end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

                                                    
end AdalyFormal.Round10.Nonvanishing.FreeProfile

namespace AdalyFormal.Round10.Nonvanishing.FreeProfile

open Finset

end AdalyFormal.Round10.Nonvanishing.FreeProfile

                                                                                
namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                                
                                                                         
def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})
end AdalyFormal.Round10.Assembly.R2

                                                                              
                                                                   
                                        
namespace AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round9.Guarded.QualitativeR2Joint

end AdalyFormal.Round10.Assembly.R2

noncomputable section
namespace AdalyFormal.Round10.Dictionary.SourceEnergy
open scoped BigOperators RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.PhaseSource
variable {L : PeriodicLatticeExtent}
attribute [local instance] Classical.propDecidable

theorem sum_backward (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * g (periodicLatticeShiftBack x ν)) =
      ∑ x, f (periodicLatticeShift x ν) * g x := by
  have h := Equiv.sum_comp (periodicLatticeShiftEquiv (L := L) ν)
    (fun x => f x * g (periodicLatticeShiftBack x ν))
  simpa only [periodicLatticeShiftEquiv_apply, periodicLatticeShiftBack_shift] using h.symm
theorem sum_backward_diff (f g : PeriodicLatticeSite L → ℝ) (ν : Fin 3) :
    (∑ x, f x * (g (periodicLatticeShiftBack x ν) - g x)) =
      ∑ x, (f (periodicLatticeShift x ν) - f x) * g x := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, sum_backward]
theorem sum_dirs (f : PeriodicPlaquetteDirections → ℝ) :
    ∑ d, f d = f ⟨(0,1), by decide⟩ + f ⟨(0,2), by decide⟩ + f ⟨(1,2), by decide⟩ := by
  have hu : (Finset.univ : Finset PeriodicPlaquetteDirections) =
      {⟨(0,1), by decide⟩, ⟨(0,2), by decide⟩, ⟨(1,2), by decide⟩} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring
theorem oriented_diag (P : Set (PeriodicLatticePlaquette L))
    (g : PeriodicLatticePlaquette L → ℝ) (ν : Fin 3) (x : PeriodicLatticeSite L) :
    oriented P g ν ν x = 0 := by
  simp [oriented]
theorem div_sum (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) :
    (∑ b : Bond L, f b * scalarDiv (oriented P g) b) =
      ∑ x : PeriodicLatticeSite L, ∑ μ : Fin 3, ∑ ν : Fin 3,
        (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [scalarDiv, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  by_cases h : ν = μ
  · subst ν
    simp only [ite_true, mul_zero, oriented_diag, Finset.sum_const_zero]
  · simp only [if_neg h]
    exact sum_backward_diff (fun x => f (x, μ)) (oriented P g ν μ) ν
theorem oriented_curl_point (P : Set (PeriodicLatticePlaquette L))
    (f : Bond L → ℝ) (g : PeriodicLatticePlaquette L → ℝ) (x : PeriodicLatticeSite L) :
    (∑ μ : Fin 3, ∑ ν : Fin 3,
      (f (periodicLatticeShift x ν, μ) - f (x, μ)) * oriented P g ν μ x) =
    ∑ d : PeriodicPlaquetteDirections, if (x,d) ∈ P then circulation f (x,d) * g (x,d) else 0 := by
  classical
  have h01 : oriented P g 0 1 x = if (x, ⟨(0,1), by decide⟩) ∈ P then g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h02 : oriented P g 0 2 x = if (x, ⟨(0,2), by decide⟩) ∈ P then g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h12 : oriented P g 1 2 x = if (x, ⟨(1,2), by decide⟩) ∈ P then g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  have h10 : oriented P g 1 0 x = if (x, ⟨(0,1), by decide⟩) ∈ P then -g (x, ⟨(0,1), by decide⟩) else 0 := by simp [oriented]
  have h20 : oriented P g 2 0 x = if (x, ⟨(0,2), by decide⟩) ∈ P then -g (x, ⟨(0,2), by decide⟩) else 0 := by simp [oriented]
  have h21 : oriented P g 2 1 x = if (x, ⟨(1,2), by decide⟩) ∈ P then -g (x, ⟨(1,2), by decide⟩) else 0 := by simp [oriented]
  rw [sum_dirs]
  simp only [Fin.sum_univ_three, oriented_diag, h01, h02, h12, h10, h20, h21, circulation]
  split_ifs <;> ring
theorem source_sbp (P : Set (PeriodicLatticePlaquette L)) (f g : Bond L → ℝ) :
    (∑ b : Bond L, f b * linearSourceScalar P g b) =
      ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p * circulation g p else 0 := by
  classical
  change (∑ b : Bond L, f b * scalarDiv (oriented P (circulation g)) b) = _
  rw [div_sum, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => oriented_curl_point P f (circulation g) x)
def curlEnergy (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) : ℝ :=
  ∑ p : PeriodicLatticePlaquette L, if p ∈ P then circulation f p ^ 2 else 0
theorem curlEnergy_nonneg (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 ≤ curlEnergy P f := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs <;> positivity
theorem curlEnergy_eq_zero_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    curlEnergy P f = 0 ↔ ∀ p ∈ P, circulation f p = 0 := by
  classical
  unfold curlEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by split_ifs <;> positivity)]
  constructor
  · intro h p hp
    have hz := h p (Finset.mem_univ p)
    simpa only [if_pos hp, sq_eq_zero_iff] using hz
  · intro h p _
    by_cases hp : p ∈ P
    · simp only [if_pos hp, h p hp, zero_pow (by decide : 2 ≠ 0)]
    · simp only [if_neg hp]
theorem curlEnergy_pos_iff (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) :
    0 < curlEnergy P f ↔ ∃ p ∈ P, circulation f p ≠ 0 := by
  have h : 0 < curlEnergy P f ↔ curlEnergy P f ≠ 0 :=
    lt_iff_le_and_ne.trans (and_iff_right (curlEnergy_nonneg P f)) |>.trans ne_comm
  rw [h, ne_eq, curlEnergy_eq_zero_iff]
  simp only [not_forall, exists_prop]
def neutralCoordinate (w : BondFnL2 L) (b : Bond L) : ℝ := ⟪pauliE3, w b⟫
theorem inner_sourceLinear (P : Set (PeriodicLatticePlaquette L))
    (w : BondFnL2 L) (f : Bond L → ℝ) :
    ⟪w, sourceLinear P f⟫ = ∑ p : PeriodicLatticePlaquette L,
      if p ∈ P then circulation (neutralCoordinate w) p * circulation f p else 0 := by
  rw [PiLp.inner_apply]
  have h (b : Bond L) : ⟪w b, sourceLinear P f b⟫ =
      neutralCoordinate w b * linearSourceScalar P f b := by
    change ⟪w b, linearSourceScalar P f b • pauliE3⟫ = _
    rw [inner_smul_right, real_inner_comm]
    exact mul_comm _ _
  simp_rw [h]
  exact source_sbp P (neutralCoordinate w) f
end AdalyFormal.Round10.Dictionary.SourceEnergy

                                                                                                      
noncomputable section
namespace AdalyFormal.Round10.Dictionary.FreeSource
open scoped BigOperators RealInnerProductSpace Topology Matrix
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Dictionary.PhaseSource
attribute [local instance] Classical.propDecidable

variable {L : PeriodicLatticeExtent}

theorem circulation_congr_boundary (f g : Bond L → ℝ) (p : PeriodicLatticePlaquette L)
    (h : ∀ b ∈ periodicPlaquetteBoundaryEdges p, f b = g b) :
    circulation f p = circulation g p := by
  unfold circulation
  rw [h (p.1,p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges]),
    h (periodicLatticeShift p.1 p.2.1.1,p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges]),
    h (periodicLatticeShift p.1 p.2.1.2,p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges]),
    h (p.1,p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])]
theorem circulation_interiorProfile (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : p ∈ plaqIn ((dilTower q R).Om 0)) :
    circulation (interiorProfile q R f) p = circulation f p := by
  apply circulation_congr_boundary
  intro b hb
  have hbp := hp b hb
  have hz : b ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) := by
    intro h
    exact h.1 hbp.1
  simp only [interiorProfile, if_neg hz]
def responseProfile (q R : ℕ) (u : TwistSpace q R)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ :=
  neutralCoordinate (iE (geomOf 2 1 (dilTower q R))
    ((flatData q R).H (vacJet q R u))) b
def profileCoupling (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (u : TwistSpace q R) : ℝ := vacCoupling q R (profileSourceStencil q R f) u
theorem profileCoupling_curl (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = 2 *
      ∑ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        if p ∈ plaqIn ((dilTower q R).Om 0) then
          circulation (responseProfile q R u) p * circulation f p else 0 := by
  unfold profileCoupling vacCoupling profileSourceStencil
  rw [pE_inner_right, inner_sourceLinear]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ plaqIn ((dilTower q R).Om 0)
  · rw [if_pos hp, if_pos hp, circulation_interiorProfile q R f p hp]
    rfl
  · simp only [if_neg hp]
theorem adaptive_energy (q R : ℕ) (u : TwistSpace q R) :
    profileCoupling q R (responseProfile q R u) u =
      2 * curlEnergy (plaqIn ((dilTower q R).Om 0)) (responseProfile q R u) := by
  rw [profileCoupling_curl]
  simp only [curlEnergy, pow_two]
def CurlDetected (q R : ℕ) (u : TwistSpace q R) : Prop :=
  ∃ p ∈ plaqIn ((dilTower q R).Om 0), circulation (responseProfile q R u) p ≠ 0
theorem adaptive_pos_iff (q R : ℕ) (u : TwistSpace q R) :
    0 < profileCoupling q R (responseProfile q R u) u ↔ CurlDetected q R u := by
  rw [adaptive_energy, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2), curlEnergy_pos_iff]
  rfl
theorem exists_profile_iff_curlDetected (q R : ℕ) (u : TwistSpace q R) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, profileCoupling q R f u ≠ 0) ↔
      CurlDetected q R u := by
  constructor
  · rintro ⟨f, hf⟩
    by_contra hn
    have hz : ∀ p ∈ plaqIn ((dilTower q R).Om 0), circulation (responseProfile q R u) p = 0 := by
      simpa only [CurlDetected, not_exists, not_and, not_not] using hn
    apply hf
    rw [profileCoupling_curl]
    have hs : (∑ p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)),
        if p ∈ plaqIn ((dilTower q R).Om 0) then
          circulation (responseProfile q R u) p * circulation f p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      split_ifs with hp
      · rw [hz p hp, zero_mul]
      · rfl
    rw [hs, mul_zero]
  · intro h
    exact ⟨responseProfile q R u, ne_of_gt ((adaptive_pos_iff q R u).mpr h)⟩
end AdalyFormal.Round10.Dictionary.FreeSource

                                                                               
                                                      
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner

                                                                                       
def responseField (q R : ℕ) (u : TwistSpace q R) : TwistSpace q R :=
  (flatData q R).H (vacJet q R u)
def responseProfile (q R : ℕ) (u : TwistSpace q R)
    (b : Bond (scaleUp 2 1 (dilLu q R))) : ℝ :=
  neutralCoord ((responseField q R u : BondFnL2 _) b)
end AdalyFormal.Round10.Assembly.R3

                                                                          
                                                                                    
                                                                                              
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace Topology
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource (profileCoupling CurlDetected)
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                                            
abbrev profileData (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    BaseDataS (TwistSpace q R) (SiteL2 (scaleUp 2 1 (dilLu q R)))
      (FSp (geomOf 2 1 (dilTower q R))) := dataS selIn selIn (bulkP q R f ε)
def ProfileRegular (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ContinuousAt (fun ε : ℝ => (profileData q R f ε).H) 0 ∧
  (∀ u : TwistSpace q R, Tendsto (fun ε : ℝ => (profileData q R f ε).C2 u)
    (𝓝 0) (𝓝 ((profileData q R f 0).C2 u))) ∧
  HasDerivAt (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f) 0
def RegularityFacts : Prop :=
  ∀ q R : ℕ, 0 < q → 2 ∣ R → 18 ≤ R →
    ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f
theorem bulkD_zero_source (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    bulkD q R f 0 = 0 := by
  have hs := (profileData q R f 0).Delta2_spec (dataS_laws selIn selIn _)
  apply symm_unique hs.1
    (S2 := (0 : TwistSpace q R →L[ℝ] TwistSpace q R))
    (fun x y => by simp only [zero_apply, inner_zero_left, inner_zero_right])
  intro u
  rw [hs.2 u, bulkSource_zero]
  change 2 * ⟪(profileData q R f 0).H ((profileData q R f 0).C2 u),
    (0 : TwistSpace q R)⟫ = ⟪u, (0 : TwistSpace q R)⟫
  rw [inner_zero_right, inner_zero_right, mul_zero]
theorem bulkData_zero (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    dataS selIn selIn (bulkP q R f 0) = flatData q R := by
  have hu : bulkU q R f 0 = (fun _ => 1) := by
    rw [bulkU_phase]
    funext b
    simp only [Dictionary.PhaseSource.phase, zero_mul, Dictionary.PhaseSource.phase_zero]
  unfold bulkP
  rw [hu]
theorem corrDeriv_profile_form (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (hr : ProfileRegular q R f)
    (u : TwistSpace q R) :
    ⟪u, corrDeriv q R f u⟫ = profileCoupling q R f u := by
  have ht := Dictionary.PhaseSource.tendsto_div_of_hasDerivAt_zero
    (fun ε : ℝ => bulkD q R f ε) (corrDeriv q R f)
    (bulkD_zero_source q R f) hr.2.2
  have h := limit_Delta2_div_form
    (profileData q R f) (fun _ => dataS_laws selIn selIn _) 
    hr.1 hr.2.1 (profileSourceStencil q R f) (bulkSource_tendsto q R f)
    (corrDeriv q R f)
    (ht.mono_left (nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => ne_of_gt hx))) u
  change ⟪u, corrDeriv q R f u⟫ =
    2 * ⟪(dataS selIn selIn (bulkP q R f 0)).H
      ((dataS selIn selIn (bulkP q R f 0)).C2 u), profileSourceStencil q R f⟫ at h
  rw [bulkData_zero] at h
  exact h
def CofinalAnyPathCurlLine : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      ∃ u : TwistSpace (2^j) R, KernelLine (2^j) R V u ∧ CurlDetected (2^j) R u
end AdalyFormal.Round10.Assembly.R3


                                                            
                                                                                   
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace AdalyFormal.Round10.Nonvanishing.Flux

open Finset

variable {T : Type*} [Fintype T]

                                                    
section Tiling
variable {C O : Type*} [Fintype C] [Fintype O]

                                                                                
                                                                
end Tiling

end AdalyFormal.Round10.Nonvanishing.Flux

namespace AdalyFormal.Round10.Nonvanishing.TorusFlux

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Round10.Nonvanishing.Flux

variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round10.Nonvanishing.TorusFlux

namespace AdalyFormal.Round10.Nonvanishing.Coordinate
open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
variable {L : PeriodicLatticeExtent}
section Cube
variable {E : Type*} [AddCommGroup E]
def cube (g : ℕ → ℕ → ℕ → E) (n a b c : ℕ) : E :=
  ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, g (a + i) (b + j) (c + k)
end Cube

def mkS (L : PeriodicLatticeExtent) (a b c : ℕ) : PeriodicLatticeSite L :=
  fun μ => ⟨(![a, b, c] μ) % (L μ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
theorem mkS_val (a b c : ℕ) (μ : Fin 3) : ((mkS L a b c) μ).val = (![a, b, c] μ) % (L μ + 1) := rfl
theorem mkS_val0 (a b c : ℕ) : ((mkS L a b c) 0).val = a % (L 0 + 1) := rfl
theorem mkS_val1 (a b c : ℕ) : ((mkS L a b c) 1).val = b % (L 1 + 1) := rfl
theorem mkS_val2 (a b c : ℕ) : ((mkS L a b c) 2).val = c % (L 2 + 1) := rfl
theorem mkS_eta (x : PeriodicLatticeSite L) : mkS L (x 0).val (x 1).val (x 2).val = x := by
  funext μ
  apply Fin.ext
  rw [mkS_val]
  fin_cases μ
  · simp [Nat.mod_eq_of_lt (x 0).isLt]
  · simp [Nat.mod_eq_of_lt (x 1).isLt]
  · simp [Nat.mod_eq_of_lt (x 2).isLt]
theorem shift_val_self (x : PeriodicLatticeSite L) (μ : Fin 3) :
    ((periodicLatticeShift x μ) μ).val = ((x μ).val + 1) % (L μ + 1) := by
  simp [periodicLatticeShift, Fin.val_add]
theorem shift_val_ne (x : PeriodicLatticeSite L) (μ ν : Fin 3) (h : ν ≠ μ) :
    ((periodicLatticeShift x μ) ν) = x ν := by
  simp [periodicLatticeShift, Function.update_of_ne h]
theorem shift_mkS1 (a b c : ℕ) : periodicLatticeShift (mkS L a b c) 1 = mkS L a (b + 1) c := by
  funext ν
  apply Fin.ext
  by_cases h : ν = 1
  · subst h
    rw [shift_val_self, mkS_val1, mkS_val1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  · rw [shift_val_ne _ _ _ h, mkS_val, mkS_val]
    fin_cases ν <;> simp_all
theorem mkS_mem_block (Y : PeriodicLatticeSite L) (n : ℕ) (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1)
    (i j k : ℕ) (hi : i < n) (hj : j < n) (hk : k < n) :
    mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k) ∈ blockOf Y n := by
  rw [mem_blockOf]
  intro μ
  have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
  fin_cases μ
  · simp only [Fin.zero_eta, mkS_val0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.mk_one, mkS_val1]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · simp only [Fin.reduceFinMk, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
theorem sum_block_eq_cube {E : Type*} [AddCommGroup E] [Module ℝ E] (Y : PeriodicLatticeSite L) (n : ℕ)
    (hfit : ∀ μ, (Y μ).val + n ≤ L μ + 1) (F : PeriodicLatticeSite L → E) :
    ∑ x ∈ blockOf Y n, F x = cube (fun a b c => F (mkS L a b c)) n (Y 0).val (Y 1).val (Y 2).val := by
  classical
  unfold cube
  have e : ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, F (mkS L ((Y 0).val + i) ((Y 1).val + j) ((Y 2).val + k))
      = ∑ p ∈ range n ×ˢ (range n ×ˢ range n), F (mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2)) := by
    simp only [Finset.sum_product]
  rw [e]
  symm
  refine Finset.sum_nbij' (fun p => mkS L ((Y 0).val + p.1) ((Y 1).val + p.2.1) ((Y 2).val + p.2.2))
    (fun x => ((x 0).val - (Y 0).val, (x 1).val - (Y 1).val, (x 2).val - (Y 2).val)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    exact mkS_mem_block Y n hfit _ _ _ hp.1 hp.2.1 hp.2.2
  · intro x hx
    rw [mem_blockOf] at hx
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have := hx 0; omega
    · have := hx 1; omega
    · have := hx 2; omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have h0 := hfit 0; have h1 := hfit 1; have h2 := hfit 2
    simp only [mkS_val0, mkS_val1, mkS_val2]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp
  · intro x hx
    rw [mem_blockOf] at hx
    have a0 := hx 0; have a1 := hx 1; have a2 := hx 2
    have e0 : (Y 0).val + ((x 0).val - (Y 0).val) = (x 0).val := by omega
    have e1 : (Y 1).val + ((x 1).val - (Y 1).val) = (x 1).val := by omega
    have e2 : (Y 2).val + ((x 2).val - (Y 2).val) = (x 2).val := by omega
    simp only [e0, e1, e2]
    exact mkS_eta x
  · intro p hp
    rfl
end AdalyFormal.Round10.Nonvanishing.Coordinate

namespace AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.QOne (qOnePathSum longBondValue_ell2)
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0 mkS_val1 mkS_val2 sum_block_eq_cube cube shift_mkS1)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux

variable {L : PeriodicLatticeExtent} {ny nz : ℕ}

                                                             
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)

                                                                                 
end AdalyFormal.Round10.Nonvanishing.PhysicalBlocking
namespace AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane




end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round10.Nonvanishing.DilatedFlux

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (curlValue)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Round10.Nonvanishing.Flux
open AdalyFormal.Round10.Nonvanishing.TorusFlux
open AdalyFormal.Round10.Nonvanishing.Coordinate (mkS mkS_val0)
open AdalyFormal.Round10.Nonvanishing.PhysicalBlocking

abbrev L (q R : ℕ) := scaleUp 2 1 (dilLu q R)
abbrev G (q R : ℕ) := geomOf 2 1 (dilTower q R)
def blockCount (q R : ℕ) : ℕ := 4*q*(R+1)
open scoped RealInnerProductSpace
open AdalyFormal.Balaban.SuTwoInner (pauliE3)

end AdalyFormal.Round10.Nonvanishing.DilatedFlux

                                                                                 
                                                                   
noncomputable section
namespace AdalyFormal.Round10.Dictionary.JetDetection
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Nonvanishing.DilatedFlux

                                                                                 
end AdalyFormal.Round10.Dictionary.JetDetection

                                                                                
                                                                        
noncomputable section
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative (uthPath vacA)
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round10.Dictionary.JetDetection
open AdalyFormal.Round10.Nonvanishing.DilatedFlux (blockCount)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                              
end AdalyFormal.Round10.Assembly.R3

                                                                     
                                                                              
                                                                              
                                                         
namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

                                                                                  
theorem regularityFacts : RegularityFacts := by
  intro q R hq hR hR18 f
  exact ⟨bulk_H_cont hq (by omega) (dil_admissible hq hR) f,
    bulk_C2_tendsto hq (dil_admissible hq hR) f,
    hasDerivAt_corrDeriv hq hR (by omega) f⟩
end AdalyFormal.Round10.Assembly.R3

                                                                                       
                                                            
namespace AdalyFormal.Round10.Assembly.R3
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR2

end AdalyFormal.Round10.Assembly.R3


                                                                                
                                                                                 
noncomputable section
open scoped RealInnerProductSpace Topology
open Set
namespace AdalyFormal.Round10.Assembly.R4

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                           
                                                                 
def responseHull (K : Submodule ℝ E) (Q : E → F) : Set F :=
  closedConvexHull ℝ (Q '' {u | u ∈ K ∧ ‖u‖ = 1})
theorem separator_of_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (h : (0 : F) ∉ responseHull K Q) :
    ∃ (f : F →L[ℝ] ℝ) (c : ℝ), 0 < c ∧
      ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u) := by
  obtain ⟨f, c, hc, hf⟩ := geometric_hahn_banach_point_closed
    (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull h
  refine ⟨f, c, by simpa using hc, ?_⟩
  intro u hu hn
  exact le_of_lt (hf _ (subset_closedConvexHull (𝕜 := ℝ) ⟨u, ⟨hu, hn⟩, rfl⟩))
theorem notMem_responseHull_of_separator (K : Submodule ℝ E) (Q : E → F)
    (f : F →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u)) :
    (0 : F) ∉ responseHull K Q := by
  have hsub : responseHull K Q ⊆ {x : F | c ≤ f x} := by
    apply closedConvexHull_min
    · rintro _ ⟨u, ⟨hu, hn⟩, rfl⟩
      exact hf u hu hn
    · exact (convex_Ici c).linear_preimage f.toLinearMap
    · exact isClosed_le continuous_const f.continuous
  intro h
  have := hsub h
  simp only [mem_setOf_eq, map_zero] at this
  linarith
theorem norm_square_lower_of_unit_lower (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u)
    (f : F →L[ℝ] ℝ) (c : ℝ)
    (hf : ∀ u, u ∈ K → ‖u‖ = 1 → c ≤ f (Q u)) :
    ∀ u, u ∈ K → c * ‖u‖ ^ 2 ≤ f (Q u) := by
  intro u hu
  by_cases hz : u = 0
  · subst u
    have hzero : Q 0 = 0 := by simpa using hQ 0 0
    simp [hzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hz
  let v : E := ‖u‖⁻¹ • u
  have hvK : v ∈ K := K.smul_mem _ hu
  have hvn : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h := mul_le_mul_of_nonneg_right (hf v hvK hvn) (sq_nonneg ‖u‖)
  calc
    c * ‖u‖ ^ 2 ≤ f (Q v) * ‖u‖ ^ 2 := h
    _ = f (Q (‖u‖ • v)) := by simp only [hQ, map_smul, smul_eq_mul]; ring
    _ = f (Q u) := by rw [huv]
theorem common_coercive_iff_notMem_responseHull (K : Submodule ℝ E) (Q : E → F)
    (hQ : ∀ (a : ℝ) u, Q (a • u) = (a ^ 2) • Q u) :
    (∃ (f : F →L[ℝ] ℝ) (c : ℝ), 0 < c ∧
      ∀ u, u ∈ K → c * ‖u‖ ^ 2 ≤ f (Q u)) ↔
    (0 : F) ∉ responseHull K Q := by
  constructor
  · rintro ⟨f, c, hc, hf⟩
    apply notMem_responseHull_of_separator K Q f c hc
    intro u hu hn
    simpa only [hn, one_pow, mul_one] using hf u hu
  · intro h
    obtain ⟨f, c, hc, hf⟩ := separator_of_notMem_responseHull K Q h
    exact ⟨f, c, hc, norm_square_lower_of_unit_lower K Q hQ f c hf⟩
end AdalyFormal.Round10.Assembly.R4

                                                                             
                                                                            
noncomputable section
namespace AdalyFormal.Round10.Assembly.R4
open scoped BigOperators RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.AnalyticR2 (flatData)
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Assembly.R3 (ProfileRegular RegularityFacts corrDeriv_profile_form)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

abbrev ProfileSpace (q R : ℕ) := EuclideanSpace ℝ (Bond (scaleUp 2 1 (dilLu q R)))
def responseGradient (q R : ℕ) (u : TwistSpace q R) : ProfileSpace q R :=
  WithLp.toLp 2 (fun b => 2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
    (Dictionary.FreeSource.responseProfile q R u) b)
theorem profileCoupling_gradient (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R f u = ⟪(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫ := by
  classical
  rw [profileCoupling_curl, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change 2 * (∑ p, if p ∈ plaqIn ((dilTower q R).Om 0) then
    circulation (Dictionary.FreeSource.responseProfile q R u) p * circulation f p else 0) =
    ∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b
  rw [show (∑ b, (2 * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b) * f b) =
    2 * ∑ b, f b * linearSourceScalar (plaqIn ((dilTower q R).Om 0))
      (Dictionary.FreeSource.responseProfile q R u) b by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring]
  rw [source_sbp]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring
theorem double_inner_smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a ^ 2 • x, y⟫ = a ^ 2 * (2 * ⟪x, y⟫) := by
  rw [real_inner_smul_left]
  ring
theorem profileCoupling_smul_input (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (a • u) = a ^ 2 * profileCoupling q R f u := by
  unfold profileCoupling AdalyFormal.Round9.Guarded.AnalyticR2.vacCoupling
  simp only [map_smul]
  rw [(C2fullOf_quad (geomOf 2 1 (dilTower q R)) (fun _ => 1)).smul_sq]
  simp only [map_smul]
  exact double_inner_smul (X := TwistSpace q R)
    ((flatData q R).H (vacJet q R u)) (profileSourceStencil q R f) a
theorem responseGradient_smul (q R : ℕ) (a : ℝ) (u : TwistSpace q R) :
    responseGradient q R (a • u) = a ^ 2 • responseGradient q R u := by
  apply ext_inner_left ℝ
  intro f
  rw [inner_smul_right, ← profileCoupling_gradient q R (fun b => f b),
    ← profileCoupling_gradient q R (fun b => f b), profileCoupling_smul_input]
def crossingKernel (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    Submodule ℝ (TwistSpace q R) := (vacA q R V 1 (vacEdge q R V)).ker
def NoResponseCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : Prop :=
  (0 : ProfileSpace q R) ∉ responseHull (crossingKernel q R V) (responseGradient q R)
theorem exists_positive_profile_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) :
    (∃ (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (c : ℝ), 0 < c ∧
      ∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
        c * ‖u‖ ^ 2 ≤ profileCoupling q R f u) ↔ NoResponseCancellation q R V := by
  rw [NoResponseCancellation, ← common_coercive_iff_notMem_responseHull
    (crossingKernel q R V) (responseGradient q R) (responseGradient_smul q R)]
  constructor
  · rintro ⟨f, c, hc, hf⟩
    refine ⟨InnerProductSpace.toDual ℝ (ProfileSpace q R) (WithLp.toLp 2 f), c, hc, ?_⟩
    intro u hu
    rw [InnerProductSpace.toDual_apply_apply, ← profileCoupling_gradient]
    exact hf u hu
  · rintro ⟨f, c, hc, hf⟩
    let r : ProfileSpace q R := (InnerProductSpace.toDual ℝ (ProfileSpace q R)).symm f
    refine ⟨fun b => r b, c, hc, ?_⟩
    intro u hu
    rw [profileCoupling_gradient]
    change c * ‖u‖ ^ 2 ≤ ⟪r, responseGradient q R u⟫
    rw [InnerProductSpace.toDual_symm_apply]
    exact hf u hu
theorem profileCoupling_neg_profile (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (u : TwistSpace q R) :
    profileCoupling q R (fun b => -f b) u = -profileCoupling q R f u := by
  rw [profileCoupling_gradient, profileCoupling_gradient]
  change ⟪-(WithLp.toLp 2 f : ProfileSpace q R), responseGradient q R u⟫ = _
  exact inner_neg_left _ _
theorem exists_canonicalCoupling_iff_noCancellation (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hr : ∀ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, ProfileRegular q R f) :
    (∃ f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ,
      CanonicalCoupling q R V (corrDeriv q R f)) ↔ NoResponseCancellation q R V := by
  rw [← exists_positive_profile_iff_noCancellation]
  constructor
  · rintro ⟨f, c, hc, hsign⟩
    rcases hsign with hp | hn
    · refine ⟨f, c, hc, fun u hu => ?_⟩
      rw [← corrDeriv_profile_form q R f (hr f) u]
      exact hp u hu
    · refine ⟨fun b => -f b, c, hc, fun u hu => ?_⟩
      rw [profileCoupling_neg_profile, ← corrDeriv_profile_form q R f (hr f) u]
      exact hn u hu
  · rintro ⟨f, c, hc, hf⟩
    refine ⟨f, c, hc, Or.inl (fun u hu => ?_)⟩
    rw [corrDeriv_profile_form q R f (hr f) u]
    exact hf u hu
end AdalyFormal.Round10.Assembly.R4

                                                                        
                                                                               
noncomputable section
namespace AdalyFormal.Round10.Assembly.R4
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Assembly.R3 (RegularityFacts)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                             
theorem responseGradient_ne_zero_iff (q R : ℕ) (u : TwistSpace q R) :
    responseGradient q R u ≠ 0 ↔ CurlDetected q R u := by
  rw [← exists_profile_iff_curlDetected]
  constructor
  · intro h
    refine ⟨fun b => responseGradient q R u b, ?_⟩
    rw [profileCoupling_gradient]
    exact ne_of_gt (real_inner_self_pos.mpr h)
  · rintro ⟨f, hf⟩ hz
    apply hf
    rw [profileCoupling_gradient, hz, inner_zero_right]
def CofinalAnyPathNoResponseCancellation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)),
      AdalyFormal.D1Literal.ContFam V ∧ AnFam V ∧ V 0 = (fun _ => 1) ∧
      (∃ w, ⟪w, vacA (2^j) R V 1 Real.pi w⟫ < 0) ∧
      NoResponseCancellation (2^j) R V
theorem cofinalAnyPathCoupling_iff_noCancellation (hr : RegularityFacts) :
    CofinalAnyPathCoupling ↔ CofinalAnyPathNoResponseCancellation := by
  constructor
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, hf⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R V
        (hr (2^j) R (by positivity) hR hR18)).mp hf⟩
  · intro h j₀
    obtain ⟨j, hj, hRs⟩ := h j₀
    refine ⟨j, hj, fun R₀ => ?_⟩
    obtain ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg, hnc⟩ := hRs R₀
    exact ⟨R, hRR, hR, hR18, V, hVc, hVa, hV0, hneg,
      (exists_canonicalCoupling_iff_noCancellation (2^j) R V
        (hr (2^j) R (by positivity) hR hR18)).mpr hnc⟩
end AdalyFormal.Round10.Assembly.R4

                                                                     
                                                                             
namespace AdalyFormal.Round10.Assembly.R4
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round9.Guarded.QualitativeR2Joint

theorem goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (h : CofinalAnyPathNoResponseCancellation) : GoalNeg2 :=
  goalNeg2_of_cofinalAnyPathCoupling
    ((cofinalAnyPathCoupling_iff_noCancellation R3.regularityFacts).mpr h)
end AdalyFormal.Round10.Assembly.R4

namespace AdalyFormal.Round10.Dictionary.FreeSource
open scoped BigOperators RealInnerProductSpace Topology Matrix
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Dictionary.PhaseSource
attribute [local instance] Classical.propDecidable

variable {L : PeriodicLatticeExtent}

theorem phase_axis_fixed (α : ℝ) : RMap (AdalyFormal.D1Literal.uθ α) pauliE3 = pauliE3 := by
  apply Subtype.ext
  rw [AdalyFormal.Balaban.CovariantOperators.RMap_coe_apply]
  change AdalyFormal.D1Literal.uMat α * _ * (AdalyFormal.D1Literal.uMat α)ᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, pauliE3,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitness,
      AdalyFormal.Balaban.CovariantOperators.suTwoWitnessVal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      ← Complex.exp_conj, Complex.exp_neg]
  all_goals field_simp
end AdalyFormal.Round10.Dictionary.FreeSource

noncomputable section
namespace AdalyFormal.Round10.Dictionary.Color
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round9.Guarded.QualitativeR2 (flipElt flipGauge)
open AdalyFormal.Round10.Dictionary.Source (neutralCoord neutral_of_half_fixed)
open AdalyFormal.D1Literal (uθ)

section Quadratic
variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]

end Quadratic

variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round10.Dictionary.Color
noncomputable section
namespace AdalyFormal.Round10.Dictionary.ColorResponse
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.Color

variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round10.Dictionary.ColorResponse
noncomputable section
namespace AdalyFormal.Round10.Dictionary.ColorObstruction
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.Color
open AdalyFormal.Round10.Dictionary.ColorResponse
open AdalyFormal.D1Literal (sing sing_apply sing_apply_self)

                                                     
end AdalyFormal.Round10.Dictionary.ColorObstruction
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AdalyFormal.Round10.Nonvanishing.PolynomialGrid

open Polynomial

                                                                                       
end AdalyFormal.Round10.Nonvanishing.PolynomialGrid

namespace AdalyFormal.Round10.Nonvanishing.PolynomialGrid

open Polynomial

                                                                                       
end AdalyFormal.Round10.Nonvanishing.PolynomialGrid

namespace AdalyFormal.Round10.Nonvanishing.PolynomialGrid

open Polynomial

                                                                           
                                                                            
                                                                       

end AdalyFormal.Round10.Nonvanishing.PolynomialGrid
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                              
section Selectors
variable (sD sJ : PlaqSel)

section Ops
variable (P : IngrBParams)

end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin


namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin

open Classical
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

open Classical
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2

open Classical
end AdalyFormal.Round9.Guarded.Qualitative

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round9.Guarded.QualitativeR2Joint
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2

open Classical
end AdalyFormal.Round9.Guarded.QualitativeR2Joint

namespace AdalyFormal.Round9.Guarded.AnalyticR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

open Classical
end AdalyFormal.Round9.Guarded.AnalyticR1

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1

open Classical
end AdalyFormal.Round9.Guarded.AnalyticR2

namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open Filter
open scoped Topology
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.D1Literal

open Classical
end AdalyFormal.Round10.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.PhaseSource
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily
open AdalyFormal.D1Literal (uθ uMat)
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.SourceJ
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Balaban.SuTwoInner
variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round10.Dictionary.PhaseSource

                                                                                  
                                                                                
                                                                                     
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round10.Dictionary.KKT
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E S F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

                                                              
end AdalyFormal.Round10.Dictionary.KKT

                                                                                
noncomputable section
namespace AdalyFormal.Round10.Dictionary.Source
open scoped RealInnerProductSpace Topology
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_coe_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.D1Literal (uθ)

                                                                           
end AdalyFormal.Round10.Dictionary.Source

                                                                 
noncomputable section
namespace AdalyFormal.Round10.Dictionary.SourceEnergy
open scoped BigOperators RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo)
open AdalyFormal.Balaban.CovariantHjMinimizer
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.PhaseSource
variable {L : PeriodicLatticeExtent}
attribute [local instance] Classical.propDecidable

end AdalyFormal.Round10.Dictionary.SourceEnergy

                                                                                                      
noncomputable section
namespace AdalyFormal.Round10.Dictionary.FreeSource
open scoped BigOperators RealInnerProductSpace Topology Matrix
open Filter
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.QualitativeR2Joint
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 SuTwo RMap)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Dictionary.PhaseSource
attribute [local instance] Classical.propDecidable

variable {L : PeriodicLatticeExtent}

theorem sourceLinear_U1 (P : Set (PeriodicLatticePlaquette L)) (f : Bond L → ℝ) (α : ℝ) :
    adBL (rotGauge α) (sourceLinear P f) = sourceLinear P f := by
  apply PiLp.ext
  intro b
  change RMap (AdalyFormal.D1Literal.uθ α) (linearSourceScalar P f b • pauliE3) =
    linearSourceScalar P f b • pauliE3
  rw [map_smul, phase_axis_fixed]
theorem profileSource_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (α : ℝ) :
    adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (profileSourceStencil q R f) =
      profileSourceStencil q R f := by
  unfold profileSourceStencil
  rw [← pE_adBL, sourceLinear_U1]
theorem profileCoupling_U1 (q R : ℕ) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (α : ℝ) (u : TwistSpace q R) :
    profileCoupling q R f (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      profileCoupling q R f u := by
  have h := AdalyFormal.M1GaugeW4.baseEqv_gparams (by norm_num : 0 < 2)
    (dilTower q R) 1 (dilLam q R) (fun _ => 1) (rotGauge α)
  rw [rot_trivial] at h
  change 2 * ⟪(flatData q R).H ((flatData q R).C2
    (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u)), profileSourceStencil q R f⟫ =
    2 * ⟪(flatData q R).H ((flatData q R).C2 u), profileSourceStencil q R f⟫
  have hc : (flatData q R).C2 (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      adFL (rotGauge α) (geomOf 2 1 (dilTower q R)) ((flatData q R).C2 u) := h.C2 u
  rw [hc, flatH_U1]
  conv_lhs => rw [← profileSource_U1 q R f α]
  rw [LinearIsometryEquiv.inner_map_map]
def responseField (q R : ℕ) (u : TwistSpace q R) : BondFnL2 (scaleUp 2 1 (dilLu q R)) :=
  WithLp.toLp 2 (fun b => responseProfile q R u b • pauliE3)
end AdalyFormal.Round10.Dictionary.FreeSource

                                                                                    
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace AdalyFormal.Round12.Kernel.Response
open scoped RealInnerProductSpace
open AdalyFormal.IngredientFamilyR2
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

                                                                                     
theorem quadratic_on_charged_line (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    Q (a • u + b • J u) = (a^2+b^2) • Q u := by
  obtain ⟨B, hB⟩ := hQ
  have he := hJ u
  have hm := hJ (u + J u)
  rw [map_add, hu] at hm
  simp only [hB, map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply] at he hm
  have hc : B u (J u) + B (J u) u = 0 := by
    have hh : (2 : ℝ) • (B u (J u) + B (J u) u) = 0 := by
      calc
        _ = (B u u + B (J u) u + (B u (J u) + B (J u) (J u))) -
            (B (J u) (J u) + -B u (J u) + -(B (J u) u + -B u u)) := by module
        _ = 0 := sub_eq_zero.mpr hm.symm
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  simp only [hB, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  calc
    _ = (a^2) • B u u + (b^2) • B (J u) (J u) +
        (a*b) • (B u (J u) + B (J u) u) := by module
    _ = (a^2+b^2) • B u u := by rw [hc, smul_zero, add_zero, he, add_smul]
theorem norm_sq_on_charged_line (J : E ≃ₗᵢ[ℝ] E)
    (u : E) (hu : J (J u) = -u) (a b : ℝ) :
    ‖a • u + b • J u‖^2 = (a^2+b^2) * ‖u‖^2 := by
  have h := J.inner_map_map u (J u)
  rw [hu, inner_neg_right] at h
  have hc := real_inner_comm (J u) u
  have hz : ⟪u,J u⟫ = 0 := by linarith
  have hz' : ⟪J u,u⟫ = 0 := by linarith
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hz, hz', J.inner_map_map, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  ring
theorem response_eq_norm_ratio (Q : E → F) (hQ : IsQuadMap Q)
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ x, Q (J x) = Q x)
    (u : E) (hu : J (J u) = -u) (hne : u ≠ 0)
    (v : E) (hv : v ∈ Submodule.span ℝ ({u,J u} : Set E)) :
    Q v = (‖v‖^2 / ‖u‖^2) • Q u := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [quadratic_on_charged_line Q hQ J hJ u hu,
    norm_sq_on_charged_line J u hu]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hne))]
end AdalyFormal.Round12.Kernel.Response

namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
end AdalyFormal.Round9.Guarded.Qualitative
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open Set
open AdalyFormal.D1Literal (PSD)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end AdalyFormal.Round9.Guarded.QualitativeR2



namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round10.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
end AdalyFormal.Round10.Assembly.R2


namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
variable {L : PeriodicLatticeExtent}
open AdalyFormal.D1Literal (SU2m)
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round10.Assembly.R4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end AdalyFormal.Round10.Assembly.R4

namespace AdalyFormal.Round10.Assembly.R4
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
end AdalyFormal.Round10.Assembly.R4

namespace AdalyFormal.Round10.Assembly.R3
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round10.Dictionary.PhaseSource
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Dictionary.SourceEnergy
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
end AdalyFormal.Round10.Assembly.R3

namespace AdalyFormal.Round12.Kernel.ResponseActual
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Dictionary.Source
open AdalyFormal.Round10.Dictionary.FreeSource
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round10.Assembly.R3
open AdalyFormal.Round10.Assembly.R4
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round12.Kernel.Response

theorem double_inner_linear {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x y : X) (a : ℝ) : 2 * ⟪a • x,y⟫ = a * (2 * ⟪x,y⟫) := by
  rw [real_inner_smul_left]; ring
theorem profileCoupling_quad (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    IsQuadMap (profileCoupling q R f) := by
  let G := geomOf 2 1 (dilTower q R)
  let M : FSp G →ₗ[ℝ] ℝ :=
    { toFun := fun z => 2 * ⟪(flatData q R).H z, profileSourceStencil q R f⟫
      map_add' := by intros; simp only [map_add, inner_add_left]; ring
      map_smul' := by
        intro c z
        change 2 * ⟪(flatData q R).H (c • z), profileSourceStencil q R f⟫ =
          c * (2 * ⟪(flatData q R).H z, profileSourceStencil q R f⟫)
        rw [map_smul]
        exact double_inner_linear (X := TwistSpace q R) _ _ c }
  exact ((C2fullOf_quad G (fun _ => 1)).comp_linear
    (((Wop G (fun _ => 1) 1).comp (iE G)).toLinearMap)).map_linear M
theorem responseGradient_on_line (q R : ℕ) (u : TwistSpace q R)
    (hu : u ≠ 0)
    (hJu : adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R))
      (adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u) = -u)
    (v : TwistSpace q R)
    (hv : v ∈ Submodule.span ℝ {u,
      adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)) u}) :
    responseGradient q R v = (‖v‖^2 / ‖u‖^2) • responseGradient q R u := by
  apply ext_inner_left ℝ
  intro f
  rw [inner_smul_right, ← profileCoupling_gradient q R (fun b => f b),
    ← profileCoupling_gradient q R (fun b => f b)]
  exact response_eq_norm_ratio (profileCoupling q R (fun b => f b))
    (profileCoupling_quad q R _) (adEL (rotGauge (Real.pi/4)) (geomOf 2 1 (dilTower q R)))
    (profileCoupling_U1 q R _ (Real.pi/4)) u hJu hu v hv
theorem responseHull_singleton (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    responseHull (crossingKernel q R V) (responseGradient q R) =
      {(‖u‖^2)⁻¹ • responseGradient q R u} := by
  have himage : responseGradient q R ''
      {v | v ∈ crossingKernel q R V ∧ ‖v‖ = 1} =
      {(‖u‖^2)⁻¹ • responseGradient q R u} := by
    ext z
    constructor
    · rintro ⟨v,⟨hv,hn⟩,rfl⟩
      rw [Set.mem_singleton_iff,
        responseGradient_on_line q R u hline.1 hline.2.2.1 v (hline.2.2.2 v hv), hn]
      simp
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨‖u‖⁻¹ • u, ⟨(crossingKernel q R V).smul_mem _ hline.2.1, ?_⟩, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hline.1)]
      · rw [responseGradient_smul, inv_pow]
  rw [responseHull, himage, closedConvexHull_eq_closure_convexHull, convexHull_singleton,
    isClosed_singleton.closure_eq]
theorem noCancellation_iff_curlDetected_of_kernelLine (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u : TwistSpace q R) (hline : KernelLine q R V u) :
    NoResponseCancellation q R V ↔ CurlDetected q R u := by
  rw [NoResponseCancellation, responseHull_singleton q R V u hline,
    Set.mem_singleton_iff, eq_comm]
  change (‖u‖^2)⁻¹ • responseGradient q R u ≠ 0 ↔ CurlDetected q R u
  rw [smul_ne_zero_iff, responseGradient_ne_zero_iff]
  simp [hline.1]
theorem cofinal_noCancellation_of_curlLine
    (h : CofinalAnyPathCurlLine) : CofinalAnyPathNoResponseCancellation := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,fun R₀ => ?_⟩
  obtain ⟨R,hRR,hR,hR18,V,hcont,han,hzero,hneg,u,hline,hcurl⟩ := hRs R₀
  exact ⟨R,hRR,hR,hR18,V,hcont,han,hzero,hneg,
    (noCancellation_iff_curlDetected_of_kernelLine (2^j) R V u hline).mpr hcurl⟩
end AdalyFormal.Round12.Kernel.ResponseActual

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin

open Classical

end AdalyFormal.Round4.Guarded.RefuteR1
namespace AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

theorem Ginv_all_gauge {ell k : ℕ} {Lu : PeriodicLatticeExtent} (hell : 0 < ell)
    (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu)) (a : ℝ)
    (Lam : Set (PeriodicLatticeSite Lu)) (γ : GaugeFn (scaleUp ell k Lu))
    (x : ↥(bondSupp (geomOf ell k S))) :
    (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Ginv
        (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ginv x) := by
  have hB := bondEqv_gauge (gparams ell k Lu hell S U a Lam) γ
  have hD := hB.baseEqv
  have hW : ∀ z, Wop (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (Wop (geomOf ell k S) U a z) := fun z => hB.W z
  have hΔ : ∀ z, AdalyFormal.StatementLaneR6.deltaKLocCLM (periodicGaugeTransform γ U) Set.univ
      (adBL γ z) = adBL γ (AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ z) :=
    fun z => deltaKLocCLM_gauge γ U Set.univ z
  have hDp : ∀ z, DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a (adBL γ z) =
      adBL γ (DpiFullS selAll (geomOf ell k S) U a z) := by
    intro z
    simp only [DpiFullS, DeltaS, selAll, ContinuousLinearMap.comp_apply]
    rw [hW, hΔ]
    exact adjoint_intertwine (adBL γ) (adBL γ) hW _
  have hDpi : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Dpi
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Dpi x) := by
    show pE (geomOf ell k S) (DpiFullS selAll (geomOf ell k S) (periodicGaugeTransform γ U) a
        (iE (geomOf ell k S) (adEL γ (geomOf ell k S) x))) =
      adEL γ (geomOf ell k S) (pE (geomOf ell k S)
        (DpiFullS selAll (geomOf ell k S) U a (iE (geomOf ell k S) x)))
    rw [iE_adEL, hDp, pE_adBL]
  have hT : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).T
      (adEL γ (geomOf ell k S) x) =
      adSL γ ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).T x) := hD.T x
  have hTs : ∀ s, (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a
      Lam)).Ts (adSL γ s) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Ts s) :=
    hD.Ts
  have hM : (dataS selAll selAll (gparams ell k Lu hell S (periodicGaugeTransform γ U) a Lam)).Mass
      (adEL γ (geomOf ell k S) x) =
      adEL γ (geomOf ell k S) ((dataS selAll selAll (gparams ell k Lu hell S U a Lam)).Mass x) :=
    hD.Mass x
  simp only [BaseDataS.Ginv, add_apply, ContinuousLinearMap.comp_apply]
  rw [hDpi, hT, hTs, hM, map_add, map_add]
end AdalyFormal.Round10.Dictionary
open scoped RealInnerProductSpace

namespace AdalyFormal.Round12.Kernel

section SpectralExclusion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

                                                                                          
                                                                                      
theorem charged_span_finrank (J : E ≃ₗᵢ[ℝ] E) (u : E) (hu : u ≠ 0)
    (hJJ : J (J u) = -u) :
    Module.finrank ℝ (Submodule.span ℝ ({u, J u} : Set E)) = 2 := by
  have horth : ⟪u, J u⟫ = 0 := by
    have h := J.inner_map_map u (J u)
    rw [hJJ, inner_neg_right, real_inner_comm u (J u)] at h
    linarith
  have hJn : J u ≠ 0 := by simpa using hu
  have hind : LinearIndependent ℝ ![u, J u] := by
    rw [linearIndependent_fin2]
    refine ⟨hJn, fun a ha => ?_⟩
    have hh := congrArg (fun x => ⟪u, x⟫) ha
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      inner_smul_right, horth, mul_zero] at hh
    exact hu (inner_self_eq_zero.mp hh.symm)
  have hrange : Set.range ![u, J u] = ({u, J u} : Set E) := by
    ext x
    simp [or_comm]
  have hdim := finrank_span_eq_card hind
  rw [hrange] at hdim
  simpa using hdim
theorem kernel_eq_charged_span [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E)
    (hcomm : ∀ x, A (J x) = J (A x))
    (u : E) (hu : u ≠ 0) (hAu : A u = 0) (hJJ : J (J u) = -u)
    (hdim : Module.finrank ℝ A.ker ≤ 2) :
    A.ker = Submodule.span ℝ ({u, J u} : Set E) := by
  have hle : Submodule.span ℝ ({u, J u} : Set E) ≤ A.ker := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x; exact hAu
    · have hx' : x = J u := Set.mem_singleton_iff.mp h
      subst x
      change A (J u) = 0
      rw [hcomm, hAu, map_zero]
  exact (Submodule.eq_of_le_of_finrank_le hle (by
    rw [charged_span_finrank J u hu hJJ]
    exact hdim)).symm
theorem boundary_observable_injective {B : Type*} [AddCommGroup B] [Module ℝ B]
    (A : E →L[ℝ] E) (r : E →ₗ[ℝ] B)
    (hpos : ∀ u : E, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
    Function.Injective (r.comp A.ker.subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hn
  have hr : r ((x : E) - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have ha : A ((x : E) - y) = 0 := by
    rw [map_sub, show A (x : E) = 0 from x.property,
      show A (y : E) = 0 from y.property, sub_self]
  have hh := hpos ((x : E) - y) hn hr
  simp only [ha, inner_zero_right, lt_self_iff_false] at hh
theorem kernel_finrank_le_two_of_boundary (A : E →L[ℝ] E) (r : E →ₗ[ℝ] ℂ)
    (hpos : ∀ u : E, u ≠ 0 → r u = 0 → 0 < ⟪u, A u⟫) :
    Module.finrank ℝ A.ker ≤ 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (boundary_observable_injective A r hpos)
  simpa only [Complex.finrank_real_complex] using h
theorem charged_of_boundary (A : E →L[ℝ] E) (J : E →ₗ[ℝ] E)
    (r : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ x, A (J x) = J (A x))
    (hpos : ∀ x : E, x ≠ 0 → r x = 0 → 0 < ⟪x, A x⟫)
    (hcoord : ∀ x, r (J (J x)) = -r x)
    (u : E) (hAu : A u = 0) : J (J u) = -u := by
  have hj : A (J (J u)) = 0 := by rw [hcomm, hcomm, hAu, map_zero, map_zero]
  have hn : A (-u) = 0 := by rw [map_neg, hAu, neg_zero]
  have he : (⟨J (J u), hj⟩ : A.ker) = ⟨-u, hn⟩ := by
    apply boundary_observable_injective A r hpos
    change r (J (J u)) = r (-u)
    rw [hcoord, map_neg]
  exact congrArg Subtype.val he
theorem kernel_eq_charged_span_of_boundary [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (J : E ≃ₗᵢ[ℝ] E) (r : E →ₗ[ℝ] ℂ)
    (hcomm : ∀ x, A (J x) = J (A x))
    (hpos : ∀ x : E, x ≠ 0 → r x = 0 → 0 < ⟪x, A x⟫)
    (u : E) (hu : u ≠ 0) (hAu : A u = 0) (hJJ : J (J u) = -u) :
    A.ker = Submodule.span ℝ ({u, J u} : Set E) :=
  kernel_eq_charged_span A J hcomm u hu hAu hJJ
    (kernel_finrank_le_two_of_boundary A r hpos)
end SpectralExclusion

section BoundaryCertificate
variable {𝕜 : Type*} [Field 𝕜]
variable {E B : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup B] [Module 𝕜 B]

                                                                             
                                                                                       
end BoundaryCertificate

end AdalyFormal.Round12.Kernel

namespace AdalyFormal.Round10.Dictionary.ColorObstruction
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.GaugeCov (adEL)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.D1Literal (sing sing_apply sing_apply_self)
                                                     
end AdalyFormal.Round10.Dictionary.ColorObstruction


namespace AdalyFormal.Round12.Kernel.Actual
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (BondFnL2 RMap RMap_coe_apply RMap_mul_apply)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                         
def chargedCoordinate (q R : ℕ) (b : Bond (scaleUp 2 1 (dilLu q R))) :
    TwistSpace q R →ₗ[ℝ] ℂ where
  toFun u := ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  map_add' u v := rfl
  map_smul' c u := by
    change ((c : ℂ) * _) = _
    rfl
theorem vacA_rot_of_fixed (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (α t : ℝ)
    (hV : periodicGaugeTransform (rotGauge α) (V t) = V t)
    (u : TwistSpace q R) :
    vacA q R V 1 t (adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) u) =
      adEL (rotGauge α) (geomOf 2 1 (dilTower q R)) (vacA q R V 1 t u) := by
  have h := AdalyFormal.Round10.Dictionary.Ginv_all_gauge
    (ell := 2) (k := 1) (Lu := dilLu q R) (by norm_num) (dilTower q R)
    (pathU q R V (fun _ => 0) 0 t) 1 (dilLam q R) (rotGauge α) u
  have hp : periodicGaugeTransform (rotGauge α) (pathU q R V (fun _ => 0) 0 t) =
      pathU q R V (fun _ => 0) 0 t := by
    unfold pathU
    rw [rot_maskedU, hV]
  rw [hp] at h
  exact h
theorem uθ_add (s t : ℝ) : AdalyFormal.D1Literal.uθ s * AdalyFormal.D1Literal.uθ t =
    AdalyFormal.D1Literal.uθ (s + t) := by
  apply Subtype.ext
  show AdalyFormal.D1Literal.uMat s * AdalyFormal.D1Literal.uMat t =
    AdalyFormal.D1Literal.uMat (s + t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdalyFormal.D1Literal.uMat, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ofReal_add, mul_add, Complex.exp_add, neg_add_rev, mul_comm]
theorem chargedCoordinate_quarter_twice (q R : ℕ)
    (b : Bond (scaleUp 2 1 (dilLu q R))) (u : TwistSpace q R) :
    chargedCoordinate q R b
      (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
        (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u)) =
      -chargedCoordinate q R b u := by
  change (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4))
    (RMap (AdalyFormal.D1Literal.uθ (Real.pi / 4))
      ((u : BondFnL2 (scaleUp 2 1 (dilLu q R))) b)) :
        Matrix (Fin 2) (Fin 2) ℂ) 0 1 = _
  rw [RMap_mul_apply, uθ_add,
    show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
    RMap_coe_apply, AdalyFormal.Round10.Dictionary.half_rotation_matrix]
  simp [chargedCoordinate, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring_nf
  simp [Complex.I_sq]
theorem kernelLine_of_boundary_positive (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V))
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 → chargedCoordinate q R b x = 0 →
      0 < ⟪x, vacA q R V 1 (vacEdge q R V) x⟫)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hAu : vacA q R V 1 (vacEdge q R V) u = 0) :
    KernelLine q R V u := by
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  have hcomm := vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV
  have hJJ : J (J u) = -u := charged_of_boundary
    (vacA q R V 1 (vacEdge q R V)) J.toLinearMap (chargedCoordinate q R b)
    hcomm hpos (chargedCoordinate_quarter_twice q R b) u hAu
  refine ⟨hu, hAu, hJJ, fun x hx => ?_⟩
  have hk := kernel_eq_charged_span_of_boundary
    (vacA q R V 1 (vacEdge q R V))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)))
    (chargedCoordinate q R b)
    (vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV)
    hpos u hu hAu hJJ
  rw [← hk]
  exact hx
theorem kernelLine_finrank (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (hV : periodicGaugeTransform (rotGauge (Real.pi / 4)) (V (vacEdge q R V)) =
      V (vacEdge q R V)) (u : TwistSpace q R) (hline : KernelLine q R V u) :
    Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2 := by
  let A := vacA q R V 1 (vacEdge q R V)
  let J := adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
  have hk : A.ker = Submodule.span ℝ ({u, J u} : Set (TwistSpace q R)) := by
    apply le_antisymm
    · exact fun x hx => hline.2.2.2 x hx
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with h | h
      · subst x; exact hline.2.1
      · have hx' : x = J u := Set.mem_singleton_iff.mp h
        subst x
        change A (J u) = 0
        rw [vacA_rot_of_fixed q R V (Real.pi / 4) (vacEdge q R V) hV u,
          hline.2.1, map_zero]
  change Module.finrank ℝ A.ker = 2
  rw [hk]
  exact charged_span_finrank J u hline.1 hline.2.2.1
end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace Topology
open Set
open AdalyFormal.D1Literal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem psdEdge_singular_without_isolation (A : ℝ → E →L[ℝ] E) (hc : Continuous A)
    (hs : ∀ t x y, ⟪A t x, y⟫ = ⟪x, A t y⟫) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x, A t₀ x⟫) (w : E) (hw : ⟪w, A t₁ w⟫ < 0) :
    t₀ < psdEdge A t₀ t₁ ∧ psdEdge A t₀ t₁ < t₁ ∧
    PSD (A (psdEdge A t₀ t₁)) ∧ ¬ IsUnit (A (psdEdge A t₀ t₁)) ∧
    (∀ s, t₀ ≤ s → s ≤ psdEdge A t₀ t₁ → PSD (A s)) ∧
    (∀ η : ℝ, 0 < η → ∃ s, psdEdge A t₀ t₁ < s ∧ s < psdEdge A t₀ t₁ + η ∧
        ∃ v, ⟪v, A s v⟫ < 0) := by
  set S : Set ℝ := {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)} with hS
  have hts' : psdEdge A t₀ t₁ = sSup S := rfl
  set ts := psdEdge A t₀ t₁ with hts
  have hpsd0 : PSD (A t₀) := psd_of_pd _ hpd
  have h0S : t₀ ∈ S := ⟨⟨le_rfl, h01.le⟩, fun s hs' => by
    rw [le_antisymm hs'.2 hs'.1]; exact hpsd0⟩
  have hne : S.Nonempty := ⟨t₀, h0S⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hts0 : t₀ ≤ ts := by rw [hts']; exact le_csSup hbdd h0S
  have hts1 : ts ≤ t₁ := by rw [hts']; exact csSup_le hne (fun t ht => ht.1.2)
  obtain ⟨δ, hδ, hpdn⟩ := eventually_pd hc hs t₀ hpd
  have hδS : min (t₀ + δ / 2) t₁ ∈ S := by
    refine ⟨⟨le_min (by linarith) h01.le, min_le_right _ _⟩, fun s hs' => ?_⟩
    have hs1 : s ≤ t₀ + δ / 2 := le_trans hs'.2 (min_le_left _ _)
    exact psd_of_pd _ (hpdn s (by rw [abs_lt]; constructor <;> linarith [hs'.1]))
  have hts0' : t₀ < ts := by
    have h1 : t₀ < min (t₀ + δ / 2) t₁ := lt_min (by linarith) h01
    have h2 : min (t₀ + δ / 2) t₁ ≤ ts := by rw [hts']; exact le_csSup hbdd hδS
    linarith
  have hlt : ∀ s, t₀ ≤ s → s < ts → PSD (A s) := by
    intro s hs0 hs1
    rw [hts'] at hs1
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hs1
    exact ht.2 s ⟨hs0, hst.le⟩
  have hpsd_ts : PSD (A ts) := by
    intro v
    have hsub : Ico t₀ ts ⊆ {s : ℝ | 0 ≤ ⟪v, A s v⟫} := fun s hs' => hlt s hs'.1 hs'.2 v
    have hcl : IsClosed {s : ℝ | 0 ≤ ⟪v, A s v⟫} := isClosed_le continuous_const (by fun_prop)
    have hcs := hcl.closure_subset_iff.mpr hsub
    exact hcs (by rw [closure_Ico hts0'.ne]; exact ⟨hts0, le_rfl⟩)
  have hle : ∀ s, t₀ ≤ s → s ≤ ts → PSD (A s) := by
    intro s hs0 hs1
    rcases hs1.lt_or_eq with h | h
    · exact hlt s hs0 h
    · rw [h]; exact hpsd_ts
  have hts1' : ts < t₁ := by
    rcases hts1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hpsd_ts w
      rw [h] at this
      linarith
  have haft : ∀ η : ℝ, 0 < η → ∃ s, ts < s ∧ s < ts + η ∧ ∃ v, ⟪v, A s v⟫ < 0 := by
    intro η hη
    set t' := min (ts + η / 2) t₁ with ht'
    have ht'1 : ts < t' := lt_min (by linarith) hts1'
    have hnot : t' ∉ S := by
      intro h
      have : t' ≤ ts := by rw [hts']; exact le_csSup hbdd h
      linarith
    have hnall : ¬ ∀ s ∈ Icc t₀ t', PSD (A s) := fun hall =>
      hnot ⟨⟨by linarith, min_le_right _ _⟩, hall⟩
    push Not at hnall
    obtain ⟨s, hs', hns⟩ := hnall
    have hsts : ts < s := by
      by_contra hcon
      push Not at hcon
      exact hns (hle s hs'.1 hcon)
    have hst' : s < ts + η := lt_of_le_of_lt (le_trans hs'.2 (min_le_left _ _)) (by linarith)
    unfold PSD at hns
    push Not at hns
    exact ⟨s, hsts, hst', hns⟩
  have hnu : ¬ IsUnit (A ts) := by
    intro hu
    have hpdts : ∀ x, x ≠ 0 → 0 < ⟪x, A ts x⟫ := fun x hx =>
      pos_of_psd_unit _ (hs ts) hpsd_ts hu x hx
    obtain ⟨δ', hδ', hb⟩ := eventually_pd hc hs ts hpdts
    obtain ⟨s, h1, h2, v, hv⟩ := haft δ' hδ'
    have hsd := hb s (by rw [abs_lt]; constructor <;> linarith)
    by_cases hv0 : v = 0
    · rw [hv0] at hv; simp at hv
    · linarith [hsd v hv0]
  exact ⟨hts0', hts1', hpsd_ts, hnu, hle, haft⟩
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Kernel.Crossing
open scoped RealInnerProductSpace Topology
open Set
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

                                                                              
                                                                                  
theorem psdEdge_same_after_negative (A : ℝ → E →L[ℝ] E)
    {a T b : ℝ} (haT : a ≤ T) (hTb : T ≤ b) (w : E) (hw : ⟪w,A T w⟫ < 0) :
    psdEdge A a b = psdEdge A a T := by
  unfold psdEdge
  congr 1
  ext t
  constructor
  · rintro ⟨ht,hall⟩
    have htT : t < T := by
      by_contra h
      have hp := hall T ⟨haT, le_of_not_gt h⟩ w
      linarith
    exact ⟨⟨ht.1,htT.le⟩,hall⟩
  · rintro ⟨ht,hall⟩
    exact ⟨⟨ht.1,ht.2.trans hTb⟩,hall⟩
theorem exists_kernel_of_nonunit [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (h : ¬ IsUnit A) : ∃ u, u ≠ 0 ∧ A u = 0 := by
  by_contra hn
  push Not at hn
  have hi : Function.Injective A := (injective_iff_map_eq_zero A).mpr (by
    intro u hu
    by_contra hne
    exact hn u hne hu)
  exact h (ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi,(LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi⟩)
end AdalyFormal.Round12.Kernel.Crossing

namespace AdalyFormal.Round12.Kernel.CrossingActual
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Assembly.R2
open AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Round12.Kernel.Crossing
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

                                                                          
                                                                                    
                                                                           
theorem kernelLine_exists_before_halfpi (q R : ℕ)
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (b : Bond (scaleUp 2 1 (dilLu q R)))
    (hc : Continuous (vacA q R V 1))
    (hpd : ∀ x, x ≠ 0 → 0 < ⟪x,vacA q R V 1 0 x⟫)
    (hw : ∃ w, ⟪w,vacA q R V 1 (Real.pi/2) w⟫ < 0)
    (hV : ∀ t, periodicGaugeTransform (rotGauge (Real.pi/4)) (V t) = V t)
    (hp : ∀ t, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace q R,
      x ≠ 0 → chargedCoordinate q R b x = 0 → 0 < ⟪x,vacA q R V 1 t x⟫) :
    0 < vacEdge q R V ∧ vacEdge q R V < Real.pi/2 ∧
      ∃ u : TwistSpace q R, KernelLine q R V u ∧
        Module.finrank ℝ (vacA q R V 1 (vacEdge q R V)).ker = 2 := by
  obtain ⟨w,hw⟩ := hw
  have hs : ∀ t x y, ⟪vacA q R V 1 t x,y⟫ = ⟪x,vacA q R V 1 t y⟫ := by
    intro t x y
    exact (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll
      AdalyFormal.D1Literal.selAll (pathP q R V (fun _ => 0) 0 1 t)).Ginv_symm
      (AdalyFormal.D1Literal.dataS_laws _ _ _) x y
  have heq : vacEdge q R V = psdEdge (vacA q R V 1) 0 (Real.pi/2) :=
    psdEdge_same_after_negative _ (by positivity) (by linarith [Real.pi_pos]) w hw
  obtain ⟨h0,ht,_,hn,_,_⟩ := psdEdge_singular_without_isolation
    (vacA q R V 1) hc hs (by positivity : (0:ℝ) < Real.pi/2) hpd w hw
  rw [← heq] at h0 ht hn
  obtain ⟨u,hu,hAu⟩ := exists_kernel_of_nonunit _ hn
  have hl := kernelLine_of_boundary_positive q R V b (hV _) (hp _ h0 ht) u hu hAu
  exact ⟨h0,ht,u,hl,kernelLine_finrank q R V (hV _) u hl⟩
end AdalyFormal.Round12.Kernel.CrossingActual

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
variable {L : PeriodicLatticeExtent}

                                                                                                
def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}
open Classical in
/-- Equal-sign exterior star; unlike the translation-invariant twist, the support is local. -/
def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1
theorem starPath_zero (x : PeriodicLatticeSite L) : starPath x 0 = fun _ => 1 := by
  funext e
  simp [starPath, uθ_zero]
theorem starPath_cont (x : PeriodicLatticeSite L) : ContFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    change Continuous fun t => uMat t
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [starPath, h, if_false]
    exact continuous_const
theorem starPath_an (x : PeriodicLatticeSite L) : AnFam (starPath x) := by
  intro e
  by_cases h : e ∈ starLinks x
  · simp only [starPath, h, if_true]
    show AnM fun t => uMat t
    exact anM_uMat
  · intro t i j
    simp only [starPath, h, if_false]
    exact analyticAt_const
theorem starLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om)) :
    starLinks x ⊆ Zb Om := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change z = x at hz
    subst z
    exact ⟨hx, fun h => hx ((htrans x ν hν).mp h)⟩
  · exact ⟨fun h => hx (hz ▸ (htrans z ν hν).mpr h), fun h => hx (hz ▸ h)⟩
theorem starPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => he (starLinks_exterior Om x hx htrans h)
  simp [starPath, hh]
theorem starPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : starPath x t e = 1 := by
  have hh : e ∉ starLinks x := fun h => (starLinks_exterior Om x hx htrans h).1 he
  simp [starPath, hh]
theorem starPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    starPath x t (z,0) = 1 := by simp [starPath, starLinks]
theorem star_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) x t
  have h2 : starPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t := by
    simp [starPath, starLinks, hν]
  have h3 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P1
  simp only
  rw [h1,h2,h3,h4]
  simp
theorem star_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (starPath (periodicLatticeShift x 0) t) (P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := starPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : starPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starPath, starLinks, hν, hs]
  have h3 := starPath_normal (periodicLatticeShift x 0) x t
  have h4 := starPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp
theorem star_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (starPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := starPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (starPath _ Real.pi) (P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [star_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact starPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round3.Guarded.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.Path

                                                                                                        
def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)
theorem rightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    rightStar hq R 0 = fun _ => 1 := starPath_zero _
theorem rightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AdalyFormal.D1Literal.ContFam (rightStar hq R) := starPath_cont _
theorem rightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AnFam (rightStar hq R) := starPath_an _
theorem rightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    rightStar hq R t e = 1 :=
  starPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e he
theorem pathU_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (rightStar hq R) f 0 t = rightStar hq R t := by
  classical
  funext e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp [pathU,maskedU,he]
  · rw [rightStar_off_exterior hq R t e he]
    simp [pathU,maskedU,he,Ug_zero]
theorem vacA_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (rightStar hq R) a t =
      (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (rightStar hq R t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_rightStar]
  rfl
theorem rightStar_negative {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w, ⟪w, vacA q R (rightStar hq R) 1 Real.pi w⟫ < 0 := by
  rw [vacA_rightStar]
  exact star_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero
end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round12.Noncancel.Gauge
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round12.Noncancel.Path

                                                                           
theorem uθ_comm (α s : ℝ) : uθ α * uθ s = uθ s * uθ α := by
  apply Subtype.ext
  show uMat α * uMat s = uMat s * uMat α
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
theorem starPath_fixed {L : PeriodicLatticeExtent}
    (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (starPath x t) = starPath x t := by
  funext e
  change uθ α * starPath x t e * (uθ α)⁻¹ = starPath x t e
  by_cases he : e ∈ starLinks x
  · simp only [starPath,he,if_true]
    rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
  · simp [starPath,he]
end AdalyFormal.Round12.Noncancel.Gauge

namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Assembly.R3 (CofinalAnyPathCurlLine)
open AdalyFormal.Round10.Assembly.R4 (CofinalAnyPathNoResponseCancellation)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Kernel.Actual (chargedCoordinate)
open AdalyFormal.Round12.Noncancel.RightFamily

                                                                             
def P1 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
  ∃ w : TwistSpace q R,
    ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0
def P2 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (t : ℝ), 0 < t → t < Real.pi/2 →
  ∀ x : TwistSpace q R, x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫
def P3 : Prop :=
∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
  (u : TwistSpace q R), KernelLine q R (rightStar hq R) u →
    CurlDetected q R u
def StartInputs : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q), 2 ∣ R → 18 ≤ R →
    Continuous (vacA q R (rightStar hq R) 1) ∧
    (∀ x : TwistSpace q R, x ≠ 0 →
      0 < ⟪x, vacA q R (rightStar hq R) 1 0 x⟫)
def CofinalRightStarCurlLine : Prop :=
∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
  R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
  ∃ u : TwistSpace (2^j) R,
    KernelLine (2^j) R (rightStar (by positivity) R) u ∧
    CurlDetected (2^j) R u
theorem rightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (rightStar hq R t) = rightStar hq R t :=
  AdalyFormal.Round12.Noncancel.Gauge.starPath_fixed _ t α
theorem detected_line_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3)
    {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      CurlDetected q R u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2 := by
  obtain ⟨hc,hpd⟩ := hs hq hR hR18
  obtain ⟨h0,ht,u,hl,hfin⟩ :=
    AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi
      q R (rightStar hq R) (rightSite hq R,0) hc hpd (h1 hq hR hR18)
      (fun t => rightStar_fixed hq R t (Real.pi/4)) (h2 hq hR hR18)
  exact ⟨h0,ht,u,hl,h3 hq hR hR18 u hl,hfin⟩
theorem cofinalRightStarCurlLine_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalRightStarCurlLine := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  let R := 2*(R₀+18)
  have hR : 2 ∣ R := dvd_mul_right _ _
  have hR18 : 18 ≤ R := by dsimp [R]; omega
  obtain ⟨_,_,u,hl,hd,_⟩ := detected_line_of_physicalInputs hs h1 h2 h3
    (by positivity : 0 < 2^j₀) hR hR18
  exact ⟨R,by dsimp [R]; omega,hR,hR18,u,hl,hd⟩
theorem cofinalAnyPathCurlLine_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,u,hl,hd⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  exact ⟨R,hR0,hR,hR18,rightStar hq R,rightStar_cont hq R,
    rightStar_an hq R,rightStar_zero hq R,rightStar_negative hq hR hR18,u,hl,hd⟩
theorem cofinalNoCancellation_of_rightStar (h : CofinalRightStarCurlLine) :
    CofinalAnyPathNoResponseCancellation :=
  AdalyFormal.Round12.Kernel.ResponseActual.cofinal_noCancellation_of_curlLine
    (cofinalAnyPathCurlLine_of_rightStar h)
theorem cofinalNoCancellation_of_physicalInputs (hs : StartInputs)
    (h1 : P1) (h2 : P2) (h3 : P3) : CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_rightStar
    (cofinalRightStarCurlLine_of_physicalInputs hs h1 h2 h3)
end AdalyFormal.Round13.Assembly.R1

namespace AdalyFormal.Round9.Guarded.AnalyticR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Round4.Guarded.RefuteR1
variable {L : PeriodicLatticeExtent}
end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                              

                                                                                              
                                                                                                 
                                                                                               
                                                                                            
                                                                                                 
                                                                                            
                                                                                          
                                              
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

                                                                                       

variable {q R : ℕ}

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                       
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

                                                                                              
                                                                              
end FlatCarrier
end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.QualitativeR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round12.Noncancel.RightFamily

                                                                                             
theorem rightStar_vacA_cont {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    Continuous (vacA q R (rightStar hq R) 1) := by
  have hc := AdalyFormal.D1Residual.GinvLit_cont (by norm_num : 0 < 2)
    (dil_admissible hq hR) (by norm_num) (by nlinarith : 17*2 ≤ R*(2*q))
    1 (dilLam q R) (rightStar hq R)
    (fun t e he => (rightStar_off_exterior hq R t e he).trans
      (rightStar_off_exterior hq R 0 e he).symm)
    (rightStar_cont hq R)
  have heq : vacA q R (rightStar hq R) 1 =
      AdalyFormal.D1Residual.GinvLit (by norm_num : 0 < 2)
        (dilTower q R) 1 (dilLam q R) (rightStar hq R) := by
    funext t
    exact vacA_rightStar hq R 1 t
  rw [heq]
  exact hc
theorem rightStar_vacA_pd_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : TwistSpace q R) (hx : x ≠ 0) :
    0 < ⟪x, vacA q R (rightStar hq R) 1 0 x⟫ := by
  rw [vacA_rightStar, rightStar_zero]
  have hp := AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos hq hR x hx
  have hm := Ginv_loc_le_all_flat
    (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) 1 (dilLam q R)) rfl x
  exact lt_of_lt_of_le hp hm
theorem startInputs : StartInputs := by
  intro q R hq hR hR18
  exact ⟨rightStar_vacA_cont hq hR hR18,
    rightStar_vacA_pd_zero hq (by omega)⟩
theorem cofinalNoCancellation_of_P1_P2_P3 (h1 : P1) (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_physicalInputs startInputs h1 h2 h3
def CofinalPhysicalInputs : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    (∃ w : TwistSpace (2^j) R,
      ⟪w, vacA (2^j) R (rightStar (by positivity) R) 1 (Real.pi/2) w⟫ < 0) ∧
    (∀ t : ℝ, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace (2^j) R,
      x ≠ 0 → AdalyFormal.Round12.Kernel.Actual.chargedCoordinate (2^j) R
        (AdalyFormal.Round5.Guarded.IVTR2.rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫) ∧
    (∀ u : TwistSpace (2^j) R,
      AdalyFormal.Round10.Assembly.R2.KernelLine (2^j) R (rightStar (by positivity) R) u →
      AdalyFormal.Round10.Dictionary.FreeSource.CurlDetected (2^j) R u)
theorem cofinalRightStarCurlLine_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    CofinalRightStarCurlLine := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,hw,hp,hd⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  obtain ⟨hc,hpd⟩ := startInputs hq hR hR18
  obtain ⟨_,_,u,hl,_⟩ :=
    AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi
      (2^j) R (rightStar hq R)
      (AdalyFormal.Round5.Guarded.IVTR2.rightSite hq R,0) hc hpd hw
      (fun t => rightStar_fixed hq R t (Real.pi/4)) hp
  exact ⟨R,hR0,hR,hR18,u,hl,hd u hl⟩
theorem cofinalNoCancellation_of_cofinalPhysical (h : CofinalPhysicalInputs) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_rightStar (cofinalRightStarCurlLine_of_cofinalPhysical h)
end AdalyFormal.Round13.Assembly.R1

                                                                                 
                                                                    
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack gradCovariantAdjointValue)
variable {L : PeriodicLatticeExtent}

                                                                         
                                                                               
theorem potential_zero_off_om1 {ell k : ℕ} (S : Tower L) (U : Cfg L)
    (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 1) :
    (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U f)) x = 0 := by
  by_cases hx0 : x ∈ S.Om 0
  · apply Gp_Rproj_lam0
    exact ⟨fun μ => by simp, hx0, by simpa using hx⟩
  · exact Gp_Rproj_out _ _ _ _ hx0
theorem Wop_eq_on_collar {ell k : ℕ} (S : Tower L) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) (e : Bond L)
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  have hz : (gradL2 U (Gp (geomOf ell k S) U a
      (Rproj (geomOf ell k S) U (gradAdj U A)))) e = 0 := by
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [potential_zero_off_om1 S U a _ h0, potential_zero_off_om1 S U a _ h1]
    simp
  change A e - (gradL2 U (Gp (geomOf ell k S) U a
    (Rproj (geomOf ell k S) U (gradAdj U A)))) e = A e
  rw [hz, sub_zero]
theorem Wop_eq_on_omitted {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (h4 : 4 ≤ R*M) (U : Cfg L) (a : ℝ)
    (A : BondFnL2 L) {p : PeriodicLatticePlaquette L}
    (hp : p ∉ plaqIn (S.Om 0)) {e : Bond L} (he : e ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop (geomOf ell k S) U a A) e = A e := by
  obtain ⟨h0,h1⟩ := edge_ends_not_om1_of_notIn hS h4 hp he
  exact Wop_eq_on_collar S U a A e h0 h1
theorem gradAdj_sing_support (U : Cfg L) (e : Bond L) (X : SuTwo)
    (z : PeriodicLatticeSite L) (hz0 : z ≠ e.1)
    (hz1 : z ≠ periodicLatticeShift e.1 e.2) :
    gradAdj U (sing e X) z = 0 := by
  rw [show gradAdj U (sing e X) z = (WithLp.ofLp (gradAdj U (sing e X))) z from rfl,
    gradAdj_apply]
  unfold gradCovariantAdjointValue
  refine Finset.sum_eq_zero (fun μ _ => ?_)
  have h0 : (WithLp.ofLp (sing e X)) (z,μ) = 0 :=
    sing_apply_ne _ _ (fun h => hz0 (congrArg Prod.fst h))
  have h1 : (WithLp.ofLp (sing e X)) (periodicLatticeShiftBack z μ,μ) = 0 := by
    apply sing_apply_ne
    intro h
    have hμ : μ = e.2 := congrArg Prod.snd h
    have hx : periodicLatticeShiftBack z μ = e.1 := congrArg Prod.fst h
    apply hz1
    rw [← hx, ← hμ, periodicLatticeShift_shiftBack]
  rw [h0,h1]
  simp
theorem Tfull_sing_zero_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Tfull (geomOf ell k S) U (sing e X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : z = e.1 ∨ z = periodicLatticeShift e.1 e.2
  · have huz : u z = 0 := by
      apply RImage_support S U hu z
      intro y hy hy1
      have hcl := hS.2.2.2.2.1 0 (Nat.zero_le _) x hx y hy1
      have hxz : pdist x z ≤ d := by
        rcases hz with rfl | rfl
        · exact h0
        · exact h1
      have hyz : pdist z y ≤ 1 := hy
      have ht := pdist_triangle x z y
      have hb : bigSide M ell 0 = M := by simp [bigSide]
      rw [hb] at hcl
      omega
    rw [huz]
    simp
  · push Not at hz
    rw [gradAdj_sing_support U e X z hz.1 hz.2]
    simp
theorem Wop_sing_near {ell M R k d : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hd : d+1 ≤ R*M)
    (U : Cfg L) (a : ℝ) (e : Bond L) (X : SuTwo)
    (x : PeriodicLatticeSite L) (hx : x ∉ S.Om 0)
    (h0 : pdist x e.1 ≤ d) (h1 : pdist x (periodicLatticeShift e.1 e.2) ≤ d) :
    Wop (geomOf ell k S) U a (sing e X) = sing e X := by
  have ht := Tfull_sing_zero_near hS hd U e X x hx h0 h1
  unfold Tfull at ht
  simp only [ContinuousLinearMap.comp_apply] at ht
  unfold Wop
  simp only [sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [ht]
  simp
end AdalyFormal.Round12.Noncancel.Boundary

                                                                                      
                                                                               
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Mass
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
variable {L : PeriodicLatticeExtent}

def rowZero (G : TowerGeom L) (e : Bond L) (he : e ∈ bondsLam G 0) : BIdx G :=
  ⟨⟨0,Nat.zero_lt_succ _⟩,e,he⟩
theorem Qfull_rowZero (G : TowerGeom L) (U : Cfg L)
    (e : Bond L) (he : e ∈ bondsLam G 0) (A : BondFnL2 L) :
    QfullOf G U A (rowZero G e he) = A e := by
  change (((G.ell : ℝ)^0)⁻¹) • (QlinB G U 0 A) e = _
  rw [QlinB_zero]
  simp
theorem collar_levelZero {ell M R k : ℕ} {S : Tower L}
    (hS : Admissible ell M R k S) (hell : 0 < ell) (e : Bond L)
    (ht : e ∈ bondsOm0 (geomOf ell k S))
    (h0 : e.1 ∉ S.Om 1) (h1 : periodicLatticeShift e.1 e.2 ∉ S.Om 1) :
    e ∈ bondsLam (geomOf ell k S) 0 := by
  by_contra h
  rcases endpoint_om1 hell hS e ht h with h | h
  · exact h0 h
  · exact h1 h
theorem leaf_mass_le (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ha : 0 ≤ a)
    (leaves : Finset (Bond L)) (hl : ∀ e ∈ leaves, e ∈ bondsLam G 0)
    (A : BondFnL2 L) :
    a * ∑ e ∈ leaves, ‖A e‖^2 ≤ ⟪A,MassFull G a (bondSectorOf G U) A⟫ := by
  classical
  let f : BIdx G → ℝ := fun p => a*(G.ell : ℝ)^(p.1 : ℕ)*‖QfullOf G U A p‖^2
  let r : {e // e ∈ leaves} → BIdx G := fun e => rowZero G e.val (hl e.val e.property)
  have hinj : Function.Injective r := by
    intro e e' h
    apply Subtype.ext
    exact congrArg (fun p : BIdx G => p.2.val) h
  have hterm (e : {e // e ∈ leaves}) : f (r e) = a * ‖A e.val‖^2 := by
    change a*(G.ell : ℝ)^0*‖QfullOf G U A (rowZero G e.val (hl e.val e.property))‖^2 = _
    rw [Qfull_rowZero]
    simp
  have hsum : (∑ e : {e // e ∈ leaves}, f (r e)) = a * ∑ e ∈ leaves, ‖A e‖^2 := by
    rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort leaves (fun e => ‖A e‖^2)
  have hn : ∀ p, 0 ≤ f p := fun p => mul_nonneg (mul_nonneg ha (by positivity)) (sq_nonneg _)
  rw [inner_MassFull]
  change _ ≤ ∑ p, f p
  rw [← hsum, ← Finset.sum_image (fun x _ y _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun p _ _ => hn p)
end AdalyFormal.Round12.Noncancel.Mass

                                                                      
                                                                  
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Star
open scoped RealInnerProductSpace

                                                          
def pairForm (c s : ℝ) (y z : ℂ) : ℝ :=
  c * Complex.normSq (y + z) + 2 * s * (star y * z).im
def tripleForm (c s : ℝ) (x y z : ℂ) : ℝ :=
  c * Complex.normSq (x + y + z) +
    2 * s * ((star x * y).im + (star x * z).im + (star y * z).im)
theorem tripleForm_zero_left (c s : ℝ) (y z : ℂ) :
    tripleForm c s 0 y z = pairForm c s y z := by
  simp [tripleForm, pairForm]
theorem tripleForm_zero_right (c s : ℝ) (x y : ℂ) :
    tripleForm c s x y 0 = pairForm c s x y := by
  simp [tripleForm, pairForm]
theorem pair_completion (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    Complex.normSq y + Complex.normSq z + pairForm c s y z =
      c * (Complex.normSq y + Complex.normSq z) +
        Complex.normSq (y + ((c : ℂ) - (s : ℂ) * Complex.I) * z) := by
  simp only [pairForm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im,
    congrArg (fun a : ℝ => a * z.re^2) hcs,
    congrArg (fun a : ℝ => a * z.im^2) hcs]
theorem pair_mass_lower (c s : ℝ) (hcs : c^2 + s^2 = 1) (y z : ℂ) :
    c * (Complex.normSq y + Complex.normSq z) ≤
      Complex.normSq y + Complex.normSq z + pairForm c s y z := by
  rw [pair_completion c s hcs]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)
section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

                                                                                             
end Kernel

                                                                              
                                                                   
                                                                                            
end AdalyFormal.Round12.Noncancel.Star

                                                                            
                                                                
namespace AdalyFormal.Round12.Noncancel.Plaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star

                                                                                       
def chargedMat (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, z; -star z, 0]
def realHol (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (c : ℂ) • 1
def imagHol (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(s : ℂ), 0; 0, -(s : ℂ)]
theorem chargedMat_add (y z : ℂ) : chargedMat (y+z) = chargedMat y + chargedMat z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chargedMat, add_comm]
theorem charged_inner (X : SuTwo) (z : ℂ)
    (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) = chargedMat z) :
    ⟪X, X⟫ = Complex.normSq z := by
  change hsInner X X = _
  rw [hsInner_entries, hX]
  simp [chargedMat, Complex.normSq_apply, Complex.mul_re]
  ring
theorem first_atom (c : ℝ) (z : ℂ) :
    (Matrix.trace (smulILM (chargedMat z) * smulILM (chargedMat z) *
      (realHol c - 1))).re = 2*(c-1)*Complex.normSq z := by
  simp [chargedMat, realHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Complex.normSq_apply]
  ring
theorem comm_atom (s : ℝ) (y z : ℂ) :
    (Matrix.trace (smulILM (smulILM (chargedMat y)) * smulILM (chargedMat z) *
      imagHol s)).re -
    (Matrix.trace (smulILM (smulILM (chargedMat z)) * smulILM (chargedMat y) *
      imagHol s)).re = 4*s*(star y*z).im := by
  simp [chargedMat, imagHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]
  ring
variable {L : PeriodicLatticeExtent}

theorem curl_atoms (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo) :
    curlMatLM U p A = a1LM U p A + a2LM p A + a3LM p A + a4LM U p A := by
  rw [curlMatLM_apply, a1LM_apply, a2LM_apply, a3LM_apply, a4LM_apply,
    ← sum_Aprime_eq_curl]
  change (AprimeXY A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeYZ U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeZW U A p : Matrix (Fin 2) (Fin 2) ℂ) +
    (AprimeWX A p : Matrix (Fin 2) (Fin 2) ℂ) = _
  abel
end AdalyFormal.Round12.Noncancel.Plaquette


namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

abbrev Fine (q R : ℕ) := scaleUp 2 1 (dilLu q R)
theorem seven_le_side {q : ℕ} (hq : 0 < q) (R : ℕ) (μ : Fin 3) :
    7 ≤ Fine q R μ + 1 := by
  rw [dil_fine_size hq]
  split_ifs <;> omega
def patchSite {q : ℕ} (hq : 0 < q) (R : ℕ) (v : Fin 3 → Fin 7) :
    PeriodicLatticeSite (Fine q R) :=
  fun μ => rightSite hq R μ + (Fin.castLE (seven_le_side hq R μ) (v μ) - 3)
theorem patchSite_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (patchSite hq R) := by
  intro v w h
  funext μ
  have he := congrFun h μ
  dsimp [patchSite] at he
  have he' := add_left_cancel he
  have he'' := sub_left_inj.mp he'
  exact Fin.ext (congrArg (fun a : Fin (Fine q R μ+1) => a.val) he'')
theorem castLE_add_one {n : ℕ} (hn : 7 ≤ n+1) (v : Fin 7) (hv : v.val < 6) :
    Fin.castLE hn (v + 1) = Fin.castLE hn v + (1 : Fin (n+1)) := by
  apply Fin.ext
  simp only [Fin.val_castLE, Fin.val_add, Fin.val_one']
  rw [Nat.mod_eq_of_lt (by omega : 1 < 7), Nat.mod_eq_of_lt (by omega : 1 < n+1),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < 7),
    Nat.mod_eq_of_lt (by omega : v.val + 1 < n+1)]
theorem patchSite_shift {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    periodicLatticeShift (patchSite hq R v) μ =
      patchSite hq R (Function.update v μ (v μ + 1)) := by
  funext ν
  by_cases h : ν = μ
  · subst ν
    simp only [periodicLatticeShift, Function.update_self, patchSite]
    rw [castLE_add_one _ _ hv]
    abel
  · simp [periodicLatticeShift, patchSite, Function.update_of_ne h]
def centerCoord : Fin 3 → Fin 7 := ![3,3,3]
theorem patchSite_center {q : ℕ} (hq : 0 < q) (R : ℕ) :
    patchSite hq R centerCoord = rightSite hq R := by
  funext μ
  have hc : Fin.castLE (seven_le_side hq R μ) (centerCoord μ) = (3 : Fin (Fine q R μ+1)) := by
    apply Fin.ext
    have hμ : 3 < Fine q R μ+1 := lt_of_lt_of_le (by decide) (seven_le_side hq R μ)
    have hv : (centerCoord μ).val = 3 := by fin_cases μ <;> rfl
    change (centerCoord μ).val = 3 % (Fine q R μ+1)
    rw [hv, Nat.mod_eq_of_lt hμ]
  simp [patchSite, hc]
def trialCoord : Fin 6 → (Fin 3 → Fin 7) :=
  ![![3,3,3], ![3,4,3], ![3,2,3], ![3,3,4], ![3,3,2], ![3,3,3]]
def trialDir : Fin 6 → Fin 3 := ![0,0,0,0,0,1]
def trialBond {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) : Bond (Fine q R) :=
  (patchSite hq R (trialCoord i), trialDir i)
theorem trialBond_injective {q : ℕ} (hq : 0 < q) (R : ℕ) :
    Function.Injective (trialBond hq R) := by
  intro i j h
  have hc := patchSite_injective hq R (congrArg Prod.fst h)
  have hd := congrArg Prod.snd h
  change trialDir i = trialDir j at hd
  fin_cases i <;> fin_cases j <;> simp_all [trialCoord, trialDir, funext_iff, Fin.forall_fin_succ]
def charged (z : ℂ) : SuTwo :=
  ⟨!![0,z;-star z,0], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    · simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩
theorem charged_norm (z : ℂ) : ‖charged z‖^2 = Complex.normSq z := by
  rw [← real_inner_self_eq_norm_sq]
  change hsInner (charged z) (charged z) = _
  rw [hsInner_self_entries]
  simp [charged]
def trialAmplitude : Fin 6 → ℂ :=
  ![1, -Complex.I/4, Complex.I/4, -Complex.I/4, Complex.I/4, -Complex.I/4]
def trialField {q : ℕ} (hq : 0 < q) (R : ℕ) : BondFnL2 (Fine q R) :=
  ∑ i : Fin 6, sing (trialBond hq R i) (charged (trialAmplitude i))
theorem trialField_apply {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R)) :
    trialField hq R e = ∑ i : Fin 6,
      if e = trialBond hq R i then charged (trialAmplitude i) else 0 := by
  simp [trialField, sing_apply]
theorem trialField_at {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialField hq R (trialBond hq R i) = charged (trialAmplitude i) := by
  rw [trialField_apply]
  simp only [(trialBond_injective hq R).eq_iff]
  simp
theorem trialField_support {q : ℕ} (hq : 0 < q) (R : ℕ) (e : Bond (Fine q R))
    (he : trialField hq R e ≠ 0) : ∃ i : Fin 6, e = trialBond hq R i := by
  by_contra h
  push Not at h
  apply he
  rw [trialField_apply]
  simp [h]
theorem trialField_norm {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ‖trialField hq R‖^2 = (21/16 : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hs : (∑ e : Bond (Fine q R), ‖trialField hq R e‖^2) =
      ∑ i : Fin 6, ‖trialField hq R (trialBond hq R i)‖^2 := by
    rw [← Finset.sum_image (f := fun e : Bond (Fine q R) => ‖trialField hq R e‖^2)
      (s := Finset.univ) (g := trialBond hq R)
      (fun i _ j _ h => trialBond_injective hq R h)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hz : trialField hq R e = 0 := by
      by_contra hn
      obtain ⟨i,rfl⟩ := trialField_support hq R e hn
      exact he (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp [hz]
  rw [hs]
  simp only [trialField_at, charged_norm]
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply]
end AdalyFormal.Round13.Trial
namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Boundary
open AdalyFormal.Round12.Noncancel.Mass
open Classical

theorem trial_sites {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (fun i : Fin 6 => (trialBond hq R i).1) =
      ![rightSite hq R, periodicLatticeShift (rightSite hq R) 1,
        periodicLatticeShiftBack (rightSite hq R) 1,
        periodicLatticeShift (rightSite hq R) 2,
        periodicLatticeShiftBack (rightSite hq R) 2, rightSite hq R] := by
  have hp1 := patchSite_shift hq R centerCoord 1 (by decide)
  have hp2 := patchSite_shift hq R centerCoord 2 (by decide)
  have hm1 := patchSite_shift hq R (trialCoord 2) 1 (by decide)
  have hm2 := patchSite_shift hq R (trialCoord 4) 2 (by decide)
  rw [patchSite_center] at hp1 hp2
  have hu1 : Function.update centerCoord 1 (centerCoord 1+1) = trialCoord 1 := by decide
  have hu2 : Function.update centerCoord 2 (centerCoord 2+1) = trialCoord 3 := by decide
  have hd1 : Function.update (trialCoord 2) 1 (trialCoord 2 1+1) = centerCoord := by decide
  have hd2 : Function.update (trialCoord 4) 2 (trialCoord 4 2+1) = centerCoord := by decide
  rw [hu1] at hp1
  rw [hu2] at hp2
  rw [hd1, patchSite_center] at hm1
  rw [hd2, patchSite_center] at hm2
  have hm1' := congrArg (fun z => periodicLatticeShiftBack z 1) hm1
  have hm2' := congrArg (fun z => periodicLatticeShiftBack z 2) hm2
  rw [periodicLatticeShiftBack_shift] at hm1' hm2'
  funext i
  fin_cases i
  · exact patchSite_center hq R
  · exact hp1.symm
  · exact hm1'
  · exact hp2.symm
  · exact hm2'
  · exact patchSite_center hq R
theorem trial_start_near {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (rightSite hq R) (trialBond hq R i).1 ≤ 1 := by
  have h := congrFun (trial_sites hq R) i
  rw [h]
  fin_cases i
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · exact pdist_shift_le _ _
  · exact pdist_shiftBack_le _ _
  · change pdist (rightSite hq R) (rightSite hq R) ≤ 1
    rw [AdalyFormal.StatementLaneR8.pdist_self]
    omega
theorem trial_start_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    ((trialBond hq R i).1 0).val = 12*(R*q)+12*q-1 := by
  have hv : trialCoord i 0 = (3 : Fin 7) := by fin_cases i <;> rfl
  have hc : Fin.castLE (seven_le_side hq R 0) (3 : Fin 7) = (3 : Fin (Fine q R 0+1)) := by
    apply Fin.ext
    change 3 = 3 % (Fine q R 0+1)
    rw [Nat.mod_eq_of_lt (by have := seven_le_side hq R 0; omega)]
  simp [trialBond, patchSite, hv, hc, rightSite]
theorem trial_touch {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    trialBond hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  apply Or.inl
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  rw [trial_start_zero]
  omega
theorem trial_collar {q R : ℕ} (hq : 0 < q) (hR18 : 18 ≤ R) (i : Fin 6) :
    (trialBond hq R i).1 ∉ (dilTower q R).Om 1 ∧
      periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2 ∉
        (dilTower q R).Om 1 := by
  have hr : 18*q ≤ R*q := Nat.mul_le_mul_right q hR18
  constructor
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [trial_start_zero]
    omega
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [dil_shift_zero hq, trial_start_zero]
    split_ifs
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
theorem trial_levelZero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) (i : Fin 6) :
    trialBond hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 :=
  collar_levelZero (dil_admissible hq hR) (by norm_num) _ (trial_touch hq R i)
    (trial_collar hq hR18 i).1 (trial_collar hq hR18 i).2
theorem trialField_mem {q : ℕ} (hq : 0 < q) (R : ℕ) :
    trialField hq R ∈ bondSupp (geomOf 2 1 (dilTower q R)) := by
  intro e he
  by_contra hn
  obtain ⟨i,rfl⟩ := trialField_support hq R e hn
  exact he (trial_touch hq R i)
def trialVector {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) := ⟨trialField hq R,trialField_mem hq R⟩
theorem trial_near_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 6) :
    pdist (periodicLatticeShift (rightSite hq R) 0) (trialBond hq R i).1 ≤ 2 ∧
    pdist (periodicLatticeShift (rightSite hq R) 0)
      (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2) ≤ 3 := by
  have h1 : pdist (periodicLatticeShift (rightSite hq R) 0) (rightSite hq R) ≤ 1 := by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]
    exact pdist_shift_le _ _
  have h2 := trial_start_near hq R i
  have ht := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (rightSite hq R) (trialBond hq R i).1
  have h3 := pdist_shift_le (trialBond hq R i).1 (trialBond hq R i).2
  have ht' := pdist_triangle (periodicLatticeShift (rightSite hq R) 0)
    (trialBond hq R i).1 (periodicLatticeShift (trialBond hq R i).1 (trialBond hq R i).2)
  omega
theorem trialField_hsupp {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ∀ e : Bond (Fine q R), trialField hq R e ≠ 0 →
      ∃ w : PeriodicLatticeSite (Fine q R), w ∉ (dilTower q R).Om 0 ∧ pdist e.1 w ≤ 2 := by
  intro e he
  obtain ⟨i,rfl⟩ := trialField_support hq R e he
  exact ⟨periodicLatticeShift (rightSite hq R) 0, (rightSite_bd hq R).hx', by
    rw [AdalyFormal.StatementLaneR8.pdist_comm]; exact (trial_near_exterior hq R i).1⟩
theorem trial_mass_upper {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ ≤ (21/16 : ℝ) := by
  have h := Mass_supp_le (dil_admissible hq hR) (by norm_num) (by nlinarith)
    U 1 (by norm_num) (trialField hq R) (trialField_hsupp hq R)
  simpa only [trialField_norm, one_mul] using h
theorem trial_mass_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) :
    ⟪trialField hq R, MassFull (geomOf 2 1 (dilTower q R)) 1
      (bondSectorOf (geomOf 2 1 (dilTower q R)) U) (trialField hq R)⟫ = (21/16 : ℝ) := by
  apply le_antisymm (trial_mass_upper hq hR hR18 U)
  have h := leaf_mass_le (geomOf 2 1 (dilTower q R)) U 1 (by norm_num)
    (Finset.univ.image (trialBond hq R)) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact trial_levelZero hq hR hR18 i) (trialField hq R)
  rw [Finset.sum_image (fun i _ j _ h => trialBond_injective hq R h)] at h
  simp only [one_mul, trialField_at, charged_norm] at h
  norm_num [Fin.sum_univ_succ, trialAmplitude, Complex.normSq_apply] at h ⊢
  exact h
theorem trial_T_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) : Tfull (geomOf 2 1 (dilTower q R)) U (trialField hq R) = 0 := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact Tfull_sing_zero_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2
theorem trial_W_eq {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (U : Cfg (Fine q R)) (a : ℝ) :
    Wop (geomOf 2 1 (dilTower q R)) U a (trialField hq R) = trialField hq R := by
  unfold trialField
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Wop_sing_near (dil_admissible hq hR) (d := 3) (by nlinarith)
    U a _ _ _ (rightSite_bd hq R).hx'
    (by have := (trial_near_exterior hq R i).1; omega) (trial_near_exterior hq R i).2
end AdalyFormal.Round13.Trial
namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open Classical

def stepCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ+1)
def backCoord (v : Fin 3 → Fin 7) (μ : Fin 3) := Function.update v μ (v μ-1)
theorem patchSite_back {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : 0 < (v μ).val) :
    periodicLatticeShiftBack (patchSite hq R v) μ = patchSite hq R (backCoord v μ) := by
  have hb : ((backCoord v μ) μ).val < 6 := by
    simp only [backCoord, Function.update_self]
    have hvlt := (v μ).isLt
    rw [Fin.val_sub]
    norm_num
    omega
  have h := patchSite_shift hq R (backCoord v μ) μ hb
  have hu : Function.update (backCoord v μ) μ ((backCoord v μ) μ+1) = v := by
    simp [backCoord]
  rw [hu] at h
  have hh := congrArg (fun z => periodicLatticeShiftBack z μ) h
  rw [periodicLatticeShiftBack_shift] at hh
  exact hh.symm
def d02 : PeriodicPlaquetteDirections := ⟨(0,2),by decide⟩
def d12 : PeriodicPlaquetteDirections := ⟨(1,2),by decide⟩
def trialPlaqPattern : Fin 19 → ((Fin 3 → Fin 7) × PeriodicPlaquetteDirections) :=
  ![(![2,3,3],d01), (![3,1,3],d01), (![3,2,2],d01), (![3,2,2],d02),
    (![3,2,3],d01), (![3,2,3],d02), (![3,2,4],d01), (![3,3,1],d02),
    (![3,3,2],d01), (![3,3,2],d02), (![3,3,2],d12), (![3,3,3],d01),
    (![3,3,3],d02), (![3,3,3],d12), (![3,3,4],d01), (![3,3,4],d02),
    (![3,4,2],d02), (![3,4,3],d01), (![3,4,3],d02)]
def trialPlaq {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) : PeriodicLatticePlaquette (Fine q R) :=
  (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2)
theorem trialPlaqPattern_injective : Function.Injective trialPlaqPattern := by decide
theorem trialPlaq_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (trialPlaq hq R) := by
  intro i j h
  apply trialPlaqPattern_injective
  exact Prod.ext (patchSite_injective hq R (congrArg Prod.fst h))
    (congrArg (fun p : PeriodicLatticePlaquette (Fine q R) => p.2) h)
theorem pattern_front : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    (d.1.1 = trialDir i ∨ d.1.2 = trialDir i) →
      ∃ k : Fin 19, trialPlaqPattern k = (trialCoord i,d) := by decide
theorem pattern_back1 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.1 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.2,d) := by decide
theorem pattern_back2 : ∀ (i : Fin 6) (d : PeriodicPlaquetteDirections),
    d.1.2 = trialDir i →
      ∃ k : Fin 19, trialPlaqPattern k = (backCoord (trialCoord i) d.1.1,d) := by decide
theorem trialCoord_positive (i : Fin 6) (μ : Fin 3) : 0 < (trialCoord i μ).val := by
  fin_cases i <;> fin_cases μ <;> decide
theorem front_mem {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i ∨ d.1.2 = trialDir i) :
    (patchSite hq R (trialCoord i),d) ∈ Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_front i d hd
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩
theorem back_mem1 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.1 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.2,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back1 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩
theorem back_mem2 {q : ℕ} (hq : 0 < q) (R : ℕ)
    (i : Fin 6) (d : PeriodicPlaquetteDirections) (hd : d.1.2 = trialDir i) :
    (periodicLatticeShiftBack (patchSite hq R (trialCoord i)) d.1.1,d) ∈
      Finset.univ.image (trialPlaq hq R) := by
  obtain ⟨k,hk⟩ := pattern_back2 i d hd
  rw [patchSite_back hq R _ _ (trialCoord_positive i _)]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _, by simp [trialPlaq, hk]⟩
theorem trial_plaq_zero_off {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R))
    (p : PeriodicLatticePlaquette (Fine q R)) (hp : p ∉ Finset.univ.image (trialPlaq hq R)) :
    contrib U (WithLp.ofLp (trialField hq R)) p = 0 := by
  have hc : curlValueCovariant U (WithLp.ofLp (trialField hq R)) p = 0 ∧
      bilPlaq U p (WithLp.ofLp (trialField hq R)) (WithLp.ofLp (trialField hq R)) = 0 := by
    apply curl_bil_zero
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.2 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem1 hq R i p.2 hd)
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inr hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      exact hp (by simpa only [← hx, Prod.mk.eta] using front_mem hq R i p.2 (Or.inl hd))
    · by_contra hn
      obtain ⟨i,hi⟩ := trialField_support hq R _ hn
      have hx := congrArg Prod.fst hi
      have hd := congrArg Prod.snd hi
      dsimp only [trialBond] at hx hd
      have hx' : p.1 = periodicLatticeShiftBack (patchSite hq R (trialCoord i)) p.2.1.1 := by
        rw [← hx, periodicLatticeShiftBack_shift]
      exact hp (by simpa only [← hx', Prod.mk.eta] using back_mem2 hq R i p.2 hd)
  unfold contrib
  rw [hc.1, hc.2]
  change ⟪(0 : SuTwo), 0⟫ + (1/2 : ℝ)*0 = 0
  simp
theorem trial_delta_sum {q : ℕ} (hq : 0 < q) (R : ℕ) (U : Cfg (Fine q R)) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM U Set.univ (trialField hq R)⟫ =
      ∑ i : Fin 19, contrib U (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) := by
  rw [delta_form_sum]
  change (∑ p, contrib U (WithLp.ofLp (trialField hq R)) p) = _
  rw [← Finset.sum_image (f := contrib U (WithLp.ofLp (trialField hq R)))
    (s := Finset.univ) (g := trialPlaq hq R)
    (fun i _ j _ h => trialPlaq_injective hq R h)]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => trial_plaq_zero_off hq R U p hp)
end AdalyFormal.Round13.Trial
namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

def quadForm (c s : ℝ) (x y z w : ℂ) : ℝ :=
  c * Complex.normSq (x+y+z+w) + 2*s*((star x*y).im+(star x*z).im+
    (star x*w).im+(star y*z).im+(star y*w).im+(star z*w).im)
theorem frozen_four_form {L : PeriodicLatticeExtent} (U : Cfg L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s : ℝ) (x y z w : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = chargedMat x) (h2 : a2LM p A = chargedMat y)
    (h3 : a3LM p A = chargedMat z) (h4 : a4LM U p A = chargedMat w) :
    contrib U A p = quadForm c s x y z w := by
  have hc : curlMatLM U p A = chargedMat (x+y+z+w) := by
    rw [curl_atoms, h1, h2, h3, h4, chargedMat_add, chargedMat_add, chargedMat_add]
  have hn : ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ =
      Complex.normSq (x+y+z+w) := charged_inner _ _ hc
  unfold contrib
  change ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ + _ = _
  rw [hn, bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4]
  rw [first_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom, comm_atom]
  unfold quadForm
  ring
def anchorCoord : Fin 3 → Fin 7 := ![4,3,3]
theorem star_anchor {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (rightSite hq R) 0 = patchSite hq R anchorCoord := by
  have h := patchSite_shift hq R centerCoord 0 (by decide)
  rw [patchSite_center] at h
  have he : Function.update centerCoord 0 (centerCoord 0+1) = anchorCoord := by decide
  simpa only [he] using h
def localStar (v : Fin 3 → Fin 7) (μ : Fin 3) : Prop :=
  μ ≠ 0 ∧ (v = anchorCoord ∨ stepCoord v μ = anchorCoord)
theorem rightStar_patch {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) (hv : (v μ).val < 6) :
    rightStar hq R t (patchSite hq R v,μ) =
      if localStar v μ then uθ t else 1 := by
  unfold rightStar starPath starLinks
  simp only [Set.mem_setOf_eq, star_anchor, patchSite_shift hq R v μ hv,
    (patchSite_injective hq R).eq_iff, localStar, stepCoord]
  split_ifs <;> rfl
def localField (v : Fin 3 → Fin 7) (μ : Fin 3) : SuTwo :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then charged (trialAmplitude i) else 0
theorem trialField_patch {q : ℕ} (hq : 0 < q) (R : ℕ)
    (v : Fin 3 → Fin 7) (μ : Fin 3) :
    trialField hq R (patchSite hq R v,μ) = localField v μ := by
  rw [trialField_apply]
  simp only [trialBond, Prod.mk.injEq, (patchSite_injective hq R).eq_iff, localField]
theorem charged_zero : charged 0 = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]
theorem charged_neg (z : ℂ) : -charged z = charged (-z) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged]
def isCurved (i : Fin 19) : Bool := decide (i = 4 ∨ i = 9 ∨ i = 11 ∨ i = 12)
theorem pattern_room (i : Fin 19) (μ : Fin 3) : ((trialPlaqPattern i).1 μ).val < 5 := by
  fin_cases i <;> fin_cases μ <;> decide
theorem pattern_base_flat (i : Fin 19) :
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1 ∧
    ¬ localStar (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2 := by
  revert i
  unfold localStar
  decide
theorem pattern_shift_links (i : Fin 19) :
    (localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2 ↔ isCurved i = true) ∧
    ¬ localStar (stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1 := by
  revert i
  unfold localStar
  decide
theorem trial_base_links {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.1) = 1 ∧
    rightStar hq R t ((trialPlaq hq R i).1,(trialPlaq hq R i).2.1.2) = 1 := by
  have hm := pattern_room i (trialPlaqPattern i).2.1.1
  have hn := pattern_room i (trialPlaqPattern i).2.1.2
  change rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.1) = 1 ∧
    rightStar hq R t (patchSite hq R (trialPlaqPattern i).1, (trialPlaqPattern i).2.1.2) = 1
  rw [rightStar_patch hq R t _ _ (by omega), rightStar_patch hq R t _ _ (by omega)]
  simp only [(pattern_base_flat i).1,(pattern_base_flat i).2,↓reduceIte,and_self]
theorem trial_holonomy {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    holonomyElem (rightStar hq R t) (trialPlaq hq R i) =
      if isCurved i then uθ t else 1 := by
  have hb := trial_base_links hq R t i
  unfold holonomyElem periodicPlaquetteHolonomy
  dsimp only
  rw [hb.1,hb.2]
  change 1 * rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.1,
        (trialPlaqPattern i).2.1.2) *
      (rightStar hq R t
      (periodicLatticeShift (patchSite hq R (trialPlaqPattern i).1) (trialPlaqPattern i).2.1.2,
        (trialPlaqPattern i).2.1.1))⁻¹ * 1⁻¹ = _
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega)]
  have h1 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.1)
      (trialPlaqPattern i).2.1.2).val < 6 := by
    fin_cases i <;> decide
  have h2 : ((stepCoord (trialPlaqPattern i).1 (trialPlaqPattern i).2.1.2)
      (trialPlaqPattern i).2.1.1).val < 6 := by
    fin_cases i <;> decide
  have he1 := rightStar_patch hq R t _ _ h1
  have he2 := rightStar_patch hq R t _ _ h2
  have hp := pattern_shift_links i
  dsimp only [stepCoord] at he1 he2 hp
  rw [he1,he2]
  simp only [hp.1, hp.2, ↓reduceIte, inv_one, mul_one, one_mul]
theorem uhalf_coe : ((uθ (Real.pi/2) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.I,0;0,-Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uθ,uMat,Complex.ofReal_div,Complex.exp_pi_div_two_mul_I,Complex.exp_neg]
theorem trial_hol_parts {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    reHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = realHol (if isCurved i then 0 else 1) ∧
    imHolonomy (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) = imagHol (if isCurved i then 1 else 0) := by
  have he := trial_holonomy hq R (Real.pi/2) i
  have hinv : ((holonomyElemInv (rightStar hq R (Real.pi/2)) (trialPlaq hq R i) : SU2m) :
      Matrix (Fin 2) (Fin 2) ℂ) = star ((holonomyElem (rightStar hq R (Real.pi/2))
        (trialPlaq hq R i) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) := rfl
  unfold reHolonomy imHolonomy
  rw [hinv,he]
  cases hc : isCurved i <;> simp only [hc, Bool.false_eq_true, ↓reduceIte, uhalf_coe]
  all_goals constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [realHol,imagHol,Matrix.star_apply,Matrix.ofNat_apply,Complex.ext_iff,Complex.div_re,Complex.div_im]
end AdalyFormal.Round13.Trial
namespace AdalyFormal.Round13.Trial
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Plaquette
open Classical

theorem charged_add (z w : ℂ) : charged (z+w) = charged z + charged w := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charged,add_comm]
def chargedHom : ℂ →+ SuTwo where
  toFun := charged
  map_zero' := charged_zero
  map_add' := charged_add
def localAmplitude (v : Fin 3 → Fin 7) (μ : Fin 3) : ℂ :=
  ∑ i : Fin 6, if v = trialCoord i ∧ μ = trialDir i then trialAmplitude i else 0
theorem localField_amplitude (v : Fin 3 → Fin 7) (μ : Fin 3) :
    localField v μ = charged (localAmplitude v μ) := by
  unfold localField localAmplitude
  change _ = chargedHom _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [chargedHom,charged_zero]
theorem trial_edge_values {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    trialField hq R ((trialPlaq hq R i).1, μ) = charged (localAmplitude v μ) ∧
    trialField hq R ((trialPlaq hq R i).1, ν) = charged (localAmplitude v ν) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 ν,μ) =
      charged (localAmplitude (stepCoord v ν) μ) ∧
    trialField hq R (periodicLatticeShift (trialPlaq hq R i).1 μ,ν) =
      charged (localAmplitude (stepCoord v μ) ν) := by
  dsimp only [trialPlaq]
  rw [patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.2; omega),
    patchSite_shift hq R _ _ (by have := pattern_room i (trialPlaqPattern i).2.1.1; omega)]
  simp only [trialField_patch,localField_amplitude,stepCoord,and_self]
theorem trial_atom_values {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) (i : Fin 19) :
    let v := (trialPlaqPattern i).1
    let μ := (trialPlaqPattern i).2.1.1
    let ν := (trialPlaqPattern i).2.1.2
    a1LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (-localAmplitude (stepCoord v ν) μ) ∧
    a2LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (-localAmplitude v ν) ∧
    a3LM (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) = chargedMat (localAmplitude v μ) ∧
    a4LM (rightStar hq R t) (trialPlaq hq R i) (WithLp.ofLp (trialField hq R)) =
      chargedMat (localAmplitude (stepCoord v μ) ν) := by
  have hb := trial_base_links hq R t i
  have he := trial_edge_values hq R i
  dsimp only [trialPlaq] at hb he
  dsimp only at ⊢
  constructor
  · rw [a1LM_apply]
    unfold AprimeZW
    dsimp only [trialPlaq]
    rw [hb.2, he.2.2.1, AdalyFormal.Balaban.CovariantOperators.RMap_one, LinearMap.id_apply, charged_neg]
    rfl
  constructor
  · rw [a2LM_apply]
    unfold AprimeWX
    dsimp only [trialPlaq]
    rw [he.2.1,charged_neg]
    rfl
  constructor
  · rw [a3LM_apply]
    unfold AprimeXY
    dsimp only [trialPlaq]
    rw [he.1]
    rfl
  · rw [a4LM_apply]
    unfold AprimeYZ
    dsimp only [trialPlaq]
    rw [hb.1,he.2.2.2,AdalyFormal.Balaban.CovariantOperators.RMap_one]
    rfl
def localQuad (i : Fin 19) : ℝ :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (stepCoord v ν) μ) (-localAmplitude v ν)
    (localAmplitude v μ) (localAmplitude (stepCoord v μ) ν)
theorem trial_contrib_quad {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 19) :
    contrib (rightStar hq R (Real.pi/2)) (WithLp.ofLp (trialField hq R)) (trialPlaq hq R i) =
      localQuad i := by
  have h := trial_atom_values hq R (Real.pi/2) i
  have hh := trial_hol_parts hq R i
  exact frozen_four_form _ _ _ _ _ _ _ _ _ hh.1 hh.2 h.1 h.2.1 h.2.2.1 h.2.2.2
def plaqNumerator : Fin 19 → ℝ := ![1,1,1,1,-8,1,1,1,1,-8,1,-16,-8,1,1,1,1,1,1]
def edgePattern (i : Fin 19) : Fin 4 → ((Fin 3 → Fin 7) × Fin 3) :=
  let v := (trialPlaqPattern i).1
  let μ := (trialPlaqPattern i).2.1.1
  let ν := (trialPlaqPattern i).2.1.2
  ![(v,μ),(stepCoord v μ,ν),(stepCoord v ν,μ),(v,ν)]
def edgeIndex : Fin 19 → Fin 4 → Option (Fin 6) :=
  ![![none,some 5,none,none], ![none,none,some 2,none],
    ![none,none,some 4,none], ![none,none,some 2,none],
    ![some 2,none,some 0,none], ![some 2,none,none,none],
    ![none,none,some 3,none], ![none,none,some 4,none],
    ![some 4,none,none,none], ![some 4,none,some 0,none],
    ![none,none,some 5,none], ![some 0,none,some 1,some 5],
    ![some 0,none,some 3,none], ![some 5,none,none,none],
    ![some 3,none,none,none], ![some 3,none,none,none],
    ![none,none,some 1,none], ![some 1,none,none,none], ![some 1,none,none,none]]
theorem edgeIndex_spec : ∀ (i : Fin 19) (k : Fin 4) (j : Fin 6),
    ((edgePattern i k).1 = trialCoord j ∧ (edgePattern i k).2 = trialDir j) ↔
      edgeIndex i k = some j := by decide
theorem localAmplitude_edge (i : Fin 19) (k : Fin 4) :
    localAmplitude (edgePattern i k).1 (edgePattern i k).2 =
      (edgeIndex i k).elim 0 trialAmplitude := by
  unfold localAmplitude
  simp only [edgeIndex_spec]
  cases h : edgeIndex i k <;> simp [h]
theorem localQuad_value (i : Fin 19) : localQuad i = plaqNumerator i / 16 := by
  change quadForm (if isCurved i then 0 else 1) (if isCurved i then 1 else 0)
    (-localAmplitude (edgePattern i 2).1 (edgePattern i 2).2)
    (-localAmplitude (edgePattern i 3).1 (edgePattern i 3).2)
    (localAmplitude (edgePattern i 0).1 (edgePattern i 0).2)
    (localAmplitude (edgePattern i 1).1 (edgePattern i 1).2) = _
  rw [localAmplitude_edge,localAmplitude_edge,localAmplitude_edge,localAmplitude_edge]
  fin_cases i
  · change quadForm 1 0 (-(0)) (-(0)) (0) (-Complex.I/4) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(1)) (-(0)) (Complex.I/4) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(-Complex.I/4)) (1) (0) = (-16 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 0 1 (-(-Complex.I/4)) (-(0)) (1) (0) = (-8 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(-Complex.I/4)) (-(0)) (0) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
  · change quadForm 1 0 (-(0)) (-(0)) (-Complex.I/4) (0) = (1 : ℝ)/16
    norm_num [quadForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im]
theorem trial_delta_value {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ⟪trialField hq R, AdalyFormal.StatementLaneR6.deltaKLocCLM
      (rightStar hq R (Real.pi/2)) Set.univ (trialField hq R)⟫ = (-25/16 : ℝ) := by
  rw [trial_delta_sum]
  simp only [trial_contrib_quad,localQuad_value]
  norm_num [plaqNumerator,Fin.sum_univ_succ]
theorem trial_carrier_energy {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ⟪trialVector hq R, vacA q R (rightStar hq R) 1 (Real.pi/2) (trialVector hq R)⟫ = (-1/4 : ℝ) := by
  rw [vacA_rightStar, BaseDataS.inner_Ginv]
  have hd : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Dpi (trialVector hq R)⟫ = (-25/16 : ℝ) := by
    have e := E0_Dpi_inner selAll (geomOf 2 1 (dilTower q R))
      (rightStar hq R (Real.pi/2)) 1 (trialVector hq R)
    refine e.trans ?_
    change ⟪Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R),
      DeltaS selAll (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2))
        (Wop (geomOf 2 1 (dilTower q R)) (rightStar hq R (Real.pi/2)) 1 (trialField hq R))⟫ = _
    rw [trial_W_eq hq hR hR18]
    exact trial_delta_value hq R
  have ht : (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).T (trialVector hq R) = 0 :=
    trial_T_zero hq hR hR18 _
  have hm : ⟪trialVector hq R,
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R (Real.pi/2)) 1 (dilLam q R))).Mass (trialVector hq R)⟫ = (21/16 : ℝ) := by
    change ⟪trialVector hq R, pE (geomOf 2 1 (dilTower q R))
      (MassFull (geomOf 2 1 (dilTower q R)) 1 (bondSectorOf (geomOf 2 1 (dilTower q R))
        (rightStar hq R (Real.pi/2))) (iE (geomOf 2 1 (dilTower q R)) (trialVector hq R)))⟫ = _
    rw [pE_inner_right]
    exact trial_mass_eq hq hR hR18 _
  rw [hd,ht,hm]
  norm_num
theorem rightStar_negative_halfpi :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
      ∃ w : TwistSpace q R,
        ⟪w, vacA q R (rightStar hq R) 1 (Real.pi/2) w⟫ < 0 := by
  intro q R hq hR hR18
  exact ⟨trialVector hq R, by rw [trial_carrier_energy hq hR hR18]; norm_num⟩
end AdalyFormal.Round13.Trial
namespace AdalyFormal.Round13.Assembly.R1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Kernel.Crossing

                                                                  
theorem p1 : P1 := AdalyFormal.Round13.Trial.rightStar_negative_halfpi
theorem cofinalNoCancellation_of_P2_P3 (h2 : P2) (h3 : P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_P1_P2_P3 p1 h2 h3
def CofinalP2P3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    (∀ t : ℝ, 0 < t → t < Real.pi/2 → ∀ x : TwistSpace (2^j) R,
      x ≠ 0 → AdalyFormal.Round12.Kernel.Actual.chargedCoordinate (2^j) R
        (rightSite (by positivity) R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA (2^j) R (rightStar (by positivity) R) 1 t x⟫) ∧
    (∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u)
theorem cofinalPhysical_of_cofinalP2P3 (h : CofinalP2P3) : CofinalPhysicalInputs := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,hp,hd⟩ := hRs R₀
  exact ⟨R,hR0,hR,hR18,p1 (by positivity) hR hR18,hp,hd⟩
theorem cofinalNoCancellation_of_cofinalP2P3 (h : CofinalP2P3) :
    AdalyFormal.Round10.Assembly.R4.CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_cofinalPhysical (cofinalPhysical_of_cofinalP2P3 h)
end AdalyFormal.Round13.Assembly.R1
namespace AdalyFormal.Round13.Assembly.R2
open AdalyFormal.Round13.Assembly.R1
open AdalyFormal.Round2.Guarded.Pin (GoalNeg2)

                                                                            
theorem goalNeg2_of_P2_P3 (h2 : P2) (h3 : P3) : GoalNeg2 :=
  AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (cofinalNoCancellation_of_P2_P3 h2 h3)
theorem goalNeg2_of_cofinalP2P3 (h : CofinalP2P3) : GoalNeg2 :=
  AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation
    (cofinalNoCancellation_of_cofinalP2P3 h)
end AdalyFormal.Round13.Assembly.R2
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
noncomputable section
namespace AdalyFormal.Round12.Noncancel.Star
open scoped RealInnerProductSpace

                                                          
section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

                                                                                             
end Kernel

                                                                              
                                                                   
                                                                                            
end AdalyFormal.Round12.Noncancel.Star

                                                                            
                                                                
namespace AdalyFormal.Round12.Noncancel.Plaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star

                                                                                       
variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round12.Noncancel.Plaquette

                                                                                
                                                                            
                                       
namespace AdalyFormal.Round12.Noncancel.FullPlaquette
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.Plaquette

                                                                               
def lieMat (h : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(h : ℂ)*Complex.I, z; -star z, -(h : ℂ)*Complex.I]
theorem lieMat_add (h k : ℝ) (y z : ℂ) :
    lieMat (h+k) (y+z) = lieMat h y + lieMat k z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lieMat, add_mul, add_comm]
theorem lieMat_coordinates (X : SuTwo) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) =
      lieMat ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
        ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  have h00 := re_entry00_eq_zero X
  have h10 := entry_skew X.property.1 0 1
  have h11 := entry11_eq_neg_entry00 X
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [lieMat, h00]
  · simp [lieMat]
  · simpa [lieMat] using h10
  · apply Complex.ext <;> simp [lieMat, h11, h00]
theorem full_inner (X : SuTwo) (h : ℝ) (z : ℂ)
    (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) = lieMat h z) :
    ⟪X,X⟫ = Complex.normSq z + h^2 := by
  change hsInner X X = _
  rw [hsInner_self_entries,hX]
  simp [lieMat, add_comm]
theorem full_first_atom (c h : ℝ) (z : ℂ) :
    (Matrix.trace (smulILM (lieMat h z) * smulILM (lieMat h z) *
      (realHol c - 1))).re = 2*(c-1)*(Complex.normSq z+h^2) := by
  simp [lieMat, realHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two, Complex.normSq_apply]
  ring
theorem full_comm_atom (s h k : ℝ) (y z : ℂ) :
    (Matrix.trace (smulILM (smulILM (lieMat h y)) * smulILM (lieMat k z) *
      imagHol s)).re -
    (Matrix.trace (smulILM (smulILM (lieMat k z)) * smulILM (lieMat h y) *
      imagHol s)).re = 4*s*(star y*z).im := by
  simp [lieMat, imagHol, smulILM_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fin.sum_univ_two]
  ring
variable {L : PeriodicLatticeExtent}

                                                                                     
theorem frozen_full_three_right
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L)
    (p : PeriodicLatticePlaquette L) (A : Bond L → SuTwo)
    (c s h k l : ℝ) (x y z : ℂ)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p A = lieMat h x) (h2 : a2LM p A = lieMat k y)
    (h3 : a3LM p A = lieMat l z) (h4 : a4LM U p A = 0) :
    ⟪curlValueCovariant U A p, curlValueCovariant U A p⟫ +
      (1/2 : ℝ) * bilPlaq U p A A = tripleForm c s x y z + c*(h+k+l)^2 := by
  have hc : curlMatLM U p A = lieMat (h+k+l) (x+y+z) := by
    rw [curl_atoms,h1,h2,h3,h4,add_zero,lieMat_add,lieMat_add]
  have hn := full_inner (curlValueCovariant U A p) (h+k+l) (x+y+z) hc
  rw [hn,bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,hr,hi,hc,h1,h2,h3,h4,
    map_zero,mul_zero,zero_mul,Matrix.trace_zero,Complex.zero_re,sub_zero,add_zero]
  rw [full_first_atom,full_comm_atom,full_comm_atom,full_comm_atom]
  unfold tripleForm
  ring
theorem full_pair_mass_lower (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    c*(Complex.normSq y+k^2 + (Complex.normSq z+l^2)) ≤
      Complex.normSq y+k^2 + (Complex.normSq z+l^2) +
        pairForm c s y z + c*(h+k+l)^2 := by
  have hp := pair_mass_lower c s hcs y z
  have hn := mul_nonneg hc (sq_nonneg (h+k+l))
  have hk := mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg k)
  have hl := mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg l)
  nlinarith
end AdalyFormal.Round12.Noncancel.FullPlaquette

namespace AdalyFormal.Round12.Noncancel.Mass
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round12.Noncancel.Mass

namespace AdalyFormal.Round12.Noncancel.Boundary
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Guarded
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack gradCovariantAdjointValue)
variable {L : PeriodicLatticeExtent}

                                                                         
                                                                               
end AdalyFormal.Round12.Noncancel.Boundary

namespace AdalyFormal.Round13.Positivity
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.FullPlaquette
variable {L : PeriodicLatticeExtent}

                                                             
def plaqEnergy (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L) : ℝ :=
  ⟪curlValueCovariant U (WithLp.ofLp A) p, curlValueCovariant U (WithLp.ofLp A) p⟫ +
    (1/2 : ℝ) * bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A)
theorem delta_form_sum_set (U : Cfg L) (S : Set (PeriodicLatticePlaquette L))
    (A : BondFnL2 L) :
    ⟪A, deltaKLocCLM U S A⟫ = ∑ p, if p ∈ S then plaqEnergy U A p else 0 := by
  classical
  rw [inner_deltaKLocCLM]
  have h1 : ⟪plaqMask S (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A),
      plaqMask S (AdalyFormal.Balaban.DeltaKFull.curlCovariantLM_L2 U A)⟫ =
      ∑ p, if p ∈ S then
        ⟪curlValueCovariant U (WithLp.ofLp A) p, curlValueCovariant U (WithLp.ofLp A) p⟫ else 0 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p _
    simp only [plaqMask_apply]
    split_ifs
    · rfl
    · simp
  have h2 : deltaPrimeBilL2NormLoc U S A A =
      (1/2 : ℝ) * ∑ p, if p ∈ S then bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A) else 0 := by
    change deltaPrimeBilNormLoc U S (WithLp.ofLp A) (WithLp.ofLp A) = _
    simp only [deltaPrimeBilNormLoc, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.flip_apply, smul_eq_mul, deltaPrimeBilRawLoc_apply]
    ring
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ S <;> simp [hp, plaqEnergy]
theorem plaqEnergy_nonneg (U : Cfg L) (A : BondFnL2 L) (p : PeriodicLatticePlaquette L)
    (hr : reHolonomy U p = 1) (hi : imHolonomy U p = 0) :
    0 ≤ plaqEnergy U A p := by
  have hb : bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp A) = 0 := by
    rw [bilPlaq_atoms, hr, hi]
    simp
  simp only [plaqEnergy, hb, mul_zero, add_zero]
  exact real_inner_self_nonneg
open Classical in
def omittedEnergy (P : IngrBParams) (x : ↥(bondSupp P.G)) : ℝ :=
  ∑ p, if p ∈ plaqIn P.G.Om0 then 0 else
    plaqEnergy P.U (Wop P.G P.U P.a (iE P.G x)) p
theorem carrier_form_split (P : IngrBParams) (x : ↥(bondSupp P.G)) :
    ⟪x, (dataS selAll selAll P).Ginv x⟫ =
      ⟪x, (dataS selIn selIn P).Ginv x⟫ + omittedEnergy P x := by
  classical
  have hd : ⟪x, (dataS selAll selAll P).Dpi x⟫ =
      ⟪x, (dataS selIn selIn P).Dpi x⟫ + omittedEnergy P x := by
    change ⟪x, ((pE P.G).comp ((DpiFullS selAll P.G P.U P.a).comp (iE P.G))) x⟫ =
      ⟪x, ((pE P.G).comp ((DpiFullS selIn P.G P.U P.a).comp (iE P.G))) x⟫ + _
    rw [E0_Dpi_inner, E0_Dpi_inner]
    simp only [DeltaS, selAll, selIn, delta_form_sum_set, Set.mem_univ, if_true]
    unfold omittedEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p ∈ plaqIn P.G.Om0 <;> simp [hp]
  rw [BaseDataS.inner_Ginv, BaseDataS.inner_Ginv, hd]
  have ht : (dataS selAll selAll P).T = (dataS selIn selIn P).T := rfl
  have hm : (dataS selAll selAll P).Mass = (dataS selIn selIn P).Mass := rfl
  rw [ht, hm]
  ring
theorem localized_Dpi_nonneg (P : IngrBParams) (x : ↥(bondSupp P.G))
    (hr : ∀ p ∈ plaqIn P.G.Om0, reHolonomy P.U p = 1)
    (hi : ∀ p ∈ plaqIn P.G.Om0, imHolonomy P.U p = 0) :
    0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫ := by
  classical
  change 0 ≤ ⟪x, ((pE P.G).comp ((DpiFullS selIn P.G P.U P.a).comp (iE P.G))) x⟫
  rw [E0_Dpi_inner]
  simp only [DeltaS, selIn, delta_form_sum_set]
  apply Finset.sum_nonneg
  intro p _
  split_ifs with hp
  · exact plaqEnergy_nonneg _ _ _ (hr p hp) (hi p hp)
  · exact le_rfl
theorem carrier_ge_scaled_local (P : IngrBParams) (x : ↥(bondSupp P.G))
    (c leaves : ℝ) (hc : c ≤ 1)
    (hd : 0 ≤ ⟪x, (dataS selIn selIn P).Dpi x⟫)
    (hl : leaves ≤ ⟪x, (dataS selIn selIn P).Mass x⟫)
    (ho : -(1-c)*leaves ≤ omittedEnergy P x) :
    c * ⟪x, (dataS selIn selIn P).Ginv x⟫ ≤
      ⟪x, (dataS selAll selAll P).Ginv x⟫ := by
  have hm : leaves ≤ ⟪x, (dataS selIn selIn P).Ginv x⟫ := by
    rw [BaseDataS.inner_Ginv]
    have ht : 0 ≤ ‖(dataS selIn selIn P).T x‖^2 := sq_nonneg _
    linarith
  have habs := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hc)
  rw [carrier_form_split]
  nlinarith
theorem full_pair_loss_bound (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤
      pairForm c s y z + c*(h+k+l)^2 := by
  have hp := full_pair_mass_lower c s h k l y z hc hc1 hcs
  nlinarith
set_option pp.fullNames true
end AdalyFormal.Round13.Positivity

namespace AdalyFormal.Round13.Positivity
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Round12.Noncancel.Star
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round12.Noncancel.Plaquette
variable {L : PeriodicLatticeExtent}

                                                                                 
theorem plaqEnergy_congr_field (U : Cfg L) (A B : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (h : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = B e) :
    plaqEnergy U A p = plaqEnergy U B p := by
  have h1 := h _ ((edge_mem p _).mpr (Or.inl rfl))
  have h2 := h _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl)))
  have h3 := h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 := h _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have hc : curlValueCovariant U (WithLp.ofLp A) p =
      curlValueCovariant U (WithLp.ofLp B) p := by
    unfold curlValueCovariant
    rw [h1,h2,h3,h4]
  have ha1 : a1LM U p (WithLp.ofLp A) = a1LM U p (WithLp.ofLp B) := by
    simp only [a1LM_apply, AprimeZW, h3]
  have ha2 : a2LM p (WithLp.ofLp A) = a2LM p (WithLp.ofLp B) := by
    simp only [a2LM_apply, AprimeWX, h4]
  have ha3 : a3LM p (WithLp.ofLp A) = a3LM p (WithLp.ofLp B) := by
    simp only [a3LM_apply, AprimeXY, h1]
  have ha4 : a4LM U p (WithLp.ofLp A) = a4LM U p (WithLp.ofLp B) := by
    simp only [a4LM_apply, AprimeYZ, h2]
  unfold plaqEnergy
  rw [hc, bilPlaq_atoms, bilPlaq_atoms]
  simp only [b1LM,b2LM,b3LM,b4LM,LinearMap.comp_apply,
    ha1,ha2,ha3,ha4,curlMatLM_apply,hc]
theorem omittedEnergy_eq_raw (P : IngrBParams) {M R : ℕ}
    (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) :
    omittedEnergy P x = ∑ p, if p ∈ plaqIn P.G.Om0 then 0 else
      plaqEnergy P.U (iE P.G x) p := by
  unfold omittedEnergy
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with hp
  · rfl
  · apply plaqEnergy_congr_field
    intro e he
    exact AdalyFormal.Round12.Noncancel.Boundary.Wop_eq_on_omitted hS h4 P.U P.a _ hp he
theorem frozen_right_zero_first_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat h 0)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat k y)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat l z)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p := by
  unfold plaqEnergy
  rw [frozen_full_three_right U p _ c s h k l 0 y z hr hi h1 h2 h3 h4,
    tripleForm_zero_left]
  exact full_pair_loss_bound c s h k l y z hc hc1 hcs
theorem frozen_right_zero_third_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (c s h k l : ℝ) (y z : ℂ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcs : c^2+s^2=1)
    (hr : reHolonomy U p = realHol c) (hi : imHolonomy U p = imagHol s)
    (h1 : a1LM U p (WithLp.ofLp A) = lieMat k y)
    (h2 : a2LM p (WithLp.ofLp A) = lieMat l z)
    (h3 : a3LM p (WithLp.ofLp A) = lieMat h 0)
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-c)*(Complex.normSq y+k^2+(Complex.normSq z+l^2)) ≤ plaqEnergy U A p := by
  unfold plaqEnergy
  rw [frozen_full_three_right U p _ c s k l h y z 0 hr hi h1 h2 h3 h4,
    tripleForm_zero_right]
  convert full_pair_loss_bound c s h k l y z hc hc1 hcs using 1
  ring
theorem omitted_loss_of_injective_arms {ι : Type*} [Fintype ι]
    (P : IngrBParams) {M R : ℕ} (hS : Admissible P.ell M R P.k P.S) (h4 : 4 ≤ R*M)
    (x : ↥(bondSupp P.G)) (c : ℝ)
    (arm : ι → PeriodicLatticePlaquette P.Lf) (ha : Function.Injective arm)
    (hout : ∀ i, arm i ∉ plaqIn P.G.Om0) (budget : ι → ℝ)
    (hbad : ∀ i, -(1-c)*budget i ≤ plaqEnergy P.U (iE P.G x) (arm i))
    (hgood : ∀ p, p ∉ plaqIn P.G.Om0 → (∀ i, p ≠ arm i) →
      0 ≤ plaqEnergy P.U (iE P.G x) p) :
    -(1-c)*(∑ i, budget i) ≤ omittedEnergy P x := by
  rw [omittedEnergy_eq_raw P hS h4 x, Finset.mul_sum]
  let f : PeriodicLatticePlaquette P.Lf → ℝ := fun p =>
    if p ∈ plaqIn P.G.Om0 then 0 else plaqEnergy P.U (iE P.G x) p
  have hb : (∑ i, -(1-c)*budget i) ≤ ∑ i, f (arm i) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [f, if_neg (hout i)] using hbad i
  apply hb.trans
  rw [← Finset.sum_image (fun i _ j _ h => ha h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro p _ hp
  change 0 ≤ if p ∈ plaqIn P.G.Om0 then 0 else plaqEnergy P.U (iE P.G x) p
  split_ifs with hin
  · exact le_rfl
  · apply hgood p hin
    intro i heq
    apply hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i,heq.symm⟩
set_option pp.fullNames true
end AdalyFormal.Round13.Positivity

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (SU2m)
variable {L : PeriodicLatticeExtent}

end AdalyFormal.Round9.Guarded.QualitativeR2

namespace AdalyFormal.Round12.Noncancel.Path
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.D1Literal
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnM AnFam anM_uMat)
variable {L : PeriodicLatticeExtent}

                                                                                                
end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round2.Guarded.Pin

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

                                                              
section Selectors
variable (sD sJ : PlaqSel)

section Ops
variable (P : IngrBParams)

end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin


namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin

open Classical

end AdalyFormal.Round4.Guarded.RefuteR1


namespace AdalyFormal.Round5.Guarded.IVTR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

end AdalyFormal.Round5.Guarded.IVTR1


namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1

open Classical

end AdalyFormal.Round5.Guarded.IVTR2


namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2

open Classical

end AdalyFormal.Round9.Guarded.Qualitative



namespace AdalyFormal.Round3.Guarded.RefuteR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
end AdalyFormal.Round3.Guarded.RefuteR2

namespace AdalyFormal.Round4.Guarded.RefuteR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round3.Guarded.RefuteR2 (zero_coord_le_pdist)
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')
end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.D1Literal (BdPt)
end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.RightFamily
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2 (AnFam)
open AdalyFormal.Round12.Noncancel.Path

                                                                                                        
end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round13.Positivity.Leaves
open Classical
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.Mass

                                                                                    
def leaf {q : ℕ} (hq : 0 < q) (R : ℕ) : Fin 8 → Bond (scaleUp 2 1 (dilLu q R)) :=
  ![(periodicLatticeShift (rightSite hq R) 1,0),
    (periodicLatticeShiftBack (rightSite hq R) 1,0),
    (periodicLatticeShift (rightSite hq R) 2,0),
    (periodicLatticeShiftBack (rightSite hq R) 2,0),
    (rightSite hq R,1),
    (periodicLatticeShiftBack (rightSite hq R) 1,1),
    (rightSite hq R,2),
    (periodicLatticeShiftBack (rightSite hq R) 2,2)]
def code {L : PeriodicLatticeExtent} (e : Bond L) : ℕ × ℕ × ℕ :=
  (e.2.val,(e.1 1).val,(e.1 2).val)
private theorem transverse_sizes {q : ℕ} (hq : 0 < q) (R : ℕ) :
    (scaleUp 2 1 (dilLu q R) 1 + 1 = 8*q) ∧
    (scaleUp 2 1 (dilLu q R) 2 + 1 = 8*q) := by
  constructor <;> simp [dil_fine_size hq]
private theorem right_coord {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ((rightSite hq R) 1).val = 0 ∧ ((rightSite hq R) 2).val = 0 := by
  simp [rightSite]
theorem leaf_code {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    code (leaf hq R i) =
      ![(0,1,0),(0,8*q-1,0),(0,0,1),(0,0,8*q-1),
        (1,0,0),(1,8*q-1,0),(2,0,0),(2,0,8*q-1)] i := by
  have hs := transverse_sizes hq R
  have hz := right_coord hq R
  fin_cases i <;>
    simp [leaf,code,periodicLatticeShift,periodicLatticeShiftBack,
      Fin.val_add,Fin.val_sub,hz.1,hz.2,hs.1,hs.2,
      Nat.mod_eq_of_lt (show 1 < 8*q by omega),
      Nat.mod_eq_of_lt (show 8*q-1 < 8*q by omega)]
theorem leaf_injective {q : ℕ} (hq : 0 < q) (R : ℕ) : Function.Injective (leaf hq R) := by
  intro i j h
  have hc := congrArg code h
  rw [leaf_code hq R i,leaf_code hq R j] at hc
  clear h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num at hc
  all_goals omega
theorem leaf_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    (((leaf hq R i).1) 0).val = 12*(R*q)+12*q-1 := by
  fin_cases i <;> simp [leaf,periodicLatticeShift,periodicLatticeShiftBack,rightSite]
theorem leaf_end_zero_coord {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    ((periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2) 0).val =
      if i.val < 4 then 12*(R*q)+12*q else 12*(R*q)+12*q-1 := by
  rw [dil_shift_zero hq R, leaf_zero_coord]
  have hf : (12*(R*q)+12*q-1+1) % (12*(R*q)+16*q) = 12*(R*q)+12*q := by
    rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt (by omega)]
  fin_cases i <;> simp [leaf,hf]
theorem leaf_collar {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R) (i : Fin 8) :
    (leaf hq R i).1 ∉ (dilTower q R).Om 1 ∧
    periodicLatticeShift (leaf hq R i).1 (leaf hq R i).2 ∉ (dilTower q R).Om 1 := by
  have hprod : 1 ≤ R*q := by nlinarith
  constructor
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [leaf_zero_coord]
    omega
  · change ¬ (2*(R*q)+4*q ≤ _ ∧ _ < 10*(R*q)+12*q)
    rw [leaf_end_zero_coord]
    split_ifs <;> omega
theorem leaf_touching {q : ℕ} (hq : 0 < q) (R : ℕ) (i : Fin 8) :
    leaf hq R i ∈ bondsOm0 (geomOf 2 1 (dilTower q R)) := by
  apply Or.inl
  change 4*q ≤ _ ∧ _ < 12*(R*q)+12*q
  rw [leaf_zero_coord]
  omega
theorem leaf_level_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (i : Fin 8) : leaf hq R i ∈ bondsLam (geomOf 2 1 (dilTower q R)) 0 :=
  collar_levelZero (dil_admissible hq hR) (by norm_num) _
    (leaf_touching hq R i) (leaf_collar hq hR1 i).1 (leaf_collar hq hR1 i).2
def leafSet {q : ℕ} (hq : 0 < q) (R : ℕ) : Finset (Bond (scaleUp 2 1 (dilLu q R))) :=
  Finset.univ.image (leaf hq R)
open scoped RealInnerProductSpace in
/-- Unconditional physical eight-leaf mass extraction for this exact right star's
geometry, with an arbitrary background and an arbitrary full fine input. -/
theorem eight_leaf_mass {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR1 : 1 ≤ R)
    (U : Cfg (scaleUp 2 1 (dilLu q R)))
    (A : AdalyFormal.Balaban.CovariantOperators.BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i : Fin 8, ‖A (leaf hq R i)‖^2) ≤
      ⟪A,MassFull (geomOf 2 1 (dilTower q R)) 1
        (bondSectorOf (geomOf 2 1 (dilTower q R)) U) A⟫ := by
  have hh := leaf_mass_le (geomOf 2 1 (dilTower q R)) U 1 (by norm_num)
    (leafSet hq R) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
      exact leaf_level_zero hq hR hR1 i) A
  simpa only [one_mul,leafSet,
    Finset.sum_image (fun i _ j _ h => leaf_injective hq R h)] using hh
set_option pp.fullNames true
end AdalyFormal.Round13.Positivity.Leaves

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

                                                                            
def exteriorPair (Om : Set (PeriodicLatticeSite L)) (z : PeriodicLatticeSite L) : Prop :=
  z ∉ Om ∧ periodicLatticeShift z 0 ∉ Om
theorem exteriorPair_shift {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShift z ν) := by
  constructor
  · exact fun h => hz.1 ((hb.trans z ν hν).mp h)
  · rw [shift_comm z hν]
    exact fun h => hz.2 ((hb.trans _ ν hν).mp h)
theorem exteriorPair_back {Om : Set (PeriodicLatticeSite L)} {x z : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hz : exteriorPair Om z) {ν : Fin 3} (hν : ν ≠ 0) :
    exteriorPair Om (periodicLatticeShiftBack z ν) := by
  have hz0 : periodicLatticeShiftBack z ν ∉ Om := by
    intro h
    exact hz.1 (by simpa only [periodicLatticeShift_shiftBack] using
      (hb.trans _ ν hν).mpr h)
  refine ⟨hz0, ?_⟩
  intro h
  have hh := (hb.trans _ ν hν).mpr h
  rw [shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack] at hh
  exact hz.2 hh
theorem exteriorPair_vertices {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (p : PeriodicLatticePlaquette L) (hp : exteriorPair Om p.1) :
    ∀ e ∈ periodicPlaquetteBoundaryEdges p,
      e.1 ∉ Om ∧ periodicLatticeShift e.1 e.2 ∉ Om := by
  have hν : p.2.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) p.2.2)
  have hμ : periodicLatticeShift p.1 p.2.1.1 ∉ Om := by
    by_cases h : p.2.1.1 = 0
    · simpa only [h] using hp.2
    · exact (exteriorPair_shift hb hp h).1
  have hμν : periodicLatticeShift (periodicLatticeShift p.1 p.2.1.1) p.2.1.2 ∉ Om :=
    fun h => hμ ((hb.trans _ _ hν).mp h)
  have hν' := (exteriorPair_shift hb hp hν).1
  intro e he
  rcases (edge_mem p e).mp he with rfl | rfl | rfl | rfl
  · exact ⟨hp.1,hμ⟩
  · exact ⟨hμ,hμν⟩
  · refine ⟨hν', ?_⟩
    rw [shift_comm _ (ne_of_gt p.2.2)]
    exact hμν
  · exact ⟨hp.1,hν'⟩
theorem star_edge_cases {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ Om)
    (p : PeriodicLatticePlaquette L) (e : Bond L)
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hs : e ∈ starLinks (periodicLatticeShift x 0)) :
    (∃ ν : {ν : Fin 3 // 0 < ν}, p = P1 x ν ∨ p = P2 x ν) ∨
      exteriorPair Om p.1 := by
  have hx : exteriorPair Om (periodicLatticeShift x 0) := ⟨hb.hx',hf⟩
  have hsites : e.1 = periodicLatticeShift x 0 ∨
      e.1 = periodicLatticeShiftBack (periodicLatticeShift x 0) e.2 := by
    rcases hs.2 with h | h
    · exact Or.inl h
    · right
      have := congrArg (fun z => periodicLatticeShiftBack z e.2) h
      simpa only [periodicLatticeShiftBack_shift] using this
  have hext : exteriorPair Om e.1 := by
    rcases hsites with h | h
    · rw [h]; exact hx
    · rw [h]; exact exteriorPair_back hb hx hs.1
  rcases (edge_mem p e).mp he with he | he | he | he
  · right
    have hsite := congrArg Prod.fst he
    simpa only [hsite] using hext
  · have hsite := congrArg Prod.fst he
    have hdir := congrArg Prod.snd he
    by_cases hμ : p.2.1.1 = 0
    · left
      have hν : 0 < p.2.1.2 := lt_of_le_of_lt (Fin.zero_le _) p.2.2
      refine ⟨⟨p.2.1.2,hν⟩, ?_⟩
      have hh : periodicLatticeShift p.1 0 = e.1 := by simpa only [hμ] using hsite.symm
      rcases hsites with hx | hx
      · left
        have hbase : p.1 = x := by
          have := congrArg (fun z => periodicLatticeShiftBack z 0) (hh.trans hx)
          simpa only [periodicLatticeShiftBack_shift] using this
        apply Prod.ext hbase
        apply Subtype.ext
        exact Prod.ext hμ rfl
      · right
        have hscomm : periodicLatticeShiftBack (periodicLatticeShift x 0) p.2.1.2 =
            periodicLatticeShift (periodicLatticeShiftBack x p.2.1.2) 0 := by
          have hh : periodicLatticeShift
              (periodicLatticeShift (periodicLatticeShiftBack x p.2.1.2) 0) p.2.1.2 =
              periodicLatticeShift x 0 := by
            rw [shift_comm _ (Ne.symm (ne_of_gt hν)), periodicLatticeShift_shiftBack]
          have := congrArg (fun z => periodicLatticeShiftBack z p.2.1.2) hh
          simpa only [periodicLatticeShiftBack_shift] using this.symm
        rw [hdir,hscomm] at hx
        have hbase : p.1 = periodicLatticeShiftBack x p.2.1.2 := by
          have := congrArg (fun z => periodicLatticeShiftBack z 0) (hh.trans hx)
          simpa only [periodicLatticeShiftBack_shift] using this
        apply Prod.ext hbase
        apply Subtype.ext
        exact Prod.ext hμ rfl
    · right
      have hh := exteriorPair_back hb hext hμ
      simpa only [hsite,periodicLatticeShiftBack_shift] using hh
  · right
    have hsite := congrArg Prod.fst he
    have hν : p.2.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) p.2.2)
    have hh := exteriorPair_back hb hext hν
    simpa only [hsite,periodicLatticeShiftBack_shift] using hh
  · right
    have hsite := congrArg Prod.fst he
    simpa only [hsite] using hext
end AdalyFormal.Round13.Positivity.Physical
namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

theorem plaqEnergy_zero_input (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hz : ∀ e ∈ periodicPlaquetteBoundaryEdges p, A e = 0) : plaqEnergy U A p = 0 := by
  rw [plaqEnergy_congr_field U A 0 p (by simpa using hz)]
  simp [plaqEnergy, curlValueCovariant]
theorem hol_flat_components (U : Cfg L) (p : PeriodicLatticePlaquette L)
    (h : holonomyElem U p = 1) : reHolonomy U p = 1 ∧ imHolonomy U p = 0 := by
  constructor
  · simp [reHolonomy,holonomyElemInv,h]
    ext i j
    by_cases hij : i=j <;> norm_num [Matrix.one_apply,hij]
  · simp [imHolonomy,holonomyElemInv,h]
theorem plaqEnergy_nonneg_links (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L)
    (hU : ∀ e ∈ periodicPlaquetteBoundaryEdges p, U e = 1) : 0 ≤ plaqEnergy U A p := by
  have hh : holonomyElem U p = 1 := by
    unfold holonomyElem periodicPlaquetteHolonomy
    dsimp only
    rw [hU _ ((edge_mem p _).mpr (Or.inl rfl)),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))),
      hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))]
    simp
  exact plaqEnergy_nonneg U A p (hol_flat_components U p hh).1 (hol_flat_components U p hh).2
theorem nonstar_nonneg {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (hf : periodicLatticeShift (periodicLatticeShift x 0) 0 ∉ G.Om0)
    (t : ℝ) (u : ↥(bondSupp G)) (p : PeriodicLatticePlaquette L)
    (hnot : ∀ ν : {ν : Fin 3 // 0 < ν}, p ≠ P1 x ν ∧ p ≠ P2 x ν) :
    0 ≤ plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) p := by
  by_cases he : ∃ e ∈ periodicPlaquetteBoundaryEdges p, e ∈ starLinks (periodicLatticeShift x 0)
  · obtain ⟨e,he,hs⟩ := he
    rcases star_edge_cases hb hf p e he hs with ⟨ν,h | h⟩ | hp
    · exact False.elim ((hnot ν).1 h)
    · exact False.elim ((hnot ν).2 h)
    · rw [plaqEnergy_zero_input]
      intro e he
      have hz := exteriorPair_vertices hb p hp e he
      exact u.property e (fun h => h.elim hz.1 hz.2)
  · apply plaqEnergy_nonneg_links
    intro e he'
    have hs : e ∉ starLinks (periodicLatticeShift x 0) := fun hs => he ⟨e,he',hs⟩
    simp [starPath,hs]
theorem right_forward_out {q : ℕ} (hq : 0 < q) (R : ℕ) :
    periodicLatticeShift (periodicLatticeShift (rightSite hq R) 0) 0 ∉ (dilTower q R).Om 0 := by
  change ¬ (4*q ≤ _ ∧ _ < 12*(R*q)+12*q)
  have hcoord : ((rightSite hq R) 0).val = 12*(R*q)+12*q-1 := by simp [rightSite]
  simp only [dil_shift_zero hq R,hcoord,ite_true]
  have ha : 12*(R*q)+12*q-1+1 = 12*(R*q)+12*q := Nat.sub_add_cancel (by omega)
  have hb : (12*(R*q)+12*q) % (12*(R*q)+16*q) = 12*(R*q)+12*q :=
    Nat.mod_eq_of_lt (by omega)
  have hc : (12*(R*q)+12*q+1) % (12*(R*q)+16*q) = 12*(R*q)+12*q+1 :=
    Nat.mod_eq_of_lt (by omega)
  rw [ha,hb,hc]
  omega
theorem hol_phase_components (U : Cfg L) (p : PeriodicLatticePlaquette L) (t : ℝ)
    (hh : holonomyElem U p = uθ t) :
    reHolonomy U p = realHol (Real.cos t) ∧ imHolonomy U p = imagHol (Real.sin t) := by
  have hinv : (holonomyElemInv U p : Matrix (Fin 2) (Fin 2) ℂ) = star (uMat t) := by
    change star (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [hh]
    rfl
  have hcoe : (holonomyElem U p : Matrix (Fin 2) (Fin 2) ℂ) = uMat t := by rw [hh]; rfl
  have hexp (r : ℝ) : Complex.exp ((r : ℂ)*Complex.I) =
      (Real.cos r : ℂ) + (Real.sin r : ℂ)*Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hneg : Complex.exp (-((t : ℂ)*Complex.I)) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ)*Complex.I := by
    rw [← neg_mul, ← Complex.ofReal_neg,hexp]
    simp [Real.cos_neg,Real.sin_neg,sub_eq_add_neg]
  simp only [reHolonomy, imHolonomy, hcoe,hinv]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [uMat,realHol,imagHol,Matrix.star_apply,hexp,hneg,
      Complex.ext_iff] <;> ring
theorem norm_coordinates (X : SuTwo) :
    Complex.normSq ((X : Matrix (Fin 2) (Fin 2) ℂ) 0 1) +
      (((X : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im)^2 = ‖X‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  exact (full_inner X _ _ (lieMat_coordinates X)).symm
theorem right_first_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hX : (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖Y‖^2+‖Z‖^2) ≤ plaqEnergy U A p := by
  have hx := lieMat_coordinates X
  rw [hX] at hx
  have hh' := hol_phase_components U p t hh
  have hp := frozen_right_zero_first_lower U A p (Real.cos t) (Real.sin t)
    _ _ _ _ _ ht (Real.cos_le_one t) (by nlinarith [Real.sin_sq_add_cos_sq t])
    hh'.1 hh'.2 (h1.trans hx) (h2.trans (lieMat_coordinates Y))
    (h3.trans (lieMat_coordinates Z)) h4
  simpa only [norm_coordinates] using hp
theorem right_third_norm_lower (U : Cfg L) (A : BondFnL2 L)
    (p : PeriodicLatticePlaquette L) (t : ℝ) (ht : 0 ≤ Real.cos t)
    (X Y Z : SuTwo) (hZ : (Z : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hh : holonomyElem U p = uθ t)
    (h1 : a1LM U p (WithLp.ofLp A) = (X : Matrix (Fin 2) (Fin 2) ℂ))
    (h2 : a2LM p (WithLp.ofLp A) = (Y : Matrix (Fin 2) (Fin 2) ℂ))
    (h3 : a3LM p (WithLp.ofLp A) = (Z : Matrix (Fin 2) (Fin 2) ℂ))
    (h4 : a4LM U p (WithLp.ofLp A) = 0) :
    -(1-Real.cos t)*(‖X‖^2+‖Y‖^2) ≤ plaqEnergy U A p := by
  have hz := lieMat_coordinates Z
  rw [hZ] at hz
  have hh' := hol_phase_components U p t hh
  have hp := frozen_right_zero_third_lower U A p (Real.cos t) (Real.sin t)
    _ _ _ _ _ ht (Real.cos_le_one t) (by nlinarith [Real.sin_sq_add_cos_sq t])
    hh'.1 hh'.2 (h1.trans (lieMat_coordinates X)) (h2.trans (lieMat_coordinates Y))
    (h3.trans hz) h4
  simpa only [norm_coordinates] using hp
end AdalyFormal.Round13.Positivity.Physical
namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap curlValueCovariant RMap_one)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round12.Noncancel.Plaquette
open AdalyFormal.Round12.Noncancel.FullPlaquette
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

                                                             
theorem arm1_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShift x ν.1,0)‖^2 +
      ‖(iE G u) (x,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P1 x ν) := by
  let A := iE G u
  let U := starPath (periodicLatticeShift x 0) t
  have hU : U (x,ν.1) = 1 := starPath_interior _ _ hb.hx' hb.trans t _ hb.hx
  have hzero : A (periodicLatticeShift x 0,ν.1) = 0 := by
    apply u.property
    intro h
    rcases h with h | h
    · exact hb.hx' h
    · exact hb.hx' ((hb.trans _ ν.1 (ne_of_gt ν.2)).mp h)
  have h := right_third_norm_lower U A (P1 x ν) t ht
    (-A (periodicLatticeShift x ν.1,0)) (-A (x,ν.1)) (A (x,0)) hu
    (star_holonomy1 hb t ν)
    (by simp [a1LM_apply,AprimeZW,AdalyFormal.D1Literal.P1,hU,RMap_one])
    (by rfl) (by rfl)
    (by simp [a4LM_apply,AprimeYZ,AdalyFormal.D1Literal.P1,hzero])
  simpa only [norm_neg] using h
theorem arm2_lower {G : TowerGeom L} {x : PeriodicLatticeSite L}
    (hb : BdPt G.Om0 x) (t : ℝ) (ht : 0 ≤ Real.cos t) (u : ↥(bondSupp G))
    (hu : (((iE G u) (x,0) : SuTwo) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (ν : {ν : Fin 3 // 0 < ν}) :
    -(1-Real.cos t)*(‖(iE G u) (periodicLatticeShiftBack x ν.1,0)‖^2 +
      ‖(iE G u) (periodicLatticeShiftBack x ν.1,ν.1)‖^2) ≤
    plaqEnergy (starPath (periodicLatticeShift x 0) t) (iE G u) (P2 x ν) := by
  let A := iE G u
  let U := starPath (periodicLatticeShift x 0) t
  have hU : U (periodicLatticeShiftBack x ν.1,ν.1) = 1 :=
    starPath_interior _ _ hb.hx' hb.trans t _ (hb.shiftBack_mem ν)
  have hsh : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
      periodicLatticeShift x 0 := by
    rw [shift_comm _ (Ne.symm (ne_of_gt ν.2)),periodicLatticeShift_shiftBack]
  have hzero : A (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = 0 := by
    apply u.property
    intro h
    rcases h with h | h
    · exact hb.hx' (by rw [← hsh]; exact (hb.trans _ ν.1 (ne_of_gt ν.2)).mpr h)
    · exact hb.hx' (by simpa only [hsh] using h)
  have h := right_first_norm_lower U A (P2 x ν) t ht
    (-A (x,0)) (-A (periodicLatticeShiftBack x ν.1,ν.1)) (A (periodicLatticeShiftBack x ν.1,0))
    (by change -_ = 0; rw [hu,neg_zero])
    (star_holonomy2 hb t ν)
    (by simp [a1LM_apply,AprimeZW,P2,hU,RMap_one,periodicLatticeShift_shiftBack])
    (by rfl) (by rfl)
    (by simp [a4LM_apply,AprimeYZ,P2,hzero])
  simpa only [norm_neg,add_comm] using h
theorem arm1_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P1 x ν ∉ plaqIn Om := by
  intro h
  exact hb.hx' (h (x,0) ((edge_mem _ _).mpr (Or.inl rfl))).2
theorem arm2_omitted {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) (ν : {ν : Fin 3 // 0 < ν}) : P2 x ν ∉ plaqIn Om := by
  intro h
  have he := h (periodicLatticeShift (periodicLatticeShiftBack x ν.1) ν.1,0)
    ((edge_mem _ _).mpr (Or.inr (Or.inr (Or.inl rfl))))
  rw [periodicLatticeShift_shiftBack] at he
  exact hb.hx' he.2
end AdalyFormal.Round13.Positivity.Physical
namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneR8
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack)
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
variable {L : PeriodicLatticeExtent}

                                                                
def arm (x : PeriodicLatticeSite L) : Fin 4 → PeriodicLatticePlaquette L :=
  ![P1 x ⟨1,by decide⟩,P2 x ⟨1,by decide⟩,P1 x ⟨2,by decide⟩,P2 x ⟨2,by decide⟩]
theorem arm_injective {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hb : BdPt Om x) : Function.Injective (arm x) := by
  intro i j h
  have hd := congrArg (fun p : PeriodicLatticePlaquette L => p.2.1.2.val) h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [arm,AdalyFormal.D1Literal.P1,P2] at hd
  all_goals first
    | exact False.elim (P1_ne_P2 x hb.side ⟨1,by decide⟩ ⟨1,by decide⟩ h)
    | exact False.elim (P1_ne_P2 x hb.side ⟨1,by decide⟩ ⟨1,by decide⟩ h.symm)
    | exact False.elim (P1_ne_P2 x hb.side ⟨2,by decide⟩ ⟨2,by decide⟩ h)
    | exact False.elim (P1_ne_P2 x hb.side ⟨2,by decide⟩ ⟨2,by decide⟩ h.symm)
def armBudget {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) : Fin 4 → ℝ :=
  ![‖A (leaf hq R 0)‖^2+‖A (leaf hq R 4)‖^2,
    ‖A (leaf hq R 1)‖^2+‖A (leaf hq R 5)‖^2,
    ‖A (leaf hq R 2)‖^2+‖A (leaf hq R 6)‖^2,
    ‖A (leaf hq R 3)‖^2+‖A (leaf hq R 7)‖^2]
theorem armBudget_sum {q : ℕ} (hq : 0 < q) (R : ℕ)
    (A : BondFnL2 (scaleUp 2 1 (dilLu q R))) :
    (∑ i, armBudget hq R A i) = ∑ i : Fin 8, ‖A (leaf hq R i)‖^2 := by
  simp only [Fin.sum_univ_succ]
  change (‖A (leaf hq R 0)‖^2+‖A (leaf hq R 4)‖^2) +
    ((‖A (leaf hq R 1)‖^2+‖A (leaf hq R 5)‖^2) +
    ((‖A (leaf hq R 2)‖^2+‖A (leaf hq R 6)‖^2) +
    ((‖A (leaf hq R 3)‖^2+‖A (leaf hq R 7)‖^2) + 0))) =
    ‖A (leaf hq R 0)‖^2 + (‖A (leaf hq R 1)‖^2 + (‖A (leaf hq R 2)‖^2 +
    (‖A (leaf hq R 3)‖^2 + (‖A (leaf hq R 4)‖^2 + (‖A (leaf hq R 5)‖^2 +
    (‖A (leaf hq R 6)‖^2 + (‖A (leaf hq R 7)‖^2 + 0)))))))
  ring
theorem rightStar_omitted_loss {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t)
    (u : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hu : (((iE (geomOf 2 1 (dilTower q R)) u) (rightSite hq R,0) : SuTwo) :
      Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0) :
    -(1-Real.cos t)*(∑ i : Fin 8,
      ‖(iE (geomOf 2 1 (dilTower q R)) u) (leaf hq R i)‖^2) ≤
    omittedEnergy (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R)) u := by
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (rightStar hq R t) 1 (dilLam q R)
  have hb := rightSite_bd hq R
  have hPG : P.G = geomOf 2 1 (dilTower q R) := rfl
  have hPU : P.U = starPath (periodicLatticeShift (rightSite hq R) 0) t := rfl
  have hh := omitted_loss_of_injective_arms P (dil_admissible hq hR) (by nlinarith)
    u (Real.cos t) (arm (rightSite hq R)) (arm_injective hb)
    (by
      intro i
      fin_cases i
      · exact arm1_omitted hb ⟨1,by decide⟩
      · exact arm2_omitted hb ⟨1,by decide⟩
      · exact arm1_omitted hb ⟨2,by decide⟩
      · exact arm2_omitted hb ⟨2,by decide⟩)
    (armBudget hq R (iE P.G u))
    (by
      intro i
      fin_cases i
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm1_lower hb t ht u hu ⟨1,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm2_lower hb t ht u hu ⟨1,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm1_lower hb t ht u hu ⟨2,by decide⟩
      · simpa [arm,armBudget,leaf,hPG,hPU] using arm2_lower hb t ht u hu ⟨2,by decide⟩)
    (by
      intro p _ hn
      apply nonstar_nonneg hb (right_forward_out hq R) t u p
      intro ν
      have hν : ν.1 = 1 ∨ ν.1 = 2 := by have := ν.2; omega
      rcases hν with hν | hν
      · have heq : ν = ⟨1,by decide⟩ := Subtype.ext hν
        subst ν
        exact ⟨hn 0,hn 1⟩
      · have heq : ν = ⟨2,by decide⟩ := Subtype.ext hν
        subst ν
        exact ⟨hn 2,hn 3⟩)
  rw [armBudget_sum] at hh
  exact hh
end AdalyFormal.Round13.Positivity.Physical
namespace AdalyFormal.Round9.Guarded.AnalyticR2
open scoped RealInnerProductSpace Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.QjComposite (stepAverage)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
variable {L : PeriodicLatticeExtent}
end AdalyFormal.Round9.Guarded.AnalyticR2
namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                              

                                                                                              
                                                                                                 
                                                                                               
                                                                                            
                                                                                                 
                                                                                            
                                                                                          
                                              
section FlatKernel

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dil_fine_size)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_one curlValueCovariant
  gradValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf stepAverage)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open Fin.NatCast

                                                                                       

variable {q R : ℕ}

section Kernel
variable (hq : 0 < q) (hR : 1 ≤ R) (A : BondFnL2 (scaleUp 2 1 (dilLu q R)))
  (hsupp : ∀ b, b ∉ bondsOm0 (geomOf 2 1 (dilTower q R)) → A b = 0)
  (hQ : QfullOf (geomOf 2 1 (dilTower q R)) flatCfg A = 0)

end Kernel

end FlatKernel

end AdalyFormal.Round9.Guarded.AnalyticR2


namespace AdalyFormal.Round9.Guarded.AnalyticR2

open scoped RealInnerProductSpace Topology
open Filter Set

                                                                       
section FlatCarrier

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1 (dilLu dilTower dilLam dilU)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 curlValueCovariant)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantCLM_L2 curlCovariantCLM_L2_toLp)
open AdalyFormal.StatementLaneR6 (plaqMask plaqMask_apply)

                                                                                              
                                                                              
end FlatCarrier

end AdalyFormal.Round9.Guarded.AnalyticR2

namespace AdalyFormal.Round13.Positivity.Local
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round2.Guarded.Pin

                                                                             
theorem rightStar_local_data_flat {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (a t : ℝ) :
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) a (dilLam q R)) =
    dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (fun _ => 1) a (dilLam q R)) := by
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (fun _ => 1) a (dilLam q R)
  have hroom : 17*2 ≤ R*(2*q) := by nlinarith
  have hbd := rightSite_bd hq R
  have hboth : ∀ e : Bond (scaleUp 2 1 (dilLu q R)),
      BothIn ((dilTower q R).Om 0) e → P.U e = rightStar hq R t e := by
    intro e he
    symm
    exact starPath_interior _ _ hbd.hx' hbd.trans t e he.1
  exact AdalyFormal.StatementLaneR8.data_congr P (dil_admissible hq hR)
    (by norm_num) hroom (rightStar hq R t) hboth
theorem rightStar_local_positive {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (x : ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (hx : x ≠ 0) :
    0 < ⟪x, (dataS selIn selIn (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
      (rightStar hq R t) 1 (dilLam q R))).Ginv x⟫ := by
  rw [rightStar_local_data_flat hq hR hR18]
  exact AdalyFormal.Round9.Guarded.AnalyticR2.dil_flat_pos hq (by omega) x hx
set_option pp.fullNames true
end AdalyFormal.Round13.Positivity.Local

namespace AdalyFormal.Round9.Guarded.AnalyticR1
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative

end AdalyFormal.Round9.Guarded.AnalyticR1

namespace AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Target.ClayStatement AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.CovariantOperators (BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
                                                                         
end AdalyFormal.Round12.Kernel.Actual

namespace AdalyFormal.Round13.Positivity.Physical
open Classical
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR6
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Positivity.Leaves
open AdalyFormal.Round13.Positivity.Local
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round12.Kernel.Actual (chargedCoordinate)

                                                           
theorem rightStar_local_hol {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (p : PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))
    (hp : p ∈ plaqIn ((dilTower q R).Om 0)) :
    reHolonomy (rightStar hq R t) p = 1 ∧ imHolonomy (rightStar hq R t) p = 0 := by
  have hU : ∀ e ∈ periodicPlaquetteBoundaryEdges p, rightStar hq R t e = 1 := by
    intro e he
    exact starPath_interior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e (hp e he).1
  apply hol_flat_components
  unfold holonomyElem periodicPlaquetteHolonomy
  dsimp only
  rw [hU _ ((edge_mem p _).mpr (Or.inl rfl)),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inl rfl))),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inl rfl)))),
    hU _ ((edge_mem p _).mpr (Or.inr (Or.inr (Or.inr rfl))))]
  simp
theorem rightStar_carrier_lower {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht : 0 ≤ Real.cos t) (u : TwistSpace q R)
    (hu : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    Real.cos t * ⟪u, (dataS selIn selIn
      (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (rightStar hq R t) 1 (dilLam q R))).Ginv u⟫ ≤
      ⟪u, vacA q R (rightStar hq R) 1 t u⟫ := by
  rw [vacA_rightStar]
  let P := gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
    (rightStar hq R t) 1 (dilLam q R)
  apply carrier_ge_scaled_local P u (Real.cos t)
    (∑ i : Fin 8, ‖(iE P.G u) (leaf hq R i)‖^2) (Real.cos_le_one t)
  · apply localized_Dpi_nonneg
    · intro p hp; exact (rightStar_local_hol hq R t p hp).1
    · intro p hp; exact (rightStar_local_hol hq R t p hp).2
  · change _ ≤ ⟪u,pE P.G (MassFull P.G P.a (bondSectorOf P.G P.U) (iE P.G u))⟫
    rw [pE_inner_right]
    exact eight_leaf_mass hq hR (by omega) P.U (iE P.G u)
  · exact rightStar_omitted_loss hq hR hR18 t ht u hu
theorem rightStar_zero_coordinate_positive {q R : ℕ}
    (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t < Real.pi/2)
    (u : TwistSpace q R) (hu : u ≠ 0)
    (hz : chargedCoordinate q R (rightSite hq R,(0 : Fin 3)) u = 0) :
    0 < ⟪u, vacA q R (rightStar hq R) 1 t u⟫ := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],ht⟩
  exact lt_of_lt_of_le (mul_pos hc (rightStar_local_positive hq hR hR18 t u hu))
    (rightStar_carrier_lower hq hR hR18 t hc.le u hz)
set_option linter.unusedVariables false in
/-- P2 VERBATIM, no extra analytic, geometric, inverse or spectral hypothesis. -/
theorem rightStar_P2 :
    ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
      (t : ℝ), 0 < t → t < Real.pi/2 →
      ∀ x : TwistSpace q R, x ≠ 0 →
        AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
          (rightSite hq R, (0 : Fin 3)) x = 0 →
        0 < ⟪x, vacA q R (rightStar hq R) 1 t x⟫ := by
  intro q R hq hR hR18 t ht0 ht x hx hz
  exact rightStar_zero_coordinate_positive hq hR hR18 t ht0.le ht x hx hz
end AdalyFormal.Round13.Positivity.Physical
namespace AdalyFormal.Round13.Assembly.R2
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Assembly.R4 (CofinalAnyPathNoResponseCancellation)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Round13.Assembly.R1
open AdalyFormal.Round2.Guarded.Pin (GoalNeg2)

                                                                      
theorem p2 : P2 := AdalyFormal.Round13.Positivity.Physical.rightStar_P2
theorem rightStar_kernelLine {q R : ℕ} (hq : 0 < q)
    (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    0 < vacEdge q R (rightStar hq R) ∧
    vacEdge q R (rightStar hq R) < Real.pi/2 ∧
    ∃ u : TwistSpace q R, KernelLine q R (rightStar hq R) u ∧
      Module.finrank ℝ (vacA q R (rightStar hq R) 1
        (vacEdge q R (rightStar hq R))).ker = 2 := by
  obtain ⟨hc,hpd⟩ := startInputs hq hR hR18
  exact AdalyFormal.Round12.Kernel.CrossingActual.kernelLine_exists_before_halfpi
    q R (rightStar hq R) (rightSite hq R,0) hc hpd (p1 hq hR hR18)
    (fun t => rightStar_fixed hq R t (Real.pi/4)) (p2 hq hR hR18)
theorem cofinal_rightStar_kernelLine :
    ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
      R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
      0 < vacEdge (2^j) R (rightStar (by positivity) R) ∧
      vacEdge (2^j) R (rightStar (by positivity) R) < Real.pi/2 ∧
      ∃ u : TwistSpace (2^j) R,
        KernelLine (2^j) R (rightStar (by positivity) R) u ∧
        Module.finrank ℝ (vacA (2^j) R (rightStar (by positivity) R) 1
          (vacEdge (2^j) R (rightStar (by positivity) R))).ker = 2 := by
  intro j₀
  refine ⟨j₀,le_rfl,?_⟩
  intro R₀
  exact ⟨2*(R₀+18),by omega,⟨R₀+18,rfl⟩,by omega,
    rightStar_kernelLine (by positivity) ⟨R₀+18,rfl⟩ (by omega)⟩
theorem cofinalNoCancellation_of_P3 (h3 : P3) : CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_P2_P3 p2 h3
theorem goalNeg2_of_P3 (h3 : P3) : GoalNeg2 := goalNeg2_of_P2_P3 p2 h3
def CofinalP3 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ,
    R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∀ u : TwistSpace (2^j) R,
      KernelLine (2^j) R (rightStar (by positivity) R) u → CurlDetected (2^j) R u
theorem cofinalP2P3_of_cofinalP3 (h : CofinalP3) : CofinalP2P3 := by
  intro j₀
  obtain ⟨j,hj,hRs⟩ := h j₀
  refine ⟨j,hj,?_⟩
  intro R₀
  obtain ⟨R,hR0,hR,hR18,hd⟩ := hRs R₀
  exact ⟨R,hR0,hR,hR18,p2 (by positivity) hR hR18,hd⟩
theorem cofinalNoCancellation_of_cofinalP3 (h : CofinalP3) :
    CofinalAnyPathNoResponseCancellation :=
  cofinalNoCancellation_of_cofinalP2P3 (cofinalP2P3_of_cofinalP3 h)
theorem goalNeg2_of_cofinalP3 (h : CofinalP3) : GoalNeg2 :=
  goalNeg2_of_cofinalP2P3 (cofinalP2P3_of_cofinalP3 h)
end AdalyFormal.Round13.Assembly.R2

#print axioms AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation
#check @AdalyFormal.Round10.Assembly.R4.goalNeg2_of_cofinalAnyPathNoResponseCancellation
#print axioms AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3
#check @AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P2_P3
#print axioms AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3
#check @AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP2P3
#print axioms AdalyFormal.Round13.Assembly.R2.CofinalP3
#check @AdalyFormal.Round13.Assembly.R2.CofinalP3
#print axioms AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_P3
#check @AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_P3
#print axioms AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_cofinalP3
#check @AdalyFormal.Round13.Assembly.R2.cofinalNoCancellation_of_cofinalP3
#print axioms AdalyFormal.Round13.Assembly.R2.cofinalP2P3_of_cofinalP3
#check @AdalyFormal.Round13.Assembly.R2.cofinalP2P3_of_cofinalP3
#print axioms AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine
#check @AdalyFormal.Round13.Assembly.R2.cofinal_rightStar_kernelLine
#print axioms AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3
#check @AdalyFormal.Round13.Assembly.R2.goalNeg2_of_P3
#print axioms AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
#check @AdalyFormal.Round13.Assembly.R2.goalNeg2_of_cofinalP3
#print axioms AdalyFormal.Round13.Assembly.R2.p2
#check @AdalyFormal.Round13.Assembly.R2.p2
#print axioms AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine
#check @AdalyFormal.Round13.Assembly.R2.rightStar_kernelLine

namespace AdalyFormal.Round14.PathChoice
open scoped RealInnerProductSpace Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 suTwoWitness suTwoWitness_ne_zero)
open AdalyFormal.GaugeCov
open AdalyFormal.Balaban.SuTwoInner (hsInner)
open AdalyFormal.Balaban.DeltaPrime
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.CovariantHjMinimizer (periodicLatticeShiftBack periodicLatticeShift_shiftBack)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round9.Guarded.AnalyticR1 (TwistSpace)
open AdalyFormal.Round10.Assembly.R2 (KernelLine)
open AdalyFormal.Round10.Dictionary.FreeSource (CurlDetected)
open AdalyFormal.Round12.Noncancel.Path
variable {L : PeriodicLatticeExtent}

/-- Forward iteration of a transverse lattice shift. -/
def shiftN (x : PeriodicLatticeSite L) (μ : Fin 3) : ℕ → PeriodicLatticeSite L
  | 0 => x
  | n+1 => periodicLatticeShift (shiftN x μ n) μ

/-- Backward iteration of a transverse lattice shift. -/
def backN (x : PeriodicLatticeSite L) (μ : Fin 3) : ℕ → PeriodicLatticeSite L
  | 0 => x
  | n+1 => periodicLatticeShiftBack (backN x μ n) μ

theorem shiftN_mem_iff (Om : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : shiftN x μ n ∈ Om ↔ x ∈ Om := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change periodicLatticeShift (shiftN x μ n) μ ∈ Om ↔ x ∈ Om
      rw [htrans _ _ hμ, ih]

theorem backN_mem_iff (Om : Set (PeriodicLatticeSite L)) (x : PeriodicLatticeSite L)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : backN x μ n ∈ Om ↔ x ∈ Om := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change periodicLatticeShiftBack (backN x μ n) μ ∈ Om ↔ x ∈ Om
      have h := htrans (periodicLatticeShiftBack (backN x μ n) μ) μ hμ
      rw [periodicLatticeShift_shiftBack] at h
      exact h.symm.trans ih

/-- The forward bond at level `n`, and the backward bond at level `n+1`. -/
def forwardBond (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Bond L :=
  (shiftN x μ n, μ)

def backwardBond (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Bond L :=
  (backN x μ n, μ)

/-- The two transverse bonds added at one arm level. -/
def armLevel (x : PeriodicLatticeSite L) (μ : Fin 3) (n : ℕ) : Set (Bond L) :=
  {forwardBond x μ n, backwardBond x μ (n+1)}

/-- All transverse bonds on both arms through level `N-1`.  Level zero is the
original four-bond star; each further level adds four bonds. -/
def longStarLinks (x : PeriodicLatticeSite L) (N : ℕ) : Set (Bond L) :=
  {e | ∃ μ : Fin 3, μ ≠ 0 ∧ ∃ n : ℕ, n < N ∧ e ∈ armLevel x μ n}

theorem forwardBond_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : forwardBond x μ n ∈ Zb Om := by
  constructor
  · exact fun h => hx ((shiftN_mem_iff Om x htrans μ hμ n).mp h)
  · change periodicLatticeShift (shiftN x μ n) μ ∉ Om
    exact fun h => hx ((shiftN_mem_iff Om x htrans μ hμ (n+1)).mp h)

theorem backwardBond_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (μ : Fin 3) (hμ : μ ≠ 0) (n : ℕ) : backwardBond x μ (n+1) ∈ Zb Om := by
  constructor
  · exact fun h => hx ((backN_mem_iff Om x htrans μ hμ (n+1)).mp h)
  · change periodicLatticeShift (periodicLatticeShiftBack (backN x μ n) μ) μ ∉ Om
    rw [periodicLatticeShift_shiftBack]
    exact fun h => hx ((backN_mem_iff Om x htrans μ hμ n).mp h)

theorem longStarLinks_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (N : ℕ) : longStarLinks x N ⊆ Zb Om := by
  rintro e ⟨μ,hμ,n,hn,he⟩
  change e = forwardBond x μ n ∨ e = backwardBond x μ (n+1) at he
  rcases he with rfl | rfl
  · exact forwardBond_exterior Om x hx htrans μ hμ n
  · exact backwardBond_exterior Om x hx htrans μ hμ n

open Classical in
/-- Independent real angle coefficients on a finite two-sided transverse star. -/
def longStarPath (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) (t : ℝ) : Cfg L :=
  fun e => if e ∈ longStarLinks x N then uθ (c e * t) else 1

theorem longStarPath_zero (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    longStarPath x N c 0 = fun _ => 1 := by
  funext e
  simp [longStarPath, uθ_zero]

theorem longStarPath_cont (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    ContFam (longStarPath x N c) := by
  intro e
  by_cases h : e ∈ longStarLinks x N
  · simp only [longStarPath, h, if_true]
    change Continuous fun t => uMat (c e * t)
    unfold uMat
    refine continuous_matrix (fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · simp only [longStarPath, h, if_false]
    exact continuous_const

theorem longStarPath_an (x : PeriodicLatticeSite L) (N : ℕ) (c : Bond L → ℝ) :
    AnFam (longStarPath x N c) := by
  intro e
  by_cases h : e ∈ longStarLinks x N
  · simp only [longStarPath, h, if_true]
    show AnM fun t => uMat (c e * t)
    intro t₀ i j
    have hlin : AnalyticAt ℝ (fun t : ℝ => c e * t) t₀ := by fun_prop
    exact (anM_uMat (c e * t₀) i j).comp hlin
  · intro t i j
    simp only [longStarPath, h, if_false]
    exact analyticAt_const

theorem longStarPath_off_exterior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (N : ℕ) (c : Bond L → ℝ) (t : ℝ) (e : Bond L) (he : e ∉ Zb Om) :
    longStarPath x N c t e = 1 := by
  have hh : e ∉ longStarLinks x N := fun h => he (longStarLinks_exterior Om x hx htrans N h)
  simp [longStarPath, hh]

theorem longStarPath_fixed (x : PeriodicLatticeSite L) (N : ℕ)
    (c : Bond L → ℝ) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (longStarPath x N c t) = longStarPath x N c t := by
  funext e
  change uθ α * longStarPath x N c t e * (uθ α)⁻¹ = longStarPath x N c t e
  by_cases he : e ∈ longStarLinks x N
  · simp only [longStarPath, he, if_true]
    rw [uθ_comm, mul_assoc, mul_inv_cancel, mul_one]
  · simp [longStarPath, he]

/-- The right-placed finite-arm family. -/
def longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  longStarPath (periodicLatticeShift (rightSite hq R) 0) N c

theorem longRightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    longRightStar hq R N c 0 = fun _ => 1 := longStarPath_zero _ _ _

theorem longRightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    ContFam (longRightStar hq R N c) := longStarPath_cont _ _ _

theorem longRightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    AnFam (longRightStar hq R N c) := longStarPath_an _ _ _

theorem longRightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ Zb ((dilTower q R).Om 0)) : longRightStar hq R N c t e = 1 :=
  longStarPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans N c t e he

theorem longRightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (longRightStar hq R N c t) = longRightStar hq R N c t :=
  longStarPath_fixed _ _ _ _ _

theorem pathU_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (longRightStar hq R N c) f 0 t = longRightStar hq R N c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [pathU, maskedU, he]
  · rw [longRightStar_off_exterior hq R N c t e he]
    simp [pathU, maskedU, he, Ug_zero]

theorem dilU_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    dilU q R 0 (longRightStar hq R N c t) = longRightStar hq R N c t := by
  classical
  funext e
  by_cases he : e ∈ Zb ((dilTower q R).Om 0)
  · simp [dilU, he]
  · rw [longRightStar_off_exterior hq R N c t e he]
    simp [dilU, he, Ug_zero]

theorem vacA_longRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (N : ℕ)
    (c : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    vacA q R (longRightStar hq R N c) a t =
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (longRightStar hq R N c t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  rw [pathU_longRightStar]
  rfl

open Classical in
/-- Exact coefficients used by the low-cancellation three-level path. -/
def tailCoeff (x : PeriodicLatticeSite L) (e : Bond L) : ℝ :=
  if e ∈ longStarLinks x 1 then 1
  else if e ∈ longStarLinks x 2 then -(1/4 : ℝ)
  else if e ∈ longStarLinks x 3 then -(9/4 : ℝ)
  else 0

/-- Three levels with coefficients 1, -1/4 and -9/4. -/
def tailPath (x : PeriodicLatticeSite L) : ℝ → Cfg L :=
  longStarPath x 3 (tailCoeff x)

def tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  tailPath (periodicLatticeShift (rightSite hq R) 0)

theorem tailCoeff_zero_level (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 1) : tailCoeff x e = 1 := by simp [tailCoeff, he]

theorem tailCoeff_first_extension (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 2) (hn : e ∉ longStarLinks x 1) :
    tailCoeff x e = -(1/4 : ℝ) := by simp [tailCoeff, he, hn]

theorem tailCoeff_second_extension (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ longStarLinks x 3) (hn : e ∉ longStarLinks x 2)
    (hn0 : e ∉ longStarLinks x 1) :
    tailCoeff x e = -(9/4 : ℝ) := by simp [tailCoeff, he, hn, hn0]

theorem tailPath_zero (x : PeriodicLatticeSite L) : tailPath x 0 = fun _ => 1 :=
  longStarPath_zero _ _ _

theorem tailPath_cont (x : PeriodicLatticeSite L) : ContFam (tailPath x) :=
  longStarPath_cont _ _ _

theorem tailPath_an (x : PeriodicLatticeSite L) : AnFam (tailPath x) :=
  longStarPath_an _ _ _

theorem tailPath_fixed (x : PeriodicLatticeSite L) (t α : ℝ) :
    periodicGaugeTransform (fun _ => uθ α) (tailPath x t) = tailPath x t :=
  longStarPath_fixed _ _ _ _ _

theorem tailRightStar_zero {q : ℕ} (hq : 0 < q) (R : ℕ) :
    tailRightStar hq R 0 = fun _ => 1 := tailPath_zero _

theorem tailRightStar_cont {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ContFam (tailRightStar hq R) := tailPath_cont _

theorem tailRightStar_an {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AnFam (tailRightStar hq R) := tailPath_an _

theorem tailRightStar_fixed {q : ℕ} (hq : 0 < q) (R : ℕ) (t α : ℝ) :
    periodicGaugeTransform (rotGauge α) (tailRightStar hq R t) = tailRightStar hq R t :=
  tailPath_fixed _ _ _

theorem tailRightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ Zb ((dilTower q R).Om 0)) : tailRightStar hq R t e = 1 :=
  longRightStar_off_exterior hq R 3 (tailCoeff _) t e he

theorem pathU_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) :
    pathU q R (tailRightStar hq R) f 0 t = tailRightStar hq R t :=
  pathU_longRightStar hq R 3 (tailCoeff _) t f

theorem dilU_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ) :
    dilU q R 0 (tailRightStar hq R t) = tailRightStar hq R t :=
  dilU_longRightStar hq R 3 (tailCoeff _) t

theorem vacA_tailRightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (tailRightStar hq R) a t =
      (dataS selAll selAll (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
        (tailRightStar hq R t) a (dilLam q R))).Ginv :=
  vacA_longRightStar hq R 3 (tailCoeff _) a t

open AdalyFormal.Round12.Kernel.Crossing
open AdalyFormal.Round12.Kernel.Actual
open AdalyFormal.Round9.Guarded.QualitativeR2Joint (flat_loc_unit)
set_option linter.unusedVariables false

/-- Negative-direction input at the original pi endpoint. -/
def TailEndpointNegative : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0

/-- Zero-coordinate positivity only at the canonical crossing, not on a whole
prefix.  This is the weaker input used by the crossing package below. -/
def TailCrossingPositive : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (x : TwistSpace q R), x ≠ 0 →
    AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
      (rightSite hq R, (0 : Fin 3)) x = 0 →
    0 < ⟪x, vacA q R (tailRightStar hq R) 1 (vacEdge q R (tailRightStar hq R)) x⟫

/-- Continuity of the actual tail-path carrier, using its proved analytic path. -/
theorem tailRightStar_vacA_cont {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    Continuous (vacA q R (tailRightStar hq R) 1) := by
  exact pathA_continuous hq hR (by nlinarith) (tailRightStar_cont hq R) (fun _ => 0) 0 1

/-- Positive-definite start for the same actual carrier. -/
theorem tailRightStar_vacA_pd_zero {q R : ℕ} (hq : 0 < q) (hR : 1 ≤ R)
    (x : TwistSpace q R) (hx : x ≠ 0) :
    0 < ⟪x, vacA q R (tailRightStar hq R) 1 0 x⟫ := by
  exact vacA_pd_zero (tailRightStar_zero hq R) (flat_loc_unit hq hR) x hx

/-- A negative pi direction and positivity at the crossing suffice for the
complete charged line and real nullity two; no full-interval P2 is assumed. -/
theorem tailKernelLine_of_inputs {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R)
    (hneg : ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0)
    (hpos : ∀ x : TwistSpace q R, x ≠ 0 →
      AdalyFormal.Round12.Kernel.Actual.chargedCoordinate q R
        (rightSite hq R, (0 : Fin 3)) x = 0 →
      0 < ⟪x, vacA q R (tailRightStar hq R) 1 (vacEdge q R (tailRightStar hq R)) x⟫) :
    0 < vacEdge q R (tailRightStar hq R) ∧ vacEdge q R (tailRightStar hq R) < Real.pi ∧
      ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
        Module.finrank ℝ (vacA q R (tailRightStar hq R) 1
          (vacEdge q R (tailRightStar hq R))).ker = 2 := by
  obtain ⟨w,hw⟩ := hneg
  have hc := tailRightStar_vacA_cont hq hR hR18
  have hpd : ∀ x : TwistSpace q R, x ≠ 0 →
      0 < ⟪x, vacA q R (tailRightStar hq R) 1 0 x⟫ :=
    tailRightStar_vacA_pd_zero (q := q) (R := R) hq (by omega)
  have hs : ∀ t x y, ⟪vacA q R (tailRightStar hq R) 1 t x,y⟫ =
      ⟪x, vacA q R (tailRightStar hq R) 1 t y⟫ := by
    intro t x y
    exact (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll
      AdalyFormal.D1Literal.selAll (pathP q R (tailRightStar hq R) (fun _ => 0) 0 1 t)).Ginv_symm
      (AdalyFormal.D1Literal.dataS_laws _ _ _) x y
  have heq : vacEdge q R (tailRightStar hq R) =
      psdEdge (vacA q R (tailRightStar hq R) 1) 0 Real.pi :=
    psdEdge_same_after_negative _ (by positivity) (le_refl _) w hw
  obtain ⟨h0,ht,_,hn,_,_⟩ := psdEdge_singular_without_isolation
    (vacA q R (tailRightStar hq R) 1) hc hs Real.pi_pos hpd w hw
  rw [← heq] at h0 ht hn
  obtain ⟨u,hu,hAu⟩ := exists_kernel_of_nonunit _ hn
  have hl := kernelLine_of_boundary_positive q R (tailRightStar hq R)
    (rightSite hq R, (0 : Fin 3)) (tailRightStar_fixed hq R _ _) hpos u hu hAu
  exact ⟨h0,ht,u,hl,kernelLine_finrank q R (tailRightStar hq R)
    (tailRightStar_fixed hq R _ _) u hl⟩

/-- Exact all-instance crossing package remaining for the modified path. -/
def TailKernelLinePackage : Prop :=
  ∀ {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R),
    0 < vacEdge q R (tailRightStar hq R) ∧ vacEdge q R (tailRightStar hq R) < Real.pi ∧
      ∃ u : TwistSpace q R, KernelLine q R (tailRightStar hq R) u ∧
        Module.finrank ℝ (vacA q R (tailRightStar hq R) 1
          (vacEdge q R (tailRightStar hq R))).ker = 2

theorem tailKernelLinePackage_of_inputs (hneg : TailEndpointNegative)
    (hpos : TailCrossingPositive) : TailKernelLinePackage := by
  intro q R hq hR hR18
  exact tailKernelLine_of_inputs hq hR hR18 (hneg hq hR hR18) (hpos hq hR hR18)

/-- Original four arms are contained in every longer finite-arm support. -/
theorem starLinks_subset_longStarLinks (x : PeriodicLatticeSite L) :
    starLinks x ⊆ longStarLinks x 1 := by
  rintro ⟨z,ν⟩ ⟨hν,hz | hz⟩
  · change ν ≠ 0 at hν
    change z = x at hz
    subst z
    exact ⟨ν,hν,0,by omega,Or.inl rfl⟩
  · change periodicLatticeShift z ν = x at hz
    have hz' : z = periodicLatticeShiftBack x ν := by
      rw [← hz, AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack_shift]
    subst z
    exact ⟨ν,hν,0,by omega,Or.inr rfl⟩

theorem longStarLinks_mono (x : PeriodicLatticeSite L) {N M : ℕ} (hNM : N ≤ M) :
    longStarLinks x N ⊆ longStarLinks x M := by
  rintro e ⟨μ,hμ,n,hn,he⟩
  exact ⟨μ,hμ,n,lt_of_lt_of_le hn hNM,he⟩

theorem tailPath_original (x : PeriodicLatticeSite L) (e : Bond L)
    (he : e ∈ starLinks x) (t : ℝ) : tailPath x t e = uθ t := by
  have hs := starLinks_subset_longStarLinks x he
  have hs3 := longStarLinks_mono x (by omega : 1 ≤ 3) hs
  simp [tailPath, longStarPath, hs3, tailCoeff_zero_level x e hs]

theorem tailPath_interior (Om : Set (PeriodicLatticeSite L))
    (x : PeriodicLatticeSite L) (hx : x ∉ Om)
    (htrans : ∀ z (ν : Fin 3), ν ≠ 0 → (periodicLatticeShift z ν ∈ Om ↔ z ∈ Om))
    (t : ℝ) (e : Bond L) (he : e.1 ∈ Om) : tailPath x t e = 1 := by
  have hh : e ∉ longStarLinks x 3 := fun h => (longStarLinks_exterior Om x hx htrans 3 h).1 he
  simp [tailPath, longStarPath, hh]

theorem tailPath_normal (x z : PeriodicLatticeSite L) (t : ℝ) :
    tailPath x t (z,0) = 1 := by
  have hh : (z,0) ∉ longStarLinks x 3 := by
    rintro ⟨μ,hμ,n,hn,he⟩
    change (z,0) = forwardBond x μ n ∨ (z,0) = backwardBond x μ (n+1) at he
    rcases he with h | h
    · exact hμ (congrArg (fun e : Bond L => e.2) h).symm
    · exact hμ (congrArg (fun e : Bond L => e.2) h).symm
  simp [tailPath, longStarPath, hh]

theorem tailPath_holonomy1 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (tailPath (periodicLatticeShift x 0) t) (AdalyFormal.D1Literal.P1 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := tailPath_normal (periodicLatticeShift x 0) x t
  have h2 : tailPath (periodicLatticeShift x 0) t (periodicLatticeShift x 0,ν.1) = uθ t :=
    tailPath_original _ _ (by simp [starLinks, hν]) t
  have h3 := tailPath_normal (periodicLatticeShift x 0) (periodicLatticeShift x ν.1) t
  have h4 := tailPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t (x,ν.1) hbd.hx
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy AdalyFormal.D1Literal.P1
  simp only
  rw [h1,h2,h3,h4]
  simp

theorem tailPath_holonomy2 {Om : Set (PeriodicLatticeSite L)} {x : PeriodicLatticeSite L}
    (hbd : BdPt Om x) (t : ℝ) (ν : {ν : Fin 3 // 0 < ν}) :
    holonomyElem (tailPath (periodicLatticeShift x 0) t) (AdalyFormal.D1Literal.P2 x ν) = uθ t := by
  have hν : ν.1 ≠ 0 := ne_of_gt ν.2
  have h1 := tailPath_normal (periodicLatticeShift x 0) (periodicLatticeShiftBack x ν.1) t
  have h2 : tailPath (periodicLatticeShift x 0) t
      (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0,ν.1) = uθ t := by
    apply tailPath_original
    have hs : periodicLatticeShift (periodicLatticeShift (periodicLatticeShiftBack x ν.1) 0) ν.1 =
        periodicLatticeShift x 0 := by
      rw [AdalyFormal.StatementLaneR8.shift_comm _ (Ne.symm hν), periodicLatticeShift_shiftBack]
    simp [starLinks, hν, hs]
  have h3 := tailPath_normal (periodicLatticeShift x 0) x t
  have h4 := tailPath_interior Om (periodicLatticeShift x 0) hbd.hx' hbd.trans t
    (periodicLatticeShiftBack x ν.1,ν.1) (hbd.shiftBack_mem ν)
  change periodicPlaquetteHolonomy _ _ = _
  unfold periodicPlaquetteHolonomy AdalyFormal.D1Literal.P2
  simp only
  rw [h1,h2,periodicLatticeShift_shiftBack,h3,h4]
  simp

/-- The original central-bond negative-energy trial is unchanged by the added arms. -/
theorem tailPath_negative_endpoint {ell M R k : ℕ} {Lu : PeriodicLatticeExtent}
    (hell0 : 0 < ell) (S : Tower (scaleUp ell k Lu))
    (Lam : Set (PeriodicLatticeSite Lu)) (a : ℝ)
    (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 17*ell ≤ R*M)
    {x : PeriodicLatticeSite (scaleUp ell k Lu)} (hbd : BdPt (S.Om 0) x)
    (ha : 0 ≤ a) (ha4 : a < 4) (X : SuTwo) (hX : X ≠ 0) :
    ∃ v : ↥(bondSupp (geomOf ell k S)),
      ⟪v, (dataS selAll selAll (gparams ell k Lu hell0 S
        (tailPath (periodicLatticeShift x 0) Real.pi) a Lam)).Ginv v⟫ < 0 := by
  let U := tailPath (periodicLatticeShift x 0) Real.pi
  let P := gparams ell k Lu hell0 S U a Lam
  have hm := sing_mem_bondSupp (geomOf ell k S) hbd.hx X
  let v : ↥(bondSupp (geomOf ell k S)) := ⟨sing (x,0) X,hm⟩
  have hn : 0 < hsInner X X := by
    exact lt_of_le_of_ne (real_inner_self_nonneg (x := X))
      (fun h => hX (AdalyFormal.Balaban.SuTwoInner.hsInner_self_eq_zero h.symm))
  have hd : ⟪v, (dataS selAll selAll P).Dpi v⟫ = -4*hsInner X X := by
    have e := E0_Dpi_inner selAll (geomOf ell k S) U a v
    refine e.trans ?_
    have hw : Wop (geomOf ell k S) U a (iE (geomOf ell k S) v) = sing (x,0) X :=
      Wop_sing hS (by omega) hbd U a X
    rw [hw]
    apply delta_value U x X hbd.side
    · intro ν
      change ((holonomyElem (tailPath _ Real.pi) (AdalyFormal.D1Literal.P1 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [tailPath_holonomy1 hbd, uθ_pi_coe]
    · intro ν
      change ((holonomyElem (tailPath _ Real.pi) (AdalyFormal.D1Literal.P2 x ν) : SU2m) : Matrix (Fin 2) (Fin 2) ℂ) = -1
      rw [tailPath_holonomy2 hbd, uθ_pi_coe]
    · intro ν
      exact tailPath_interior (S.Om 0) _ hbd.hx' hbd.trans _ _ (hbd.shiftBack_mem ν)
  have ht : (dataS selAll selAll P).T v = 0 :=
    Tfull_sing_zero hS (by omega) hbd U X
  have hmass : ⟪v, (dataS selAll selAll P).Mass v⟫ ≤ a*hsInner X X := by
    change ⟪v, ((pE (geomOf ell k S)).comp ((MassFull (geomOf ell k S) a
      (bondSectorOf (geomOf ell k S) U)).comp (iE (geomOf ell k S)))) v⟫ ≤ _
    simp only [ContinuousLinearMap.comp_apply]
    rw [pE_inner_right]
    exact Mass_sing_le hS hell (by omega) hbd U a ha X
  refine ⟨v,?_⟩
  change ⟪v, (dataS selAll selAll P).Ginv v⟫ < 0
  rw [BaseDataS.inner_Ginv,hd,ht]
  simp only [norm_zero]
  nlinarith

theorem tailRightStar_negative_pi {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (hR18 : 18 ≤ R) :
    ∃ w : TwistSpace q R, ⟪w, vacA q R (tailRightStar hq R) 1 Real.pi w⟫ < 0 := by
  rw [vacA_tailRightStar]
  unfold tailRightStar
  exact tailPath_negative_endpoint (by norm_num) (dilTower q R) (dilLam q R) 1
    (dil_admissible hq hR) (by norm_num) (by nlinarith)
    (rightSite_bd hq R) (by norm_num) (by norm_num) suTwoWitness suTwoWitness_ne_zero

theorem tailEndpointNegative : TailEndpointNegative := by
  intro q R hq hR hR18
  exact tailRightStar_negative_pi hq hR hR18

/-- After the proved endpoint input, only crossing positivity remains for the
complete charged-line package. -/
theorem tailKernelLinePackage_of_crossingPositive (hpos : TailCrossingPositive) :
    TailKernelLinePackage :=
  tailKernelLinePackage_of_inputs tailEndpointNegative hpos

#print axioms longStarLinks_mono
#print axioms starLinks_subset_longStarLinks
#print axioms tailPath_original
#print axioms tailPath_interior
#print axioms tailPath_normal
#print axioms tailPath_holonomy1
#print axioms tailPath_holonomy2
#print axioms tailPath_negative_endpoint
#print axioms tailRightStar_negative_pi
#print axioms tailEndpointNegative
#print axioms tailKernelLinePackage_of_crossingPositive
#print axioms TailEndpointNegative
#print axioms TailCrossingPositive
#print axioms tailRightStar_vacA_cont
#print axioms tailRightStar_vacA_pd_zero
#print axioms tailKernelLine_of_inputs
#print axioms TailKernelLinePackage
#print axioms tailKernelLinePackage_of_inputs
#check @tailKernelLinePackage_of_inputs
end AdalyFormal.Round14.PathChoice

import DrEquiv
import ZXR2Flat6
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

namespace AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.NonVac (iv_block pcd_clamp pcd_near pcd_self')

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

/-- The coordinate-zero term is bounded by the full periodic distance. -/
theorem zero_coord_le_pdist {L : PeriodicLatticeExtent} (x y : PeriodicLatticeSite L) :
    pcd (L 0 + 1) (x 0).val (y 0).val ≤ pdist x y := by
  unfold pdist
  exact Finset.single_le_sum
    (f := fun μ : Fin 3 => pcd (L μ + 1) (x μ).val (y μ).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

theorem dil_fine_bound {q : ℕ} (hq : 0 < q) (R : ℕ)
    (x : PeriodicLatticeSite (scaleUp 2 1 (dilLu q R))) :
    (x 0).val < 12 * (R * q) + 16 * q := by
  have h := (x 0).isLt
  simpa only [dil_fine_size hq, ↓reduceIte] using h

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

end AdalyFormal.Round4.Guarded.RefuteR1

namespace AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.StatementLane2 (Ug)

noncomputable def rightSite {q : ℕ} (hq : 0 < q) (R : ℕ) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu q R)) :=
  fun μ => ⟨if μ = 0 then 12*(R*q)+12*q-1 else 0,
    by rw [dil_fine_size hq]; split_ifs <;> omega⟩

theorem rightSite_bd {q : ℕ} (hq : 0 < q) (R : ℕ) :
    AdalyFormal.D1Literal.BdPt ((dilTower q R).Om 0) (rightSite hq R) := by
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

open Classical in
noncomputable def maskedU (q R : ℕ)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (V : LinkCfg (scaleUp 2 1 (dilLu q R))) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun e => if e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) then V e else Ug (f e)

end AdalyFormal.Round5.Guarded.IVTR2

namespace AdalyFormal.Round12.Noncancel.Path
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (uθ Zb)
variable {L : PeriodicLatticeExtent}

def starLinks (x : PeriodicLatticeSite L) : Set (Bond L) :=
  {e | e.2 ≠ 0 ∧ (e.1 = x ∨ periodicLatticeShift e.1 e.2 = x)}

open Classical in
noncomputable def starPath (x : PeriodicLatticeSite L) (t : ℝ) : Cfg L :=
  fun e => if e ∈ starLinks x then uθ t else 1

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

end AdalyFormal.Round12.Noncancel.Path

namespace AdalyFormal.Round12.Noncancel.RightFamily
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round12.Noncancel.Path

noncomputable def rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) :
    ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  starPath (periodicLatticeShift (rightSite hq R) 0)

theorem rightStar_off_exterior {q : ℕ} (hq : 0 < q) (R : ℕ) (t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    rightStar hq R t e = 1 :=
  starPath_off_exterior _ _ (rightSite_bd hq R).hx' (rightSite_bd hq R).trans t e he

end AdalyFormal.Round12.Noncancel.RightFamily

namespace AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.IngredientFamilyR2

abbrev TwistSpace (q R : ℕ) : Type := ↥(bondSupp (geomOf 2 1 (dilTower q R)))
end AdalyFormal.Round9.Guarded.AnalyticR1

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
  show ⟪((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) x, y⟫ =
    ⟪x, ((pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G))) y⟫
  simp only [ContinuousLinearMap.comp_apply]
  rw [pE_inner_left, pE_inner_right]
  exact DpiFullS_symm sD P.G P.U P.a _ _

end Ops
end Selectors
end AdalyFormal.Round2.Guarded.Pin

namespace AdalyFormal.Round9.Guarded.Qualitative
open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

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

noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

theorem vacA_rightStar {q : ℕ} (hq : 0 < q) (R : ℕ) (a t : ℝ) :
    vacA q R (AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R) a t =
      (AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R)
          (AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R t) a (dilLam q R))).Ginv := by
  unfold vacA pathA pathP
  have hmask : pathU q R (AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R)
      (fun _ => 0) 0 t = AdalyFormal.Round12.Noncancel.RightFamily.rightStar hq R t := by
    funext e
    by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
    · simp [pathU, maskedU, he]
    · rw [AdalyFormal.Round12.Noncancel.RightFamily.rightStar_off_exterior hq R t e he]
      simp [pathU, maskedU, he, AdalyFormal.StatementLane2.Ug_zero]
  rw [hmask]
  rfl

end AdalyFormal.Round9.Guarded.Qualitative

namespace AdalyFormal.Round9.Guarded.QualitativeR2
open Set
open AdalyFormal.Target.ClayStatement
open AdalyFormal.D1Literal (PSD)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def psdEdge (A : ℝ → E →L[ℝ] E) (t₀ t₁ : ℝ) : ℝ :=
  sSup {t | t ∈ Icc t₀ t₁ ∧ ∀ s ∈ Icc t₀ t, PSD (A s)}

noncomputable def vacEdge (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) : ℝ :=
  psdEdge (vacA q R V 1) 0 Real.pi

noncomputable def rotGauge {L : PeriodicLatticeExtent} (α : ℝ) : GaugeFn L :=
  fun _ => AdalyFormal.D1Literal.uθ α

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

def KernelLine (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (u₀ : TwistSpace q R) : Prop :=
  u₀ ≠ 0 ∧ vacA q R V 1 (vacEdge q R V) u₀ = 0 ∧
  adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R))
    (adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀) = -u₀ ∧
  (∀ u, vacA q R V 1 (vacEdge q R V) u = 0 →
    u ∈ Submodule.span ℝ {u₀,
      adEL (rotGauge (Real.pi / 4)) (geomOf 2 1 (dilTower q R)) u₀})

end AdalyFormal.Round10.Assembly.R2


namespace AdalyFormal.Round10.Nonvanishing.DilatedFlux

open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round4.Guarded.RefuteR1

abbrev L (q R : ℕ) := scaleUp 2 1 (dilLu q R)
abbrev G (q R : ℕ) := geomOf 2 1 (dilTower q R)

end AdalyFormal.Round10.Nonvanishing.DilatedFlux

namespace AdalyFormal.Round15.Dictionary.Physical

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLaneR8
open AdalyFormal.StatementLaneR6
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators
  (SuTwo BondFnL2 RMap RMap_one curlValueCovariant gradValueCovariant)
open AdalyFormal.Balaban.DeltaKFull (curlCovariantLM_L2)
open AdalyFormal.Balaban.CStarDeltaKCOperator (curlCovariantLM_L2_toLp)
open AdalyFormal.Balaban.DeltaPrimeOperator
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CoarseCurl (coarseShift coarseShift_val_eq coarseShift_apply_ne)
open AdalyFormal.Balaban.LineIntegralCovariant (lineCoarseRestrictSuTwo)
open AdalyFormal.Balaban.QOne (pathSite)
open AdalyFormal.Balaban.ReparamCDisjoint (pathSite_apply_self_val pathSite_apply_ne)
open AdalyFormal.GenuineU1
open AdalyFormal.Balaban.CovariantHjMinimizer
  (periodicLatticeShiftBack periodicLatticeShift_shiftBack periodicLatticeShiftBack_shift
    gradCovariantAdjointValue)
open AdalyFormal.Balaban.SuTwoInner
  (pauliE1 pauliE2 hsInner_e1_e1 hsInner_e2_e2 hsInner_e1_e2 hsInner_e1_e3 hsInner_e2_e3
    inner_eq_hsInner)
open AdalyFormal.D1Literal
open AdalyFormal.D1Guarded
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round9.Guarded.AnalyticR1
open AdalyFormal.Round9.Guarded.Qualitative
open AdalyFormal.Round9.Guarded.QualitativeR2
open AdalyFormal.Round10.Nonvanishing.DilatedFlux
open AdalyFormal.Round12.Noncancel.RightFamily

/-- The physical two-level tower geometry used below. -/
abbrev qG : TowerGeom (L 1 20) := geomOf 2 1 (dilTower 1 20)

/-- One physical site on the eight-by-eight transverse torus. -/
noncomputable def q1Site (x : Fin (12*1*20+16)) (y z : Fin 8) :
    PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) :=
  Function.update (Function.update (Function.update
    (rightSite (q := 1) (by norm_num) 20) 0 x) 1 y) 2 z

@[simp] theorem q1Site_zero (x : Fin (12*1*20+16)) (y z : Fin 8) :
    (q1Site x y z) 0 = x := by simp [q1Site]

@[simp] theorem q1Site_one (x : Fin (12*1*20+16)) (y z : Fin 8) :
    (q1Site x y z) 1 = y := by simp [q1Site]

@[simp] theorem q1Site_two (x : Fin (12*1*20+16)) (y z : Fin 8) :
    (q1Site x y z) 2 = z := by simp [q1Site]

theorem q1Site_shift_zero (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShift (q1Site x y z) 0 = q1Site (x + 1) y z := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShift, q1Site] <;> rfl

theorem q1Site_shift_one (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShift (q1Site x y z) 1 = q1Site x (y + 1) z := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShift, q1Site] <;> rfl

theorem q1Site_shift_two (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShift (q1Site x y z) 2 = q1Site x y (z + 1) := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShift, q1Site] <;> rfl

theorem q1Site_shiftBack_zero (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShiftBack (q1Site x y z) 0 = q1Site (x - 1) y z := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShiftBack, q1Site] <;> rfl

theorem q1Site_shiftBack_one (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShiftBack (q1Site x y z) 1 = q1Site x (y - 1) z := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShiftBack, q1Site] <;> rfl

theorem q1Site_shiftBack_two (x : Fin (12*1*20+16)) (y z : Fin 8) :
    periodicLatticeShiftBack (q1Site x y z) 2 = q1Site x y (z - 1) := by
  ext μ
  fin_cases μ <;> simp [periodicLatticeShiftBack, q1Site] <;> rfl

theorem q1Site_ne_of_x {x x' : Fin (12*1*20+16)} {y z y' z' : Fin 8}
    (h : x ≠ x') : q1Site x y z ≠ q1Site x' y' z' := by
  intro he
  apply h
  have hc := congrArg (fun w : PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) => w 0) he
  simpa [scaleUp, dilLu] using hc

theorem q1Site_ne_of_y {x x' : Fin (12*1*20+16)} {y z y' z' : Fin 8}
    (h : y ≠ y') : q1Site x y z ≠ q1Site x' y' z' := by
  intro he
  apply h
  have hc := congrArg (fun w : PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) => w 1) he
  simpa [scaleUp, dilLu] using hc

theorem q1Site_ne_of_z {x x' : Fin (12*1*20+16)} {y z y' z' : Fin 8}
    (h : z ≠ z') : q1Site x y z ≠ q1Site x' y' z' := by
  intro he
  apply h
  have hc := congrArg (fun w : PeriodicLatticeSite (scaleUp 2 1 (dilLu 1 20)) => w 2) he
  simpa [scaleUp, dilLu] using hc

theorem q1_om0_mem (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 4 ≤ x.val) (hx' : x.val < 252) : q1Site x y z ∈ (dilTower 1 20).Om 0 := by
  change 4 ≤ x.val ∧ x.val < 252
  exact ⟨hx, hx'⟩

theorem q1_not_om1 (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 212 ≤ x.val) : q1Site x y z ∉ (dilTower 1 20).Om 1 := by
  change ¬ (44 ≤ x.val ∧ x.val < 212)
  omega

theorem q1_lam0_mem (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 212 ≤ x.val) (hx' : x.val < 252) :
    q1Site x y z ∈ qG.Lam 0 := by
  refine ⟨?_, q1_om0_mem x y z (by omega) (by omega), q1_not_om1 x y z hx⟩
  intro μ
  simp

theorem q1_nq0_zero (f : SiteL2 (L 1 20)) (hf : f ∈ NQp qG (flatCfg : Cfg (L 1 20))
    ) (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 212 ≤ x.val) (hx' : x.val < 252) :
    (WithLp.ofLp f) (q1Site x y z) = 0 := by
  have h := hf.2 0 (Nat.zero_le _) (q1Site x y z) (q1_lam0_mem x y z hx hx')
  simpa [Qlev_apply, AdalyFormal.Balaban.QjComposite.Qcomposite_zero] using h

theorem q1_nq0_zero_any (f : SiteL2 (L 1 20)) (hf : f ∈ NQp qG (flatCfg : Cfg (L 1 20))
    ) (z : PeriodicLatticeSite (L 1 20))
    (hz0 : 212 ≤ (z 0).val) (hz1 : (z 0).val < 252) :
    (WithLp.ofLp f) z = 0 := by
  have heq : q1Site (z 0) (z 1) (z 2) = z := by
    funext μ
    fin_cases μ <;> simp [q1Site]
  have h := q1_nq0_zero f hf (z 0) (z 1) (z 2) hz0 hz1
  rw [heq] at h
  exact h

/-- The level-zero constraint already vanishes at every deep site, including
its left endpoint at x=213. -/
theorem q1_lap_zero (f : SiteL2 (L 1 20)) (hf : f ∈ NQp qG (flatCfg : Cfg (L 1 20))
    ) (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 213 ≤ x.val) (hx' : x.val ≤ 250) :
    (WithLp.ofLp (lapDir qG (flatCfg : Cfg (L 1 20)) f)) (q1Site x y z) = 0 := by
  have hball : ∀ w ∈ Ball (q1Site x y z) 1, (WithLp.ofLp (siteMask qG.Om0 f)) w = 0 := by
    intro w hw
    have hw0 : 212 ≤ (w 0).val := by
      have hnon : ∀ μ : Fin 3, 0 ≤ pcd (scaleUp 2 1 (dilLu 1 20) μ + 1) ((q1Site x y z μ).val) ((w μ).val) := by
        intro μ
        unfold pcd
        omega
      have hnon0 := hnon 0
      have hnon1 := hnon 1
      have hnon2 := hnon 2
      change pdist (q1Site x y z) w ≤ 1 at hw
      unfold pdist at hw
      rw [Fin.sum_univ_three] at hw
      simp only [q1Site_zero] at *
      unfold pcd at hw
      by_cases hle : x.val ≤ (w 0).val
      · rw [if_pos hle] at hw
        simp only [scaleUp, dilLu] at hw
        norm_num at hw
        rcases min_choice ((w 0).val - x.val) (256 - ((w 0).val - x.val)) with hm | hm <;>
          rw [hm] at hw <;> omega
      · rw [if_neg hle] at hw
        simp only [scaleUp, dilLu] at hw
        norm_num at hw
        rcases min_choice (x.val - (w 0).val) (256 - (x.val - (w 0).val)) with hm | hm <;>
          rw [hm] at hw <;> omega
    by_cases hw0' : (w 0).val < 252
    · rw [siteMask_apply, if_pos (show w ∈ qG.Om0 from q1_om0_mem (w 0) (w 1) (w 2) (by omega) (by omega))]
      exact q1_nq0_zero_any f hf w hw0 hw0'
    · have hnot : w ∉ qG.Om0 := by
        intro hmem
        exact hw0' hmem.2
      rw [siteMask_apply, if_neg hnot]
  unfold lapDir
  simp only [ContinuousLinearMap.comp_apply, siteMask_apply]
  rw [if_pos (show q1Site x y z ∈ qG.Om0 from q1_om0_mem x y z (by omega) (by omega))]
  exact lapFull_zero_of_ball _ _ _ hball

theorem q1_RImage_zero (v : SiteL2 (L 1 20)) (hv : v ∈ RImage qG (flatCfg : Cfg (L 1 20))
    ) (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 213 ≤ x.val) (hx' : x.val ≤ 250) :
    (WithLp.ofLp v) (q1Site x y z) = 0 := by
  obtain ⟨f, hf, rfl⟩ := hv
  exact q1_lap_zero f hf x y z hx hx'

theorem q1_Rproj_zero (f : SiteL2 (L 1 20)) (x : Fin (12*1*20+16)) (y z : Fin 8)
    (hx : 213 ≤ x.val) (hx' : x.val ≤ 250) :
    (WithLp.ofLp (Rproj qG (flatCfg : Cfg (L 1 20)) f)) (q1Site x y z) = 0 := by
  apply q1_RImage_zero _ (Submodule.starProjection_apply_mem _ _) x y z hx hx'

theorem q1_pcd_left {a b : ℕ} (ha : a ≤ 42) (hb : 44 ≤ b) (hb' : b < 212) :
    2 ≤ pcd 256 a b := by
  unfold pcd
  rw [if_pos (by omega : a ≤ b)]
  rcases min_choice (b - a) (256 - (b - a)) with h | h <;> rw [h] <;> omega

theorem q1_pcd_right {a b : ℕ} (ha : 213 ≤ a) (haN : a < 256)
    (hb : 44 ≤ b) (hb' : b < 212) :
    2 ≤ pcd 256 a b := by
  unfold pcd
  rw [if_neg (by omega : ¬ a ≤ b)]
  rcases min_choice (a - b) (256 - (a - b)) with h | h <;> rw [h] <;> omega

/-- The range of R is supported in the one-site enlargement of Omega_1. -/
theorem q1_RImage_zero_of_far (v : SiteL2 (L 1 20))
    (hv : v ∈ RImage qG (flatCfg : Cfg (L 1 20)))
    (z : PeriodicLatticeSite (L 1 20))
    (hz : ¬ (43 ≤ (z 0).val ∧ (z 0).val ≤ 212)) :
    (WithLp.ofLp v) z = 0 := by
  apply RImage_support (dilTower 1 20) (flatCfg : Cfg (L 1 20)) hv z
  intro y hy hy1
  change pdist z y ≤ 1 at hy
  change 44 ≤ (y 0).val ∧ (y 0).val < 212 at hy1
  have hcoord : 2 ≤ pcd 256 (z 0).val (y 0).val := by
    by_cases hleft : (z 0).val < 43
    · exact q1_pcd_left (by omega) hy1.1 hy1.2
    · have hzN : (z 0).val < 256 := by
        have hfin := (z 0).isLt
        norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hfin
        exact hfin
      exact q1_pcd_right (by omega) hzN hy1.1 hy1.2
  have hle := zero_coord_le_pdist z y
  norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hle
  omega

theorem q1_shift0_deep (e : Bond (L 1 20)) (he : 213 ≤ (e.1 0).val) :
    (periodicLatticeShift e.1 e.2 0).val = 0 ∨
      213 ≤ (periodicLatticeShift e.1 e.2 0).val := by
  rw [dil_shift_zero (by norm_num) 20 e.1 e.2]
  split_ifs with hd
  · by_cases hlast : (e.1 0).val = 255
    · have hval : (e.1 0).val + 1 = 256 := by omega
      rw [hval, Nat.mod_self]
      exact Or.inl rfl
    · have hlt : (e.1 0).val + 1 < 256 := by
        have hfin := (e.1 0).isLt
        norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hfin
        omega
      rw [Nat.mod_eq_of_lt hlt]
      exact Or.inr (by omega)
  · exact Or.inr he

theorem q1_gradAdj_sing_support {L : PeriodicLatticeExtent}
    (U : Cfg L) (e : Bond L) (X : SuTwo)
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

theorem q1_gradAdj_sing_zero_of_mid (e : Bond (L 1 20)) (X : SuTwo)
    (he : 213 ≤ (e.1 0).val) (z : PeriodicLatticeSite (L 1 20))
    (hz : 43 ≤ (z 0).val ∧ (z 0).val ≤ 212) :
    (WithLp.ofLp (gradAdj (flatCfg : Cfg (L 1 20)) (sing e X))) z = 0 := by
  apply q1_gradAdj_sing_support (flatCfg : Cfg (L 1 20)) e X z
  · intro h
    have hc := congrArg (fun w : PeriodicLatticeSite (L 1 20) => (w 0).val) h
    omega
  · intro h
    have hc := congrArg (fun w : PeriodicLatticeSite (L 1 20) => (w 0).val) h
    have hs := q1_shift0_deep e he
    rcases hs with hs | hs <;> omega

theorem q1_plaq_base_not_om1 {p : PeriodicLatticePlaquette (L 1 20)}
    {e b : Bond (L 1 20)}
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hb : b ∈ periodicPlaquetteBoundaryEdges p)
    (hdeep : 213 ≤ (e.1 0).val) : b.1 ∉ (dilTower 1 20).Om 1 := by
  change ¬ (44 ≤ (b.1 0).val ∧ (b.1 0).val < 212)
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he hb
  have hfin := (p.1 0).isLt
  norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hfin
  have hshift (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
      ((periodicLatticeShift x μ) 0).val =
        if μ = 0 then ((x 0).val + 1) % 256 else (x 0).val := by
    simpa using dil_shift_zero (q := 1) (by norm_num) 20 x μ
  rcases he with he | he | he | he <;> rcases hb with hb | hb | hb | hb <;>
    subst e <;> subst b <;>
    by_cases hμ : p.2.1.1 = 0 <;> by_cases hν : p.2.1.2 = 0 <;>
    simp [hshift, hμ, hν,
      AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at * <;> omega

theorem q1_plaq_shift_not_om1 {p : PeriodicLatticePlaquette (L 1 20)}
    {e b : Bond (L 1 20)}
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hb : b ∈ periodicPlaquetteBoundaryEdges p)
    (hdeep : 213 ≤ (e.1 0).val) :
    periodicLatticeShift b.1 b.2 ∉ (dilTower 1 20).Om 1 := by
  change ¬ (44 ≤ (periodicLatticeShift b.1 b.2 0).val ∧
    (periodicLatticeShift b.1 b.2 0).val < 212)
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he hb
  have hfin := (p.1 0).isLt
  norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hfin
  have hshift (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
      ((periodicLatticeShift x μ) 0).val =
        if μ = 0 then ((x 0).val + 1) % 256 else (x 0).val := by
    simpa using dil_shift_zero (q := 1) (by norm_num) 20 x μ
  rcases he with he | he | he | he <;> rcases hb with hb | hb | hb | hb <;>
    subst e <;> subst b <;>
    by_cases hμ : p.2.1.1 = 0 <;> by_cases hν : p.2.1.2 = 0 <;>
    simp [hshift, hμ, hν,
      AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at * <;> omega

theorem q1_Rproj_gradAdj_sing_zero (e : Bond (L 1 20)) (X : SuTwo)
    (he : 213 ≤ (e.1 0).val) :
    Rproj qG (flatCfg : Cfg (L 1 20)) (gradAdj (flatCfg : Cfg (L 1 20)) (sing e X)) = 0 := by
  unfold Rproj
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro v hv
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : 43 ≤ (z 0).val ∧ (z 0).val ≤ 212
  · rw [q1_gradAdj_sing_zero_of_mid e X he z hz]
    simp
  · rw [q1_RImage_zero_of_far v hv z hz]
    simp

/-- The dressing is exactly trivial on every deep single-bond test field. -/
theorem q1_Wop_sing (e : Bond (L 1 20)) (X : SuTwo)
    (he : 213 ≤ (e.1 0).val) :
    Wop qG (flatCfg : Cfg (L 1 20)) 1 (sing e X) = sing e X := by
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [q1_Rproj_gradAdj_sing_zero e X he]
  simp

noncomputable def q1Plaq (x : PeriodicLatticeSite (L 1 20)) (μ ν : Fin 3)
    (h : μ < ν) : PeriodicLatticePlaquette (L 1 20) :=
  (x, ⟨(μ, ν), h⟩)

noncomputable def q1Plaquettes (e : Bond (L 1 20)) :
    Finset (PeriodicLatticePlaquette (L 1 20)) :=
  if e.2 = 0 then
    {q1Plaq e.1 0 1 (by decide), q1Plaq (periodicLatticeShiftBack e.1 1) 0 1 (by decide),
      q1Plaq e.1 0 2 (by decide), q1Plaq (periodicLatticeShiftBack e.1 2) 0 2 (by decide)}
  else if e.2 = 1 then
    {q1Plaq e.1 0 1 (by decide), q1Plaq (periodicLatticeShiftBack e.1 0) 0 1 (by decide),
      q1Plaq e.1 1 2 (by decide), q1Plaq (periodicLatticeShiftBack e.1 2) 1 2 (by decide)}
  else
    {q1Plaq e.1 0 2 (by decide), q1Plaq (periodicLatticeShiftBack e.1 0) 0 2 (by decide),
      q1Plaq e.1 1 2 (by decide), q1Plaq (periodicLatticeShiftBack e.1 1) 1 2 (by decide)}

theorem q1_shiftBack_right (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
    x = periodicLatticeShiftBack (periodicLatticeShift x μ) μ :=
  (periodicLatticeShiftBack_shift _ _).symm

theorem q1_shift_ne (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
    periodicLatticeShift x μ ≠ x :=
  AdalyFormal.Balaban.RegularUCurvedWitness.shift_ne_self x μ (by
    fin_cases μ <;> norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu])

theorem q1_shiftBack_ne (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
    periodicLatticeShiftBack x μ ≠ x :=
  AdalyFormal.Balaban.RegularityGap.shiftBack_ne_self x μ (by
    fin_cases μ <;> norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu])

theorem q1_shiftBack_ne_rev (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
    x ≠ periodicLatticeShiftBack x μ := (q1_shiftBack_ne x μ).symm

theorem q1_shift_ite (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) (X : SuTwo) :
    (if periodicLatticeShift x μ = x then X else 0) = 0 :=
  if_neg (q1_shift_ne x μ)

theorem q1_shiftBack_ite (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) (X : SuTwo) :
    (if periodicLatticeShiftBack x μ = x then X else 0) = 0 :=
  if_neg (q1_shiftBack_ne x μ)

theorem q1_inner_shift_zero (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3)
    (X Y : SuTwo) :
    inner ℝ (if periodicLatticeShift x μ = x then X else 0) Y = 0 := by
  rw [if_neg (q1_shift_ne x μ), inner_zero_left]

theorem q1_inner_shiftBack_zero (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3)
    (X Y : SuTwo) :
    inner ℝ (if periodicLatticeShiftBack x μ = x then X else 0) Y = 0 := by
  rw [if_neg (q1_shiftBack_ne x μ), inner_zero_left]

theorem q1Plaq_shift_ne (x : PeriodicLatticeSite (L 1 20)) (μ ν : Fin 3)
    (h : μ < ν) :
    q1Plaq (periodicLatticeShiftBack x μ) μ ν h ≠ q1Plaq x μ ν h := by
  have hL : 1 ≤ (L 1 20) μ := by
    fin_cases μ <;> norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu]
  intro he
  exact (AdalyFormal.Balaban.RegularityGap.shiftBack_ne_self x μ hL) (congrArg Prod.fst he)

theorem q1Plaq_shiftBase_ne (x : PeriodicLatticeSite (L 1 20)) (κ μ ν : Fin 3)
    (h : μ < ν) :
    q1Plaq (periodicLatticeShiftBack x κ) μ ν h ≠ q1Plaq x μ ν h := by
  intro he
  exact q1_shiftBack_ne x κ (congrArg Prod.fst he)

theorem q1Plaq_shiftBase_ne_rev (x : PeriodicLatticeSite (L 1 20)) (κ μ ν : Fin 3)
    (h : μ < ν) :
    q1Plaq x μ ν h ≠ q1Plaq (periodicLatticeShiftBack x κ) μ ν h :=
  (q1Plaq_shiftBase_ne x κ μ ν h).symm

theorem q1_mem_plaquettes_of_boundary {e : Bond (L 1 20)}
    {p : PeriodicLatticePlaquette (L 1 20)}
    (he : e ∈ periodicPlaquetteBoundaryEdges p) : p ∈ q1Plaquettes e := by
  rcases e with ⟨z, d⟩
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he
  fin_cases d <;> fin_cases μ <;> fin_cases ν <;>
    simp_all [q1Plaquettes, q1Plaq, q1_shiftBack_right,
      periodicLatticeShift_shiftBack, periodicLatticeShiftBack_shift] <;> aesop
  all_goals exact Or.inr (periodicLatticeShiftBack_shift _ _).symm

theorem q1_curl_apply_flat (A : BondFnL2 (L 1 20))
    (p : PeriodicLatticePlaquette (L 1 20)) :
    (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) A) p =
      curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp A) p := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl, curlCovariantLM_L2_toLp]

theorem q1_curl_sing_zero_of_not_mem (e : Bond (L 1 20)) (X : SuTwo)
    (p : PeriodicLatticePlaquette (L 1 20)) (hp : p ∉ q1Plaquettes e) :
    curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp (sing e X)) p = 0 := by
  unfold curlValueCovariant
  have hs (b : Bond (L 1 20)) (hb : b ∈ periodicPlaquetteBoundaryEdges p) :
      (WithLp.ofLp (sing e X)) b = 0 :=
    sing_apply_ne _ _ (fun h => hp (q1_mem_plaquettes_of_boundary (h ▸ hb)))
  have h1 := hs (p.1, p.2.1.1) (by simp [periodicPlaquetteBoundaryEdges])
  have h2 := hs (periodicLatticeShift p.1 p.2.1.1, p.2.1.2)
    (by simp [periodicPlaquetteBoundaryEdges])
  have h3 := hs (periodicLatticeShift p.1 p.2.1.2, p.2.1.1)
    (by simp [periodicPlaquetteBoundaryEdges])
  have h4 := hs (p.1, p.2.1.2) (by simp [periodicPlaquetteBoundaryEdges])
  rw [h1, h2, h3, h4]
  simp

theorem q1_deltaPrime_flat_zero (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo) :
    deltaPrimeBilL2NormLoc (flatCfg : Cfg (L 1 20)) Set.univ (sing e X) A = 0 := by
  have hop : deltaPrimeOpLoc (flatCfg : Cfg (L 1 20)) Set.univ = 0 := by
    rw [deltaPrimeOpLoc_univ, deltaPrimeOpNormalized_eq_half_smul,
      show (flatCfg : Cfg (L 1 20)) = AdalyFormal.Balaban.DeltaPrime.trivialU from rfl,
      deltaPrimeOp_trivialU]
    simp
  rw [← inner_deltaPrimeOpLoc (flatCfg : Cfg (L 1 20)) Set.univ (sing e X) A, hop]
  simp

theorem q1_flat_Delta_inner (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo) :
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) A) =
      ∑ p ∈ q1Plaquettes e,
        inner ℝ (curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp (sing e X)) p)
          (curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp A) p) := by
  unfold AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll
  rw [inner_deltaKLocCLM]
  rw [q1_deltaPrime_flat_zero, plaqMask_univ, plaqMask_univ, add_zero, PiLp.inner_apply]
  simp only [q1_curl_apply_flat]
  set f : PeriodicLatticePlaquette (L 1 20) → ℝ := fun p =>
    inner ℝ (curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp (sing e X)) p)
      (curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp A) p) with hf
  symm
  apply Finset.sum_subset (Finset.subset_univ (q1Plaquettes e))
  intro p _ hp
  have hz := q1_curl_sing_zero_of_not_mem e X p hp
  simp only [f] at *
  simp only [hz, inner_zero_left]

theorem q1_inner_e1_self : inner ℝ pauliE1 pauliE1 = 1 := by
  rw [inner_eq_hsInner]
  exact hsInner_e1_e1

theorem q1_inner_e1_e2 : inner ℝ pauliE1 pauliE2 = 0 := by
  rw [inner_eq_hsInner]
  exact hsInner_e1_e2

theorem q1_inner_e1_e3 : inner ℝ pauliE1 AdalyFormal.Balaban.SuTwoInner.pauliE3 = 0 := by
  rw [inner_eq_hsInner]
  exact hsInner_e1_e3

theorem q1_inner_e2_self : inner ℝ pauliE2 pauliE2 = 1 := by
  rw [inner_eq_hsInner]
  exact hsInner_e2_e2

theorem q1_inner_e2_e1 : inner ℝ pauliE2 pauliE1 = 0 := by
  rw [inner_eq_hsInner, AdalyFormal.Balaban.SuTwoInner.hsInner_symm]
  exact hsInner_e1_e2

theorem q1_inner_e2_e3 : inner ℝ pauliE2 AdalyFormal.Balaban.SuTwoInner.pauliE3 = 0 := by
  rw [inner_eq_hsInner]
  exact hsInner_e2_e3

theorem q1_inner_e1_entry (A : SuTwo) :
    inner ℝ pauliE1 A = ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im := by
  conv_lhs => rw [AdalyFormal.Balaban.SuTwoInner.suTwo_decompose A]
  simp only [inner_add_right, inner_smul_right, q1_inner_e1_self,
    q1_inner_e1_e2, q1_inner_e1_e3]
  ring

theorem q1_inner_e2_entry (A : SuTwo) :
    inner ℝ pauliE2 A = ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re := by
  have h21 : inner ℝ pauliE2 pauliE1 = 0 := by
    rw [real_inner_comm]
    exact hsInner_e1_e2
  conv_lhs => rw [AdalyFormal.Balaban.SuTwoInner.suTwo_decompose A]
  simp only [inner_add_right, inner_smul_right, q1_inner_e2_self,
    h21, q1_inner_e2_e3]
  ring

/-- The four cells in one transverse fundamental domain. -/
noncomputable def q1Cell (a : Fin 4) : Fin 8 × Fin 8 :=
  ![(0,0),(1,0),(0,1),(1,1)] a

/-- The complex charged coordinate of a physical bond field. -/
noncomputable def q1Value (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) : ℂ :=
  (inner ℝ pauliE2 (WithLp.ofLp A e) : ℂ) +
    (inner ℝ pauliE1 (WithLp.ofLp A e) : ℂ) * Complex.I

/-- The `(1,0)` character phase on the four translates of the two-site fundamental cell. -/
noncomputable def q1Phase10 (y : Fin 8) : ℂ :=
  ![1, 1, Complex.I, Complex.I, -1, -1, -Complex.I, -Complex.I] y

/-- Exact membership in the `(1,0)` transverse character sector.
The four-cell layer samples the fundamental cell; this predicate supplies the
phase relations for all the other physical transverse sites. -/
def q1Character10 (A : BondFnL2 (L 1 20)) : Prop :=
  ∀ (x : Fin (12*1*20+16)) (y z : Fin 8) (d : Fin 3),
    q1Value A (q1Site x y z, d) = q1Phase10 y *
      q1Value A (q1Site x ⟨y.val % 2, by omega⟩ ⟨z.val % 2, by omega⟩, d)

theorem q1Character10_e1 (A : BondFnL2 (L 1 20)) (hA : q1Character10 A)
    (x : Fin (12*1*20+16)) (y z : Fin 8) (d : Fin 3) :
    inner ℝ pauliE1 (WithLp.ofLp A (q1Site x y z, d)) =
      (q1Phase10 y * q1Value A (q1Site x ⟨y.val % 2, by omega⟩
        ⟨z.val % 2, by omega⟩, d)).im := by
  have h := congrArg Complex.im (hA x y z d)
  simpa [q1Value] using h

theorem q1Character10_e2 (A : BondFnL2 (L 1 20)) (hA : q1Character10 A)
    (x : Fin (12*1*20+16)) (y z : Fin 8) (d : Fin 3) :
    inner ℝ pauliE2 (WithLp.ofLp A (q1Site x y z, d)) =
      (q1Phase10 y * q1Value A (q1Site x ⟨y.val % 2, by omega⟩
        ⟨z.val % 2, by omega⟩, d)).re := by
  have h := congrArg Complex.re (hA x y z d)
  simpa [q1Value] using h

noncomputable def q1Layer12 (A : BondFnL2 (L 1 20)) (x : Fin (12*1*20+16)) : Fin 12 → ℂ :=
  fun i =>
    let a : Fin 4 := ⟨i.val % 4, by omega⟩
    let d : Fin 3 := ⟨i.val / 4, by omega⟩
    let yz : Fin 8 × Fin 8 := q1Cell a
    q1Value A (q1Site x yz.1 yz.2, d)

noncomputable def q1LayerDir0 (A : BondFnL2 (L 1 20)) (x : Fin (12*1*20+16)) : Fin 4 → ℂ :=
  fun a => q1Layer12 A x ⟨a.val, by omega⟩

noncomputable def q1Layer (A : BondFnL2 (L 1 20)) (x : Fin (12*1*20+16)) : Fin 8 → ℂ :=
  fun i => q1Layer12 A x ⟨i.val + 4, by omega⟩

noncomputable def q1Eval (X : SuTwo) (i : Fin 12) (z : Fin 12 → ℂ) : ℝ :=
  if X = pauliE1 then (z i).im else (z i).re

theorem q1_inner_sing0 (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo) :
    inner ℝ (sing e X) A = inner ℝ X (A e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e]
  · rw [sing_apply_self]
  · intro b hb hne
    rw [sing_apply_ne _ _ hne]
    simp
  · simp

/-- The raw twelve-component physical stencil in the `(1,0)` character sector. -/
theorem q1_raw_stencil (A : BondFnL2 (L 1 20)) (hA : q1Character10 A)
    (x : Fin (12*1*20+16)) (a : Fin 4) (d : Fin 3) (X : SuTwo)
    (hX : X = pauliE1 ∨ X = pauliE2) :
    inner ℝ (sing (q1Site x (q1Cell a).1 (q1Cell a).2, d) X)
        (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) A) +
      inner ℝ (sing (q1Site x (q1Cell a).1 (q1Cell a).2, d) X) A =
      q1Eval X ⟨4*d.val+a.val, by omega⟩
        ((Matrix.mulVec q1Kminus (q1Layer12 A (x-1)) +
          Matrix.mulVec q1Kzero (q1Layer12 A x) +
          Matrix.mulVec q1Kplus (q1Layer12 A (x+1))) : Fin 12 → ℂ) := by
  rcases hX with rfl | rfl <;>
    fin_cases a <;> fin_cases d <;>
    rw [q1_flat_Delta_inner] <;>
    simp [q1Plaquettes, q1Plaq, q1Cell, q1Layer12, q1Eval, q1Kplus, q1Kzero, q1Kminus,
      Finset.sum_insert, Finset.sum_singleton, q1Plaq_shiftBase_ne, q1Plaq_shiftBase_ne_rev,
      q1_shiftBack_ne, q1_shiftBack_ne_rev, curlValueCovariant,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, inner_add_right, inner_sub_right,
      inner_smul_right, periodicLatticeShift_shiftBack, periodicLatticeShiftBack_shift,
      flatCfg, RMap_one, q1Site_shift_zero, q1Site_shift_one, q1Site_shift_two,
      q1Site_shiftBack_zero, q1Site_shiftBack_one, q1Site_shiftBack_two,
      q1_shift_ne, q1Site_ne_of_x, q1Site_ne_of_y, q1Site_ne_of_z,
      q1Character10_e1 A hA, q1Character10_e2 A hA, q1Phase10,
      q1_inner_sing0, sing_apply_self, sing_apply_ne,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;>
    norm_num <;>
    ring_nf <;> try simp only [pow_two, Complex.I_mul_I] <;> ring

theorem q1_curl_apply (A : BondFnL2 (L 1 20))
    (p : PeriodicLatticePlaquette (L 1 20)) :
    (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) A) p =
      curlValueCovariant (flatCfg : Cfg (L 1 20)) (WithLp.ofLp A) p := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl, curlCovariantLM_L2_toLp]

theorem deltaPrime_norm_of_raw {L' : PeriodicLatticeExtent}
    (U : Cfg L') (P : Set (PeriodicLatticePlaquette L'))
    (A B : BondFnL2 L') (e : Bond L') (X : SuTwo)
    (hraw1 : deltaPrimeBilRawLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
      deltaPrimeBilRawLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp B))
    (hraw2 : deltaPrimeBilRawLoc U P (WithLp.ofLp A) (WithLp.ofLp (sing e X)) =
      deltaPrimeBilRawLoc U P (WithLp.ofLp B) (WithLp.ofLp (sing e X))) :
    deltaPrimeBilL2NormLoc U P (sing e X) A = deltaPrimeBilL2NormLoc U P (sing e X) B := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl,
    show B = WithLp.toLp 2 (WithLp.ofLp B) from rfl]
  show deltaPrimeBilNormLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
    deltaPrimeBilNormLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp B)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [hraw1, hraw2]

/-- The exact dressing potential vanishes outside the first coarse region. -/
theorem potential_zero_off_om1 {L : PeriodicLatticeExtent} {ell k : ℕ} (S : Tower L)
    (U : Cfg L) (a : ℝ) (f : SiteL2 L) {x : PeriodicLatticeSite L} (hx : x ∉ S.Om 1) :
    (Gp (geomOf ell k S) U a (Rproj (geomOf ell k S) U f)) x = 0 := by
  by_cases hx0 : x ∈ S.Om 0
  · apply Gp_Rproj_lam0
    exact ⟨fun μ => by simp, hx0, by simpa using hx⟩
  · exact Gp_Rproj_out _ _ _ _ hx0

/-- W agrees with the original field on bonds whose endpoints avoid Omega_1. -/
theorem Wop_eq_on_collar {L : PeriodicLatticeExtent} {ell k : ℕ} (S : Tower L)
    (U : Cfg L) (a : ℝ) (A : BondFnL2 L) (e : Bond L)
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

/-- Row locality of the full localized Delta operator against a single-bond test. -/
theorem q1_deltaK_row_congr (P : Set (PeriodicLatticePlaquette (L 1 20)))
    (A B : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo)
    (hAB : ∀ p, p ∈ P → e ∈ periodicPlaquetteBoundaryEdges p →
      ∀ b ∈ periodicPlaquetteBoundaryEdges p,
        A b = B b) :
    inner ℝ (sing e X) (deltaKLocCLM (flatCfg : Cfg (L 1 20)) P A) =
      inner ℝ (sing e X) (deltaKLocCLM (flatCfg : Cfg (L 1 20)) P B) := by
  have hcurl :
      inner ℝ (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) (sing e X)))
          (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) A)) =
        inner ℝ (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) (sing e X)))
          (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) B)) := by
    simp only [PiLp.inner_apply, plaqMask_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · simp only [q1_curl_apply]
        have hc := AdalyFormal.Balaban.CStarDeltaKCOperator.curlValueCovariant_congr_on_plaq
          (flatCfg : Cfg (L 1 20))
          (WithLp.ofLp A) (WithLp.ofLp B) p
          (hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]))
          (hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]))
          (hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]))
          (hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]))
        rw [hc]
      · have hs : curlValueCovariant (flatCfg : Cfg (L 1 20))
            (WithLp.ofLp (sing e X)) p = 0 := by
          unfold curlValueCovariant
          have h1 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h2 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h3 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h4 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          rw [h1, h2, h3, h4]
          simp
        simp only [q1_curl_apply, hs]
        simp
    · simp [hp]
  have hraw1 : deltaPrimeBilRawLoc (flatCfg : Cfg (L 1 20)) P
      (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
      deltaPrimeBilRawLoc (flatCfg : Cfg (L 1 20)) P
        (WithLp.ofLp (sing e X)) (WithLp.ofLp B) := by
    rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · have hz : bilPlaq (flatCfg : Cfg (L 1 20)) p (WithLp.ofLp (sing e X))
            (WithLp.ofLp A - WithLp.ofLp B) = 0 := by
          apply bilPlaq_eq_zero_of_right_bonds_zero
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
        rw [map_sub] at hz
        exact sub_eq_zero.mp hz
      · have hs (b : Bond (L 1 20)) (hb : b ∈ periodicPlaquetteBoundaryEdges p) :
            (WithLp.ofLp (sing e X)) b = 0 :=
          sing_apply_ne _ _ (fun h => he (h ▸ hb))
        have hza : bilPlaq (flatCfg : Cfg (L 1 20)) p
            (WithLp.ofLp (sing e X)) (WithLp.ofLp A) = 0 := by
          apply bilPlaq_eq_zero_of_left_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        have hzb : bilPlaq (flatCfg : Cfg (L 1 20)) p
            (WithLp.ofLp (sing e X)) (WithLp.ofLp B) = 0 := by
          apply bilPlaq_eq_zero_of_left_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        rw [hza, hzb]
    · simp [hp]
  have hraw2 : deltaPrimeBilRawLoc (flatCfg : Cfg (L 1 20)) P
      (WithLp.ofLp A) (WithLp.ofLp (sing e X)) =
      deltaPrimeBilRawLoc (flatCfg : Cfg (L 1 20)) P
        (WithLp.ofLp B) (WithLp.ofLp (sing e X)) := by
    rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · have hz : bilPlaq (flatCfg : Cfg (L 1 20)) p
            (WithLp.ofLp A - WithLp.ofLp B) (WithLp.ofLp (sing e X)) = 0 := by
          apply bilPlaq_eq_zero_of_left_bonds_zero
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
          · rw [Pi.sub_apply, hAB p hp he _ (by simp [periodicPlaquetteBoundaryEdges]), sub_self]
        rw [map_sub] at hz
        exact sub_eq_zero.mp hz
      · have hs (b : Bond (L 1 20)) (hb : b ∈ periodicPlaquetteBoundaryEdges p) :
            (WithLp.ofLp (sing e X)) b = 0 :=
          sing_apply_ne _ _ (fun h => he (h ▸ hb))
        have hza : bilPlaq (flatCfg : Cfg (L 1 20)) p
            (WithLp.ofLp A) (WithLp.ofLp (sing e X)) = 0 := by
          apply bilPlaq_eq_zero_of_right_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        have hzb : bilPlaq (flatCfg : Cfg (L 1 20)) p
            (WithLp.ofLp B) (WithLp.ofLp (sing e X)) = 0 := by
          apply bilPlaq_eq_zero_of_right_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        rw [hza, hzb]
    · simp [hp]
  have hnorm : deltaPrimeBilL2NormLoc (flatCfg : Cfg (L 1 20)) P (sing e X) A =
      deltaPrimeBilL2NormLoc (flatCfg : Cfg (L 1 20)) P (sing e X) B :=
    deltaPrime_norm_of_raw (flatCfg : Cfg (L 1 20)) P A B e X hraw1 hraw2
  calc
    inner ℝ (sing e X) (deltaKLocCLM (flatCfg : Cfg (L 1 20)) P A) =
        inner ℝ (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) (sing e X)))
            (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) A)) +
          deltaPrimeBilL2NormLoc (flatCfg : Cfg (L 1 20)) P (sing e X) A :=
      inner_deltaKLocCLM (flatCfg : Cfg (L 1 20)) P (sing e X) A
    _ = inner ℝ (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) (sing e X)))
            (plaqMask P (curlCovariantLM_L2 (flatCfg : Cfg (L 1 20)) B)) +
          deltaPrimeBilL2NormLoc (flatCfg : Cfg (L 1 20)) P (sing e X) B := by
      rw [hcurl, hnorm]
    _ = inner ℝ (sing e X) (deltaKLocCLM (flatCfg : Cfg (L 1 20)) P B) :=
      (inner_deltaKLocCLM (flatCfg : Cfg (L 1 20)) P (sing e X) B).symm

theorem deltaPrime_norm_of_raw_config {L' : PeriodicLatticeExtent}
    (U U' : Cfg L') (P : Set (PeriodicLatticePlaquette L'))
    (A : BondFnL2 L') (e : Bond L') (X : SuTwo)
    (hraw1 : deltaPrimeBilRawLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
      deltaPrimeBilRawLoc U' P (WithLp.ofLp (sing e X)) (WithLp.ofLp A))
    (hraw2 : deltaPrimeBilRawLoc U P (WithLp.ofLp A) (WithLp.ofLp (sing e X)) =
      deltaPrimeBilRawLoc U' P (WithLp.ofLp A) (WithLp.ofLp (sing e X))) :
    deltaPrimeBilL2NormLoc U P (sing e X) A = deltaPrimeBilL2NormLoc U' P (sing e X) A := by
  rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl]
  show deltaPrimeBilNormLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
    deltaPrimeBilNormLoc U' P (WithLp.ofLp (sing e X)) (WithLp.ofLp A)
  unfold deltaPrimeBilNormLoc
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.flip_apply, smul_eq_mul]
  rw [hraw1, hraw2]

/-- Row locality when the background changes only away from the test bond. -/
theorem q1_deltaK_row_congr_config (P : Set (PeriodicLatticePlaquette (L 1 20)))
    (U U' : Cfg (L 1 20)) (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo)
    (hUU : ∀ p, p ∈ P → e ∈ periodicPlaquetteBoundaryEdges p →
      ∀ b ∈ periodicPlaquetteBoundaryEdges p, U b = U' b) :
    inner ℝ (sing e X) (deltaKLocCLM U P A) =
      inner ℝ (sing e X) (deltaKLocCLM U' P A) := by
  have hcurl :
      inner ℝ (plaqMask P (curlCovariantLM_L2 U (sing e X)))
          (plaqMask P (curlCovariantLM_L2 U A)) =
        inner ℝ (plaqMask P (curlCovariantLM_L2 U' (sing e X)))
          (plaqMask P (curlCovariantLM_L2 U' A)) := by
    simp only [PiLp.inner_apply, plaqMask_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · have hc : curlValueCovariant U (WithLp.ofLp A) p =
            curlValueCovariant U' (WithLp.ofLp A) p := by
          apply curlValue_congr (hUU p hp he)
        have hs : curlValueCovariant U (WithLp.ofLp (sing e X)) p =
            curlValueCovariant U' (WithLp.ofLp (sing e X)) p := by
          apply curlValue_congr (hUU p hp he)
        have hca : (curlCovariantLM_L2 U A) p = curlValueCovariant U (WithLp.ofLp A) p := by
          rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl, curlCovariantLM_L2_toLp]
        have hcb : (curlCovariantLM_L2 U' A) p = curlValueCovariant U' (WithLp.ofLp A) p := by
          rw [show A = WithLp.toLp 2 (WithLp.ofLp A) from rfl, curlCovariantLM_L2_toLp]
        have hsa : (curlCovariantLM_L2 U (sing e X)) p =
            curlValueCovariant U (WithLp.ofLp (sing e X)) p := by
          rw [show (sing e X) = WithLp.toLp 2 (WithLp.ofLp (sing e X)) from rfl,
            curlCovariantLM_L2_toLp]
        have hsb : (curlCovariantLM_L2 U' (sing e X)) p =
            curlValueCovariant U' (WithLp.ofLp (sing e X)) p := by
          rw [show (sing e X) = WithLp.toLp 2 (WithLp.ofLp (sing e X)) from rfl,
            curlCovariantLM_L2_toLp]
        rw [hca, hcb, hsa, hsb, hc, hs]
      · have hsU : curlValueCovariant U (WithLp.ofLp (sing e X)) p = 0 := by
          unfold curlValueCovariant
          have h1 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h2 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h3 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h4 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          rw [h1, h2, h3, h4]
          simp
        have hsU' : curlValueCovariant U' (WithLp.ofLp (sing e X)) p = 0 := by
          unfold curlValueCovariant
          have h1 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h2 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h3 : (WithLp.ofLp (sing e X))
              (periodicLatticeShift p.1 p.2.1.2, p.2.1.1) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          have h4 : (WithLp.ofLp (sing e X)) (p.1, p.2.1.2) = 0 :=
            sing_apply_ne _ _ (fun h => he (h ▸ by simp [periodicPlaquetteBoundaryEdges]))
          rw [h1, h2, h3, h4]
          simp
        have hsa : (curlCovariantLM_L2 U (sing e X)) p =
            curlValueCovariant U (WithLp.ofLp (sing e X)) p := by
          rw [show (sing e X) = WithLp.toLp 2 (WithLp.ofLp (sing e X)) from rfl,
            curlCovariantLM_L2_toLp]
        have hsb : (curlCovariantLM_L2 U' (sing e X)) p =
            curlValueCovariant U' (WithLp.ofLp (sing e X)) p := by
          rw [show (sing e X) = WithLp.toLp 2 (WithLp.ofLp (sing e X)) from rfl,
            curlCovariantLM_L2_toLp]
        rw [hsa, hsb, hsU, hsU']
        simp
    · simp [hp]
  have hraw1 : deltaPrimeBilRawLoc U P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) =
      deltaPrimeBilRawLoc U' P (WithLp.ofLp (sing e X)) (WithLp.ofLp A) := by
    rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · rw [bilPlaq_congr (hUU p hp he)]
      · have hs (b : Bond (L 1 20)) (hb : b ∈ periodicPlaquetteBoundaryEdges p) :
            (WithLp.ofLp (sing e X)) b = 0 :=
          sing_apply_ne _ _ (fun h => he (h ▸ hb))
        have hza : bilPlaq U p (WithLp.ofLp (sing e X)) (WithLp.ofLp A) = 0 := by
          apply bilPlaq_eq_zero_of_left_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        have hzb : bilPlaq U' p (WithLp.ofLp (sing e X)) (WithLp.ofLp A) = 0 := by
          apply bilPlaq_eq_zero_of_left_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        rw [hza, hzb]
    · simp [hp]
  have hraw2 : deltaPrimeBilRawLoc U P (WithLp.ofLp A) (WithLp.ofLp (sing e X)) =
      deltaPrimeBilRawLoc U' P (WithLp.ofLp A) (WithLp.ofLp (sing e X)) := by
    rw [deltaPrimeBilRawLoc_apply, deltaPrimeBilRawLoc_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ P
    · simp only [if_pos hp]
      by_cases he : e ∈ periodicPlaquetteBoundaryEdges p
      · rw [bilPlaq_congr (hUU p hp he)]
      · have hs (b : Bond (L 1 20)) (hb : b ∈ periodicPlaquetteBoundaryEdges p) :
            (WithLp.ofLp (sing e X)) b = 0 :=
          sing_apply_ne _ _ (fun h => he (h ▸ hb))
        have hza : bilPlaq U p (WithLp.ofLp A) (WithLp.ofLp (sing e X)) = 0 := by
          apply bilPlaq_eq_zero_of_right_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        have hzb : bilPlaq U' p (WithLp.ofLp A) (WithLp.ofLp (sing e X)) = 0 := by
          apply bilPlaq_eq_zero_of_right_bonds_zero
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
          · exact hs _ (by simp [periodicPlaquetteBoundaryEdges])
        rw [hza, hzb]
    · simp [hp]
  have hnorm : deltaPrimeBilL2NormLoc U P (sing e X) A =
      deltaPrimeBilL2NormLoc U' P (sing e X) A :=
    deltaPrime_norm_of_raw_config U U' P A e X hraw1 hraw2
  calc
    inner ℝ (sing e X) (deltaKLocCLM U P A) =
        inner ℝ (plaqMask P (curlCovariantLM_L2 U (sing e X)))
            (plaqMask P (curlCovariantLM_L2 U A)) +
          deltaPrimeBilL2NormLoc U P (sing e X) A :=
      inner_deltaKLocCLM U P (sing e X) A
    _ = inner ℝ (plaqMask P (curlCovariantLM_L2 U' (sing e X)))
            (plaqMask P (curlCovariantLM_L2 U' A)) +
          deltaPrimeBilL2NormLoc U' P (sing e X) A := by
      rw [hcurl, hnorm]
    _ = inner ℝ (sing e X) (deltaKLocCLM U' P A) :=
      (inner_deltaKLocCLM U' P (sing e X) A).symm

theorem q1_plaq_base_mem_om0 {p : PeriodicLatticePlaquette (L 1 20)}
    {e b : Bond (L 1 20)}
    (he : e ∈ periodicPlaquetteBoundaryEdges p)
    (hb : b ∈ periodicPlaquetteBoundaryEdges p)
    (hdeep : 213 ≤ (e.1 0).val) (hupper : (e.1 0).val ≤ 250) :
    b.1 ∈ (dilTower 1 20).Om 0 := by
  change 4 ≤ (b.1 0).val ∧ (b.1 0).val < 252
  simp only [periodicPlaquetteBoundaryEdges, Finset.mem_insert, Finset.mem_singleton] at he hb
  have hfin := (p.1 0).isLt
  norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hfin
  have hshift (x : PeriodicLatticeSite (L 1 20)) (μ : Fin 3) :
      ((periodicLatticeShift x μ) 0).val =
        if μ = 0 then ((x 0).val + 1) % 256 else (x 0).val := by
    simpa using dil_shift_zero (q := 1) (by norm_num) 20 x μ
  rcases he with he | he | he | he <;> rcases hb with hb | hb | hb | hb <;>
    subst e <;> subst b <;>
    by_cases hμ : p.2.1.1 = 0 <;> by_cases hν : p.2.1.2 = 0 <;>
    simp [hshift, hμ, hν,
      AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at * <;> omega

theorem q1_rightStar_on_boundary (t : ℝ) (e : Bond (L 1 20))
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250)
    (p : PeriodicLatticePlaquette (L 1 20))
    (hep : e ∈ periodicPlaquetteBoundaryEdges p) (b : Bond (L 1 20))
    (hbp : b ∈ periodicPlaquetteBoundaryEdges p) :
    rightStar (q := 1) (by norm_num) 20 t b = (flatCfg : Cfg (L 1 20)) b := by
  have hb0 := q1_plaq_base_mem_om0 hep hbp heDeep heUpper
  have hZb : b ∉ AdalyFormal.D1Literal.Zb ((dilTower 1 20).Om 0) := by
    intro hz
    exact hz.1 hb0
  simpa [flatCfg] using
    (rightStar_off_exterior (q := 1) (by norm_num) 20 t b hZb)

/-- Flat Q rows are the exact block line averages. -/
theorem Qfull_flat_row (G : TowerGeom (L 1 20)) (hell : 0 < G.ell) (J : ℕ)
    (hdvdJ : ∀ ν, G.ell ^ J ∣ (L 1 20) ν + 1)
    (p : BIdx G) (hpJ : (p.1 : ℕ) ≤ J)
    (hc : p.2.1.1 ∈ CoarseLattice (L 1 20) (G.ell ^ (p.1 : ℕ))) (A : BondFnL2 (L 1 20)) :
    (QfullOf G (flatCfg : Cfg (L 1 20)) A) p =
      lineCoarseRestrictSuTwo (G.ell ^ (p.1 : ℕ)) (WithLp.ofLp A)
        ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩ := by
  have hell' : (G.ell : ℝ) ≠ 0 := by exact_mod_cast hell.ne'
  have key := Qcomp_closed G.ell hell (bgTower G (flatCfg : Cfg (L 1 20)))
    (fun j => by unfold bgTower; exact Ubar_flat _ j) J hdvdJ
    (suCoordF (WithLp.ofLp A)) (p.1 : ℕ) hpJ (G.ell ^ (p.1 : ℕ)) rfl
    ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩
  rw [suCoordFInv_suCoordF] at key
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) •
    (WithLp.ofLp (QlinB G (flatCfg : Cfg (L 1 20)) (p.1 : ℕ) A)) p.2.1 = _
  have hQ : (WithLp.ofLp (QlinB G (flatCfg : Cfg (L 1 20)) (p.1 : ℕ) A)) p.2.1 =
      suCoordFInv (QlinCompX G.ell (bgTower G (flatCfg : Cfg (L 1 20))) (p.1 : ℕ)
        (suCoordF (WithLp.ofLp A))) (p.2.1.1, p.2.1.2) := by
    have hb := QlinCompL_eq_QlinCompX G.ell (bgTower G (flatCfg : Cfg (L 1 20))) J
      (fun j _ => by unfold bgTower; rw [Ubar_flat]; exact RegBg_flat _ _) (p.1 : ℕ) hpJ
    rw [← hb]
    rfl
  rw [hQ]
  have key' : suCoordFInv (QlinCompX G.ell (bgTower G (flatCfg : Cfg (L 1 20))) (p.1 : ℕ)
      (suCoordF (WithLp.ofLp A))) (p.2.1.1, p.2.1.2) =
      (((G.ell ^ (p.1 : ℕ) : ℕ) : ℝ)) • lineCoarseRestrictSuTwo (G.ell ^ (p.1 : ℕ))
        (WithLp.ofLp A) ⟨⟨p.2.1.1, hc⟩, p.2.1.2⟩ := key
  rw [key', smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (pow_ne_zero _ hell'), one_smul]

theorem q1_level1_base_le (p : BIdx qG) (hp1 : (p.1 : ℕ) = 1) :
    (p.2.1.1 0).val ≤ 210 := by
  have hc0 := AdalyFormal.M1IMS.row_aligned (ell := 2) (k := 1)
    (Lu := dilLu 1 20) (S := dilTower 1 20) (by norm_num) p
  have hc : p.2.1.1 ∈ CoarseLattice (L 1 20) 2 := by
    simpa [hp1] using hc0
  have heven : 2 ∣ (p.2.1.1 0).val :=
    Nat.dvd_of_mod_eq_zero ((mem_CoarseLattice.mp hc) 0)
  have hfin : (p.2.1.1 0).val < 256 := by
    have h := (p.2.1.1 0).isLt
    norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at h
    exact h
  have hb := p.2.2.1
  simp only [hp1] at hb
  rcases hb with hmem | hmem
  · have hΩ := hmem.2.1
    change 44 ≤ (p.2.1.1 0).val ∧ (p.2.1.1 0).val < 212 at hΩ
    obtain ⟨t, ht⟩ := heven
    omega
  · have hΩ := hmem.2.1
    change 44 ≤ ((coarseShift p.2.1.1 2 p.2.1.2) 0).val ∧
      ((coarseShift p.2.1.1 2 p.2.1.2) 0).val < 212 at hΩ
    by_cases hd : p.2.1.2 = 0
    · rw [hd, coarseShift_val_eq] at hΩ
      norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu] at hΩ
      by_cases hlt : (p.2.1.1 0).val + 2 < 256
      · rw [Nat.mod_eq_of_lt hlt] at hΩ
        omega
      · have hmod : ((p.2.1.1 0).val + 2) % 256 = (p.2.1.1 0).val + 2 - 256 := by
          rw [Nat.mod_eq_sub_mod (by omega : 256 ≤ (p.2.1.1 0).val + 2)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hmod] at hΩ
        omega
    · rw [coarseShift_apply_ne _ _ _ _ (Ne.symm hd)] at hΩ
      obtain ⟨t, ht⟩ := heven
      omega

theorem q1_Qfull_sing_level1_zero (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (p : BIdx qG) (hp1 : (p.1 : ℕ) = 1) :
    (bondSectorOf qG (flatCfg : Cfg (L 1 20))).Qfull (sing e X) p = 0 := by
  have hbase := q1_level1_base_le p hp1
  have hj : p.1 = 1 := Fin.ext hp1
  cases p with
  | mk j b =>
    have hj' : j = 1 := hj
    subst j
    have hbase' : (b.1.1 0).val ≤ 210 := hbase
    have hc0 := AdalyFormal.M1IMS.row_aligned (ell := 2) (k := 1)
      (Lu := dilLu 1 20) (S := dilTower 1 20) (by norm_num) (⟨1, b⟩ : BIdx qG)
    have hc' : b.1.1 ∈ CoarseLattice (L 1 20) (qG.ell ^ ((1 : Fin 2) : ℕ)) := by
      simpa [qG, geomOf] using hc0
    have hdvd : ∀ ν, qG.ell ^ 1 ∣ (L 1 20) ν + 1 := by
      intro ν
      change (2 : ℕ) ∣ (L 1 20) ν + 1
      fin_cases ν <;> norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu]
    change (QfullOf qG (flatCfg : Cfg (L 1 20)) (sing e X)) ⟨1, b⟩ = 0
    rw [Qfull_flat_row qG (by change 0 < (2 : ℕ); norm_num) 1 hdvd
      (⟨1, b⟩ : BIdx qG) (by norm_num [qG, geomOf]) hc' (sing e X)]
    change lineCoarseRestrictSuTwo 2 (WithLp.ofLp (sing e X))
      ⟨⟨b.1.1, hc'⟩, b.1.2⟩ = 0
    unfold lineCoarseRestrictSuTwo
    have hsum : ∑ x ∈ blockOf b.1.1 2, ∑ i ∈ Finset.range 2,
        (WithLp.ofLp (sing e X)) (pathSite x b.1.2 i, b.1.2) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      refine Finset.sum_eq_zero (fun i hi => ?_)
      apply sing_apply_ne
      intro heq
      have hxbound := (mem_blockOf.mp hx) 0
      have hi' := Finset.mem_range.mp hi
      have hpath : ((pathSite x b.1.2 i) 0).val ≤ 212 := by
        by_cases hd : b.1.2 = 0
        · rw [hd, pathSite_apply_self_val]
          norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu]
          rw [Nat.mod_eq_of_lt (by omega : (x 0).val + i < 256)]
          omega
        · rw [pathSite_apply_ne _ _ _ _ (Ne.symm hd)]
          omega
      have heq0 := congrArg (fun w : Bond (L 1 20) => (w.1 0).val) heq
      change ((pathSite x b.1.2 i) 0).val = (e.1 0).val at heq0
      omega
    rw [hsum]
    simp

theorem q1_Qfull_level0 (A : BondFnL2 (L 1 20)) (p : BIdx qG)
    (hp0 : (p.1 : ℕ) = 0) :
    (bondSectorOf qG (flatCfg : Cfg (L 1 20))).Qfull A p = A p.2.1 := by
  change (QfullOf qG (flatCfg : Cfg (L 1 20)) A) p = _
  simp only [QfullOf, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  have key : ∀ (j : ℕ), j = 0 → ∀ b : Bond (L 1 20),
      (((qG.ell : ℝ) ^ j)⁻¹) •
        (WithLp.ofLp (QlinB qG (flatCfg : Cfg (L 1 20)) j A)) b = A b := by
    rintro j rfl b
    rw [pow_zero, inv_one, one_smul, QlinB_zero]
  exact key _ hp0 _

theorem q1_inner_sing (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo) :
    inner ℝ (sing e X) A = inner ℝ X (A e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e]
  · rw [sing_apply_self]
  · intro b hb hne
    rw [sing_apply_ne _ _ hne]
    simp
  · simp

theorem q1_Mass_row_of_mem (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (hb0 : e ∈ bondsLam qG 0) :
    inner ℝ (sing e X) (MassFull qG 1 (bondSectorOf qG (flatCfg : Cfg (L 1 20))) A) =
      inner ℝ (sing e X) A := by
  let p0 : BIdx qG := ⟨0, ⟨e, hb0⟩⟩
  rw [MassFull]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [PiLp.inner_apply]
  simp only [diagW, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single p0]
  · rw [q1_Qfull_level0 (sing e X) p0 (by simp [p0]),
      q1_Qfull_level0 A p0 (by simp [p0])]
    rw [sing_apply_self]
    simp [p0, massW, q1_inner_sing]
  · intro p hp hne
    have hlevel : (p.1 : ℕ) = 0 ∨ (p.1 : ℕ) = 1 := by
      have hlt := p.1.isLt
      norm_num [qG, geomOf] at hlt
      omega
    rcases hlevel with h0 | h1
    · have hz : (bondSectorOf qG (flatCfg : Cfg (L 1 20))).Qfull (sing e X) p =
          if p.2.1 = e then X else 0 := by
        rw [q1_Qfull_level0 (sing e X) p h0]
        exact sing_apply e X p.2.1
      rw [hz]
      by_cases hbe : p.2.1 = e
      · have hp0 : p = p0 := by
          cases p with
          | mk j b =>
            have hj : j = 0 := Fin.ext h0
            cases hj
            apply Sigma.ext (by rfl)
            change b.1 = e at hbe
            exact heq_of_eq (Subtype.ext hbe)
        exact (hne hp0).elim
      · simp [hbe]
    · rw [q1_Qfull_sing_level1_zero e X heDeep p h1]
      simp
  · simp

theorem q1_not_OmGe1_deep (z : PeriodicLatticeSite (L 1 20))
    (hz : 213 ≤ (z 0).val) : ¬ OmGe qG 1 z := by
  intro h
  rcases h with ⟨i, hi1, hik, y, hy, hxy⟩
  have hi : i = 1 := by
    norm_num [qG, geomOf] at hik
    omega
  subst i
  have hyΩ := hy.2.1
  change 44 ≤ (y 0).val ∧ (y 0).val < 212 at hyΩ
  have hx0 := hxy 0
  change (y 0).val ≤ (z 0).val ∧ (z 0).val < (y 0).val + 2 at hx0
  omega

theorem q1_coarseShift1_deep (e : Bond (L 1 20))
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    213 ≤ (coarseShift e.1 1 e.2 0).val := by
  by_cases hd : e.2 = 0
  · rw [hd, coarseShift_val_eq]
    norm_num [AdalyFormal.Round10.Nonvanishing.DilatedFlux.L, scaleUp, dilLu]
    rw [Nat.mod_eq_of_lt (by omega : (e.1 0).val + 1 < 256)]
    omega
  · rw [coarseShift_apply_ne _ _ _ _ (Ne.symm hd)]
    exact heDeep

theorem q1_deep_bondsLam0 (e : Bond (L 1 20))
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    e ∈ bondsLam qG 0 := by
  have hLam0 : e.1 ∈ qG.Lam 0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro μ
      simp
    · change 4 ≤ (e.1 0).val ∧ (e.1 0).val < 252
      omega
    · change ¬ (44 ≤ (e.1 0).val ∧ (e.1 0).val < 212)
      omega
  refine ⟨Or.inl hLam0, ?_⟩
  intro hdis
  rcases hdis with h | h
  · exact q1_not_OmGe1_deep e.1 heDeep h
  · exact q1_not_OmGe1_deep _ (q1_coarseShift1_deep e heDeep heUpper) h

theorem q1_Mass_row (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (sing e X) (MassFull qG 1 (bondSectorOf qG (flatCfg : Cfg (L 1 20))) A) =
      inner ℝ (sing e X) A :=
  q1_Mass_row_of_mem A e X heDeep (q1_deep_bondsLam0 e heDeep heUpper)

theorem q1_Wop_on_boundary (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20))
    (heDeep : 213 ≤ (e.1 0).val) (p : PeriodicLatticePlaquette (L 1 20))
    (hep : e ∈ periodicPlaquetteBoundaryEdges p) (b : Bond (L 1 20))
    (hbp : b ∈ periodicPlaquetteBoundaryEdges p) :
    (Wop qG (flatCfg : Cfg (L 1 20)) 1 A) b = A b := by
  have h0 := q1_plaq_base_not_om1 hep hbp heDeep
  have h1 := q1_plaq_shift_not_om1 hep hbp heDeep
  have hz : (gradL2 (flatCfg : Cfg (L 1 20))
      (Gp (geomOf 2 1 (dilTower 1 20)) (flatCfg : Cfg (L 1 20)) 1
        (Rproj (geomOf 2 1 (dilTower 1 20)) (flatCfg : Cfg (L 1 20))
          (gradAdj (flatCfg : Cfg (L 1 20)) A)))) b = 0 := by
    rw [gradL2_apply]
    unfold gradValueCovariant
    rw [potential_zero_off_om1 (dilTower 1 20) (flatCfg : Cfg (L 1 20)) 1 _ h0,
      potential_zero_off_om1 (dilTower 1 20) (flatCfg : Cfg (L 1 20)) 1 _ h1]
    simp
  unfold Wop
  simp only [ContinuousLinearMap.sub_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply]
  rw [PiLp.sub_apply, hz, sub_zero]

/-- The actual dressed all-plaquette Dpi row is the flat Delta row deep in the collar. -/
theorem q1_Dpi_row_flat (A : BondFnL2 (L 1 20)) (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) :
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DpiFullS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) 1 A) =
      inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) A) := by
  calc
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DpiFullS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) 1 A) =
        inner ℝ (Wop qG (flatCfg : Cfg (L 1 20)) 1 (sing e X))
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) (Wop qG (flatCfg : Cfg (L 1 20)) 1 A)) := by
      simp only [AdalyFormal.D1Literal.DpiFullS, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) (Wop qG (flatCfg : Cfg (L 1 20)) 1 A)) := by
      rw [q1_Wop_sing e X heDeep]
    _ = inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) A) := by
      unfold AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll
      apply q1_deltaK_row_congr Set.univ _ _ e X
      intro p hp hep b hbp
      exact q1_Wop_on_boundary A e heDeep p hep b hbp

theorem q1_rightStar_Wop (t : ℝ) :
    Wop qG (rightStar (q := 1) (by norm_num) 20 t) 1 =
      Wop qG (flatCfg : Cfg (L 1 20)) 1 := by
  apply Wop_congr_Z (dil_admissible (q := 1) (R := 20) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)
  intro e he
  simpa [flatCfg] using
    (rightStar_off_exterior (q := 1) (by norm_num) 20 t e he)

theorem q1_rightStar_Tfull (t : ℝ) :
    Tfull qG (rightStar (q := 1) (by norm_num) 20 t) =
      Tfull qG (flatCfg : Cfg (L 1 20)) := by
  apply Tfull_congr (dil_admissible (q := 1) (R := 20) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)
  intro e he
  have heZ : e ∉ AdalyFormal.D1Literal.Zb ((dilTower 1 20).Om 0) := by
    intro hz
    exact hz.1 he.1
  simpa [flatCfg] using
    (rightStar_off_exterior (q := 1) (by norm_num) 20 t e heZ)

theorem q1_Tfull_sing_zero (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) :
    Tfull qG (flatCfg : Cfg (L 1 20)) (sing e X) = 0 := by
  unfold Tfull
  simp only [ContinuousLinearMap.comp_apply]
  exact q1_Rproj_gradAdj_sing_zero e X heDeep

theorem q1_TsT_row_rightStar (t : ℝ) (A : BondFnL2 (L 1 20))
    (e : Bond (L 1 20)) (X : SuTwo) (heDeep : 213 ≤ (e.1 0).val) :
    inner ℝ (sing e X)
      ((ContinuousLinearMap.adjoint (Tfull qG (rightStar (q := 1) (by norm_num) 20 t)))
        (Tfull qG (rightStar (q := 1) (by norm_num) 20 t) A)) = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_right, q1_rightStar_Tfull,
    q1_Tfull_sing_zero e X heDeep]
  simp

/-- The actual right-star dressed row agrees with the flat all-plaquette Delta row
through the deep-collar range used by the dictionary. -/
theorem q1_Dpi_row_rightStar (t : ℝ) (A : BondFnL2 (L 1 20))
    (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DpiFullS AdalyFormal.D1Literal.selAll qG
          (rightStar (q := 1) (by norm_num) 20 t) 1 A) =
      inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) A) := by
  have hW := q1_rightStar_Wop t
  calc
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DpiFullS AdalyFormal.D1Literal.selAll qG
          (rightStar (q := 1) (by norm_num) 20 t) 1 A) =
        inner ℝ (Wop qG (rightStar (q := 1) (by norm_num) 20 t) 1 (sing e X))
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (rightStar (q := 1) (by norm_num) 20 t)
            (Wop qG (rightStar (q := 1) (by norm_num) 20 t) 1 A)) := by
      simp only [AdalyFormal.D1Literal.DpiFullS, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ (Wop qG (flatCfg : Cfg (L 1 20)) 1 (sing e X))
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (rightStar (q := 1) (by norm_num) 20 t)
            (Wop qG (flatCfg : Cfg (L 1 20)) 1 A)) := by
      rw [hW]
    _ = inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (rightStar (q := 1) (by norm_num) 20 t)
            (Wop qG (flatCfg : Cfg (L 1 20)) 1 A)) := by
      rw [q1_Wop_sing e X heDeep]
    _ = inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) (Wop qG (flatCfg : Cfg (L 1 20)) 1 A)) := by
      unfold AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll
      apply q1_deltaK_row_congr_config Set.univ _ _ _ e X
      intro p hp hep b hbp
      exact q1_rightStar_on_boundary t e heDeep heUpper p hep b hbp
    _ = inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) A) := by
      unfold AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll
      apply q1_deltaK_row_congr Set.univ _ _ e X
      intro p hp hep b hbp
      exact q1_Wop_on_boundary A e heDeep p hep b hbp

theorem q1_rightStar_sector (t : ℝ) :
    bondSectorOf qG (rightStar (q := 1) (by norm_num) 20 t) =
      bondSectorOf qG (flatCfg : Cfg (L 1 20)) := by
  apply sector_congr (dil_admissible (q := 1) (R := 20) (by norm_num) (by norm_num))
    (by norm_num) (by norm_num)
  intro e he
  have heZ : e ∉ AdalyFormal.D1Literal.Zb ((dilTower 1 20).Om 0) := by
    intro hz
    exact hz.1 he.1
  simpa [flatCfg] using
    (rightStar_off_exterior (q := 1) (by norm_num) 20 t e heZ)

theorem q1_Mass_row_rightStar (t : ℝ) (A : BondFnL2 (L 1 20))
    (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (sing e X)
      (MassFull qG 1 (bondSectorOf qG (rightStar (q := 1) (by norm_num) 20 t)) A) =
      inner ℝ (sing e X) A := by
  rw [q1_rightStar_sector]
  exact q1_Mass_row A e X heDeep heUpper

theorem q1_deep_om0 (e : Bond (L 1 20))
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    e.1 ∈ qG.Om0 := by
  change 4 ≤ (e.1 0).val ∧ (e.1 0).val < 252
  omega

noncomputable def q1SingE (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) : ↥(bondSupp qG) :=
  ⟨sing e X, by
    intro b hb
    apply sing_apply_ne
    intro h
    apply hb
    rw [h]
    exact Or.inl (q1_deep_om0 e heDeep heUpper)⟩

@[simp] theorem q1_iE_singE (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    iE qG (q1SingE e X heDeep heUpper) = sing e X := rfl

theorem q1_TsT_row_rightStar_E (t : ℝ) (u : TwistSpace 1 20)
    (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (q1SingE e X heDeep heUpper)
      ((ContinuousLinearMap.adjoint ((Tfull qG (rightStar (q := 1) (by norm_num) 20 t)).comp (iE qG)))
        (Tfull qG (rightStar (q := 1) (by norm_num) 20 t) (iE qG u))) = 0 := by
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    q1_iE_singE, q1_rightStar_Tfull, q1_Tfull_sing_zero e X heDeep]
  simp

theorem q1_Ginv_row_rightStar (t : ℝ) (u : TwistSpace 1 20)
    (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (q1SingE e X heDeep heUpper)
      ((AdalyFormal.D1Literal.dataS AdalyFormal.D1Literal.selAll AdalyFormal.D1Literal.selAll
        (gparams 2 1 (dilLu 1 20) (by norm_num) (dilTower 1 20)
          (rightStar (q := 1) (by norm_num) 20 t) 1 (dilLam 1 20))).Ginv u) =
      inner ℝ (sing e X)
          (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
            (flatCfg : Cfg (L 1 20)) (iE qG u)) +
        inner ℝ (sing e X) (iE qG u) := by
  simp only [qG, BaseDataS.Ginv, AdalyFormal.D1Literal.dataS, baseData,
    gparams, IngrBParams.G, IngrBParams.sector,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right,
    pE_inner_right, q1_iE_singE]
  rw [q1_Dpi_row_rightStar t (iE qG u) e X heDeep heUpper,
    q1_TsT_row_rightStar_E t u e X heDeep heUpper]
  have hM := q1_Mass_row_rightStar t (iE qG u) e X heDeep heUpper
  simp only [qG] at hM
  rw [hM]
  simp

theorem q1_kernel_deep_row (u : TwistSpace 1 20)
    (hline : AdalyFormal.Round10.Assembly.R2.KernelLine 1 20
      (rightStar (q := 1) (by norm_num) 20) u)
    (e : Bond (L 1 20)) (X : SuTwo)
    (heDeep : 213 ≤ (e.1 0).val) (heUpper : (e.1 0).val ≤ 250) :
    inner ℝ (sing e X)
        (AdalyFormal.D1Literal.DeltaS AdalyFormal.D1Literal.selAll qG
          (flatCfg : Cfg (L 1 20)) (iE qG u)) +
      inner ℝ (sing e X) (iE qG u) = 0 := by
  have hzero : inner ℝ (q1SingE e X heDeep heUpper)
      (vacA 1 20 (rightStar (q := 1) (by norm_num) 20) 1
        (vacEdge 1 20 (rightStar (q := 1) (by norm_num) 20)) u) = 0 := by
    rw [hline.2.1]
    simp
  rw [vacA_rightStar (q := 1) (by norm_num) 20 1
    (vacEdge 1 20 (rightStar (q := 1) (by norm_num) 20))] at hzero
  have hG := q1_Ginv_row_rightStar
    (vacEdge 1 20 (rightStar (q := 1) (by norm_num) 20)) u e X heDeep heUpper
  rw [hzero] at hG
  exact hG.symm

end AdalyFormal.Round15.Dictionary.Physical

#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_kernel_deep_row
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Ginv_row_rightStar
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_TsT_row_rightStar_E
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Mass_row
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Qfull_sing_level1_zero
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Dpi_row_rightStar
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_rightStar_Wop
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Dpi_row_flat
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_deltaK_row_congr
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Wop_sing
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Rproj_gradAdj_sing_zero
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_Rproj_zero
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_RImage_zero
#print axioms AdalyFormal.Round15.Dictionary.Physical.q1_lap_zero

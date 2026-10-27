import GdGen1
import GdGap2

/-!
# GdGen2 -- for an ARBITRARY configuration `U`: the literal and localised data agree on the subspace `V` of fields vanishing on the level-0 bonds.

* `dataS_*_eq` : projection lemmas for `dataS`; the subspaces `V0` (fields vanishing on the level-0 bonds) and `Z0` (fields on `𝔅` with zero level-0 part);
  `C2full_level0_coord` (`C^(2)` has no level-0 part); `FnuMuLoc_congr_sets`, `JfieldLoc_congr_sets` (the source only reads the plaquette set near the bond).
  (`JfS_eq_near`, `Ginv_eq_on_V` are in GdGen3; `twoData_lit_loc` in GdGen4.)
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
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.DeltaPrime

variable {L : PeriodicLatticeExtent}

section proj
variable (sD sJ : PlaqSel) (P : IngrBParams)

theorem dataS_C2_eq : (dataS sD sJ P).C2 = fun A => P.sector.C2full (Wop P.G P.U P.a (iE P.G A)) := rfl
theorem dataS_J_proj : (dataS sD sJ P).J = pE P.G (JfS sJ P) := rfl
theorem dataS_Ginv_eq : (dataS sD sJ P).Ginv =
    (pE P.G).comp ((DpiFullS sD P.G P.U P.a).comp (iE P.G)) +
      (ContinuousLinearMap.adjoint ((Tfull P.G P.U).comp (iE P.G))).comp ((Tfull P.G P.U).comp (iE P.G)) +
      (pE P.G).comp ((MassFull P.G P.a P.sector).comp (iE P.G)) := rfl

end proj

/-! ### the subspaces -/

def V0 (G : TowerGeom L) : Submodule ℝ ↥(bondSupp G) where
  carrier := {x | ∀ β ∈ bondsLam G 0, (WithLp.ofLp (iE G x)) β = 0}
  zero_mem' := fun β _ => by simp
  add_mem' := fun {x y} hx hy β hβ => by simp [hx β hβ, hy β hβ]
  smul_mem' := fun c x hx β hβ => by simp [hx β hβ]

def Z0 (G : TowerGeom L) : Submodule ℝ (FSp G) where
  carrier := {y | ∀ β (hβ : β ∈ bondsLam G (((0 : Fin (G.k + 1)) : Fin (G.k + 1)) : ℕ)),
    (WithLp.ofLp y) ⟨(0 : Fin (G.k + 1)), ⟨β, hβ⟩⟩ = 0}
  zero_mem' := fun β _ => by simp
  add_mem' := fun {x y} hx hy β hβ => by
    have h1 := hx β hβ
    have h2 := hy β hβ
    show (x + y).ofLp _ = 0
    rw [PiLp.add_apply, h1, h2, add_zero]
  smul_mem' := fun c x hx β hβ => by
    have h1 := hx β hβ
    show (c • x).ofLp _ = 0
    rw [PiLp.smul_apply, h1, smul_zero]

theorem C2full_level0_coord (G : TowerGeom L) (U : Cfg L) (X : BondFnL2 L) (β : Bond L)
    (hβ : β ∈ bondsLam G (((0 : Fin (G.k + 1)) : Fin (G.k + 1)) : ℕ)) :
    (WithLp.ofLp (C2fullOf G U X)) ⟨(0 : Fin (G.k + 1)), ⟨β, hβ⟩⟩ = 0 := by
  show (((G.ell : ℝ) ^ (((0 : Fin (G.k + 1)) : Fin (G.k + 1)) : ℕ))⁻¹) •
      (WithLp.ofLp (C2rawB G U (((0 : Fin (G.k + 1)) : Fin (G.k + 1)) : ℕ) X)) β = 0
  have h0 : (((0 : Fin (G.k + 1)) : Fin (G.k + 1)) : ℕ) = 0 := rfl
  rw [h0, C2rawB_eq, C2CompL_zero]
  simp

#print axioms C2full_level0_coord

/-! ### the source -/

theorem FnuMuLoc_congr_sets (P P' : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (ν μ : Fin 3) (y : PeriodicLatticeSite L)
    (h : ∀ q : PeriodicLatticePlaquette L, q.1 = y → (q ∈ P ↔ q ∈ P')) :
    AdalyFormal.IngredientFamily.FnuMuLoc P U ν μ y = AdalyFormal.IngredientFamily.FnuMuLoc P' U ν μ y := by
  classical
  unfold AdalyFormal.IngredientFamily.FnuMuLoc
  by_cases hlt : ν < μ
  · have hm := h (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) rfl
    simp only [dif_pos hlt]
    by_cases hP : (y, (⟨(ν, μ), hlt⟩ : PeriodicPlaquetteDirections)) ∈ P
    · rw [if_pos hP, if_pos (hm.mp hP)]
    · rw [if_neg hP, if_neg (fun h' => hP (hm.mpr h'))]
  · by_cases hgt : μ < ν
    · have hm := h (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) rfl
      simp only [dif_neg hlt, dif_pos hgt]
      by_cases hP : (y, (⟨(μ, ν), hgt⟩ : PeriodicPlaquetteDirections)) ∈ P
      · rw [if_pos hP, if_pos (hm.mp hP)]
      · rw [if_neg hP, if_neg (fun h' => hP (hm.mpr h'))]
    · simp only [dif_neg hlt, dif_neg hgt]

theorem JfieldLoc_congr_sets (P P' : Set (PeriodicLatticePlaquette L))
    (U : PeriodicLinkConfiguration (Matrix.specialUnitaryGroup (Fin 2) ℂ) L) (x : PeriodicLatticeSite L) (μ : Fin 3)
    (h : ∀ q : PeriodicLatticePlaquette L, pdist q.1 x ≤ 1 → (q ∈ P ↔ q ∈ P')) :
    AdalyFormal.IngredientFamily.JfieldLoc P U x μ = AdalyFormal.IngredientFamily.JfieldLoc P' U x μ := by
  unfold AdalyFormal.IngredientFamily.JfieldLoc
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs with hνμ
  · rfl
  · unfold AdalyFormal.Balaban.SourceJ.DstarDir
    have h1 := FnuMuLoc_congr_sets P P' U ν μ x (fun q hq => h q (by rw [hq, AdalyFormal.StatementLaneR8.pdist_self]; omega))
    have h2 := FnuMuLoc_congr_sets P P' U ν μ (AdalyFormal.Balaban.CovariantHjMinimizer.periodicLatticeShiftBack x ν)
      (fun q hq => h q (by
        rw [hq, AdalyFormal.StatementLaneR8.pdist_comm]
        exact AdalyFormal.StatementLaneR8.pdist_shiftBack_le x ν))
    beta_reduce
    rw [h1, h2]

#print axioms FnuMuLoc_congr_sets
#print axioms JfieldLoc_congr_sets

end AdalyFormal.D1Guarded

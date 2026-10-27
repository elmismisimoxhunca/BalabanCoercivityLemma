import GdAbs

/-!
# GdTheta -- (step) the source `J` of the assembled data is `Q* j0` with `j0` the level-0 part of `J`, provided `J` vanishes on the bonds of `E₀` that are not level-0 bonds.
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
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.D1Literal

variable {L : PeriodicLatticeExtent}

open Classical in
/-- the level-0 part of a bond field, as an element of `L²(𝔅)`. -/
noncomputable def level0 (G : TowerGeom L) (Jf : BondFnL2 L) : FSp G :=
  WithLp.toLp 2 (fun p : BIdx G => if (p.1 : ℕ) = 0 then (WithLp.ofLp Jf) p.2.1 else 0)

open Classical in
theorem inner_Qfull_level0 (G : TowerGeom L) (U : Cfg L) (B Jf : BondFnL2 L) :
    ⟪(bondSectorOf G U).Qfull B, level0 G Jf⟫ =
      ∑ b : Bond L, if b ∈ bondsLam G 0 then ⟪WithLp.ofLp B b, WithLp.ofLp Jf b⟫ else 0 := by
  unfold level0
  simp only [PiLp.inner_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (0 : Fin (G.k + 1))]
  · have h1 : ∀ x : {b : Bond L // b ∈ bondsLam G (((0 : Fin (G.k + 1)) : ℕ))},
        ⟪((bondSectorOf G U).Qfull B).ofLp ⟨(0 : Fin (G.k + 1)), x⟩, (if (((⟨(0 : Fin (G.k + 1)), x⟩ : BIdx G).1 : Fin (G.k + 1)) : ℕ) = 0 then Jf.ofLp (⟨(0 : Fin (G.k + 1)), x⟩ : BIdx G).2.1 else 0)⟫
        = ⟪B.ofLp x.1, Jf.ofLp x.1⟫ := by
      intro x
      simp [bondSectorOf, QfullOf, QlinB_zero]
    simp only [h1]
    classical
    refine (Finset.sum_subtype (Finset.univ.filter (fun b => b ∈ bondsLam G (((0 : Fin (G.k + 1)) : ℕ))))
      (p := fun b => b ∈ bondsLam G (((0 : Fin (G.k + 1)) : ℕ))) (by simp)
      (fun b => ⟪B.ofLp b, Jf.ofLp b⟫)).symm.trans ?_
    rw [Finset.sum_filter]
    simp
  · intro j _ hj
    have : ((j : Fin (G.k + 1)) : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h


open Classical in
theorem C2full_level0_inner (G : TowerGeom L) (U : Cfg L) (X Jf : BondFnL2 L) :
    ⟪(bondSectorOf G U).C2full X, level0 G Jf⟫ = 0 := by
  unfold level0
  simp only [PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun p _ => ?_)
  by_cases h : (p.1 : ℕ) = 0
  · have : (bondSectorOf G U).C2full X = C2fullOf G U X := rfl
    rw [this]
    simp [C2fullOf, h, C2rawB_eq, C2CompL_zero]
  · simp [h]

section concrete
variable (sD sJ : PlaqSel) (P : IngrBParams)

theorem dataS_J_eq_Qs
    (hJ : ∀ b : Bond P.Lf, b ∈ bondsOm0 P.G → b ∉ bondsLam P.G 0 → (WithLp.ofLp (JfS sJ P)) b = 0) :
    (dataS sD sJ P).J = (dataS sD sJ P).Qs (level0 P.G (JfS sJ P)) := by
  classical
  apply ext_inner_right ℝ
  intro A
  have h1 : ⟪(dataS sD sJ P).J, A⟫ = ⟪JfS sJ P, iE P.G A⟫ := pE_inner_left P.G A _
  have h2 : ⟪(dataS sD sJ P).Qs (level0 P.G (JfS sJ P)), A⟫ = ⟪(bondSectorOf P.G P.U).Qfull (iE P.G A), level0 P.G (JfS sJ P)⟫ := by
    show ⟪ContinuousLinearMap.adjoint ((bondSectorOf P.G P.U).Qfull.comp (iE P.G)) _, A⟫ = _
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    rfl
  rw [h1, h2, inner_Qfull_level0]
  simp only [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hb : b ∈ bondsLam P.G 0
  · simp only [hb, if_true]; rw [real_inner_comm]
  · simp only [hb, if_false]
    by_cases hb0 : b ∈ bondsOm0 P.G
    · rw [hJ b hb0 hb]; simp
    · have : (WithLp.ofLp (iE P.G A)) b = 0 := A.2 b hb0
      rw [this]; simp

theorem G1invS_eq_Ginv_of
    (hJ : ∀ b : Bond P.Lf, b ∈ bondsOm0 P.G → b ∉ bondsLam P.G 0 → (WithLp.ofLp (JfS sJ P)) b = 0) :
    G1invS sD sJ P = (dataS sD sJ P).Ginv :=
  G1inv_eq_Ginv_of (dataS sD sJ P) (dataS_laws sD sJ P) (level0 P.G (JfS sJ P))
    (dataS_J_eq_Qs sD sJ P hJ) (fun A => C2full_level0_inner P.G P.U _ _) (G1invS_spec sD sJ P)

end concrete

#print axioms G1invS_eq_Ginv_of

#print axioms inner_Qfull_level0
#print axioms C2full_level0_inner
#print axioms dataS_J_eq_Qs

end AdalyFormal.D1Guarded

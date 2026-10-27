import GdGap
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000
namespace AdalyFormal.D1Guarded
open scoped RealInnerProductSpace
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.D1Literal

/-- the fourth inverse `(Q G Q*)⁻¹` inside `H` is subsumed by `WellDefAt`. -/
theorem wd_NG (sD sJ : PlaqSel) (P : IngrBParams) (h : WellDefAt sD sJ P) :
    IsUnit (((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs) := by
  by_contra hn
  have hH : (dataS sD sJ P).H = 0 := by
    unfold BaseDataS.H
    rw [Ring.inverse_non_unit _ hn]
    simp
  have hI : (dataS sD sJ P).IsG1inv (dataS sD sJ P).Ginv := by
    refine ⟨(dataS_laws sD sJ P).Dpi_symm |> fun _ => ?_, fun A => ?_⟩
    · intro x y; exact (dataS sD sJ P).Ginv_symm (dataS_laws sD sJ P) x y
    · rw [BaseDataS.K_eq, hH]; simp
  have hE := (dataS sD sJ P).G1inv_unique (G1invS_spec sD sJ P) hI
  apply hn
  have e : GenS.NmatS sD sJ P = ((dataS sD sJ P).Q.comp (dataS sD sJ P).G).comp (dataS sD sJ P).Qs := by
    unfold GenS.NmatS BaseDataS.G1 BaseDataS.G
    rw [hE]
  rw [← e]; exact h.2.2
#print axioms wd_NG
end AdalyFormal.D1Guarded

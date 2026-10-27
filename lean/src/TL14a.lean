import TL13e
import ZLocJ
import ZXR2Wire2

/-!
# TL14a -- the source `J` is natural
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.Thin
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.SourceJ (DstarDir piProj)
open AdalyFormal.Balaban.DeltaPrime (imHolonomy)
open AdalyFormal.IngredientFamily (FnuMuLoc JfieldLoc JSU2Loc)
open AdalyFormal.IngredientFamilyR2

section jj
variable {Lt L : PeriodicLatticeExtent} (h : Covers Lt L) (o : Fin 3 → ℕ)

theorem FnuMuLoc_nat (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L) (ν μ : Fin 3) (y : PeriodicLatticeSite Lt) :
    FnuMuLoc (phiP h o ⁻¹' P) (pullCfg h o U) ν μ y = FnuMuLoc P U ν μ (phiS h o y) := by
  unfold FnuMuLoc
  have him : ∀ dir, imHolonomy (pullCfg h o U) (y, dir) = imHolonomy U (phiS h o y, dir) :=
    fun dir => (re_im_nat h o U (y, dir)).2
  split_ifs with h1 h2 h3 h4 <;> simp_all [phiP, Set.mem_preimage, him]

theorem DstarDir_nat (U : Cfg L) (ν : Fin 3) (Gt : PeriodicLatticeSite Lt → Matrix (Fin 2) (Fin 2) ℂ)
    (G : PeriodicLatticeSite L → Matrix (Fin 2) (Fin 2) ℂ) (hG : ∀ y, Gt y = G (phiS h o y)) (x : PeriodicLatticeSite Lt) :
    DstarDir (pullCfg h o U) ν Gt x = DstarDir U ν G (phiS h o x) := by
  unfold DstarDir
  rw [hG, hG, phiS_shiftBack]
  simp only [pullCfg, phiE, phiS_shiftBack]

theorem JfieldLoc_nat (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L) (x : PeriodicLatticeSite Lt) (μ : Fin 3) :
    JfieldLoc (phiP h o ⁻¹' P) (pullCfg h o U) x μ = JfieldLoc P U (phiS h o x) μ := by
  unfold JfieldLoc
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  split_ifs with hν
  · rfl
  · exact DstarDir_nat h o U ν _ _ (fun y => FnuMuLoc_nat h o P U ν μ y) x

theorem JSU2Loc_nat (η : ℝ) (P : Set (PeriodicLatticePlaquette L)) (U : Cfg L) (b : Bond Lt) :
    JSU2Loc η (phiP h o ⁻¹' P) (pullCfg h o U) b = JSU2Loc η P U (phiE h o b) := by
  apply Subtype.ext
  show ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc _ _ b.1 b.2 = ((-Complex.I) * ((η⁻¹ ^ 3 : ℝ) : ℂ)) • JfieldLoc _ _ (phiE h o b).1 (phiE h o b).2
  rw [JfieldLoc_nat]
  rfl

end jj

end AdalyFormal.Thin

import R8UR5s
import ZR8Class

/-!
# R8URC -- the UR counterexample re-run against the r8 statement: `Ubad` NO LONGER changes the conclusion

UR lane (r7 objects, `compute/u_reads_omega0_20261012/UR5.lean`): on the slab tower family (ell = 2, k = 1, M = 2^m, R = 2h, h ≥ 6)
`Ubad = cfg1 (−1)` (= −1 on the single bond `b1 = (0, e₀)`, outside `Ω₀`) is in the class, the r7 level-1 rows vanish, and
`genForm(B) = −a⟪B,B⟫` (`not_P428Genuine6_slab`).
Here, at the slab point `m = 1, h = 9` (`M = 2`, `R = 18`, room `17·2 ≤ 18·2`), with the r8 (per-component) jets:
 * `ur_control_genForm`  : `genForm_Ubad(C_Ubad B̃) = genForm_1(C_1 B̃)` for EVERY `B̃` and every `a`;
 * `ur_control_instIneq` : `InstIneq` at `Ubad` ↔ `InstIneq` at `U = 1` (every `a`, `γ₀`);
 * `ur_control_wellDefG` : `WellDefG` at `Ubad` ↔ at `U = 1`;
 * `ur_control_class`    : `Ubad` is in the class `ClassCoupled 2 2 12 1 S α₀ (1/2)` for every `α₀ > 0` (so the point is inside the headline's
   hypotheses).
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocalityR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.StatementLaneR8
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)

/-- the slab parameters `M = 2`, `h = 9` (`H = 18`, `R = 18`, fine extent `N = 12·18 + 32 = 248`). -/
theorem P29 : SlabP 2 9 (12 * (9 * 2) + 16 * 2) := ⟨le_rfl, dvd_rfl, by norm_num, rfl⟩

abbrev S29 : Tower (scaleUp 2 1 (LuF 2 9)) := SlabT (scaleUp 2 1 (LuF 2 9)) 2 (9 * 2)
abbrev Lam29 : Set (PeriodicLatticeSite (LuF 2 9)) := LamF (LuF 2 9) 2 9

theorem loc29 : LocHyp 2 2 18 1 S29 Lam29 where
  adm := slab_admissible P29 (fine_ext P29)
  hk := le_rfl
  hell := le_rfl
  room := by norm_num
  lam := slab_lambdaOK2 P29

theorem o0_not_Om0 : (o0 : PeriodicLatticeSite (scaleUp 2 1 (LuF 2 9))) ∉ S29.Om 0 := by
  rw [slab_om0]; simp only [slabOm, Set.mem_setOf_eq, o0]; omega

/-- `Ubad` and `U = 1` agree on every bond with both endpoints in `Ω₀`. -/
theorem Ubad_agree29 : ∀ e : Bond (scaleUp 2 1 (LuF 2 9)), BothIn (S29.Om 0) e →
    (cfg1 su2NegOne : Cfg (scaleUp 2 1 (LuF 2 9))) e = (flatCfg : Cfg (scaleUp 2 1 (LuF 2 9))) e := by
  intro e he
  have hne : e ≠ b1 := by rintro rfl; exact o0_not_Om0 he.1
  show (if e = b1 then su2NegOne else 1) = (1 : SU2)
  rw [if_neg hne]

/-- **r8: `Ubad` gives the same value of the printed form as `U = 1`, for every `B̃` and `a`.** -/
theorem ur_control_genForm (a : ℝ) (Bt : Bond (LuF 2 9) → SuTwo) :
    GenP.genForm (gparams 2 1 (LuF 2 9) (by norm_num) S29 (cfg1 su2NegOne) a Lam29)
        (WithLp.toLp 2 (GenP.genC (gparams 2 1 (LuF 2 9) (by norm_num) S29 (cfg1 su2NegOne) a Lam29) Bt))
      = GenP.genForm (gparams 2 1 (LuF 2 9) (by norm_num) S29 flatCfg a Lam29)
        (WithLp.toLp 2 (GenP.genC (gparams 2 1 (LuF 2 9) (by norm_num) S29 flatCfg a Lam29) Bt)) :=
  genForm_congr_outside (gparams 2 1 (LuF 2 9) (by norm_num) S29 flatCfg a Lam29) loc29 (cfg1 su2NegOne)
    (fun e he => (Ubad_agree29 e he).symm) Bt

theorem ur_control_instIneq (a γ₀ : ℝ) :
    InstIneq 2 1 (by norm_num) a (LuF 2 9) γ₀ S29 Lam29 (cfg1 su2NegOne)
      ↔ InstIneq 2 1 (by norm_num) a (LuF 2 9) γ₀ S29 Lam29 flatCfg :=
  InstIneq_congr (by norm_num) a γ₀ loc29 Ubad_agree29

theorem ur_control_wellDefG (a : ℝ) :
    GenP.WellDefG (gparams 2 1 (LuF 2 9) (by norm_num) S29 (cfg1 su2NegOne) a Lam29)
      ↔ GenP.WellDefG (gparams 2 1 (LuF 2 9) (by norm_num) S29 flatCfg a Lam29) :=
  WellDefG_congr (gparams 2 1 (LuF 2 9) (by norm_num) S29 flatCfg a Lam29) loc29 (cfg1 su2NegOne)
    (fun e he => (Ubad_agree29 e he).symm)

/-- the point is inside the headline's hypotheses: `Ubad` is in the class for every `α₀ > 0`. -/
theorem ur_control_class {α₀ : ℝ} (hα : 0 < α₀) :
    ClassCoupled 2 2 12 1 S29 α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ (cfg1 su2NegOne) :=
  classCoupled_bad_gen hα (by norm_num) (by norm_num) (by norm_num)
    (slab_coversp P29 (fine_ext P29)) (slab_admissible P29 (fine_ext P29)).1 o0_not_Om0

#print axioms loc29
#print axioms Ubad_agree29
#print axioms ur_control_genForm
#print axioms ur_control_instIneq
#print axioms ur_control_wellDefG
#print axioms ur_control_class

end AdalyFormal.URLocalityR8

import ZR2B11
import ZR2B1

/-!
# R2E -- consolidated headline list (every claimed theorem with its `#print axioms`) and the
corollary that the multi-stratum tower's class is also smallness-restricted.
-/
set_option autoImplicit false
set_option maxRecDepth 8000

namespace AdalyFormal.StatementLane2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)

theorem TT_class_excludes_some_U {Lf : PeriodicLatticeExtent} (hLf : ∀ μ, Lf μ + 1 = 120)
    {α₀ : ℝ} (hα : 0 < α₀) (hsmall : α₀ ≤ 1 / 20) :
    ∃ U : LinkCfg Lf, ¬ PerCubeRegularMix 2 1 10 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U := by
  obtain ⟨p, hp⟩ : ∃ p : PeriodicLatticeSite Lf, p ∈ (TT Lf).Om 0 :=
    ⟨fun μ => ⟨10, by have := hLf μ; omega⟩, by simp [TT, OmA]⟩
  refine covered_class_excludes_some_U (fun μ => by have := hLf μ; omega) (by norm_num) (by norm_num)
    _ (TT_covers hLf 10 le_rfl) ⟨p, hp⟩ (by norm_num) hα ?_
  push_cast; nlinarith

/-- the three non-vacuity/restriction facts TOGETHER on the multi-stratum tower, one statement -/
theorem multistratum_class_is_nonvacuous_and_restrictive {Lu Lf : PeriodicLatticeExtent}
    (hLu : ∀ μ, Lu μ + 1 = 60) (hLf : ∀ μ, Lf μ + 1 = 120) {α₀ : ℝ} (hα : 0 < α₀)
    (hα1 : α₀ ≤ 1 / 20) :
    (∃ U : LinkCfg Lf, PerCubeRegularMix 2 1 10 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U ∧
       ¬ ∃ g : PeriodicLatticeSite Lf → G2, periodicGaugeTransform g U = fun _ => (1 : G2)) ∧
    (∃ U : LinkCfg Lf, ¬ PerCubeRegularMix 2 1 10 1 (TT Lf) α₀ (((2 : ℕ) : ℝ) ^ 1)⁻¹ U) :=
  ⟨(multistratum_satisfiable hLu hLf hα (by linarith)).2.2.2.2.2.2.2.1,
    TT_class_excludes_some_U hLf hα hα1⟩

/- (r5: `Sthin_perCubeRegular2_all` removed with `Sthin`, a `k = 0` tower.) -/

-- headline list
#print axioms P428Faithful2
#print axioms P428Strong
#print axioms CoversOm0
#print axioms PerCubeRegular2
#print axioms Sk_covers_scaleUp
#print axioms badU_not_perCubeRegular2
#print axioms covered_class_excludes_some_U
#print axioms ufield_perCubeRegular2
#print axioms spike_not_pure_gauge
#print axioms multistratum_satisfiable
#print axioms multistratum_class_is_nonvacuous_and_restrictive
#print axioms IngrBAt.H1_ne_zero
#print axioms JunkCopy.junk_not_IngrB
#print axioms IngrB_nonempty
#print axioms touching_strictly_larger
#print axioms not_P428Faithful2_of_H1_zero

end AdalyFormal.StatementLane2

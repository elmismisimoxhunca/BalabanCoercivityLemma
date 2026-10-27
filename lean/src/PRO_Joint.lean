import UNI_NV

/-! prosecution: JOINT non-vacuity of ALL hypotheses of P428Target8FamilyTorusU (smallness and TorusOK included). -/
set_option autoImplicit false

namespace PRO

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open UNI.AllC UNI.Total

theorem joint_nonvacuous (ell m R k : ℕ) (a₀ : ℝ) (hell : 2 ≤ ell) (hm : 1 ≤ m) (hk : 1 ≤ k) (ha₀ : 0 < a₀) :
    ∃ (Lu : PeriodicLatticeExtent) (α₀ : ℝ), 0 < α₀ ∧
      ∃ F : CubeFam (scaleUp ell k Lu),
        (∀ (s : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j f : ℕ), (s, j, f) ∈ F →
            10 ≤ f ∧ (f : ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ ≤ a₀) ∧
        TorusOK ell (ell ^ m) Lu ∧
        ∃ S : Tower (scaleUp ell k Lu), Admissible ell (ell ^ m) R k S ∧
        ∃ Lam : Set (PeriodicLatticeSite Lu), AdalyFormal.StatementLaneG.LambdaOK2 (Lu := Lu) (Lf := scaleUp ell k Lu) ell (ell ^ m) R k S Lam ∧
        ∃ U : LinkCfg (scaleUp ell k Lu),
          ClassCoupledU ell (ell ^ m) F k S α₀ (((ell : ℝ) ^ k)⁻¹) U := by
  have hell0 : 0 < ell := by omega
  have hM : 0 < ell ^ m := pow_pos hell0 _
  let Lu : PeriodicLatticeExtent := fun _ => ell ^ (m + 1) - 1
  have hLu : ∀ μ : Fin 3, Lu μ + 1 = ell ^ (m + 1) := by
    intro μ; have : 0 < ell ^ (m + 1) := pow_pos hell0 _
    show ell ^ (m + 1) - 1 + 1 = _; omega
  have hT1 : ∀ μ : Fin 3, ell ^ m ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact pow_dvd_pow ell (by omega)
  have hT2 : ∀ μ : Fin 3, ell ∣ Lu μ + 1 := fun μ => by rw [hLu μ]; exact dvd_pow_self ell (by omega)
  have hT3 : ∀ μ : Fin 3, ell < Lu μ + 1 := fun μ => by
    rw [hLu μ]
    calc ell = ell ^ 1 := (pow_one ell).symm
      _ < ell ^ (m + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hMr : (0:ℝ) < ((ell ^ m : ℕ) : ℝ) := by exact_mod_cast hM
  let α₀ : ℝ := a₀ / (10 * ((ell ^ m : ℕ) : ℝ))
  have hα : 0 < α₀ := by positivity
  have hχ : ∀ e : AdalyFormal.Balaban.AdmissibleSubspace.Bond (scaleUp ell k Lu), |(fun _ => (0:ℝ)) e| ≤ α₀ * (((ell : ℝ) ^ k)⁻¹) ^ 2 / 10 := fun e => by
    simp only [abs_zero]; positivity
  obtain ⟨hadm, hlam, ⟨⟨hs, hp⟩, hreg⟩⟩ := AdalyFormal.AllC.classHyps_nonvacuous ell (ell ^ m) R k 10 hell0 hM le_rfl Lu hT1 hα hk
    (fun _ => 0) hχ
  let F : CubeFam (scaleUp ell k Lu) := {t | t.2.2 = 10 ∧ boxShape (scaleUp ell k Lu) ell (ell ^ m) 10 t.1 t.2.1}
  have hmem : ∀ (sites : Set (PeriodicLatticeSite (scaleUp ell k Lu))) (j : ℕ),
      IsClassCube ell (ell ^ m) 10 k (fullTower ell k Lu) sites j → (sites, j, 10) ∈ F := fun sites j hq =>
    ⟨rfl, hq.1.2.1⟩
  refine ⟨Lu, α₀, hα, F, ?_, ⟨hT2, hT3, hT1⟩, fullTower ell k Lu, hadm, Set.univ, hlam, Ufield (((ell : ℝ) ^ k)⁻¹) (fun _ => 0), ?_⟩
  · intro s j f hmF
    have h1 : f = 10 := hmF.1
    subst h1
    refine ⟨le_rfl, ?_⟩
    have : ((10:ℕ):ℝ) * ((ell ^ m : ℕ) : ℝ) * α₀ = a₀ := by
      simp only [α₀]; push_cast; field_simp
    rw [this]
  · refine ⟨fun x hx => ?_, fun p hp' => ?_, fun f sites j hm hu => ?_⟩
    · obtain ⟨sites, j, hq, hx'⟩ := hs x hx
      exact ⟨sites, j, ⟨10, hmem sites j hq, ((boxClass_iff hadm 10 sites j).1 hq).1⟩, hx'⟩
    · obtain ⟨sites, j, hq, hb⟩ := hp p hp'
      exact ⟨sites, j, ⟨10, hmem sites j hq, ((boxClass_iff hadm 10 sites j).1 hq).1⟩, hb⟩
    · obtain ⟨hfc, hbox⟩ := hm
      have hf : f = 10 := hfc
      subst hf
      exact hreg sites j ((boxClass_iff hadm 10 sites j).2 ⟨hu, hbox⟩)

end PRO

#print axioms PRO.joint_nonvacuous

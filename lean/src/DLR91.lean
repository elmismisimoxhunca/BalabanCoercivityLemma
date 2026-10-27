import DLR90
import ZNonVacuity

/-!
# DL91 -- the conclusion at the witness is NOT vacuous: `Λ̃` contains a nonzero field and the printed form is strictly positive

`witness_form_pos k` : on the witness torus `Lu16 = (15,15,15)` (Λ = univ, ℓ = 2) the tree's explicit seed `tildeSeed`
(`lambdaTilde_nonvacuous`, legacy `CoercUMainDesigned`) is a field `B̃` with `OnLambdaTildeIn univ 2 B̃`, `OnLambdaT univ B̃`,
`bondEnergy B̃ > 0`, and at the curved witness `Uw k` the printed form obeys `9·10⁻⁵·bondEnergy B̃ ≤ ⟨C B̃, Δ_k C B̃⟩`, hence
`⟨C B̃, Δ_k C B̃⟩ > 0`, every `k`.  `witnessM_form_pos M k` : the same on the `(16M)³` torus at `UwM M k` (DL90), every `M ≥ 1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace AdalyFormal.DLayer

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CovariantOperators (SuTwo)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)

theorem witness_form_pos (k : ℕ) :
    ∃ Bt : Bond Lu16 → SuTwo,
      AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu16)) 2 Bt ∧
      OnLambdaT (Set.univ : Set (PeriodicLatticeSite Lu16)) Bt ∧ 0 < bondEnergy Bt ∧
      9e-5 * bondEnergy Bt ≤ AdalyFormal.StatementLaneG.GenP.genForm
          (gparams 2 k Lu16 (by norm_num) (fullTower 2 k Lu16) (Uw k) 1 Set.univ)
          (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC
            (gparams 2 k Lu16 (by norm_num) (fullTower 2 k Lu16) (Uw k) 1 Set.univ) Bt)) ∧
      0 < AdalyFormal.StatementLaneG.GenP.genForm
          (gparams 2 k Lu16 (by norm_num) (fullTower 2 k Lu16) (Uw k) 1 Set.univ)
          (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC
            (gparams 2 k Lu16 (by norm_num) (fullTower 2 k Lu16) (Uw k) 1 Set.univ) Bt)) := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ (Lu16 μ + 1) := fun μ => by show 2 ∣ 15 + 1; norm_num
  obtain ⟨Bt, hBt, hpos⟩ := AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := Lu16) (ell := 2)
    (by norm_num) hdvd
  have h1 : AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite Lu16)) 2 Bt :=
    (AdalyFormal.StatementLane.onLambdaTildeIn_univ 2 Bt).mpr hBt
  have h2 : OnLambdaT (Set.univ : Set (PeriodicLatticeSite Lu16)) Bt :=
    fun b hb => absurd (Or.inl (Set.mem_univ _)) hb
  have hI := (witness_instIneq k).2 Bt h1 h2
  exact ⟨Bt, h1, h2, hpos, hI, lt_of_lt_of_le (by positivity) hI⟩

theorem witnessM_form_pos (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    ∃ Bt : Bond (LuM M) → SuTwo,
      AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuM M))) 2 Bt ∧
      OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuM M))) Bt ∧ 0 < bondEnergy Bt ∧
      0 < AdalyFormal.StatementLaneG.GenP.genForm
          (gparams 2 k (LuM M) (by norm_num) (fullTower 2 k (LuM M)) (UwM M k) 1 Set.univ)
          (WithLp.toLp 2 (AdalyFormal.StatementLaneG.GenP.genC
            (gparams 2 k (LuM M) (by norm_num) (fullTower 2 k (LuM M)) (UwM M k) 1 Set.univ) Bt)) := by
  have hdvd : ∀ μ : Fin 3, 2 ∣ (LuM M μ + 1) := fun μ => by rw [LuM_succ M hM μ]; exact ⟨8 * M, by ring⟩
  obtain ⟨Bt, hBt, hpos⟩ := AdalyFormal.Balaban.CoercUMainDesigned.lambdaTilde_nonvacuous (L := LuM M) (ell := 2)
    (by norm_num) hdvd
  have h1 : AdalyFormal.StatementLane.OnLambdaTildeIn (Set.univ : Set (PeriodicLatticeSite (LuM M))) 2 Bt :=
    (AdalyFormal.StatementLane.onLambdaTildeIn_univ 2 Bt).mpr hBt
  have h2 : OnLambdaT (Set.univ : Set (PeriodicLatticeSite (LuM M))) Bt :=
    fun b hb => absurd (Or.inl (Set.mem_univ _)) hb
  have hI := (M0Core_two_domain_nonempty M hM k).2.2.2.2.2 Bt h1 h2
  exact ⟨Bt, h1, h2, hpos, lt_of_lt_of_le (by positivity) hI⟩

#print axioms witness_form_pos
#print axioms witnessM_form_pos

end AdalyFormal.DLayer

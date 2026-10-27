import DLR102
import MF11

/-!
# DL103 -- plug-in check: the m0_finish theorems `instIneq_M0_kuniform` (MF7) and `wellDef_M0` (MF11) with their D-layer premises
`hD2`, `hJ` DISCHARGED by DL100, on M0 ∩ PerCubeRegular2; and both at the explicit witness, every `k`

* `instIneq_M0_kuniform_discharged` : MF7's conclusion (constant `gam0M0 … (eps2op Num) (epsJfree Num) …`), hypotheses = those of
  `instIneq_M0_class_unconditional` + `eps2op·K̂ < 1`.
* `wellDef_M0_discharged` : `GenP.WellDef (PU …)` (MF11), same hypotheses.
* `witness_wellDef_instIneq k` : at the sine witness `Uw k` (ℓ = 2, a = 1, Λ = univ, DL89): `GenP.WellDef` AND MF7's `InstIneq`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT PerCubeRegular2)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq lamBlockSum_univ)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.RegBgKU (KUSmall kapHat)
open AdalyFormal.M0Finish (PU UnitSmall dCM0 cBM0 gam0M0)

theorem instIneq_M0_kuniform_discharged (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t (rhoM0 ell k e q0) ((f : ℝ) * M * α₀) θ)
    (hε'op : eps2op Num * KhatM0 ell a t (rhoM0 ell k e q0) < 1) :
    InstIneq ell k hell a Lu
      (gam0M0 ell a t (rhoM0 ell k e q0) (eps2op Num) (epsJfree Num)
        (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
      (fullTower ell k Lu) Lam U :=
  have hD := dlayer_M0_class ell k Lu hell U a t e q0 R H HU hd Lam M f α₀ hM hf hP hsm θ Num
  AdalyFormal.M0Finish.instIneq_M0_kuniform ell k Lu hell U a t e q0 R H HU hstrict hd Lam hLB (eps2op Num) (epsJfree Num)
    (eps2op_nonneg Num) (epsJfree_nonneg Num) hε'op hD.1 hD.2

theorem wellDef_M0_discharged (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell)
    (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0)
    (H : KUSmall ell (rhoM0 ell k e q0)) (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hd : ∀ μ, ell ∣ Lu μ + 1) (Lam : Set (PeriodicLatticeSite Lu))
    (M f : ℕ) (α₀ : ℝ) (hM : 0 < M) (hf : 4 ≤ f)
    (hP : PerCubeRegular2 ell M f k (fullTower ell k Lu) α₀ ((ell : ℝ) ^ k)⁻¹ U)
    (hsm : 4 * ((f : ℝ) * M * α₀) ≤ 1)
    (θ : ℝ) (Num : M0ClassNum ell a t (rhoM0 ell k e q0) ((f : ℝ) * M * α₀) θ)
    (hε'op : eps2op Num * KhatM0 ell a t (rhoM0 ell k e q0) < 1) :
    AdalyFormal.StatementLaneG.GenP.WellDef (PU ell k Lu hell U a Lam) :=
  AdalyFormal.M0Finish.wellDef_M0 ell k Lu hell U a t e q0 R H HU hd Lam (eps2op Num) hε'op
    (dlayer_M0_class ell k Lu hell U a t e q0 R H HU hd Lam M f α₀ hM hf hP hsm θ Num).1

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

/-- at the explicit witness, every `k`: well-definedness AND MF7's inequality, all premises discharged -/
theorem witness_wellDef_instIneq (k : ℕ) :
    AdalyFormal.StatementLaneG.GenP.WellDef (PU 2 k Lu16 (by norm_num) (Uw k) 1 Set.univ) ∧
    InstIneq 2 k (by norm_num) 1 Lu16
      (gam0M0 2 1 1 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2))
        (eps2op (witness_all_k k).2.2.2.2.2.2.2.2.1) (epsJfree (witness_all_k k).2.2.2.2.2.2.2.2.1)
        (dCM0 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2)))
        (cBM0 2 (rhoM0 2 k (αbw / ((2 : ℕ) : ℝ) ^ k) (αbw / (((2 : ℕ) : ℝ) ^ k) ^ 2))))
      (fullTower 2 k Lu16) Set.univ (Uw k) := by
  obtain ⟨R, H, HU, hstrict, hd, hLB, hP, h4, Num, -, -, -⟩ := witness_all_k k
  obtain ⟨-, -, -, -, -, -, h0, h1, hβ, -⟩ := witness_numerics
  have hρ := witness_rho k
  have hcast : ((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w = (12 : ℝ) * ((1 : ℕ) : ℝ) * α₀w := by norm_num
  have key : ∀ (ρ : ℝ) (hρρ : ρw = ρ) (Num' : M0ClassNum 2 1 1 ρ (((12 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * α₀w) θ₀),
      eps2op Num' * KhatM0 2 1 1 ρ < 1 := by
    intro ρ hρρ Num'
    subst hρρ
    exact (eps2op_two ρw _ h0 h1 (by rw [hcast]; have := α₀w_pos; positivity) (by rw [hcast]; exact hβ) Num').2.2
  have hε := key _ hρ.symm Num
  exact ⟨wellDef_M0_discharged 2 k Lu16 (by norm_num) (Uw k) 1 1 _ _ R H HU hd Set.univ 1 12 α₀w one_pos (by norm_num) hP h4
      θ₀ Num hε,
    instIneq_M0_kuniform_discharged 2 k Lu16 (by norm_num) (Uw k) 1 1 _ _ R H HU hstrict hd Set.univ hLB 1 12 α₀w one_pos
      (by norm_num) hP h4 θ₀ Num hε⟩

#print axioms instIneq_M0_kuniform_discharged
#print axioms wellDef_M0_discharged
#print axioms witness_wellDef_instIneq

end AdalyFormal.DLayer

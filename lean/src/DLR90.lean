import DLR89

/-!
# DL90 -- the M0 inner claim at `ℓ = 2`, `a = 1` with EXPLICIT constants, and its domain is non-empty and curved for EVERY `M`, `k`

* `M0Core_two_explicit M k` : every `U` in the whole-torus printed class `GlobalRegular2 2 M 12 k α₀ 2⁻ᵏ` with `TorusOK 2 M Lu`,
  `0 < α₀`, `12 M α₀ ≤ a₀ := epsB·10⁻³⁰⁰` satisfies the frozen r7 `InstIneq 2 k _ 1 Lu (9·10⁻⁵) (fullTower) univ U`
  (every `k`, `k = 0` included).  `M0Core_two` (DL89) is its existential packaging (same `a₀`, same `γ₀`).
* `M0Core_two_domain_nonempty M k` (`1 ≤ M`): the torus `LuM M = (16M−1)³`, the amplitude `α₀M M = a₀/(12M)` and the sine field
  `UwM M k` satisfy `TorusOK 2 M`, `0 < α₀`, `12Mα₀ ≤ a₀`, `GlobalRegular2` (all three printed clauses), the field is CURVED,
  and the conclusion `InstIneq … 9·10⁻⁵ …` holds at it: the `∀`-domain of `M0Core 2 M _ 1` at the chosen `a₀` is not empty.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option exponentiation.threshold 1000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp TorusOK)
open AdalyFormal.StatementLane2 (Ufield)
open AdalyFormal.StatementLaneG (InstIneq lamBlockSum_univ)
open AdalyFormal.IngredientFamilyR2 (fullTower)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M0Corollary (GlobalRegular2)

local notation "θ₀" => ((1 : ℝ) / 10 ^ 45)

/-- **M0 inner claim at `ℓ = 2`, `a = 1`, explicit `a₀ = epsB·10⁻³⁰⁰` and `γ₀ = 9·10⁻⁵`, every `M`, every `k`** -/
theorem M0Core_two_explicit (M k : ℕ) (Lu : PeriodicLatticeExtent) (hT : TorusOK 2 M Lu) (α₀ : ℝ) (hα₀ : 0 < α₀)
    (hsm : (12 : ℝ) * M * α₀ ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 300) (U : LinkCfg (scaleUp 2 k Lu))
    (hU : GlobalRegular2 2 M 12 k α₀ (((2 : ℕ) : ℝ) ^ k)⁻¹ U) :
    InstIneq 2 k (by norm_num) 1 Lu 9e-5 (fullTower 2 k Lu) Set.univ U := by
  have hM : 0 < M := Nat.pos_of_dvd_of_pos (hT.2.2 0) (Nat.succ_pos _)
  have hβ0 : 0 ≤ (12 : ℝ) * M * α₀ := by positivity
  obtain ⟨hcb, h216, h1000, hsU, H, HU, hρ0, hρs, hβs, h4⟩ := regime_numerics_two ((12 : ℝ) * M * α₀) hβ0 hsm
  have hcast : ((12 : ℕ) : ℝ) * M * α₀ = (12 : ℝ) * M * α₀ := by norm_num
  have Num : M0ClassNum 2 1 1 ((1 + 3 * Real.pi) * ((4 * Real.pi + 4) * ((12 : ℝ) * M * α₀)))
      (((12 : ℕ) : ℝ) * M * α₀) θ₀ :=
    m0ClassNum_two _ _ hρ0 hρs (by rw [hcast]; exact hβ0) (by rw [hcast]; exact hβs)
  have key := instIneq_globalRegular2_unconditional 2 M k le_rfl Lu hT U 1 1 α₀
    ((4 * Real.pi + 4) * ((12 : ℝ) * M * α₀)) le_rfl one_pos one_pos hα₀ h4 Set.univ
    (lamBlockSum_univ 2 (by norm_num)) hU hcb h216 h1000 hsU H HU θ₀ Num
  exact instIneq_mono (gam0_two_pos _ _ hρ0 hρs (by rw [hcast]; exact hβ0) (by rw [hcast]; exact hβs) Num) key

/-- the torus `(16M)³` (unit lattice), compatible with blocks of side `M` and `ℓ = 2` -/
def LuM (M : ℕ) : PeriodicLatticeExtent := fun _ => 16 * M - 1

theorem LuM_succ (M : ℕ) (hM : 1 ≤ M) (μ : Fin 3) : LuM M μ + 1 = 16 * M := by
  show 16 * M - 1 + 1 = 16 * M; omega

theorem torusOK_LuM (M : ℕ) (hM : 1 ≤ M) : TorusOK 2 M (LuM M) := by
  refine ⟨fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
  · rw [LuM_succ M hM]; exact ⟨8 * M, by ring⟩
  · rw [LuM_succ M hM]; omega
  · rw [LuM_succ M hM]; exact ⟨16, by ring⟩

/-- the amplitude at which `12 M α₀ = a₀` -/
noncomputable def α₀M (M : ℕ) : ℝ := AdalyFormal.RegBgKU.epsB / 10 ^ 300 / (12 * M)

/-- the sine field of MC8 on the `(16M)³` torus at level `k` -/
noncomputable def UwM (M k : ℕ) : LinkCfg (scaleUp 2 k (LuM M)) :=
  Ufield (((2 : ℕ) : ℝ) ^ k)⁻¹ (AdalyFormal.M0Corollary.chiP (scaleUp 2 k (LuM M)) ((12 : ℝ) * M * α₀M M / 2))

theorem α₀M_pos (M : ℕ) (hM : 1 ≤ M) : 0 < α₀M M := by
  unfold α₀M
  have := AdalyFormal.RegBgKU.epsB_pos
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  positivity

theorem βM_eq (M : ℕ) (hM : 1 ≤ M) : (12 : ℝ) * M * α₀M M = AdalyFormal.RegBgKU.epsB / 10 ^ 300 := by
  unfold α₀M
  have : (0 : ℝ) < M := by exact_mod_cast hM
  field_simp

/-- **the `∀`-domain of `M0Core 2 M _ 1` at the chosen `a₀` contains a curved field, every `M ≥ 1`, every `k`;
the conclusion holds there** -/
theorem M0Core_two_domain_nonempty (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    TorusOK 2 M (LuM M) ∧ 0 < α₀M M ∧ (12 : ℝ) * M * α₀M M ≤ AdalyFormal.RegBgKU.epsB / 10 ^ 300 ∧
    GlobalRegular2 2 M 12 k (α₀M M) (((2 : ℕ) : ℝ) ^ k)⁻¹ (UwM M k) ∧
    (∃ p : PeriodicLatticePlaquette (scaleUp 2 k (LuM M)), 0 < dv (periodicPlaquetteHolonomy (UwM M k) p)) ∧
    InstIneq 2 k (by norm_num) 1 (LuM M) 9e-5 (fullTower 2 k (LuM M)) Set.univ (UwM M k) := by
  have hT := torusOK_LuM M hM
  have hα := α₀M_pos M hM
  have hβ := βM_eq M hM
  have hε := AdalyFormal.RegBgKU.epsB_pos
  have hε1 := AdalyFormal.RegBgKU.epsB_le1
  have h16 : 16 ≤ LuM M 0 + 1 := by rw [LuM_succ M hM 0]; omega
  have hpos : 0 < (12 : ℝ) * M * α₀M M := by rw [hβ]; positivity
  have hG : GlobalRegular2 2 M 12 k (α₀M M) (((2 : ℕ) : ℝ) ^ k)⁻¹ (UwM M k) :=
    AdalyFormal.M0Corollary.sine_globalRegular2 2 M k (by norm_num) (LuM M) h16 (α₀M M) hpos
  have hAc1 : (12 : ℝ) * M * α₀M M / 2 < 1 := by
    rw [hβ]
    have : AdalyFormal.RegBgKU.epsB / 10 ^ 300 ≤ (1 / 10 ^ 13) / 10 ^ 300 := div_le_div_of_nonneg_right hε1 (by norm_num)
    have : (1 / 10 ^ 13 : ℝ) / 10 ^ 300 / 2 < 1 := by norm_num
    linarith
  have hn1 : (1 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hcurv : ∃ p : PeriodicLatticePlaquette (scaleUp 2 k (LuM M)), 0 < dv (periodicPlaquetteHolonomy (UwM M k) p) := by
    refine AdalyFormal.M0Corollary.sine_curved (scaleUp 2 k (LuM M)) _ _ (by positivity) hAc1 (by positivity)
      (inv_le_one_of_one_le₀ hn1) ?_
    have := AdalyFormal.IngredientFamilyR2.scaleUp_succ 2 k (LuM M) (by norm_num) 0
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [this, LuM_succ M hM 0]
    nlinarith
  exact ⟨hT, hα, le_of_eq hβ, hG, hcurv,
    M0Core_two_explicit M k (LuM M) hT (α₀M M) hα (le_of_eq hβ) (UwM M k) hG⟩

#print axioms M0Core_two_explicit
#print axioms torusOK_LuM
#print axioms M0Core_two_domain_nonempty

end AdalyFormal.DLayer

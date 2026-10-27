import LF5e
import LF2
import PW8

/-!
# LF6 -- `LemIFlat` on gradients (proved, explicit `j`-free constant) and `LemIFlat` from the coupling bound `LemV`

* **`lemS`** (`LemIFlat` restricted to gradient fields, PROVED): on every two-stratum patch (any `j`, unit torus `Lu`,
  `Rg` a union of `ell^{j+1}`-blocks), for every `φ` with `D*Dφ ⟂ N(Q')` at flat `U`,
  `‖D*Dφ‖² ≤ CS ell a · Φ(Dφ)`, `CS ell a = 12 · 2286144² · (1 + 165 ell⁴) / a`.
* `LemV ell a K` (the named remaining input): `Φ(Dφ) ≤ K · Φ(Dφ + c)` for every `φ` and every divergence-free `c`.
* **`lemIFlat_of_lemV`**: `LemV ell a K → LemIFlat ell a (CS ell a · K)` (`K ≥ 0`).
* `w3flat_of_LemV`: hence lane D's `W3FlatStmt`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace AdalyFormal.LemIFlat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1Patch (patchTower corner corner_dvd GP LemIFlat W3FlatStmt w3flat_of_LemI dvd_scaleUp PhiP)
open AdalyFormal.StatementLane (BlockClosed scaleUp)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf mem_blockOf)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)

variable {L : PeriodicLatticeExtent}

/-- the scalar constant. -/
noncomputable def CS (ell : ℕ) (a : ℝ) : ℝ := 12 * 2286144 ^ 2 * (1 + 165 * (ell : ℝ) ^ 4) / a

section patch
variable {ell j : ℕ} (hell : 0 < ell) {Rg : Set (PeriodicLatticeSite L)} (hRg : BlockClosed (ell ^ (j + 1)) Rg)
  (hdvd : ∀ μ : Fin 3, ell ^ (j + 1) ∣ L μ + 1)
include hell hRg hdvd

/-- `‖w‖² = Σ_corners Σ_{x ∈ cell} ‖w x‖²`. -/
theorem sum_cells (g : PeriodicLatticeSite L → ℝ) :
    ∑ x : PeriodicLatticeSite L, g x
      = ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then ∑ x ∈ blockOf y (ell ^ j), g x else 0) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  rw [← Finset.sum_fiberwise Finset.univ (corner (ell ^ j)) g]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : OnLatN (ell ^ j) y
  · rw [if_pos hy]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_blockOf_iff_corner hn y x hy).symm
  · rw [if_neg hy]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact absurd (hx ▸ corner_dvd (ell ^ j) x) hy

/-- `ε(w) ≤ (12/n³) ‖w‖²` for cell-constant `w`. -/
theorem epsN_le_norm (w : SiteL2 L) (hw : ∀ x, w.ofLp x = w.ofLp (corner (ell ^ j) x)) :
    epsN (ell ^ j) w.ofLp ≤ 12 / ((ell : ℝ) ^ j) ^ 3 * ‖w‖ ^ 2 := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  set T := ∑ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then ‖w.ofLp y‖ ^ 2 else 0) with hT
  -- ‖w‖² = n³ T
  have hnorm : ‖w‖ ^ 2 = ((ell : ℝ) ^ j) ^ 3 * T := by
    rw [PiLp.norm_sq_eq_of_L2, sum_cells hell hRg hdvd (fun x => ‖w.ofLp x‖ ^ 2), hT, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hy : OnLatN (ell ^ j) y
    · rw [if_pos hy, if_pos hy]
      have hconst : ∀ x ∈ blockOf y (ell ^ j), ‖w.ofLp x‖ ^ 2 = ‖w.ofLp y‖ ^ 2 := by
        intro x hx; rw [hw x, (mem_blockOf_iff_corner hn y x hy).mp hx]
      have hfit : ∀ μ : Fin 3, (y μ).val + ell ^ j ≤ L μ + 1 := by
        intro μ
        obtain ⟨a', ha'⟩ := hy μ
        obtain ⟨b', hb'⟩ := (pow_dvd_pow ell (Nat.le_succ j)).trans (hdvd μ)
        have hlt : ell ^ j * a' < ell ^ j * b' := by rw [← ha', ← hb']; exact (y μ).isLt
        have hab : a' + 1 ≤ b' := Nat.lt_of_mul_lt_mul_left hlt
        have h2 := Nat.mul_le_mul_left (ell ^ j) hab
        rw [Nat.mul_succ] at h2
        rw [ha', hb']; omega
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, AdalyFormal.M1Site.card_blockOf y _ hfit, nsmul_eq_mul]
      push_cast; ring
    · rw [if_neg hy, if_neg hy, mul_zero]
  -- ε ≤ 12 T
  have hNu := hNuOf hell hRg hdvd
  have hmu : ∀ μ : Fin 3, epsMu (ell ^ j) w.ofLp μ ≤ 4 * T := by
    intro μ
    unfold epsMu
    have hpt : ∀ y : PeriodicLatticeSite L, (if OnLatN (ell ^ j) y then
          ‖w.ofLp (coarseShift y (ell ^ j) μ) - w.ofLp y‖ ^ 2 else 0)
        ≤ 2 * (if OnLatN (ell ^ j) y then ‖w.ofLp (coarseShift y (ell ^ j) μ)‖ ^ 2 else 0)
          + 2 * (if OnLatN (ell ^ j) y then ‖w.ofLp y‖ ^ 2 else 0) := by
      intro y
      by_cases hy : OnLatN (ell ^ j) y
      · simp only [if_pos hy]
        have h1 := norm_sub_le (w.ofLp (coarseShift y (ell ^ j) μ)) (w.ofLp y)
        have h0 : 0 ≤ ‖w.ofLp (coarseShift y (ell ^ j) μ) - w.ofLp y‖ := norm_nonneg _
        have h2 : ‖w.ofLp (coarseShift y (ell ^ j) μ) - w.ofLp y‖ ^ 2
            ≤ (‖w.ofLp (coarseShift y (ell ^ j) μ)‖ + ‖w.ofLp y‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
        nlinarith [sq_nonneg (‖w.ofLp (coarseShift y (ell ^ j) μ)‖ - ‖w.ofLp y‖)]
      · simp only [if_neg hy]; norm_num
    refine (Finset.sum_le_sum (fun y _ => hpt y)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs := sum_shift_corner hell hRg hdvd (fun z => ‖w.ofLp z‖ ^ 2) μ
    simp only at hs
    rw [hs, ← hT]; linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun y _ => by split_ifs <;> positivity)
  unfold epsN
  calc ∑ μ : Fin 3, epsMu (ell ^ j) w.ofLp μ ≤ ∑ _μ : Fin 3, 4 * T := Finset.sum_le_sum (fun μ _ => hmu μ)
    _ = 12 * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ = 12 / ((ell : ℝ) ^ j) ^ 3 * ‖w‖ ^ 2 := by rw [hnorm]; field_simp

/-- **`LemIFlat` on gradients** (one patch). -/
theorem lemS_patch (a : ℝ) (ha : 0 < a) (φ : SiteL2 L)
    (hφ : ∀ ν ∈ NQp (GQ ell j Rg) (flatCfg : Cfg L), ⟪gradAdj (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) φ), ν⟫ = 0) :
    ‖gradAdj (flatCfg : Cfg L) (gradL2 (flatCfg : Cfg L) φ)‖ ^ 2
      ≤ CS ell a * PhiP (GQ ell j Rg) (flatCfg : Cfg L) a (gradL2 (flatCfg : Cfg L) φ) := by
  classical
  have hn : 0 < ell ^ j := pow_pos hell j
  have hnr : (0 : ℝ) < (ell : ℝ) ^ j := by positivity
  set K := (NQp (GQ ell j Rg) (flatCfg : Cfg L))ᗮ with hK
  have hNu := hNuOf hell hRg hdvd
  have hKK : Kᗮ = NQp (GQ ell j Rg) (flatCfg : Cfg L) := by
    rw [hK]; exact Submodule.orthogonal_orthogonal _
  set ψ := K.starProjection φ with hψdef
  have hψK : ψ ∈ K := K.starProjection_apply_mem φ
  have hdiff : φ - ψ ∈ NQp (GQ ell j Rg) (flatCfg : Cfg L) := by
    rw [← hKK]; exact K.sub_starProjection_mem_orthogonal φ
  have hφψ : ∀ v ∈ K, ⟪v, φ⟫ = ⟪v, ψ⟫ := by
    intro v hv
    have h0 : ⟪v, φ - ψ⟫ = 0 := by
      have := (Submodule.mem_orthogonal _ v).mp hv (φ - ψ) hdiff
      rw [real_inner_comm]; exact this
    rw [inner_sub_right] at h0; linarith
  have hmass : massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) ψ) = massP (GQ ell j Rg) a (gradL2 (flatCfg : Cfg L) φ) := by
    have h := massP_add_NQp hell hRg hdvd a (gradL2 (flatCfg : Cfg L) ψ) (φ - ψ) hdiff
    rw [← map_add, add_sub_cancel] at h
    exact h.symm
  have hG : ContinuousLinearMap.adjoint (gradL2 (flatCfg : Cfg L)) (gradL2 (flatCfg : Cfg L) φ) ∈ K := by
    rw [hK, Submodule.mem_orthogonal]
    intro u hu
    rw [real_inner_comm]; exact hφ u hu
  have hcore := scalar_core (gradL2 (flatCfg : Cfg L)) (massP (GQ ell j Rg) a) K (fun w => epsN (ell ^ j) w.ofLp)
    (fun w => ext3 (ell ^ j) (NuOf (ell ^ j) L) w.ofLp) 2286144 (1 + 165 * (ell : ℝ) ^ 4) ((ell : ℝ) ^ j) a hnr ha
    (by norm_num) (by positivity)
    (fun w hw v hv => by
      have hcc : ∀ x, w.ofLp x = w.ofLp (corner (ell ^ j) x) := orth_cell hell hRg w hw
      have hm := ext3_sub_mem hell hRg hdvd (NuOf (ell ^ j) L) hNu w.ofLp hcc
      rw [WithLp.toLp_ofLp] at hm
      have h0 := (Submodule.mem_orthogonal _ v).mp hv _ hm
      rw [inner_sub_left] at h0
      show ⟪v, ext3 (ell ^ j) (NuOf (ell ^ j) L) w.ofLp⟫ = ⟪v, w⟫
      rw [real_inner_comm (ext3 (ell ^ j) (NuOf (ell ^ j) L) w.ofLp) v, real_inner_comm w v]
      linarith)
    (fun w _ => by
      have := ext3_grad (ell ^ j) (NuOf (ell ^ j) L) hn hNu w.ofLp
      push_cast at this
      exact this)
    (fun w hw => epsN_le_mass hell hRg hdvd w hw a ha)
    (fun w hw => epsN_le_norm hell hRg hdvd w (orth_cell hell hRg w hw))
    φ ψ hψK hφψ hmass (massP_nonneg _ a ha.le _) hG
  rw [PhiP_grad]
  unfold CS
  exact hcore

end patch

/-- **`LemIFlat` restricted to gradient fields**, with an explicit `j`-, torus- and `Rg`-free constant. -/
theorem lemS (ell : ℕ) (hell : 0 < ell) (a : ℝ) (ha : 0 < a) :
    ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
      BlockClosed (ell ^ (j + 1)) Rg →
      ∀ φ : SiteL2 (scaleUp ell (j + 1) Lu),
        (∀ ν ∈ NQp (GP ell j Lu Rg) (flatCfg : Cfg _), ⟪gradAdj (flatCfg : Cfg _) (gradL2 (flatCfg : Cfg _) φ), ν⟫ = 0) →
        ‖gradAdj (flatCfg : Cfg _) (gradL2 (flatCfg : Cfg _) φ)‖ ^ 2
          ≤ CS ell a * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a (gradL2 (flatCfg : Cfg _) φ) := by
  intro j Lu Rg hRg φ hφ
  exact lemS_patch hell hRg (dvd_scaleUp ell j Lu hell) a ha φ hφ

/-- **the named remaining input**: the mass of the gradient part is controlled by the full form, for every
divergence-free remainder `c`. -/
def LemV (ell : ℕ) (a K : ℝ) : Prop :=
  ∀ (j : ℕ) (Lu : PeriodicLatticeExtent) (Rg : Set (PeriodicLatticeSite (scaleUp ell (j + 1) Lu))),
    BlockClosed (ell ^ (j + 1)) Rg →
    ∀ (φ : SiteL2 (scaleUp ell (j + 1) Lu)) (c : BondFnL2 (scaleUp ell (j + 1) Lu)),
      gradAdj (flatCfg : Cfg _) c = 0 →
      PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a (gradL2 (flatCfg : Cfg _) φ)
        ≤ K * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a (gradL2 (flatCfg : Cfg _) φ + c)

/-- every bond field is a gradient plus a divergence-free field. -/
theorem hodge_split (y : BondFnL2 L) :
    ∃ φ : SiteL2 L, gradAdj (flatCfg : Cfg L) (y - gradL2 (flatCfg : Cfg L) φ) = 0 := by
  classical
  set V := LinearMap.range (gradL2 (flatCfg : Cfg L) : SiteL2 L →ₗ[ℝ] BondFnL2 L) with hV
  have hmem : V.starProjection y ∈ V := V.starProjection_apply_mem y
  obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hmem
  refine ⟨φ, ?_⟩
  have hperp : y - V.starProjection y ∈ Vᗮ := V.sub_starProjection_mem_orthogonal y
  have hφ' : gradL2 (flatCfg : Cfg L) φ = V.starProjection y := hφ
  rw [hφ']
  apply ext_inner_left ℝ
  intro ψ
  rw [inner_zero_right]
  show ⟪ψ, ContinuousLinearMap.adjoint (gradL2 (flatCfg : Cfg L)) (y - V.starProjection y)⟫ = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hm : gradL2 (flatCfg : Cfg L) ψ ∈ V := LinearMap.mem_range_self _ ψ
  exact (Submodule.mem_orthogonal V _).mp hperp _ hm

/-- **`LemIFlat` from `LemV`**. -/
theorem lemIFlat_of_lemV (ell : ℕ) (hell : 0 < ell) (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) (hV : LemV ell a K) :
    LemIFlat ell a (CS ell a * K) := by
  intro j Lu Rg hRg y hy
  obtain ⟨φ, hφ⟩ := hodge_split y
  set c := y - gradL2 (flatCfg : Cfg _) φ with hc
  have hy' : y = gradL2 (flatCfg : Cfg _) φ + c := by rw [hc]; abel
  have hDy : gradAdj (flatCfg : Cfg _) y = gradAdj (flatCfg : Cfg _) (gradL2 (flatCfg : Cfg _) φ) := by
    rw [hy', map_add, hφ, add_zero]
  have hS := lemS ell hell a ha j Lu Rg hRg φ (by intro ν hν; rw [← hDy]; exact hy ν hν)
  have hVb := hV j Lu Rg hRg φ c hφ
  have hCS : 0 ≤ CS ell a := by unfold CS; positivity
  rw [hDy]
  calc ‖gradAdj (flatCfg : Cfg _) (gradL2 (flatCfg : Cfg _) φ)‖ ^ 2
      ≤ CS ell a * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a (gradL2 (flatCfg : Cfg _) φ) := hS
    _ ≤ CS ell a * (K * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a (gradL2 (flatCfg : Cfg _) φ + c)) :=
        mul_le_mul_of_nonneg_left hVb hCS
    _ = CS ell a * K * PhiP (GP ell j Lu Rg) (flatCfg : Cfg _) a y := by rw [← hy']; ring

/-- hence lane D's flat W3 statement. -/
theorem w3flat_of_LemV {ell : ℕ} (hell : 2 ≤ ell) {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hV : LemV ell a K) :
    W3FlatStmt ell (by omega) a :=
  w3flat_of_LemI hell ha (mul_nonneg (by unfold CS; positivity) hK) (lemIFlat_of_lemV ell (by omega) a K ha hK hV)

#print axioms sum_cells
#print axioms epsN_le_norm
#print axioms lemS_patch
#print axioms lemS
#print axioms hodge_split
#print axioms lemIFlat_of_lemV
#print axioms w3flat_of_LemV

end AdalyFormal.LemIFlat

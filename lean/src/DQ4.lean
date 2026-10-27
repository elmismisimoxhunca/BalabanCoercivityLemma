import DQ3

/-!
# DQ4 -- D4 `K2_strat`: the stratified quadratic `ℓ¹` bound of the composite second jet on the M1 regime (sub-builder DQ)

For `U` in lane B's `M1Regular ell M 12 k S α₀ (ℓ^k)⁻¹` on an admissible tower with `18ℓ ≤ RM`, `ℓ < N_u` (torus), `ℓ ≥ 2`,
`β = 12Mα₀ ≥ 0` satisfying the k-free smallness `DQSmall ℓ β`:
  **`C2full_strat`** : `Σ_p ‖C2fullOf (geomOf ℓ k S) U z p‖ ≤ K2strat ℓ β · wnormSq S ℓ k z`,
  `K2strat ℓ β = 3ℓ²·K2free ℓ ((1+3π)·α(β))`, `α(β) = ℓ²(4β + 8β² + 512β³)`.
Route.
1. Gauge (GCa4 `C2fullOf_gauge`, `norm_RMap`): pass to `V = U^g = exp(iηA)`; both sides are gauge invariant.
2. Rows of level `n ≥ 1` read `V` only on `Ball(b₋, 2ρ_T(n))` and `z` only on bonds based in `Ball(b₋, ρ_T(n))` (r8
   `C2CompL_congr_U`, `C2CompL_congr_in`).  There: `V = cutCfg η χ_n A` (DQ1, DQ3 cut-off, `χ_n = 1` near the rows), and
   `z = maskN n z` (bonds with `n−1 ≤ bstrat ≤ n+1`, collar of the admissible tower).
3. `cutCfg η χ_n A` has GLOBAL link bound `α/ℓⁿ` and plaquette bound `α/ℓ²ⁿ` (DQ1 `cut_link`, `cut_plaq`, M1Bounds clauses
   1–2 at level `n−1`), so DQ2 `C2Comp_depth_any` on `scaleUp ℓ n (scaleUp ℓ (k−n) Lu) = scaleUp ℓ k Lu` bounds the level-`n`
   sum by `K2free·ℓ^{-2n}‖maskN n z‖²`.
4. `Σ_n ℓ^{-2n}‖maskN n z‖² ≤ 3ℓ² wnormSq z` (each bond is read by at most three levels, `ℓ^{-n} ≤ ℓ·ℓ^{-bstrat}`).
`dqSmall_exists` : for every `ℓ ≥ 2` there is `β₀ > 0` with `DQSmall ℓ β` for all `0 ≤ β ≤ β₀` (DL106 `stageB2`).
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat.DQ

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist bigSide Admissible Tower scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self rhoT AgreeAt AgreeX
  C2CompL_congr_U C2CompL_congr_in)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.IngredientFamilyR2 (bondsLam geomOf C2fullOf C2rawB_eq C2CompL C2CompL_zero bgTower Cfg XS suCoord
  suCoordInv fromM2 BIdx)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (nrm nrm_one_suCoord)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.DLayer (K2free fN_rsmul)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M1 (strat bstrat M1Regular M1Bounds wnormSq)
open EstimatesLayer.E1E3 (e2Majorant)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

/-! ## 0. constants and the k-free smallness -/

/-- the plaquette scale of the level cut-offs at amplitude `β` -/
noncomputable def alphaQ (ell : ℕ) (β : ℝ) : ℝ := (ell : ℝ) ^ 2 * (4 * β + 8 * β ^ 2 + 512 * β ^ 3)

/-- the k-free smallness of the amplitude `β = 12 M α₀` -/
structure DQSmall (ell : ℕ) (β : ℝ) : Prop where
  h4 : 4 * β ≤ 1
  hcb : 4000000 * (ell : ℝ) ^ 2 * alphaQ ell β ≤ 1
  hKU : KUSmall ell ((1 + 3 * Real.pi) * alphaQ ell β)
  h1000 : (1 + 3 * Real.pi) * alphaQ ell β ≤ 1 / (1000 * (ell : ℝ) ^ 3)
  hK2c : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ((1 + 3 * Real.pi) * alphaQ ell β)) < 1 - 1 / (ell : ℝ)

/-- the constant of D4 -/
noncomputable def K2strat (ell : ℕ) (β : ℝ) : ℝ := 3 * (ell : ℝ) ^ 2 * K2free ell ((1 + 3 * Real.pi) * alphaQ ell β)

theorem alphaQ_nonneg (ell : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ alphaQ ell β := by unfold alphaQ; positivity

/-! ## 1. units of the M1 bounds -/

theorem units1 (η c X : ℝ) (P : ℝ) (hη : 0 < η) (hP : 0 < P) (h : X < c * ((P * η)⁻¹) ^ 1) : η * X ≤ c / P := by
  have e : c * ((P * η)⁻¹) ^ 1 = c / P / η := by field_simp
  rw [e, lt_div_iff₀ hη] at h
  linarith

theorem units2 (η c : ℝ) (D : Mt) (P : ℝ) (hη : 0 < η) (hP : 0 < P)
    (h : frobNorm (η⁻¹ • D) < c * ((P * η)⁻¹) ^ 2) : η * frobNorm D ≤ c / P ^ 2 := by
  rw [fN_rsmul, abs_of_pos (inv_pos.mpr hη)] at h
  have e : c * ((P * η)⁻¹) ^ 2 = (c / P ^ 2) / η / η := by field_simp
  rw [e] at h
  have h1 : η⁻¹ * frobNorm D * η * η < c / P ^ 2 := by
    rw [lt_div_iff₀ hη, lt_div_iff₀ hη] at h; linarith
  have e2 : η⁻¹ * frobNorm D * η * η = η * frobNorm D := by field_simp
  linarith

/-! ## 2. the level-`n` cut-off configuration and its bounds -/

section level
variable {L : PeriodicLatticeExtent}

/-- the radius of the region read by level-`n` rows -/
def rN (ell n : ℕ) : ℕ := 2 * rhoT ell n + ell ^ n

/-- the level-`n` cut-off configuration -/
noncomputable def levelCfg (S : Tower L) (ell n : ℕ) (η : ℝ) (A : Bond L → Mt)
    (hA : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0) : PeriodicLinkConfiguration SU2 L :=
  cutCfg η (chiN S n ((rN ell n : ℕ) : ℝ) ((ell : ℝ) ^ (n - 1))) A hA

variable {ell M R k : ℕ} {S : Tower L}

theorem level_bounds (hA : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) (η : ℝ) (hη : 0 < η) (α₀ : ℝ) (A : Bond L → Mt)
    (hB : M1Bounds S ell M 12 k α₀ η A) (hHT : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0)
    (hβ0 : 0 ≤ 12 * (M : ℝ) * α₀) (h4 : 4 * (12 * (M : ℝ) * α₀) ≤ 1) :
    (∀ b, dv (levelCfg S ell n η A hHT b) ≤ alphaQ ell (12 * M * α₀) / (ell : ℝ) ^ n) ∧
    (∀ p : PeriodicLatticePlaquette L, dv (periodicPlaquetteHolonomy (levelCfg S ell n η A hHT) p)
      ≤ alphaQ ell (12 * M * α₀) / ((ell : ℝ) ^ n) ^ 2) := by
  obtain ⟨-, hb1, hb2, -⟩ := hB
  set β : ℝ := 12 * (M : ℝ) * α₀ with hβ
  set w : ℝ := (ell : ℝ) ^ (n - 1) with hw
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hw1 : 1 ≤ w := one_le_pow₀ (by linarith)
  have hw0 : 0 < w := by linarith
  set χ := chiN S n ((rN ell n : ℕ) : ℝ) w with hχ
  have hgood : ∀ x : PeriodicLatticeSite L, χ x ≠ 0 → ∀ e : Bond L, pdist x e.1 ≤ 1 → n - 1 ≤ bstrat S k e :=
    fun x hx e he => goodN hA hell hroom hn1 hnk hx e he
  have hc : ((12 : ℕ) : ℝ) * (M : ℝ) * α₀ = β := by rw [hβ]; norm_num
  -- clause 1 at level n-1
  have hA1 : ∀ e : Bond L, n - 1 ≤ bstrat S k e → η * frobNorm (A e) ≤ β / w := by
    intro e he
    have h := hb1 e (n - 1) he
    rw [hc] at h
    exact units1 η β _ w hη hw0 h
  -- clause 2 at level n-1
  have hA2 : ∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3), n - 1 ≤ bstrat S k (x, ν) →
      n - 1 ≤ bstrat S k (periodicLatticeShift x μ, ν) →
      η * frobNorm (A (periodicLatticeShift x μ, ν) - A (x, ν)) ≤ β / w ^ 2 := by
    intro x μ ν h1 h2
    have h := hb2 μ ν x (n - 1) h1 h2
    rw [hc] at h
    exact units2 η β _ w hη hw0 h
  have hdist1 : ∀ (x : PeriodicLatticeSite L) (μ : Fin 3), pdist (periodicLatticeShift x μ) x ≤ 1 := fun x μ => by
    rw [pdist_comm]; exact pdist_shift_le x μ
  have hd0 : ∀ x : PeriodicLatticeSite L, pdist x x ≤ 1 := fun x => by rw [pdist_self]; exact Nat.zero_le _
  have ha1 : 0 ≤ β / w := by positivity
  have ha1' : β / w ≤ β := div_le_self hβ0 hw1
  have h1e : ∀ e : Bond L, χ e.1 ≠ 0 → η * frobNorm (A e) ≤ β / w :=
    fun e he => hA1 e (hgood e.1 he e (hd0 e.1))
  have hα : 0 ≤ alphaQ ell β := alphaQ_nonneg ell hβ0
  have hpow : (ell : ℝ) ^ n = w * ell := by rw [hw, ← pow_succ]; congr 1; omega
  refine ⟨fun b => ?_, fun p => ?_⟩
  · have h := cut_link η χ A hHT (β / w) hη.le (chiN_nonneg S n _ w) (chiN_le_one S n _ w) ha1 (by linarith) h1e b
    refine h.trans ?_
    rw [hpow, alphaQ]
    have : 2 * β ≤ (ell : ℝ) * (4 * β + 8 * β ^ 2 + 512 * β ^ 3) := by nlinarith [sq_nonneg β, pow_nonneg hβ0 3]
    have e : (ell : ℝ) ^ 2 * (4 * β + 8 * β ^ 2 + 512 * β ^ 3) / (w * ell)
        = ((ell : ℝ) * (4 * β + 8 * β ^ 2 + 512 * β ^ 3)) / w := by field_simp
    rw [e, mul_div_assoc']
    exact div_le_div_of_nonneg_right this hw0.le
  · have h := cut_plaq η χ A hHT (β / w) (β / w ^ 2) (1 / w) hη.le (chiN_nonneg S n _ w) (chiN_le_one S n _ w) ha1
      (by positivity) (by positivity) (by linarith)
      (fun x μ ν hx => hA2 x μ ν (hgood _ hx (x, ν) (hdist1 x μ)) (hgood _ hx _ (hd0 _)))
      (fun x μ ν hx => by
        rcases hx with hx | hx
        · exact hA1 (x, ν) (hgood x hx (x, ν) (hd0 x))
        · exact hA1 (x, ν) (hgood _ hx (x, ν) (hdist1 x μ)))
      (fun x μ => chiN_lip S n _ w hw0 x μ) p
    refine h.trans ?_
    rw [hpow, alphaQ]
    have hw3 : β ^ 3 / w ^ 3 ≤ β ^ 3 / w ^ 2 :=
      div_le_div_of_nonneg_left (pow_nonneg hβ0 3) (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
    have e1 : 2 * (β / w ^ 2 + 1 / w * (β / w)) + 8 * (β / w) ^ 2 + 512 * (β / w) ^ 3
        = (4 * β + 8 * β ^ 2) / w ^ 2 + 512 * (β ^ 3 / w ^ 3) := by field_simp; ring
    have e2 : (ell : ℝ) ^ 2 * (4 * β + 8 * β ^ 2 + 512 * β ^ 3) / (w * ell) ^ 2
        = (4 * β + 8 * β ^ 2) / w ^ 2 + 512 * (β ^ 3 / w ^ 2) := by field_simp
    rw [e1, e2]
    linarith

end level

/-! ## 3. the mask and the counting -/

section mask
variable {L : PeriodicLatticeExtent}

/-- the bonds a level-`n` row can read: `n − 1 ≤ bstrat ≤ n + 1` -/
noncomputable def maskN (S : Tower L) (k n : ℕ) (x : BondFnL2 L) : BondFnL2 L :=
  WithLp.toLp 2 (fun e => if n ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ n + 1 then (WithLp.ofLp x) e else 0)

theorem maskN_norm_sq (S : Tower L) (k n : ℕ) (x : BondFnL2 L) :
    ‖maskN S k n x‖ ^ 2 = ∑ e, if n ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ n + 1 then ‖(WithLp.ofLp x) e‖ ^ 2 else 0 := by
  rw [maskN, PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h : n ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ n + 1
  · simp [h]
  · simp [h]

theorem count_bound (ell k s : ℕ) (hell : 1 ≤ ell) :
    ∑ n : Fin (k + 1), (if (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1 then (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 else 0)
      ≤ 3 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ s)⁻¹) ^ 2 := by
  have hl : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hl0 : (0 : ℝ) < ell := by linarith
  set c : ℝ := (ell : ℝ) ^ 2 * (((ell : ℝ) ^ s)⁻¹) ^ 2 with hcdef
  have hterm : ∀ n : Fin (k + 1), (if (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1 then (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 else 0)
      ≤ if (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1 then c else 0 := by
    intro n
    split_ifs with h
    · have h1 : (ell : ℝ) ^ s ≤ (ell : ℝ) ^ ((n : ℕ) + 1) := pow_le_pow_right₀ hl h.2
      have h2 : ((ell : ℝ) ^ (n : ℕ))⁻¹ ≤ ell * ((ell : ℝ) ^ s)⁻¹ := by
        have e : ((ell : ℝ) ^ (n : ℕ))⁻¹ = ell * ((ell : ℝ) ^ ((n : ℕ) + 1))⁻¹ := by
          rw [pow_succ]; field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (by positivity)
      have h3 := pow_le_pow_left₀ (by positivity) h2 2
      rw [mul_pow] at h3
      rw [hcdef]; exact h3
    · exact le_rfl
  refine (Finset.sum_le_sum (fun n _ => hterm n)).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun n : Fin (k + 1) => (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1)).card ≤ 3 := by
    have h : (Finset.univ.filter (fun n : Fin (k + 1) => (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1)).card
        ≤ (Finset.Icc (s - 1) (s + 1)).card := Finset.card_le_card_of_injOn (fun n : Fin (k + 1) => (n : ℕ)) (by
        intro n hn
        rw [Finset.mem_coe, Finset.mem_filter] at hn
        rw [Finset.mem_coe, Finset.mem_Icc]
        show s - 1 ≤ (n : ℕ) ∧ (n : ℕ) ≤ s + 1
        omega) (by intro a _ b _ hab; exact Fin.ext hab)
    rw [Nat.card_Icc] at h
    omega
  have hc0 : 0 ≤ c := by positivity
  have : ((Finset.univ.filter (fun n : Fin (k + 1) => (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1)).card : ℝ) ≤ 3 := by
    exact_mod_cast hcard
  calc ((Finset.univ.filter (fun n : Fin (k + 1) => (n : ℕ) ≤ s + 1 ∧ s ≤ (n : ℕ) + 1)).card : ℝ) * c ≤ 3 * c :=
        mul_le_mul_of_nonneg_right this hc0
    _ = 3 * (ell : ℝ) ^ 2 * (((ell : ℝ) ^ s)⁻¹) ^ 2 := by rw [hcdef]; ring

/-- **the weighted sum of the level masks** -/
theorem masks_le_wnorm (S : Tower L) (ell k : ℕ) (hell : 1 ≤ ell) (x : BondFnL2 L) :
    ∑ n : Fin (k + 1), (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖maskN S k n x‖ ^ 2 ≤ 3 * (ell : ℝ) ^ 2 * wnormSq S ell k x := by
  simp only [maskN_norm_sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold wnormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hc := count_bound ell k (bstrat S k e) hell
  have hx := sq_nonneg ‖(WithLp.ofLp x) e‖
  have e1 : ∑ n : Fin (k + 1), (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 *
      (if (n : ℕ) ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ (n : ℕ) + 1 then ‖(WithLp.ofLp x) e‖ ^ 2 else 0)
      = (∑ n : Fin (k + 1), (if (n : ℕ) ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ (n : ℕ) + 1
          then (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 else 0)) * ‖(WithLp.ofLp x) e‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> ring
  rw [e1]
  have := mul_le_mul_of_nonneg_right hc hx
  linarith

end mask

/-! ## 4. the gauge step -/

theorem C2full_norm {L : PeriodicLatticeExtent} (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (V : Cfg L)
    (x : BondFnL2 L) (p : BIdx G) :
    ‖C2fullOf G V x p‖ = ((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹ * ‖suOf (C2CompL G.ell (bgTower G V) p.1 (suCoord x) p.2.1)‖ := by
  show ‖(((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (AdalyFormal.IngredientFamilyR2.C2rawB G V p.1 x)) p.2.1‖ = _
  rw [norm_smul, Real.norm_of_nonneg (by positivity), C2rawB_eq]
  rfl

theorem gauge_C2full_norm {L : PeriodicLatticeExtent} (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (U : Cfg L)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (z : BondFnL2 L) (p : BIdx G) :
    ‖C2fullOf G U z p‖ = ‖C2fullOf G (periodicGaugeTransform g U) (AdalyFormal.GaugeCov.adBL g z) p‖ := by
  rw [AdalyFormal.GaugeCov.C2fullOf_gauge G U g z, AdalyFormal.GaugeCov.adFL_apply,
    AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

theorem gauge_wnorm {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (z : BondFnL2 L) :
    wnormSq S ell k (AdalyFormal.GaugeCov.adBL g z) = wnormSq S ell k z := by
  unfold wnormSq
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h : (WithLp.ofLp (AdalyFormal.GaugeCov.adBL g z)) b
      = AdalyFormal.Balaban.CovariantOperators.RMap (g b.1) ((WithLp.ofLp z) b) :=
    AdalyFormal.GaugeCov.adGen_apply (fun b : Bond L => g b.1) z b
  rw [h, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]

#print axioms alphaQ
#print axioms DQSmall
#print axioms K2strat
#print axioms rN
#print axioms levelCfg
#print axioms maskN
#print axioms alphaQ_nonneg
#print axioms units1
#print axioms units2
#print axioms level_bounds
#print axioms maskN_norm_sq
#print axioms count_bound
#print axioms masks_le_wnorm
#print axioms C2full_norm
#print axioms gauge_C2full_norm
#print axioms gauge_wnorm

end AdalyFormal.M1DStrat.DQ

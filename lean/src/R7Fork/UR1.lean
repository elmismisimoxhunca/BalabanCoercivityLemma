import R7Fork.R2RawX
import AdalyFormal.Balaban.SuTwoLogExpTorus

/-!
# UR1 -- the one-step jet `QlinStepX` (an `fderiv` over ALL fine bonds) is the junk `0` as soon as ONE loop of the
background, anywhere on the torus, equals the centre `−1`.

`QlinStepX s ell V0 := fderiv ℝ (qStepX s ell V0) 0` (R2RawX) differentiates the map `XS L → XS L` on the WHOLE
fine torus.  Mathlib's `fderiv` is `0` when the map is not differentiable, and a map into a finite product is
differentiable iff every component is.  Here: on the 120³ torus (the fine torus of the statement's `TT` witness),
with `V0 = cfg1 (−1)` (`−1` on the single bond `b1 = (0, e₀)`, `1` elsewhere), the component of `qStepX 1 2 V0`
at the bond `c = (0, e₀)` is DISCONTINUOUS at `0`: along `a = t·e₀·δ_{b1}`, `t ∈ (0, π)`, its first coordinate is
`3π/4 + t/8` (`qStepX_aT_val`), while at `t = 0` it is `0` (`qStepX_zero`).  Hence `¬ DifferentiableAt`
(`qStepX_not_differentiableAt`) and `QlinStepX 1 2 V0 = 0` (`QlinStepX_bad_eq_zero`).
Mechanism: six of the eight loops `loopVar` of the (43)-average at `c` equal `−1` at `t = 0`, where `su2Log` takes
its junk value `0`; for `t > 0` they are `torus (π − t)` with logarithm `(π − t)·J`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace AdalyFormal.URLocality

open Filter Topology
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath coarsePathEndpoint)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.QjComposite (stepBlockOf mem_stepBlockOf inStepBlock)
open AdalyFormal.Balaban.UbarTowerCov (stridedBlockedGauge cPlusS coarseBondVar gammaVarStrided loopVar)

/-! ## 0. generic objects (any torus) -/

section generic
variable {L : PeriodicLatticeExtent}

/-- the origin site -/
def o0 : PeriodicLatticeSite L := fun _ => ⟨0, Nat.succ_pos _⟩

/-- the bond `b1 = (0, e₀)` -/
def b1 : PeriodicLatticeEdge L := (o0, 0)

/-- the configuration equal to `g` on `b1` and to `1` elsewhere -/
noncomputable def cfg1 (g : SU2) : PeriodicLinkConfiguration SU2 L := fun b => if b = b1 then g else 1

/-- the coordinate field `t·e₀` on `b1`, `0` elsewhere -/
noncomputable def aT (t : ℝ) : XS L := fun b => if b = b1 then (fun i => if i = 0 then t else 0) else 0

/-- bonds visited by a unit-stride forward path -/
def pathBonds : PeriodicLatticeSite L → List (Fin 3) → List (PeriodicLatticeEdge L)
  | _, [] => []
  | y, μ :: r => (y, μ) :: pathBonds (coarseShift y 1 μ) r

theorem hol_cfg1_of_not_mem (g : SU2) (p : List (Fin 3)) :
    ∀ (y : PeriodicLatticeSite L), b1 ∉ pathBonds y p → coarsePathHolonomy 1 (cfg1 g) y p = 1 := by
  induction p with
  | nil => intro y _; rfl
  | cons μ r ih =>
    intro y hy
    simp only [pathBonds, List.mem_cons, not_or] at hy
    show cfg1 g (y, μ) * coarsePathHolonomy 1 (cfg1 g) (coarseShift y 1 μ) r = 1
    rw [ih _ hy.2, mul_one, cfg1, if_neg (fun h => hy.1 h.symm)]

theorem hol_cfg1_cons_b1 (g : SU2) (r : List (Fin 3))
    (hr : b1 ∉ pathBonds (coarseShift (o0 : PeriodicLatticeSite L) 1 0) r) :
    coarsePathHolonomy 1 (cfg1 g) (o0 : PeriodicLatticeSite L) (0 :: r) = g := by
  show cfg1 g (o0, 0) * coarsePathHolonomy 1 (cfg1 g) (coarseShift o0 1 0) r = g
  rw [hol_cfg1_of_not_mem g r _ hr, mul_one]
  unfold cfg1
  exact if_pos rfl

theorem cfg1_mul (g h : SU2) : (fun b => (cfg1 g : PeriodicLinkConfiguration SU2 L) b * cfg1 h b) = cfg1 (g * h) := by
  funext b; unfold cfg1; split_ifs <;> simp

theorem toM2_e0 (t : ℝ) : toM2 (fun i : Fin 3 => if i = 0 then t else 0) = psiR t := by
  rw [psiR_dg]
  ext i j; fin_cases i <;> fin_cases j <;> simp [toM2, dg, Matrix.diagonal] <;> ring

theorem expCfgX_aT (t : ℝ) : expCfgX (aT t : XS L) = cfg1 (torus t) := by
  funext b
  unfold expCfgX aT cfg1
  split_ifs
  · rw [toM2_e0, su2Exp_psiR]
  · simp

theorem aT_zero : (aT 0 : XS L) = 0 := by
  funext b i; unfold aT; split_ifs <;> simp

theorem aT_eq_smul (t : ℝ) : (aT t : XS L) = t • aT 1 := by
  funext b i
  unfold aT
  by_cases hb : b = b1 <;> by_cases hi : i = 0 <;> simp [hb, hi]

end generic

/-! ## 1. the torus group facts -/

theorem torus_inv (t : ℝ) : (torus t)⁻¹ = torus (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← torus_add]; simp

theorem torus_pi : torus Real.pi = su2NegOne := by
  apply Subtype.ext
  rw [coe_torus, coe_su2NegOne, torusM, ← dg_neg_one]
  refine dg_congr ?_ ?_
  · rw [Complex.exp_mul_I]; simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · rw [show -((Real.pi : ℂ) * Complex.I) = (-(Real.pi : ℂ)) * Complex.I by ring, Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem negOne_inv : su2NegOne⁻¹ = su2NegOne := by
  rw [← torus_pi, torus_inv]
  have : torus (-Real.pi) = torus Real.pi * torus (-(2 * Real.pi)) := by rw [← torus_add]; ring_nf
  rw [this]
  have h2 : torus (-(2 * Real.pi)) = 1 := by
    apply Subtype.ext
    rw [coe_torus, coe_one, torusM]
    refine (dg_congr ?_ ?_).trans dg_one
    · rw [Complex.exp_mul_I]; push_cast; simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · rw [show -(((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I]
      simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [h2, mul_one]

theorem psiR_add (a b : ℝ) : psiR a + psiR b = psiR (a + b) := by
  simp only [psiR]; push_cast; rw [add_smul]

theorem qsmul_psiR (q : ℚ) (a : ℝ) : q • psiR a = psiR ((q : ℝ) * a) := by
  rw [qsmul_real, psiR, psiR, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast; ring

theorem nsmul_psiR (n : ℕ) (a : ℝ) : n • psiR a = psiR (n * a) := by
  rw [psiR, psiR, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; push_cast; ring_nf

theorem neg_psiR (a : ℝ) : -psiR a = psiR (-a) := by
  simp only [psiR]; push_cast; rw [neg_smul]

theorem fromM2_psiR (a : ℝ) : fromM2 (psiR a) 0 = a := by
  rw [psiR_dg]; simp [fromM2, dg, Matrix.diagonal]

/-! ## 2. the concrete torus `120³` and the block at the origin -/

/-- the fine extent of the `TT` witness (`(59+1)·2 − 1 = 119`) -/
abbrev L0 : PeriodicLatticeExtent := fun _ => 119

/-- `y + δ`, `δ ∈ {0,1}³` (no wrap for the base sites used) -/
def embAt (y : PeriodicLatticeSite L0) (hy : ∀ μ, (y μ).val + 2 ≤ 120) (δ : Fin 3 → Fin 2) :
    PeriodicLatticeSite L0 :=
  fun μ => ⟨(y μ).val + (δ μ).val, by
    have h1 := hy μ; have h2 := (δ μ).isLt
    show (y μ).val + (δ μ).val < 119 + 1
    omega⟩

theorem embAt_inj (y : PeriodicLatticeSite L0) (hy : ∀ μ, (y μ).val + 2 ≤ 120) :
    Function.Injective (embAt y hy) := by
  intro δ δ' h
  funext μ
  have := congrArg (fun x : PeriodicLatticeSite L0 => (x μ).val) h
  simp only [embAt] at this
  exact Fin.ext (by omega)

theorem stepBlock_eq (y : PeriodicLatticeSite L0) (hy : ∀ μ, (y μ).val + 2 ≤ 120) :
    stepBlockOf y 1 2 = Finset.univ.image (embAt y hy) := by
  ext x
  rw [mem_stepBlockOf, Finset.mem_image]
  constructor
  · intro h
    refine ⟨fun μ => ⟨(x μ).val - (y μ).val, by have := (h μ).2.1; have := (h μ).1; omega⟩, Finset.mem_univ _, ?_⟩
    funext μ
    apply Fin.ext
    simp only [embAt]
    have := (h μ).1
    omega
  · rintro ⟨δ, -, rfl⟩ μ
    simp only [embAt]
    have := (δ μ).isLt
    exact ⟨by omega, by omega, one_dvd _⟩

theorem oo_ok : ∀ μ, ((o0 : PeriodicLatticeSite L0) μ).val + 2 ≤ 120 := by intro μ; simp [o0]

/-- `c₊ = 2e₀` -/
def cP : PeriodicLatticeSite L0 := fun μ => if μ = 0 then 2 else 0
theorem cP_ok : ∀ μ, (cP μ).val + 2 ≤ 120 := by decide

theorem cPlus_eq : cPlusS 1 2 ((o0, 0) : PeriodicLatticeEdge L0) = cP := by decide

def d000 : Fin 3 → Fin 2 := ![0, 0, 0]
def d100 : Fin 3 → Fin 2 := ![1, 0, 0]

/-- THE PATH FACTS (kernel `decide` on the 120³ torus): which loops at `c = (0,e₀)` pass through `b1`. -/
theorem paths_avoid :
    ∀ δ : Fin 3 → Fin 2, δ ≠ d000 → δ ≠ d100 →
      (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (o0 : PeriodicLatticeSite L0) (coarseGammaPath 1 (o0 : PeriodicLatticeSite L0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok δ)) ∧
      (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (embAt (o0 : PeriodicLatticeSite L0) oo_ok δ) [0, 0] ∧
      (b1 : PeriodicLatticeEdge L0) ∉ pathBonds cP (coarseGammaPath 1 (o0 : PeriodicLatticeSite L0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok δ)) := by
  decide

theorem path_000 : coarseGammaPath 1 (o0 : PeriodicLatticeSite L0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok d000) = [] := by decide
theorem path_100 : coarseGammaPath 1 (o0 : PeriodicLatticeSite L0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok d100) = [0] := by decide
theorem emb_000 : embAt (o0 : PeriodicLatticeSite L0) oo_ok d000 = (o0 : PeriodicLatticeSite L0) := by decide
theorem bond_tail : (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (coarseShift (o0 : PeriodicLatticeSite L0) 1 0) [0] := by decide
theorem bond_tail0 : (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (coarseShift (o0 : PeriodicLatticeSite L0) 1 0) [] := by decide
theorem e0_bonds : (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (embAt (o0 : PeriodicLatticeSite L0) oo_ok d100) [0, 0] := by decide
theorem cP_bonds1 : (b1 : PeriodicLatticeEdge L0) ∉ pathBonds cP [0] := by decide
theorem rprod_avoid : ∀ δ : Fin 3 → Fin 2, δ ≠ d100 →
    (b1 : PeriodicLatticeEdge L0) ∉ pathBonds (o0 : PeriodicLatticeSite L0) (coarseGammaPath 1 (o0 : PeriodicLatticeSite L0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok δ)) := by decide
theorem rprodP_avoid : ∀ δ : Fin 3 → Fin 2,
    (b1 : PeriodicLatticeEdge L0) ∉ pathBonds cP (coarseGammaPath 1 cP (embAt cP cP_ok δ)) := by decide
theorem card_bad : (Finset.univ.filter (fun δ : Fin 3 → Fin 2 => ¬ (δ = d000 ∨ δ = d100))).card = 6 := by decide

/-! ## 3. the loops and the (43)-average at `c = (0,e₀)` for `cfg1 g` -/

theorem coarseBondVar_cfg1 (g : SU2) : coarseBondVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (o0, 0) = g := by
  show coarsePathHolonomy 1 (cfg1 g) (o0 : PeriodicLatticeSite L0) [0, 0] = g
  exact hol_cfg1_cons_b1 g [0] bond_tail

theorem loopVar_cfg1 (g : SU2) (δ : Fin 3 → Fin 2) :
    loopVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (o0, 0) (embAt (o0 : PeriodicLatticeSite L0) oo_ok δ)
      = if δ = d000 ∨ δ = d100 then 1 else g⁻¹ := by
  unfold loopVar gammaVarStrided
  rw [coarseBondVar_cfg1, cPlus_eq]
  dsimp only [List.replicate]
  split_ifs with h
  · rcases h with rfl | rfl
    · rw [path_000, emb_000, hol_cfg1_cons_b1 g [0] bond_tail]
      show 1 * g * (1 : SU2)⁻¹ * g⁻¹ = 1
      group
    · rw [path_100, hol_cfg1_cons_b1 g [] bond_tail0, hol_cfg1_of_not_mem g _ _ e0_bonds,
        hol_cfg1_of_not_mem g _ _ cP_bonds1]
      group
  · have h' : δ ≠ d000 ∧ δ ≠ d100 := ⟨fun e => h (Or.inl e), fun e => h (Or.inr e)⟩
    obtain ⟨h1, h2, h3⟩ := paths_avoid δ h'.1 h'.2
    rw [hol_cfg1_of_not_mem g _ _ h1, hol_cfg1_of_not_mem g _ _ h2, hol_cfg1_of_not_mem g _ _ h3]
    group

/-- `Σ_x ℓ^{-3} log loopVar = 6·ℓ^{-3}·log g⁻¹` -/
theorem avgSum_cfg1 (g : SU2) :
    (∑ x ∈ stepBlockOf (o0 : PeriodicLatticeSite L0) 1 2,
        ((2 : ℚ) ^ 3)⁻¹ • su2Log (loopVar 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (o0, 0) x))
      = (6 : ℕ) • (((2 : ℚ) ^ 3)⁻¹ • su2Log g⁻¹) := by
  rw [stepBlock_eq (o0 : PeriodicLatticeSite L0) oo_ok, Finset.sum_image (fun δ _ δ' _ h => embAt_inj (o0 : PeriodicLatticeSite L0) oo_ok h)]
  simp_rw [loopVar_cfg1]
  rw [← card_bad, ← Finset.sum_const, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  split_ifs <;> simp_all

theorem ubar_cfg1 (g : SU2) :
    stridedBlockedGauge su2LogExp 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (o0, 0)
      = su2Exp ((6 : ℕ) • (((2 : ℚ) ^ 3)⁻¹ • su2Log g⁻¹)) * g := by
  unfold stridedBlockedGauge
  rw [su2LogExp_exp, ← avgSum_cfg1 g, coarseBondVar_cfg1]
  rfl

/-! ## 4. the `sBlock` terms -/

theorem sBlock_o (h g : SU2) :
    sBlock 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (cfg1 h) (o0 : PeriodicLatticeSite L0)
      = ((2 : ℚ) ^ 3)⁻¹ • su2Log ((h * g) * g⁻¹) := by
  unfold sBlock
  rw [stepBlock_eq (o0 : PeriodicLatticeSite L0) oo_ok, Finset.sum_image (fun δ _ δ' _ hh => embAt_inj (o0 : PeriodicLatticeSite L0) oo_ok hh)]
  rw [Finset.sum_eq_single d100]
  · rw [rProd_eq, path_100, cfg1_mul, hol_cfg1_cons_b1 _ [] bond_tail0, hol_cfg1_cons_b1 _ [] bond_tail0]
    simp only [Nat.cast_ofNat]
  · intro δ _ hδ
    rw [rProd_eq, cfg1_mul, hol_cfg1_of_not_mem _ _ _ (rprod_avoid δ hδ),
      hol_cfg1_of_not_mem _ _ _ (rprod_avoid δ hδ)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sBlock_cP (h g : SU2) :
    sBlock 1 2 (cfg1 g : PeriodicLinkConfiguration SU2 L0) (cfg1 h) cP = 0 := by
  unfold sBlock
  rw [stepBlock_eq cP cP_ok, Finset.sum_image (fun δ _ δ' _ hh => embAt_inj cP cP_ok hh)]
  refine Finset.sum_eq_zero (fun δ _ => ?_)
  rw [rProd_eq, cfg1_mul, hol_cfg1_of_not_mem _ _ _ (rprodP_avoid δ),
    hol_cfg1_of_not_mem _ _ _ (rprodP_avoid δ)]
  simp

/-! ## 5. the raw step at `c` along `a = t e₀ δ_{b1}`, `0 < t < π` -/

theorem rawStep_aT {t : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi) :
    rawStep 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0) (expCfgX (aT t)) (o0, 0)
      = torus (3 * Real.pi / 4 + t / 8) := by
  have hn : su2NegOne⁻¹ = su2NegOne := negOne_inv
  have hlog1 : su2Log ((torus t * su2NegOne) * su2NegOne⁻¹) = psiR t := by
    rw [mul_assoc, mul_inv_cancel, mul_one, su2Log_torus ht0.le htpi]
  have hinv : (torus t * su2NegOne)⁻¹ = torus (Real.pi - t) := by
    rw [mul_inv_rev, hn, torus_inv, ← torus_pi, ← torus_add]; ring_nf
  have hlog2 : su2Log (torus t * su2NegOne)⁻¹ = psiR (Real.pi - t) := by
    rw [hinv, su2Log_torus (by linarith) (by linarith)]
  rw [rawStep_simp, expCfgX_aT, cfg1_mul]
  dsimp only
  rw [ubar_cfg1, ubar_cfg1, sBlock_o, cPlus_eq, sBlock_cP, hlog1, hlog2, hn, su2Log_center]
  simp only [smul_zero, su2Exp_zero, one_mul, mul_one, qsmul_psiR, nsmul_psiR, neg_psiR, su2Exp_psiR]
  rw [← torus_pi, torus_inv]
  simp only [← torus_add]
  congr 1
  push_cast
  ring

theorem qStepX_aT_val {t : ℝ} (ht0 : 0 < t) (htpi : t < Real.pi) :
    qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0) (aT t) (o0, 0) 0 = 3 * Real.pi / 4 + t / 8 := by
  unfold qStepX
  rw [rawStep_aT ht0 htpi, su2Log_torus (by positivity) (by linarith [Real.pi_pos]), fromM2_psiR]

/-! ## 6. discontinuity, non-differentiability, junk jet -/

theorem qStepX_not_differentiableAt0 :
    ¬ DifferentiableAt ℝ (qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0)) 0 := by
  intro hd
  have hc := hd.continuousAt
  set F : ℝ → ℝ := fun t => qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0) (aT t) (o0, 0) 0 with hF
  have hcont_aT : Continuous (fun t : ℝ => (aT t : XS L0)) := by
    have : (fun t : ℝ => (aT t : XS L0)) = fun t => t • aT 1 := funext aT_eq_smul
    rw [this]; exact continuous_id.smul continuous_const
  have hFc : ContinuousAt F 0 := by
    have h1 : ContinuousAt (fun t : ℝ => qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0) (aT t)) 0 := by
      have : (aT 0 : XS L0) = 0 := aT_zero
      refine ContinuousAt.comp (g := qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L0)) ?_ hcont_aT.continuousAt
      rw [this]; exact hc
    exact ((continuous_apply 0).continuousAt.comp ((continuous_apply ((o0, 0) : PeriodicLatticeEdge L0)).continuousAt.comp h1))
  have hF0 : F 0 = 0 := by
    simp only [hF, aT_zero, qStepX_zero]; rfl
  have hlim1 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := hFc.tendsto
    rw [hF0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : F =ᶠ[𝓝[>] 0] fun t => 3 * Real.pi / 4 + t / 8 := by
    have : Set.Ioo (0 : ℝ) Real.pi ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT Real.pi_pos
    filter_upwards [this] with t ht
    exact qStepX_aT_val ht.1 ht.2
  have hlim2 : Tendsto F (𝓝[>] 0) (𝓝 (3 * Real.pi / 4 + 0 / 8)) := by
    refine Tendsto.congr' hev.symm ?_
    exact ((continuous_const.add (continuous_id.div_const 8)).tendsto 0).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique hlim1 hlim2
  have hp := Real.pi_pos
  linarith

/-- the same at any torus equal to `L0` (e.g. `scaleUp 2 1 (fun _ => 59)`) -/
theorem qStepX_not_differentiableAt {L : PeriodicLatticeExtent} (hL : L = L0) :
    ¬ DifferentiableAt ℝ (qStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L)) 0 := by
  subst hL; exact qStepX_not_differentiableAt0

/-- **THE JUNK JET**: the printed one-step linear part `L Q(V₀)` (an `fderiv` over all fine bonds) is the zero
operator at a background with one centre-valued bond, at EVERY bond of the torus. -/
theorem QlinStepX_bad_eq_zero {L : PeriodicLatticeExtent} (hL : L = L0) :
    QlinStepX 1 2 (cfg1 su2NegOne : PeriodicLinkConfiguration SU2 L) = 0 :=
  fderiv_zero_of_not_differentiableAt (qStepX_not_differentiableAt hL)

#print axioms qStepX_aT_val
#print axioms qStepX_not_differentiableAt
#print axioms QlinStepX_bad_eq_zero

end AdalyFormal.URLocality

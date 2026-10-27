import RI2

/-!
# RI3 -- weighted norm and COVARIANT gradient of the twisted right inverse `EU` (lane m2_rightinv_20261015)

* `gradWU_gauge` : `gradWU V ((adBL γ)⁻¹ f) μ = gradWU (V^γ) f μ` (exact gauge covariance, `V^γ(x,μ) = γ(x) V γ(x+μ)⁻¹`).
* `gradWU_le_chart` : `gradWU V f μ ≤ 2 gradW f μ + 8 Σ_b ‖V(b₋,μ) − 1‖²_F ‖f(b₋+μ, b.dir)‖²`;  `gradWU_crude` : `≤ 4‖f‖²`.
* `FineOK U γ τ` : for every row `p` of level `≥ 1`, the fine links of `U^{γ_p}` within `20 ℓ^{lev p + 1}` of `z_p` are within
  `τ ℓ^{-lev p}` of `1` (Frobenius).
* `grad_src`, `wnorm_src` : one source, in its own gauge: `gradWU U (srcL γ p w) μ ≤ Cg1 τ · wD p ‖w‖²`, `wnormSq ≤ ℓ² CE wD p ‖w‖²`.
* `card_Fb` : a bond carries the kernels of at most `2187` rows (`phi_strat`, `card_rows_near`).
* **`EU_wnorm`**, **`EU_grad`** : `wnormSq (EU v) ≤ 2187 ℓ² CE nD v`, `gradWU U (EU v) μ ≤ 4374 Cg1 τ nD v`.
No difference of the gauges of two DIFFERENT rows appears anywhere.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace AdalyFormal.M2RightInv

open Finset
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap RMap_mul RMap_one)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg norm_RMap_sub_self_le)
open AdalyFormal.Balaban.AlphaAnalyticity (norm_RMap)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneR8 (pdist_triangle pdist_comm pdist_shift_le pdist_coarseShift_le)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.AlphaAnalyticity (GaugeFn)
open AdalyFormal.W6 (nD wD wD_pos nD_nonneg nF wF gradW GE CE CE_pos GE_pos E_grad E_wnorm EflatL phiK phi_strat phi_support
  pdist_block_le)
open AdalyFormal.M2W6 (sglL psiL psiL_apply psiL_norm_sq srcL EU EU_apply card_rows_near)
open AdalyFormal.M1DStrat (gradWU gradWU_nonneg)
open AdalyFormal.GaugeCov (adBL adGen_symm_apply)
open AdalyFormal.DLayer (sum_shift_site)

section gen
variable {L : PeriodicLatticeExtent}

/-- shifting the base site of every bond permutes the bonds -/
theorem sum_shift_bond (μ : Fin 3) (g : Bond L → ℝ) :
    ∑ b : Bond L, g (periodicLatticeShift b.1 μ, b.2) = ∑ b : Bond L, g b := by
  rw [show (Finset.univ : Finset (Bond L)) = Finset.univ ×ˢ Finset.univ from rfl, Finset.sum_product_right,
    Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  exact sum_shift_site μ (fun x => g (x, ν))

/-- **gauge covariance of the covariant gradient** -/
theorem gradWU_gauge (V : LinkCfg L) (γ : GaugeFn L) (f : BondFnL2 L) (μ : Fin 3) :
    gradWU V ((adBL γ).symm f) μ = gradWU (periodicGaugeTransform γ V) f μ := by
  unfold gradWU
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have e1 := adGen_symm_apply (fun b : Bond L => γ b.1) f (periodicLatticeShift b.1 μ, b.2)
  have e2 := adGen_symm_apply (fun b : Bond L => γ b.1) f b
  have hl : ((adBL γ).symm f) (periodicLatticeShift b.1 μ, b.2) = RMap ((γ (periodicLatticeShift b.1 μ))⁻¹)
      (f (periodicLatticeShift b.1 μ, b.2)) := e1
  have hr : ((adBL γ).symm f) b = RMap ((γ b.1)⁻¹) (f b) := e2
  rw [hl, hr]
  congr 1
  set g := γ b.1
  set g' := γ (periodicLatticeShift b.1 μ)
  set a := f (periodicLatticeShift b.1 μ, b.2)
  set c := f b
  have key : RMap (V (b.1, μ)) (RMap g'⁻¹ a) - RMap g⁻¹ c
      = RMap g⁻¹ (RMap (g * V (b.1, μ) * g'⁻¹) a - c) := by
    rw [map_sub]
    congr 1
    have h1 : g⁻¹ * (g * V (b.1, μ) * g'⁻¹) = V (b.1, μ) * g'⁻¹ := by group
    rw [← LinearMap.comp_apply (RMap g⁻¹) (RMap (g * V (b.1, μ) * g'⁻¹)), ← RMap_mul, h1, RMap_mul,
      LinearMap.comp_apply]
  rw [key, norm_RMap]
  rfl

/-- the covariant gradient by the flat gradient and the link deviation -/
theorem gradWU_le_chart (V : LinkCfg L) (f : BondFnL2 L) (μ : Fin 3) :
    gradWU V f μ ≤ 2 * gradW f μ + 8 * ∑ b : Bond L,
      frobNorm (((V (b.1, μ) : SU2) : M2) - 1) ^ 2 * ‖f (periodicLatticeShift b.1 μ, b.2)‖ ^ 2 := by
  unfold gradWU gradW
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun b _ => ?_)
  set a := f (periodicLatticeShift b.1 μ, b.2)
  set c := f b
  set F := frobNorm (((V (b.1, μ) : SU2) : M2) - 1)
  have hF : 0 ≤ F := frobNorm_nonneg _
  have h1 : ‖RMap (V (b.1, μ)) a - c‖ ≤ ‖a - c‖ + 2 * F * ‖a‖ := by
    calc ‖RMap (V (b.1, μ)) a - c‖ = ‖(a - c) + (RMap (V (b.1, μ)) a - a)‖ := by congr 1; abel
      _ ≤ ‖a - c‖ + ‖RMap (V (b.1, μ)) a - a‖ := norm_add_le _ _
      _ ≤ ‖a - c‖ + 2 * F * ‖a‖ := by have := norm_RMap_sub_self_le (V (b.1, μ)) a; linarith
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a - c‖ - 2 * F * ‖a‖), norm_nonneg a, norm_nonneg (a - c)]

/-- the crude covariant gradient bound -/
theorem gradWU_crude (V : LinkCfg L) (f : BondFnL2 L) (μ : Fin 3) : gradWU V f μ ≤ 4 * ‖f‖ ^ 2 := by
  have hn : ‖f‖ ^ 2 = ∑ b : Bond L, ‖f b‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
  have hs : ∑ b : Bond L, ‖f (periodicLatticeShift b.1 μ, b.2)‖ ^ 2 = ∑ b : Bond L, ‖f b‖ ^ 2 :=
    sum_shift_bond μ (fun b => ‖f b‖ ^ 2)
  unfold gradWU
  have hpt : ∀ b : Bond L, ‖RMap (V (b.1, μ)) (f (periodicLatticeShift b.1 μ, b.2)) - f b‖ ^ 2
      ≤ 2 * ‖f (periodicLatticeShift b.1 μ, b.2)‖ ^ 2 + 2 * ‖f b‖ ^ 2 := by
    intro b
    have h1 : ‖RMap (V (b.1, μ)) (f (periodicLatticeShift b.1 μ, b.2)) - f b‖
        ≤ ‖f (periodicLatticeShift b.1 μ, b.2)‖ + ‖f b‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_RMap]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖f (periodicLatticeShift b.1 μ, b.2)‖ - ‖f b‖)]
  refine (Finset.sum_le_sum (fun b _ => hpt b)).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hn]
  linarith

end gen

section src
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}

theorem srcL_apply (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p : BIdx (geomOf ell k S)) (w : SuTwo) (b : Bond (scaleUp ell k Lu)) :
    (srcL hell γ p w) b = RMap (((γ p) b.1)⁻¹) (phiK hell p b • RMap ((γ p) p.2.1.1) w) := by
  have h1 := adGen_symm_apply (fun b : Bond (scaleUp ell k Lu) => (γ p) b.1)
    (psiL hell p (RMap ((γ p) p.2.1.1) w)) b
  calc (srcL hell γ p w) b = RMap (((γ p) b.1)⁻¹) ((psiL hell p (RMap ((γ p) p.2.1.1) w)) b) := h1
    _ = _ := by rw [psiL_apply]

/-- the kernel of a row lives within `4 ℓ^{lev p}` of its base -/
theorem phi_near (hell : 0 < ell) (p : BIdx (geomOf ell k S)) (b : Bond (scaleUp ell k Lu))
    (h : phiK hell p b ≠ 0) : pdist p.2.1.1 b.1 ≤ 4 * ell ^ (p.1 : ℕ) := by
  obtain ⟨-, hs⟩ := phi_support hell p b h
  rcases hs with ⟨-, hb⟩ | ⟨-, hb⟩
  · have := pdist_block_le hb; omega
  · have h1 := pdist_block_le hb
    have h2 := pdist_coarseShift_le p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2
    have h3 := pdist_triangle p.2.1.1
      (AdalyFormal.Balaban.CoarseCurl.coarseShift p.2.1.1 (ell ^ (p.1 : ℕ)) p.2.1.2) b.1
    omega

/-- **fine-link closeness of each row's gauge on its ball** (rows of level `≥ 1`) -/
def FineOK (U : LinkCfg (scaleUp ell k Lu)) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (τ : ℝ) : Prop :=
  ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) → ∀ x : PeriodicLatticeSite (scaleUp ell k Lu),
    pdist p.2.1.1 x ≤ 20 * ell ^ ((p.1 : ℕ) + 1) → ∀ μ : Fin 3,
      frobNorm (((periodicGaugeTransform (γ p) U (x, μ) : SU2) : M2) - 1) ≤ τ * ((ell : ℝ) ^ (p.1 : ℕ))⁻¹

/-- the per-source gradient constant -/
def Cg1 (τ : ℝ) : ℝ := 4 * GE + 8 * τ ^ 2 * CE + 4 * CE

theorem Cg1_nonneg (τ : ℝ) : 0 ≤ Cg1 τ := by
  unfold Cg1; have := CE_pos; have := GE_pos; positivity

/-- **one source, covariant gradient, in its own gauge** -/
theorem grad_src (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {τ : ℝ} (hτ : 0 ≤ τ) (hfine : FineOK U γ τ)
    (p : BIdx (geomOf ell k S)) (w : SuTwo) (μ : Fin 3) :
    gradWU U (srcL hell γ p w) μ ≤ Cg1 τ * (wD p * ‖w‖ ^ 2) := by
  set w' := RMap ((γ p) p.2.1.1) w with hw'd
  have hw' : ‖w'‖ = ‖w‖ := norm_RMap _ _
  have e : srcL hell γ p w = (adBL (γ p)).symm (psiL hell p w') := rfl
  rw [e, gradWU_gauge]
  set ψ := psiL hell p w' with hψd
  have hψ := psiL_norm_sq hell hell2 hS p w'
  rw [hw'] at hψ
  have hCE := CE_pos
  have hGE := GE_pos
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hwD0 : 0 ≤ wD p * ‖w‖ ^ 2 := mul_nonneg (wD_pos hell p).le (sq_nonneg _)
  rcases Nat.eq_zero_or_pos (p.1 : ℕ) with h0 | h1
  · have hc := gradWU_crude (periodicGaugeTransform (γ p) U) ψ μ
    have hwF : wF p = wD p := by
      show ((ell : ℝ) ^ (p.1 : ℕ)) ^ 3 = (ell : ℝ) ^ (p.1 : ℕ)
      rw [h0]; norm_num
    rw [hwF] at hψ
    unfold Cg1
    have : 0 ≤ (4 * GE + 8 * τ ^ 2 * CE) * (wD p * ‖w‖ ^ 2) := by positivity
    nlinarith
  · have hc := gradWU_le_chart (periodicGaugeTransform (γ p) U) ψ μ
    have hg : gradW ψ μ ≤ 2 * GE * (wD p * ‖w‖ ^ 2) := by
      have h := E_grad hell hell2 hS (sglL p w') μ
      rw [nD_sglL, hw'] at h
      exact h
    set a : ℝ := (ell : ℝ) ^ (p.1 : ℕ) with had
    have ha0 : 0 < a := by rw [had]; positivity
    have hlink : ∑ b : Bond (scaleUp ell k Lu),
        frobNorm (((periodicGaugeTransform (γ p) U (b.1, μ) : SU2) : M2) - 1) ^ 2 * ‖ψ (periodicLatticeShift b.1 μ, b.2)‖ ^ 2
        ≤ ∑ b : Bond (scaleUp ell k Lu), (τ * a⁻¹) ^ 2 * ‖ψ (periodicLatticeShift b.1 μ, b.2)‖ ^ 2 := by
      refine Finset.sum_le_sum (fun b _ => ?_)
      by_cases hz : ψ (periodicLatticeShift b.1 μ, b.2) = 0
      · rw [hz, norm_zero]; simp
      · have hphi : phiK hell p (periodicLatticeShift b.1 μ, b.2) ≠ 0 := by
          intro h; apply hz; rw [hψd, psiL_apply, h, zero_smul]
        have hn : pdist p.2.1.1 (periodicLatticeShift b.1 μ) ≤ 4 * ell ^ (p.1 : ℕ) := phi_near hell p _ hphi
        have hd1 := pdist_shift_le b.1 μ
        rw [pdist_comm] at hd1
        have hd2 := pdist_triangle p.2.1.1 (periodicLatticeShift b.1 μ) b.1
        have hpow : ell ^ (p.1 : ℕ) ≤ ell ^ ((p.1 : ℕ) + 1) := Nat.pow_le_pow_right hell (by omega)
        have hone : 1 ≤ ell ^ (p.1 : ℕ) := Nat.one_le_pow _ _ hell
        have hx : pdist p.2.1.1 b.1 ≤ 20 * ell ^ ((p.1 : ℕ) + 1) := by omega
        have hF := hfine p h1 b.1 hx μ
        have hF0 := frobNorm_nonneg (((periodicGaugeTransform (γ p) U (b.1, μ) : SU2) : M2) - 1)
        have hsq := pow_le_pow_left₀ hF0 hF 2
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hsum : ∑ b : Bond (scaleUp ell k Lu), (τ * a⁻¹) ^ 2 * ‖ψ (periodicLatticeShift b.1 μ, b.2)‖ ^ 2
        = (τ * a⁻¹) ^ 2 * ‖ψ‖ ^ 2 := by
      rw [← Finset.mul_sum, sum_shift_bond μ (fun b => ‖ψ b‖ ^ 2), PiLp.norm_sq_eq_of_L2]
    rw [hsum] at hlink
    have hwF : wF p = a ^ 3 := rfl
    have hwD : wD p = a := rfl
    rw [hwF] at hψ
    have hb : (τ * a⁻¹) ^ 2 * ‖ψ‖ ^ 2 ≤ τ ^ 2 * CE * (wD p * ‖w‖ ^ 2) := by
      have h2 : (τ * a⁻¹) ^ 2 * ‖ψ‖ ^ 2 ≤ (τ * a⁻¹) ^ 2 * (CE * (a ^ 3 * ‖w‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hψ (sq_nonneg _)
      have e : (τ * a⁻¹) ^ 2 * (CE * (a ^ 3 * ‖w‖ ^ 2)) = τ ^ 2 * CE * (a * ‖w‖ ^ 2) := by
        field_simp
      rw [hwD]; linarith
    unfold Cg1
    have : 0 ≤ 4 * CE * (wD p * ‖w‖ ^ 2) := by positivity
    nlinarith

/-- **one source, weighted norm** -/
theorem wnorm_src (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hR1 : 1 ≤ R) (hM : 1 ≤ M)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (p : BIdx (geomOf ell k S)) (w : SuTwo) :
    AdalyFormal.M1.wnormSq S ell k (srcL hell γ p w) ≤ (ell : ℝ) ^ 2 * CE * (wD p * ‖w‖ ^ 2) := by
  set w' := RMap ((γ p) p.2.1.1) w with hw'd
  have hw' : ‖w'‖ = ‖w‖ := norm_RMap _ _
  have e : AdalyFormal.M1.wnormSq S ell k (srcL hell γ p w) = AdalyFormal.M1.wnormSq S ell k (psiL hell p w') := by
    unfold AdalyFormal.M1.wnormSq
    refine Finset.sum_congr rfl (fun b _ => ?_)
    congr 2
    show ‖(srcL hell γ p w) b‖ = ‖(psiL hell p w') b‖
    rw [srcL_apply, norm_RMap, psiL_apply]
  rw [e]
  have h := E_wnorm hell hell2 hS hR1 hM (sglL p w')
  rw [nD_sglL, hw'] at h
  exact h

open Classical in
/-- the rows whose kernel can touch the bond `b` -/
def Fb (ell k : ℕ) {Lu : PeriodicLatticeExtent} (S : Tower (scaleUp ell k Lu)) (b : Bond (scaleUp ell k Lu)) :
    Finset (BIdx (geomOf ell k S)) :=
  Finset.univ.filter (fun p : BIdx (geomOf ell k S) => (p.1 : ℕ) = AdalyFormal.M1.strat S k b.1 ∧
    pdist p.2.1.1 b.1 ≤ 4 * ell ^ (AdalyFormal.M1.strat S k b.1))

theorem card_Fb (hell : 0 < ell) (b : Bond (scaleUp ell k Lu)) : (Fb ell k S b).card ≤ 2187 := by
  classical
  set l := AdalyFormal.M1.strat S k b.1 with hl
  have h := card_rows_near (S := S) hell l (AdalyFormal.M1.strat_le S k b.1) b.1 (4 * ell ^ l)
  have e : 2 * (4 * ell ^ l) / ell ^ l = 8 := by
    rw [show 2 * (4 * ell ^ l) = 8 * ell ^ l by ring]
    exact Nat.mul_div_cancel 8 (pow_pos hell l)
  rw [e] at h
  refine le_trans (Finset.card_le_card ?_) (le_of_le_of_eq h (by norm_num))
  intro p hp
  simp only [Fb, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp

theorem mem_Fb (hell : 0 < ell) (hS : Admissible ell M R k S) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu))
    (p : BIdx (geomOf ell k S)) (w : SuTwo) (b : Bond (scaleUp ell k Lu)) (h : (srcL hell γ p w) b ≠ 0) :
    p ∈ Fb ell k S b := by
  classical
  have hphi : phiK hell p b ≠ 0 := by
    intro h0; apply h; rw [srcL_apply, h0, zero_smul, map_zero]
  have hs := phi_strat hell hS p b hphi
  have hn := phi_near hell p b hphi
  simp only [Fb, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hs.symm, ?_⟩
  rw [hs]; exact hn

theorem EU_pt (hell : 0 < ell) (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (v : FSp (geomOf ell k S))
    (b : Bond (scaleUp ell k Lu)) : (EU hell γ v) b = ∑ p, (srcL hell γ p (v p)) b := by
  rw [EU_apply, WithLp.ofLp_sum, Finset.sum_apply]

/-- **weighted norm of the twisted right inverse** -/
theorem EU_wnorm (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hR1 : 1 ≤ R) (hM : 1 ≤ M)
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) (v : FSp (geomOf ell k S)) :
    AdalyFormal.M1.wnormSq S ell k (EU hell γ v) ≤ 2187 * ((ell : ℝ) ^ 2 * CE) * nD v := by
  have hpt : ∀ b : Bond (scaleUp ell k Lu),
      ‖(EU hell γ v) b‖ ^ 2 ≤ 2187 * ∑ p, ‖(srcL hell γ p (v p)) b‖ ^ 2 := by
    intro b
    rw [EU_pt]
    have h := norm_sq_sum_le_card (Fb ell k S b) (fun p => (srcL hell γ p (v p)) b)
      (fun p hp => by by_contra hne; exact hp (mem_Fb hell hS γ p (v p) b hne))
    have hc : ((Fb ell k S b).card : ℝ) ≤ 2187 := by exact_mod_cast card_Fb hell b
    exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  unfold AdalyFormal.M1.wnormSq
  calc ∑ b, (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * ‖(EU hell γ v) b‖ ^ 2
      ≤ ∑ b, (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * (2187 * ∑ p, ‖(srcL hell γ p (v p)) b‖ ^ 2) :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hpt b) (sq_nonneg _))
    _ = ∑ b, ∑ p, 2187 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * ‖(srcL hell γ p (v p)) b‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
    _ = ∑ p, ∑ b, 2187 * ((((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * ‖(srcL hell γ p (v p)) b‖ ^ 2) :=
        Finset.sum_comm
    _ = 2187 * ∑ p, ∑ b, (((ell : ℝ) ^ AdalyFormal.M1.bstrat S k b)⁻¹) ^ 2 * ‖(srcL hell γ p (v p)) b‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ 2187 * ∑ p, (ell : ℝ) ^ 2 * CE * (wD p * ‖v p‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => ?_)) (by norm_num)
        exact wnorm_src hell hell2 hS hR1 hM γ p (v p)
    _ = 2187 * ((ell : ℝ) ^ 2 * CE) * nD v := by
        rw [← Finset.mul_sum]; unfold nD; ring

/-- **covariant gradient of the twisted right inverse** -/
theorem EU_grad (hell : 0 < ell) (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (U : LinkCfg (scaleUp ell k Lu))
    (γ : BIdx (geomOf ell k S) → GaugeFn (scaleUp ell k Lu)) {τ : ℝ} (hτ : 0 ≤ τ) (hfine : FineOK U γ τ)
    (v : FSp (geomOf ell k S)) (μ : Fin 3) :
    gradWU U (EU hell γ v) μ ≤ 4374 * Cg1 τ * nD v := by
  classical
  have hpt : ∀ b : Bond (scaleUp ell k Lu),
      ‖RMap (U (b.1, μ)) ((EU hell γ v) (periodicLatticeShift b.1 μ, b.2)) - (EU hell γ v) b‖ ^ 2
        ≤ 4374 * ∑ p, ‖RMap (U (b.1, μ)) ((srcL hell γ p (v p)) (periodicLatticeShift b.1 μ, b.2))
            - (srcL hell γ p (v p)) b‖ ^ 2 := by
    intro b
    rw [EU_pt, EU_pt, map_sum, ← Finset.sum_sub_distrib]
    set b' : Bond (scaleUp ell k Lu) := (periodicLatticeShift b.1 μ, b.2)
    have h := norm_sq_sum_le_card (Fb ell k S b' ∪ Fb ell k S b)
      (fun p => RMap (U (b.1, μ)) ((srcL hell γ p (v p)) b') - (srcL hell γ p (v p)) b)
      (fun p hp => by
        rw [Finset.mem_union, not_or] at hp
        have h1 : (srcL hell γ p (v p)) b' = 0 := by
          by_contra hne; exact hp.1 (mem_Fb hell hS γ p (v p) b' hne)
        have h2 : (srcL hell γ p (v p)) b = 0 := by
          by_contra hne; exact hp.2 (mem_Fb hell hS γ p (v p) b hne)
        simp only [h1, h2, map_zero, sub_zero])
    have hc : ((Fb ell k S b' ∪ Fb ell k S b).card : ℝ) ≤ 4374 := by
      have h1 := Finset.card_union_le (Fb ell k S b') (Fb ell k S b)
      have h2 := card_Fb (S := S) hell b'
      have h3 := card_Fb (S := S) hell b
      have : (Fb ell k S b' ∪ Fb ell k S b).card ≤ 4374 := by omega
      exact_mod_cast this
    exact h.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  unfold gradWU
  calc ∑ b : Bond (scaleUp ell k Lu),
        ‖RMap (U (b.1, μ)) ((EU hell γ v) (periodicLatticeShift b.1 μ, b.2)) - (EU hell γ v) b‖ ^ 2
      ≤ ∑ b : Bond (scaleUp ell k Lu), 4374 * ∑ p, ‖RMap (U (b.1, μ))
          ((srcL hell γ p (v p)) (periodicLatticeShift b.1 μ, b.2)) - (srcL hell γ p (v p)) b‖ ^ 2 :=
        Finset.sum_le_sum (fun b _ => hpt b)
    _ = 4374 * ∑ p, gradWU U (srcL hell γ p (v p)) μ := by
        rw [← Finset.mul_sum, Finset.sum_comm]; rfl
    _ ≤ 4374 * ∑ p, Cg1 τ * (wD p * ‖v p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => grad_src hell hell2 hS U γ hτ hfine p (v p) μ))
          (by norm_num)
    _ = 4374 * Cg1 τ * nD v := by rw [← Finset.mul_sum]; unfold nD; ring

end src

end AdalyFormal.M2RightInv

#print axioms AdalyFormal.M2RightInv.sum_shift_bond
#print axioms AdalyFormal.M2RightInv.gradWU_gauge
#print axioms AdalyFormal.M2RightInv.gradWU_le_chart
#print axioms AdalyFormal.M2RightInv.gradWU_crude
#print axioms AdalyFormal.M2RightInv.srcL_apply
#print axioms AdalyFormal.M2RightInv.phi_near
#print axioms AdalyFormal.M2RightInv.FineOK
#print axioms AdalyFormal.M2RightInv.Cg1
#print axioms AdalyFormal.M2RightInv.Cg1_nonneg
#print axioms AdalyFormal.M2RightInv.grad_src
#print axioms AdalyFormal.M2RightInv.wnorm_src
#print axioms AdalyFormal.M2RightInv.Fb
#print axioms AdalyFormal.M2RightInv.card_Fb
#print axioms AdalyFormal.M2RightInv.mem_Fb
#print axioms AdalyFormal.M2RightInv.EU_pt
#print axioms AdalyFormal.M2RightInv.EU_wnorm
#print axioms AdalyFormal.M2RightInv.EU_grad

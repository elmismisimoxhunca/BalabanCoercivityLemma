import DY2
import DH1

/-!
# DY3 -- the bilinear form of `Δ⁽²⁾` and its Combes–Thomas conjugate on the M1 regime (M1 D-layer lane, clause 2, 2026-10-14)

`P = gparams ℓ k Lu hell S V a Λ`, `ψ = psiD P = H* J`, `W` the gauge-fixing map, `β = polar`.
* `C2row_level0` : the rows of level `0` of `C2fullOf` vanish; `polar_level0` likewise;
* **`delta2_bil`** : `⟪A, Δ⁽²⁾ B⟫ = 2 Σ_p ⟪β(W ιA, W ιB)(p), ψ(p)⟫`;
* `wnorm_le_N` : `wnormSq B ≤ ℓ² ‖e^{−σ} B‖²` (the reverse of lane E's `N_le_wnorm`);
* `wq_ballRes_wt` : on a read ball where `φ − c ≤ Ω`, `‖wq(ballRes (e^{−c} e^{φ} u))‖ ≤ e^{Ω} ‖wq(ballRes u)‖`;
* **`delta2_conj`** : if the conjugated `W` is bounded (`‖e^{−σ} W^{∓ξ} z‖ ≤ kW ‖e^{−σ} z‖`), the oscillation of `ξ` on every
  read ball of level `≥ 1` is `≤ Ω`, `‖ψ(p)‖ ≤ Sψ` and `Σ_p ‖C2 z p‖ ≤ K2 ‖wq z‖²`, then
  `|⟪e^{ξ} A, Δ⁽²⁾ e^{−ξ} B⟫| ≤ 2·Sψ·K2·e^{2Ω}·44217·(ℓ kW)² ‖wq ιA‖ ‖wq ιB‖`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.M1IMS
open AdalyFormal.M1Site
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.StatementLane (Tower Admissible scaleUp pdist)
open AdalyFormal.StatementLaneG (gparams)
open AdalyFormal.StatementLaneR8 (Ball rhoT)
open AdalyFormal.DLayer (polar polar_eq polar_scale psiD delta2_pair bondWt bondWt_apply bondWt_neg_cancel
  bondWt_cancel_neg)
open AdalyFormal.M1 (bstrat strat wnormSq)

/-! ## 1. level-0 rows -/

theorem C2row_level0 {L : PeriodicLatticeExtent} (G : TowerGeom L) (V : Cfg L) (z : BondFnL2 L) (p : BIdx G)
    (hp : (p.1 : ℕ) = 0) : C2fullOf G V z p = 0 := by
  have h0 : ∀ m : ℕ, m = 0 → ∀ (bg : ℕ → Cfg L) (a : XS L), C2CompL G.ell bg m a = 0 := by
    rintro m rfl bg a; exact C2CompL_zero G.ell bg a
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (C2rawB G V p.1 z)) p.2.1 = 0
  rw [C2rawB_eq]
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (⟨toM2 (C2CompL G.ell (bgTower G V) p.1 (suCoord z) p.2.1), toM2_mem _⟩ : SuTwo)
    = 0
  rw [h0 _ hp, Pi.zero_apply]
  apply Subtype.ext
  simp [map_zero]

theorem polar_level0 {L : PeriodicLatticeExtent} (G : TowerGeom L) (V : Cfg L) (u v : BondFnL2 L) (p : BIdx G)
    (hp : (p.1 : ℕ) = 0) : polar G V u v p = 0 := by
  unfold polar
  rw [PiLp.smul_apply, PiLp.sub_apply, C2row_level0 G V _ p hp, C2row_level0 G V _ p hp, sub_self, smul_zero]

/-! ## 2. the bilinear form of `Δ⁽²⁾` -/

theorem delta2_bil (P : IngrBParams) (A B : ↥(bondSupp P.G)) :
    ⟪A, P.data.Delta2 P.data_laws B⟫ = 2 * ∑ p, ⟪polar P.G P.U (Wop P.G P.U P.a (iE P.G A))
      (Wop P.G P.U P.a (iE P.G B)) p, psiD P p⟫ := by
  have hs := (P.data.Delta2_spec P.data_laws).1
  have h1 := delta2_pair P (A + B)
  have h2 := delta2_pair P (A - B)
  have hsym : ⟪B, P.data.Delta2 P.data_laws A⟫ = ⟪A, P.data.Delta2 P.data_laws B⟫ := by
    rw [real_inner_comm, hs]
  have hpol : ⟪A, P.data.Delta2 P.data_laws B⟫
      = (⟪A + B, P.data.Delta2 P.data_laws (A + B)⟫ - ⟪A - B, P.data.Delta2 P.data_laws (A - B)⟫) / 4 := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [hsym]; ring
  rw [hpol, h1, h2]
  have hC : ∀ X : ↥(bondSupp P.G), P.data.C2 X = C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G X)) := fun X => rfl
  simp only [hC, map_add, map_sub]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have e : ∀ p, ⟪(C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A) + Wop P.G P.U P.a (iE P.G B))) p, psiD P p⟫
      - ⟪(C2fullOf P.G P.U (Wop P.G P.U P.a (iE P.G A) - Wop P.G P.U P.a (iE P.G B))) p, psiD P p⟫
      = 4 * ⟪polar P.G P.U (Wop P.G P.U P.a (iE P.G A)) (Wop P.G P.U P.a (iE P.G B)) p, psiD P p⟫ := by
    intro p
    unfold polar
    rw [PiLp.smul_apply, PiLp.sub_apply, inner_smul_left, inner_sub_left]
    simp only [RCLike.conj_to_real]
    ring
  rw [Finset.sum_congr rfl (fun p _ => e p), ← Finset.mul_sum]
  ring

/-! ## 3. norms -/

section norms
variable {ell M R k : ℕ} {Lf : PeriodicLatticeExtent} {S : Tower Lf}

theorem wnorm_le_Nw (hS : Admissible ell M R k S) (hR : 1 ≤ R) (hM : 1 ≤ M) (hell : 1 ≤ ell) (B : BondFnL2 Lf) :
    wnormSq S ell k B ≤ (ell : ℝ) ^ 2 * ‖bondWt (-sigG (geomOf ell k S)) B‖ ^ 2 := by
  have hell0 : 0 < ell := by omega
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  unfold wnormSq
  refine Finset.sum_le_sum (fun b _ => ?_)
  rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  show (((ell : ℝ) ^ bstrat S k b)⁻¹) ^ 2 ≤ (ell : ℝ) ^ 2 * Real.exp (-(sigG (geomOf ell k S) b.1)) ^ 2
  rw [Real.exp_neg, exp_sig (geomOf ell k S) hell0, ← strat_eq_stratG hell0 hS]
  have hb := AdalyFormal.M1.bstrat_ge hS hR hM hell b
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : ∀ n : ℕ, (0 : ℝ) < (ell : ℝ) ^ n := fun n => by positivity
  have h3 : (ell : ℝ) ^ strat S k b.1 ≤ (ell : ℝ) ^ (bstrat S k b + 1) := pow_le_pow_right₀ h1 hb
  have h4 : ((ell : ℝ) ^ bstrat S k b)⁻¹ ≤ (ell : ℝ) * ((ell : ℝ) ^ strat S k b.1)⁻¹ := by
    rw [pow_succ] at h3
    have hl0 : (0 : ℝ) < ell := by linarith
    rw [inv_le_comm₀ (hp _) (by have := hp (strat S k b.1); positivity), mul_inv, inv_inv]
    calc (ell : ℝ)⁻¹ * (ell : ℝ) ^ strat S k b.1 ≤ (ell : ℝ)⁻¹ * ((ell : ℝ) ^ bstrat S k b * ell) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (ell : ℝ) ^ bstrat S k b := by field_simp
  have := pow_le_pow_left₀ (by positivity) h4 2
  rw [mul_pow] at this
  exact this

end norms

theorem le_of_sq_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by nlinarith

/-- the weighted restriction of a re-weighted field -/
theorem wq_ballRes_wt {L : PeriodicLatticeExtent} (S : Tower L) (ell k : ℕ) (G : TowerGeom L) (p : BIdx G)
    (u : BondFnL2 L) (φ : PeriodicLatticeSite L → ℝ) (c Ω : ℝ)
    (h : ∀ e : Bond L, e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) → φ e.1 - c ≤ Ω) :
    ‖wq S ell k (ballRes G p (Real.exp (-c) • bondWt φ u))‖ ≤ Real.exp Ω * ‖wq S ell k (ballRes G p u)‖ := by
  classical
  have hsq : ‖wq S ell k (ballRes G p (Real.exp (-c) • bondWt φ u))‖ ^ 2
      ≤ (Real.exp Ω * ‖wq S ell k (ballRes G p u)‖) ^ 2 := by
    rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    refine Finset.sum_le_sum (fun e _ => ?_)
    rw [wq_apply, wq_apply]
    show ‖(((ell : ℝ) ^ bstrat S k e)⁻¹) • (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1)
        then (Real.exp (-c) • bondWt φ u) e else 0)‖ ^ 2
      ≤ Real.exp Ω ^ 2 * ‖(((ell : ℝ) ^ bstrat S k e)⁻¹) • (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then u e else 0)‖ ^ 2
    split_ifs with he
    · rw [PiLp.smul_apply, bondWt_apply, smul_smul, smul_smul, norm_smul, norm_smul, mul_pow, mul_pow,
        Real.norm_of_nonneg (show (0 : ℝ) ≤ ((ell : ℝ) ^ bstrat S k e)⁻¹ * Real.exp (-c) * Real.exp (φ e.1) by positivity),
        Real.norm_of_nonneg (show (0 : ℝ) ≤ ((ell : ℝ) ^ bstrat S k e)⁻¹ by positivity)]
      have hx : Real.exp (-c) * Real.exp (φ e.1) ≤ Real.exp Ω := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [h e he])
      have hx0 : 0 ≤ Real.exp (-c) * Real.exp (φ e.1) := by positivity
      have h2 := pow_le_pow_left₀ hx0 hx 2
      have hw : (0 : ℝ) ≤ (((ell : ℝ) ^ bstrat S k e)⁻¹) ^ 2 * ‖u e‖ ^ 2 := by positivity
      calc (((ell : ℝ) ^ bstrat S k e)⁻¹ * Real.exp (-c) * Real.exp (φ e.1)) ^ 2 * ‖u e‖ ^ 2
          = (Real.exp (-c) * Real.exp (φ e.1)) ^ 2 * ((((ell : ℝ) ^ bstrat S k e)⁻¹) ^ 2 * ‖u e‖ ^ 2) := by ring
        _ ≤ Real.exp Ω ^ 2 * ((((ell : ℝ) ^ bstrat S k e)⁻¹) ^ 2 * ‖u e‖ ^ 2) := mul_le_mul_of_nonneg_right h2 hw
        _ = _ := by ring
    · simp
  have h0 : 0 ≤ Real.exp Ω * ‖wq S ell k (ballRes G p u)‖ := by positivity
  exact le_of_sq_le' (norm_nonneg _) h0 hsq

/-! ## 4. the conjugated form -/

section conj
variable {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
  (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell) (hroom : 18 * ell ≤ R * M)
include hA hell2 hroom

/-- **the conjugated `Δ⁽²⁾`** -/
theorem delta2_conj (hell0 : 0 < ell) (V : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (ξ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (kW : ℝ) (hkW : 0 ≤ kW)
    (hWp : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt (-ξ) (Wop (geomOf ell k S) V a (bondWt ξ z)))‖
      ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖)
    (hWm : ∀ z, ‖bondWt (-sigG (geomOf ell k S)) (bondWt ξ (Wop (geomOf ell k S) V a (bondWt (-ξ) z)))‖
      ≤ kW * ‖bondWt (-sigG (geomOf ell k S)) z‖)
    (Ω : ℝ) (hΩ : 0 ≤ Ω)
    (hosc : ∀ p : BIdx (geomOf ell k S), 1 ≤ (p.1 : ℕ) → ∀ e : Bond (scaleUp ell k Lu),
      e.1 ∈ Ball p.2.1.1 (rhoT ell p.1) → |ξ e.1 - ξ p.2.1.1| ≤ Ω)
    (Sψ : ℝ) (hSψ : 0 ≤ Sψ) (hψ : ∀ p, ‖psiD (gparams ell k Lu hell0 S V a Lam) p‖ ≤ Sψ)
    (K2 : ℝ) (hK2 : 0 ≤ K2)
    (hC : ∀ z, ∑ q, ‖C2fullOf (geomOf ell k S) V z q‖ ≤ K2 * ‖wq S ell k z‖ ^ 2)
    (hR : 1 ≤ R) (hM : 1 ≤ M)
    (A B : ↥(bondSupp (geomOf ell k S))) :
    |⟪eW (geomOf ell k S) ξ A, (gparams ell k Lu hell0 S V a Lam).data.Delta2 (gparams ell k Lu hell0 S V a Lam).data_laws
        (eW (geomOf ell k S) (-ξ) B)⟫|
      ≤ 2 * Sψ * K2 * Real.exp (2 * Ω) * 44217 * ((ell : ℝ) * kW) ^ 2
        * ‖wq S ell k (iE (geomOf ell k S) A)‖ * ‖wq S ell k (iE (geomOf ell k S) B)‖ := by
  classical
  have hl1 : 1 ≤ ell := by omega
  -- the two conjugated inputs
  set u : BondFnL2 (scaleUp ell k Lu) := bondWt (-ξ) (Wop (geomOf ell k S) V a (bondWt ξ (iE (geomOf ell k S) A))) with hu
  set v : BondFnL2 (scaleUp ell k Lu) := bondWt ξ (Wop (geomOf ell k S) V a (bondWt (-ξ) (iE (geomOf ell k S) B))) with hv
  have eu : Wop (geomOf ell k S) V a (iE (geomOf ell k S) (eW (geomOf ell k S) ξ A)) = bondWt ξ u := by
    rw [iE_eW, hu, bondWt_neg_cancel]
  have ev : Wop (geomOf ell k S) V a (iE (geomOf ell k S) (eW (geomOf ell k S) (-ξ) B)) = bondWt (-ξ) v := by
    rw [iE_eW, hv, bondWt_cancel_neg]
  rw [delta2_bil (gparams ell k Lu hell0 S V a Lam)]
  show |2 * ∑ p : BIdx (geomOf ell k S), ⟪polar (geomOf ell k S) V (Wop (geomOf ell k S) V a (iE (geomOf ell k S) (eW (geomOf ell k S) ξ A)))
      (Wop (geomOf ell k S) V a (iE (geomOf ell k S) (eW (geomOf ell k S) (-ξ) B))) p, psiD (gparams ell k Lu hell0 S V a Lam) p⟫| ≤ _
  rw [eu, ev]
  -- row-wise
  set ap : BIdx (geomOf ell k S) → ℝ := fun p => if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes (geomOf ell k S) p u)‖ else 0 with hap
  set bp : BIdx (geomOf ell k S) → ℝ := fun p => if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes (geomOf ell k S) p v)‖ else 0 with hbp
  have hrow : ∀ p : BIdx (geomOf ell k S), |⟪polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p, psiD (gparams ell k Lu hell0 S V a Lam) p⟫|
      ≤ Sψ * (K2 * Real.exp (2 * Ω)) * (ap p * bp p) := by
    intro p
    refine (abs_real_inner_le_norm _ _).trans ?_
    by_cases hp1 : 1 ≤ (p.1 : ℕ)
    · set c := ξ p.2.1.1 with hc
      have hscale : polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p
          = polar (geomOf ell k S) V (Real.exp (-c) • bondWt ξ u) (Real.exp (-(-c)) • bondWt (-ξ) v) p := by
        have h := polar_scale (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) (Real.exp (-c)) (Real.exp_pos _).ne'
        rw [← Real.exp_neg] at h
        exact (congrFun (congrArg (fun f => WithLp.ofLp f) h) p).symm
      have hpr := polar_row_ball (geomOf ell k S) (by show 0 < ell; omega) V (wq S ell k) K2 hK2 hC p
        (Real.exp (-c) • bondWt ξ u) (Real.exp (-(-c)) • bondWt (-ξ) v)
      have h1 := wq_ballRes_wt S ell k (geomOf ell k S) p u ξ c Ω (fun e he => by
        have := hosc p hp1 e he; rw [abs_le] at this; linarith)
      have h2 := wq_ballRes_wt S ell k (geomOf ell k S) p v (-ξ) (-c) Ω (fun e he => by
        have := hosc p hp1 e he; rw [abs_le] at this; simp only [Pi.neg_apply]; linarith)
      have hn : ‖polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p‖
          ≤ K2 * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p u)‖) * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p v)‖) := by
        rw [hscale]
        refine hpr.trans ?_
        have h0 : 0 ≤ K2 * ‖wq S ell k (ballRes (geomOf ell k S) p (Real.exp (-c) • bondWt ξ u))‖ := by positivity
        calc K2 * ‖wq S ell k (ballRes (geomOf ell k S) p (Real.exp (-c) • bondWt ξ u))‖
              * ‖wq S ell k (ballRes (geomOf ell k S) p (Real.exp (-(-c)) • bondWt (-ξ) v))‖
            ≤ K2 * ‖wq S ell k (ballRes (geomOf ell k S) p (Real.exp (-c) • bondWt ξ u))‖
              * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p v)‖) := mul_le_mul_of_nonneg_left h2 h0
          _ ≤ K2 * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p u)‖) * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p v)‖) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h1 hK2
      have hap1 : ap p = ‖wq S ell k (ballRes (geomOf ell k S) p u)‖ := by simp only [hap, if_pos hp1]
      have hbp1 : bp p = ‖wq S ell k (ballRes (geomOf ell k S) p v)‖ := by simp only [hbp, if_pos hp1]
      rw [hap1, hbp1]
      have e2 : Real.exp (2 * Ω) = Real.exp Ω * Real.exp Ω := by rw [← Real.exp_add]; ring_nf
      calc ‖polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p‖ * ‖psiD (gparams ell k Lu hell0 S V a Lam) p‖
          ≤ (K2 * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p u)‖) * (Real.exp Ω * ‖wq S ell k (ballRes (geomOf ell k S) p v)‖)) * Sψ :=
            mul_le_mul hn (hψ p) (norm_nonneg _) (by positivity)
        _ = Sψ * (K2 * Real.exp (2 * Ω)) * (‖wq S ell k (ballRes (geomOf ell k S) p u)‖ * ‖wq S ell k (ballRes (geomOf ell k S) p v)‖) := by
            rw [e2]; ring
    · have h0 : (p.1 : ℕ) = 0 := by omega
      rw [show polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p = 0 from polar_level0 (geomOf ell k S) V _ _ p h0, norm_zero, zero_mul]
      have hap0 : ap p = 0 := by simp only [hap, if_neg hp1]
      rw [hap0, zero_mul, mul_zero]
  -- Cauchy–Schwarz and the multiplicity
  have hsa : ∑ p, ap p ^ 2 ≤ 44217 * ‖wq S ell k u‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (ball_mult hA hell2 hroom u)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [hap]; split_ifs <;> simp
  have hsb : ∑ p, bp p ^ 2 ≤ 44217 * ‖wq S ell k v‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) (ball_mult hA hell2 hroom v)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [hbp]; split_ifs <;> simp
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ ap bp
  have hsqa : Real.sqrt (∑ p, ap p ^ 2) ≤ Real.sqrt 44217 * ‖wq S ell k u‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (wq S ell k u)), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hsa
  have hsqb : Real.sqrt (∑ p, bp p ^ 2) ≤ Real.sqrt 44217 * ‖wq S ell k v‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (wq S ell k v)), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hsb
  have hab : ∑ p, ap p * bp p ≤ 44217 * ‖wq S ell k u‖ * ‖wq S ell k v‖ := by
    refine hCS.trans ?_
    have h44 : Real.sqrt 44217 * Real.sqrt 44217 = 44217 := Real.mul_self_sqrt (by norm_num)
    calc Real.sqrt (∑ p, ap p ^ 2) * Real.sqrt (∑ p, bp p ^ 2)
        ≤ (Real.sqrt 44217 * ‖wq S ell k u‖) * (Real.sqrt 44217 * ‖wq S ell k v‖) :=
          mul_le_mul hsqa hsqb (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt 44217 * Real.sqrt 44217) * (‖wq S ell k u‖ * ‖wq S ell k v‖) := by ring
      _ = 44217 * ‖wq S ell k u‖ * ‖wq S ell k v‖ := by rw [h44]; ring
  -- the conjugated `W`
  have hNu : ‖wq S ell k u‖ ≤ ell * kW * ‖wq S ell k (iE (geomOf ell k S) A)‖ := by
    have h1 : ‖wq S ell k u‖ ^ 2 ≤ ((ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) u‖) ^ 2 := by
      rw [wq_normSq, mul_pow]; exact wnorm_le_Nw hA hR hM hl1 u
    have h1' : ‖wq S ell k u‖ ≤ (ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) u‖ :=
      le_of_sq_le' (norm_nonneg _) (by positivity) h1
    have h2 : ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) A)‖ ≤ ‖wq S ell k (iE (geomOf ell k S) A)‖ := by
      have h := N_le_wnorm hA hell0 (iE (geomOf ell k S) A)
      rw [← wq_normSq] at h
      exact le_of_sq_le' (norm_nonneg _) (norm_nonneg _) h
    have h3 := hWp (iE (geomOf ell k S) A)
    calc ‖wq S ell k u‖ ≤ (ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) u‖ := h1'
      _ ≤ (ell : ℝ) * (kW * ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) A)‖) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (ell : ℝ) * (kW * ‖wq S ell k (iE (geomOf ell k S) A)‖) := by gcongr
      _ = ell * kW * ‖wq S ell k (iE (geomOf ell k S) A)‖ := by ring
  have hNv : ‖wq S ell k v‖ ≤ ell * kW * ‖wq S ell k (iE (geomOf ell k S) B)‖ := by
    have h1 : ‖wq S ell k v‖ ^ 2 ≤ ((ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) v‖) ^ 2 := by
      rw [wq_normSq, mul_pow]; exact wnorm_le_Nw hA hR hM hl1 v
    have h1' : ‖wq S ell k v‖ ≤ (ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) v‖ :=
      le_of_sq_le' (norm_nonneg _) (by positivity) h1
    have h2 : ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) B)‖ ≤ ‖wq S ell k (iE (geomOf ell k S) B)‖ := by
      have h := N_le_wnorm hA hell0 (iE (geomOf ell k S) B)
      rw [← wq_normSq] at h
      exact le_of_sq_le' (norm_nonneg _) (norm_nonneg _) h
    have h3 := hWm (iE (geomOf ell k S) B)
    calc ‖wq S ell k v‖ ≤ (ell : ℝ) * ‖bondWt (-sigG (geomOf ell k S)) v‖ := h1'
      _ ≤ (ell : ℝ) * (kW * ‖bondWt (-sigG (geomOf ell k S)) (iE (geomOf ell k S) B)‖) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (ell : ℝ) * (kW * ‖wq S ell k (iE (geomOf ell k S) B)‖) := by gcongr
      _ = ell * kW * ‖wq S ell k (iE (geomOf ell k S) B)‖ := by ring
  -- assemble
  have hsum : |2 * ∑ p, ⟪polar (geomOf ell k S) V (bondWt ξ u) (bondWt (-ξ) v) p, psiD (gparams ell k Lu hell0 S V a Lam) p⟫|
      ≤ 2 * (Sψ * (K2 * Real.exp (2 * Ω)) * ∑ p, ap p * bp p) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => hrow p)
  refine hsum.trans ?_
  have hc0 : 0 ≤ Sψ * (K2 * Real.exp (2 * Ω)) := by positivity
  have hu0 := norm_nonneg (wq S ell k u)
  have hv0 := norm_nonneg (wq S ell k v)
  have hm : ‖wq S ell k u‖ * ‖wq S ell k v‖
      ≤ (ell * kW * ‖wq S ell k (iE (geomOf ell k S) A)‖) * (ell * kW * ‖wq S ell k (iE (geomOf ell k S) B)‖) :=
    mul_le_mul hNu hNv hv0 (by positivity)
  calc 2 * (Sψ * (K2 * Real.exp (2 * Ω)) * ∑ p, ap p * bp p)
      ≤ 2 * (Sψ * (K2 * Real.exp (2 * Ω)) * (44217 * ‖wq S ell k u‖ * ‖wq S ell k v‖)) := by gcongr
    _ = 2 * Sψ * K2 * Real.exp (2 * Ω) * 44217 * (‖wq S ell k u‖ * ‖wq S ell k v‖) := by ring
    _ ≤ 2 * Sψ * K2 * Real.exp (2 * Ω) * 44217
          * ((ell * kW * ‖wq S ell k (iE (geomOf ell k S) A)‖) * (ell * kW * ‖wq S ell k (iE (geomOf ell k S) B)‖)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end conj

#print axioms C2row_level0
#print axioms polar_level0
#print axioms delta2_bil
#print axioms wnorm_le_Nw
#print axioms wq_ballRes_wt
#print axioms delta2_conj

end AdalyFormal.M1DStrat

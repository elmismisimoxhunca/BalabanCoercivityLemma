import OL1

/-!
# OL2 -- `hC2` at the printed class, from `BallChartsAt` (lane m2_oplayer_20261015)

* `level_bounds12`, `C2full_strat12` : DQ4 `level_bounds` / DQ5 `C2full_strat` (text copies) with `M1Bounds12` / `M1Regular12`
  (the clause-3 field is not read by either proof).
* `C2row_congr_U` : the row `p` of `C2fullOf G V` reads `V` only on `Ball(p.2.1.1, 2 ρ_T(p.1))` (r8 `C2CompL_congr_U`).
* **`hC2_class`** : at a configuration with `BallChartsAt` (constant `C`, `α₀`), every `z`:
  `Σ_p ‖C2fullOf G U z p‖ ≤ 44217 · K2strat ℓ (12 M α_V) · wnormSq z`,  `α_V = ℓ³ (2 (ℓ³ (C α₀)))`.
  Per row `p` of level `≥ 1`: one anchor chart (`rowChart2_ball`), the gauge step (`gauge_C2full_norm`), the read-ball
  restriction (`C2row_congr`), the global bound at the anchor's `M1Regular12` configuration (`C2full_strat12`); then
  `ball_mult` (multiplicity `44217`).  Level-0 rows vanish (`C2row_level0`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M2OpLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (pdist bigSide Admissible Tower scaleUp)
open AdalyFormal.StatementLaneR8 (Ball pdist_comm pdist_triangle pdist_shift_le pdist_self rhoT AgreeAt AgreeX
  C2CompL_congr_U C2CompL_congr_in)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobNorm_nonneg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2 (bondsLam geomOf C2fullOf C2rawB_eq C2CompL C2CompL_zero bgTower Cfg XS suCoord
  suCoordInv fromM2 BIdx)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (nrm nrm_one_suCoord sum_le_of_injective)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.DLayer (K2free fN_rsmul)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M1 (strat bstrat wnormSq)
open AdalyFormal.M1DStrat (wq wq_apply wq_normSq ballRes ballRes_apply_in C2row_congr C2row_level0 wq_ballRes_sq ball_mult)
open AdalyFormal.M1DStrat.DQ
open EstimatesLayer.E1E3 (e2Majorant)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

section level
variable {L : PeriodicLatticeExtent}
variable {ell M R k : ℕ} {S : Tower L}

theorem level_bounds12 (hA : Admissible ell M R k S) (hell : 2 ≤ ell) (hroom : 18 * ell ≤ R * M) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) (η : ℝ) (hη : 0 < η) (α₀ : ℝ) (A : Bond L → Mt)
    (hB : AdalyFormal.OneGap12.M1Bounds12 S ell M 12 k α₀ η A) (hHT : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0)
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

section c2
/-- DQ5 `C2full_strat` (text copy) at `M1Regular12` (clause 3 is not used) -/
theorem C2full_strat12 (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell)
    (hroom : 18 * ell ≤ R * M) (hLu : ∀ μ, ell < Lu μ + 1) (hα₀ : 0 ≤ α₀)
    (hU : AdalyFormal.OneGap12.M1Regular12 ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : DQSmall ell (12 * M * α₀))
    (z : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, ‖C2fullOf (geomOf ell k S) U z p‖ ≤ K2strat ell (12 * M * α₀) * wnormSq S ell k z := by
  classical
  have hell : 0 < ell := by omega
  obtain ⟨g, A, hrep, hB⟩ := hU
  have hHT : ∀ e, (A e)ᴴ = A e ∧ Matrix.trace (A e) = 0 := fun e => hB.1 e
  have hη0 : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hβ0 : 0 ≤ 12 * (M : ℝ) * α₀ := by positivity
  -- gauge
  rw [Finset.sum_congr rfl (fun p _ => gauge_C2full_norm (geomOf ell k S) U g z p), ← gauge_wnorm S ell k g z]
  set V : Cfg (scaleUp ell k Lu) := periodicGaugeTransform g U with hV
  set x : BondFnL2 (scaleUp ell k Lu) := AdalyFormal.GaugeCov.adBL g z with hx
  set Vc : ℕ → Cfg (scaleUp ell k Lu) := fun n => levelCfg S ell n ((ell : ℝ) ^ k)⁻¹ A hHT with hVc
  set xs : ℕ → BondFnL2 (scaleUp ell k Lu) := fun n => maskN S k n x with hxs
  set α : ℝ := alphaQ ell (12 * M * α₀) with hα
  have hα0 : 0 ≤ α := alphaQ_nonneg ell hβ0
  set K : ℝ := K2free ell ((1 + 3 * Real.pi) * α) with hK
  have hK0 : 0 ≤ K := K2free_nonneg ell _ (thetaK2_lt_of ell _ hsm.hK2c)
  -- the injection rows → (level, aligned bond)
  let φ : BIdx (geomOf ell k S) → (Σ n : Fin (k + 1), CoarseBond (scaleUp ell k Lu) (ell ^ (n : ℕ))) := fun p =>
    ⟨p.1, (⟨p.2.1.1, row_base_aligned ell k Lu hell S (Nat.lt_succ_iff.mp p.1.isLt) p.2.2⟩, p.2.1.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨j, ⟨b, hb⟩⟩ ⟨j', ⟨b', hb'⟩⟩ h
    simp only [φ, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    have h3 := eq_of_heq h2
    have hbb : b = b' := Prod.ext (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)) => c.1.1) h3)
      (congrArg (fun c : CoarseBond (scaleUp ell k Lu) (ell ^ (j : ℕ)) => c.2) h3)
    subst hbb
    rfl
  -- per row
  have hrow : ∀ p : BIdx (geomOf ell k S), ‖C2fullOf (geomOf ell k S) V x p‖ ≤ rowF ell k Vc xs (φ p) := by
    rintro ⟨j, ⟨b, hb⟩⟩
    rw [C2full_norm]
    show ((ell : ℝ) ^ (j : ℕ))⁻¹ * ‖suOf (C2CompL ell (bgTower (geomOf ell k S) V) (j : ℕ) (suCoord x) b)‖
      ≤ ((ell : ℝ) ^ (j : ℕ))⁻¹ *
        ‖suOf (C2CompL ell (bgTower (geomOf ell k S) (Vc (j : ℕ))) (j : ℕ) (suCoord (xs (j : ℕ))) (b.1, b.2))‖
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj1
    · rw [hj0, C2CompL_zero, Pi.zero_apply, suOf_zero, norm_zero, mul_zero]
      positivity
    · set n : ℕ := (j : ℕ) with hn
      have hnk : n ≤ k := Nat.lt_succ_iff.mp j.isLt
      obtain ⟨y, hy, hy', hby, -⟩ := row_anchor ell k S hb
      have hw0 : (0 : ℝ) < (ell : ℝ) ^ (n - 1) := by positivity
      -- the configurations agree on the ball read by the row
      have hagree : AgreeAt (Ball b.1 (2 * rhoT (geomOf ell k S).ell n)) V (Vc n) := by
        intro z' hz' μ
        have hz'' : pdist b.1 z' ≤ 2 * rhoT ell n := hz'
        have hd : pdist z' y ≤ rN ell n := by
          have := pdist_triangle z' b.1 y
          rw [pdist_comm z' b.1] at this
          unfold rN; omega
        have hχ := chiN_eq_one S n ((rN ell n : ℕ) : ℝ) _ hw0 hy (by exact_mod_cast hd) (x := z')
        apply Subtype.ext
        show ((V (z', μ) : SU2) : Mt) = NormedSpace.exp (cutH ((ell : ℝ) ^ k)⁻¹
          (chiN S n ((rN ell n : ℕ) : ℝ) ((ell : ℝ) ^ (n - 1))) A (z', μ))
        rw [hrep (z', μ), cutH_of_one _ _ A (z', μ) hχ]
      -- the input agrees with its level mask on the bonds read by the row
      have hmask : AgreeX (Ball b.1 (rhoT ell n)) (suCoord x) (suCoord (xs n)) := by
        intro e he
        have he' : pdist b.1 e.1 ≤ rhoT ell n := he
        have hR1 := room_prev hell2 hroom hj1 (n := n)
        have hR2 := room_next hell2 hroom n
        have hey : pdist e.1 y ≤ rhoT ell n + ell ^ n := by
          have := pdist_triangle e.1 b.1 y
          rw [pdist_comm e.1 b.1] at this
          omega
        have hP : n ≤ bstrat S k e + 1 ∧ bstrat S k e ≤ n + 1 := by
          constructor
          · have h1 : pdist e.1 y ≤ R * M * ell ^ (n - 1) := by omega
            have h2 : pdist (periodicLatticeShift e.1 e.2) y ≤ R * M * ell ^ (n - 1) := by
              have := pdist_triangle (periodicLatticeShift e.1 e.2) e.1 y
              have h3 := pdist_shift_le e.1 e.2
              rw [pdist_comm] at h3
              omega
            have := bstrat_ge_prev hA hj1 hnk hy e h1 h2
            omega
          · have hye : pdist y e.1 ≤ R * (M * ell ^ (n + 1)) := by
              rw [pdist_comm]; omega
            have := strat_le_of_near hA hnk hy hy' hye
            have hb' : bstrat S k e ≤ strat S k e.1 := by unfold bstrat; exact min_le_left _ _
            omega
        show fromM2 (((WithLp.ofLp x) e : SuTwo) : M2) = fromM2 (((WithLp.ofLp (maskN S k n x)) e : SuTwo) : M2)
        simp only [maskN, WithLp.ofLp_toLp, if_pos hP]
      have e1 : C2CompL ell (bgTower (geomOf ell k S) V) n (suCoord x) b
          = C2CompL ell (bgTower (geomOf ell k S) (Vc n)) n (suCoord x) b :=
        C2CompL_congr_U (geomOf ell k S) hell (suCoord x) n b hagree
      have e2 : C2CompL ell (bgTower (geomOf ell k S) (Vc n)) n (suCoord x) b
          = C2CompL ell (bgTower (geomOf ell k S) (Vc n)) n (suCoord (xs n)) b :=
        C2CompL_congr_in ell hell (bgTower (geomOf ell k S) (Vc n)) n b hmask
      rw [e1, e2]
  -- per level
  have hlev : ∀ n : Fin (k + 1), ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (n : ℕ)), rowF ell k Vc xs ⟨n, c⟩
      ≤ K * (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖xs n‖ ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos (n : ℕ) with hn0 | hn1
    · rw [Finset.sum_eq_zero (fun c _ => rowF_zero ell k Vc xs n hn0 c)]
      exact mul_nonneg (mul_nonneg hK0 (by positivity)) (by positivity)
    · have hnk : (n : ℕ) ≤ k := Nat.lt_succ_iff.mp n.isLt
      obtain ⟨hlinks, hplaq⟩ := level_bounds12 hA hell2 hroom hn1 hnk ((ell : ℝ) ^ k)⁻¹ hη0 α₀ A hB hHT hβ0 hsm.h4
      have hmain := C2Comp_depth_any ell (n : ℕ) (scaleUp ell (k - n) Lu) (scaleUp ell k Lu)
        (scaleUp_split ell k n Lu hell hnk) hell2 (Vc n) α hα0 hlinks hplaq
        (fun ρ => torus_big ell k n Lu hell2 hLu hnk ρ) hsm.hcb hsm.hKU hsm.h1000 hsm.hK2c (suCoord (xs n))
      rw [nrm_one_suCoord] at hmain
      have e1 : ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (n : ℕ)), rowF ell k Vc xs ⟨n, c⟩
          = ((ell : ℝ) ^ (n : ℕ))⁻¹ * ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (n : ℕ)),
            ‖suOf (C2CompL ell (AdalyFormal.Balaban.UbarTowerCov.UbarTower AdalyFormal.Balaban.SuTwoLogExp.su2LogExp ell
              (Vc n)) n (suCoord (xs n)) (c.1.1, c.2))‖ := by
        rw [Finset.mul_sum]; rfl
      rw [e1]
      have hpos : (0 : ℝ) ≤ ((ell : ℝ) ^ (n : ℕ))⁻¹ := by positivity
      refine (mul_le_mul_of_nonneg_left hmain hpos).trans (le_of_eq ?_)
      rw [hK, one_div, inv_pow]; ring
  calc ∑ p, ‖C2fullOf (geomOf ell k S) V x p‖ ≤ ∑ p, rowF ell k Vc xs (φ p) :=
        Finset.sum_le_sum (fun p _ => hrow p)
    _ ≤ ∑ q, rowF ell k Vc xs q := sum_le_of_injective φ hφ _ (rowF_nonneg ell k Vc xs)
    _ = ∑ n : Fin (k + 1), ∑ c : CoarseBond (scaleUp ell k Lu) (ell ^ (n : ℕ)), rowF ell k Vc xs ⟨n, c⟩ :=
        Fintype.sum_sigma _
    _ ≤ ∑ n : Fin (k + 1), K * (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖xs n‖ ^ 2 := Finset.sum_le_sum (fun n _ => hlev n)
    _ = K * ∑ n : Fin (k + 1), (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖maskN S k n x‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun n _ => ?_)
        show K * (((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖maskN S k n x‖ ^ 2
          = K * ((((ell : ℝ) ^ (n : ℕ))⁻¹) ^ 2 * ‖maskN S k n x‖ ^ 2)
        ring
    _ ≤ K * (3 * (ell : ℝ) ^ 2 * wnormSq S ell k x) :=
        mul_le_mul_of_nonneg_left (masks_le_wnorm S ell k (by omega) x) hK0
    _ = K2strat ell (12 * M * α₀) * wnormSq S ell k x := by unfold K2strat; rw [← hα, ← hK]; ring

end c2

/-- the row `p` reads the configuration only on `Ball(p.2.1.1, 2 ρ_T(p.1))` -/
theorem C2row_congr_U {L : PeriodicLatticeExtent} (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (hell : 0 < G.ell)
    (V V' : Cfg L) (p : BIdx G) (x : BondFnL2 L)
    (h : AgreeAt (Ball p.2.1.1 (2 * rhoT G.ell p.1)) V V') :
    C2fullOf G V x p = C2fullOf G V' x p := by
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (AdalyFormal.IngredientFamilyR2.C2rawB G V p.1 x)) p.2.1
    = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (WithLp.ofLp (AdalyFormal.IngredientFamilyR2.C2rawB G V' p.1 x)) p.2.1
  rw [C2rawB_eq, C2rawB_eq]
  have hc := C2CompL_congr_U G hell (suCoord x) p.1 p.2.1 h
  show (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (⟨AdalyFormal.IngredientFamilyR2.toM2
      (C2CompL G.ell (bgTower G V) p.1 (suCoord x) p.2.1), AdalyFormal.IngredientFamilyR2.toM2_mem _⟩ : SuTwo)
    = (((G.ell : ℝ) ^ (p.1 : ℕ))⁻¹) • (⟨AdalyFormal.IngredientFamilyR2.toM2
      (C2CompL G.ell (bgTower G V') p.1 (suCoord x) p.2.1), AdalyFormal.IngredientFamilyR2.toM2_mem _⟩ : SuTwo)
  simp only [hc]

/-- the gauge rotation does not change the weighted norm of a read-ball restriction -/
theorem wq_ballRes_gauge {ell k : ℕ} {L : PeriodicLatticeExtent} (S : Tower L)
    (G : AdalyFormal.IngredientFamilyR2.TowerGeom L) (_hG : G.ell = ell) (p : BIdx G)
    (g : PeriodicLatticeSite L → Matrix.specialUnitaryGroup (Fin 2) ℂ) (z : BondFnL2 L) :
    ‖wq S ell k (ballRes G p (AdalyFormal.GaugeCov.adBL g z))‖ = ‖wq S ell k (ballRes G p z)‖ := by
  classical
  have h2 : ‖wq S ell k (ballRes G p (AdalyFormal.GaugeCov.adBL g z))‖ ^ 2 = ‖wq S ell k (ballRes G p z)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [wq_apply, wq_apply]
    show ‖(((ell : ℝ) ^ bstrat S k e)⁻¹) • (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1)
        then (WithLp.ofLp (AdalyFormal.GaugeCov.adBL g z)) e else 0)‖ ^ 2
      = ‖(((ell : ℝ) ^ bstrat S k e)⁻¹) • (if e.1 ∈ Ball p.2.1.1 (rhoT G.ell p.1) then (WithLp.ofLp z) e else 0)‖ ^ 2
    split_ifs
    · have h : (WithLp.ofLp (AdalyFormal.GaugeCov.adBL g z)) e
          = AdalyFormal.Balaban.CovariantOperators.RMap (g e.1) ((WithLp.ofLp z) e) :=
        AdalyFormal.GaugeCov.adGen_apply (fun b : Bond L => g b.1) z e
      rw [h, norm_smul, norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap]
    · simp
  have h0 := norm_nonneg (wq S ell k (ballRes G p (AdalyFormal.GaugeCov.adBL g z)))
  have h1 := norm_nonneg (wq S ell k (ballRes G p z))
  nlinarith [sq_nonneg (‖wq S ell k (ballRes G p (AdalyFormal.GaugeCov.adBL g z))‖ - ‖wq S ell k (ballRes G p z)‖),
    sq_nonneg (‖wq S ell k (ballRes G p (AdalyFormal.GaugeCov.adBL g z))‖ + ‖wq S ell k (ballRes G p z)‖)]

/-- **`hC2` at the printed class** (from `BallChartsAt`; no global gauge) -/
theorem hC2_class {ell M R k : ℕ} {Lu : PeriodicLatticeExtent} {S : Tower (scaleUp ell k Lu)}
    (hell2 : 2 ≤ ell) (hS : Admissible ell M R k S) (hM : 2002 ≤ M) (hRM : 1000 * ell ≤ R * M)
    (hL : ∀ σ : Fin 3, 1 ≤ scaleUp ell k Lu σ) (hLu : ∀ μ, ell < Lu μ + 1) {C α₀ : ℝ} (hC : 1 ≤ C) (hα : 0 < α₀)
    {U : LinkCfg (scaleUp ell k Lu)} (hB : AdalyFormal.OneGap.BallChartsAt ell M k S U C α₀ ((ell : ℝ) ^ k)⁻¹)
    (hsm : DQSmall ell (12 * M * ((ell : ℝ) ^ 3 * (2 * ((ell : ℝ) ^ 3 * (C * α₀))))))
    (z : BondFnL2 (scaleUp ell k Lu)) :
    ∑ p, ‖C2fullOf (geomOf ell k S) U z p‖
      ≤ 44217 * K2strat ell (12 * M * ((ell : ℝ) ^ 3 * (2 * ((ell : ℝ) ^ 3 * (C * α₀))))) * wnormSq S ell k z := by
  classical
  have hell : 0 < ell := by omega
  have hη : (0 : ℝ) < ((ell : ℝ) ^ k)⁻¹ := by positivity
  have hroom : 18 * ell ≤ R * M := by omega
  set αV : ℝ := (ell : ℝ) ^ 3 * (2 * ((ell : ℝ) ^ 3 * (C * α₀))) with hαV
  have hαV0 : 0 ≤ αV := by have : (0 : ℝ) ≤ C := by linarith
                           positivity
  set K2 : ℝ := K2strat ell (12 * M * αV) with hK2
  have hK20 : 0 ≤ K2 := by
    rw [hK2]; unfold K2strat
    have := K2free_nonneg ell ((1 + 3 * Real.pi) * alphaQ ell (12 * M * αV)) (thetaK2_lt_of ell _ hsm.hK2c)
    positivity
  set G := geomOf ell k S
  have hrow : ∀ p : BIdx G, ‖C2fullOf G U z p‖
      ≤ K2 * (if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes G p z)‖ ^ 2 else 0) := by
    intro p
    by_cases hp : 1 ≤ (p.1 : ℕ)
    · rw [if_pos hp]
      obtain ⟨g, V, hV, hag⟩ := rowChart2_ball hell2 hS hM hRM hL hC hα hη hB p hp
      refine (le_of_eq (gauge_C2full_norm G U g z p)).trans ?_
      set x := AdalyFormal.GaugeCov.adBL g z with hx
      have e1 : C2fullOf G (periodicGaugeTransform g U) x p = C2fullOf G V x p :=
        C2row_congr_U G hell _ V p x hag
      have e2 : C2fullOf G V x p = C2fullOf G V (ballRes G p x) p :=
        C2row_congr G hell V p _ _ (fun e he => (ballRes_apply_in G p x e he).symm)
      have hglob := C2full_strat12 ell M R k Lu S V αV hS hell2 hroom hLu hαV0 hV hsm (ballRes G p x)
      have hone : ‖C2fullOf G V (ballRes G p x) p‖ ≤ ∑ q, ‖C2fullOf G V (ballRes G p x) q‖ :=
        Finset.single_le_sum (f := fun q => ‖C2fullOf G V (ballRes G p x) q‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ p)
      have hw : wnormSq S ell k (ballRes G p x) = ‖wq S ell k (ballRes G p z)‖ ^ 2 := by
        rw [← wq_normSq, hx]
        exact congrArg (fun t : ℝ => t ^ 2) (wq_ballRes_gauge S G rfl p g z)
      rw [e1, e2]
      calc ‖C2fullOf G V (ballRes G p x) p‖ ≤ ∑ q, ‖C2fullOf G V (ballRes G p x) q‖ := hone
        _ ≤ K2 * wnormSq S ell k (ballRes G p x) := hglob
        _ = K2 * ‖wq S ell k (ballRes G p z)‖ ^ 2 := by rw [hw]
    · rw [if_neg hp, C2row_level0 G U z p (by omega), norm_zero, mul_zero]
  calc ∑ p, ‖C2fullOf G U z p‖
      ≤ ∑ p : BIdx G, K2 * (if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes G p z)‖ ^ 2 else 0) :=
        Finset.sum_le_sum (fun p _ => hrow p)
    _ = K2 * ∑ p : BIdx G, (if 1 ≤ (p.1 : ℕ) then ‖wq S ell k (ballRes G p z)‖ ^ 2 else 0) := by
        rw [Finset.mul_sum]
    _ ≤ K2 * (44217 * ‖wq S ell k z‖ ^ 2) := mul_le_mul_of_nonneg_left (ball_mult hS hell2 hroom z) hK20
    _ = 44217 * K2 * wnormSq S ell k z := by rw [wq_normSq]; ring

end AdalyFormal.M2OpLayer

#print axioms AdalyFormal.M2OpLayer.level_bounds12
#print axioms AdalyFormal.M2OpLayer.C2full_strat12
#print axioms AdalyFormal.M2OpLayer.C2row_congr_U
#print axioms AdalyFormal.M2OpLayer.wq_ballRes_gauge
#print axioms AdalyFormal.M2OpLayer.hC2_class

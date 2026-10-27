import DQ4

/-!
# DQ5 -- **D4 `K2_strat` (premise `hC2` of `DParts`)**: the stratified quadratic `ℓ¹` bound on the M1 regime (sub-builder DQ)

* **`C2full_strat`** : `Admissible ℓ M R k S`, `18ℓ ≤ RM`, `ℓ < N_u` (TorusOK's `hstrict`), `ℓ ≥ 2`, `α₀ ≥ 0`,
  `U ∈ M1Regular ℓ M 12 k S α₀ (ℓ^k)⁻¹`, `DQSmall ℓ (12Mα₀)`  ⟹
  `∀ z, Σ_p ‖C2fullOf (geomOf ℓ k S) U z p‖ ≤ K2strat ℓ (12Mα₀) · wnormSq S ℓ k z`.
* `dqSmall_exists` : `∀ ℓ ≥ 2, ∃ β₀ > 0, ∀ β ∈ [0, β₀], DQSmall ℓ β` (DL106 `stageB2` at `a = t = 1`).
* `K2free_mono`, `K2strat_mono` : the constant is monotone in the amplitude below the threshold.
* **`C2full_strat_window`** : `∀ ℓ ≥ 2, ∃ β₀ > 0, ∃ K2 ≥ 0` (both depending on `ℓ` only) such that the bound holds with `K2` for
  every `M R k Lu S U α₀` with `12Mα₀ ≤ β₀` (and the hypotheses above).
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
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond CoarseLattice mem_CoarseLattice)
open AdalyFormal.Balaban.LatticeOperators (CoarseBond)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.IngredientFamilyR2 (bondsLam geomOf C2fullOf C2CompL C2CompL_zero bgTower Cfg XS suCoord fromM2 BIdx
  toM2)
open AdalyFormal.NonflatJet (suOf rhoOf)
open AdalyFormal.BondComposite (nrm nrm_one_suCoord sum_le_of_injective rr)
open AdalyFormal.RegBgKU (KUSmall)
open AdalyFormal.DLayer (K2free K2s thetaK2 rhoOf_mono)
open AdalyFormal.CurvBlock (dv)
open AdalyFormal.M1 (strat bstrat M1Regular M1Bounds wnormSq)
open EstimatesLayer.E1E3 (e2Majorant e2Majorant_mono e2Majorant_nonneg)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

/-! ## 1. lattice bookkeeping -/

theorem scaleUp_split (ell k n : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (hnk : n ≤ k) :
    scaleUp ell n (scaleUp ell (k - n) Lu) = scaleUp ell k Lu := by
  funext μ
  unfold scaleUp
  have h1 : 1 ≤ (Lu μ + 1) * ell ^ (k - n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.sub_add_cancel h1, Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hnk]

theorem torus_big (ell k n : ℕ) (Lu : PeriodicLatticeExtent) (hell : 2 ≤ ell) (hLu : ∀ μ, ell < Lu μ + 1)
    (hnk : n ≤ k) (ρ : Fin 3) : 2 * ell ^ n < scaleUp ell k Lu ρ + 1 := by
  unfold scaleUp
  have hp : 0 < ell ^ k := pow_pos (by omega) k
  have h1 : 1 ≤ (Lu ρ + 1) * ell ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [Nat.sub_add_cancel h1]
  have h2 : ell ^ n ≤ ell ^ k := Nat.pow_le_pow_right (by omega) hnk
  have h3 := hLu ρ
  have h4 : 0 < ell ^ n := pow_pos (by omega) n
  nlinarith

theorem K2free_nonneg (ell : ℕ) (ρ : ℝ) (hθ : thetaK2 ell ρ < 1) : 0 ≤ K2free ell ρ := by
  unfold K2free
  have : 0 < 1 - thetaK2 ell ρ := by linarith
  have : 0 ≤ K2s ell := by unfold K2s; positivity
  positivity

theorem thetaK2_lt_of (ell : ℕ) (ρ : ℝ)
    (h : 1536 * (ell : ℝ) ^ 2 * e2Majorant (rhoOf ell ρ) < 1 - 1 / (ell : ℝ)) : thetaK2 ell ρ < 1 := by
  unfold thetaK2; linarith

/-! ## 2. the level sums -/

section
variable {L : PeriodicLatticeExtent}

/-- the per-(level, aligned bond) majorant -/
noncomputable def rowF (ell k : ℕ) (Vc : ℕ → Cfg L) (xs : ℕ → BondFnL2 L)
    (q : Σ n : Fin (k + 1), CoarseBond L (ell ^ (n : ℕ))) : ℝ :=
  ((ell : ℝ) ^ (q.1 : ℕ))⁻¹ *
    ‖suOf (C2CompL ell (AdalyFormal.Balaban.UbarTowerCov.UbarTower AdalyFormal.Balaban.SuTwoLogExp.su2LogExp ell
      (Vc q.1)) q.1 (suCoord (xs q.1)) (q.2.1.1, q.2.2))‖

theorem rowF_nonneg (ell k : ℕ) (Vc : ℕ → Cfg L) (xs : ℕ → BondFnL2 L)
    (q : Σ n : Fin (k + 1), CoarseBond L (ell ^ (n : ℕ))) : 0 ≤ rowF ell k Vc xs q := by
  unfold rowF; positivity

theorem suOf_zero : suOf (0 : Fin 3 → ℝ) = 0 := Subtype.ext (map_zero toM2)

theorem rowF_zero (ell k : ℕ) (Vc : ℕ → Cfg L) (xs : ℕ → BondFnL2 L) (n : Fin (k + 1)) (hn : (n : ℕ) = 0)
    (c : CoarseBond L (ell ^ (n : ℕ))) : rowF ell k Vc xs ⟨n, c⟩ = 0 := by
  have h0 : ∀ m : ℕ, m = 0 → ∀ (bg : ℕ → Cfg L) (a : XS L), C2CompL ell bg m a = 0 := by
    rintro m rfl bg a; exact C2CompL_zero ell bg a
  unfold rowF
  simp only
  rw [h0 _ hn, Pi.zero_apply, suOf_zero, norm_zero, mul_zero]

end

/-! ## 3. the theorem -/

/-- **D4 `K2_strat`** -/
theorem C2full_strat (ell M R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu))
    (U : LinkCfg (scaleUp ell k Lu)) (α₀ : ℝ) (hA : Admissible ell M R k S) (hell2 : 2 ≤ ell)
    (hroom : 18 * ell ≤ R * M) (hLu : ∀ μ, ell < Lu μ + 1) (hα₀ : 0 ≤ α₀)
    (hU : M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U) (hsm : DQSmall ell (12 * M * α₀))
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
      obtain ⟨hlinks, hplaq⟩ := level_bounds hA hell2 hroom hn1 hnk ((ell : ℝ) ^ k)⁻¹ hη0 α₀ A hB hHT hβ0 hsm.h4
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

/-! ## 4. the threshold and a β-free constant -/

theorem dqSmall_exists (ell : ℕ) (hell : 2 ≤ ell) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → DQSmall ell β := by
  obtain ⟨θ₁, hθ₁, ε₀, hε₀, γm, hγm, hall⟩ := AdalyFormal.DLayer.stageB2 ell hell 1 1 one_pos one_pos
  have hl : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  set c : ℝ := 38 * (ell : ℝ) ^ 2 with hc
  set P : ℝ := 1 + 3 * Real.pi with hP
  have hc0 : 0 < c := by positivity
  have hP0 : 0 < P := by positivity
  set β₀ : ℝ := min (1 / 4) (min (1 / (4000000 * (ell : ℝ) ^ 2 * c))
    (min (ε₀ / (2 * P * c)) (1 / (1000 * (ell : ℝ) ^ 3 * P * c)))) with hβ₀
  have hβ₀pos : 0 < β₀ := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  refine ⟨β₀, hβ₀pos, fun β hβ0 hβ => ?_⟩
  have hb4 : β ≤ 1 / 4 := hβ.trans (min_le_left _ _)
  have hb1 : β ≤ 1 / (4000000 * (ell : ℝ) ^ 2 * c) := hβ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb2 : β ≤ ε₀ / (2 * P * c) :=
    hβ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hb3 : β ≤ 1 / (1000 * (ell : ℝ) ^ 3 * P * c) :=
    hβ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hαc : alphaQ ell β ≤ c * β := by
    unfold alphaQ
    have h1 : 8 * β ^ 2 ≤ 2 * β := by nlinarith
    have h2 : 512 * β ^ 3 ≤ 32 * β := by
      have : β ^ 2 ≤ 1 / 16 := by nlinarith
      have h5 := mul_le_mul_of_nonneg_left this hβ0
      nlinarith
    have h3 : 4 * β + 8 * β ^ 2 + 512 * β ^ 3 ≤ 38 * β := by linarith
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (ell : ℝ) ^ 2)
    rw [hc]; linarith
  have hα0 : 0 ≤ alphaQ ell β := alphaQ_nonneg ell hβ0
  have hcb : 4000000 * (ell : ℝ) ^ 2 * alphaQ ell β ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hb1
    have := mul_le_mul_of_nonneg_left hαc (by positivity : (0 : ℝ) ≤ 4000000 * (ell : ℝ) ^ 2)
    nlinarith
  have h1000 : P * alphaQ ell β ≤ 1 / (1000 * (ell : ℝ) ^ 3) := by
    rw [le_div_iff₀ (by positivity)] at hb3
    rw [le_div_iff₀ (by positivity)]
    have h6 := mul_le_mul_of_nonneg_left hαc hP0.le
    have h7 := mul_le_mul_of_nonneg_right h6 (by positivity : (0 : ℝ) ≤ 1000 * (ell : ℝ) ^ 3)
    nlinarith
  have hρ : P * alphaQ ell β < ε₀ := by
    rw [le_div_iff₀ (by positivity)] at hb2
    have := mul_le_mul_of_nonneg_left hαc hP0.le
    nlinarith
  obtain ⟨hKU, -, Num, -⟩ := hall (P * alphaQ ell β) 0 (mul_nonneg hP0.le hα0) hρ le_rfl hε₀
  exact ⟨by linarith, hcb, hKU, h1000, Num.hK2c⟩

theorem thetaK2_mono (ell : ℕ) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') : thetaK2 ell ρ ≤ thetaK2 ell ρ' := by
  unfold thetaK2
  have := e2Majorant_mono (by unfold rhoOf; positivity) (rhoOf_mono ell h)
  have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1536 * (ell : ℝ) ^ 2)
  linarith

theorem K2free_mono (ell : ℕ) (hell : 1 ≤ ell) {ρ ρ' : ℝ} (h0 : 0 ≤ ρ) (h : ρ ≤ ρ') (hθ' : thetaK2 ell ρ' < 1) :
    K2free ell ρ ≤ K2free ell ρ' := by
  unfold K2free
  have hθ := thetaK2_mono ell h0 h
  have hd : 0 < 1 - thetaK2 ell ρ' := by linarith
  have hd' : 1 - thetaK2 ell ρ' ≤ 1 - thetaK2 ell ρ := by linarith
  have hl0 : (0 : ℝ) < ell := by exact_mod_cast (show 0 < ell by omega)
  have hr : 0 < rr ell := Real.sqrt_pos.mpr (by positivity)
  have hK : 0 ≤ K2s ell := by unfold K2s; positivity
  have he : Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) ≤ Real.exp (2 * (3600 * (ell : ℝ) * ρ') / rr ell) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hr.le
    have : (0 : ℝ) ≤ ell := by positivity
    nlinarith
  have hnum : K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) * ell
      ≤ K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ') / rr ell) * ell :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) (by positivity)
  calc K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ) / rr ell) * ell / (1 - thetaK2 ell ρ)
      ≤ K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ') / rr ell) * ell / (1 - thetaK2 ell ρ) :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ K2s ell * Real.exp (2 * (3600 * (ell : ℝ) * ρ') / rr ell) * ell / (1 - thetaK2 ell ρ') :=
        div_le_div_of_nonneg_left (by positivity) hd hd'

theorem alphaQ_mono (ell : ℕ) {β β' : ℝ} (h0 : 0 ≤ β) (h : β ≤ β') : alphaQ ell β ≤ alphaQ ell β' := by
  unfold alphaQ
  have h2 : β ^ 2 ≤ β' ^ 2 := pow_le_pow_left₀ h0 h 2
  have h3 : β ^ 3 ≤ β' ^ 3 := pow_le_pow_left₀ h0 h 3
  have : 4 * β + 8 * β ^ 2 + 512 * β ^ 3 ≤ 4 * β' + 8 * β' ^ 2 + 512 * β' ^ 3 := by linarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem K2strat_mono (ell : ℕ) (hell : 1 ≤ ell) {β β' : ℝ} (h0 : 0 ≤ β) (h : β ≤ β') (hs : DQSmall ell β') :
    K2strat ell β ≤ K2strat ell β' := by
  unfold K2strat
  have hρ : (1 + 3 * Real.pi) * alphaQ ell β ≤ (1 + 3 * Real.pi) * alphaQ ell β' :=
    mul_le_mul_of_nonneg_left (alphaQ_mono ell h0 h) (by positivity)
  have := K2free_mono ell hell (by have := alphaQ_nonneg ell h0; positivity) hρ (thetaK2_lt_of ell _ hs.hK2c)
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **D4 on a k-free window with an amplitude-free constant** -/
theorem C2full_strat_window (ell : ℕ) (hell2 : 2 ≤ ell) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ K2 : ℝ, 0 ≤ K2 ∧
      ∀ (M R k : ℕ) (Lu : PeriodicLatticeExtent) (S : Tower (scaleUp ell k Lu)) (U : LinkCfg (scaleUp ell k Lu))
        (α₀ : ℝ), Admissible ell M R k S → 18 * ell ≤ R * M → (∀ μ, ell < Lu μ + 1) → 0 ≤ α₀ →
        (12 : ℝ) * M * α₀ ≤ β₀ → M1Regular ell M 12 k S α₀ ((ell : ℝ) ^ k)⁻¹ U →
        ∀ z : BondFnL2 (scaleUp ell k Lu),
          ∑ p, ‖C2fullOf (geomOf ell k S) U z p‖ ≤ K2 * wnormSq S ell k z := by
  obtain ⟨β₀, hβ₀, hsm⟩ := dqSmall_exists ell hell2
  have hs0 := hsm β₀ hβ₀.le le_rfl
  refine ⟨β₀, hβ₀, K2strat ell β₀, ?_, ?_⟩
  · unfold K2strat
    have := K2free_nonneg ell _ (thetaK2_lt_of ell _ hs0.hK2c)
    positivity
  · intro M R k Lu S U α₀ hA hroom hLu hα₀ hle hU z
    have hβ0 : 0 ≤ 12 * (M : ℝ) * α₀ := by positivity
    have h := C2full_strat ell M R k Lu S U α₀ hA hell2 hroom hLu hα₀ hU (hsm _ hβ0 hle) z
    have hw : 0 ≤ wnormSq S ell k z := by
      unfold wnormSq; exact Finset.sum_nonneg (fun b _ => by positivity)
    exact h.trans (mul_le_mul_of_nonneg_right (K2strat_mono ell (by omega) hβ0 hle hs0) hw)

#print axioms rowF
#print axioms scaleUp_split
#print axioms torus_big
#print axioms K2free_nonneg
#print axioms thetaK2_lt_of
#print axioms rowF_nonneg
#print axioms suOf_zero
#print axioms rowF_zero
#print axioms C2full_strat
#print axioms dqSmall_exists
#print axioms thetaK2_mono
#print axioms K2free_mono
#print axioms alphaQ_mono
#print axioms K2strat_mono
#print axioms C2full_strat_window

end AdalyFormal.M1DStrat.DQ

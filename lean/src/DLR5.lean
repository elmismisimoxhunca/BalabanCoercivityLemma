import DLR4

/-!
# DL5 -- `InstIneq` at milestone M0 with the D-layer DECOMPOSED into five elementary premises on the genuine objects

`instIneq_M0_D` : the frozen `InstIneq` (full tower, one gauge, `M0RegimeR` + `KUSmall` + `UnitSmall`) assuming, instead of MF7's
`hD2` (operator norm of Δ⁽²⁾, needs ‖W‖) and `hJ`:
* `hJs`   : `∀ b, ‖Jf b‖ ≤ SJ`                                          (JSmooth: a SUP bound on the (3.11) source; Lean units),
* `hHcol` : `∀ c v, Σ_b ‖(H δ_c^v)(b)‖ ≤ CH ‖v‖`                       (ℓ¹ column bound of `H = G Q*(QGQ*)⁻¹`: decay of H),
* `hK2`   : `∀ z, Σ_c ‖C2fullOf z c‖ ≤ K2n ‖z‖²`                          (quadratic ℓ¹ bound of the composite second jet, CMP98 (149)-type),
* `hH1col`: `∀ e v, Σ_b ‖(H₁in δ_e^v)(b)‖ ≤ CH1 ‖v‖`                    (ℓ¹ column bound of `H₁in`),
* `hKD`   : `∀ B, Σ_e ‖(D2in B)(e)‖ ≤ KD ‖B‖²`                           (quadratic ℓ¹ bound of `D̃⁽²⁾`),
with `ε' = 2 (CH·SJ) K2n (n² K̂) < 1` and `εJ = KD (CH1·SJ)`.  In the class scaling (`CH = C_H n³`, `SJ = cJ ρ n⁻³`, `K2n = K2 n⁻²`,
`CH1 = C_H1 n³`) both are k- and volume-free: `ε' = 2 C_H cJ K2 K̂ ρ`, `εJ = KD C_H1 cJ ρ` (`instIneq_M0_D_class`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane (scaleUp OnLambdaTildeIn)
open AdalyFormal.StatementLane2 (OnLambdaT)
open AdalyFormal.StatementLaneG (LamBlockSum InstIneq gparams GenP.genForm GenP.genC GenP.Nmat pe tauAdj_apply)
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.IngredientFamily (q1SU2)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy frobSupBond)
open AdalyFormal.Balaban.CovariantHjMinimizer (trivialU)
open AdalyFormal.AsmM0
open AdalyFormal.SliceCoerc
open AdalyFormal.PortSlice
open AdalyFormal.BondComposite
open AdalyFormal.CurvBlock (dv pw pw_one_of_plaq)
open AdalyFormal.RegBgKU (KUSmall regTower_M0_kuniform ginv_coercive_M0_kuniform class_bounds)
open AdalyFormal.M0Finish

/-- **M0 `InstIneq` with the D-layer decomposed** (free constants). -/
theorem instIneq_M0_D (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (SJ CH K2n CH1 KD : ℝ) (hSJ : 0 ≤ SJ) (hCH : 0 ≤ CH) (hK2n : 0 ≤ K2n) (hCH1 : 0 ≤ CH1) (hKD : 0 ≤ KD)
    (hJs : ∀ b, ‖(PU ell k Lu hell U a Lam).Jf b‖ ≤ SJ)
    (hHcol : ∀ (p : BIdx (PU ell k Lu hell U a Lam).G) (v : SuTwo),
      ∑ b, ‖(iE (PU ell k Lu hell U a Lam).G ((PU ell k Lu hell U a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (PU ell k Lu hell U a Lam).G))) b‖ ≤ CH * ‖v‖)
    (hK2 : ∀ z : BondFnL2 (scaleUp ell k Lu),
      ∑ p, ‖C2fullOf (PU ell k Lu hell U a Lam).G U z p‖ ≤ K2n * ‖z‖ ^ 2)
    (hH1col : ∀ (e' : Bond Lu) (v : SuTwo),
      ∑ b, ‖((PU ell k Lu hell U a Lam).H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)) b‖ ≤ CH1 * ‖v‖)
    (hKDb : ∀ B : BondFnL2 Lu, ∑ e', ‖((PU ell k Lu hell U a Lam).D2in B) e'‖ ≤ KD * ‖B‖ ^ 2)
    (hε' : 2 * (CH * SJ) * K2n * (((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0)) < 1) :
    InstIneq ell k hell a Lu
      (gam0M0f ell a t (rhoM0 ell k e q0) (2 * (CH * SJ) * K2n * (((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0)))
        (KD * (CH1 * SJ)) (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
      (fullTower ell k Lu) Lam U := by
  -- ===== constants and the M0 derivations (as in ASC4, RegTower from RKF) =====
  have hell2 : 2 ≤ ell := R.hell
  have hell0 : 0 < ell := hell
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell2
  have hellpos : (0 : ℝ) < ell := by linarith
  set n : ℝ := (ell : ℝ) ^ k with hn
  have hnpos : 0 < n := by positivity
  have hpi := Real.pi_pos
  have ha := R.ha
  have he0 := R.he0
  have hq0 := R.hq0
  set ρ := rhoM0 ell k e q0 with hρdef
  set η := e + 3 * Real.pi * (n * q0) with hη
  have hρ : ρ = n * η := by rw [hρdef]; unfold rhoM0; rfl
  have hηnn : 0 ≤ η := by rw [hη]; positivity
  have hρnn : 0 ≤ ρ := by rw [hρ]; positivity
  have hηρ : η = ρ / n := by rw [hρ]; field_simp
  have hρ1000 := R.h1000
  have hρ216 := R.h216
  set Kh := KhatM0 ell a t ρ with hKh
  have hKhpos : 0 < Kh := KhatM0_pos ell a t ρ ha hρ216
  -- class
  set ε : ℕ → ℝ := fun j => (ell : ℝ) ^ j * e + 3 * Real.pi * (((ell : ℝ) ^ 2) ^ j * q0) with hεdef
  have hεnn : ∀ j, 0 ≤ ε j := fun j => by simp only [hεdef]; positivity
  have hεη : ∀ j, j < k → ε j ≤ (ell : ℝ) ^ j * η := fun j hj => by
    have := eps_class_le ell k (by omega) e q0 hq0 j hj.le
    rw [hη]; exact this
  have hεs : ∀ j, j < k → ε j ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
    intro j hj
    have h1 : (ell : ℝ) ^ j * ell ≤ n := by
      rw [hn, ← pow_succ]; exact pow_le_pow_right₀ (by linarith) hj
    have h2 : (ell : ℝ) ^ j * η ≤ ρ / ell := by
      rw [hηρ, mul_div_assoc', div_le_div_iff₀ hnpos hellpos]
      nlinarith [mul_le_mul_of_nonneg_left h1 hρnn]
    have h3 : ρ / ell ≤ 1 / (1000 * (ell : ℝ) ^ 4) := by
      calc ρ / ell ≤ (1 / (1000 * (ell : ℝ) ^ 3)) / ell := div_le_div_of_nonneg_right hρ1000 hellpos.le
        _ = 1 / (1000 * (ell : ℝ) ^ 4) := by field_simp
    exact (hεη j hj).trans (h2.trans h3)
  have h0 := pw_one_of_plaq U q0 hq0 R.hplaq
  have hcl : TowerClass ell k Lu U ε :=
    towerClass_of_blocking ell k Lu hell2 U q0 e hq0 h0 R.hlinks R.hN R.hcb
  have hU : frobSupBond U ≤ ρ / n := by
    refine (frobSupBond_le_of U R.hlinks).trans ?_
    rw [← hηρ, hη]
    nlinarith [mul_nonneg hnpos.le hq0, hpi]
  have hAl : ∀ i, i < k → AlignedLinkBound (ell ^ i) (bgTower (GF ell k Lu) U i) (ρ * (ell : ℝ) ^ i / n) := by
    intro i hi z hz μ
    refine (hcl i hi z hz μ).trans ?_
    refine (hεη i hi).trans (le_of_eq ?_)
    rw [hηρ]; ring
  have hpos : 72 * ρ ^ 2 + 4 * (6 * ρ) ^ 2 < 1 := by nlinarith
  have hE := AdalyFormal.SiteCoercivity.geom_tower_sum ell k hell2 ρ hρnn
  have hu := hu_al ell k Lu hell2 U a ha ρ (6 * ρ) hpos hU (fun i => ρ * (ell : ℝ) ^ i / n) hAl hE
  have hreg : RegTower ell (bgTower (GF ell k Lu) U) k :=
    regTower_M0_kuniform ell k Lu hell2 U e q0 he0 hq0 R.hlinks R.hplaq H
  have hB0 := B0_fullTower ell k Lu hell0 U hreg
  -- ===== the D-layer from the decomposed premises =====
  set P := PU ell k Lu hell U a Lam with hP
  have hOm : P.G.Om0 = Set.univ := PU_Om0 ell k Lu hell U a Lam
  have hcoer : ∀ y : ↥(bondSupp P.G), ‖y‖ ^ 2 ≤ (n ^ 2 * Kh) * ⟪y, P.data.Ginv y⟫ :=
    fun y => ginv_coercive_M0_kuniform ell k Lu U a t e q0 R H Lam y
  have hψ : ∀ p, ‖psiD P p‖ ≤ CH * SJ := psi_le_of_col P CH SJ hCH hSJ hHcol hJs
  have hD2f := formD2 P hOm hu hB0 (n ^ 2 * Kh) (by positivity) hcoer (CH * SJ) K2n (mul_nonneg hCH hSJ) hK2n hψ hK2
  have hψ1 : ∀ e', ‖psi1u P e'‖ ≤ CH1 * SJ := psi1u_le_of_col P CH1 SJ hCH1 hSJ hH1col hJs
  have hJ : ∀ Bt : Bond Lu → SuTwo, OnLambdaTildeIn Lam ell Bt → OnLambdaT Lam Bt →
      |⟪P.H1in (P.D2in (WithLp.toLp 2 (Cop Lam P.Q1 Bt))), P.Jf⟫|
        ≤ KD * (CH1 * SJ) * ‖(WithLp.toLp 2 (Cop Lam P.Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by
    intro Bt _ _
    have h1 := hJ_le P (CH1 * SJ) hψ1 (WithLp.toLp 2 (Cop Lam P.Q1 Bt))
    have h2 := hKDb (WithLp.toLp 2 (Cop Lam P.Q1 Bt))
    calc _ ≤ CH1 * SJ * ∑ e', ‖(P.D2in (WithLp.toLp 2 (Cop Lam P.Q1 Bt))) e'‖ := h1
      _ ≤ CH1 * SJ * (KD * ‖(WithLp.toLp 2 (Cop Lam P.Q1 Bt) : BondFnL2 Lu)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCH1 hSJ)
      _ = KD * (CH1 * SJ) * ‖(WithLp.toLp 2 (Cop Lam P.Q1 Bt) : BondFnL2 Lu)‖ ^ 2 := by ring
  have hε'0 : 0 ≤ 2 * (CH * SJ) * K2n * (n ^ 2 * Kh) := by positivity
  exact instIneq_M0_kuniform_f ell k Lu hell U a t e q0 R H HU hstrict hd Lam hLB
    (2 * (CH * SJ) * K2n * (n ^ 2 * Kh)) (KD * (CH1 * SJ)) hε'0 (by positivity) hε' hD2f hJ

/-- **class-scaled form**: `CH = C_H n³`, `SJ = cJ ρ n⁻³`, `K2n = K2 n⁻²`, `CH1 = C_H1 n³`; then `ε' = 2 C_H cJ K2 K̂ ρ`, `εJ = KD C_H1 cJ ρ`
(both k- and volume-free). -/
theorem instIneq_M0_D_class (ell k : ℕ) (Lu : PeriodicLatticeExtent) (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu))
    (a t e q0 : ℝ) (R : M0RegimeR ell k Lu U a t e q0) (H : KUSmall ell (rhoM0 ell k e q0))
    (HU : UnitSmall ell (rhoM0 ell k e q0))
    (hstrict : ∀ μ : Fin 3, ell < Lu μ + 1) (hd : ∀ μ, ell ∣ Lu μ + 1)
    (Lam : Set (PeriodicLatticeSite Lu)) (hLB : LamBlockSum ell Lam)
    (cJ C_H K2 C_H1 KD : ℝ) (hcJ : 0 ≤ cJ) (hC_H : 0 ≤ C_H) (hK2 : 0 ≤ K2) (hC_H1 : 0 ≤ C_H1) (hKD : 0 ≤ KD)
    (hJs : ∀ b, ‖(PU ell k Lu hell U a Lam).Jf b‖ ≤ cJ * rhoM0 ell k e q0 / ((ell : ℝ) ^ k) ^ 3)
    (hHcol : ∀ (p : BIdx (PU ell k Lu hell U a Lam).G) (v : SuTwo),
      ∑ b, ‖(iE (PU ell k Lu hell U a Lam).G ((PU ell k Lu hell U a Lam).data.H
        (WithLp.toLp 2 (Pi.single p v) : FSp (PU ell k Lu hell U a Lam).G))) b‖ ≤ C_H * ((ell : ℝ) ^ k) ^ 3 * ‖v‖)
    (hK2b : ∀ z : BondFnL2 (scaleUp ell k Lu),
      ∑ p, ‖C2fullOf (PU ell k Lu hell U a Lam).G U z p‖ ≤ K2 / ((ell : ℝ) ^ k) ^ 2 * ‖z‖ ^ 2)
    (hH1col : ∀ (e' : Bond Lu) (v : SuTwo),
      ∑ b, ‖((PU ell k Lu hell U a Lam).H1in (WithLp.toLp 2 (Pi.single e' v) : BondFnL2 Lu)) b‖
        ≤ C_H1 * ((ell : ℝ) ^ k) ^ 3 * ‖v‖)
    (hKDb : ∀ B : BondFnL2 Lu, ∑ e', ‖((PU ell k Lu hell U a Lam).D2in B) e'‖ ≤ KD * ‖B‖ ^ 2)
    (hε' : 2 * C_H * cJ * K2 * KhatM0 ell a t (rhoM0 ell k e q0) * rhoM0 ell k e q0 < 1) :
    InstIneq ell k hell a Lu
      (gam0M0f ell a t (rhoM0 ell k e q0) (2 * C_H * cJ * K2 * KhatM0 ell a t (rhoM0 ell k e q0) * rhoM0 ell k e q0)
        (KD * C_H1 * cJ * rhoM0 ell k e q0) (dCM0 ell (rhoM0 ell k e q0)) (cBM0 ell (rhoM0 ell k e q0)))
      (fullTower ell k Lu) Lam U := by
  have hn : (0 : ℝ) < (ell : ℝ) ^ k := pow_pos (by exact_mod_cast hell) k
  have hρ : 0 ≤ rhoM0 ell k e q0 := by
    have := (class_bounds ell k (by have := R.hell; omega) e q0 R.he0 R.hq0).1
    exact le_trans (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) R.he0) this
  have e1 : 2 * (C_H * ((ell : ℝ) ^ k) ^ 3 * (cJ * rhoM0 ell k e q0 / ((ell : ℝ) ^ k) ^ 3))
      * (K2 / ((ell : ℝ) ^ k) ^ 2) * (((ell : ℝ) ^ k) ^ 2 * KhatM0 ell a t (rhoM0 ell k e q0))
      = 2 * C_H * cJ * K2 * KhatM0 ell a t (rhoM0 ell k e q0) * rhoM0 ell k e q0 := by
    field_simp
  have e2 : KD * (C_H1 * ((ell : ℝ) ^ k) ^ 3 * (cJ * rhoM0 ell k e q0 / ((ell : ℝ) ^ k) ^ 3))
      = KD * C_H1 * cJ * rhoM0 ell k e q0 := by
    field_simp
  have h := instIneq_M0_D ell k Lu hell U a t e q0 R H HU hstrict hd Lam hLB
    (cJ * rhoM0 ell k e q0 / ((ell : ℝ) ^ k) ^ 3) (C_H * ((ell : ℝ) ^ k) ^ 3) (K2 / ((ell : ℝ) ^ k) ^ 2)
    (C_H1 * ((ell : ℝ) ^ k) ^ 3) KD (by positivity) (by positivity) (by positivity) (by positivity) hKD
    hJs hHcol hK2b hH1col hKDb (by rw [e1]; exact hε')
  rw [e1, e2] at h
  exact h

#print axioms instIneq_M0_D
#print axioms instIneq_M0_D_class

end AdalyFormal.DLayer

import DLR65
import AdalyFormal.Balaban.UbarTowerCovariance

/-!
# DL66 -- even-part bounds for the BLOCKED piece `V̄(V1·V0)_c` of the raw step (CMP98 (15)/(43) at stride `s`)

`V̄_c = exp[Σ_{x∈B(c₋)} ell⁻³ log W_x] · V(c)`, `W_x = V(Γ_{c,x})V(c)⁻¹` (`loopVar`), at `V = V1·V0`, base `V = V0`
(the loops `W_x(V0)` are NOT the identity: curved background).  Background hypothesis (per `c`):
`‖W_x(V0) − 1‖ ≤ 1/16` for `x ∈ B(c₋)`  (then `‖log W_x(V0)‖ ≤ π/32 ≤ 1/10`, `log_small_of`).
Constants: `loopVar` `(344N², 16N)`; `log loopVar` `(16048N², 32N)` (`EvQ.log` at a NON-identity base);
`exp(average)` `(76480N², 224N)`;  `V̄` `(78310N², 228N)`.  Smallness used: `16Nτ ≤ 1/4`, `32Nτ ≤ 1/2`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.DLayer

open scoped Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.RMapLipschitz (frobSq frobNorm frobSq_nonneg frobNorm_nonneg frobNorm_sq)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp su2Angle su2NegOne coe_mul coe_inv coe_one
  su2Log_one su2Exp_zero su2LogExp su2LogExp_log su2LogExp_exp)
open AdalyFormal.Balaban.TowerLawCov (coarsePathHolonomy coarseGammaPath)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.UbarTowerCov (loopVar gammaVarStrided coarseBondVar stridedBlockedGauge cPlusS)
open AdalyFormal.IngredientFamilyR2 (qsmul_real Wt rat_cast_Wt su2Log_mem_suTwo)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem one_mul_cfg (V0 : PeriodicLinkConfiguration SU2 L) : (fun b => (fun _ => (1 : SU2)) b * V0 b) = V0 := by
  funext b; exact one_mul _

/-- `e^y ≤ 1/(1−y)` -/
theorem exp_le_inv_one_sub (y : ℝ) (hy : y < 1) : Real.exp y ≤ 1 / (1 - y) := by
  have h1 := Real.add_one_le_exp (-y)
  have hpos : 0 < 1 - y := by linarith
  have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [le_div_iff₀ hpos]
  have hey := (Real.exp_pos y).le
  nlinarith [mul_le_mul_of_nonneg_left (show 1 - y ≤ Real.exp (-y) by linarith) hey]

theorem exp_small (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 10) :
    2 * (Real.exp (Real.sqrt 2 * x) - 1) ≤ 1 / 2 ∧ Real.exp (Real.sqrt 2 * x) ≤ 2 := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hy : Real.sqrt 2 * x ≤ 3 / 20 := by nlinarith
  have h := exp_le_inv_one_sub (Real.sqrt 2 * x) (by linarith)
  have h2 : 1 / (1 - Real.sqrt 2 * x) ≤ 20 / 17 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  constructor <;> linarith

theorem log_small_of (g : SU2) (hg : frobNorm ((g : Mt) - 1) ≤ 1 / 16) : frobNorm (su2Log g) ≤ 1 / 10 := by
  have ha := AdalyFormal.Balaban.Bch2.angle_le_of_frobNorm_sub_one (g := g) (by linarith)
  have h := AdalyFormal.Balaban.Bch2.frobNorm_su2Log_le ha
  have hpi := Real.pi_lt_d2
  have := mul_le_mul (by norm_num at hpi ⊢; linarith : Real.pi / 2 ≤ 8 / 5) hg (frobNorm_nonneg _) (by norm_num)
  linarith

/-- the four holonomy factors of a loop -/
theorem ev_loopVar (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L) (hx : x ∈ stepBlockOf c.1 s ell) :
    EvQ ((loopVar s ell (fun b => V1p b * V0 b) c x : SU2) : Mt) ((loopVar s ell (fun b => V1m b * V0 b) c x : SU2) : Mt)
      ((loopVar s ell (fun b => (fun _ => (1 : SU2)) b * V0 b) c x : SU2) : Mt) (344 * N ^ 2) (16 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  have hlen := gamma_len_le s ell hs c.1 x hx
  have hG : ((coarseGammaPath s c.1 x).length : ℝ) ≤ N := by
    have : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * ((ell : ℝ) - 1) := by
      have h3 : ((3 * (ell - 1) : ℕ) : ℝ) = 3 * ((ell : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; norm_num
      rw [← h3]; exact_mod_cast hlen
    linarith
  have hR : ((List.replicate ell c.2).length : ℝ) ≤ N := by
    rw [List.length_replicate]; linarith
  have h1 := ev_hol s hτ h V0 N hN1 c.1 _ hG
  have h2 := ev_hol s hτ h V0 N hN1 x _ hR
  have h3 := (ev_hol s hτ h V0 N hN1 (cPlusS s ell c) _ hG).inv
  have h4 := (ev_hol s hτ h V0 N hN1 c.1 _ hR).inv
  have h12 := h1.mul h2
  have h123 := h12.mul h3
  have h1234 := h123.mul h4
  unfold loopVar gammaVarStrided coarseBondVar
  refine h1234.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

theorem ev_log_loopVar (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 16 * N * τ ≤ 1 / 4) (c : PeriodicLatticeEdge L) (x : PeriodicLatticeSite L)
    (hx : x ∈ stepBlockOf c.1 s ell) (hW : frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16) :
    EvQ (su2Log (loopVar s ell (fun b => V1p b * V0 b) c x)) (su2Log (loopVar s ell (fun b => V1m b * V0 b) c x))
      (su2Log (loopVar s ell (fun b => (fun _ => (1 : SU2)) b * V0 b) c x)) (16048 * N ^ 2) (32 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  have h1 := ev_loopVar s ell hs hell hτ h V0 N hN c x hx
  rw [one_mul_cfg] at h1 ⊢
  have hlog := log_small_of _ hW
  have hE := (exp_small _ (frobNorm_nonneg _) hlog).1
  have := EvQ.log hτ h1 (by nlinarith) (by linarith) hE
  exact this.mono hτ (by nlinarith) (by nlinarith)

/-- `V̄(V1·V0)_c` -/
theorem ev_ubar (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 32 * N * τ ≤ 1 / 2) (c : PeriodicLatticeEdge L)
    (hW : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16) :
    EvQ ((stridedBlockedGauge su2LogExp s ell (fun b => V1p b * V0 b) c : SU2) : Mt)
      ((stridedBlockedGauge su2LogExp s ell (fun b => V1m b * V0 b) c : SU2) : Mt)
      ((stridedBlockedGauge su2LogExp s ell V0 c : SU2) : Mt) (78310 * N ^ 2) (228 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  -- the average of the logs
  set Yof : PeriodicLinkConfiguration SU2 L → Mt := fun V =>
    ∑ x ∈ stepBlockOf c.1 s ell, Wt ell • su2Log (loopVar s ell V c x) with hYof
  have hY : ∀ V, ∑ x ∈ stepBlockOf c.1 s ell, ((ell : ℚ) ^ 3)⁻¹ • su2LogExp.log (loopVar s ell V c x) = Yof V := by
    intro V
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [su2LogExp_log, qsmul_real, rat_cast_Wt]
  have hmem : ∀ V, Yof V ∈ AdalyFormal.Balaban.CovariantOperators.suTwo := fun V =>
    Submodule.sum_mem _ (fun x _ => Submodule.smul_mem _ _ (su2Log_mem_suTwo _))
  have hav : EvQ (Yof (fun b => V1p b * V0 b)) (Yof (fun b => V1m b * V0 b)) (Yof V0) (16048 * N ^ 2) (32 * N) τ := by
    have := EvQ.avg (stepBlockOf c.1 s ell) (Wt ell) (Wt_nonneg ell) (Wt_card s ell hs hell c.1)
      (fun x => su2Log (loopVar s ell (fun b => V1p b * V0 b) c x))
      (fun x => su2Log (loopVar s ell (fun b => V1m b * V0 b) c x))
      (fun x => su2Log (loopVar s ell V0 c x)) (16048 * N ^ 2) (32 * N) τ (by positivity) (by positivity)
      (fun x hx => by
        have := ev_log_loopVar s ell hs hell hτ h V0 N hN (by nlinarith) c x hx (hW x hx)
        rwa [one_mul_cfg] at this) hτ
    exact this
  -- the base is small
  have hY0 : frobNorm (Yof V0) ≤ 1 / 10 := by
    have hs1 : frobNorm (Yof V0) ≤ ∑ x ∈ stepBlockOf c.1 s ell, Wt ell * (1 / 10) := by
      refine (AdalyFormal.RegBgKU.frob_sum _ _).trans (Finset.sum_le_sum (fun x hx => ?_))
      rw [fN_rsmul, abs_of_nonneg (Wt_nonneg ell)]
      exact mul_le_mul_of_nonneg_left (log_small_of _ (hW x hx)) (Wt_nonneg ell)
    rw [Finset.sum_const, nsmul_eq_mul] at hs1
    have := Wt_card s ell hs hell c.1
    nlinarith
  have hE := (exp_small _ (frobNorm_nonneg _) hY0).2
  have hexp := EvQ.exp hτ hav (by nlinarith) hE
  rw [← su2Exp_coe (hmem _), ← su2Exp_coe (hmem _), ← su2Exp_coe (hmem _)] at hexp
  -- the straight line
  have hR : ((List.replicate ell c.2).length : ℝ) ≤ N := by
    rw [List.length_replicate]; linarith
  have hline := ev_hol s hτ h V0 N hN1 c.1 _ hR
  rw [one_mul_cfg] at hline
  have hall := hexp.mul hline
  unfold stridedBlockedGauge
  rw [su2LogExp_exp, su2LogExp_exp, su2LogExp_exp, hY, hY, hY]
  unfold coarseBondVar
  refine hall.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

#print axioms exp_small
#print axioms log_small_of
#print axioms ev_loopVar
#print axioms ev_log_loopVar
#print axioms ev_ubar

end AdalyFormal.DLayer

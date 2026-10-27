import DLR66
import DLR63
import DLR28

/-!
# DL67 -- **the per-step second jet**: `‖C2StepX s ell V0 A c‖ ≤ 3613500·(3ell)²·β²` at a CURVED background

* `ev_rawStep` : the raw step (63)/(89) `V̿_c = exp(−S₋)·V̄(V1V0)_c·exp(S₊)·V̄(V0)_c⁻¹` (`rawStep_simp`), constants `(145478N², 340N)`;
* `ev_log_rawStep` : `log V̿_c` (base `log 1 = 0`): `(7227000N², 680N)`, under `1360Nτ ≤ 1`;
* `linkEv_expCfgX` : the links `exp(±t A_e)` (`EvQ.base`);
* **`C2StepX_row_le`** : for `A` with `‖toM2 (A e)‖_F ≤ β` on the edges `VisStep s ell c` read by the step at `c`, and the
  background loops at `c` within `1/16` of `1`:  `‖C2StepX s ell V0 A c‖ ≤ 3613500·(3ell)²·β²`.
  Route: even part of `t ↦ qStepX(tA)(c)` bounded at value level (DL64-DL66), then DL63 (`second_deriv_le_of_even`).
  Locality: `qStepX_congr` (DL27) replaces `A` by its restriction to `VisStep c`.
The background enters ONLY through (i) `RegBg s ell V0` (for `ContDiffAt`, i.e. so that the second derivative is the
genuine one) and (ii) `‖W_x(V0) − 1‖_F ≤ 1/16` for the loops at `c` — no derivative of `log` at a non-identity point.
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
open AdalyFormal.IngredientFamilyR2 (rawStep rawStep_simp rawStep_one_right qStepX qStepX_zero qStepX_contDiffAt
  C2StepX RegBg XS expCfgX toM2 fromM2 toM2_mem)

local notation "Mt" => Matrix (Fin 2) (Fin 2) ℂ

variable {L : PeriodicLatticeExtent}

theorem ev_rawStep (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 32 * N * τ ≤ 1 / 2) (c : PeriodicLatticeEdge L)
    (hW : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16) :
    EvQ ((rawStep s ell V0 V1p c : SU2) : Mt) ((rawStep s ell V0 V1m c : SU2) : Mt)
      ((rawStep s ell V0 (fun _ => (1 : SU2)) c : SU2) : Mt) (145478 * N ^ 2) (340 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  have hsm4 : 4 * N * τ ≤ 1 / 4 := by nlinarith
  rw [rawStep_simp, rawStep_simp, rawStep_simp, one_mul_cfg]
  have e1 : ∀ V1 : PeriodicLinkConfiguration SU2 L,
      su2Exp (-(AdalyFormal.IngredientFamilyR2.sBlock s ell V0 V1 c.1))
        = su2Exp ((-1 : ℝ) • AdalyFormal.IngredientFamilyR2.sBlock s ell V0 V1 c.1) := by
    intro V1; rw [neg_one_smul]
  have e2 : ∀ V1 : PeriodicLinkConfiguration SU2 L,
      su2Exp (AdalyFormal.IngredientFamilyR2.sBlock s ell V0 V1 (cPlusS s ell c))
        = su2Exp ((1 : ℝ) • AdalyFormal.IngredientFamilyR2.sBlock s ell V0 V1 (cPlusS s ell c)) := by
    intro V1; rw [one_smul]
  rw [e1, e1, e1, e2, e2, e2]
  have f1 := ev_exp_sBlock s ell hs hell hτ h V0 N hN hsm4 c.1 (-1) (by norm_num)
  have f2 := ev_ubar s ell hs hell hτ h V0 N hN hsm c hW
  have f3 := ev_exp_sBlock s ell hs hell hτ h V0 N hN hsm4 (cPlusS s ell c) 1 (by norm_num)
  have f4 := EvQ.const1 ((stridedBlockedGauge su2LogExp s ell V0 c)⁻¹) τ
  have hall := ((f1.mul f2).mul f3).mul f4
  refine hall.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

theorem ev_log_rawStep (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) {V1p V1m : PeriodicLinkConfiguration SU2 L} {τ : ℝ}
    (hτ : 0 ≤ τ) (h : LinkEv V1p V1m τ) (V0 : PeriodicLinkConfiguration SU2 L) (N : ℝ)
    (hN : 3 * (ell : ℝ) ≤ N) (hsm : 1360 * N * τ ≤ 1) (c : PeriodicLatticeEdge L)
    (hW : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16) :
    EvQ (su2Log (rawStep s ell V0 V1p c)) (su2Log (rawStep s ell V0 V1m c)) 0 (7227000 * N ^ 2) (680 * N) τ := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hN1 : 1 ≤ N := by linarith
  have h1 := ev_rawStep s ell hs hell hτ h V0 N hN (by nlinarith) c hW
  have hb : rawStep s ell V0 (fun _ => (1 : SU2)) c = 1 := rawStep_one_right s ell V0 c
  have hg0 : frobNorm (((rawStep s ell V0 (fun _ => (1 : SU2)) c : SU2) : Mt) - 1) ≤ 1 := by
    rw [hb, coe_one, sub_self, fN_zero]; norm_num
  have hE : 2 * (Real.exp (Real.sqrt 2 * frobNorm (su2Log (rawStep s ell V0 (fun _ => (1 : SU2)) c))) - 1) ≤ 1 / 2 := by
    rw [hb, su2Log_one, fN_zero, mul_zero, Real.exp_zero]; norm_num
  have h2 := EvQ.log hτ h1 (by nlinarith) hg0 hE
  rw [hb, su2Log_one] at h2
  refine h2.mono hτ ?_ ?_
  · nlinarith
  · nlinarith

/-! ## the links `exp(±tA)` -/

theorem linkEv_expCfgX (A : XS L) (t τ : ℝ) (hH : ∀ e, frobNorm (toM2 ((t • A) e)) ≤ τ) (hτ : τ ≤ 1 / 2) :
    LinkEv (expCfgX (t • A)) (expCfgX (-(t • A))) τ := by
  intro e
  have hm : toM2 ((t • A) e) ∈ AdalyFormal.Balaban.CovariantOperators.suTwo := toM2_mem _
  have hm' : -toM2 ((t • A) e) ∈ AdalyFormal.Balaban.CovariantOperators.suTwo := Submodule.neg_mem _ hm
  have e1 : ((expCfgX (t • A) e : SU2) : Mt) = NormedSpace.exp (toM2 ((t • A) e)) := su2Exp_coe hm
  have e2 : ((expCfgX (-(t • A)) e : SU2) : Mt) = NormedSpace.exp (-toM2 ((t • A) e)) := by
    have : ((expCfgX (-(t • A)) e : SU2) : Mt) = ((su2Exp (-toM2 ((t • A) e)) : SU2) : Mt) := by
      show ((su2Exp (toM2 ((-(t • A)) e)) : SU2) : Mt) = _
      rw [Pi.neg_apply, map_neg]
    rw [this]; exact su2Exp_coe hm'
  rw [e1, e2, coe_one]
  exact EvQ.base _ τ (hH e) hτ

/-! ## coordinates -/

theorem entry_le_fN (X : Mt) (i j : Fin 2) : ‖X i j‖ ≤ frobNorm X := by
  have hF : frobNorm X ^ 2 = ‖X 0 0‖ ^ 2 + ‖X 0 1‖ ^ 2 + ‖X 1 0‖ ^ 2 + ‖X 1 1‖ ^ 2 := by
    rw [frobNorm_sq]; unfold frobSq; simp only [nsq]
  have h2 : ‖X i j‖ ^ 2 ≤ frobNorm X ^ 2 := by
    rw [hF]
    fin_cases i <;> fin_cases j <;> simp <;>
      nlinarith [sq_nonneg ‖X 1 0‖, sq_nonneg ‖X 1 1‖, sq_nonneg ‖X 0 0‖, sq_nonneg ‖X 0 1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (frobNorm_nonneg _) two_ne_zero).mp h2

theorem fromM2_le (X : Mt) : ‖fromM2 X‖ ≤ frobNorm X := by
  refine (pi_norm_le_iff_of_nonneg (frobNorm_nonneg X)).mpr (fun i => ?_)
  fin_cases i
  · show ‖(X 0 0).im‖ ≤ _
    exact (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm _).trans (entry_le_fN X 0 0)
  · show ‖(X 0 1).re‖ ≤ _
    exact (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans (entry_le_fN X 0 1)
  · show ‖(X 0 1).im‖ ≤ _
    exact (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm _).trans (entry_le_fN X 0 1)

/-- the even part of the step, value level, `A` globally bounded -/
theorem even_qStepX (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (V0 : PeriodicLinkConfiguration SU2 L)
    (c : PeriodicLatticeEdge L)
    (hW : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16)
    (A : XS L) (β : ℝ) (hβ : 0 ≤ β) (hA : ∀ e, frobNorm (toM2 (A e)) ≤ β) (t : ℝ) (ht : 0 < t)
    (hsm : 1360 * (3 * (ell : ℝ)) * (t * β) ≤ 1) :
    ‖qStepX s ell V0 (t • A) c + qStepX s ell V0 (-(t • A)) c - (2 : ℝ) • qStepX s ell V0 0 c‖
      ≤ 7227000 * (3 * (ell : ℝ)) ^ 2 * β ^ 2 * t ^ 2 := by
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  set N : ℝ := 3 * (ell : ℝ) with hN
  set τ : ℝ := t * β with hτdef
  have hτ : 0 ≤ τ := by positivity
  have hτ2 : τ ≤ 1 / 2 := by nlinarith
  have hH : ∀ e, frobNorm (toM2 ((t • A) e)) ≤ τ := by
    intro e
    rw [Pi.smul_apply, map_smul, fN_rsmul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hA e) ht.le
  have hl := linkEv_expCfgX A t τ hH hτ2
  have hev := ev_log_rawStep s ell hs hell hτ hl V0 N le_rfl hsm c hW
  rw [qStepX_zero]
  have e : qStepX s ell V0 (t • A) c + qStepX s ell V0 (-(t • A)) c - (2 : ℝ) • (0 : XS L) c
      = fromM2 (su2Log (rawStep s ell V0 (expCfgX (t • A)) c) + su2Log (rawStep s ell V0 (expCfgX (-(t • A))) c)
          - 2 • (0 : Mt)) := by
    simp only [qStepX, map_add, map_sub, map_nsmul, map_zero, Pi.zero_apply, smul_zero, sub_zero, nsmul_zero]
  rw [e]
  refine (fromM2_le _).trans (hev.he.trans (le_of_eq ?_))
  rw [hτdef]; ring

/-- **the per-step second jet at a curved background** -/
theorem C2StepX_row_le (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell) (V0 : PeriodicLinkConfiguration SU2 L)
    (hreg : RegBg s ell V0) (c : PeriodicLatticeEdge L)
    (hW : ∀ x ∈ stepBlockOf c.1 s ell, frobNorm (((loopVar s ell V0 c x : SU2) : Mt) - 1) ≤ 1 / 16)
    (A : XS L) (β : ℝ) (hβ : 0 ≤ β) (hA : ∀ e, VisStep s ell c e → frobNorm (toM2 (A e)) ≤ β) :
    ‖C2StepX s ell V0 A c‖ ≤ 3613500 * (3 * (ell : ℝ)) ^ 2 * β ^ 2 := by
  classical
  have hl1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  -- the restriction of A to the visible edges
  set A' : XS L := fun e => if VisStep s ell c e then A e else 0 with hA'
  have hA'b : ∀ e, frobNorm (toM2 (A' e)) ≤ β := by
    intro e
    by_cases he : VisStep s ell c e
    · simp only [hA', if_pos he]; exact hA e he
    · simp only [hA', if_neg he, map_zero, fN_zero]; exact hβ
  set f := qStepX s ell V0 with hf
  have hC2 : ContDiffAt ℝ 2 f 0 := (qStepX_contDiffAt s ell V0 hreg).of_le (by simp)
  set π : XS L →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.proj c with hπ
  set t0 : ℝ := 1 / (1360 * (3 * (ell : ℝ)) * (β + 1)) with ht0
  have ht0pos : 0 < t0 := by positivity
  have hmain := AdalyFormal.DLayer.EvenLimit.second_deriv_le_of_even f hC2 π A
    (7227000 * (3 * (ell : ℝ)) ^ 2 * β ^ 2) t0 ht0pos (fun t ht htt0 => by
      have hsm : 1360 * (3 * (ell : ℝ)) * (t * β) ≤ 1 := by
        have h1 : t * β ≤ t0 * (β + 1) := by
          have := mul_le_mul htt0 (by linarith : β ≤ β + 1) hβ ht0pos.le
          linarith
        have h2 : 1360 * (3 * (ell : ℝ)) * (t0 * (β + 1)) = 1 := by
          rw [ht0]; field_simp
        have h3 : (0 : ℝ) ≤ 1360 * (3 * (ell : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 h3]
      have hev := even_qStepX s ell hs hell V0 c hW A' β hβ hA'b t ht hsm
      have e1 : f (t • A) c = qStepX s ell V0 (t • A') c :=
        qStepX_congr s ell V0 _ _ c (fun e he => by simp [hA', he])
      have e2 : f (-(t • A)) c = qStepX s ell V0 (-(t • A')) c :=
        qStepX_congr s ell V0 _ _ c (fun e he => by simp [hA', he])
      show ‖f (t • A) c + f (-(t • A)) c - (2 : ℝ) • f 0 c‖ ≤ _
      rw [e1, e2, hf]
      exact hev)
  show ‖((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 A A) c‖ ≤ _
  rw [Pi.smul_apply, norm_smul]
  have : ‖(fderiv ℝ (fderiv ℝ (qStepX s ell V0)) 0 A A) c‖ ≤ 7227000 * (3 * (ell : ℝ)) ^ 2 * β ^ 2 := hmain
  rw [Real.norm_of_nonneg (by norm_num)]
  linarith

#print axioms ev_rawStep
#print axioms ev_log_rawStep
#print axioms linkEv_expCfgX
#print axioms fromM2_le
#print axioms even_qStepX
#print axioms C2StepX_row_le

end AdalyFormal.DLayer

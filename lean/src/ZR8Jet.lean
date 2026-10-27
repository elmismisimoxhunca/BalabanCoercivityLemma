import ZR8Read

/-!
# ZR8Jet -- r8 locality of the REPAIRED (per-component) jets

For the local jets of `ZLocJet`:
 * component `c` of `QlinStepL s ell V₀ v` reads `V₀` and `v` only at bonds based in the ball `(c₋, 4 s ell)` (`QlinStepL_congr_bg`,
   `QlinStepL_congr_in`), same for the second derivative `D2StepL` (`D2StepL_congr_bg`, `D2StepL_mask`);
 * component `c` of the level composite `QlinCompL ell (bgTower G U) j` reads `U` only in the ball `(c₋, 2 rhoT ell j)` and its input
   only at bonds based in the ball `(c₋, rhoT ell j)` (`QlinCompL_congr_U`, `QlinCompL_congr_in`); the same for `C2CompL`
   (`C2CompL_congr_U`, `C2CompL_congr_in`).
These are exactly the statements that FAIL for the r7 jets (`fderiv` of the whole-torus map: one non-differentiable component anywhere
changes every row, `UR1.QlinStepX_bad_eq_zero`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace AdalyFormal.StatementLaneR8

open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.SuTwoLogExp (su2LogExp su2Log su2Exp M2 SU2)

variable {L : PeriodicLatticeExtent}

/-- agreement of two coordinate fields at every bond based in `W`. -/
def AgreeX (W : Set (PeriodicLatticeSite L)) (v v' : XS L) : Prop := ∀ e : PeriodicLatticeEdge L, e.1 ∈ W → v e = v' e

theorem AgreeX.mono {W W' : Set (PeriodicLatticeSite L)} {v v' : XS L} (h : AgreeX W v v') (hW : W' ⊆ W) : AgreeX W' v v' :=
  fun e he => h e (hW he)

/-! ## one step -/

theorem QlinStepL_congr_bg (s ell : ℕ) (hs : 0 < s) {V0 V0' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L)
    (h : AgreeAt (Ball c.1 (4 * (s * ell))) V0 V0') (v : XS L) : QlinStepL s ell V0 v c = QlinStepL s ell V0' v c := by
  rw [QlinStepL_apply, QlinStepL_apply, qStepComp_congr_bg s ell hs c h]

theorem QlinStepL_congr_in (s ell : ℕ) (hs : 0 < s) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    {v v' : XS L} (h : AgreeX (Ball c.1 (4 * (s * ell))) v v') : QlinStepL s ell V0 v c = QlinStepL s ell V0 v' c := by
  rw [QlinStepL_apply, QlinStepL_apply,
    fderiv_mask (maskX (Ball c.1 (4 * (s * ell)))) _ (qStepComp_mask s ell hs V0 c) v,
    fderiv_mask (maskX (Ball c.1 (4 * (s * ell)))) _ (qStepComp_mask s ell hs V0 c) v', maskX_eq_of_agree _ h]

theorem D2StepL_congr_bg (s ell : ℕ) (hs : 0 < s) {V0 V0' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L)
    (h : AgreeAt (Ball c.1 (4 * (s * ell))) V0 V0') (v w : XS L) : D2StepL s ell V0 v w c = D2StepL s ell V0' v w c := by
  rw [D2StepL_apply, D2StepL_apply, qStepComp_congr_bg s ell hs c h]

theorem D2StepL_congr_in (s ell : ℕ) (hs : 0 < s) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    {v v' w w' : XS L} (hv : AgreeX (Ball c.1 (4 * (s * ell))) v v') (hw : AgreeX (Ball c.1 (4 * (s * ell))) w w') :
    D2StepL s ell V0 v w c = D2StepL s ell V0 v' w' c := by
  rw [D2StepL_apply, D2StepL_apply,
    fderiv2_mask (maskX (Ball c.1 (4 * (s * ell)))) (maskX_idem _) _ (qStepComp_mask s ell hs V0 c) v w,
    fderiv2_mask (maskX (Ball c.1 (4 * (s * ell)))) (maskX_idem _) _ (qStepComp_mask s ell hs V0 c) v' w',
    maskX_eq_of_agree _ hv, maskX_eq_of_agree _ hw]

theorem C2StepL_congr_bg (s ell : ℕ) (hs : 0 < s) {V0 V0' : PeriodicLinkConfiguration SU2 L} (c : PeriodicLatticeEdge L)
    (h : AgreeAt (Ball c.1 (4 * (s * ell))) V0 V0') (v : XS L) : C2StepL s ell V0 v c = C2StepL s ell V0' v c := by
  show (1 / 2 : ℝ) • D2StepL s ell V0 v v c = (1 / 2 : ℝ) • D2StepL s ell V0' v v c
  rw [D2StepL_congr_bg s ell hs c h]

theorem C2StepL_congr_in (s ell : ℕ) (hs : 0 < s) (V0 : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L)
    {v v' : XS L} (h : AgreeX (Ball c.1 (4 * (s * ell))) v v') : C2StepL s ell V0 v c = C2StepL s ell V0 v' c := by
  show (1 / 2 : ℝ) • D2StepL s ell V0 v v c = (1 / 2 : ℝ) • D2StepL s ell V0 v' v' c
  rw [D2StepL_congr_in s ell hs V0 c h h]

/-! ## level composites: input locality (any background) -/

theorem QlinCompL_congr_in (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    ∀ (c : PeriodicLatticeEdge L) {v v' : XS L}, AgreeX (Ball c.1 (rhoT ell j)) v v' →
      QlinCompL ell bg j v c = QlinCompL ell bg j v' c := by
  induction j with
  | zero => intro c v v' h; exact h c (mem_Ball_self _ _)
  | succ j ih =>
      intro c v v' h
      rw [QlinCompL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      refine QlinStepL_congr_in _ ell (pow_pos hell j) _ c (fun e he => ih e (h.mono (Ball_sub he ?_)))
      rw [rhoT_succ]; omega

theorem C2CompL_congr_in (ell : ℕ) (hell : 0 < ell) (bg : ℕ → PeriodicLinkConfiguration SU2 L) (j : ℕ) :
    ∀ (c : PeriodicLatticeEdge L) {a a' : XS L}, AgreeX (Ball c.1 (rhoT ell j)) a a' →
      C2CompL ell bg j a c = C2CompL ell bg j a' c := by
  induction j with
  | zero => intro c a a' _; rw [C2CompL_zero, C2CompL_zero]
  | succ j ih =>
      intro c a a' h
      rw [C2CompL_succ, C2CompL_succ, Pi.add_apply, Pi.add_apply]
      have hsub : ∀ e : PeriodicLatticeEdge L, e.1 ∈ Ball c.1 (4 * (ell ^ j * ell)) →
          Ball e.1 (rhoT ell j) ⊆ Ball c.1 (rhoT ell (j + 1)) :=
        fun e he => Ball_sub he (by rw [rhoT_succ]; omega)
      congr 1
      · exact QlinStepL_congr_in _ ell (pow_pos hell j) _ c (fun e he => ih e (h.mono (hsub e he)))
      · exact C2StepL_congr_in _ ell (pow_pos hell j) _ c
          (fun e he => QlinCompL_congr_in ell hell bg j e (h.mono (hsub e he)))

/-! ## level composites: locality in the fine configuration `U` -/

theorem QlinCompL_congr_U (G : TowerGeom L) (hell : 0 < G.ell) {U U' : Cfg L} (v : XS L) (j : ℕ) :
    ∀ c : PeriodicLatticeEdge L, AgreeAt (Ball c.1 (2 * rhoT G.ell j)) U U' →
      QlinCompL G.ell (bgTower G U) j v c = QlinCompL G.ell (bgTower G U') j v c := by
  induction j with
  | zero => intro c _; rfl
  | succ j ih =>
      intro c h
      rw [QlinCompL_succ, QlinCompL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      have hbg : AgreeAt (Ball c.1 (4 * (G.ell ^ j * G.ell))) (bgTower G U j) (bgTower G U' j) :=
        bgTower_agreeAt G hell j c.1 _ (h.mono (Ball_mono (by rw [rhoT_succ]; omega)))
      rw [QlinStepL_congr_bg _ G.ell (pow_pos hell j) c hbg]
      refine QlinStepL_congr_in _ G.ell (pow_pos hell j) _ c (fun e he => ih e (h.mono (Ball_sub he ?_)))
      rw [rhoT_succ]; omega

theorem C2CompL_congr_U (G : TowerGeom L) (hell : 0 < G.ell) {U U' : Cfg L} (a : XS L) (j : ℕ) :
    ∀ c : PeriodicLatticeEdge L, AgreeAt (Ball c.1 (2 * rhoT G.ell j)) U U' →
      C2CompL G.ell (bgTower G U) j a c = C2CompL G.ell (bgTower G U') j a c := by
  induction j with
  | zero => intro c _; rw [C2CompL_zero, C2CompL_zero]
  | succ j ih =>
      intro c h
      rw [C2CompL_succ, C2CompL_succ, Pi.add_apply, Pi.add_apply]
      have hbg : AgreeAt (Ball c.1 (4 * (G.ell ^ j * G.ell))) (bgTower G U j) (bgTower G U' j) :=
        bgTower_agreeAt G hell j c.1 _ (h.mono (Ball_mono (by rw [rhoT_succ]; omega)))
      have hsub : ∀ e : PeriodicLatticeEdge L, e.1 ∈ Ball c.1 (4 * (G.ell ^ j * G.ell)) →
          Ball e.1 (2 * rhoT G.ell j) ⊆ Ball c.1 (2 * rhoT G.ell (j + 1)) :=
        fun e he => Ball_sub he (by rw [rhoT_succ]; omega)
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [QlinStepL_congr_bg _ G.ell (pow_pos hell j) c hbg]
        exact QlinStepL_congr_in _ G.ell (pow_pos hell j) _ c (fun e he => ih e (h.mono (hsub e he)))
      · rw [C2StepL_congr_bg _ G.ell (pow_pos hell j) c hbg]
        exact C2StepL_congr_in _ G.ell (pow_pos hell j) _ c
          (fun e he => QlinCompL_congr_U G hell a j e (h.mono (hsub e he)))

#print axioms QlinStepL_congr_bg
#print axioms QlinStepL_congr_in
#print axioms D2StepL_congr_in
#print axioms QlinCompL_congr_in
#print axioms C2CompL_congr_in
#print axioms QlinCompL_congr_U
#print axioms C2CompL_congr_U

end AdalyFormal.StatementLaneR8

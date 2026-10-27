import CB4
/-!
# CB5 -- level-uniform curvature blocking for the genuine tower `ubarTowerSU2` (global form)

Hypotheses: `0 < ell`, `blkConstOf ell < ell²` (true for every `ell ≥ 13`, `blkConst_lt_sq`), and a
bound `q0` on every fine (stride-1) plaquette word.  Conclusions, for every level `l`, every bond /
site of every periodic extent (no divisibility, no smallness, no gauge choice):

* `defect_tower`:  `dv (Ū^l(c) · strT^l(c)⁻¹) ≤ K · (ell²)^l · q0`,  `K = KC ell`;
* `link_tower`:    `dv (Ū^l(c)) ≤ ell^l · e + K · (ell²)^l · q0`  if every fine link has `dv ≤ e`;
* `curv_tower`:    `dv (pw (ell^l) Ū^l y ν μ) ≤ (4K + 1) · (ell²)^l · q0`  (level-uniform curvature
  blocking of the genuine tower);
* `KC_le_sixty`:   `K ≤ 60` for every `ell ≥ 14`.

`KC ell = (π/2)·3(ell−1)ell / (ell² − blkConstOf ell)`; `blkConstOf ell = ell + (π/2)(8 ell − 6)` is
the tree's per-level link constant (17.708 at `ell = 2`); here it is the growth rate of the DEFECT,
which is sourced at rate `ell²` by the curvature; the bound is level-uniform iff the source outruns
the defect rate.

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)

variable {L : PeriodicLatticeExtent}

/-- The curvature-source coefficient `(π/2)·3(ell−1)·ell`. -/
def aC (ell : ℕ) : ℝ := Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ))

/-- The level-uniform defect constant. -/
def KC (ell : ℕ) : ℝ := aC ell / ((ell : ℝ) ^ 2 - blkConstOf ell)

theorem aC_nonneg (ell : ℕ) (hell : 0 < ell) : 0 ≤ aC ell := by
  have h1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have h2 : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
  unfold aC; have := Real.pi_pos; positivity

theorem KC_nonneg (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2) :
    0 ≤ KC ell := div_nonneg (aC_nonneg ell hell) (by linarith)

theorem KC_eq (ell : ℕ) (hr : blkConstOf ell < (ell : ℝ) ^ 2) :
    KC ell * ((ell : ℝ) ^ 2 - blkConstOf ell) = aC ell := by
  unfold KC; field_simp [ne_of_gt (sub_pos.mpr hr)]

/-- **The defect tower is level-uniform.** -/
theorem defect_tower (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) :
    ∀ (l : ℕ) (c : PeriodicLatticeEdge L),
      dv (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) ≤ KC ell * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hK := KC_nonneg ell hell hr
  have hKe := KC_eq ell hr
  intro l
  induction l with
  | zero =>
      intro c
      show dv (U c * (U c)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one, pow_zero, mul_one]; exact mul_nonneg hK hq0
  | succ k ih =>
      intro c
      have hs : 0 < ell ^ k := pow_pos hell k
      set X : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hX : 0 ≤ X := by positivity
      have hq := pw_strT_le ell U q0 h0 k
      have hstep := defect_step (ell ^ k) ell hs hell (ubarTowerSU2 ell U k) (strT ell U k) c
        (KC ell * X) X (by positivity) hX
        (fun x _ b _ => (ih b).trans (le_of_eq (by simp only [X]; ring)))
        (fun b _ => (ih b).trans (le_of_eq (by simp only [X]; ring)))
        (fun x _ t _ => hq t.1 t.2.1 t.2.2)
      have hsh : ubarTowerSU2 ell U (k + 1) c * (strT ell U (k + 1) c)⁻¹
          = ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k) c
            * (coarseBondVar (ell ^ k) ell (strT ell U k) c)⁻¹ := rfl
      rw [hsh]
      refine le_trans hstep (le_of_eq ?_)
      have hb : blkConstOf ell = (ell : ℝ) + Real.pi / 2 * (8 * (ell : ℝ) - 6) := rfl
      have ha : aC ell = Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ)) := rfl
      have hpow : ((ell : ℝ) ^ 2) ^ (k + 1) * q0 = (ell : ℝ) ^ 2 * X := by
        simp only [X]; ring
      rw [mul_assoc (KC ell), hpow]
      rw [hb, ha] at hKe
      linear_combination (-X) * hKe

/-- **Link tower.** -/
theorem link_tower (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (q0 e : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) (he : ∀ b, dv (U b) ≤ e)
    (l : ℕ) (c : PeriodicLatticeEdge L) :
    dv (ubarTowerSU2 ell U l c) ≤ (ell : ℝ) ^ l * e + KC ell * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have h1 := defect_tower ell hell hr U q0 hq0 h0 l c
  have h2 := strT_link_le ell U e he l c
  have hid : ubarTowerSU2 ell U l c
      = (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) * strT ell U l c := by group
  rw [hid]
  have := dv_mul (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹) (strT ell U l c)
  linarith

/-- **Level-uniform curvature blocking of the genuine tower.** -/
theorem curv_tower (ell : ℕ) (hell : 0 < ell) (hr : blkConstOf ell < (ell : ℝ) ^ 2)
    (U : PeriodicLinkConfiguration SU2 L) (q0 : ℝ) (hq0 : 0 ≤ q0)
    (h0 : ∀ y ν μ, dv (pw 1 U y ν μ) ≤ q0) (l : ℕ) (y : PeriodicLatticeSite L) (ν μ : Fin 3) :
    dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ)
      ≤ (4 * KC ell + 1) * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hD := defect_tower ell hell hr U q0 hq0 h0 l
  have hT := pw_strT_le ell U q0 h0 l y ν μ
  have h4 := four_cmp
    (ubarTowerSU2 ell U l (y, ν) * (strT ell U l (y, ν))⁻¹)
    (ubarTowerSU2 ell U l (coarseShift y (ell ^ l) ν, μ)
      * (strT ell U l (coarseShift y (ell ^ l) ν, μ))⁻¹)
    (ubarTowerSU2 ell U l (coarseShift y (ell ^ l) μ, ν)
      * (strT ell U l (coarseShift y (ell ^ l) μ, ν))⁻¹)
    (ubarTowerSU2 ell U l (y, μ) * (strT ell U l (y, μ))⁻¹)
    (strT ell U l (y, ν)) (strT ell U l (coarseShift y (ell ^ l) ν, μ))
    (strT ell U l (coarseShift y (ell ^ l) μ, ν)) (strT ell U l (y, μ))
  simp only [inv_mul_cancel_right] at h4
  have e1 := hD (y, ν)
  have e2 := hD (coarseShift y (ell ^ l) ν, μ)
  have e3 := hD (coarseShift y (ell ^ l) μ, ν)
  have e4 := hD (y, μ)
  unfold pw at hT ⊢
  linarith

/-- `ell ≥ 13` gives the threshold. -/
theorem blkConst_lt_sq (ell : ℕ) (h : 13 ≤ ell) : blkConstOf ell < (ell : ℝ) ^ 2 := by
  have hl : (13 : ℝ) ≤ ell := by exact_mod_cast h
  have hpi := Real.pi_lt_d2
  have hb : blkConstOf ell = (ell : ℝ) + Real.pi / 2 * (8 * (ell : ℝ) - 6) := rfl
  rw [hb]
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hl), Real.pi_pos]

/-- For `ell ≥ 14` the defect constant is at most `60`. -/
theorem KC_le_sixty (ell : ℕ) (h : 14 ≤ ell) : KC ell ≤ 60 := by
  have hl : (14 : ℝ) ≤ ell := by exact_mod_cast h
  have hr := blkConst_lt_sq ell (by omega)
  have hpos : 0 < (ell : ℝ) ^ 2 - blkConstOf ell := sub_pos.mpr hr
  unfold KC
  rw [div_le_iff₀ hpos]
  have hpi := Real.pi_lt_d4
  have hb : blkConstOf ell = (ell : ℝ) + Real.pi / 2 * (8 * (ell : ℝ) - 6) := rfl
  have ha : aC ell = Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ)) := rfl
  rw [hb, ha]
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hl), Real.pi_pos,
    mul_nonneg (sub_nonneg.mpr hl) (le_of_lt Real.pi_pos)]

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.defect_tower
#print axioms AdalyFormal.CurvBlock.link_tower
#print axioms AdalyFormal.CurvBlock.curv_tower
#print axioms AdalyFormal.CurvBlock.blkConst_lt_sq
#print axioms AdalyFormal.CurvBlock.KC_le_sixty

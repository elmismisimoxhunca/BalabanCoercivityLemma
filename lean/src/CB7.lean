import CB6
/-!
# CB7 -- every `ell ≥ 2`: level-uniform curvature blocking ⟹ level-uniform link tower

If the genuine tower's own stride-`ell^l` plaquettes satisfy the level-uniform (CMP98 Prop. 2 type)
bound `dv (pw (ell^l) Ū^l ·) ≤ C·(ell²)^l·q0` for every level `l < n`, then for every `l ≤ n` the defect
`D_l = Ū^l · (strT^l)⁻¹` obeys `dv D_l ≤ (3π/2)·C·(ell²)^l·q0` — the defect now compounds only at the
telescoping rate `ell` (no perimeter term), which is `< ell²` for every `ell ≥ 2`.  So for the
dyadic tower the ONLY missing input for the link tower class is the curvature blocking itself.

(`curv_tower` gives the hypothesis for `ell ≥ 13` with `C = 4·KC ell + 1`.)

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Log su2Exp)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.TowerLawCov (coarseGammaPath)
open AdalyFormal.Balaban.UbarTowerCov (coarseBondVar loopVar)
open AdalyFormal.Balaban.QjComposite (stepBlockOf)
open AdalyFormal.Balaban.BlockedBackground (ubarSU2 ubarTowerSU2 ubarSU2_eq_blockedLink)
open AdalyFormal.Balaban.BlockingLinkEstimate (blockExponent frobNorm_su2Log_le_pi_div_two)
open AdalyFormal.Balaban.ClassPropagationUbar (blockExponent_antiHerm blockExponent_trace
  frobNorm_blockExponent_le' frobNorm_su2Exp_sub_one_le_uncond weight_sum_le_one gammaPath_length_le)

variable {L : PeriodicLatticeExtent}

/-- One step with the genuine curvature as input. -/
theorem defect_step_curv (s ell : ℕ) (hs : 0 < s) (hell : 0 < ell)
    (V T : PeriodicLinkConfiguration SU2 L) (c : PeriodicLatticeEdge L) (d P : ℝ)
    (hP0 : 0 ≤ P)
    (hdc : ∀ b ∈ pathBonds s c.1 (List.replicate ell c.2), dv (V b * (T b)⁻¹) ≤ d)
    (hP : ∀ x ∈ stepBlockOf c.1 s ell, ∀ t ∈ ladPlaqs s c.2 ell c.1 (coarseGammaPath s c.1 x),
      dv (pw s V t.1 t.2.1 t.2.2) ≤ P) :
    dv (ubarSU2 s ell V c * (coarseBondVar s ell T c)⁻¹)
      ≤ (ell : ℝ) * d + Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ) * P) := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  set S := stepBlockOf c.1 s ell
  set w : PeriodicLatticeSite L → ℝ := fun _ => ((ell : ℝ) ^ 3)⁻¹
  set W : PeriodicLatticeSite L → SU2 := fun x => loopVar s ell V c x
  set bnd : ℝ := Real.pi / 2 * (3 * ((ell : ℝ) - 1) * (ell : ℝ) * P)
  have hbnn : 0 ≤ bnd := by
    have h2 : (0 : ℝ) ≤ (ell : ℝ) - 1 := by linarith
    have hpi := Real.pi_pos
    positivity
  have hlog : ∀ x ∈ S, frobNorm (su2Log (W x)) ≤ bnd := by
    intro x hx
    refine le_trans (frobNorm_su2Log_le_pi_div_two (W x)) ?_
    have hg := gammaPath_length_le c.1 x hs hx
    have hgR : ((coarseGammaPath s c.1 x).length : ℝ) ≤ 3 * (ell : ℝ) - 3 := by
      have h1 : ((coarseGammaPath s c.1 x).length : ℝ) ≤ ((3 * (ell - 1) : ℕ) : ℝ) := by
        exact_mod_cast hg
      have h3 : ((3 * (ell - 1) : ℕ) : ℝ) = 3 * (ell : ℝ) - 3 := by
        rw [Nat.cast_mul, Nat.cast_sub hell]; push_cast; ring
      linarith
    have hl : dv (W x) ≤ ((coarseGammaPath s c.1 x).length : ℝ) * ((ell : ℝ) * P) := by
      show dv (loopVar s ell V c x) ≤ _
      rw [loopVar_eq_ladS s ell V c x hx]
      exact ladS_le s V c.2 ell P _ c.1 (hP x hx)
    have hm : ((coarseGammaPath s c.1 x).length : ℝ) * ((ell : ℝ) * P)
        ≤ (3 * (ell : ℝ) - 3) * ((ell : ℝ) * P) :=
      mul_le_mul_of_nonneg_right hgR (by positivity)
    have hW : dv (W x) ≤ 3 * ((ell : ℝ) - 1) * (ell : ℝ) * P := by nlinarith
    have hpi := Real.pi_pos
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  have hE : frobNorm (blockExponent S w W) ≤ bnd :=
    frobNorm_blockExponent_le' S w W bnd (fun _ _ => by positivity)
      (weight_sum_le_one c.1 hs hell) hbnn hlog
  have hexp : dv (su2Exp (blockExponent S w W)) ≤ bnd :=
    le_trans (frobNorm_su2Exp_sub_one_le_uncond (blockExponent_antiHerm S w W)
      (blockExponent_trace S w W)) hE
  have hshape : ubarSU2 s ell V c = su2Exp (blockExponent S w W) * coarseBondVar s ell V c := by
    rw [ubarSU2_eq_blockedLink]; rfl
  have hcb : dv (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹) ≤ (ell : ℝ) * d := by
    have := path_cmp s V T d (List.replicate ell c.2) c.1 hdc
    rw [List.length_replicate] at this; exact this
  have hid : ubarSU2 s ell V c * (coarseBondVar s ell T c)⁻¹
      = su2Exp (blockExponent S w W)
        * (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹) := by
    rw [hshape]; group
  rw [hid]
  have ht := dv_mul (su2Exp (blockExponent S w W))
    (coarseBondVar s ell V c * (coarseBondVar s ell T c)⁻¹)
  linarith

/-- **Reduction for every `ell ≥ 2`.** -/
theorem defect_tower_of_curv (ell : ℕ) (hell : 2 ≤ ell) (U : PeriodicLinkConfiguration SU2 L)
    (q0 C : ℝ) (hq0 : 0 ≤ q0) (hC : 0 ≤ C) (n : ℕ)
    (hP : ∀ l < n, ∀ y ν μ,
      dv (pw (ell ^ l) (ubarTowerSU2 ell U l) y ν μ) ≤ C * ((ell : ℝ) ^ 2) ^ l * q0) :
    ∀ l ≤ n, ∀ c : PeriodicLatticeEdge L,
      dv (ubarTowerSU2 ell U l c * (strT ell U l c)⁻¹)
        ≤ 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ l * q0 := by
  have hell0 : 0 < ell := by omega
  have hl2 : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hpi := Real.pi_pos
  intro l
  induction l with
  | zero =>
      intro _ c
      show dv (U c * (U c)⁻¹) ≤ _
      rw [mul_inv_cancel, dv_one, pow_zero, mul_one]; positivity
  | succ k ih =>
      intro hk c
      have hs : 0 < ell ^ k := pow_pos hell0 k
      set X : ℝ := ((ell : ℝ) ^ 2) ^ k * q0
      have hX : 0 ≤ X := by positivity
      have hstep := defect_step_curv (ell ^ k) ell hs hell0 (ubarTowerSU2 ell U k) (strT ell U k) c
        (3 * Real.pi / 2 * C * X) (C * X) (by positivity)
        (fun b _ => (ih (by omega) b).trans (le_of_eq (by simp only [X]; ring)))
        (fun x _ t _ => (hP k (by omega) t.1 t.2.1 t.2.2).trans (le_of_eq (by simp only [X]; ring)))
      have hsh : ubarTowerSU2 ell U (k + 1) c * (strT ell U (k + 1) c)⁻¹
          = ubarSU2 (ell ^ k) ell (ubarTowerSU2 ell U k) c
            * (coarseBondVar (ell ^ k) ell (strT ell U k) c)⁻¹ := rfl
      rw [hsh]
      refine le_trans hstep ?_
      have hpow : 3 * Real.pi / 2 * C * ((ell : ℝ) ^ 2) ^ (k + 1) * q0
          = 3 * Real.pi / 2 * C * X * (ell : ℝ) ^ 2 := by simp only [X]; ring
      rw [hpow]
      -- ell·(3π/2)CX + (π/2)·3(ell−1)ell·CX = (3π/2)CX·ell²
      exact le_of_eq (by ring)

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.defect_step_curv
#print axioms AdalyFormal.CurvBlock.defect_tower_of_curv

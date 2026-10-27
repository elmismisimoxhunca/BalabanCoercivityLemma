import ASW1
import NB32

/-!
# ASW2 -- NON-VACUITY at a genuinely CURVED background.

`ell = 2, k = 1, Lu = (3,3,3)` (fine torus `8³`).  `U = torusCfg f_ε` with `f_ε = ε` on the single bond `(0, direction 0)` and `0` elsewhere
(the curvature-blocking lane's NB32 shape, with `ε` a parameter instead of `10⁻⁹`):  every fine plaquette containing that bond has defect
`> 0`, so `U` is NOT flat.  `ε := min (10⁻¹³) (r0/100)`.  All of `M0Regime` holds, so `ginv_coercive_M0` applies to a curved `U`.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
noncomputable section
namespace AdalyFormal.AsmM0

open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2 (Cfg)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 torus)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg frobNorm_torus_sub_one)
open AdalyFormal.CurvBlock
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (r0 r0_pos)
open AdalyFormal.Balaban.ClassPropagationUbar (blkConstOf)

abbrev Lu3 : PeriodicLatticeExtent := fun _ => 3

theorem scaleUp_Lu3 : scaleUp 2 1 Lu3 = L8 := rfl

def fE (ε : ℝ) (b : PeriodicLatticeEdge L8) : ℝ := if b = (o8, 0) then ε else 0

def U8 (ε : ℝ) : Cfg (scaleUp 2 1 Lu3) := torusCfg (fE ε)

theorem fE_abs (ε : ℝ) (hε : 0 ≤ ε) (b : PeriodicLatticeEdge L8) : |fE ε b| ≤ ε := by
  unfold fE; split_ifs <;> simp [abs_of_nonneg hε, hε]

theorem U8_link (ε : ℝ) (hε : 0 ≤ ε) (b : PeriodicLatticeEdge L8) : dv (torusCfg (fE ε) b) ≤ Real.sqrt 2 * ε := by
  have := dv_torus_le (fE ε b)
  exact this.trans (mul_le_mul_of_nonneg_left (fE_abs ε hε b) (Real.sqrt_nonneg _))

theorem U8_plaq (ε : ℝ) (hε : 0 ≤ ε) : ∀ y ν μ, dv (pw 1 (torusCfg (fE ε)) y ν μ) ≤ 4 * Real.sqrt 2 * ε := by
  intro y ν μ
  rw [pw_torusCfg]
  refine le_trans (dv_torus_le _) ?_
  have h1 := fE_abs ε hε (y, ν); have h2 := fE_abs ε hε (coarseShift y 1 ν, μ)
  have h3 := fE_abs ε hε (coarseShift y 1 μ, ν); have h4 := fE_abs ε hε (y, μ)
  have : |curlS 1 (fE ε) y ν μ| ≤ 4 * ε := by
    unfold curlS
    obtain ⟨a1, b1⟩ := abs_le.mp h1; obtain ⟨a2, b2⟩ := abs_le.mp h2
    obtain ⟨a3, b3⟩ := abs_le.mp h3; obtain ⟨a4, b4⟩ := abs_le.mp h4
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- the plaquette `(o8; 0, 1)` of the curved witness has positive defect, for every `0 < ε < π`. -/
theorem U8_nonflat (ε : ℝ) (hε : 0 < ε) (hπ : ε < Real.pi) : 0 < dv (pw 1 (torusCfg (fE ε)) o8 0 1) := by
  rw [pw_torusCfg]
  have hc : curlS 1 (fE ε) o8 0 1 = ε := by
    unfold curlS fE
    have e1 : ((coarseShift o8 1 0, (1 : Fin 3)) = (o8, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h; exact absurd (congrArg Prod.snd h) (by decide)
      · intro h; exact h.elim
    have e2 : ((coarseShift o8 1 1, (0 : Fin 3)) = (o8, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h
        have := congrArg (fun p => (p.1 1).val) h
        simp [coarseShift, o8, periodicLatticeShift] at this
      · intro h; exact h.elim
    have e3 : ((o8, (1 : Fin 3)) = (o8, (0 : Fin 3))) = False := by
      apply propext; constructor
      · intro h; exact absurd (congrArg Prod.snd h) (by decide)
      · intro h; exact h.elim
    simp only [e1, e2, e3, if_true, if_false]
    ring
  rw [hc]
  unfold dv
  rw [frobNorm_torus_sub_one]
  apply Real.sqrt_pos.mpr
  have hc1 : Real.cos ε < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le hε
    rwa [Real.cos_zero] at this
  linarith

def epsA : ℝ := min (1 / 10 ^ 13) (r0 / 100)

theorem epsA_pos : 0 < epsA := lt_min (by norm_num) (by have := r0_pos; positivity)
theorem epsA_le1 : epsA ≤ 1 / 10 ^ 13 := min_le_left _ _
theorem epsA_le2 : epsA ≤ r0 / 100 := min_le_right _ _

theorem witness_regime : M0Regime 2 1 Lu3 (U8 epsA) 1 1 (Real.sqrt 2 * epsA) (4 * Real.sqrt 2 * epsA) := by
  have hε := epsA_pos
  have hε1 := epsA_le1
  have hε2 := epsA_le2
  have hr0 := r0_pos
  have hs2 : Real.sqrt 2 ≤ 1.5 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs2' : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hE : Real.sqrt 2 * epsA ≤ 1.5 * epsA := by nlinarith
  have hQ : 4 * Real.sqrt 2 * epsA ≤ 6 * epsA := by nlinarith
  have hρ : rhoM0 2 1 (Real.sqrt 2 * epsA) (4 * Real.sqrt 2 * epsA) ≤ 3e-11 := by
    unfold rhoM0
    push_cast
    have e1 : (2 : ℝ) ^ 1 * (Real.sqrt 2 * epsA + 3 * Real.pi * (2 ^ 1 * (4 * Real.sqrt 2 * epsA)))
        = 2 * (Real.sqrt 2 * epsA) + 12 * Real.pi * (4 * Real.sqrt 2 * epsA) := by ring
    rw [e1]
    nlinarith [mul_nonneg hpi0.le (by nlinarith : 0 ≤ 6 * epsA - 4 * Real.sqrt 2 * epsA)]
  have hρ0 : 0 ≤ rhoM0 2 1 (Real.sqrt 2 * epsA) (4 * Real.sqrt 2 * epsA) := by
    unfold rhoM0; positivity
  refine ⟨le_refl _, one_pos, one_pos, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; show 2 * 2 ^ 1 < (3 + 1) * 2 ^ 1 - 1 + 1; norm_num
  · intro b; exact U8_link epsA hε.le b
  · exact plaq_of_pw_one (torusCfg (fE epsA)) _ (U8_plaq epsA hε.le)
  · push_cast
    nlinarith
  · nlinarith
  · refine hρ.trans ?_
    push_cast; norm_num
  · intro j hj
    have : j = 0 := by omega
    subst this
    simp only [pow_zero, one_mul]
    push_cast
    nlinarith
  · exact Theta_num _ hρ0 hρ

theorem witness_curved : ∃ p : PeriodicLatticePlaquette (scaleUp 2 1 Lu3), 0 < dv (periodicPlaquetteHolonomy (U8 epsA) p) := by
  refine ⟨(o8, ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩), ?_⟩
  have := U8_nonflat epsA epsA_pos (by have := epsA_le1; have := Real.pi_gt_three; linarith)
  exact this

/-- the headline theorem at the curved witness (type inferred from `ginv_coercive_M0`:
`‖x‖² ≤ (2^1)² · KhatM0 2 1 1 ρ · ⟪x, Ginv x⟫`, `ρ = rhoM0 2 1 (√2 ε) (4√2 ε)`). -/
def witness_coercive (Lam : Set (PeriodicLatticeSite Lu3)) (x : ↥(IngredientFamilyR2.bondSupp (SliceCoerc.GF 2 1 Lu3))) :=
  ginv_coercive_M0 2 1 Lu3 (U8 epsA) 1 1 _ _ witness_regime Lam x

#print axioms U8_nonflat
#print axioms witness_regime
#print axioms witness_curved
#print axioms witness_coercive

end AdalyFormal.AsmM0

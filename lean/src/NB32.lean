import NB20
import AB5
/-!
# NB32 -- a NON-FLAT witness satisfying every hypothesis of `curv_tower_na` (non-vacuity)

8×8×8 torus, `ell = 2`, `n = 1`; `U = torusCfg f` with `f = ε` on the single bond `(0, direction 0)` and `0`
elsewhere, `ε = 10⁻⁹`, `q0 = 4√2 ε`.  All hypotheses of `curv_tower_na` hold (`witness_hyps`) and the fine
plaquette `(0; 0, 1)` has strictly positive defect (`witness_nonflat`).

No sorry / native_decide / axioms.
-/
set_option autoImplicit false
noncomputable section
namespace AdalyFormal.CurvBlock
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 torus torus_add)
open AdalyFormal.Balaban.CoarseCurl (coarseShift)
open AdalyFormal.Balaban.AbelianBlockingRate (torusCfg torus_inv frobNorm_torus_sub_one)

abbrev L8 : PeriodicLatticeExtent := fun _ => 7

def o8 : PeriodicLatticeSite L8 := fun _ => 0

def epsW : ℝ := 1 / 1000000000

def fW (b : PeriodicLatticeEdge L8) : ℝ := if b = (o8, 0) then epsW else 0

theorem fW_abs (b : PeriodicLatticeEdge L8) : |fW b| ≤ epsW := by
  unfold fW; split_ifs <;> simp [epsW]

theorem pw_torusCfg (s : ℕ) (f : PeriodicLatticeEdge L8 → ℝ) (y : PeriodicLatticeSite L8) (ν μ : Fin 3) :
    pw s (torusCfg f) y ν μ = torus (curlS s f y ν μ) := by
  unfold pw curlS torusCfg
  rw [torus_inv, torus_inv, ← torus_add, ← torus_add, ← torus_add]
  congr 1
  try ring

theorem witness_h0 : ∀ y ν μ, dv (pw 1 (torusCfg fW) y ν μ) ≤ 4 * Real.sqrt 2 * epsW := by
  intro y ν μ
  rw [pw_torusCfg]
  refine le_trans (dv_torus_le _) ?_
  have h1 := fW_abs (y, ν); have h2 := fW_abs (coarseShift y 1 ν, μ)
  have h3 := fW_abs (coarseShift y 1 μ, ν); have h4 := fW_abs (y, μ)
  have : |curlS 1 fW y ν μ| ≤ 4 * epsW := by
    unfold curlS
    obtain ⟨a1, b1⟩ := abs_le.mp h1; obtain ⟨a2, b2⟩ := abs_le.mp h2
    obtain ⟨a3, b3⟩ := abs_le.mp h3; obtain ⟨a4, b4⟩ := abs_le.mp h4
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

theorem witness_hyps :
    (0 : ℝ) ≤ 4 * Real.sqrt 2 * epsW ∧
    (∀ y ν μ, dv (pw 1 (torusCfg fW) y ν μ) ≤ 4 * Real.sqrt 2 * epsW) ∧
    (∀ ρ, 2 ^ 1 ∣ L8 ρ + 1) ∧ (∀ ρ, 2 * 2 ^ 1 < L8 ρ + 1) ∧
    4000000 * ((2 : ℕ) : ℝ) ^ 2 * ((((2 : ℕ) : ℝ) ^ 2) ^ 1 * (4 * Real.sqrt 2 * epsW)) ≤ 1 := by
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine ⟨by unfold epsW; positivity, witness_h0, fun _ => by show 2 ^ 1 ∣ 7 + 1; decide, fun _ => by show 2 * 2 ^ 1 < 7 + 1; decide, ?_⟩
  unfold epsW; push_cast; nlinarith [Real.sqrt_nonneg 2]

theorem witness_nonflat : 0 < dv (pw 1 (torusCfg fW) o8 0 1) := by
  rw [pw_torusCfg]
  have hc : curlS 1 fW o8 0 1 = epsW := by
    unfold curlS fW
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
  have hc1 : Real.cos epsW < 1 := by
    have h0 : 0 < epsW := by unfold epsW; norm_num
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
      (by have := Real.pi_gt_three; unfold epsW; linarith) h0
    rwa [Real.cos_zero] at this
  linarith

end AdalyFormal.CurvBlock

#print axioms AdalyFormal.CurvBlock.witness_hyps
#print axioms AdalyFormal.CurvBlock.witness_nonflat

import BLC7

/-!
# BLC8 -- the ladders of the axial gauge and the `j = 0` ball chart (m2_ballcharts, 2026-10-15)

`V ν p = U^{axg}(ι_w p, ν)`.  `V 2 ≡ 1`; `V 1 = 1` on `p₂ = 0`; `V 0 = 1` on `p₁ = p₂ = 0` (`axG_e*`).  A plaquette with two
trivial sides gives `|V μ b − V μ (b + e_ν)| = |plq − 1| ≤ 4X` (`rung`).  Ladders: `|V 1 p − 1| ≤ |p₂| 4X`,
`|V 0 p − 1| ≤ (|p₁| + |p₂|) 4X`.  `ball_chart_zero`: `GChart` on `Ball w r` at `(56 M X, 56 M X)`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem frob_one_sub_one : frobNorm (((1 : SU2) : M2) - 1) = 0 := by
  simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]

/-- the axial-gauge ladders, given a plaquette bound `B` on the coordinate `ℓ¹` ball. -/
theorem axial_bound {U : LinkCfg L} {w : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hPB : ∀ b : Z3, ∀ μ ν : Fin 3, μ < ν → b ∈ Bz r → b + ev μ ∈ Bz r → b + ev ν ∈ Bz r → b + ev μ + ev ν ∈ Bz r →
      frobNorm (((plq U (axg U w r) (iota w b) μ ν : SU2) : M2) - 1) ≤ B) :
    ∀ p ν, p ∈ Bz r → p + ev ν ∈ Bz r →
      frobNorm (((periodicGaugeTransform (axg U w r) U (iota w p, ν) : SU2) : M2) - 1) ≤ r * B := by
  set V : Fin 3 → Z3 → SU2 := fun ν p => periodicGaugeTransform (axg U w r) U (iota w p, ν) with hV
  have box : ∀ p, p ∈ Bz r → p ∈ Box r := fun p hp => Bz_sub_box hp
  -- trivial sides
  have A2 : ∀ p, p ∈ Bz r → p + ev 2 ∈ Bz r → V 2 p = 1 := by
    intro p hp hp2
    simp only [hV]; rw [axg_V hL (box p hp) (box _ hp2), axG_e2]; group
  have A1 : ∀ p, p 2 = 0 → p ∈ Bz r → p + ev 1 ∈ Bz r → V 1 p = 1 := by
    intro p h2 hp hp1
    simp only [hV]; rw [axg_V hL (box p hp) (box _ hp1), axG_e1 U w p h2]; group
  have A0 : ∀ p, p 1 = 0 → p 2 = 0 → p ∈ Bz r → p + ev 0 ∈ Bz r → V 0 p = 1 := by
    intro p h1 h2 hp hp0
    simp only [hV]; rw [axg_V hL (box p hp) (box _ hp0), axG_e0 U w p h1 h2]; group
  -- plaquette in `V` form
  have hplq : ∀ b μ ν, plq U (axg U w r) (iota w b) μ ν = V μ b * V ν (b + ev μ) * (V μ (b + ev ν))⁻¹ * (V ν b)⁻¹ := by
    intro b μ ν
    simp only [plq, hV, iota_shift]
  -- a rung: two trivial sides
  have rung : ∀ b μ ν, μ < ν → b ∈ Bz r → b + ev μ ∈ Bz r → b + ev ν ∈ Bz r → b + ev μ + ev ν ∈ Bz r →
      V ν b = 1 → V ν (b + ev μ) = 1 →
      frobNorm (((V μ b : SU2) : M2) - (V μ (b + ev ν) : SU2)) ≤ B := by
    intro b μ ν hμν h0 h1 h2 h3 t0 t1
    have := hPB b μ ν hμν h0 h1 h2 h3
    rw [hplq, t0, t1, mul_one, inv_one, mul_one, su2_mul_inv_sub_one] at this
    exact this
  have mem : ∀ p : Z3, p ∈ Bz r ↔ (p 0).natAbs + (p 1).natAbs + (p 2).natAbs ≤ r := fun p => Iff.rfl
  have c0 : ∀ (p : Z3) (i : Fin 3), (p + ev i) i = p i + 1 := fun p i => by simp [ev]
  -- ladder for ν = 1
  have L1 : ∀ n : ℕ, ∀ p, (p 2).natAbs = n → p ∈ Bz r → p + ev 1 ∈ Bz r →
      frobNorm (((V 1 p : SU2) : M2) - 1) ≤ n * B := by
    intro n
    induction n with
    | zero =>
      intro p hn hp hp1
      rw [A1 p (by omega) hp hp1, frob_one_sub_one]; simp
    | succ n ih =>
      intro p hn hp hp1
      rw [mem] at hp hp1
      simp [ev] at hp1
      rcases lt_or_gt_of_ne (show p 2 ≠ 0 by omega) with hneg | hpos
      · -- p₂ < 0 : step up to p + e₂
        set p' := p + ev 2 with hp'
        have q0 : p' ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have q1 : p' + ev 1 ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have hn' : (p' 2).natAbs = n := by simp [hp', ev]; omega
        have e : p + ev 1 + ev 2 = p' + ev 1 := by rw [hp']; abel
        have hr := rung p 1 2 (by decide) ((mem p).mpr hp) (by rw [mem]; simp [ev]; omega) q0 (by rw [e]; exact q1)
          (A2 p ((mem p).mpr hp) q0) (A2 _ (by rw [mem]; simp [ev]; omega) (by rw [e]; exact q1))
        have := ih p' hn' q0 q1
        have t := frobNorm_sub_le' ((V 1 p : SU2) : M2) ((V 1 p' : SU2) : M2) 1
        push_cast at this ⊢; linarith
      · -- p₂ > 0 : step down to b = p - e₂
        set b := p - ev 2 with hb
        have q0 : b ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have q1 : b + ev 1 ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have hn' : (b 2).natAbs = n := by simp [hb, ev]; omega
        have e2 : b + ev 2 = p := by rw [hb]; abel
        have e12 : b + ev 1 + ev 2 = p + ev 1 := by rw [hb]; abel
        have hr := rung b 1 2 (by decide) q0 q1 (by rw [e2]; exact (mem p).mpr hp)
          (by rw [e12]; rw [mem]; simp [ev]; omega)
          (A2 b q0 (by rw [e2]; exact (mem p).mpr hp)) (A2 _ q1 (by rw [e12]; rw [mem]; simp [ev]; omega))
        rw [e2] at hr
        have := ih b hn' q0 q1
        have t := frobNorm_sub_le' ((V 1 p : SU2) : M2) ((V 1 b : SU2) : M2) 1
        rw [frobNorm_sub_comm] at hr
        push_cast at this ⊢; linarith
  -- ladder for ν = 0 on the plane p₂ = 0
  have L0a : ∀ n : ℕ, ∀ p, p 2 = 0 → (p 1).natAbs = n → p ∈ Bz r → p + ev 0 ∈ Bz r →
      frobNorm (((V 0 p : SU2) : M2) - 1) ≤ n * B := by
    intro n
    induction n with
    | zero =>
      intro p h2 hn hp hp0
      rw [A0 p (by omega) h2 hp hp0, frob_one_sub_one]; simp
    | succ n ih =>
      intro p h2 hn hp hp0
      rw [mem] at hp hp0
      simp [ev] at hp0
      rcases lt_or_gt_of_ne (show p 1 ≠ 0 by omega) with hneg | hpos
      · set p' := p + ev 1 with hp'
        have q0 : p' ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have q1 : p' + ev 0 ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have hn' : (p' 1).natAbs = n := by simp [hp', ev]; omega
        have h2' : p' 2 = 0 := by simp [hp', ev, h2]
        have e : p + ev 0 + ev 1 = p' + ev 0 := by rw [hp']; abel
        have hp0' : p + ev 0 ∈ Bz r := by rw [mem]; simp [ev]; omega
        have hr := rung p 0 1 (by decide) ((mem p).mpr hp) hp0' q0 (by rw [e]; exact q1)
          (A1 p h2 ((mem p).mpr hp) q0) (A1 _ (by simp [ev, h2]) hp0' (by rw [e]; exact q1))
        have := ih p' h2' hn' q0 q1
        have t := frobNorm_sub_le' ((V 0 p : SU2) : M2) ((V 0 p' : SU2) : M2) 1
        push_cast at this ⊢; linarith
      · set b := p - ev 1 with hb
        have q0 : b ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have q1 : b + ev 0 ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have hn' : (b 1).natAbs = n := by simp [hb, ev]; omega
        have h2' : b 2 = 0 := by simp [hb, ev, h2]
        have e1 : b + ev 1 = p := by rw [hb]; abel
        have e01 : b + ev 0 + ev 1 = p + ev 0 := by rw [hb]; abel
        have hp0' : p + ev 0 ∈ Bz r := by rw [mem]; simp [ev]; omega
        have hr := rung b 0 1 (by decide) q0 q1 (by rw [e1]; exact (mem p).mpr hp) (by rw [e01]; exact hp0')
          (A1 b h2' q0 (by rw [e1]; exact (mem p).mpr hp))
          (A1 _ (by simp [hb, ev, h2]) q1 (by rw [e01]; exact hp0'))
        rw [e1] at hr
        have := ih b h2' hn' q0 q1
        have t := frobNorm_sub_le' ((V 0 p : SU2) : M2) ((V 0 b : SU2) : M2) 1
        rw [frobNorm_sub_comm] at hr
        push_cast at this ⊢; linarith
  -- ladder for ν = 0 in general
  have L0 : ∀ n : ℕ, ∀ p, (p 2).natAbs = n → p ∈ Bz r → p + ev 0 ∈ Bz r →
      frobNorm (((V 0 p : SU2) : M2) - 1) ≤ ((p 1).natAbs + n) * B := by
    intro n
    induction n with
    | zero =>
      intro p hn hp hp0
      have := L0a _ p (by omega) rfl hp hp0
      simpa using this
    | succ n ih =>
      intro p hn hp hp0
      rw [mem] at hp hp0
      simp [ev] at hp0
      rcases lt_or_gt_of_ne (show p 2 ≠ 0 by omega) with hneg | hpos
      · set p' := p + ev 2 with hp'
        have q0 : p' ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have q1 : p' + ev 0 ∈ Bz r := by rw [mem]; simp [hp', ev]; omega
        have hn' : (p' 2).natAbs = n := by simp [hp', ev]; omega
        have h1' : (p' 1).natAbs = (p 1).natAbs := by simp [hp', ev]
        have e : p + ev 0 + ev 2 = p' + ev 0 := by rw [hp']; abel
        have hp0' : p + ev 0 ∈ Bz r := by rw [mem]; simp [ev]; omega
        have hr := rung p 0 2 (by decide) ((mem p).mpr hp) hp0' q0 (by rw [e]; exact q1)
          (A2 p ((mem p).mpr hp) q0) (A2 _ hp0' (by rw [e]; exact q1))
        have := ih p' hn' q0 q1
        rw [h1'] at this
        have t := frobNorm_sub_le' ((V 0 p : SU2) : M2) ((V 0 p' : SU2) : M2) 1
        push_cast at this ⊢; linarith
      · set b := p - ev 2 with hb
        have q0 : b ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have q1 : b + ev 0 ∈ Bz r := by rw [mem]; simp [hb, ev]; omega
        have hn' : (b 2).natAbs = n := by simp [hb, ev]; omega
        have h1' : (b 1).natAbs = (p 1).natAbs := by simp [hb, ev]
        have e2 : b + ev 2 = p := by rw [hb]; abel
        have e02 : b + ev 0 + ev 2 = p + ev 0 := by rw [hb]; abel
        have hp0' : p + ev 0 ∈ Bz r := by rw [mem]; simp [ev]; omega
        have hr := rung b 0 2 (by decide) q0 q1 (by rw [e2]; exact (mem p).mpr hp) (by rw [e02]; exact hp0')
          (A2 b q0 (by rw [e2]; exact (mem p).mpr hp)) (A2 _ q1 (by rw [e02]; exact hp0'))
        rw [e2] at hr
        have := ih b hn' q0 q1
        rw [h1'] at this
        have t := frobNorm_sub_le' ((V 0 p : SU2) : M2) ((V 0 b : SU2) : M2) 1
        rw [frobNorm_sub_comm] at hr
        push_cast at this ⊢; linarith
  -- assemble
  intro p ν hp hpν
  have hp' := (mem p).mp hp
  have hrB : ∀ m : ℕ, m ≤ r → (m : ℝ) * B ≤ r * B := fun m hm =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hB0
  fin_cases ν
  · have := L0 _ p rfl hp hpν
    exact this.trans (by have := hrB ((p 1).natAbs + (p 2).natAbs) (by omega); push_cast at this ⊢; linarith)
  · have := L1 _ p rfl hp hpν
    exact this.trans (hrB _ (by omega))
  · have := A2 p hp hpν
    show frobNorm (((V 2 p : SU2) : M2) - 1) ≤ r * B
    rw [this, frob_one_sub_one]; positivity

/-- **the ball chart at `j = 0`**. -/
theorem ball_chart_zero {ell M R k : ℕ} {S : Tower L} (hcov : CoversOm0p ell M 12 k S) (hell : 0 < ell)
    {w : PeriodicLatticeSite L} {r : ℕ} (hr7 : r ≤ 7 * M) (hnw : ∀ σ : Fin 3, 2 * r + 2 ≤ L σ + 1)
    (hin : ∀ x ∈ Ball w r, x ∈ S.Om 0)
    {α₀ η : ℝ} (hη : 0 < η) (hα : 0 ≤ α₀) {U : LinkCfg L} (hP : PerCubeRegular2 ell M 12 k S α₀ η U)
    (hX : (12 : ℝ) * M * α₀ ≤ 1 / 2) :
    ∃ g : PeriodicLatticeSite L → SU2, GChart U g (Ball w r)
      (56 * M * ((12 : ℝ) * M * α₀)) (56 * M * ((12 : ℝ) * M * α₀)) := by
  have hL : ∀ μ, 2 * r + 1 < L μ + 1 := fun μ => by have := hnw μ; omega
  set X : ℝ := (12 : ℝ) * M * α₀ with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hPB : ∀ b : Z3, ∀ μ ν : Fin 3, μ < ν → b ∈ Bz r → b + ev μ ∈ Bz r → b + ev ν ∈ Bz r → b + ev μ + ev ν ∈ Bz r →
      frobNorm (((plq U (axg U w r) (iota w b) μ ν : SU2) : M2) - 1) ≤ 4 * X := by
    intro b μ ν hμν h0 h1 h2 h3
    have hc : periodicLatticeShift (periodicLatticeShift (iota w b) μ) ν
        = periodicLatticeShift (periodicLatticeShift (iota w b) ν) μ := by
      rw [iota_shift2, iota_shift2, add_right_comm]
    exact plq_class (R := R) hcov hell hη hα hP hX hμν (hin _ (iota_mem_ball h0))
      (by rw [iota_shift]; exact hin _ (iota_mem_ball h1)) (by rw [iota_shift]; exact hin _ (iota_mem_ball h2))
      (by rw [iota_shift2]; exact hin _ (iota_mem_ball h3)) hc _
  have hb := axial_bound (U := U) (w := w) hL (by positivity) hPB
  have hz : ZCh U (axg U w r) w (Bz r) (fun _ => r * (4 * X)) (fun _ => 2 * (r * (4 * X))) := by
    refine ⟨fun p ν hp hpν => hb p ν hp hpν, fun p μ ν h0 h1 h2 h3 => ?_⟩
    have a := hb (p + ev μ) ν h2 h3
    have b := hb p ν h0 h1
    have t := frobNorm_sub_le' ((periodicGaugeTransform (axg U w r) U (iota w (p + ev μ), ν) : SU2) : M2) 1
      ((periodicGaugeTransform (axg U w r) U (iota w p, ν) : SU2) : M2)
    rw [frobNorm_sub_comm 1] at t
    show _ ≤ 2 * (r * (4 * X)); linarith
  have hGs := gchart_sub_of_zch (v := w) hL (S := Bz r) Bz_sub_box (P := fun _ => True) (T := Bz r)
    (fun p hp _ => hp) hz
  refine ⟨axg U w r, hGs.mono (fun x hx => ⟨ball_sub_liftL1 w r hx, trivial⟩) ?_ ?_⟩
  · have : (r : ℝ) ≤ 7 * M := by exact_mod_cast hr7
    nlinarith
  · have : (r : ℝ) ≤ 7 * M := by exact_mod_cast hr7
    nlinarith

end AdalyFormal.M2BallCharts

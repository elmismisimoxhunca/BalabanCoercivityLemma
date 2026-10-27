import UW2

/-!
# UW3 -- the slowed velocity profile `Φ(t, x) = ζ(t/w) · t · P_{t-1}(x)` (lane unif_20261016)

`zeta w t = 1 − stepS((t − w)/w)` (1 for `t ≤ w`, 0 for `t ≥ 2w`), `cf w t = zeta w t · t`;
`cf_d1 : |cf(t+1) − cf t| ≤ 21`, `cf_d2 : |cf(t+2) − 2cf(t+1) + cf t| ≤ 84/w`, `cf_le : cf t ≤ t`, `cf_le_2w : cf t ≤ 2w`.
`Phi w P t x = cf w t • P (t − 1) x` for a radius-indexed family `P` with the bounds of `UW2` (`PFam`):
first differences in `t` (`≤ 21 VB + 8w D`), in the plane (`≤ 2w D`), second differences `tt` (`≤ 84 VB / w + 186 D`),
mixed (`≤ 29 D`), plane-plane (`≤ 2 D`).  Reusable.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.M2Glue2 (stepS stepS_of_nonpos stepS_of_one_le stepS_mem stepS_lip stepS_second frobNorm_sub_le')
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)

noncomputable def zeta (w : ℕ) (t : ℕ) : ℝ := 1 - stepS (((t : ℝ) - w) / w)

noncomputable def cf (w t : ℕ) : ℝ := zeta w t * t

section prof
variable {w : ℕ} (hw : 1 ≤ w)
include hw

theorem zeta_mem (t : ℕ) : 0 ≤ zeta w t ∧ zeta w t ≤ 1 := by
  have := stepS_mem (((t : ℝ) - w) / w); unfold zeta; constructor <;> linarith [this.1, this.2]

theorem zeta_of_le {t : ℕ} (ht : t ≤ w) : zeta w t = 1 := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have htw : (t : ℝ) ≤ w := by exact_mod_cast ht
  have h : ((t : ℝ) - w) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
  unfold zeta
  simp only [stepS_of_nonpos h, sub_zero]

theorem zeta_of_ge {t : ℕ} (ht : 2 * w ≤ t) : zeta w t = 0 := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have htw : (2 * w : ℝ) ≤ t := by exact_mod_cast ht
  have h : 1 ≤ ((t : ℝ) - w) / w := by rw [le_div_iff₀ hw0]; linarith
  unfold zeta
  simp only [stepS_of_one_le h, sub_self]

theorem cf_nonneg (t : ℕ) : 0 ≤ cf w t := by unfold cf; have := (zeta_mem hw t).1; positivity

theorem cf_le (t : ℕ) : cf w t ≤ t := by
  unfold cf; have := (zeta_mem hw t).2; have : (0 : ℝ) ≤ t := by positivity
  nlinarith

theorem cf_le_2w (t : ℕ) : cf w t ≤ 2 * w := by
  rcases le_or_gt (2 * w) t with h | h
  · unfold cf; rw [zeta_of_ge hw h, zero_mul]; positivity
  · have h1 := cf_le hw t
    have h2 : (t : ℝ) ≤ 2 * w := by exact_mod_cast h.le
    linarith

theorem zeta_d1 (t : ℕ) : |zeta w (t + 1) - zeta w t| ≤ 10 / w := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  unfold zeta
  have := stepS_lip (((t : ℝ) - w) / w) ((((t + 1 : ℕ) : ℝ) - w) / w)
  have e : (((t + 1 : ℕ) : ℝ) - w) / w - (((t : ℝ) - w) / w) = 1 / w := by push_cast; field_simp; ring
  rw [e, abs_of_pos (one_div_pos.mpr hw0)] at this
  rw [show 1 - stepS ((((t + 1 : ℕ) : ℝ) - w) / w) - (1 - stepS (((t : ℝ) - w) / w))
      = -(stepS ((((t + 1 : ℕ) : ℝ) - w) / w) - stepS (((t : ℝ) - w) / w)) by ring, abs_neg]
  refine this.trans ?_
  rw [div_pow, one_pow]
  have : 8 * (1 / (w : ℝ) ^ 2) ≤ 8 / w := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hw0]; nlinarith
  have : 2 * (1 / (w : ℝ)) = 2 / w := by ring
  have : 2 / (w : ℝ) + 8 / w = 10 / w := by ring
  linarith

theorem zeta_d2 (t : ℕ) : |zeta w (t + 2) - zeta w (t + 1) - (zeta w (t + 1) - zeta w t)| ≤ 32 / w ^ 2 := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  unfold zeta
  have := stepS_second (((t : ℝ) - w) / w) ((((t + 1 : ℕ) : ℝ) - w) / w) ((((t + 1 : ℕ) : ℝ) - w) / w)
    ((((t + 2 : ℕ) : ℝ) - w) / w)
  have e0 : ((((t + 2 : ℕ) : ℝ) - w) / w) - ((((t + 1 : ℕ) : ℝ) - w) / w) - ((((t + 1 : ℕ) : ℝ) - w) / w)
      + (((t : ℝ) - w) / w) = 0 := by push_cast; field_simp; ring
  have e1 : ((((t + 1 : ℕ) : ℝ) - w) / w) - (((t : ℝ) - w) / w) = 1 / w := by push_cast; field_simp; ring
  have e2 : ((((t + 2 : ℕ) : ℝ) - w) / w) - ((((t + 1 : ℕ) : ℝ) - w) / w) = 1 / w := by push_cast; field_simp; ring
  rw [e0, e1, e2, abs_zero, abs_of_pos (one_div_pos.mpr hw0)] at this
  rw [show 1 - stepS ((((t + 2 : ℕ) : ℝ) - w) / w) - (1 - stepS ((((t + 1 : ℕ) : ℝ) - w) / w))
      - (1 - stepS ((((t + 1 : ℕ) : ℝ) - w) / w) - (1 - stepS (((t : ℝ) - w) / w)))
      = -(stepS ((((t + 2 : ℕ) : ℝ) - w) / w) - stepS ((((t + 1 : ℕ) : ℝ) - w) / w)
        - stepS ((((t + 1 : ℕ) : ℝ) - w) / w) + stepS (((t : ℝ) - w) / w)) by ring, abs_neg]
  refine this.trans (le_of_eq ?_)
  field_simp; ring

theorem cf_d1 (t : ℕ) : |cf w (t + 1) - cf w t| ≤ 21 := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  rcases le_or_gt (2 * w) t with h | h
  · unfold cf; rw [zeta_of_ge hw h, zeta_of_ge hw (by omega)]; simp
  · unfold cf
    have hz := zeta_d1 hw t
    have hm := zeta_mem hw (t + 1)
    have ht : (t : ℝ) ≤ 2 * w := by exact_mod_cast h.le
    have e : zeta w (t + 1) * ((t + 1 : ℕ) : ℝ) - zeta w t * t = zeta w (t + 1) + (zeta w (t + 1) - zeta w t) * t := by
      push_cast; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hm.1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t)]
    have : |zeta w (t + 1) - zeta w t| * t ≤ 10 / w * (2 * w) := by
      apply mul_le_mul hz ht (by positivity) (by positivity)
    have : 10 / (w : ℝ) * (2 * w) = 20 := by field_simp; ring
    linarith [hm.2]

theorem cf_d2 (t : ℕ) : |cf w (t + 2) - cf w (t + 1) - (cf w (t + 1) - cf w t)| ≤ 84 / w := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rcases le_or_gt (2 * w) t with h | h
  · unfold cf; rw [zeta_of_ge hw h, zeta_of_ge hw (by omega), zeta_of_ge hw (by omega)]; simp; positivity
  · unfold cf
    have h2 := zeta_d2 hw t
    have h1 := zeta_d1 hw (t + 1)
    have ht : (t : ℝ) ≤ 2 * w := by exact_mod_cast h.le
    have e : zeta w (t + 2) * ((t + 2 : ℕ) : ℝ) - zeta w (t + 1) * ((t + 1 : ℕ) : ℝ)
        - (zeta w (t + 1) * ((t + 1 : ℕ) : ℝ) - zeta w t * t)
        = (zeta w (t + 2) - zeta w (t + 1) - (zeta w (t + 1) - zeta w t)) * t + 2 * (zeta w (t + 2) - zeta w (t + 1)) := by
      push_cast; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have a : |zeta w (t + 2) - zeta w (t + 1) - (zeta w (t + 1) - zeta w t)| * t ≤ 32 / w ^ 2 * (2 * w) :=
      mul_le_mul h2 ht (by positivity) (by positivity)
    have b : (32 : ℝ) / w ^ 2 * (2 * w) = 64 / w := by field_simp; ring
    have c : 2 * |zeta w (t + 1 + 1) - zeta w (t + 1)| ≤ 2 * (10 / w) := by linarith
    rw [show t + 1 + 1 = t + 2 by ring] at c
    have : (64 : ℝ) / w + 2 * (10 / w) = 84 / w := by ring
    linarith

end prof

/-! ## the profile -/

/-- bounds of a radius-indexed plane family, as provided by `UW2` (`τ₁ τ₂` the plane directions). -/
structure PFam (P : ℕ → Z3 → M2) (τ₁ τ₂ : Fin 3) (VB D : ℝ) : Prop where
  sup : ∀ n x, frobNorm (P n x) ≤ VB
  d1 : ∀ n x μ, (μ = τ₁ ∨ μ = τ₂) → frobNorm (P n (x + ev μ) - P n x) ≤ D
  dd : ∀ n x μ ν, (μ = τ₁ ∨ μ = τ₂) → (ν = τ₁ ∨ ν = τ₂) →
    frobNorm (P n (x + ev μ + ev ν) - P n (x + ev μ) - P n (x + ev ν) + P n x) ≤ 2 * D / (2 * n + 1)
  step : ∀ n x, frobNorm (P (n + 1) x - P n x) ≤ 4 * D
  step_d : ∀ n x μ, (μ = τ₁ ∨ μ = τ₂) →
    frobNorm ((P (n + 1) (x + ev μ) - P n (x + ev μ)) - (P (n + 1) x - P n x)) ≤ 8 * D / (2 * n + 1)
  step2 : ∀ n x, frobNorm ((P (n + 2) x - P (n + 1) x) - (P (n + 1) x - P n x)) ≤ 36 * D / (2 * n + 3)

/-- `UW2` gives `PFam` for plane averages of a field with plane differences `≤ D` and `|f| ≤ VB`. -/
theorem pfam_P2 {τ₁ τ₂ : Fin 3} {f : Z3 → M2} {VB D : ℝ} (hsup : SupB f VB) (h1 : D1 τ₁ f D) (h2 : D1 τ₂ f D)
    (hD : 0 ≤ D) : PFam (fun n => P2 τ₁ τ₂ n f) τ₁ τ₂ VB D where
  sup := fun n x => p2_sup hsup x
  d1 := fun n x μ hμ => by rcases hμ with rfl | rfl <;> [exact p2_d1 (D1v_of_D1 h1) x; exact p2_d1 (D1v_of_D1 h2) x]
  dd := fun n x μ ν hμ hν => by
    rcases hν with rfl | rfl
    · exact p2_dd h1 h2 (D1v_of_D1 h1) μ hμ x
    · exact p2_dd h1 h2 (D1v_of_D1 h2) μ hμ x
  step := fun n x => p2_step h1 h2 hD x
  step_d := fun n x μ hμ => p2_step_d h1 h2 hD μ hμ x
  step2 := fun n x => p2_step2 h1 h2 hD x

/-- the profile `Φ(t, x) = cf(t) · P_{t−1}(x)`. -/
noncomputable def Phi (w : ℕ) (P : ℕ → Z3 → M2) (t : ℕ) (x : Z3) : M2 := cf w t • P (t - 1) x

section phi
variable {w : ℕ} (hw : 1 ≤ w) {P : ℕ → Z3 → M2} {τ₁ τ₂ : Fin 3} {VB D : ℝ} (hP : PFam P τ₁ τ₂ VB D)
  (hVB : 0 ≤ VB) (hD : 0 ≤ D)
include hw hP hVB hD

theorem phi_zero (x : Z3) : Phi w P 0 x = 0 := by simp [Phi, cf]

theorem phi_one (x : Z3) : Phi w P 1 x = P 0 x := by
  simp only [Phi, cf, Nat.sub_self]
  rw [zeta_of_le hw hw]; simp

theorem phi_dt (t : ℕ) (x : Z3) : frobNorm (Phi w P (t + 1) x - Phi w P t x) ≤ 21 * VB + 8 * w * D := by
  simp only [Phi]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp only [zero_add, Nat.sub_self, cf, Nat.cast_zero, mul_zero, zero_smul, sub_zero]
    rw [frobNorm_smul]
    have := hP.sup 0 x
    have hz := zeta_mem hw 1
    rw [abs_of_nonneg (by have := hz.1; push_cast; positivity)]
    push_cast
    nlinarith [hz.2, frobNorm_nonneg (P 0 x)]
  · have e : t + 1 - 1 = (t - 1) + 1 := by omega
    rw [e]
    have l := AdalyFormal.M2Glue2.leib_one (cf w t) (cf w (t + 1)) (P (t - 1) x) (P (t - 1 + 1) x)
    refine l.trans ?_
    have a := mul_le_mul (cf_d1 hw t) (hP.sup (t - 1 + 1) x) (frobNorm_nonneg _) (by norm_num)
    have b := mul_le_mul (le_of_eq (abs_of_nonneg (cf_nonneg hw t))) (hP.step (t - 1) x) (frobNorm_nonneg _)
      (cf_nonneg hw t)
    have c : cf w t * (4 * D) ≤ 2 * w * (4 * D) := mul_le_mul_of_nonneg_right (cf_le_2w hw t) (by positivity)
    nlinarith

theorem phi_dx (t : ℕ) (x : Z3) (μ : Fin 3) (hμ : μ = τ₁ ∨ μ = τ₂) :
    frobNorm (Phi w P t (x + ev μ) - Phi w P t x) ≤ 2 * w * D := by
  simp only [Phi]; rw [← smul_sub, frobNorm_smul, abs_of_nonneg (cf_nonneg hw t)]
  exact mul_le_mul (cf_le_2w hw t) (hP.d1 _ x μ hμ) (frobNorm_nonneg _) (by positivity)

theorem phi_dxx (t : ℕ) (x : Z3) (μ ν : Fin 3) (hμ : μ = τ₁ ∨ μ = τ₂) (hν : ν = τ₁ ∨ ν = τ₂) :
    frobNorm (Phi w P t (x + ev μ + ev ν) - Phi w P t (x + ev μ) - Phi w P t (x + ev ν) + Phi w P t x) ≤ 2 * D := by
  simp only [Phi]
  rw [show cf w t • P (t - 1) (x + ev μ + ev ν) - cf w t • P (t - 1) (x + ev μ) - cf w t • P (t - 1) (x + ev ν)
      + cf w t • P (t - 1) x = cf w t • (P (t - 1) (x + ev μ + ev ν) - P (t - 1) (x + ev μ) - P (t - 1) (x + ev ν)
      + P (t - 1) x) by module, frobNorm_smul, abs_of_nonneg (cf_nonneg hw t)]
  have h := hP.dd (t - 1) x μ ν hμ hν
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; simp [cf]; positivity
  · have hct := cf_le hw t
    have hn : (2 * ((t - 1 : ℕ) : ℝ) + 1) = 2 * t - 1 := by
      rw [Nat.cast_sub h0]; push_cast; ring
    rw [hn] at h
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast h0
    calc cf w t * frobNorm _ ≤ t * (2 * D / (2 * t - 1)) :=
          mul_le_mul hct h (frobNorm_nonneg _) (by positivity)
      _ ≤ 2 * D := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith

theorem phi_dtx (t : ℕ) (x : Z3) (μ : Fin 3) (hμ : μ = τ₁ ∨ μ = τ₂) :
    frobNorm ((Phi w P (t + 1) (x + ev μ) - Phi w P t (x + ev μ)) - (Phi w P (t + 1) x - Phi w P t x)) ≤ 29 * D := by
  simp only [Phi]
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    simp only [zero_add, Nat.sub_self, cf, Nat.cast_zero, mul_zero, zero_smul, sub_zero]
    rw [← smul_sub, frobNorm_smul]
    have hz := zeta_mem hw 1
    have := hP.d1 0 x μ hμ
    rw [abs_of_nonneg (by have := hz.1; push_cast; positivity)]
    push_cast
    nlinarith [hz.2, frobNorm_nonneg (P 0 (x + ev μ) - P 0 x)]
  · have e : t + 1 - 1 = (t - 1) + 1 := by omega
    rw [e]
    set m := t - 1
    have id : (cf w (t + 1) • P (m + 1) (x + ev μ) - cf w t • P m (x + ev μ)) - (cf w (t + 1) • P (m + 1) x - cf w t • P m x)
        = (cf w (t + 1) - cf w t) • (P (m + 1) (x + ev μ) - P (m + 1) x)
          + cf w t • ((P (m + 1) (x + ev μ) - P m (x + ev μ)) - (P (m + 1) x - P m x)) := by module
    rw [id]
    refine (frobNorm_add_le _ _).trans ?_
    rw [frobNorm_smul, frobNorm_smul, abs_of_nonneg (cf_nonneg hw t)]
    have a := mul_le_mul (cf_d1 hw t) (hP.d1 (m + 1) x μ hμ) (frobNorm_nonneg _) (by norm_num)
    have hb := hP.step_d m x μ hμ
    have hn : (2 * (m : ℝ) + 1) = 2 * t - 1 := by simp only [m]; rw [Nat.cast_sub h0]; push_cast; ring
    rw [hn] at hb
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast h0
    have b : cf w t * frobNorm ((P (m + 1) (x + ev μ) - P m (x + ev μ)) - (P (m + 1) x - P m x)) ≤ 8 * D := by
      calc _ ≤ t * (8 * D / (2 * t - 1)) := mul_le_mul (cf_le hw t) hb (frobNorm_nonneg _) (by positivity)
        _ ≤ 8 * D := by rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    linarith

theorem phi_dtt (t : ℕ) (x : Z3) :
    frobNorm ((Phi w P (t + 2) x - Phi w P (t + 1) x) - (Phi w P (t + 1) x - Phi w P t x)) ≤ 84 * VB / w + 186 * D := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
  simp only [Phi]
  -- c2 P_{t+1} − 2 c1 P_t + c0 P_{t−1} with indices (nat sub)
  set p2 := P (t + 2 - 1) x
  set p1 := P (t + 1 - 1) x
  set p0 := P (t - 1) x
  have id : (cf w (t + 2) • p2 - cf w (t + 1) • p1) - (cf w (t + 1) • p1 - cf w t • p0)
      = (cf w (t + 2) - cf w (t + 1) - (cf w (t + 1) - cf w t)) • p2 + (2 * (cf w (t + 1) - cf w t)) • (p2 - p1)
        + cf w t • ((p2 - p1) - (p1 - p0)) := by module
  rw [id]
  have t1 := frobNorm_add_le ((cf w (t + 2) - cf w (t + 1) - (cf w (t + 1) - cf w t)) • p2
    + (2 * (cf w (t + 1) - cf w t)) • (p2 - p1)) (cf w t • ((p2 - p1) - (p1 - p0)))
  have t2 := frobNorm_add_le ((cf w (t + 2) - cf w (t + 1) - (cf w (t + 1) - cf w t)) • p2)
    ((2 * (cf w (t + 1) - cf w t)) • (p2 - p1))
  rw [frobNorm_smul, frobNorm_smul] at t2
  rw [frobNorm_smul, abs_of_nonneg (cf_nonneg hw t)] at t1
  have a : |cf w (t + 2) - cf w (t + 1) - (cf w (t + 1) - cf w t)| * frobNorm p2 ≤ 84 / w * VB :=
    mul_le_mul (cf_d2 hw t) (hP.sup _ x) (frobNorm_nonneg _) (by positivity)
  have hp21 : frobNorm (p2 - p1) ≤ 4 * D := by
    simp only [p2, p1]; rw [show t + 2 - 1 = (t + 1 - 1) + 1 by omega]; exact hP.step _ x
  have b : |2 * (cf w (t + 1) - cf w t)| * frobNorm (p2 - p1) ≤ 42 * (4 * D) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (by linarith [cf_d1 hw t]) hp21 (frobNorm_nonneg _) (by norm_num)
  have c : cf w t * frobNorm ((p2 - p1) - (p1 - p0)) ≤ 18 * D := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp [cf]; positivity
    · have e2 : t + 2 - 1 = (t - 1) + 2 := by omega
      have e1 : t + 1 - 1 = (t - 1) + 1 := by omega
      have hb := hP.step2 (t - 1) x
      have hn : (2 * ((t - 1 : ℕ) : ℝ) + 3) = 2 * t + 1 := by rw [Nat.cast_sub h0]; push_cast; ring
      rw [hn] at hb
      simp only [p2, p1, p0]; rw [e2, e1]
      calc cf w t * _ ≤ t * (36 * D / (2 * t + 1)) := mul_le_mul (cf_le hw t) hb (frobNorm_nonneg _) (by positivity)
        _ ≤ 18 * D := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have : 84 / (w : ℝ) * VB = 84 * VB / w := by ring
  linarith

end phi

end AdalyFormal.UnifLane.Z

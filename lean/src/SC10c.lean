import SC10a
import SC10b
import SC5b

/-!
# SC10c -- v2: THE EXPLICIT CELL THEOREM with the low-mode term and the two sinc regimes.

`cell_coercive_explicit2`:  for every `n>0`, `κ>0`, every twist `z`, field `w`, slack `S`:
    `(hfun2 (κ n^7) / n²) Σ‖w_μ‖² ≤ g1 + κ g2 + S`,
`hfun2 a = min (cS2 a) (cL2 a)` with closed forms below.  Standard axioms only.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped ComplexInnerProductSpace BigOperators ComplexConjugate
open AdalyFormal.FlatCoercivity

namespace AdalyFormal.ScaledCoercivity

noncomputable def muF (σ a x : ℝ) : ℝ := a * σ ^ 8 / (x * (1 + a / 4) + a)
noncomputable def LmF (σ a : ℝ) : ℝ := min (a * σ ^ 8 / 4) (4 * σ ^ 8 / (4 + σ ^ 8))
noncomputable def rat (m : ℝ) : ℝ := m / (1 + m)

/-- small-twist regime constant (`|θ_μ| ≤ 1`, `σ = 15/16`): the infimum over `x = n²λ0 > 0` of
`max(min(x,4), Lm) · rat(muF(x))` is attained at `x = Lm` -/
noncomputable def cS2 (a : ℝ) : ℝ := rat (muF (15 / 16) a (LmF (15 / 16) a)) * LmF (15 / 16) a
/-- large-twist regime constant (`σ = 2/π`, `4/π² ≤ n²λ0`, `Θ² ≤ 3π²`) -/
noncomputable def cL2 (a : ℝ) : ℝ :=
  min (4 * rat (muF (2 / Real.pi) a (3 * Real.pi ^ 2))) (4 / Real.pi ^ 2 * rat (muF (2 / Real.pi) a 4))
noncomputable def hfun2 (a : ℝ) : ℝ := min (cS2 a) (cL2 a)

section RealF
theorem rat_nonneg {m : ℝ} (h : 0 ≤ m) : 0 ≤ rat m := by unfold rat; positivity
theorem rat_le_one {m : ℝ} (h : 0 ≤ m) : rat m ≤ 1 := by
  unfold rat; rw [div_le_one (by linarith)]; linarith

theorem muF_nonneg {σ a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) : 0 ≤ muF σ a x := by
  unfold muF; positivity

theorem muF_anti {σ a x x' : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hxx : x ≤ x') :
    muF σ a x' ≤ muF σ a x := by
  unfold muF
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : 0 ≤ 1 + a / 4 := by positivity
  nlinarith

theorem LmF_nonneg {σ a : ℝ} (ha : 0 ≤ a) : 0 ≤ LmF σ a := by
  unfold LmF; exact le_min (by positivity) (by positivity)

theorem rat_muF {σ a y : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hy : 0 ≤ y) :
    rat (muF σ a y) = a * σ ^ 8 / (y * (1 + a / 4) + a + a * σ ^ 8) := by
  unfold rat muF
  have h1 : 0 < y * (1 + a / 4) + a := by positivity
  have h2 : 0 < a * σ ^ 8 := by positivity
  field_simp
end RealF

section Core
variable {n : ℕ}

/-- the common core: general `σ`-regime, non-trivial twist -/
theorem cell_core_nontrivial (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) (z : Fin 3 → Circle) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hσ : SigmaOK z σ) (μ0 : Fin 3) (hμ0 : ((z μ0 : Circle) : ℂ) ≠ 1)
    (w : Fin 3 → CV n) (S : ℝ) (hS0 : 0 ≤ S)
    (hS : ∀ u : CV n, ⟪epsV n, u⟫ = 0 →
      ‖⟪(cellSym hn z).Dstar w, (cellSym hn z).Lap u⟫‖ ^ 2 ≤ S * ‖(cellSym hn z).Lap u‖ ^ 2) :
    rat (muF σ (κ * (n : ℝ) ^ 7) ((n : ℝ) ^ 2 * lam n z (k0 hn))) *
        max (min ((n : ℝ) ^ 2 * lam n z (k0 hn)) 4) (LmF σ (κ * (n : ℝ) ^ 7)) / (n : ℝ) ^ 2
        * ∑ μ, ‖w μ‖ ^ 2 ≤ g1 hn (z, w) + κ * g2 hn (z, w) + S := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : 0 ≤ cn n := by unfold cn; positivity
  have hepsn : 0 < ‖epsV n‖ := norm_pos_iff.mpr (epsV_ne hn)
  set A : ℝ := (n : ℝ) * ‖epsV n‖ with hA
  set q0 : ℝ := cn n * (σ * (n : ℝ)) ^ 4 with hq0
  have hApos : 0 < A := by positivity
  have hq0nn : 0 ≤ q0 := by positivity
  have hAq : ∀ μ x, ‖(cellSym hn z).Qm μ x‖ ≤ A * ‖x‖ := by
    intro μ x
    exact Qm_norm_le (cellSym hn z) μ x
  have hq : ∀ μ, q0 ≤ ‖(cellSym hn z).Qm μ (cellMode hn z).e0‖ :=
    fun μ => Qm_e0_lower_σ hn z σ hσ0.le hσ1 hσ μ
  have hg1 : g1 hn (z, w) = g1b (cellSym hn z) w := rfl
  have hg2 : g2 hn (z, w) = g2b (cellSym hn z) w := rfl
  rw [hg1, hg2]
  have hl0 : 0 < (cellMode hn z).l0 := lam0_pos hn z μ0 hμ0
  set β : ℝ := cn n ^ 2 * (σ * (n : ℝ)) ^ 6 with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβle : β ≤ ‖⟪(cellMode hn z).e0, (cellSym hn z).eps⟫‖ ^ 2 := inner_e0_eps_lower_σ hn z σ hσ0.le hσ1 hσ
  set u : ℝ := (cellMode hn z).l0 with hu
  have hGv : (cellMode hn z).G = 4 / (n : ℝ) ^ 2 := rfl
  have hu_def : u = lam n z (k0 hn) := rfl
  have hcn2 : cn n ^ 2 * (n : ℝ) ^ 3 = 1 := cn_sq hn
  have hβv : β = σ ^ 6 * (n : ℝ) ^ 3 := by
    rw [hβ, mul_pow]
    calc cn n ^ 2 * (σ ^ 6 * (n : ℝ) ^ 6) = (cn n ^ 2 * (n : ℝ) ^ 3) * (σ ^ 6 * (n : ℝ) ^ 3) := by ring
      _ = _ := by rw [hcn2, one_mul]
  have hA2 : A ^ 2 = (n : ℝ) ^ 5 := by rw [hA, mul_pow, norm_epsV_sq hn]; ring
  have hq02 : q0 ^ 2 = σ ^ 8 * (n : ℝ) ^ 5 := by
    rw [hq0, mul_pow, ← pow_mul, mul_pow]
    calc cn n ^ 2 * (σ ^ (4 * 2) * (n : ℝ) ^ (4 * 2))
        = (cn n ^ 2 * (n : ℝ) ^ 3) * (σ ^ 8 * (n : ℝ) ^ 5) := by ring
      _ = _ := by rw [hcn2, one_mul]
  -- x := n² u
  set a : ℝ := κ * (n : ℝ) ^ 7 with ha
  set x : ℝ := (n : ℝ) ^ 2 * u with hx
  have hxpos : 0 < x := by positivity
  have hu_le : u ≤ Th2 z / (n : ℝ) ^ 2 := lam0_le hn z
  have hxTh : x ≤ Th2 z := by
    have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mp hu_le
    calc x = u * (n : ℝ) ^ 2 := by rw [hx]; ring
      _ ≤ _ := h1
  have hζ := zeta_ge_σ z σ hσ0.le hσ
  set ζ2 : ℝ := ∑ μ, ‖((cellSym hn z).ph μ) - 1‖ ^ 2 with hζ2
  have hζ2ge : σ ^ 2 * x ≤ ζ2 := by
    have : σ ^ 2 * Th2 z ≤ ζ2 := hζ
    calc σ ^ 2 * x ≤ σ ^ 2 * Th2 z := mul_le_mul_of_nonneg_left hxTh (by positivity)
      _ ≤ ζ2 := this
  set G2 : ℝ := ζ2 * β / u ^ 2 with hG2
  set S2 : ℝ := A ^ 2 * (1 / u + 1 / (4 / (n : ℝ) ^ 2)) with hS2
  have hS2nn : 0 ≤ κ * S2 := by
    have : 0 ≤ S2 := by rw [hS2]; positivity
    positivity
  have hP : σ ^ 8 * a / x ≤ κ * G2 := by
    have e1 : σ ^ 8 * a / x = κ * ((σ ^ 2 * x) * β / u ^ 2) := by
      rw [hx, ha, hβv]
      field_simp
    rw [e1, hG2]
    have : (σ ^ 2 * x) * β / u ^ 2 ≤ ζ2 * β / u ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hζ2ge hβ0
    exact mul_le_mul_of_nonneg_left this hκ.le
  have hQeq : κ * S2 = a / x + a / 4 := by
    rw [hS2, hA2, hx, ha]
    field_simp
  have hmuF : muF σ a x ≤ mu0c κ G2 S2 := by
    unfold mu0c muF
    have hd : 0 < 1 + κ * S2 := by linarith
    have e : σ ^ 8 * a / x / (1 + κ * S2) = a * σ ^ 8 / (x * (1 + a / 4) + a) := by
      rw [hQeq]
      field_simp
      ring
    rw [← e]
    exact div_le_div_of_nonneg_right hP hd.le
  -- lamN2
  have hlamN : lamN κ (cellMode hn z).G A q0 = LmF σ a / (n : ℝ) ^ 2 := by
    unfold lamN LmF
    rw [hq02, hA2, hGv]
    have e1 : κ * (σ ^ 8 * (n : ℝ) ^ 5) / 4 = a * σ ^ 8 / 4 / (n : ℝ) ^ 2 := by
      rw [ha]; field_simp
    have e2 : 4 / (n : ℝ) ^ 2 * (σ ^ 8 * (n : ℝ) ^ 5) / (4 * (n : ℝ) ^ 5 + σ ^ 8 * (n : ℝ) ^ 5)
        = 4 * σ ^ 8 / (4 + σ ^ 8) / (n : ℝ) ^ 2 := by
      have h5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
      have h6 : (0 : ℝ) < 4 + σ ^ 8 := by positivity
      field_simp
    rw [e1, e2, ← min_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  have hminug : min u (cellMode hn z).G = min x 4 / (n : ℝ) ^ 2 := by
    rw [hGv, hx]
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [show u = (n : ℝ) ^ 2 * u / (n : ℝ) ^ 2 by field_simp, show (4 : ℝ) / (n : ℝ) ^ 2 = 4 / (n : ℝ) ^ 2 from rfl]
    rw [← min_div_div_right hn2.le]
    congr 1
    field_simp
  have hlN2 : lamN2 κ u (cellMode hn z).G A q0 = max (min x 4) (LmF σ a) / (n : ℝ) ^ 2 := by
    unfold lamN2
    rw [hminug, hlamN, ← max_div_div_right (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  have hNw := N_coercive2 (cellMode hn z) κ A q0 hκ.le hApos hq0nn hq hAq
  have hlN0 : 0 ≤ lamN2 κ u (cellMode hn z).G A q0 :=
    lamN2_nonneg κ u _ A q0 hκ.le (cellMode hn z).l0_nonneg (by rw [hGv]; positivity)
  have key := cell_abstract_nontrivial_gen (cellMode hn z) κ A β (lamN2 κ u (cellMode hn z).G A q0)
    hκ hApos hl0 hlN0 hNw hAq hβle hβ0 μ0 hμ0 w S hS0 hS
  -- compare constants
  have hmu0nn : 0 ≤ muF σ a x := muF_nonneg (by positivity) hxpos.le
  have hratio := ratio_mono hmu0nn hmuF
  have h3 : 0 ≤ ∑ μ, ‖w μ‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcomp : rat (muF σ a x) * (max (min x 4) (LmF σ a) / (n : ℝ) ^ 2)
      ≤ mu0c κ G2 S2 / (1 + mu0c κ G2 S2) * lamN2 κ u (cellMode hn z).G A q0 := by
    rw [hlN2]
    unfold rat
    apply mul_le_mul_of_nonneg_right hratio
    have : 0 ≤ LmF σ a := LmF_nonneg (by positivity)
    positivity
  have h4 : rat (muF σ a x) * max (min x 4) (LmF σ a) / (n : ℝ) ^ 2 * ∑ μ, ‖w μ‖ ^ 2
      ≤ mu0c κ G2 S2 / (1 + mu0c κ G2 S2) * lamN2 κ u (cellMode hn z).G A q0 * ∑ μ, ‖w μ‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ h3
    rw [mul_div_assoc]
    exact hcomp
  exact h4.trans key

end Core

end AdalyFormal.ScaledCoercivity

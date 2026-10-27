import GG2

/-!
# GG3 -- two-chart collar gluing on the periodic lattice, group level (m2_glue2, 2026-10-15)

`GChart U g D t₁ t₂`: on the site set `D`, `|U^g(x,ν) − 1| ≤ t₁` on every bond with both ends in `D`, and
`|U^g(x+μ,ν) − U^g(x,ν)| ≤ t₂` on every stencil `{x, x+ν, x+μ, x+μ+ν} ⊆ D`.

**`glue_two`**: charts `(g_P, D_P)`, `(g_Q, D_Q)` at constants `(t₁, t₂)`, transition `h = g_Q g_P⁻¹` with `|h − 1| ≤ τ ≤ 2`
on `D_P ∩ D_Q`, and a cut-off `c` with `0 ≤ c ≤ 1`, `|Δc| ≤ κ₁`, `|Δ²c| ≤ κ₂`, such that every bond / stencil of the target
set `D` is either `c ≡ 0` inside `D_P`, `c ≡ 1` inside `D_Q`, or inside `D_P ∩ D_Q`.  Then
`g = (if c = 1 then h else cay (c · icay h)) · g_P` is a `GChart` on `D` at constants `glueT1`, `glueT2` (explicit).
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 su2Exp su2Log su2Angle coe_mul coe_inv coe_one)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm frobSq frobSq_nonneg)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)
open scoped Matrix

/-! ## §1 pointwise transition and Leibniz bounds -/

theorem frobNorm_star_sub_one (g : SU2) : frobNorm ((g : M2)ᴴ - 1) = frobNorm ((g : M2) - 1) := by
  rw [← frobNorm_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_one]

/-- transition, first difference: `h₁ = G_Q⁻¹ h₀ G_P ⇒ |h₁ − h₀| ≤ |G_P − 1| + |G_Q − 1|`. -/
theorem trans_one (h0 h1 GP GQ : SU2) (hrel : h1 = GQ⁻¹ * h0 * GP) :
    frobNorm ((h1 : M2) - (h0 : M2)) ≤ frobNorm ((GP : M2) - 1) + frobNorm ((GQ : M2) - 1) := by
  rw [hrel, coe_mul, coe_mul, coe_inv]
  have e : (GQ : M2)ᴴ * (h0 : M2) * (GP : M2) - (h0 : M2)
      = (GQ : M2)ᴴ * ((h0 : M2) * ((GP : M2) - 1)) + ((GQ : M2)ᴴ - 1) * (h0 : M2) := by noncomm_ring
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  rw [frobNorm_su2_mul_star, frobNorm_su2_mul, frobNorm_mul_su2, frobNorm_star_sub_one]

/-- transition, second difference. -/
theorem trans_two (h0 h1 h2 h3 GP GQ GP' GQ' : SU2) (hrel : h1 = GQ⁻¹ * h0 * GP)
    (hrel' : h3 = GQ'⁻¹ * h2 * GP') :
    frobNorm ((h3 : M2) - (h2 : M2) - ((h1 : M2) - (h0 : M2)))
      ≤ frobNorm ((GP' : M2) - (GP : M2)) + frobNorm ((GQ' : M2) - (GQ : M2))
        + frobNorm ((h2 : M2) - (h0 : M2)) * (frobNorm ((GP : M2) - 1) + frobNorm ((GQ : M2) - 1))
        + frobNorm ((GQ' : M2) - 1) * frobNorm ((GP' : M2) - 1)
        + frobNorm ((GQ : M2) - 1) * frobNorm ((GP : M2) - 1) := by
  rw [hrel, hrel']
  simp only [coe_mul, coe_inv]
  set E : M2 := (GP : M2) - 1 with hE
  set E' : M2 := (GP' : M2) - 1 with hE'
  set F : M2 := (GQ : M2)ᴴ - 1 with hF
  set F' : M2 := (GQ' : M2)ᴴ - 1 with hF'
  have e : (GQ' : M2)ᴴ * (h2 : M2) * (GP' : M2) - (h2 : M2) - ((GQ : M2)ᴴ * (h0 : M2) * (GP : M2) - (h0 : M2))
      = (h2 : M2) * (E' - E) + ((h2 : M2) - (h0 : M2)) * E + (F' - F) * (h2 : M2) + F * ((h2 : M2) - (h0 : M2))
        + (F' * ((h2 : M2) * E') - F * ((h0 : M2) * E)) := by
    rw [hE, hE', hF, hF']; noncomm_ring
  rw [e]
  have hEE : E' - E = (GP' : M2) - GP := by rw [hE, hE']; abel
  have hFF : frobNorm (F' - F) = frobNorm ((GQ' : M2) - (GQ : M2)) := by
    rw [hF, hF', show (GQ' : M2)ᴴ - 1 - ((GQ : M2)ᴴ - 1) = ((GQ' : M2) - (GQ : M2))ᴴ by
      rw [Matrix.conjTranspose_sub]; abel, frobNorm_conjTranspose]
  have hFn : frobNorm F = frobNorm ((GQ : M2) - 1) := frobNorm_star_sub_one GQ
  have hFn' : frobNorm F' = frobNorm ((GQ' : M2) - 1) := frobNorm_star_sub_one GQ'
  have n1 : frobNorm ((h2 : M2) * (E' - E)) = frobNorm ((GP' : M2) - (GP : M2)) := by
    rw [frobNorm_su2_mul, hEE]
  have n2 : frobNorm (((h2 : M2) - (h0 : M2)) * E) ≤ frobNorm ((h2 : M2) - (h0 : M2)) * frobNorm E := frobNorm_mul_le _ _
  have n3 : frobNorm ((F' - F) * (h2 : M2)) = frobNorm ((GQ' : M2) - (GQ : M2)) := by rw [frobNorm_mul_su2, hFF]
  have n4 : frobNorm (F * ((h2 : M2) - (h0 : M2))) ≤ frobNorm F * frobNorm ((h2 : M2) - (h0 : M2)) := frobNorm_mul_le _ _
  have n5 : frobNorm (F' * ((h2 : M2) * E') - F * ((h0 : M2) * E))
      ≤ frobNorm F' * frobNorm E' + frobNorm F * frobNorm E := by
    refine (AdalyFormal.Balaban.RegularityGap.frobNorm_sub_le _ _).trans ?_
    have a := frobNorm_mul_le F' ((h2 : M2) * E'); rw [frobNorm_su2_mul] at a
    have b := frobNorm_mul_le F ((h0 : M2) * E); rw [frobNorm_su2_mul] at b
    linarith
  have := frobNorm_add5_le ((h2 : M2) * (E' - E)) (((h2 : M2) - (h0 : M2)) * E) ((F' - F) * (h2 : M2))
    (F * ((h2 : M2) - (h0 : M2))) (F' * ((h2 : M2) * E') - F * ((h0 : M2) * E))
  rw [hFn] at n4; rw [hFn, hFn'] at n5
  nlinarith [frobNorm_nonneg ((h2 : M2) - (h0 : M2)), frobNorm_nonneg E]

theorem leib_one (c0 c1 : ℝ) (W0 W1 : M2) :
    frobNorm (c1 • W1 - c0 • W0) ≤ |c1 - c0| * frobNorm W1 + |c0| * frobNorm (W1 - W0) := by
  have e : c1 • W1 - c0 • W0 = (c1 - c0) • W1 + c0 • (W1 - W0) := by module
  rw [e]; refine (frobNorm_add_le _ _).trans ?_
  rw [frobNorm_smul, frobNorm_smul]

theorem leib_two (c0 c1 c2 c3 : ℝ) (W0 W1 W2 W3 : M2) :
    frobNorm (c3 • W3 - c2 • W2 - (c1 • W1 - c0 • W0))
      ≤ |c3 - c2 - c1 + c0| * frobNorm W3 + |c2 - c0| * frobNorm (W3 - W2) + |c1 - c0| * frobNorm (W3 - W1)
        + |c0| * frobNorm (W3 - W2 - (W1 - W0)) := by
  have e : c3 • W3 - c2 • W2 - (c1 • W1 - c0 • W0)
      = (c3 - c2 - c1 + c0) • W3 + (c2 - c0) • (W3 - W2) + (c1 - c0) • (W3 - W1)
        + c0 • (W3 - W2 - (W1 - W0)) := by module
  rw [e]; refine (frobNorm_add4_le _ _ _ _).trans ?_
  rw [frobNorm_smul, frobNorm_smul, frobNorm_smul, frobNorm_smul]

/-! ## §2 lattice -/

variable {L : PeriodicLatticeExtent}

/-- `= CoercUMainDesigned.LinkCfg`. -/
abbrev LinkCfg (L : PeriodicLatticeExtent) : Type := PeriodicLinkConfiguration SU2 L

theorem shift_comm' (x : PeriodicLatticeSite L) (μ ν : Fin 3) :
    periodicLatticeShift (periodicLatticeShift x μ) ν = periodicLatticeShift (periodicLatticeShift x ν) μ := by
  by_cases h : μ = ν
  · subst h; rfl
  · simp only [periodicLatticeShift]
    rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne h]
    exact Function.update_comm h _ _ x

/-- group-level chart on a site set. -/
def GChart (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (D : Set (PeriodicLatticeSite L)) (t1 t2 : ℝ) : Prop :=
  (∀ (x : PeriodicLatticeSite L) (ν : Fin 3), x ∈ D → periodicLatticeShift x ν ∈ D →
      frobNorm (((periodicGaugeTransform g U (x, ν) : SU2) : M2) - 1) ≤ t1) ∧
  (∀ (x : PeriodicLatticeSite L) (μ ν : Fin 3), x ∈ D → periodicLatticeShift x ν ∈ D →
      periodicLatticeShift x μ ∈ D → periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D →
      frobNorm (((periodicGaugeTransform g U (periodicLatticeShift x μ, ν) : SU2) : M2)
        - (periodicGaugeTransform g U (x, ν) : SU2)) ≤ t2)

/-- the transition function. -/
def trans (gP gQ : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) : SU2 := gQ x * (gP x)⁻¹

theorem trans_rel (U : LinkCfg L) (gP gQ : PeriodicLatticeSite L → SU2) (x : PeriodicLatticeSite L) (ν : Fin 3) :
    trans gP gQ (periodicLatticeShift x ν)
      = (periodicGaugeTransform gQ U (x, ν))⁻¹ * trans gP gQ x * periodicGaugeTransform gP U (x, ν) := by
  simp only [trans, periodicGaugeTransform]
  group

/-- the interpolating gauge factor. -/
noncomputable def kglue (gP gQ : PeriodicLatticeSite L → SU2) (c : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) : SU2 :=
  open Classical in if c x = 1 then trans gP gQ x else cay (c x • icay (trans gP gQ x))

noncomputable def gglue (gP gQ : PeriodicLatticeSite L → SU2) (c : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) : SU2 := kglue gP gQ c x * gP x

theorem gglue_of_one {gP gQ : PeriodicLatticeSite L → SU2} {c : PeriodicLatticeSite L → ℝ}
    {x : PeriodicLatticeSite L} (h : c x = 1) : gglue gP gQ c x = gQ x := by
  classical
  simp only [gglue, kglue, if_pos h, trans]; group

theorem gglue_of_zero {gP gQ : PeriodicLatticeSite L → SU2} {c : PeriodicLatticeSite L → ℝ}
    {x : PeriodicLatticeSite L} (h : c x = 0) : gglue gP gQ c x = gP x := by
  classical
  have : c x ≠ 1 := by rw [h]; norm_num
  rw [gglue, kglue, if_neg this, h, zero_smul, cay_zero, one_mul]

theorem kglue_of_mem {gP gQ : PeriodicLatticeSite L → SU2} {c : PeriodicLatticeSite L → ℝ}
    {x : PeriodicLatticeSite L} (hh : frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ 2) :
    kglue gP gQ c x = cay (c x • icay (trans gP gQ x)) := by
  classical
  by_cases h : c x = 1
  · rw [kglue, if_pos h, h, one_smul]; exact (cay_icay hh).symm
  · rw [kglue, if_neg h]

theorem gauge_gglue (U : LinkCfg L) (gP gQ : PeriodicLatticeSite L → SU2) (c : PeriodicLatticeSite L → ℝ)
    (x : PeriodicLatticeSite L) (ν : Fin 3) :
    periodicGaugeTransform (gglue gP gQ c) U (x, ν)
      = kglue gP gQ c x * periodicGaugeTransform gP U (x, ν) * (kglue gP gQ c (periodicLatticeShift x ν))⁻¹ := by
  simp only [gglue, periodicGaugeTransform]; group

/-- the constants. -/
noncomputable def glueK (t1 τ κ1 : ℝ) : ℝ := κ1 * τ + 4 * t1
noncomputable def glueT1 (t1 τ κ1 : ℝ) : ℝ := t1 + (9 / 2) * glueK t1 τ κ1
noncomputable def glueT2 (t1 t2 τ κ1 κ2 : ℝ) : ℝ :=
  t2 + t1 * (2 * ((9 / 2) * glueK t1 τ κ1)) + ((9 / 2) * glueK t1 τ κ1) * ((9 / 2) * glueK t1 τ κ1)
    + (9 / 2) * (κ2 * τ + 8 * κ1 * t1 + 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2)
    + (27 / 4) * (2 * glueK t1 τ κ1) * glueK t1 τ κ1

/-- pointwise bond bound in the collar. -/
theorem collar_bond {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2} {c : PeriodicLatticeSite L → ℝ}
    {t1 τ κ1 : ℝ} (hτ2 : τ ≤ 2) {x : PeriodicLatticeSite L} {ν : Fin 3}
    (hP1 : frobNorm (((periodicGaugeTransform gP U (x, ν) : SU2) : M2) - 1) ≤ t1)
    (hQ1 : frobNorm (((periodicGaugeTransform gQ U (x, ν) : SU2) : M2) - 1) ≤ t1)
    (hh0 : frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ τ)
    (hh1 : frobNorm (((trans gP gQ (periodicLatticeShift x ν) : SU2) : M2) - 1) ≤ τ)
    (hc0 : 0 ≤ c x ∧ c x ≤ 1) (hcd : |c (periodicLatticeShift x ν) - c x| ≤ κ1) (hκ : 0 ≤ κ1) :
    frobNorm (((kglue gP gQ c (periodicLatticeShift x ν) : SU2) : M2) - (kglue gP gQ c x : SU2))
      ≤ (9 / 2) * glueK t1 τ κ1 ∧
    frobNorm (c (periodicLatticeShift x ν) • icay (trans gP gQ (periodicLatticeShift x ν))
      - c x • icay (trans gP gQ x)) ≤ glueK t1 τ κ1 := by
  set x1 := periodicLatticeShift x ν
  have h0 : frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ 2 := hh0.trans hτ2
  have h1 : frobNorm (((trans gP gQ x1 : SU2) : M2) - 1) ≤ 2 := hh1.trans hτ2
  rw [kglue_of_mem h0, kglue_of_mem h1]
  have ht := trans_one (trans gP gQ x) (trans gP gQ x1) _ _ (trans_rel U gP gQ x ν)
  have hW := frobNorm_icay_sub_le (acos2_nonneg h1) (acos2_nonneg h0)
  have hW1 := frobNorm_icay_le h1
  have hY := leib_one (c x) (c x1) (icay (trans gP gQ x)) (icay (trans gP gQ x1))
  have hc0' : |c x| ≤ 1 := by rw [abs_of_nonneg hc0.1]; exact hc0.2
  have hYb : frobNorm (c x1 • icay (trans gP gQ x1) - c x • icay (trans gP gQ x)) ≤ glueK t1 τ κ1 := by
    rw [glueK]
    have a1 : |c x1 - c x| * frobNorm (icay (trans gP gQ x1)) ≤ κ1 * τ :=
      mul_le_mul hcd (hW1.trans hh1) (frobNorm_nonneg _) hκ
    have a2 : |c x| * frobNorm (icay (trans gP gQ x1) - icay (trans gP gQ x)) ≤ 1 * (2 * (2 * t1)) := by
      apply mul_le_mul hc0' _ (frobNorm_nonneg _) (by norm_num)
      linarith
    linarith
  refine ⟨?_, hYb⟩
  refine (frobNorm_cay_sub_le ((isSu2_icay _).smul _) ((isSu2_icay _).smul _)).trans ?_
  exact mul_le_mul_of_nonneg_left hYb (by norm_num)

theorem cay_second4 {Y0 Y1 Y2 Y3 : M2} (h0 : IsSu2 Y0) (h1 : IsSu2 Y1) (h2 : IsSu2 Y2) (h3 : IsSu2 Y3) :
    frobNorm (((cay Y3 : SU2) : M2) - (cay Y2 : M2) - (((cay Y1 : SU2) : M2) - (cay Y0 : M2)))
      ≤ (9 / 2) * frobNorm (Y3 - Y2 - (Y1 - Y0))
        + (27 / 4) * (frobNorm (Y3 - Y1) + frobNorm (Y2 - Y0)) * frobNorm (Y1 - Y0) :=
  frobNorm_cay_second_le ![Y0, Y1, Y2, Y3] (fun i => by fin_cases i <;> [exact h0; exact h1; exact h2; exact h3])

theorem icay_second4 {h0 h1 h2 h3 : SU2} (a0 : 0 ≤ acos2 h0) (a1 : 0 ≤ acos2 h1) (a2 : 0 ≤ acos2 h2)
    (a3 : 0 ≤ acos2 h3) :
    frobNorm (icay h3 - icay h2 - (icay h1 - icay h0))
      ≤ 2 * frobNorm ((h3 : M2) - (h2 : M2) - ((h1 : M2) - (h0 : M2)))
        + 2 * (frobNorm ((h3 : M2) - (h1 : M2)) + frobNorm ((h2 : M2) - (h0 : M2)))
          * frobNorm ((h1 : M2) - (h0 : M2)) :=
  frobNorm_icay_second_le ![h0, h1, h2, h3] (fun i => by fin_cases i <;> [exact a0; exact a1; exact a2; exact a3])

/-- **two-chart collar gluing.** -/
theorem glue_two {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2}
    {DP DQ D : Set (PeriodicLatticeSite L)} {c : PeriodicLatticeSite L → ℝ}
    {t1 t2 τ κ1 κ2 : ℝ} (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) (hκ1 : 0 ≤ κ1)
    (hκ2 : 0 ≤ κ2)
    (hP : GChart U gP DP t1 t2) (hQ : GChart U gQ DQ t1 t2)
    (hh : ∀ x, x ∈ DP → x ∈ DQ → frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ τ)
    (hc : ∀ x, x ∈ D → 0 ≤ c x ∧ c x ≤ 1)
    (hc1 : ∀ x ν, x ∈ D → periodicLatticeShift x ν ∈ D → |c (periodicLatticeShift x ν) - c x| ≤ κ1)
    (hc2 : ∀ x μ ν, x ∈ D → periodicLatticeShift x ν ∈ D → periodicLatticeShift x μ ∈ D →
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D →
      |c (periodicLatticeShift (periodicLatticeShift x μ) ν) - c (periodicLatticeShift x μ)
      - c (periodicLatticeShift x ν) + c x| ≤ κ2)
    (hbond : ∀ x ν, x ∈ D → periodicLatticeShift x ν ∈ D →
      (c x = 0 ∧ c (periodicLatticeShift x ν) = 0 ∧ x ∈ DP ∧ periodicLatticeShift x ν ∈ DP) ∨
      (c x = 1 ∧ c (periodicLatticeShift x ν) = 1 ∧ x ∈ DQ ∧ periodicLatticeShift x ν ∈ DQ) ∨
      (x ∈ DP ∧ x ∈ DQ ∧ periodicLatticeShift x ν ∈ DP ∧ periodicLatticeShift x ν ∈ DQ))
    (hsten : ∀ x μ ν, x ∈ D → periodicLatticeShift x ν ∈ D → periodicLatticeShift x μ ∈ D →
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D →
      (∀ y ∈ ({x, periodicLatticeShift x ν, periodicLatticeShift x μ,
          periodicLatticeShift (periodicLatticeShift x μ) ν} : Set (PeriodicLatticeSite L)), c y = 0 ∧ y ∈ DP) ∨
      (∀ y ∈ ({x, periodicLatticeShift x ν, periodicLatticeShift x μ,
          periodicLatticeShift (periodicLatticeShift x μ) ν} : Set (PeriodicLatticeSite L)), c y = 1 ∧ y ∈ DQ) ∨
      (∀ y ∈ ({x, periodicLatticeShift x ν, periodicLatticeShift x μ,
          periodicLatticeShift (periodicLatticeShift x μ) ν} : Set (PeriodicLatticeSite L)), y ∈ DP ∧ y ∈ DQ)) :
    GChart U (gglue gP gQ c) D (glueT1 t1 τ κ1) (glueT2 t1 t2 τ κ1 κ2) := by
  have hK : 0 ≤ glueK t1 τ κ1 := by unfold glueK; positivity
  have hT1 : t1 ≤ glueT1 t1 τ κ1 := by unfold glueT1; linarith
  have hT2 : t2 ≤ glueT2 t1 t2 τ κ1 κ2 := by
    unfold glueT2
    have : 0 ≤ t1 * (2 * ((9 / 2) * glueK t1 τ κ1)) := by positivity
    have : 0 ≤ ((9 / 2) * glueK t1 τ κ1) * ((9 / 2) * glueK t1 τ κ1) := by positivity
    have : 0 ≤ (9 / 2) * (κ2 * τ + 8 * κ1 * t1 + 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2) := by positivity
    have : 0 ≤ (27 / 4) * (2 * glueK t1 τ κ1) * glueK t1 τ κ1 := by positivity
    linarith
  -- the gauge on a bond with both ends `c = 0` / `c = 1`
  have pure0 : ∀ x ν, c x = 0 → c (periodicLatticeShift x ν) = 0 →
      periodicGaugeTransform (gglue gP gQ c) U (x, ν) = periodicGaugeTransform gP U (x, ν) := by
    intro x ν a b
    simp only [periodicGaugeTransform, gglue_of_zero a, gglue_of_zero b]
  have pure1 : ∀ x ν, c x = 1 → c (periodicLatticeShift x ν) = 1 →
      periodicGaugeTransform (gglue gP gQ c) U (x, ν) = periodicGaugeTransform gQ U (x, ν) := by
    intro x ν a b
    simp only [periodicGaugeTransform, gglue_of_one a, gglue_of_one b]
  refine ⟨?_, ?_⟩
  · intro x ν hx hxν
    rcases hbond x ν hx hxν with ⟨a, b, p0, p1⟩ | ⟨a, b, q0, q1⟩ | ⟨p0, q0, p1, q1⟩
    · rw [pure0 x ν a b]; exact (hP.1 x ν p0 p1).trans hT1
    · rw [pure1 x ν a b]; exact (hQ.1 x ν q0 q1).trans hT1
    · rw [gauge_gglue]
      refine (gauge_step_one _ _ _).trans ?_
      have hb := (collar_bond (U := U) hτ2 (hP.1 x ν p0 p1) (hQ.1 x ν q0 q1) (hh x p0 q0) (hh _ p1 q1)
        (hc x hx) (hc1 x ν hx hxν) hκ1).1
      have := hP.1 x ν p0 p1
      unfold glueT1; linarith
  · intro x μ ν h0 h1 h2 h3
    have hst := hsten x μ ν h0 h1 h2 h3
    set x1 := periodicLatticeShift x ν with hx1
    set x2 := periodicLatticeShift x μ with hx2
    set x3 := periodicLatticeShift x2 ν with hx3
    have hx3' : periodicLatticeShift x1 μ = x3 := by rw [hx1, hx3, hx2, shift_comm']
    have m0 : x ∈ ({x, x1, x2, x3} : Set (PeriodicLatticeSite L)) := by simp
    have m1 : x1 ∈ ({x, x1, x2, x3} : Set (PeriodicLatticeSite L)) := by simp
    have m2 : x2 ∈ ({x, x1, x2, x3} : Set (PeriodicLatticeSite L)) := by simp
    have m3 : x3 ∈ ({x, x1, x2, x3} : Set (PeriodicLatticeSite L)) := by simp
    rcases hst with hA | hA | hA
    · obtain ⟨a0, p0⟩ := hA x m0; obtain ⟨a1, p1⟩ := hA x1 m1
      obtain ⟨a2, p2⟩ := hA x2 m2; obtain ⟨a3, p3⟩ := hA x3 m3
      rw [pure0 x ν a0 a1, pure0 x2 ν a2 a3]
      exact (hP.2 x μ ν p0 p1 p2 p3).trans hT2
    · obtain ⟨a0, p0⟩ := hA x m0; obtain ⟨a1, p1⟩ := hA x1 m1
      obtain ⟨a2, p2⟩ := hA x2 m2; obtain ⟨a3, p3⟩ := hA x3 m3
      rw [pure1 x ν a0 a1, pure1 x2 ν a2 a3]
      exact (hQ.2 x μ ν p0 p1 p2 p3).trans hT2
    · obtain ⟨p0, q0⟩ := hA x m0; obtain ⟨p1, q1⟩ := hA x1 m1
      obtain ⟨p2, q2⟩ := hA x2 m2; obtain ⟨p3, q3⟩ := hA x3 m3
      have p3' : periodicLatticeShift x1 μ ∈ DP := by rw [hx3']; exact p3
      have q3' : periodicLatticeShift x1 μ ∈ DQ := by rw [hx3']; exact q3
      rw [gauge_gglue, gauge_gglue]
      refine (gauge_step_two _ _ _ _ _ _).trans ?_
      rw [← hx3, ← hx1]
      -- first differences of `k`
      have bν := collar_bond (U := U) hτ2 (hP.1 x ν p0 p1) (hQ.1 x ν q0 q1) (hh x p0 q0) (hh _ p1 q1)
        (hc x h0) (hc1 x ν h0 h1) hκ1
      have bμ := collar_bond (U := U) hτ2 (hP.1 x μ p0 p2) (hQ.1 x μ q0 q2) (hh x p0 q0) (hh _ p2 q2)
        (hc x h0) (hc1 x μ h0 h2) hκ1
      have bμ' := collar_bond (U := U) hτ2 (hP.1 x1 μ p1 p3') (hQ.1 x1 μ q1 q3') (hh x1 p1 q1)
        (hh _ p3' q3') (hc x1 h1) (hc1 x1 μ h1 (by rw [hx3']; exact h3)) hκ1
      have bν' := collar_bond (U := U) hτ2 (hP.1 x2 ν p2 p3) (hQ.1 x2 ν q2 q3) (hh x2 p2 q2) (hh _ p3 q3)
        (hc x2 h2) (hc1 x2 ν h2 h3) hκ1
      rw [hx3'] at bμ'
      rw [← hx1] at bν
      rw [← hx2] at bμ
      rw [← hx3] at bν'
      -- second difference of `k`
      have e2 : ∀ y, y ∈ DP → y ∈ DQ → frobNorm (((trans gP gQ y : SU2) : M2) - 1) ≤ 2 :=
        fun y a b => (hh y a b).trans hτ2
      simp only [kglue_of_mem (e2 x p0 q0), kglue_of_mem (e2 x1 p1 q1), kglue_of_mem (e2 x2 p2 q2),
        kglue_of_mem (e2 x3 p3 q3)] at bν bμ bμ' bν' ⊢
      set H0 := trans gP gQ x; set H1 := trans gP gQ x1
      set H2 := trans gP gQ x2; set H3 := trans gP gQ x3
      have sY : ∀ y : SU2, ∀ r : ℝ, IsSu2 (r • icay y) := fun y r => (isSu2_icay y).smul r
      have hk2 := cay_second4 (sY H0 (c x)) (sY H1 (c x1)) (sY H2 (c x2)) (sY H3 (c x3))
      -- second difference of `Y = c · icay h`
      have hL := leib_two (c x) (c x1) (c x2) (c x3) (icay H0) (icay H1) (icay H2) (icay H3)
      -- transitions
      have r01 := trans_rel U gP gQ x ν
      have r23 := trans_rel U gP gQ x2 ν
      have r02 := trans_rel U gP gQ x μ
      have r13 := trans_rel U gP gQ x1 μ
      rw [hx3'] at r13
      have t01 := trans_one _ _ _ _ r01
      have t23 := trans_one _ _ _ _ r23
      have t02 := trans_one _ _ _ _ r02
      have t13 := trans_one _ _ _ _ r13
      have tt := trans_two _ _ _ _ _ _ _ _ r01 r23
      have aa : ∀ y, y ∈ DP → y ∈ DQ → 0 ≤ acos2 (trans gP gQ y) := fun y a b => acos2_nonneg (e2 y a b)
      have hW2 := icay_second4 (aa x p0 q0) (aa x1 p1 q1) (aa x2 p2 q2) (aa x3 p3 q3)
      have w32 := frobNorm_icay_sub_le (aa x3 p3 q3) (aa x2 p2 q2)
      have w31 := frobNorm_icay_sub_le (aa x3 p3 q3) (aa x1 p1 q1)
      have w3 := frobNorm_icay_le (e2 x3 p3 q3)
      -- chart bounds
      have gP01 := hP.1 x ν p0 p1; have gQ01 := hQ.1 x ν q0 q1
      have gP23 := hP.1 x2 ν p2 p3; have gQ23 := hQ.1 x2 ν q2 q3
      have gP02 := hP.1 x μ p0 p2; have gQ02 := hQ.1 x μ q0 q2
      have gP13 := hP.1 x1 μ p1 p3'; have gQ13 := hQ.1 x1 μ q1 q3'
      have dP := hP.2 x μ ν p0 p1 p2 p3
      have dQ := hQ.2 x μ ν q0 q1 q2 q3
      rw [← hx2] at dP dQ
      have hh3 := hh x3 p3 q3
      have c2b := hc2 x μ ν h0 h1 h2 h3
      have c1ν := hc1 x ν h0 h1; have c1μ := hc1 x μ h0 h2
      have hc0 := hc x h0
      -- assemble: abbreviations for the norms
      set nP01 := frobNorm (((periodicGaugeTransform gP U (x, ν) : SU2) : M2) - 1)
      set nQ01 := frobNorm (((periodicGaugeTransform gQ U (x, ν) : SU2) : M2) - 1)
      set nP23 := frobNorm (((periodicGaugeTransform gP U (x2, ν) : SU2) : M2) - 1)
      set nQ23 := frobNorm (((periodicGaugeTransform gQ U (x2, ν) : SU2) : M2) - 1)
      set d01 := frobNorm ((H1 : M2) - (H0 : M2))
      set d23 := frobNorm ((H3 : M2) - (H2 : M2))
      set d02 := frobNorm ((H2 : M2) - (H0 : M2))
      set d13 := frobNorm ((H3 : M2) - (H1 : M2))
      set D2h := frobNorm ((H3 : M2) - (H2 : M2) - ((H1 : M2) - (H0 : M2)))
      have nn : 0 ≤ nP01 ∧ 0 ≤ nQ01 ∧ 0 ≤ nP23 ∧ 0 ≤ nQ23 ∧ 0 ≤ d01 ∧ 0 ≤ d23 ∧ 0 ≤ d02 ∧ 0 ≤ d13 :=
        ⟨frobNorm_nonneg _, frobNorm_nonneg _, frobNorm_nonneg _, frobNorm_nonneg _, frobNorm_nonneg _,
          frobNorm_nonneg _, frobNorm_nonneg _, frobNorm_nonneg _⟩
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := nn
      have hd01 : d01 ≤ 2 * t1 := by linarith
      have hd23 : d23 ≤ 2 * t1 := by linarith
      have hd02 : d02 ≤ 2 * t1 := by linarith
      have hd13 : d13 ≤ 2 * t1 := by linarith
      have hD2h : D2h ≤ 2 * t2 + 6 * t1 ^ 2 := by
        have a1 : d02 * (nP01 + nQ01) ≤ (2 * t1) * (2 * t1) := by
          apply mul_le_mul hd02 (by linarith) (by positivity) (by linarith)
        have a2 : nQ23 * nP23 ≤ t1 * t1 := mul_le_mul gQ23 gP23 n3 ht1
        have a3 : nQ01 * nP01 ≤ t1 * t1 := mul_le_mul gQ01 gP01 n1 ht1
        nlinarith [tt]
      have hW2' : frobNorm (icay H3 - icay H2 - (icay H1 - icay H0)) ≤ 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2 := by
        have a1 : (d13 + d02) * d01 ≤ (4 * t1) * (2 * t1) := by
          apply mul_le_mul (by linarith) hd01 n5 (by linarith)
        nlinarith [hW2]
      have hY2 : frobNorm (c x3 • icay H3 - c x2 • icay H2 - (c x1 • icay H1 - c x • icay H0))
          ≤ κ2 * τ + 8 * κ1 * t1 + 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2 := by
        refine hL.trans ?_
        have hc0' : |c x| ≤ 1 := by rw [abs_of_nonneg hc0.1]; exact hc0.2
        have b1 : |c x3 - c x2 - c x1 + c x| * frobNorm (icay H3) ≤ κ2 * τ :=
          mul_le_mul c2b (w3.trans hh3) (frobNorm_nonneg _) hκ2
        have b2 : |c x2 - c x| * frobNorm (icay H3 - icay H2) ≤ κ1 * (4 * t1) :=
          mul_le_mul c1μ (by linarith) (frobNorm_nonneg _) hκ1
        have b3 : |c x1 - c x| * frobNorm (icay H3 - icay H1) ≤ κ1 * (4 * t1) :=
          mul_le_mul c1ν (by linarith) (frobNorm_nonneg _) hκ1
        have b4 : |c x| * frobNorm (icay H3 - icay H2 - (icay H1 - icay H0))
            ≤ 1 * (2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2) :=
          mul_le_mul hc0' hW2' (frobNorm_nonneg _) (by norm_num)
        nlinarith
      -- first differences of `Y`
      have yν := bν.2; have yμ := bμ.2; have yμ' := bμ'.2
      have hk2' : frobNorm (((cay (c x3 • icay H3) : SU2) : M2) - (cay (c x2 • icay H2) : M2)
          - (((cay (c x1 • icay H1) : SU2) : M2) - (cay (c x • icay H0) : M2)))
          ≤ (9 / 2) * (κ2 * τ + 8 * κ1 * t1 + 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2)
            + (27 / 4) * (2 * glueK t1 τ κ1) * glueK t1 τ κ1 := by
        refine hk2.trans ?_
        have b1 : (frobNorm (c x3 • icay H3 - c x1 • icay H1) + frobNorm (c x2 • icay H2 - c x • icay H0))
            * frobNorm (c x1 • icay H1 - c x • icay H0) ≤ (2 * glueK t1 τ κ1) * glueK t1 τ κ1 :=
          mul_le_mul (by linarith) yν (frobNorm_nonneg _) (by linarith)
        nlinarith
      have kν' := bν'.1; have kμ := bμ.1; have kμ' := bμ'.1
      have g1 : frobNorm (((periodicGaugeTransform gP U (x, ν) : SU2) : M2) - 1)
          * (frobNorm (((cay (c x2 • icay H2) : SU2) : M2) - (cay (c x • icay H0) : M2))
            + frobNorm (((cay (c x3 • icay H3) : SU2) : M2) - (cay (c x1 • icay H1) : M2)))
          ≤ t1 * (2 * ((9 / 2) * glueK t1 τ κ1)) :=
        mul_le_mul gP01 (by linarith) (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) ht1
      have g2 : frobNorm (((cay (c x2 • icay H2) : SU2) : M2) - (cay (c x • icay H0) : M2))
          * frobNorm (((cay (c x3 • icay H3) : SU2) : M2) - (cay (c x2 • icay H2) : M2))
          ≤ ((9 / 2) * glueK t1 τ κ1) * ((9 / 2) * glueK t1 τ κ1) :=
        mul_le_mul kμ kν' (frobNorm_nonneg _) (by positivity)
      unfold glueT2
      linarith

end AdalyFormal.M2Glue2

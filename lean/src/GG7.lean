import GG6

/-!
# GG7 -- the switch lemma: gluing across a straight collar (m2_glue2, 2026-10-15)

`φ` a real coordinate with `φ(x + μ) = φ x + [μ = σ]` on `D`, collar `a ≤ φ ≤ a + w`, cut-off
`c = S((φ − a)/w)`.  If `g_P` is a chart on `D ∩ {φ ≤ a + w + 2}`, `g_Q` on `D ∩ {φ ≥ a − 2}`, and the transition is
`τ`-close to `1` on the strip, then `gglue g_P g_Q c` is a chart on `D` at `glueT1/glueT2` with
`κ₁ = 2/w + 8/w²`, `κ₂ = 32/w²`; it equals `g_P` on `φ ≤ a` and `g_Q` on `φ ≥ a + w`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

noncomputable def kap1 (w : ℝ) : ℝ := 2 / w + 8 / w ^ 2
noncomputable def kap2 (w : ℝ) : ℝ := 32 / w ^ 2

noncomputable def cutS (φ : PeriodicLatticeSite L → ℝ) (a w : ℝ) (x : PeriodicLatticeSite L) : ℝ :=
  stepS ((φ x - a) / w)

theorem cutS_zero {φ : PeriodicLatticeSite L → ℝ} {a w : ℝ} (hw : 0 < w) {x : PeriodicLatticeSite L}
    (h : φ x ≤ a) : cutS φ a w x = 0 :=
  stepS_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)

theorem cutS_one {φ : PeriodicLatticeSite L → ℝ} {a w : ℝ} (hw : 0 < w) {x : PeriodicLatticeSite L}
    (h : a + w ≤ φ x) : cutS φ a w x = 1 :=
  stepS_of_one_le (by rw [le_div_iff₀ hw]; linarith)

theorem delta_abs (μ σ : Fin 3) : |(if μ = σ then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> norm_num

theorem delta_nonneg (μ σ : Fin 3) : 0 ≤ (if μ = σ then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

theorem delta_le_one (μ σ : Fin 3) : (if μ = σ then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

/-- **the switch lemma.** -/
theorem switch_glue {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2} {D : Set (PeriodicLatticeSite L)}
    {φ : PeriodicLatticeSite L → ℝ} {σ : Fin 3} {a w t1 t2 τ : ℝ} (hw : 1 ≤ w) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2)
    (hφ : ∀ x μ, x ∈ D → periodicLatticeShift x μ ∈ D →
      φ (periodicLatticeShift x μ) = φ x + (if μ = σ then 1 else 0))
    (hP : GChart U gP {x | x ∈ D ∧ φ x ≤ a + w + 2} t1 t2)
    (hQ : GChart U gQ {x | x ∈ D ∧ a - 2 ≤ φ x} t1 t2)
    (hh : ∀ x, x ∈ D → a - 2 ≤ φ x → φ x ≤ a + w + 2 → frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ τ) :
    GChart U (gglue gP gQ (cutS φ a w)) D (glueT1 t1 τ (kap1 w)) (glueT2 t1 t2 τ (kap1 w) (kap2 w)) := by
  have hw0 : 0 < w := by linarith
  have hk1 : 0 ≤ kap1 w := by unfold kap1; positivity
  have hk2 : 0 ≤ kap2 w := by unfold kap2; positivity
  -- cut-off differences
  have dc1 : ∀ x ν, x ∈ D → periodicLatticeShift x ν ∈ D →
      |cutS φ a w (periodicLatticeShift x ν) - cutS φ a w x| ≤ kap1 w := by
    intro x ν hx hxν
    unfold cutS kap1
    have h := stepS_lip ((φ x - a) / w) ((φ (periodicLatticeShift x ν) - a) / w)
    have e : (φ (periodicLatticeShift x ν) - a) / w - (φ x - a) / w = (if ν = σ then (1 : ℝ) else 0) / w := by
      rw [hφ x ν hx hxν]; ring
    rw [e] at h
    have d := delta_abs ν σ
    have h1 : |(if ν = σ then (1 : ℝ) else 0) / w| ≤ 1 / w := by
      rw [abs_div, abs_of_pos hw0]; exact div_le_div_of_nonneg_right d hw0.le
    have h2 : ((if ν = σ then (1 : ℝ) else 0) / w) ^ 2 ≤ 1 / w ^ 2 := by
      rw [div_pow]; apply div_le_div_of_nonneg_right _ (by positivity)
      have := delta_nonneg ν σ; have := delta_le_one ν σ; nlinarith
    have q1 : 2 / w = 2 * (1 / w) := by ring
    have q2 : 8 / w ^ 2 = 8 * (1 / w ^ 2) := by ring
    linarith
  have dc2 : ∀ x μ ν, x ∈ D → periodicLatticeShift x ν ∈ D → periodicLatticeShift x μ ∈ D →
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D →
      |cutS φ a w (periodicLatticeShift (periodicLatticeShift x μ) ν) - cutS φ a w (periodicLatticeShift x μ)
        - cutS φ a w (periodicLatticeShift x ν) + cutS φ a w x| ≤ kap2 w := by
    intro x μ ν h0 h1 h2 h3
    unfold cutS kap2
    have h := stepS_second ((φ x - a) / w) ((φ (periodicLatticeShift x ν) - a) / w)
      ((φ (periodicLatticeShift x μ) - a) / w) ((φ (periodicLatticeShift (periodicLatticeShift x μ) ν) - a) / w)
    rw [hφ _ ν h2 h3, hφ x ν h0 h1, hφ x μ h0 h2] at h ⊢
    have e1 : (φ x + (if μ = σ then (1 : ℝ) else 0) + (if ν = σ then 1 else 0) - a) / w
        - (φ x + (if μ = σ then (1 : ℝ) else 0) - a) / w - (φ x + (if ν = σ then 1 else 0) - a) / w
        + (φ x - a) / w = 0 := by ring
    have e2 : (φ x + (if μ = σ then (1 : ℝ) else 0) - a) / w - (φ x - a) / w = (if μ = σ then (1 : ℝ) else 0) / w := by
      ring
    have e3 : (φ x + (if ν = σ then (1 : ℝ) else 0) - a) / w - (φ x - a) / w = (if ν = σ then (1 : ℝ) else 0) / w := by
      ring
    have e4 : (φ x + (if μ = σ then (1 : ℝ) else 0) + (if ν = σ then 1 else 0) - a) / w
        - (φ x + (if μ = σ then (1 : ℝ) else 0) - a) / w = (if ν = σ then (1 : ℝ) else 0) / w := by ring
    rw [e1, e2, e3, e4] at h
    have dm := delta_abs μ σ; have dn := delta_abs ν σ
    have hm : |(if μ = σ then (1 : ℝ) else 0) / w| ≤ 1 / w := by
      rw [abs_div, abs_of_pos hw0]; exact div_le_div_of_nonneg_right dm hw0.le
    have hn : |(if ν = σ then (1 : ℝ) else 0) / w| ≤ 1 / w := by
      rw [abs_div, abs_of_pos hw0]; exact div_le_div_of_nonneg_right dn hw0.le
    have hn2 : ((if ν = σ then (1 : ℝ) else 0) / w) ^ 2 ≤ 1 / w ^ 2 := by
      rw [div_pow]; apply div_le_div_of_nonneg_right _ (by positivity)
      have := delta_nonneg ν σ; have := delta_le_one ν σ; nlinarith
    have hmn : |(if μ = σ then (1 : ℝ) else 0) / w| * |(if ν = σ then (1 : ℝ) else 0) / w| ≤ 1 / w * (1 / w) :=
      mul_le_mul hm hn (abs_nonneg _) (by positivity)
    simp only [abs_zero, mul_zero, zero_add] at h
    have q0 : 1 / w * (1 / w) = 1 / w ^ 2 := by ring
    have q3 : 32 / w ^ 2 = 32 * (1 / w ^ 2) := by ring
    linarith
  refine glue_two (DP := {x | x ∈ D ∧ φ x ≤ a + w + 2}) (DQ := {x | x ∈ D ∧ a - 2 ≤ φ x}) ht1 ht2 hτ0 hτ2 hk1 hk2
    hP hQ (fun x hp hq => hh x hp.1 hq.2 hp.2) (fun x _ => stepS_mem _) dc1 dc2 ?_ ?_
  · intro x ν hx hxν
    have e := hφ x ν hx hxν
    have d0 := delta_nonneg ν σ; have d1 := delta_le_one ν σ
    by_cases hlo : φ (periodicLatticeShift x ν) ≤ a
    · left
      exact ⟨cutS_zero hw0 (by linarith), cutS_zero hw0 hlo, ⟨hx, by linarith⟩, ⟨hxν, by linarith⟩⟩
    by_cases hhi : a + w ≤ φ x
    · right; left
      exact ⟨cutS_one hw0 hhi, cutS_one hw0 (by linarith), ⟨hx, by linarith⟩, ⟨hxν, by linarith⟩⟩
    · right; right
      push_neg at hlo hhi
      exact ⟨⟨hx, by linarith⟩, ⟨hx, by linarith⟩, ⟨hxν, by linarith⟩, ⟨hxν, by linarith⟩⟩
  · intro x μ ν h0 h1 h2 h3
    have e1 := hφ x ν h0 h1; have e2 := hφ x μ h0 h2; have e3 := hφ _ ν h2 h3
    have dm0 := delta_nonneg μ σ; have dm1 := delta_le_one μ σ
    have dn0 := delta_nonneg ν σ; have dn1 := delta_le_one ν σ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_setOf_eq]
    by_cases hlo : φ (periodicLatticeShift (periodicLatticeShift x μ) ν) ≤ a
    · left
      refine ⟨⟨cutS_zero hw0 (by linarith), h0, by linarith⟩, ⟨cutS_zero hw0 (by linarith), h1, by linarith⟩,
        ⟨cutS_zero hw0 (by linarith), h2, by linarith⟩, ⟨cutS_zero hw0 hlo, h3, by linarith⟩⟩
    by_cases hhi : a + w ≤ φ x
    · right; left
      refine ⟨⟨cutS_one hw0 hhi, h0, by linarith⟩, ⟨cutS_one hw0 (by linarith), h1, by linarith⟩,
        ⟨cutS_one hw0 (by linarith), h2, by linarith⟩, ⟨cutS_one hw0 (by linarith), h3, by linarith⟩⟩
    · right; right
      push_neg at hlo hhi
      refine ⟨⟨⟨h0, by linarith⟩, ⟨h0, by linarith⟩⟩, ⟨⟨h1, by linarith⟩, ⟨h1, by linarith⟩⟩,
        ⟨⟨h2, by linarith⟩, ⟨h2, by linarith⟩⟩, ⟨⟨h3, by linarith⟩, ⟨h3, by linarith⟩⟩⟩

theorem switch_low {gP gQ : PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a w : ℝ} (hw : 0 < w)
    {x : PeriodicLatticeSite L} (h : φ x ≤ a) : gglue gP gQ (cutS φ a w) x = gP x :=
  gglue_of_zero (cutS_zero hw h)

theorem switch_high {gP gQ : PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a w : ℝ} (hw : 0 < w)
    {x : PeriodicLatticeSite L} (h : a + w ≤ φ x) : gglue gP gQ (cutS φ a w) x = gQ x :=
  gglue_of_one (cutS_one hw h)

end AdalyFormal.M2Glue2

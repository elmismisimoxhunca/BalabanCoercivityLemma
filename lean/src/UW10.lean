import UW9

/-!
# UW10 -- scaled constants of the clause-2 stacking step and stacking along one direction (lane unif_20261016)

* `step_scaled` : if the old/new chart constants are `≤ A w Y` (clause 1) and `≤ A Y` (clause 2, plaquette), and
  `A w² Y ≤ 1`, then the glued chart of `UW9` has constants `≤ Kst · A w Y` and `≤ Kst · A Y`, `Kst = 10⁷`.
* `Ch W S B w Y` : some gauge has clause 1 at `B w Y` and clause 2 at `B Y` on `S`.
* `stack_dir` : `N + 1` consecutive slabs of thickness `s ≥ 2` along `σ`, each with a chart at `A`, and the plaquette bound
  `A Y` on their union, give a chart on the union at `Kst^N · A`, provided `Kst^N A w² Y ≤ 1`.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false

namespace AdalyFormal.UnifLane.Z

open Matrix
open AdalyFormal.M2Glue3 (Z3 ev)
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

/-- the per-step growth constant. -/
noncomputable def Kst : ℝ := 10 ^ 7

theorem one_le_Kst : (1 : ℝ) ≤ Kst := by unfold Kst; norm_num

/-- **the constants of one stacking step, scaled.** -/
theorem step_scaled {o1 o2 n1 n2 η A Y : ℝ} {w : ℕ} (hw : 1 ≤ w) (hY : 0 ≤ Y) (hA : 0 ≤ A)
    (hsm : A * w * w * Y ≤ 1) (ho1 : 0 ≤ o1) (hn1 : 0 ≤ n1) (hη : 0 ≤ η) (ho2 : 0 ≤ o2) (hn2 : 0 ≤ n2)
    (bo1 : o1 ≤ A * w * Y) (bn1 : n1 ≤ A * w * Y) (bo2 : o2 ≤ A * Y) (bn2 : n2 ≤ A * Y) (bη : η ≤ A * Y) :
    T1st o1 o2 n1 n2 η w ≤ Kst * (A * w * Y) ∧ T2st o1 o2 n1 n2 η w ≤ Kst * (A * Y) := by
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hw0 : (0 : ℝ) < w := by linarith
  set a := A * w * Y with ha
  set b := A * Y with hb
  have hb0 : 0 ≤ b := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hab : b ≤ a := by
    have : b * 1 ≤ b * w := mul_le_mul_of_nonneg_left hw' hb0
    have e : b * w = a := by rw [ha, hb]; ring
    linarith
  have hwb : (w : ℝ) * b = a := by rw [ha, hb]; ring
  have haa : a * a ≤ b := by
    have e : a * a = (A * w * w * Y) * b := by rw [ha, hb]; ring
    rw [e]; exact mul_le_of_le_one_left hb0 hsm
  have hK0 : K0c o1 n1 η ≤ 5 * a := by unfold K0c; linarith
  have hK00 : 0 ≤ K0c o1 n1 η := by unfold K0c; positivity
  have hg1 : g01c o1 n1 η ≤ 6 * a := by unfold g01c; linarith
  have hg10 : 0 ≤ g01c o1 n1 η := by unfold g01c; positivity
  have hnk : n1 * K0c o1 n1 η ≤ a * (5 * a) := mul_le_mul bn1 hK0 hK00 ha0
  have hg2 : g02c o1 o2 n1 n2 η ≤ 28 * b := by unfold g02c; nlinarith
  have hVB : VBc o1 n1 ≤ 2 * a := by unfold VBc; linarith
  have hVB0 : 0 ≤ VBc o1 n1 := by unfold VBc; positivity
  have hDv : Dvc o1 o2 n1 n2 η ≤ 58 * b := by unfold Dvc; linarith
  have hwD : 8 * (w : ℝ) * Dvc o1 o2 n1 n2 η ≤ 464 * a := by
    have := mul_le_mul_of_nonneg_left hDv (show (0 : ℝ) ≤ 8 * w by positivity)
    nlinarith
  have hF1 : F1c o1 o2 n1 n2 η w ≤ 506 * a := by unfold F1c; linarith
  have hF10 : 0 ≤ F1c o1 o2 n1 n2 η w := by
    unfold F1c Dvc VBc g02c K0c; positivity
  have hdiv : 84 * VBc o1 n1 / w ≤ 168 * b := by
    rw [div_le_iff₀ hw0]; nlinarith
  have hF2 : F2c o1 o2 n1 n2 η w ≤ 10956 * b := by unfold F2c; linarith
  have hC1 : Cy1c o1 o2 n1 n2 η w ≤ 2277 * a := by unfold Cy1c; linarith
  have hC10 : 0 ≤ Cy1c o1 o2 n1 n2 η w := by unfold Cy1c; positivity
  have hFF : F1c o1 o2 n1 n2 η w * F1c o1 o2 n1 n2 η w ≤ (506 * a) * (506 * a) := mul_le_mul hF1 hF1 hF10 (by positivity)
  have hC2 : Cy2c o1 o2 n1 n2 η w ≤ 3505788 * b := by unfold Cy2c; nlinarith
  have hoo : o1 * o1 ≤ a * a := mul_le_mul bo1 bo1 ho1 ha0
  have hgc : g01c o1 n1 η * (2 * Cy1c o1 o2 n1 n2 η w) ≤ (6 * a) * (2 * (2277 * a)) :=
    mul_le_mul hg1 (by linarith) (by positivity) (by positivity)
  have hcc : Cy1c o1 o2 n1 n2 η w * Cy1c o1 o2 n1 n2 η w ≤ (2277 * a) * (2277 * a) := mul_le_mul hC1 hC1 hC10 (by positivity)
  have hK : Kst = 10 ^ 7 := rfl
  constructor
  · unfold T1st; rw [hK]; nlinarith
  · unfold T2st; rw [hK]; nlinarith

theorem holB_mono {W : Z3 → Fin 3 → SU2} {D D' : Set Z3} {η η' : ℝ} (h : HolB W D η) (hD : D' ⊆ D) (hη : η ≤ η') :
    HolB W D' η' := fun q μ ν a b c d => (h q μ ν (hD a) (hD b) (hD c) (hD d)).trans hη

/-- a chart at level `B`. -/
def Ch (W : Z3 → Fin 3 → SU2) (S : Set Z3) (B : ℝ) (w : ℕ) (Y : ℝ) : Prop :=
  ∃ G : Z3 → SU2, C1 W G S (B * w * Y) ∧ C2 W G S (B * Y)

theorem Ch.mono {W : Z3 → Fin 3 → SU2} {S S' : Set Z3} {B B' : ℝ} {w : ℕ} {Y : ℝ} (h : Ch W S B w Y) (hS : S' ⊆ S)
    (hB : B ≤ B') (hY : 0 ≤ Y) : Ch W S' B' w Y := by
  obtain ⟨G, h1, h2⟩ := h
  have hwY : (0 : ℝ) ≤ w * Y := by positivity
  have e1 : B * w * Y ≤ B' * w * Y := by nlinarith
  exact ⟨G, h1.mono hS e1, h2.mono hS (mul_le_mul_of_nonneg_right hB hY)⟩

/-- **stacking `N + 1` slabs along `σ`.** -/
theorem stack_dir (W : Z3 → Fin 3 → SU2) {σ τ₁ τ₂ : Fin 3} (hτ : ∀ ν, ν ≠ σ → ν = τ₁ ∨ ν = τ₂) (h1σ : τ₁ ≠ σ)
    (h2σ : τ₂ ≠ σ) {lo hi : Z3} (hlh : ∀ ν, ν ≠ σ → lo ν ≤ hi ν) {s a0 : ℤ} (hs : 2 ≤ s) {w : ℕ} (hw : 1 ≤ w)
    {Y A : ℝ} (hY : 0 ≤ Y) (hA : 0 ≤ A) :
    ∀ N : ℕ, Kst ^ N * A * w * w * Y ≤ 1 →
      (∀ i : ℕ, i ≤ N → Ch W (SlabS σ lo hi (a0 + (i : ℤ) * s) (a0 + ((i : ℤ) + 1) * s)) A w Y) →
      HolB W (SlabS σ lo hi a0 (a0 + ((N : ℤ) + 1) * s)) (A * Y) →
      Ch W (SlabS σ lo hi a0 (a0 + ((N : ℤ) + 1) * s)) (Kst ^ N * A) w Y := by
  have hK := one_le_Kst
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  intro N
  induction N with
  | zero =>
    intro _ hp _
    obtain ⟨G, h1, h2⟩ := hp 0 le_rfl
    refine ⟨G, ?_, ?_⟩
    · simpa using h1
    · simpa using h2
  | succ N ih =>
    intro hsm hp hH
    have hKN : 0 ≤ Kst ^ N * A := by positivity
    have hsm' : Kst ^ N * A * w * w * Y ≤ 1 := by
      have e : Kst ^ (N + 1) * A * w * w * Y = Kst * (Kst ^ N * A * w * w * Y) := by ring
      have h0 : 0 ≤ Kst ^ N * A * w * w * Y := by positivity
      nlinarith
    have hNs : (0 : ℤ) ≤ (N : ℤ) := by positivity
    have hsub : SlabS σ lo hi a0 (a0 + ((N : ℤ) + 1) * s) ⊆ SlabS σ lo hi a0 (a0 + (((N + 1 : ℕ) : ℤ) + 1) * s) :=
      fun p hp => slab_mono le_rfl (by push_cast; nlinarith) hp
    obtain ⟨Go, hO1, hO2⟩ := ih hsm' (fun i hi => hp i (by omega)) (holB_mono hH hsub le_rfl)
    obtain ⟨Gn, hN1, hN2⟩ := hp (N + 1) le_rfl
    have e1 : (((N + 1 : ℕ) : ℤ)) = (N : ℤ) + 1 := by push_cast; ring
    rw [e1] at hN1 hN2 hH ⊢
    have hAY : 0 ≤ A * Y := by positivity
    have hAwY : 0 ≤ A * w * Y := by positivity
    -- constants
    set o1 := Kst ^ N * A * w * Y
    set o2 := Kst ^ N * A * Y
    have ho1 : 0 ≤ o1 := by positivity
    have ho2 : 0 ≤ o2 := by positivity
    have hAo2 : A * Y ≤ o2 := by
      have : (1 : ℝ) ≤ Kst ^ N := one_le_pow₀ hK
      nlinarith
    have hAo1 : A * w * Y ≤ o1 := by
      have : (1 : ℝ) ≤ Kst ^ N := one_le_pow₀ hK
      have e : o1 = Kst ^ N * (A * w * Y) := by ring
      rw [e]; nlinarith
    have hN1' : C1 W Gn (SlabS σ lo hi (a0 + ((N : ℤ) + 1) * s) (a0 + ((N : ℤ) + 1 + 1) * s)) o1 :=
      hN1.mono subset_rfl hAo1
    have hN2' : C2 W Gn (SlabS σ lo hi (a0 + ((N : ℤ) + 1) * s) (a0 + ((N : ℤ) + 1 + 1) * s)) o2 :=
      hN2.mono subset_rfl hAo2
    have hH' := holB_mono hH subset_rfl hAo2
    have hc0 : a0 + 2 ≤ a0 + ((N : ℤ) + 1) * s := by nlinarith
    have hch : a0 + ((N : ℤ) + 1) * s + 2 ≤ a0 + ((N : ℤ) + 1 + 1) * s := by nlinarith
    have hsmall : o1 + o1 ≤ 2 := by
      have : o1 ≤ Kst ^ N * A * w * w * Y := by
        have e : Kst ^ N * A * w * w * Y = o1 * w := by ring
        rw [e]; nlinarith
      linarith
    have c1 := stack2_c1 hc0 hch hO1 hO2 hN1' hN2' hH' ho1 ho1 ho2 ho2 ho2 hsmall hlh hτ h1σ h2σ hw
    have c2 := stack2_c2 hc0 hch hO1 hO2 hN1' hN2' hH' ho1 ho1 ho2 ho2 ho2 hsmall hlh hτ h1σ h2σ hw
    obtain ⟨b1, b2⟩ := step_scaled (A := Kst ^ N * A) hw hY hKN hsm' ho1 ho1 ho2 ho2 ho2 le_rfl le_rfl le_rfl le_rfl le_rfl
    refine ⟨_, c1.mono subset_rfl (b1.trans (le_of_eq (by ring))), c2.mono subset_rfl (b2.trans (le_of_eq (by ring)))⟩

end AdalyFormal.UnifLane.Z

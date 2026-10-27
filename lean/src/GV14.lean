import GV13

/-!
# GV14 -- iterated band gluing without compounding constants (InterfaceCharts item (c)) (m2_glue3, 2026-10-15)

Charts `g 0, g 1, …` along a coordinate `φ` (`φ(x + e_μ) = φ x + [μ = σ]` on `D`), chart `k` valid on the slab
`Slab k = D ∩ {a_k − 2 ≤ φ ≤ a_{k+1} + w + 2}` (no lower bound for `k = 0`), consecutive transitions `τ`-close on the
collar bands, collars separated (`a_k + w + 4 ≤ a_{k+1}`).  `sweepA N` glues them in order with the GG7 cut-offs.
**`sweep_glue`**: for EVERY `N`, `sweepA N` is a `GChart` on `D ∩ {φ ≤ a_{N+1} + w + 2}` at the SAME constants
`(glueT1 t₁ τ κ₁(w), glueT2 t₁ t₂ τ κ₁(w) κ₂(w))` — no growth with `N`.  Also `sweepA N = g N` beyond the last collar.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2Glue3

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.M2Glue2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

/-- a chart on `D` from charts on three sets covering every bond and stencil of `D`. -/
theorem GChart.union3 {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {D E1 E2 E3 : Set (PeriodicLatticeSite L)}
    {t1 t2 : ℝ} (h1 : GChart U g E1 t1 t2) (h2 : GChart U g E2 t1 t2) (h3 : GChart U g E3 t1 t2)
    (hb : ∀ x ν, x ∈ D → periodicLatticeShift x ν ∈ D →
      (x ∈ E1 ∧ periodicLatticeShift x ν ∈ E1) ∨ (x ∈ E2 ∧ periodicLatticeShift x ν ∈ E2) ∨
      (x ∈ E3 ∧ periodicLatticeShift x ν ∈ E3))
    (hs : ∀ x μ ν, x ∈ D → periodicLatticeShift x ν ∈ D → periodicLatticeShift x μ ∈ D →
      periodicLatticeShift (periodicLatticeShift x μ) ν ∈ D →
      (x ∈ E1 ∧ periodicLatticeShift x ν ∈ E1 ∧ periodicLatticeShift x μ ∈ E1 ∧
          periodicLatticeShift (periodicLatticeShift x μ) ν ∈ E1) ∨
      (x ∈ E2 ∧ periodicLatticeShift x ν ∈ E2 ∧ periodicLatticeShift x μ ∈ E2 ∧
          periodicLatticeShift (periodicLatticeShift x μ) ν ∈ E2) ∨
      (x ∈ E3 ∧ periodicLatticeShift x ν ∈ E3 ∧ periodicLatticeShift x μ ∈ E3 ∧
          periodicLatticeShift (periodicLatticeShift x μ) ν ∈ E3)) :
    GChart U g D t1 t2 := by
  refine ⟨fun x ν hx hxν => ?_, fun x μ ν a b c d => ?_⟩
  · rcases hb x ν hx hxν with ⟨p, q⟩ | ⟨p, q⟩ | ⟨p, q⟩
    · exact h1.1 x ν p q
    · exact h2.1 x ν p q
    · exact h3.1 x ν p q
  · rcases hs x μ ν a b c d with ⟨p, q, r, s⟩ | ⟨p, q, r, s⟩ | ⟨p, q, r, s⟩
    · exact h1.2 x μ ν p q r s
    · exact h2.2 x μ ν p q r s
    · exact h3.2 x μ ν p q r s

noncomputable def sweepA (g : ℕ → PeriodicLatticeSite L → SU2) (φ : PeriodicLatticeSite L → ℝ) (a : ℕ → ℝ) (w : ℝ) :
    ℕ → PeriodicLatticeSite L → SU2
  | 0 => g 0
  | n + 1 => gglue (sweepA g φ a w n) (g (n + 1)) (cutS φ (a (n + 1)) w)

def Slab (D : Set (PeriodicLatticeSite L)) (φ : PeriodicLatticeSite L → ℝ) (a : ℕ → ℝ) (w : ℝ) (k : ℕ) :
    Set (PeriodicLatticeSite L) :=
  {x | x ∈ D ∧ (k = 0 ∨ a k - 2 ≤ φ x) ∧ φ x ≤ a (k + 1) + w + 2}

theorem sweepA_high {g : ℕ → PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) : ∀ N x, (N = 0 ∨ a N + w ≤ φ x) → sweepA g φ a w N x = g N x := by
  intro N x h
  cases N with
  | zero => rfl
  | succ n =>
    rcases h with h | h
    · exact absurd h (Nat.succ_ne_zero n)
    · exact switch_high hw h

theorem sweepA_low {g : ℕ → PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) (N : ℕ) (x : PeriodicLatticeSite L) (h : φ x ≤ a (N + 1)) :
    sweepA g φ a w (N + 1) x = sweepA g φ a w N x :=
  switch_low hw h

theorem glueT_ge {t1 t2 τ w : ℝ} (hw : 0 < w) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hτ : 0 ≤ τ) :
    t1 ≤ glueT1 t1 τ (kap1 w) ∧ t2 ≤ glueT2 t1 t2 τ (kap1 w) (kap2 w) := by
  have hk1 : 0 ≤ kap1 w := by unfold kap1; positivity
  have hk2 : 0 ≤ kap2 w := by unfold kap2; positivity
  have hK : 0 ≤ glueK t1 τ (kap1 w) := by unfold glueK; positivity
  constructor
  · unfold glueT1; linarith
  · unfold glueT2
    have : 0 ≤ t1 * (2 * ((9 / 2) * glueK t1 τ (kap1 w))) := by positivity
    have : 0 ≤ ((9 / 2) * glueK t1 τ (kap1 w)) * ((9 / 2) * glueK t1 τ (kap1 w)) := by positivity
    have : 0 ≤ (9 / 2) * (kap2 w * τ + 8 * kap1 w * t1 + 2 * (2 * t2 + 6 * t1 ^ 2) + 16 * t1 ^ 2) := by positivity
    have : 0 ≤ (27 / 4) * (2 * glueK t1 τ (kap1 w)) * glueK t1 τ (kap1 w) := by positivity
    linarith

/-- **the sweep: non-compounding iterated band gluing.** -/
theorem sweep_glue {U : LinkCfg L} {D : Set (PeriodicLatticeSite L)} {φ : PeriodicLatticeSite L → ℝ} {σ : Fin 3}
    {a : ℕ → ℝ} {w t1 t2 τ : ℝ} (hw : 1 ≤ w) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2)
    (hφ : ∀ x μ, x ∈ D → periodicLatticeShift x μ ∈ D →
      φ (periodicLatticeShift x μ) = φ x + (if μ = σ then 1 else 0))
    (hgap : ∀ k, a k + w + 4 ≤ a (k + 1))
    {g : ℕ → PeriodicLatticeSite L → SU2} (hg : ∀ k, GChart U (g k) (Slab D φ a w k) t1 t2)
    (hτ : ∀ k x, x ∈ D → a (k + 1) - 2 ≤ φ x → φ x ≤ a (k + 1) + w + 2 →
      frobNorm (((trans (g k) (g (k + 1)) x : SU2) : M2) - 1) ≤ τ) :
    ∀ N, GChart U (sweepA g φ a w N) {x | x ∈ D ∧ φ x ≤ a (N + 1) + w + 2}
      (glueT1 t1 τ (kap1 w)) (glueT2 t1 t2 τ (kap1 w) (kap2 w)) := by
  have hw0 : 0 < w := by linarith
  obtain ⟨hT1, hT2⟩ := glueT_ge hw0 ht1 ht2 hτ0
  -- φ along bonds / stencils of `D`
  have d0 : ∀ μ : Fin 3, (0 : ℝ) ≤ (if μ = σ then 1 else 0) ∧ (if μ = σ then (1 : ℝ) else 0) ≤ 1 :=
    fun μ => ⟨delta_nonneg μ σ, delta_le_one μ σ⟩
  intro N
  induction N with
  | zero =>
    refine (hg 0).mono (fun x hx => ⟨hx.1, Or.inl rfl, hx.2⟩) hT1 hT2
  | succ N ih =>
    set A := sweepA g φ a w N
    set c := cutS φ (a (N + 1)) w
    have hA0 : ∀ x, (N = 0 ∨ a N + w ≤ φ x) → A x = g N x := sweepA_high hw0 N
    have g1 := hgap N; have g2 := hgap (N + 1)
    -- the window around collar `N+1`
    set W := {x | x ∈ D ∧ a (N + 1) - 3 ≤ φ x ∧ φ x ≤ a (N + 1) + w + 3}
    have hAW : ∀ x ∈ W, A x = g N x := by
      intro x hx
      exact hA0 x (by rcases Nat.eq_zero_or_pos N with h0 | h0
                      · exact Or.inl h0
                      · exact Or.inr (by linarith [hx.2.1]))
    have hPW : GChart U A {x | x ∈ W ∧ φ x ≤ a (N + 1) + w + 2} t1 t2 := by
      refine ((hg N).mono (fun x hx => ⟨hx.1.1, Or.inr (by linarith [hx.1.2.1]), by linarith [hx.2]⟩) le_rfl
        le_rfl).congr (fun x hx => hAW x hx.1)
    have hQW : GChart U (g (N + 1)) {x | x ∈ W ∧ a (N + 1) - 2 ≤ φ x} t1 t2 :=
      (hg (N + 1)).mono (fun x hx => ⟨hx.1.1, Or.inr hx.2, by linarith [hx.1.2.2]⟩) le_rfl le_rfl
    have hW := switch_glue (D := W) (σ := σ) hw ht1 ht2 hτ0 hτ2
      (fun x μ hx hxμ => hφ x μ hx.1 hxμ.1) hPW hQW
      (fun x hx h1 h2 => by
        show frobNorm (((trans A (g (N + 1)) x : SU2) : M2) - 1) ≤ τ
        have e : trans A (g (N + 1)) x = trans (g N) (g (N + 1)) x := by
          simp only [M2Glue2.trans, hAW x hx]
        rw [e]; exact hτ N x hx.1 h1 h2)
    -- the three regions
    have R1 : GChart U (sweepA g φ a w (N + 1)) {x | x ∈ D ∧ φ x ≤ a (N + 1)}
        (glueT1 t1 τ (kap1 w)) (glueT2 t1 t2 τ (kap1 w) (kap2 w)) :=
      (ih.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) le_rfl le_rfl).congr
        (fun x hx => sweepA_low hw0 N x hx.2)
    have R3 : GChart U (sweepA g φ a w (N + 1)) {x | x ∈ D ∧ a (N + 1) + w ≤ φ x ∧ φ x ≤ a (N + 2) + w + 2}
        (glueT1 t1 τ (kap1 w)) (glueT2 t1 t2 τ (kap1 w) (kap2 w)) :=
      ((hg (N + 1)).mono (fun x hx => ⟨hx.1, Or.inr (by linarith [hx.2.1]), hx.2.2⟩) hT1 hT2).congr
        (fun x hx => sweepA_high hw0 (N + 1) x (Or.inr hx.2.1))
    refine GChart.union3 R1 hW R3 ?_ ?_
    · intro x ν hx hxν
      have e := hφ x ν hx.1 hxν.1
      obtain ⟨d1, d2⟩ := d0 ν
      by_cases h1 : φ (periodicLatticeShift x ν) ≤ a (N + 1)
      · left; exact ⟨⟨hx.1, by linarith⟩, ⟨hxν.1, h1⟩⟩
      by_cases h2 : a (N + 1) + w ≤ φ x
      · right; right
        exact ⟨⟨hx.1, h2, hx.2⟩, ⟨hxν.1, by linarith, hxν.2⟩⟩
      · right; left
        push Not at h1 h2
        exact ⟨⟨hx.1, by linarith, by linarith⟩, ⟨hxν.1, by linarith, by linarith⟩⟩
    · intro x μ ν h0 h1 h2 h3
      have e1 := hφ x ν h0.1 h1.1; have e2 := hφ x μ h0.1 h2.1; have e3 := hφ _ ν h2.1 h3.1
      obtain ⟨dν1, dν2⟩ := d0 ν; obtain ⟨dμ1, dμ2⟩ := d0 μ
      by_cases k1 : φ (periodicLatticeShift (periodicLatticeShift x μ) ν) ≤ a (N + 1)
      · left
        exact ⟨⟨h0.1, by linarith⟩, ⟨h1.1, by linarith⟩, ⟨h2.1, by linarith⟩, ⟨h3.1, k1⟩⟩
      by_cases k2 : a (N + 1) + w ≤ φ x
      · right; right
        exact ⟨⟨h0.1, k2, h0.2⟩, ⟨h1.1, by linarith, h1.2⟩, ⟨h2.1, by linarith, h2.2⟩, ⟨h3.1, by linarith, h3.2⟩⟩
      · right; left
        push Not at k1 k2
        exact ⟨⟨h0.1, by linarith, by linarith⟩, ⟨h1.1, by linarith, by linarith⟩, ⟨h2.1, by linarith, by linarith⟩,
          ⟨h3.1, by linarith, by linarith⟩⟩

/-- beyond the last collar the sweep is the last chart (used to continue sweeps). -/
theorem sweep_last {g : ℕ → PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) (N : ℕ) (x : PeriodicLatticeSite L) (h : a N + w ≤ φ x) : sweepA g φ a w N x = g N x :=
  sweepA_high hw N x (Or.inr h)

/-- before collar `N+1` nothing changes any more. -/
theorem sweep_stable {g : ℕ → PeriodicLatticeSite L → SU2} {φ : PeriodicLatticeSite L → ℝ} {a : ℕ → ℝ} {w : ℝ}
    (hw : 0 < w) (hmono : ∀ k, a k ≤ a (k + 1)) (N : ℕ) :
    ∀ j x, φ x ≤ a (N + 1) → sweepA g φ a w (N + j) x = sweepA g φ a w N x := by
  intro j
  induction j with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    have hmono' : a (N + 1) ≤ a (N + j + 1) := by
      have : ∀ i, a (N + 1) ≤ a (N + 1 + i) := by
        intro i
        induction i with
        | zero => simp
        | succ i ihi => exact ihi.trans (by rw [← add_assoc]; exact hmono _)
      have := this j
      rwa [show N + 1 + j = N + j + 1 by ring] at this
    rw [show N + (j + 1) = (N + j) + 1 by ring, sweepA_low hw (N + j) x (hx.trans hmono'), ih x hx]

/-- the interpolating factor is close to `1`. -/
theorem kglue_close {gP gQ : PeriodicLatticeSite L → SU2} {c : PeriodicLatticeSite L → ℝ} {x : PeriodicLatticeSite L}
    {τ : ℝ} (hc : 0 ≤ c x ∧ c x ≤ 1) (hh : frobNorm (((trans gP gQ x : SU2) : M2) - 1) ≤ τ) (hτ2 : τ ≤ 2) :
    frobNorm (((kglue gP gQ c x : SU2) : M2) - 1) ≤ (9 / 2) * τ := by
  classical
  have hτ0 : 0 ≤ τ := (AdalyFormal.Balaban.Bch2.frobNorm_nonneg _).trans hh
  unfold kglue
  split_ifs with h1
  · linarith
  · refine (frobNorm_cay_sub_one_le ((isSu2_icay _).smul _)).trans ?_
    rw [AdalyFormal.Balaban.Bch2.frobNorm_smul]
    have hi := frobNorm_icay_le (hh.trans hτ2)
    have ha : |c x| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
    have : |c x| * frobNorm (icay (trans gP gQ x)) ≤ 1 * τ :=
      mul_le_mul ha (hi.trans hh) (AdalyFormal.Balaban.Bch2.frobNorm_nonneg _) (by norm_num)
    linarith

/-- **closeness of the sweep to each of its charts** on that chart's slab (input for the next sweep level). -/
theorem sweep_close {D : Set (PeriodicLatticeSite L)} {φ : PeriodicLatticeSite L → ℝ}
    {a : ℕ → ℝ} {w τ : ℝ} (hw : 1 ≤ w) (hτ0 : 0 ≤ τ) (hτ2 : τ ≤ 2) (hgap : ∀ k, a k + w + 4 ≤ a (k + 1))
    {g : ℕ → PeriodicLatticeSite L → SU2}
    (hτ : ∀ k x, x ∈ D → a (k + 1) - 2 ≤ φ x → φ x ≤ a (k + 1) + w + 2 →
      frobNorm (((trans (g k) (g (k + 1)) x : SU2) : M2) - 1) ≤ τ) :
    ∀ N k x, k ≤ N → x ∈ Slab D φ a w k →
      frobNorm (((trans (g k) (sweepA g φ a w N) x : SU2) : M2) - 1) ≤ (11 / 2) * τ := by
  have hw0 : 0 < w := by linarith
  have hmono : ∀ k, a k ≤ a (k + 1) := fun k => by linarith [hgap k]
  have cm : ∀ k x, 0 ≤ cutS φ (a k) w x ∧ cutS φ (a k) w x ≤ 1 := fun k x => stepS_mem _
  -- the value of the sweep at stage `k` on slab `k`
  have stage : ∀ k x, x ∈ Slab D φ a w k → φ x ≤ a (k + 1) →
      frobNorm (((trans (g k) (sweepA g φ a w k) x : SU2) : M2) - 1) ≤ (11 / 2) * τ := by
    intro k x hx hxk
    cases k with
    | zero =>
      have e : trans (g 0) (sweepA g φ a w 0) x = 1 := by simp [M2Glue2.trans, sweepA]
      rw [e]
      simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]; linarith
    | succ k =>
      have hlo : a (k + 1) - 2 ≤ φ x := by
        rcases hx.2.1 with h | h
        · exact absurd h (Nat.succ_ne_zero k)
        · exact h
      have hprev : sweepA g φ a w k x = g k x :=
        sweepA_high hw0 k x (by rcases Nat.eq_zero_or_pos k with h0 | h0
                                · exact Or.inl h0
                                · exact Or.inr (by linarith [hgap k]))
      have hs : sweepA g φ a w (k + 1) x = kglue (sweepA g φ a w k) (g (k + 1)) (cutS φ (a (k + 1)) w) x * g k x := by
        show gglue _ _ _ x = _; rw [gglue, hprev]
      have ht : trans (sweepA g φ a w k) (g (k + 1)) x = trans (g k) (g (k + 1)) x := by
        simp only [M2Glue2.trans, hprev]
      by_cases hhigh : a (k + 1) + w ≤ φ x
      · have e : trans (g (k + 1)) (sweepA g φ a w (k + 1)) x = 1 := by
          simp [M2Glue2.trans, sweepA_high hw0 (k + 1) x (Or.inr hhigh)]
        rw [e]
        simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]; linarith
      · push Not at hhigh
        have hh := hτ k x hx.1 hlo (by linarith)
        have hk := kglue_close (gP := sweepA g φ a w k) (gQ := g (k + 1)) (cm (k + 1) x) (by rw [ht]; exact hh) hτ2
        have e : trans (g (k + 1)) (sweepA g φ a w (k + 1)) x
            = kglue (sweepA g φ a w k) (g (k + 1)) (cutS φ (a (k + 1)) w) x * (trans (g k) (g (k + 1)) x)⁻¹ := by
          simp only [M2Glue2.trans]; rw [hs]; group
        rw [e]
        refine (frob_mul_sub_one _ _).trans ?_
        rw [frob_inv_sub_one]; linarith
  intro N k x hkN hx
  have hup : φ x ≤ a (k + 1) + w + 2 := hx.2.2
  rcases Nat.eq_or_lt_of_le hkN with rfl | hlt
  · -- `N = k`
    by_cases hlow : φ x ≤ a (k + 1)
    · exact stage k x hx hlow
    · -- past collar `k+1` but `N = k`: the sweep is `g k` there
      push Not at hlow
      have e : trans (g k) (sweepA g φ a w k) x = 1 := by
        have : sweepA g φ a w k x = g k x := sweepA_high hw0 k x (by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · exact Or.inl h0
          · exact Or.inr (by linarith [hgap k]))
        simp [M2Glue2.trans, this]
      rw [e]
      simp [AdalyFormal.Balaban.RMapLipschitz.frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]; linarith
  · -- `N ≥ k+1`: the sweep agrees with stage `k+1` on slab `k`
    have hstab : sweepA g φ a w N x = sweepA g φ a w (k + 1) x := by
      have := sweep_stable (g := g) (φ := φ) hw0 hmono (k + 1) (N - (k + 1)) x (by linarith [hgap (k + 1)])
      rwa [show k + 1 + (N - (k + 1)) = N by omega] at this
    have e0 : trans (g k) (sweepA g φ a w N) x = trans (g k) (sweepA g φ a w (k + 1)) x := by
      simp only [M2Glue2.trans, hstab]
    rw [e0]
    by_cases hlow : φ x ≤ a (k + 1)
    · have e1 : sweepA g φ a w (k + 1) x = sweepA g φ a w k x := sweepA_low hw0 k x hlow
      have e2 : trans (g k) (sweepA g φ a w (k + 1)) x = trans (g k) (sweepA g φ a w k) x := by
        simp only [M2Glue2.trans, e1]
      rw [e2]; exact stage k x hx hlow
    · push Not at hlow
      have hprev : sweepA g φ a w k x = g k x :=
        sweepA_high hw0 k x (by rcases Nat.eq_zero_or_pos k with h0 | h0
                                · exact Or.inl h0
                                · exact Or.inr (by linarith [hgap k]))
      have hh := hτ k x hx.1 (by linarith) hup
      have ht : trans (sweepA g φ a w k) (g (k + 1)) x = trans (g k) (g (k + 1)) x := by
        simp only [M2Glue2.trans, hprev]
      have hk := kglue_close (gP := sweepA g φ a w k) (gQ := g (k + 1)) (cm (k + 1) x) (by rw [ht]; exact hh) hτ2
      have e : trans (g k) (sweepA g φ a w (k + 1)) x = kglue (sweepA g φ a w k) (g (k + 1)) (cutS φ (a (k + 1)) w) x := by
        show _ * _ = _
        show gglue _ _ _ x * (g k x)⁻¹ = _
        rw [gglue, hprev]; group
      rw [e]
      have : 0 ≤ τ := (AdalyFormal.Balaban.Bch2.frobNorm_nonneg _).trans hh
      linarith

end AdalyFormal.M2Glue3

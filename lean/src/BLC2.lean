import BLC1

/-!
# BLC2 -- one sweep level in coordinates, with closeness supplied by constant normalisation (m2_ballcharts, 2026-10-15)

`level_sweep`: charts `g k` (`ZCh` at constants `t₁, t₂` on `Dom k`), every slab point of an integer box `IBox lo hi ⊆ Box r`
in `Dom k`, collars of width `wd` at integer positions `a k` (gaps `≥ wd + 4`) and collar `ℓ¹`-diameter `≤ dm`.  Then one
gauge `G` is a `ZCh` on `{p ∈ IBox lo hi | p_σ ≤ a (N+1) + wd + 2}` at `(glueT1 t₁ τ κ₁(wd), glueT2 t₁ t₂ τ κ₁(wd) κ₂(wd))`,
`τ = dm · 2 t₁` (the constants do not depend on `N`).
Closeness: the charts are normalised by constants in sequence (`normC`), so that the transition `G_{k+1} G_k⁻¹` is `1` at a
base point of collar `k+1`; `trans_zbox` then bounds it by `dm · 2t₁` on the whole collar.  No cocycle condition is used.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace AdalyFormal.M2BallCharts

open AdalyFormal.Target.ClayStatement AdalyFormal.M2Glue3 AdalyFormal.M2Glue2 AdalyFormal.M2GlueGeo
open AdalyFormal.StatementLane AdalyFormal.StatementLane2
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)

variable {L : PeriodicLatticeExtent}

theorem zch_const_mul {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L} {S : Set Z3}
    {a b : ℝ} (h : ZCh U g v S (fun _ => a) (fun _ => b)) (C : SU2) :
    ZCh U (fun x => C * g x) v S (fun _ => a) (fun _ => b) := by
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · rw [gauge_const_mul, frobNorm_conj_sub_one]; exact h.1 p ν hp hpν
  · rw [gauge_const_mul, gauge_const_mul, frobNorm_conj_sub]; exact h.2 p μ ν h0 h1 h2 h3

theorem zch_mono {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L} {S S' : Set Z3}
    {a b a' b' : ℝ} (h : ZCh U g v S (fun _ => a) (fun _ => b)) (hS : S' ⊆ S) (ha : a ≤ a') (hb : b ≤ b') :
    ZCh U g v S' (fun _ => a') (fun _ => b') :=
  ZCh.mono h hS (fun _ _ => ha) (fun _ _ => hb)

/-- a coordinate `ZCh` from a `GChart` on a lifted set (no injectivity). -/
theorem zch_of_lift {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {v : PeriodicLatticeSite L} {S T : Set Z3}
    (q : Z3) {a b : ℝ} (h : GChart U g (lift (iota v q) S) a b) (hT : ∀ p ∈ T, p - q ∈ S) :
    ZCh U g v T (fun _ => a) (fun _ => b) := by
  have e : ∀ p, iota v p = iota (iota v q) (p - q) := by
    intro p; rw [iota_iota]; congr 1; abel
  refine ⟨fun p ν hp hpν => ?_, fun p μ ν h0 h1 h2 h3 => ?_⟩
  · have := h.1 (iota v p) ν (by rw [e p]; exact iota_mem_lift (hT p hp))
      (by rw [iota_shift, e (p + ev ν)]; exact iota_mem_lift (hT _ hpν))
    exact this
  · have := h.2 (iota v p) μ ν (by rw [e p]; exact iota_mem_lift (hT p h0))
      (by rw [iota_shift, e (p + ev ν)]; exact iota_mem_lift (hT _ h1))
      (by rw [iota_shift, e (p + ev μ)]; exact iota_mem_lift (hT _ h2))
      (by rw [iota_shift2, e (p + ev μ + ev ν)]; exact iota_mem_lift (hT _ h3))
    rw [iota_shift] at this
    exact this

/-- the coordinate along `σ` is affine on bonds of `lift v S`, `S ⊆ Box r`. -/
theorem coord_affine' {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {S : Set Z3}
    (hS : S ⊆ Box r) (σ : Fin 3) :
    ∀ x μ, x ∈ lift v S → periodicLatticeShift x μ ∈ lift v S →
      ((coord v r (periodicLatticeShift x μ) σ : ℤ) : ℝ) = ((coord v r x σ : ℤ) : ℝ) + (if μ = σ then 1 else 0) := by
  intro x μ hx hxμ
  have := coord_affine (P := fun _ => True) hL hS σ x μ ⟨hx, trivial⟩ ⟨hxμ, trivial⟩
  exact this

/-! ## sequential normalisation -/

noncomputable def normC (g : ℕ → PeriodicLatticeSite L → SU2) (b : ℕ → PeriodicLatticeSite L) : ℕ → SU2
  | 0 => 1
  | k + 1 => normC g b k * g k (b k) * (g (k + 1) (b k))⁻¹

noncomputable def normG (g : ℕ → PeriodicLatticeSite L → SU2) (b : ℕ → PeriodicLatticeSite L) (k : ℕ)
    (x : PeriodicLatticeSite L) : SU2 :=
  normC g b k * g k x

theorem normG_trans_base (g : ℕ → PeriodicLatticeSite L → SU2) (b : ℕ → PeriodicLatticeSite L) (k : ℕ) :
    trans (normG g b k) (normG g b (k + 1)) (b k) = 1 := by
  simp only [M2Glue2.trans, normG, normC]
  group

/-! ## the collar box -/

def collar (lo hi : Z3) (σ : Fin 3) (c d : ℤ) : Set Z3 :=
  IBox (Function.update lo σ (max (lo σ) c)) (Function.update hi σ (min (hi σ) d))

theorem mem_collar {lo hi : Z3} {σ : Fin 3} {c d : ℤ} {p : Z3} :
    p ∈ collar lo hi σ c d ↔ p ∈ IBox lo hi ∧ c ≤ p σ ∧ p σ ≤ d := by
  constructor
  · intro h
    have hσ := h σ
    simp only [Function.update_self] at hσ
    refine ⟨fun i => ?_, by have := le_max_right (lo σ) c; omega, by have := min_le_right (hi σ) d; omega⟩
    have hi' := h i
    by_cases e : i = σ
    · subst e; simp only [Function.update_self] at hi'
      exact ⟨(le_max_left _ _).trans hi'.1, hi'.2.trans (min_le_left _ _)⟩
    · simp only [Function.update_of_ne e] at hi'; exact hi'
  · rintro ⟨h, h1, h2⟩ i
    by_cases e : i = σ
    · subst e; simp only [Function.update_self]
      exact ⟨max_le (h i).1 h1, le_min (h i).2 h2⟩
    · simp only [Function.update_of_ne e]; exact h i

/-! ## one level -/

theorem level_sweep {v : PeriodicLatticeSite L} {r : ℕ} (hL : ∀ μ, 2 * r + 1 < L μ + 1) {lo hi : Z3}
    (hbox : IBox lo hi ⊆ Box r) (σ : Fin 3) (a : ℕ → ℤ) (wd : ℕ) (hwd : 1 ≤ wd)
    (hgap : ∀ k, a k + wd + 4 ≤ a (k + 1)) {U : LinkCfg L} (g : ℕ → PeriodicLatticeSite L → SU2)
    (Dom : ℕ → Set Z3) {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2)
    (hg : ∀ k, ZCh U (g k) v (Dom k) (fun _ => t1) (fun _ => t2))
    (hslab : ∀ k p, p ∈ IBox lo hi → (k = 0 ∨ a k - 2 ≤ p σ) → p σ ≤ a (k + 1) + wd + 2 → p ∈ Dom k)
    (dm : ℕ) (hdm : ∀ k p p', p ∈ IBox lo hi → p' ∈ IBox lo hi → a (k + 1) - 2 ≤ p σ → p σ ≤ a (k + 1) + wd + 2 →
        a (k + 1) - 2 ≤ p' σ → p' σ ≤ a (k + 1) + wd + 2 → l1 p p' ≤ dm)
    (hτ : (dm : ℝ) * (2 * t1) ≤ 2) (N : ℕ) :
    ∃ G : PeriodicLatticeSite L → SU2,
      ZCh U G v {p | p ∈ IBox lo hi ∧ ((p σ : ℤ) : ℝ) ≤ ((a (N + 1) : ℤ) : ℝ) + (wd : ℝ) + 2}
        (fun _ => glueT1 t1 ((dm : ℝ) * (2 * t1)) (kap1 (wd : ℝ)))
        (fun _ => glueT2 t1 t2 ((dm : ℝ) * (2 * t1)) (kap1 (wd : ℝ)) (kap2 (wd : ℝ))) := by
  classical
  set τ : ℝ := (dm : ℝ) * (2 * t1) with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  -- base points
  set Cb : ℕ → Set Z3 := fun k => collar lo hi σ (a (k + 1) - 2) (a (k + 1) + wd + 2) with hCb
  set bz : ℕ → Z3 := fun k => if h : (Cb k).Nonempty then h.some else 0 with hbz
  set b : ℕ → PeriodicLatticeSite L := fun k => iota v (bz k) with hb
  set G : ℕ → PeriodicLatticeSite L → SU2 := normG g b with hG
  have hGz : ∀ k, ZCh U (G k) v (Dom k) (fun _ => t1) (fun _ => t2) := fun k => zch_const_mul (hg k) _
  -- collar points lie in both domains
  have hcol : ∀ k p, p ∈ Cb k → p ∈ Dom k ∧ p ∈ Dom (k + 1) := by
    intro k p hp
    obtain ⟨hpb, h1, h2⟩ := mem_collar.mp hp
    have g1 := hgap k; have g2 := hgap (k + 1)
    refine ⟨hslab k p hpb ?_ h2, hslab (k + 1) p hpb (Or.inr h1) (by omega)⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by omega)
  -- transitions on collars
  have htrans : ∀ k p, p ∈ Cb k → frobNorm (((trans (G k) (G (k + 1)) (iota v p) : SU2) : M2) - 1) ≤ τ := by
    intro k p hp
    have hne : (Cb k).Nonempty := ⟨p, hp⟩
    have hbk : bz k ∈ Cb k := by
      show (if h : (Cb k).Nonempty then h.some else 0) ∈ Cb k
      rw [dif_pos hne]; exact hne.some_mem
    have hβ : ∀ z μ, z ∈ Cb k → z + ev μ ∈ Cb k →
        frobNorm (((periodicGaugeTransform (G k) U (iota v z, μ) : SU2) : M2) - 1)
          + frobNorm (((periodicGaugeTransform (G (k + 1)) U (iota v z, μ) : SU2) : M2) - 1) ≤ 2 * t1 := by
      intro z μ hz hzμ
      have a1 := (hGz k).1 z μ (hcol k z hz).1 (hcol k _ hzμ).1
      have a2 := (hGz (k + 1)).1 z μ (hcol k z hz).2 (hcol k _ hzμ).2
      simp only at a1 a2; linarith
    have hw := trans_zbox v (lo := Function.update lo σ (max (lo σ) (a (k + 1) - 2)))
      (hi := Function.update hi σ (min (hi σ) (a (k + 1) + wd + 2))) hβ hbk (l1 p (bz k)) p hp rfl
    have hbase : trans (G k) (G (k + 1)) (iota v (bz k)) = 1 := normG_trans_base g b k
    rw [hbase] at hw
    obtain ⟨hpb, h1, h2⟩ := mem_collar.mp hp
    obtain ⟨hbb, h1', h2'⟩ := mem_collar.mp hbk
    have hd : (l1 p (bz k) : ℝ) ≤ dm := by exact_mod_cast hdm k p (bz k) hpb hbb h1 h2 h1' h2'
    have : (l1 p (bz k) : ℝ) * (2 * t1) ≤ τ := by
      rw [hτdef]; exact mul_le_mul_of_nonneg_right hd (by linarith)
    push_cast at hw
    linarith
  -- the sweep on sites
  set D : Set (PeriodicLatticeSite L) := lift v (IBox lo hi) with hD
  set φ : PeriodicLatticeSite L → ℝ := fun x => ((coord v r x σ : ℤ) : ℝ) with hφ
  set a' : ℕ → ℝ := fun k => ((a k : ℤ) : ℝ) with ha'
  have hw1 : (1 : ℝ) ≤ (wd : ℝ) := by exact_mod_cast hwd
  have hgap' : ∀ k, a' k + (wd : ℝ) + 4 ≤ a' (k + 1) := by
    intro k; have := hgap k; simp only [ha']; exact_mod_cast this
  have hφa : ∀ x μ, x ∈ D → periodicLatticeShift x μ ∈ D →
      φ (periodicLatticeShift x μ) = φ x + (if μ = σ then 1 else 0) := coord_affine' hL hbox σ
  have hgs : ∀ k, GChart U (G k) (Slab D φ a' (wd : ℝ) k) t1 t2 := by
    intro k
    have := gchart_sub_of_zch (v := v) hL hbox
      (P := fun p => (k = 0 ∨ a' k - 2 ≤ ((p σ : ℤ) : ℝ)) ∧ ((p σ : ℤ) : ℝ) ≤ a' (k + 1) + (wd : ℝ) + 2)
      (T := Dom k) (fun p hp hP => hslab k p hp
        (by rcases hP.1 with h | h
            · exact Or.inl h
            · exact Or.inr (by simp only [ha'] at h; exact_mod_cast h))
        (by have := hP.2; simp only [ha'] at this; exact_mod_cast this)) (hGz k)
    exact this
  have hτs : ∀ k x, x ∈ D → a' (k + 1) - 2 ≤ φ x → φ x ≤ a' (k + 1) + (wd : ℝ) + 2 →
      frobNorm (((trans (G k) (G (k + 1)) x : SU2) : M2) - 1) ≤ τ := by
    intro k x hx h1 h2
    obtain ⟨p, hp, rfl⟩ := hx
    have hc : coord v r (iota v p) = p := coord_iota (inj_box v hL) (hbox hp)
    simp only [hφ, ha', hc] at h1 h2
    refine htrans k p (mem_collar.mpr ⟨hp, ?_, ?_⟩)
    · exact_mod_cast h1
    · exact_mod_cast h2
  have hsw := sweep_glue (U := U) (D := D) (φ := φ) (σ := σ) (a := a') hw1 ht1 ht2 hτ0 hτ hφa hgap' hgs hτs N
  refine ⟨sweepA G φ a' (wd : ℝ) N, ?_⟩
  have := zch_of_gchart_sub (v := v) hL hbox
    (P := fun p => ((p σ : ℤ) : ℝ) ≤ a' (N + 1) + (wd : ℝ) + 2) hsw
  exact this

end AdalyFormal.M2BallCharts

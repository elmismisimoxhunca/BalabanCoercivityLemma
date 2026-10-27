import GG7

/-!
# GG8 -- first-order flattening at a point (the 1-jet matching of m2_glue NOTES §1b, group level)
(m2_glue2, 2026-10-15)

* `flatten g φ y`: `cay(Σ_σ φ_σ(x) B_σ) · g x` with `B_σ = icay(U^g(y,σ))`, `φ` affine coordinates vanishing at `y`.
  `flatten_base`: the flattened chart is EXACTLY `1` on the forward star of `y`.
  `flatten_gchart`: it is a `GChart` at `((11/2) t₁, t₂ + 43 t₁²)` (the affine exponent has zero second differences).
* `Walk D ν x n y`: a walk of `n` forward/backward unit steps from `x` to `y` along which every
  `ν`-bond stencil lies in `D`; `bond_growth`: `|U^g(y,ν) − U^g(x,ν)| ≤ n t₂`.
* `trans_growth`: along a walk of bonds in `D_P ∩ D_Q`, `|h(y) − h(x)| ≤ Σ (|G_P − 1| + |G_Q − 1|)`, so two charts
  that are both flat at a point (`|G − 1| ≤ m t₂` at walk-distance `m`) have transitions with
  `|h(y) − h(x)| ≤ n(n+1) t₂` — second-order flat.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace AdalyFormal.M2Glue2

open Matrix
open AdalyFormal.Target.ClayStatement
open AdalyFormal.Balaban.SuTwoLogExp (SU2 M2 coe_mul coe_inv)
open AdalyFormal.Balaban.RMapLipschitz (frobNorm)
open AdalyFormal.Balaban.Bch2 (IsSu2 frobNorm_add_le frobNorm_nonneg frobNorm_smul)
open AdalyFormal.Balaban.RegularityGap (frobNorm_neg)
open scoped Matrix

variable {L : PeriodicLatticeExtent}

/-! ## §1 the affine Cayley flattening -/

noncomputable def flatB (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (y : PeriodicLatticeSite L)
    (σ : Fin 3) : M2 := icay (periodicGaugeTransform g U (y, σ))

noncomputable def flatY (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (y : PeriodicLatticeSite L)
    (φ : Fin 3 → PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : M2 :=
  ∑ σ : Fin 3, φ σ x • flatB U g y σ

noncomputable def flatten (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (y : PeriodicLatticeSite L)
    (φ : Fin 3 → PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : SU2 :=
  cay (flatY U g y φ x) * g x

theorem isSu2_flatY (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (y : PeriodicLatticeSite L)
    (φ : Fin 3 → PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) : IsSu2 (flatY U g y φ x) := by
  unfold flatY
  rw [Fin.sum_univ_three]
  exact (((isSu2_icay _).smul _).add ((isSu2_icay _).smul _)).add ((isSu2_icay _).smul _)

theorem gauge_flatten (U : LinkCfg L) (g : PeriodicLatticeSite L → SU2) (y : PeriodicLatticeSite L)
    (φ : Fin 3 → PeriodicLatticeSite L → ℝ) (x : PeriodicLatticeSite L) (ν : Fin 3) :
    periodicGaugeTransform (flatten U g y φ) U (x, ν)
      = cay (flatY U g y φ x) * periodicGaugeTransform g U (x, ν)
        * (cay (flatY U g y φ (periodicLatticeShift x ν)))⁻¹ := by
  simp only [flatten, periodicGaugeTransform]; group

/-- affine coordinates: `φ_σ(x + e_μ) = φ_σ x + [μ = σ]`. -/
def AffineOn (D : Set (PeriodicLatticeSite L)) (φ : Fin 3 → PeriodicLatticeSite L → ℝ) : Prop :=
  ∀ x μ, x ∈ D → periodicLatticeShift x μ ∈ D → ∀ σ, φ σ (periodicLatticeShift x μ) = φ σ x + (if μ = σ then 1 else 0)

theorem flatY_step {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {y : PeriodicLatticeSite L}
    {φ : Fin 3 → PeriodicLatticeSite L → ℝ} {D : Set (PeriodicLatticeSite L)} (hφ : AffineOn D φ)
    {x : PeriodicLatticeSite L} {μ : Fin 3} (hx : x ∈ D) (hxμ : periodicLatticeShift x μ ∈ D) :
    flatY U g y φ (periodicLatticeShift x μ) - flatY U g y φ x = flatB U g y μ := by
  unfold flatY
  rw [← Finset.sum_sub_distrib]
  simp only [hφ x μ hx hxμ, add_smul, add_sub_cancel_left]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_smul]
  · intro h; exact absurd (Finset.mem_univ μ) h

theorem frobNorm_flatB_le {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {y : PeriodicLatticeSite L}
    {σ : Fin 3} {t1 : ℝ} (h : frobNorm (((periodicGaugeTransform g U (y, σ) : SU2) : M2) - 1) ≤ t1) (ht : t1 ≤ 2) :
    frobNorm (flatB U g y σ) ≤ t1 :=
  (frobNorm_icay_le (h.trans ht)).trans h

/-- the flattened chart is exactly the identity on the forward star of the base point. -/
theorem flatten_base {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {y : PeriodicLatticeSite L}
    {φ : Fin 3 → PeriodicLatticeSite L → ℝ} {D : Set (PeriodicLatticeSite L)} (hφ : AffineOn D φ)
    (hy0 : ∀ σ, φ σ y = 0) {σ : Fin 3} (hy : y ∈ D) (hyσ : periodicLatticeShift y σ ∈ D)
    (h2 : frobNorm (((periodicGaugeTransform g U (y, σ) : SU2) : M2) - 1) ≤ 2) :
    periodicGaugeTransform (flatten U g y φ) U (y, σ) = 1 := by
  rw [gauge_flatten]
  have hY0 : flatY U g y φ y = 0 := by simp [flatY, hy0]
  have hY1 : flatY U g y φ (periodicLatticeShift y σ) = flatB U g y σ := by
    have := flatY_step (U := U) (g := g) (y := y) hφ hy hyσ
    rw [hY0, sub_zero] at this; exact this
  rw [hY0, hY1, cay_zero, one_mul, flatB, cay_icay h2]
  group

/-- the flattened chart is a chart (second differences of the affine exponent vanish). -/
theorem flatten_gchart {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {y : PeriodicLatticeSite L}
    {φ : Fin 3 → PeriodicLatticeSite L → ℝ} {D : Set (PeriodicLatticeSite L)} (hφ : AffineOn D φ)
    {t1 t2 : ℝ} (ht1 : 0 ≤ t1) (ht12 : t1 ≤ 2) (hg : GChart U g D t1 t2)
    (hy : y ∈ D) (hyσ : ∀ σ, periodicLatticeShift y σ ∈ D) :
    GChart U (flatten U g y φ) D ((11 / 2) * t1) (t2 + 43 * t1 ^ 2) := by
  have hB : ∀ σ, frobNorm (flatB U g y σ) ≤ t1 := fun σ => frobNorm_flatB_le (hg.1 y σ hy (hyσ σ)) ht12
  have hk : ∀ x μ, x ∈ D → periodicLatticeShift x μ ∈ D →
      frobNorm (((cay (flatY U g y φ (periodicLatticeShift x μ)) : SU2) : M2) - (cay (flatY U g y φ x) : M2))
        ≤ (9 / 2) * t1 := by
    intro x μ hx hxμ
    refine (frobNorm_cay_sub_le (isSu2_flatY _ _ _ _ _) (isSu2_flatY _ _ _ _ _)).trans ?_
    rw [flatY_step hφ hx hxμ]
    exact mul_le_mul_of_nonneg_left (hB μ) (by norm_num)
  refine ⟨fun x ν hx hxν => ?_, fun x μ ν h0 h1 h2 h3 => ?_⟩
  · rw [gauge_flatten]
    refine (gauge_step_one _ _ _).trans ?_
    have := hg.1 x ν hx hxν
    have := hk x ν hx hxν
    linarith
  · rw [gauge_flatten, gauge_flatten]
    refine (gauge_step_two _ _ _ _ _ _).trans ?_
    set Y0 := flatY U g y φ x
    set Y1 := flatY U g y φ (periodicLatticeShift x ν)
    set Y2 := flatY U g y φ (periodicLatticeShift x μ)
    set Y3 := flatY U g y φ (periodicLatticeShift (periodicLatticeShift x μ) ν)
    have d10 : Y1 - Y0 = flatB U g y ν := flatY_step hφ h0 h1
    have d32 : Y3 - Y2 = flatB U g y ν := flatY_step hφ h2 h3
    have d20 : Y2 - Y0 = flatB U g y μ := flatY_step hφ h0 h2
    have h3' : periodicLatticeShift (periodicLatticeShift x ν) μ ∈ D := by rw [← shift_comm']; exact h3
    have d31 : Y3 - Y1 = flatB U g y μ := by
      have := flatY_step (U := U) (g := g) (y := y) hφ h1 h3'
      rw [← shift_comm'] at this; exact this
    have hsec := cay_second4 (isSu2_flatY U g y φ x) (isSu2_flatY U g y φ (periodicLatticeShift x ν))
      (isSu2_flatY U g y φ (periodicLatticeShift x μ))
      (isSu2_flatY U g y φ (periodicLatticeShift (periodicLatticeShift x μ) ν))
    rw [show Y3 - Y2 - (Y1 - Y0) = 0 by rw [d32, d10]; abel, d31, d20, d10] at hsec
    have z : frobNorm (0 : M2) = 0 := by simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
    rw [z, mul_zero, zero_add] at hsec
    have k20 := hk x μ h0 h2
    have k31 : frobNorm (((cay Y3 : SU2) : M2) - (cay Y1 : M2)) ≤ (9 / 2) * t1 := by
      have := hk _ μ h1 h3'; rw [← shift_comm'] at this; exact this
    have k32 := hk _ ν h2 h3
    have gd := hg.2 x μ ν h0 h1 h2 h3
    have g1 := hg.1 x ν h0 h1
    have bμ := hB μ; have bν := hB ν
    have nB := frobNorm_nonneg (flatB U g y μ)
    have nB' := frobNorm_nonneg (flatB U g y ν)
    have p1 : frobNorm (((periodicGaugeTransform g U (x, ν) : SU2) : M2) - 1)
        * (frobNorm (((cay Y2 : SU2) : M2) - (cay Y0 : M2)) + frobNorm (((cay Y3 : SU2) : M2) - (cay Y1 : M2)))
        ≤ t1 * (9 * t1) := mul_le_mul g1 (by linarith) (add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)) ht1
    have p2 : frobNorm (((cay Y2 : SU2) : M2) - (cay Y0 : M2)) * frobNorm (((cay Y3 : SU2) : M2) - (cay Y2 : M2))
        ≤ ((9 / 2) * t1) * ((9 / 2) * t1) := mul_le_mul k20 k32 (frobNorm_nonneg _) (by positivity)
    have p3 : (27 / 4) * (frobNorm (flatB U g y μ) + frobNorm (flatB U g y μ)) * frobNorm (flatB U g y ν)
        ≤ (27 / 4) * (t1 + t1) * t1 := by
      apply mul_le_mul (by linarith) bν nB' (by positivity)
    nlinarith

/-! ## §2 walks and growth -/

/-- a walk of `n` unit steps from `x` to `y`; every step is a forward or backward bond `(z, μ)` whose
`ν`-stencil `{z, z+ν, z+μ, z+μ+ν}` lies in `D`. -/
inductive Walk (D : Set (PeriodicLatticeSite L)) (ν : Fin 3) : PeriodicLatticeSite L → ℕ → PeriodicLatticeSite L → Prop
  | refl (x : PeriodicLatticeSite L) : Walk D ν x 0 x
  | fwd {x y : PeriodicLatticeSite L} {n : ℕ} (μ : Fin 3) (h : Walk D ν x n y)
      (h0 : y ∈ D) (h1 : periodicLatticeShift y ν ∈ D) (h2 : periodicLatticeShift y μ ∈ D)
      (h3 : periodicLatticeShift (periodicLatticeShift y μ) ν ∈ D) : Walk D ν x (n + 1) (periodicLatticeShift y μ)
  | bwd {x z : PeriodicLatticeSite L} {n : ℕ} (μ : Fin 3) (h : Walk D ν x n (periodicLatticeShift z μ))
      (h0 : z ∈ D) (h1 : periodicLatticeShift z ν ∈ D) (h2 : periodicLatticeShift z μ ∈ D)
      (h3 : periodicLatticeShift (periodicLatticeShift z μ) ν ∈ D) : Walk D ν x (n + 1) z

/-- bond values change by at most `t₂` per step. -/
theorem bond_growth {U : LinkCfg L} {g : PeriodicLatticeSite L → SU2} {D : Set (PeriodicLatticeSite L)}
    {t1 t2 : ℝ} (hg : GChart U g D t1 t2) {ν : Fin 3} {x y : PeriodicLatticeSite L} {n : ℕ}
    (w : Walk D ν x n y) :
    frobNorm (((periodicGaugeTransform g U (y, ν) : SU2) : M2) - (periodicGaugeTransform g U (x, ν) : SU2))
      ≤ n * t2 := by
  induction w with
  | refl => simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
  | fwd μ _ h0 h1 h2 h3 ih =>
    rename_i y' n' hw'
    have := hg.2 y' μ ν h0 h1 h2 h3
    have t := frobNorm_sub_le' (((periodicGaugeTransform g U (periodicLatticeShift y' μ, ν) : SU2) : M2))
      ((periodicGaugeTransform g U (y', ν) : SU2) : M2) ((periodicGaugeTransform g U (x, ν) : SU2) : M2)
    push_cast; linarith
  | bwd μ _ h0 h1 h2 h3 ih =>
    rename_i z' n' hw'
    have := hg.2 z' μ ν h0 h1 h2 h3
    rw [frobNorm_sub_comm] at this
    have t := frobNorm_sub_le' (((periodicGaugeTransform g U (z', ν) : SU2) : M2))
      ((periodicGaugeTransform g U (periodicLatticeShift z' μ, ν) : SU2) : M2)
      ((periodicGaugeTransform g U (x, ν) : SU2) : M2)
    push_cast; linarith

/-- a walk along bonds of a set `E` (each step a bond with both ends in `E`). -/
inductive BWalk (E : Set (PeriodicLatticeSite L)) : PeriodicLatticeSite L → ℕ → PeriodicLatticeSite L → Prop
  | refl (x : PeriodicLatticeSite L) : BWalk E x 0 x
  | fwd {x y : PeriodicLatticeSite L} {n : ℕ} (μ : Fin 3) (h : BWalk E x n y) (h0 : y ∈ E)
      (h1 : periodicLatticeShift y μ ∈ E) : BWalk E x (n + 1) (periodicLatticeShift y μ)
  | bwd {x z : PeriodicLatticeSite L} {n : ℕ} (μ : Fin 3) (h : BWalk E x n (periodicLatticeShift z μ))
      (h0 : z ∈ E) (h1 : periodicLatticeShift z μ ∈ E) : BWalk E x (n + 1) z

/-- transitions move by at most the sum of the two charts' bond deviations along a walk. -/
theorem trans_growth {U : LinkCfg L} {gP gQ : PeriodicLatticeSite L → SU2} {E : Set (PeriodicLatticeSite L)}
    {β : PeriodicLatticeSite L → ℝ}
    (hβ : ∀ z μ, z ∈ E → periodicLatticeShift z μ ∈ E →
      frobNorm (((periodicGaugeTransform gP U (z, μ) : SU2) : M2) - 1)
        + frobNorm (((periodicGaugeTransform gQ U (z, μ) : SU2) : M2) - 1) ≤ β z)
    {x y : PeriodicLatticeSite L} {n : ℕ} (w : BWalk E x n y) (B : ℝ) (hB : ∀ z ∈ E, β z ≤ B) :
    frobNorm (((trans gP gQ y : SU2) : M2) - (trans gP gQ x : M2)) ≤ n * B := by
  induction w with
  | refl => simp [frobNorm, AdalyFormal.Balaban.RMapLipschitz.frobSq]
  | fwd μ _ h0 h1 ih =>
    rename_i y' n' hw'
    have t1 := trans_one _ _ _ _ (trans_rel U gP gQ y' μ)
    have := hβ y' μ h0 h1
    have := hB y' h0
    have t := frobNorm_sub_le' (((trans gP gQ (periodicLatticeShift y' μ) : SU2) : M2))
      ((trans gP gQ y' : SU2) : M2) ((trans gP gQ x : SU2) : M2)
    push_cast; linarith
  | bwd μ _ h0 h1 ih =>
    rename_i z' n' hw'
    have t1 := trans_one _ _ _ _ (trans_rel U gP gQ z' μ)
    rw [frobNorm_sub_comm] at t1
    have := hβ z' μ h0 h1
    have := hB z' h0
    have t := frobNorm_sub_le' (((trans gP gQ z' : SU2) : M2))
      ((trans gP gQ (periodicLatticeShift z' μ) : SU2) : M2) ((trans gP gQ x : SU2) : M2)
    push_cast; linarith

end AdalyFormal.M2Glue2

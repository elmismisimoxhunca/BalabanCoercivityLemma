
/-!
Round 9, qualitative route: first-order separation at fixed scale and radius, with a free
exterior path and a free interior profile.

At zero curvature the localized correction vanishes, so for small curvature a corrected
crossing can only split off a vacuum crossing.  Two abstract theorems turn zero-curvature
data into a separation at EVERY small positive curvature:
* `first_order_separation`: the vacuum carrier is positive definite just before a crossing
  angle and has a negative direction just after it, the carrier is jointly continuous at
  zero curvature, and the first-order correction is positive definite on the vacuum
  kernel (no angle derivative, no gap constant, no scalar action; pre-crossing sign);
* `perturbative_sign_change`: both signs, under joint differentiability and a scalar
  action on the kernel.
The concrete part allows any continuous exterior path and any bounded interior profile
(round 5 `maskedU`).  Reflecting the profile reflects the curvature, so a coupling of
either sign gives a pre-crossing separation for the profile or for its reflection.  The
remaining premise `CofinalVacuumCoupling` is a statement about zero curvature plus soft
regularity.

Nothing here proves a pinned goal.  The family premises are explicit, unproved
hypotheses on the actual operators; the abstract lemmas are finite-dimensional facts.
-/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.D1Literal (PSD psd_kernel psd_coercive)
open AdalyFormal.Round8.Guarded.SignFree (unit_of_definite_complements)
open AdalyFormal.Round5.Guarded.IVTR2 (first_carrier_crossing)

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem abs_inner_op_le (N : E →L[ℝ] E) (u y : E) : |⟪u, N y⟫| ≤ ‖N‖ * ‖u‖ * ‖y‖ := by
  calc |⟪u, N y⟫| ≤ ‖u‖ * ‖N y‖ := abs_real_inner_le_norm u (N y)
    _ ≤ ‖u‖ * (‖N‖ * ‖y‖) := mul_le_mul_of_nonneg_left (N.le_opNorm y) (norm_nonneg u)
    _ = ‖N‖ * ‖u‖ * ‖y‖ := by ring

/-- Two-block positivity with respect to `E = K ⊕ Kᗮ`: a definite `K`-block, a
definite `Kᗮ`-block and a small off-diagonal block give a positive definite form. -/
theorem block_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (K : Submodule ℝ E)
    {a g b : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g)
    (hK : ∀ u ∈ K, a * ‖u‖ ^ 2 ≤ ⟪u, X u⟫)
    (hKp : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫)
    (hX : ∀ u ∈ K, ∀ y ∈ Kᗮ, |⟪u, X y⟫| ≤ b * ‖u‖ * ‖y‖) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hsym : ⟪y, X u⟫ = ⟪u, X y⟫ := by rw [← hs y u, real_inner_comm]
  have hexp : ⟪u + y, X (u + y)⟫ = ⟪u, X u⟫ + 2 * ⟪u, X y⟫ + ⟪y, X y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]; ring
  rw [hexp]
  have h1 := hK u hu
  have h2 := hKp y hy
  have h3 : -(b * ‖u‖ * ‖y‖) ≤ ⟪u, X y⟫ := (abs_le.mp (hX u hu y hy)).1
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have key : 0 < a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2 := by
    have hQ : a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) =
        (a * ‖u‖ - b * ‖y‖) ^ 2 + (a * g - b ^ 2) * ‖y‖ ^ 2 := by ring
    rcases hr0.lt_or_eq with hr | hr
    · have hpos : 0 < (a * g - b ^ 2) * ‖y‖ ^ 2 := mul_pos (by linarith) (pow_pos hr 2)
      have hm : 0 < a * (a * ‖u‖ ^ 2 - 2 * (b * ‖u‖ * ‖y‖) + g * ‖y‖ ^ 2) := by
        rw [hQ]; linarith [sq_nonneg (a * ‖u‖ - b * ‖y‖)]
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have := mul_le_mul_of_nonneg_left hcon' ha.le
      linarith
    · have hy0 : y = 0 := norm_eq_zero.mp hr.symm
      have hu0 : u ≠ 0 := by
        intro hu0
        apply hx
        rw [hu0, hy0, add_zero]
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      rw [← hr]
      have : 0 < a * ‖u‖ ^ 2 := mul_pos ha (pow_pos hun 2)
      linarith
  linarith

omit [FiniteDimensional ℝ E] in
/-- The quadratic form of `A0 + τ At + ε B + R` on a kernel vector of `A0` on which
`At` and `B` act as scalars. -/
theorem kernel_form (A0 At B R : E →L[ℝ] E) (τ ε σ β : ℝ) (u : E) (h0 : A0 u = 0)
    (ht : ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ⟪u, B u⟫ = β * ‖u‖ ^ 2) :
    ⟪u, (A0 + τ • At + ε • B + R) u⟫ = (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ := by
  simp only [add_apply, smul_apply, inner_add_right,
    real_inner_smul_right, h0, inner_zero_right, ht, hb]
  ring

omit [FiniteDimensional ℝ E] in
theorem expansion_dist (A0 At B R : E →L[ℝ] E) (τ ε : ℝ) :
    ‖(A0 + τ • At + ε • B + R) - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
  have h : (A0 + τ • At + ε • B + R) - A0 = τ • At + ε • B + R := by abel
  rw [h]
  calc ‖τ • At + ε • B + R‖ ≤ ‖τ • At + ε • B‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖τ • At‖ + ‖ε • B‖ + ‖R‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = |τ| * ‖At‖ + |ε| * ‖B‖ + ‖R‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

omit [FiniteDimensional ℝ E] in
theorem perp_lower (A0 X : E →L[ℝ] E) (K : Submodule ℝ E) {g δ : ℝ}
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A0 y⟫) (hδ : ‖X - A0‖ ≤ δ) :
    ∀ y ∈ Kᗮ, (g - δ) * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  intro y hy
  have h1 := hgap y hy
  have h2 := (abs_le.mp (abs_inner_op_le (X - A0) y y)).1
  have h3 : ⟪y, X y⟫ = ⟪y, A0 y⟫ + ⟪y, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right]; ring
  have h4 : ‖X - A0‖ * ‖y‖ * ‖y‖ ≤ δ * ‖y‖ ^ 2 := by
    have hy0 : 0 ≤ ‖y‖ * ‖y‖ := mul_nonneg (norm_nonneg y) (norm_nonneg y)
    calc ‖X - A0‖ * ‖y‖ * ‖y‖ = ‖X - A0‖ * (‖y‖ * ‖y‖) := by ring
      _ ≤ δ * (‖y‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ hy0
      _ = δ * ‖y‖ ^ 2 := by ring
  rw [h3]
  linarith

omit [FiniteDimensional ℝ E] in
theorem cross_upper (A0 X : E →L[ℝ] E) (hs0 : ∀ x y, ⟪A0 x, y⟫ = ⟪x, A0 y⟫)
    (K : Submodule ℝ E) (hker : ∀ u ∈ K, A0 u = 0) {δ : ℝ} (hδ : ‖X - A0‖ ≤ δ) :
    ∀ u ∈ K, ∀ y : E, |⟪u, X y⟫| ≤ δ * ‖u‖ * ‖y‖ := by
  intro u hu y
  have h0 : ⟪u, A0 y⟫ = 0 := by rw [← hs0, hker u hu, inner_zero_left]
  have h3 : ⟪u, X y⟫ = ⟪u, (X - A0) y⟫ := by
    simp only [sub_apply, inner_sub_right, h0, sub_zero]
  rw [h3]
  have huy : 0 ≤ ‖u‖ * ‖y‖ := mul_nonneg (norm_nonneg u) (norm_nonneg y)
  calc |⟪u, (X - A0) y⟫| ≤ ‖X - A0‖ * ‖u‖ * ‖y‖ := abs_inner_op_le _ _ _
    _ = ‖X - A0‖ * (‖u‖ * ‖y‖) := by ring
    _ ≤ δ * (‖u‖ * ‖y‖) := mul_le_mul_of_nonneg_right hδ huy
    _ = δ * ‖u‖ * ‖y‖ := by ring

omit [FiniteDimensional ℝ E] in
/-- First-order bookkeeping: if `X = A0 + τ At + ε B + R` with `‖R‖ ≤ ρ`, then on the
kernel `K` of `A0` (where `At`, `B` act as scalars) the form of `X` is its first-order
value up to `ρ`, and `X` is within `|τ|‖At‖ + |ε|‖B‖ + ρ` of `A0`. -/
theorem kernel_form_bounds (A0 At B X : E →L[ℝ] E) (K : Submodule ℝ E)
    (hker : ∀ u ∈ K, A0 u = 0) {σ β τ ε ρ : ℝ}
    (ht : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) (hb : ∀ u ∈ K, ⟪u, B u⟫ = β * ‖u‖ ^ 2)
    (hR : ‖X - A0 - τ • At - ε • B‖ ≤ ρ) :
    (∀ u ∈ K, |⟪u, X u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2| ≤ ρ * ‖u‖ ^ 2) ∧
      ‖X - A0‖ ≤ |τ| * ‖At‖ + |ε| * ‖B‖ + ρ := by
  obtain ⟨R, hR_def⟩ : ∃ R : E →L[ℝ] E, R = X - A0 - τ • At - ε • B := ⟨_, rfl⟩
  have hRn : ‖R‖ ≤ ρ := by rw [hR_def]; exact hR
  have hX : X = A0 + τ • At + ε • B + R := by rw [hR_def]; abel
  constructor
  · intro u hu
    rw [hX, kernel_form A0 At B R τ ε σ β u (hker u hu) (ht u hu) (hb u hu)]
    have h1 := abs_inner_op_le R u u
    have h2 : ‖R‖ * ‖u‖ * ‖u‖ ≤ ρ * ‖u‖ ^ 2 := by
      have hu0 : 0 ≤ ‖u‖ * ‖u‖ := mul_nonneg (norm_nonneg u) (norm_nonneg u)
      calc ‖R‖ * ‖u‖ * ‖u‖ = ‖R‖ * (‖u‖ * ‖u‖) := by ring
        _ ≤ ρ * (‖u‖ * ‖u‖) := mul_le_mul_of_nonneg_right hRn hu0
        _ = ρ * ‖u‖ ^ 2 := by ring
    have h3 : (σ * τ + ε * β) * ‖u‖ ^ 2 + ⟪u, R u⟫ - (σ * τ + ε * β) * ‖u‖ ^ 2 = ⟪u, R u⟫ := by
      ring
    rw [h3]
    exact le_trans h1 h2
  · rw [hX]
    exact le_trans (expansion_dist A0 At B R τ ε) (by linarith)

/-- **Perturbative sign-free separation.**  `A ε t` is a symmetric two-parameter
family, `D ε` a symmetric correction.  At `ε = 0` and `t = ts` the carrier `A 0 ts`
vanishes on a nonzero subspace `K` and is bounded below by `g > 0` on `Kᗮ` (so `A 0 ts`
is positive semidefinite and `ts` is a first crossing).  Suppose `(ε,t) ↦ A ε t` and
`ε ↦ D ε` are differentiable at `(0,ts)` and `0` in the first-order sense of `hAexp` and
`hDexp` (in particular `D 0 = 0`), with derivatives `At`, `Ae`, `De` acting on `K` as the
scalars `σ < 0`, `α`, `c`.  If `c ≠ 0` then for every sufficiently small `ε > 0` there is
an interval `[t₀,t₁]` of carrier units on which `A ε · - D ε` passes from positive
semidefinite to a negative direction.  For `c > 0` the carrier is positive definite on
the interval (pre-crossing), for `c < 0` it is an indefinite unit (post-crossing).
Only `c ≠ 0` enters, never its value. -/
theorem perturbative_sign_change
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (ts : ℝ) (K : Submodule ℝ E) (g σ α c : ℝ) (At Ae De : E →L[ℝ] E)
    (hker : ∀ u ∈ K, A 0 ts u = 0)
    (hg : 0 < g) (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A 0 ts y⟫)
    (hne : ∃ u ∈ K, u ≠ 0)
    (hσ : σ < 0) (hc : c ≠ 0)
    (hAt : ∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2)
    (hAe : ∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2)
    (hDe : ∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2)
    (hAexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖A ε (ts + τ) - A 0 ts - τ • At - ε • Ae‖ ≤ η * (|ε| + |τ|))
    (hDexp : ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r →
      ‖D ε - ε • De‖ ≤ η * |ε|) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧ (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (A ε t)) ∧
        PSD (A ε t₀ - D ε) ∧ ∃ w : E, ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
  have hs0 : ∀ x y, ⟪A 0 ts x, y⟫ = ⟪x, A 0 ts y⟫ := hsA 0 ts
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = -σ := ⟨_, rfl⟩
  have hs : 0 < s := by linarith
  have hσs : |σ| = s := by rw [abs_of_neg hσ, hs_def]
  have hcabs : 0 < |c| := abs_pos.mpr hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = |c| / (3 * s) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ_def]; exact div_pos hcabs (by linarith)
  have hsκ : s * κ = |c| / 3 := by
    rw [hκ_def, mul_div_assoc', div_eq_div_iff (mul_pos (by norm_num) hs).ne' (by norm_num)]
    ring
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = |α - c| / s + κ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ_def]; exact add_nonneg (div_nonneg (abs_nonneg _) hs.le) hκ0.le
  obtain ⟨η₁, hη₁_def⟩ : ∃ η : ℝ, η = |c| / (24 * (1 + Λ)) := ⟨_, rfl⟩
  have hη₁0 : 0 < η₁ := by rw [hη₁_def]; exact div_pos hcabs (by linarith)
  have hη₁Λ : η₁ * (1 + Λ) = |c| / 24 := by
    rw [hη₁_def, div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos (by norm_num) (by linarith : (0 : ℝ) < 1 + Λ)).ne' (by norm_num)]
    ring
  have hη₂0 : (0 : ℝ) < |c| / 24 := div_pos hcabs (by norm_num)
  obtain ⟨r₁, hr₁, hA1⟩ := hAexp η₁ hη₁0
  obtain ⟨r₂, hr₂, hD1⟩ := hDexp (|c| / 24) hη₂0
  obtain ⟨C, hC_def⟩ : ∃ C : ℝ, C = Λ * ‖At‖ + ‖Ae‖ + ‖De‖ + |c| / 12 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    have h1 := mul_nonneg hΛ0 (norm_nonneg At)
    have h2 := norm_nonneg Ae
    have h3 := norm_nonneg De
    have h4 : 0 < |c| / 12 := div_pos hcabs (by norm_num)
    rw [hC_def]; linarith
  have h1Λ : (0 : ℝ) < 1 + Λ := by linarith
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have h16C : (0 : ℝ) < 16 * C ^ 2 := mul_pos (by norm_num) (pow_pos hC0 2)
  have hr₁' : 0 < r₁ / (1 + Λ) := div_pos hr₁ h1Λ
  have hgC : 0 < g / (2 * C) := div_pos hg h2C
  have hcgC : 0 < |c| * g / (16 * C ^ 2) := div_pos (mul_pos hcabs hg) h16C
  refine ⟨min (min (r₁ / (1 + Λ)) r₂) (min (g / (2 * C)) (|c| * g / (16 * C ^ 2))),
    lt_min (lt_min hr₁' hr₂) (lt_min hgC hcgC), ?_⟩
  intro ε hε hε₀
  have hε1 : ε < r₁ / (1 + Λ) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : ε < r₂ := lt_of_lt_of_le hε₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : ε < g / (2 * C) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε4 : ε < |c| * g / (16 * C ^ 2) :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεr₁ : ε * (1 + Λ) < r₁ := (lt_div_iff₀ h1Λ).mp hε1
  have hεC : ε * C < g / 2 := by
    have h := (lt_div_iff₀ h2C).mp hε3
    linarith
  have hεC2 : ε * C ^ 2 * 16 < |c| * g := by
    have h := (lt_div_iff₀ h16C).mp hε4
    linarith
  have hεabs : |ε| = ε := abs_of_pos hε
  obtain ⟨τC, hτC_def⟩ : ∃ τ : ℝ, τ = ε * (α - c) / s := ⟨_, rfl⟩
  have hστC : σ * τC = -(ε * (α - c)) := by
    rw [hτC_def, mul_div_assoc', div_eq_iff hs.ne', hs_def]; ring
  have hτCabs : |τC| = ε * (|α - c| / s) := by
    rw [hτC_def, abs_div, abs_mul, abs_of_pos hε, abs_of_pos hs]; ring
  have hDn : ‖D ε - ε • De‖ ≤ ε * |c| / 24 := by
    have h := hD1 ε (by rw [hεabs]; exact hε2)
    rw [hεabs] at h
    linarith
  -- every angle in the window `|t - ts - τC| ≤ ε κ`
  have window : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ →
      ‖A ε t - A 0 ts‖ ≤ ε * C ∧ ‖(A ε t - D ε) - A 0 ts‖ ≤ ε * C ∧
      (∀ u ∈ K, |⟪u, A ε t u⟫ - (ε * c + σ * (t - ts - τC)) * ‖u‖ ^ 2| ≤
        ε * |c| / 24 * ‖u‖ ^ 2) ∧
      (∀ u ∈ K, |⟪u, (A ε t - D ε) u⟫ - σ * (t - ts - τC) * ‖u‖ ^ 2| ≤
        ε * |c| / 12 * ‖u‖ ^ 2) := by
    intro t ht
    obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = t - ts := ⟨_, rfl⟩
    have hτ : |τ| ≤ ε * Λ := by
      have h1 : τ = τC + (t - ts - τC) := by rw [hτ_def]; ring
      calc |τ| = |τC + (t - ts - τC)| := by rw [h1]
        _ ≤ |τC| + |t - ts - τC| := abs_add_le _ _
        _ ≤ ε * (|α - c| / s) + ε * κ := by rw [hτCabs]; linarith
        _ = ε * Λ := by rw [hΛ_def]; ring
    have hεΛ : 0 ≤ ε * Λ := mul_nonneg hε.le hΛ0
    have hτr : |τ| < r₁ := by linarith
    have hεr : |ε| < r₁ := by rw [hεabs]; linarith
    have hA := hA1 ε τ hεr hτr
    have hts : ts + τ = t := by rw [hτ_def]; ring
    rw [hts] at hA
    have hAn : ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ ε * |c| / 24 := by
      calc ‖A ε t - A 0 ts - τ • At - ε • Ae‖ ≤ η₁ * (|ε| + |τ|) := hA
        _ ≤ η₁ * (ε + ε * Λ) :=
          mul_le_mul_of_nonneg_left (by rw [hεabs]; linarith) hη₁0.le
        _ = ε * (η₁ * (1 + Λ)) := by ring
        _ = ε * |c| / 24 := by rw [hη₁Λ]; ring
    have hRD : ‖(A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De)‖ ≤ ε * |c| / 12 := by
      have h : (A ε t - D ε) - A 0 ts - τ • At - ε • (Ae - De) =
          (A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De) := by
        rw [smul_sub]; abel
      rw [h]
      calc ‖(A ε t - A 0 ts - τ • At - ε • Ae) - (D ε - ε • De)‖
          ≤ ‖A ε t - A 0 ts - τ • At - ε • Ae‖ + ‖D ε - ε • De‖ := norm_sub_le _ _
        _ ≤ ε * |c| / 24 + ε * |c| / 24 := add_le_add hAn hDn
        _ = ε * |c| / 12 := by ring
    have hADe : ∀ u ∈ K, ⟪u, (Ae - De) u⟫ = (α - c) * ‖u‖ ^ 2 := by
      intro u hu
      simp only [sub_apply, inner_sub_right, hAe u hu, hDe u hu]
      ring
    obtain ⟨hKA, hdA⟩ := kernel_form_bounds (A 0 ts) At Ae (A ε t) K hker hAt hAe hAn
    obtain ⟨hKD, hdD⟩ :=
      kernel_form_bounds (A 0 ts) At (Ae - De) (A ε t - D ε) K hker hAt hADe hRD
    have hτAt : |τ| * ‖At‖ ≤ ε * Λ * ‖At‖ := mul_le_mul_of_nonneg_right hτ (norm_nonneg _)
    have hεDe : 0 ≤ ε * ‖De‖ := mul_nonneg hε.le (norm_nonneg _)
    have hεc : 0 ≤ ε * |c| := mul_nonneg hε.le (abs_nonneg _)
    have hsub : ‖Ae - De‖ ≤ ‖Ae‖ + ‖De‖ := norm_sub_le _ _
    have hεsub : ε * ‖Ae - De‖ ≤ ε * (‖Ae‖ + ‖De‖) := mul_le_mul_of_nonneg_left hsub hε.le
    have hστ1 : σ * τ + ε * α = ε * c + σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    have hστ2 : σ * τ + ε * (α - c) = σ * (t - ts - τC) := by
      rw [hτ_def]; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc ‖A ε t - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae‖ + ε * |c| / 24 := hdA
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · calc ‖(A ε t - D ε) - A 0 ts‖ ≤ |τ| * ‖At‖ + |ε| * ‖Ae - De‖ + ε * |c| / 12 := hdD
        _ ≤ ε * C := by rw [hεabs, hC_def]; linarith
    · intro u hu
      have h := hKA u hu
      rw [hστ1] at h
      exact h
    · intro u hu
      have h := hKD u hu
      rw [hστ2] at h
      exact h
  have hσw : ∀ t : ℝ, |t - ts - τC| ≤ ε * κ → |σ * (t - ts - τC)| ≤ ε * |c| / 3 := by
    intro t ht
    rw [abs_mul, hσs]
    calc s * |t - ts - τC| ≤ s * (ε * κ) := mul_le_mul_of_nonneg_left ht hs.le
      _ = ε * (s * κ) := by ring
      _ = ε * |c| / 3 := by rw [hsκ]; ring
  obtain ⟨u₀, hu₀K, hu₀⟩ := hne
  have hεκ : 0 < ε * κ := mul_pos hε hκ0
  refine ⟨ts + τC - ε * κ, ts + τC + ε * κ, by linarith, ?_, ?_, ?_⟩
  · -- the interval guard
    intro t ht0 ht1
    have hw : |t - ts - τC| ≤ ε * κ := abs_le.mpr ⟨by linarith, by linarith⟩
    obtain ⟨hdA, -, hKA, -⟩ := window t hw
    have hδ := abs_le.mp (hσw t hw)
    have hperp := perp_lower (A 0 ts) (A ε t) K hgap hdA
    rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · -- post-crossing: negative definite on `K`, positive definite on `Kᗮ`
      have hca : |c| = -c := abs_of_neg hcneg
      apply unit_of_definite_complements (A ε t) (hsA ε t) K Kᗮ
      · intro u hu hu0
        have h := (abs_le.mp (hKA u hu)).2
        have hun : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
        rw [hca] at h hδ
        have hm := mul_le_mul_of_nonneg_right hδ.2 hun.le
        have hp : 0 < ε * (-c) * ‖u‖ ^ 2 := mul_pos (mul_pos hε (by linarith)) hun
        linarith
      · intro y hy hy0
        have h := hperp y hy
        have hyn : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
        have hg2 : 0 < g - ε * C := by linarith
        have := mul_pos hg2 hyn
        linarith
      · exact (Submodule.finrank_add_finrank_orthogonal K).ge
    · -- pre-crossing: positive definite
      have hca : |c| = c := abs_of_pos hcpos
      have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, A ε t x⟫ := by
        refine block_pos (A ε t) (hsA ε t) K (a := ε * c / 2) (g := g / 2) (b := ε * C)
          (by have := mul_pos hε hcpos; linarith) ?_ ?_ ?_ ?_
        · rw [hca] at hεC2
          have h3 : ε * (ε * C ^ 2 * 16) < ε * (c * g) := mul_lt_mul_of_pos_left hεC2 hε
          have hpos : 0 < ε * (c * g) := mul_pos hε (mul_pos hcpos hg)
          linarith
        · intro u hu
          have h := (abs_le.mp (hKA u hu)).1
          rw [hca] at h hδ
          have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
          have hm := mul_le_mul_of_nonneg_right hδ.1 hun
          have hp : 0 ≤ ε * c * ‖u‖ ^ 2 := mul_nonneg (mul_nonneg hε.le hcpos.le) hun
          linarith
        · intro y hy
          have h := hperp y hy
          have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
          have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) hyn
          linarith
        · intro u hu y _
          exact cross_upper (A 0 ts) (A ε t) hs0 K hker hdA u hu y
      refine unit_of_definite_complements (A ε t) (hsA ε t) ⊥ ⊤ ?_
        (fun x _ hx0 => hpd x hx0) ?_
      · intro x hx hx0
        exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
      · simp
  · -- the corrected carrier is positive semidefinite at `t₀`
    have hw : |ts + τC - ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC - ε * κ - ts - τC = -(ε * κ) by ring, abs_neg, abs_of_pos hεκ])
    obtain ⟨-, hdD, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC - ε * κ - ts - τC) = ε * |c| / 3 := by
      have h : σ * (ts + τC - ε * κ - ts - τC) = ε * (s * κ) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    have hperp := perp_lower (A 0 ts) (A ε (ts + τC - ε * κ) - D ε) K hgap hdD
    have hsM : ∀ x y, ⟪(A ε (ts + τC - ε * κ) - D ε) x, y⟫ =
        ⟪x, (A ε (ts + τC - ε * κ) - D ε) y⟫ := by
      intro x y
      simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
    have hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε (ts + τC - ε * κ) - D ε) x⟫ := by
      refine block_pos _ hsM K (a := ε * |c| / 4) (g := g / 2) (b := ε * C)
        (by have := mul_pos hε hcabs; linarith) ?_ ?_ ?_ ?_
      · have h3 : ε * (ε * C ^ 2 * 16) < ε * (|c| * g) := mul_lt_mul_of_pos_left hεC2 hε
        have hpos : 0 < ε * (|c| * g) := mul_pos hε (mul_pos hcabs hg)
        linarith
      · intro u hu
        have h := (abs_le.mp (hKD u hu)).1
        rw [hval] at h
        have hun : 0 ≤ ‖u‖ ^ 2 := pow_nonneg (norm_nonneg u) 2
        linarith
      · intro y hy
        have h := hperp y hy
        have hyn : 0 ≤ ‖y‖ ^ 2 := pow_nonneg (norm_nonneg y) 2
        have : (g / 2) * ‖y‖ ^ 2 ≤ (g - ε * C) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hyn
        linarith
      · intro u hu y _
        exact cross_upper (A 0 ts) _ hs0 K hker hdD u hu y
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpd v hv).le
  · -- a negative direction of the corrected carrier at `t₁`
    have hw : |ts + τC + ε * κ - ts - τC| ≤ ε * κ := le_of_eq (by
      rw [show ts + τC + ε * κ - ts - τC = ε * κ by ring, abs_of_pos hεκ])
    obtain ⟨-, -, -, hKD⟩ := window _ hw
    have hval : σ * (ts + τC + ε * κ - ts - τC) = -(ε * |c| / 3) := by
      have h : σ * (ts + τC + ε * κ - ts - τC) = -(ε * (s * κ)) := by rw [hs_def]; ring
      rw [h, hsκ]; ring
    refine ⟨u₀, ?_⟩
    have h := (abs_le.mp (hKD u₀ hu₀K)).2
    rw [hval] at h
    have hun : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
    have hp : 0 < ε * |c| * ‖u₀‖ ^ 2 := mul_pos (mul_pos hε hcabs) hun
    linarith

omit [FiniteDimensional ℝ E] in
/-- A symmetric operator commuting with an orthogonal map `J` acts as a scalar on the
plane spanned by `u₀` and `J u₀` whenever `J (J u₀) = -u₀` (a complex line of a `U(1)`
symmetry).  This is how the scalar hypotheses of `perturbative_sign_change` arise from
the diagonal `U(1)` symmetry of the curved twist family. -/
theorem scalar_on_complex_line (M J : E →L[ℝ] E) (hM : ∀ x y, ⟪M x, y⟫ = ⟪x, M y⟫)
    (hJ : ∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) (hMJ : ∀ x, M (J x) = J (M x))
    (u₀ : E) (hu₀ : u₀ ≠ 0) (hJJ : J (J u₀) = -u₀) :
    ∃ l : ℝ, ∀ u ∈ Submodule.span ℝ {u₀, J u₀}, ⟪u, M u⟫ = l * ‖u‖ ^ 2 := by
  have h01' : ⟪u₀, J u₀⟫ = -⟪u₀, J u₀⟫ := by
    calc ⟪u₀, J u₀⟫ = ⟪J u₀, J (J u₀)⟫ := (hJ _ _).symm
      _ = ⟪J u₀, -u₀⟫ := by rw [hJJ]
      _ = -⟪J u₀, u₀⟫ := inner_neg_right _ _
      _ = -⟪u₀, J u₀⟫ := by rw [real_inner_comm u₀ (J u₀)]
  have h01 : ⟪u₀, J u₀⟫ = 0 := by linarith
  have h10 : ⟪J u₀, u₀⟫ = 0 := by rw [real_inner_comm]; exact h01
  have hJn : ⟪J u₀, J u₀⟫ = ⟪u₀, u₀⟫ := hJ u₀ u₀
  have e1 : ⟪J u₀, M u₀⟫ = ⟪u₀, M (J u₀)⟫ :=
    (hM (J u₀) u₀).symm.trans (real_inner_comm u₀ (M (J u₀)))
  have h1 : ⟪u₀, M (J u₀)⟫ = -⟪u₀, M (J u₀)⟫ := by
    calc ⟪u₀, M (J u₀)⟫ = ⟪J u₀, J (M (J u₀))⟫ := (hJ _ _).symm
      _ = ⟪J u₀, M (J (J u₀))⟫ := by rw [hMJ (J u₀)]
      _ = ⟪J u₀, M (-u₀)⟫ := by rw [hJJ]
      _ = -⟪J u₀, M u₀⟫ := by rw [map_neg, inner_neg_right]
      _ = -⟪u₀, M (J u₀)⟫ := by rw [e1]
  have hc1 : ⟪u₀, M (J u₀)⟫ = 0 := by linarith
  have hc2 : ⟪J u₀, M u₀⟫ = 0 := by rw [e1]; exact hc1
  have hd : ⟪J u₀, M (J u₀)⟫ = ⟪u₀, M u₀⟫ := by rw [hMJ u₀]; exact hJ _ _
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  refine ⟨⟪u₀, M u₀⟫ / ‖u₀‖ ^ 2, fun u hu => ?_⟩
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  have hform : ⟪a • u₀ + b • J u₀, M (a • u₀ + b • J u₀)⟫ =
      (a ^ 2 + b ^ 2) * ⟪u₀, M u₀⟫ := by
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hc1, hc2, hd]
    ring
  have hnorm : ‖a • u₀ + b • J u₀‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u₀‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hJn, h01, h10]
    ring
  rw [hform, hnorm, div_mul_eq_mul_div, eq_div_iff hn.ne']
  ring

/-- First-order expansion from joint Fréchet differentiability at `(0, ts)`. -/
theorem expansion_of_hasFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ → F) (ts : ℝ) (Fe Ft : F)
    (h : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) ((0 : ℝ), ts)) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε τ : ℝ, |ε| < r → |τ| < r →
      ‖f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe‖ ≤ η * (|ε| + |τ|) := by
  intro η hη
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε τ hε hτ => ?_⟩
  have hd : dist ((ε, τ) : ℝ × ℝ) 0 < r := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    exact max_lt hε hτ
  have heq : f ε (ts + τ) - f 0 ts - τ • Ft - ε • Fe =
      (fun p : ℝ × ℝ => f p.1 p.2) (((0 : ℝ), ts) + (ε, τ)) -
      (fun p : ℝ × ℝ => f p.1 p.2) ((0 : ℝ), ts) -
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Fe +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Ft) (ε, τ) := by
    simp only [Prod.mk_add_mk, zero_add, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    abel
  have hn : ‖((ε, τ) : ℝ × ℝ)‖ ≤ |ε| + |τ| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg τ]) (by linarith [abs_nonneg ε])
  rw [heq]
  calc _ ≤ η * ‖((ε, τ) : ℝ × ℝ)‖ := hball hd
    _ ≤ η * (|ε| + |τ|) := mul_le_mul_of_nonneg_left hn hη.le

/-- First-order expansion from differentiability at `0`, for a map vanishing at `0`. -/
theorem expansion_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (Fe : F) (h0 : f 0 = 0) (h : HasDerivAt f Fe 0) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| < r → ‖f ε - ε • Fe‖ ≤ η * |ε| := by
  intro η hη
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.mp h
  rw [Asymptotics.isLittleO_iff] at hlo
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hη)
  refine ⟨r, hr, fun ε hε => ?_⟩
  have hd : dist ε 0 < r := by rw [Real.dist_eq, sub_zero]; exact hε
  have hb := hball hd
  simp only [zero_add, h0, sub_zero, Real.norm_eq_abs] at hb
  exact hb

/-! ### Pre-crossing separation from first-order data, without derivatives in the angle

The theorem `first_order_separation` below needs, at zero curvature, only that the
carrier is positive definite at angles arbitrarily close before a crossing angle `ts`
and has a negative direction at angles arbitrarily close after it.  For the curvature
it needs joint continuity at zero curvature, and a first-order expansion of the
correction whose coefficient is positive definite on the kernel of the vacuum carrier
at `ts`.  No derivative in the angle, no spectral-gap constant and no scalar action
on the kernel are assumed; the gap is produced by compactness.  The sign is the
pre-crossing one; for the families below the opposite sign is reached by reflecting
the interior profile. -/

/-- A positive definite symmetric operator is a unit. -/
theorem unit_of_pos (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : IsUnit X := by
  refine unit_of_definite_complements X hs ⊥ ⊤ ?_ (fun x _ hx0 => hpos x hx0) ?_
  · intro x hx hx0
    exact absurd ((Submodule.mem_bot ℝ).mp hx) hx0
  · simp

omit [FiniteDimensional ℝ E] in
theorem psd_of_pos (X : E →L[ℝ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪x, X x⟫) : PSD X := by
  intro x
  by_cases hx : x = 0
  · rw [hx, inner_zero_left]
  · exact (hpos x hx).le

omit [FiniteDimensional ℝ E] in
/-- Positive semidefiniteness at an angle that is a limit of positive definite angles. -/
theorem psd_of_pd_before (F : ℝ → E →L[ℝ] E) (hc : Continuous F) (ts : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, F t₀ x⟫) : PSD (F ts) := by
  intro x
  by_contra hneg
  have hx : ⟪x, F ts x⟫ < 0 := lt_of_not_ge hneg
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hcont : Continuous fun t => ⟪x, F t x⟫ :=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hev : ∀ᶠ t in nhds ts, ⟪x, F t x⟫ < 0 :=
    Filter.Tendsto.eventually (hcont.tendsto ts) (gt_mem_nhds hx)
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨t₀, h1, h2, h3⟩ := h η hη
  have hd : dist t₀ ts < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have h4 := hball hd
  have h5 := h3 x hx0
  linarith

/-- A positive semidefinite symmetric operator is bounded below by some `g > 0` on the
orthogonal complement of any subspace containing its kernel (compactness of the unit
sphere). -/
theorem exists_gap_of_psd (X : E →L[ℝ] E) (hs : ∀ x y, ⟪X x, y⟫ = ⟪x, X y⟫) (hp : PSD X)
    (K : Submodule ℝ E) (hK : ∀ v, X v = 0 → v ∈ K) :
    ∃ g : ℝ, 0 < g ∧ ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, X y⟫ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hunit : ∀ y ∈ Kᗮ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E) := by
    intro y hy hy0
    refine ⟨?_, Submodule.smul_mem _ _ hy⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hy0).ne']
  by_cases hne : (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)).Nonempty
  · have hS : IsCompact (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (isCompact_sphere (0 : E) 1).inter_right (Submodule.isClosed_orthogonal K)
    have hcont : ContinuousOn (fun y => ⟪y, X y⟫) (Metric.sphere (0 : E) 1 ∩ (Kᗮ : Set E)) :=
      (continuous_id.inner X.continuous).continuousOn
    obtain ⟨y₀, hy₀, hmin⟩ := hS.exists_isMinOn hne hcont
    have hy₀n : ‖y₀‖ = 1 := mem_sphere_zero_iff_norm.mp hy₀.1
    have hy₀K : y₀ ∈ Kᗮ := hy₀.2
    refine ⟨⟪y₀, X y₀⟫, ?_, ?_⟩
    · rcases (hp y₀).lt_or_eq with h | h
      · exact h
      · exfalso
        have hX0 : X y₀ = 0 := psd_kernel X hs hp y₀ h.symm
        have h0 : ⟪y₀, y₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (hK y₀ hX0) hy₀K
        have hy0 : y₀ = 0 := inner_self_eq_zero.mp h0
        rw [hy0, norm_zero] at hy₀n
        exact zero_ne_one hy₀n
    · intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        simp
      · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
        have h1 : ⟪y₀, X y₀⟫ ≤ ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ :=
          isMinOn_iff.mp hmin _ (hunit y hy hy0)
        have h2 : ⟪‖y‖⁻¹ • y, X (‖y‖⁻¹ • y)⟫ = (‖y‖ ^ 2)⁻¹ * ⟪y, X y⟫ := by
          rw [map_smul, real_inner_smul_left, real_inner_smul_right]
          ring
        rw [h2, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hyn 2)] at h1
        exact h1
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      simp
    · exact absurd ⟨_, hunit y hy hy0⟩ hne

/-- Positivity of a two-variable quadratic form. -/
theorem quad_pos {a b g U Y : ℝ} (ha : 0 < a) (hab : b ^ 2 < a * g) (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hne : U ≠ 0 ∨ Y ≠ 0) : 0 < a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2 := by
  have hQ : a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) =
      (a * U - b * Y) ^ 2 + (a * g - b ^ 2) * Y ^ 2 := by ring
  have hm : 0 < a * (a * U ^ 2 - 2 * b * U * Y + g * Y ^ 2) := by
    rw [hQ]
    by_cases hY0 : Y = 0
    · have hU0 : U ≠ 0 := by
        rcases hne with h | h
        · exact h
        · exact absurd hY0 h
      have hUp : 0 < U := lt_of_le_of_ne hU (Ne.symm hU0)
      subst hY0
      have h1 : 0 < (a * U) ^ 2 := pow_pos (mul_pos ha hUp) 2
      have e : (a * U - b * 0) ^ 2 + (a * g - b ^ 2) * 0 ^ 2 = (a * U) ^ 2 := by ring
      rw [e]
      exact h1
    · have hYp : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
      have h1 : 0 < (a * g - b ^ 2) * Y ^ 2 := mul_pos (by linarith) (pow_pos hYp 2)
      linarith [sq_nonneg (a * U - b * Y)]
  by_contra hcon
  have h2 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  rw [mul_zero] at h2
  linarith

/-- **The pre-crossing comparison.**  Let `A₀` vanish on `K` and be `≥ g` on `Kᗮ`, and let
`De ≥ c` on `K`.  If `C` is positive semidefinite (it may be singular) and `δ`-close to
`A₀`, then `C + ε De + R` is positive definite once `δ`, `ε` and `‖R‖/ε` are below
thresholds depending only on `g`, `c` and `‖De‖` (`κ` below).  The cross terms between
`K` and `Kᗮ` are absorbed by a fraction `κ ε` of the positive semidefinite form of `C`. -/
theorem pos_of_psd_add (A₀ C De R : E →L[ℝ] E) (K : Submodule ℝ E)
    (hs0 : ∀ x y, ⟪A₀ x, y⟫ = ⟪x, A₀ y⟫) (hsC : ∀ x y, ⟪C x, y⟫ = ⟪x, C y⟫)
    (hker : ∀ u ∈ K, A₀ u = 0) {g c δ ε μ κ : ℝ} (hg : 0 < g) (hc : 0 < c)
    (hgap : ∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, A₀ y⟫)
    (hDe : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c)
    (hC : PSD C) (hδ : ‖C - A₀‖ ≤ δ) (hδg : δ ≤ g / 2) (hκδ : κ * δ ≤ 1)
    (hε : 0 < ε) (hκε : κ * ε ≤ 1) (hμ : μ ≤ c / 4) (hR : ‖R‖ ≤ μ * ε) :
    ∀ x : E, x ≠ 0 → 0 < ⟪x, (C + ε • De + R) x⟫ := by
  intro x hx
  obtain ⟨u, hu, y, hy, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hd0 : 0 ≤ ‖De‖ := norm_nonneg _
  have hU0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hδ
  have hμε0 : 0 ≤ μ * ε := le_trans (norm_nonneg _) hR
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  have hκpos : 0 < κ := by
    by_contra hk
    have h1 := mul_le_mul_of_nonneg_right (not_lt.mp hk) (le_of_lt (half_pos hg))
    rw [zero_mul] at h1
    linarith
  have hκε0 : 0 ≤ κ * ε := (mul_pos hκpos hε).le
  -- expansions
  have hC1 : ⟪u + y, C (u + y)⟫ = ⟪u, C u⟫ + 2 * ⟪u, C y⟫ + ⟪y, C y⟫ := by
    have hsym : ⟪y, C u⟫ = ⟪u, C y⟫ := by rw [← hsC y u, real_inner_comm]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hsym]
    ring
  have hD1 : ⟪u + y, De (u + y)⟫ = ⟪u, De u⟫ + ⟪u, De y⟫ + ⟪y, De u⟫ + ⟪y, De y⟫ := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have hQ : ⟪u + y, (C + ε • De + R) (u + y)⟫ =
      ⟪u + y, C (u + y)⟫ + ε * ⟪u + y, De (u + y)⟫ + ⟪u + y, R (u + y)⟫ := by
    simp only [add_apply, smul_apply, inner_add_right, real_inner_smul_right]
  -- the bounds
  have hCnn : 0 ≤ ⟪u + y, C (u + y)⟫ := hC _
  have hCu : 0 ≤ ⟪u, C u⟫ := hC u
  have hCuy := (abs_le.mp (cross_upper A₀ C hs0 K hker hδ u hu y)).1
  have hCy := perp_lower A₀ C K hgap hδ y hy
  have hDu := hDe u hu
  have hDuy := (abs_le.mp (abs_inner_op_le De u y)).1
  have hDyu := (abs_le.mp (abs_inner_op_le De y u)).1
  have hDy := (abs_le.mp (abs_inner_op_le De y y)).1
  have hRx : -(μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2))) ≤ ⟪u + y, R (u + y)⟫ := by
    have h1 := (abs_le.mp (abs_inner_op_le R (u + y) (u + y))).1
    have hx0 : 0 ≤ ‖u + y‖ := norm_nonneg _
    have hxn : ‖u + y‖ ≤ ‖u‖ + ‖y‖ := norm_add_le u y
    have h3a : ‖u + y‖ * ‖u + y‖ ≤ (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) :=
      mul_le_mul hxn hxn hx0 (by linarith)
    have e3 : 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) - (‖u‖ + ‖y‖) * (‖u‖ + ‖y‖) = (‖u‖ - ‖y‖) ^ 2 := by
      ring
    have h3 : ‖u + y‖ * ‖u + y‖ ≤ 2 * (‖u‖ ^ 2 + ‖y‖ ^ 2) := by
      linarith [sq_nonneg (‖u‖ - ‖y‖)]
    have h4 : ‖R‖ * ‖u + y‖ * ‖u + y‖ ≤ μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by
      calc ‖R‖ * ‖u + y‖ * ‖u + y‖ = ‖R‖ * (‖u + y‖ * ‖u + y‖) := by ring
        _ ≤ (μ * ε) * (‖u + y‖ * ‖u + y‖) :=
          mul_le_mul_of_nonneg_right hR (mul_nonneg hx0 hx0)
        _ ≤ (μ * ε) * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h3 hμε0
        _ = μ * ε * (2 * (‖u‖ ^ 2 + ‖y‖ ^ 2)) := by ring
    linarith
  -- a fraction `κ ε` of the form of `C` absorbs the cross terms
  have hw1 : κ * ε * ⟪u + y, C (u + y)⟫ ≤ ⟪u + y, C (u + y)⟫ := by
    have h1 := mul_nonneg (sub_nonneg.mpr hκε) hCnn
    have e : (1 - κ * ε) * ⟪u + y, C (u + y)⟫ =
        ⟪u + y, C (u + y)⟫ - κ * ε * ⟪u + y, C (u + y)⟫ := by ring
    linarith
  have e5 : κ * ε * ⟪u + y, C (u + y)⟫ =
      κ * ε * ⟪u, C u⟫ + 2 * (κ * ε * ⟪u, C y⟫) + κ * ε * ⟪y, C y⟫ := by
    rw [hC1]
    ring
  have e6 : ε * ⟪u + y, De (u + y)⟫ =
      ε * ⟪u, De u⟫ + ε * ⟪u, De y⟫ + ε * ⟪y, De u⟫ + ε * ⟪y, De y⟫ := by
    rw [hD1]
    ring
  have h5a := mul_le_mul_of_nonneg_left hCuy hκε0
  have h5b := mul_le_mul_of_nonneg_left hCy hκε0
  have h5c := mul_nonneg hκε0 hCu
  have h6a := mul_le_mul_of_nonneg_left hDu hε.le
  have h6b := mul_le_mul_of_nonneg_left hDuy hε.le
  have h6c := mul_le_mul_of_nonneg_left hDyu hε.le
  have h6d := mul_le_mul_of_nonneg_left hDy hε.le
  -- the reduced two-variable form is positive
  have hbr : 0 < (c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2 := by
    have ha' : c / 2 ≤ c - 2 * μ := by linarith
    have hgd : κ * (g / 2) ≤ κ * (g - δ) := mul_le_mul_of_nonneg_left (by linarith) hκpos.le
    have hg' : c / 2 + 4 * (‖De‖ + 1) ^ 2 / c ≤ κ * (g - δ) - ‖De‖ - 2 * μ := by linarith
    have hprod : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) ≤
        (c - 2 * μ) * (κ * (g - δ) - ‖De‖ - 2 * μ) :=
      mul_le_mul ha' hg' (by linarith) (by linarith)
    have hcc : c / 2 * (4 * (‖De‖ + 1) ^ 2 / c) = 2 * (‖De‖ + 1) ^ 2 := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero two_ne_zero hc.ne')]
      ring
    have hval : (c / 2) * (c / 2 + 4 * (‖De‖ + 1) ^ 2 / c) =
        c ^ 2 / 4 + 2 * (‖De‖ + 1) ^ 2 := by
      rw [mul_add, hcc]
      ring
    have hb0 : 0 ≤ κ * δ + ‖De‖ := by
      have := mul_nonneg hκpos.le hδ0
      linarith
    have hb1 : κ * δ + ‖De‖ ≤ 1 + ‖De‖ := by linarith
    have hbsq : (κ * δ + ‖De‖) * (κ * δ + ‖De‖) ≤ (1 + ‖De‖) * (1 + ‖De‖) :=
      mul_le_mul hb1 hb1 hb0 (by linarith)
    have hd1 : 0 < (1 + ‖De‖) * (1 + ‖De‖) := by positivity
    have hc2 : 0 ≤ c ^ 2 / 4 := by positivity
    have e7 : (‖De‖ + 1) ^ 2 = (1 + ‖De‖) * (1 + ‖De‖) := by ring
    have e8 : (κ * δ + ‖De‖) ^ 2 = (κ * δ + ‖De‖) * (κ * δ + ‖De‖) := by ring
    refine quad_pos (by linarith) ?_ hU0 hY0 ?_
    · rw [e8]
      linarith [hbsq, hprod, hval, hd1, hc2, e7]
    · by_contra hcon
      apply hx
      have h1 : ‖u‖ = 0 := by
        by_contra h
        exact hcon (Or.inl h)
      have h2 : ‖y‖ = 0 := by
        by_contra h
        exact hcon (Or.inr h)
      rw [norm_eq_zero.mp h1, norm_eq_zero.mp h2, add_zero]
  have hfin : ε * ((c - 2 * μ) * ‖u‖ ^ 2 - 2 * (κ * δ + ‖De‖) * ‖u‖ * ‖y‖ +
      (κ * (g - δ) - ‖De‖ - 2 * μ) * ‖y‖ ^ 2) ≤ ⟪u + y, (C + ε • De + R) (u + y)⟫ := by
    rw [hQ]
    linarith
  have := mul_pos hε hbr
  linarith

omit [FiniteDimensional ℝ E] in
/-- The metric form of joint continuity at a point of zero curvature. -/
theorem metric_of_continuousAt {F : Type*} [SeminormedAddCommGroup F] (f : ℝ → ℝ → F) (t : ℝ)
    (h : ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (0, t)) :
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ ∀ ε s : ℝ, |ε| < r → |s - t| < r →
      ‖f ε s - f 0 t‖ < δ := by
  intro δ hδ
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp h δ hδ
  refine ⟨r, hr, fun ε s hε hs => ?_⟩
  have hd : dist ((ε, s) : ℝ × ℝ) (0, t) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt hε hs
  have h1 := hball hd
  simp only [dist_eq_norm] at h1
  exact h1

/-- **First-order guarded separation (pre-crossing).**  `A ε t` is the carrier at curvature
`ε` and angle `t`, `D ε` the correction.  Hypotheses: symmetry; continuity in the angle at
every curvature; joint continuity at zero curvature near `ts` (metric form); at zero
curvature the carrier is positive definite at angles arbitrarily close before `ts` and has a negative
direction at angles arbitrarily close after `ts`; the correction is `ε De + o(ε)` with
`De ≥ c > 0` on the kernel of `A 0 ts`.  Then at every small positive curvature some
angle has a positive definite (hence unit) carrier and a singular corrected carrier. -/
theorem first_order_separation
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (hsA : ∀ ε t x y, ⟪A ε t x, y⟫ = ⟪x, A ε t y⟫)
    (hsD : ∀ ε x y, ⟪D ε x, y⟫ = ⟪x, D ε y⟫)
    (hcA : ∀ ε, Continuous (A ε)) (ts : ℝ)
    (hjoint : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖A ε s - A 0 t‖ < δ)
    (hbefore : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x : E, x ≠ 0 → 0 < ⟪x, A 0 t₀ x⟫)
    (hafter : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w : E, ⟪w, A 0 t₁ w⟫ < 0)
    (c : ℝ) (De : E →L[ℝ] E) (hc : 0 < c)
    (hDe : ∀ u : E, A 0 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫)
    (hDexp : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖D ε - ε • De‖ ≤ μ * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ t : ℝ, IsUnit (A ε t) ∧ ¬ IsUnit (A ε t - D ε) := by
  have hsC : ∀ ε t x y, ⟪(A ε t - D ε) x, y⟫ = ⟪x, (A ε t - D ε) y⟫ := by
    intro ε t x y
    simp only [sub_apply, inner_sub_left, inner_sub_right, hsA, hsD]
  -- the vacuum carrier at `ts`: positive semidefinite, with a gap off its kernel
  have hpsd : PSD (A 0 ts) := psd_of_pd_before (A 0) (hcA 0) ts hbefore
  obtain ⟨K, hK_def⟩ : ∃ K : Submodule ℝ E, K = LinearMap.ker (A 0 ts : E →ₗ[ℝ] E) := ⟨_, rfl⟩
  have hmemK : ∀ v, v ∈ K ↔ A 0 ts v = 0 := by
    intro v
    rw [hK_def, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have hker : ∀ u ∈ K, A 0 ts u = 0 := fun u hu => (hmemK u).mp hu
  obtain ⟨g, hg, hgap⟩ := exists_gap_of_psd (A 0 ts) (hsA 0 ts) hpsd K
    (fun v hv => (hmemK v).mpr hv)
  have hDeK : ∀ u ∈ K, c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ :=
    fun u hu => hDe u (hker u hu)
  -- constants
  have hpos4 : 0 < 4 * (‖De‖ + 1) ^ 2 / c := div_pos (by positivity) hc
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    rw [hκ_def]
    exact mul_pos (div_pos two_pos hg) (by linarith [norm_nonneg De])
  have hκ : κ * (g / 2) = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by
    have h2g : 2 / g * (g / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 g, div_self (mul_ne_zero hg.ne' two_ne_zero)]
    rw [hκ_def]
    calc 2 / g * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) * (g / 2)
        = (2 / g * (g / 2)) * (‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c) := by ring
      _ = ‖De‖ + c + 4 * (‖De‖ + 1) ^ 2 / c := by rw [h2g, one_mul]
  obtain ⟨δ₀, hδ₀_def⟩ : ∃ δ₀ : ℝ, δ₀ = min (g / 2) (1 / κ) := ⟨_, rfl⟩
  have hδ₀ : 0 < δ₀ := by rw [hδ₀_def]; exact lt_min (half_pos hg) (one_div_pos.mpr hκpos)
  have hδ₀g : δ₀ ≤ g / 2 := by rw [hδ₀_def]; exact min_le_left _ _
  have hκδ₀ : κ * δ₀ ≤ 1 := by
    have h := min_le_right (g / 2) (1 / κ)
    rw [← hδ₀_def] at h
    calc κ * δ₀ ≤ κ * (1 / κ) := mul_le_mul_of_nonneg_left h hκpos.le
      _ = 1 := mul_one_div_cancel hκpos.ne'
  -- the window, the correction size and the endpoints
  obtain ⟨η₀, hη₀, hjoint⟩ := hjoint
  obtain ⟨r₁, hr₁, hA1⟩ := hjoint ts (by simp [hη₀]) (δ₀ / 2) (half_pos hδ₀)
  obtain ⟨r₂, hr₂, hD2⟩ := hDexp (c / 4) (by linarith)
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min r₁ η₀ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact lt_min hr₁ hη₀
  have hρ1 : ρ ≤ r₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρ2 : ρ ≤ η₀ := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨t₀, ht₀a, ht₀b, hpd₀⟩ := hbefore ρ hρ
  obtain ⟨t₁, ht₁a, ht₁b, w, hw⟩ := hafter ρ hρ
  obtain ⟨m, hm, hmc⟩ := psd_coercive (A 0 t₀) (hsA 0 t₀) (psd_of_pos _ hpd₀)
    (unit_of_pos _ (hsA 0 t₀) hpd₀)
  obtain ⟨r₃, hr₃, hA3⟩ := hjoint t₀ (by rw [abs_lt]; constructor <;> linarith) (m / 2)
    (half_pos hm)
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = -⟪w, A 0 t₁ w⟫ := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; linarith
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = ‖w‖ ^ 2 + 1 := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hW_def]; positivity
  have hwW : ‖w‖ * ‖w‖ ≤ W := by
    rw [hW_def]
    have e : ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
    rw [e]
    linarith
  obtain ⟨r₄, hr₄, hA4⟩ := hjoint t₁ (by rw [abs_lt]; constructor <;> linarith) (ν / (2 * W))
    (div_pos hν (by linarith))
  obtain ⟨Dc, hDc_def⟩ : ∃ Dc : ℝ, Dc = ‖De‖ + c / 4 + 1 := ⟨_, rfl⟩
  have hDc : 0 < Dc := by rw [hDc_def]; linarith [norm_nonneg De]
  have hDsmall : ∀ ε : ℝ, 0 < ε → ε < r₂ → ‖D ε‖ ≤ Dc * ε := by
    intro ε hε hεr
    have h1 := hD2 ε hε hεr
    have h2 : ‖D ε‖ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := by
      calc ‖D ε‖ = ‖(D ε - ε • De) + ε • De‖ := by rw [sub_add_cancel]
        _ ≤ ‖D ε - ε • De‖ + ‖ε • De‖ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h2
    rw [hDc_def]
    linarith
  have h2Dc : 0 < 2 * Dc := by linarith
  have h2WDc : 0 < 2 * W * Dc := mul_pos (mul_pos two_pos hW) hDc
  refine ⟨min (min (min r₁ r₂) (min r₃ r₄))
      (min (min (1 / κ) (δ₀ / (2 * Dc))) (min (m / (2 * Dc)) (ν / (2 * W * Dc)))), ?_, ?_⟩
  · exact lt_min (lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄))
      (lt_min (lt_min (one_div_pos.mpr hκpos) (div_pos hδ₀ h2Dc))
        (lt_min (div_pos hm h2Dc) (div_pos hν h2WDc)))
  intro ε hε hε₀
  have e1 : ε < r₁ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e2 : ε < r₂ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e3 : ε < r₃ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e4 : ε < r₄ := lt_of_lt_of_le hε₀
    (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have e5 : ε < 1 / κ := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have e6 : ε < δ₀ / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have e7 : ε < m / (2 * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e8 : ε < ν / (2 * W * Dc) := lt_of_lt_of_le hε₀
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hεabs : |ε| = ε := abs_of_pos hε
  have hDε := hDsmall ε hε e2
  have hDε1 : ‖D ε‖ < δ₀ / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e6
    linarith
  have hDε2 : ‖D ε‖ < m / 2 := by
    have h := (lt_div_iff₀ h2Dc).mp e7
    linarith
  have hDε3 : ‖D ε‖ * (2 * W) < ν := by
    have h := (lt_div_iff₀ h2WDc).mp e8
    have h' := mul_le_mul_of_nonneg_right hDε (by linarith : (0 : ℝ) ≤ 2 * W)
    linarith
  have hκε : κ * ε ≤ 1 := by
    have h := (lt_div_iff₀ hκpos).mp e5
    linarith
  -- the corrected carrier is positive definite at `t₀`
  have hC0 : ∀ x : E, x ≠ 0 → 0 < ⟪x, (A ε t₀ - D ε) x⟫ := by
    intro x hx
    have h1 := hmc x
    have h2 : ‖A ε t₀ - A 0 t₀‖ < m / 2 := hA3 ε t₀ (by rw [hεabs]; exact e3) (by simp [hr₃])
    have hxx : 0 < ‖x‖ * ‖x‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hx)
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₀ - A 0 t₀) x x)).1
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) x x)).2
    have e : ⟪x, (A ε t₀ - D ε) x⟫ = ⟪x, A 0 t₀ x⟫ + ⟪x, (A ε t₀ - A 0 t₀) x⟫ - ⟪x, D ε x⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    have h5 := mul_lt_mul_of_pos_right h2 hxx
    have h6 := mul_lt_mul_of_pos_right hDε2 hxx
    have e' : ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
    rw [e]
    rw [e'] at h1
    linarith
  -- and has a negative direction at `t₁`
  have hC1 : ⟪w, (A ε t₁ - D ε) w⟫ < 0 := by
    have h2 : ‖A ε t₁ - A 0 t₁‖ < ν / (2 * W) := hA4 ε t₁ (by rw [hεabs]; exact e4) (by simp [hr₄])
    have h2' : ‖A ε t₁ - A 0 t₁‖ * (2 * W) < ν := (lt_div_iff₀ (by linarith)).mp h2
    have h3 := (abs_le.mp (abs_inner_op_le (A ε t₁ - A 0 t₁) w w)).2
    have h4 := (abs_le.mp (abs_inner_op_le (D ε) w w)).1
    have h5 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (A ε t₁ - A 0 t₁))
    have h6 := mul_le_mul_of_nonneg_left hwW (norm_nonneg (D ε))
    have e : ⟪w, (A ε t₁ - D ε) w⟫ = ⟪w, A 0 t₁ w⟫ + ⟪w, (A ε t₁ - A 0 t₁) w⟫ - ⟪w, D ε w⟫ := by
      simp only [sub_apply, inner_sub_right]
      ring
    rw [e]
    linarith
  -- the first singular corrected carrier on the window
  have hF : Continuous fun s : ℝ => A ε (t₀ + s) - D ε :=
    ((hcA ε).comp (continuous_const.add continuous_id)).sub continuous_const
  have hT : t₀ + (t₁ - t₀) = t₁ := by ring
  obtain ⟨s, hs0, hsT, hpsdF, hnuF, -, -⟩ := first_carrier_crossing
    (fun s : ℝ => A ε (t₀ + s) - D ε) hF (fun s x y => hsC ε (t₀ + s) x y)
    (by simpa only [add_zero] using psd_of_pos _ hC0)
    (by simpa only [add_zero] using unit_of_pos _ (hsC ε t₀) hC0)
    (t₁ - t₀) (by linarith) w (by simpa only [hT] using hC1)
  have hwin : ‖A ε (t₀ + s) - A 0 ts‖ < δ₀ / 2 := hA1 ε (t₀ + s) (by rw [hεabs]; exact e1)
    (by rw [abs_lt]; constructor <;> linarith)
  have hCδ : ‖(A ε (t₀ + s) - D ε) - A 0 ts‖ ≤ δ₀ := by
    have e : (A ε (t₀ + s) - D ε) - A 0 ts = (A ε (t₀ + s) - A 0 ts) - D ε := by abel
    rw [e]
    calc ‖(A ε (t₀ + s) - A 0 ts) - D ε‖ ≤ ‖A ε (t₀ + s) - A 0 ts‖ + ‖D ε‖ := norm_sub_le _ _
      _ ≤ δ₀ := by linarith
  have hpd := pos_of_psd_add (A 0 ts) (A ε (t₀ + s) - D ε) De (D ε - ε • De)
    K (hsA 0 ts) (hsC ε (t₀ + s)) hker hg hc hgap hDeK hκ hpsdF hCδ
    hδ₀g hκδ₀ hε hκε le_rfl (hD2 ε hε e2)
  have hAeq : (A ε (t₀ + s) - D ε) + ε • De + (D ε - ε • De) = A ε (t₀ + s) := by abel
  refine ⟨t₀ + s, unit_of_pos _ (hsA ε (t₀ + s)) (fun x hx => ?_), hnuF⟩
  have h := hpd x hx
  rwa [hAeq] at h

end Abstract

#print axioms abs_inner_op_le
#print axioms block_pos
#print axioms kernel_form
#print axioms expansion_dist
#print axioms perp_lower
#print axioms cross_upper
#print axioms kernel_form_bounds
#print axioms perturbative_sign_change
#print axioms scalar_on_complex_line
#print axioms expansion_of_hasFDerivAt
#print axioms expansion_of_hasDerivAt
#print axioms unit_of_pos
#print axioms psd_of_pos
#print axioms psd_of_pd_before
#print axioms exists_gap_of_psd
#print axioms quad_pos
#print axioms pos_of_psd_add
#print axioms metric_of_continuousAt
#print axioms first_order_separation

end AdalyFormal.Round9.Guarded.Qualitative

/-! ## Curved twist families with a free interior profile and a free exterior path

The class leaves the exterior field free and allows every bounded interior amplitude mask
(round 5 `maskedU`, `masked_regular`).  A counterexample may therefore use any continuous
one-parameter family `V` of exterior configurations (round 5 uses the frozen twist `Uth`)
and any interior profile `f` with `|f| ≤ 1`, scaled by the curvature `ε`.  At `ε = 0`
the interior is flat whatever `f` is, and the correction vanishes; only the first-order
correction depends on `f`. -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.Balaban.RegularUPerturbation (bondEnergy)
open AdalyFormal.D1Literal (PSD)

/-- Interior amplitudes `ε • f` on every bond touching `Ω₀`, the exterior path `V t` on
the purely exterior bonds. -/
noncomputable def pathU (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) : LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  maskedU q R (fun e => ε * f e) (V t)

noncomputable def pathP (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) : IngrBParams :=
  gparams 2 1 (dilLu q R) (by norm_num) (dilTower q R) (pathU q R V f ε t) a (dilLam q R)

/-- The actual all-plaquette carrier of the family. -/
noncomputable def pathA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selAll selAll (pathP q R V f ε a t)).Ginv

/-- The actual localized correction of the family. -/
noncomputable def pathD (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  (dataS selIn selIn (pathP q R V f ε a t)).Delta2 (dataS_laws selIn selIn _)

theorem path_agrees (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε s t : ℝ)
    (e : Bond (scaleUp 2 1 (dilLu q R)))
    (he : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)) :
    pathU q R V f ε s e = pathU q R V f ε t e := by
  classical
  simp only [pathU, maskedU, if_neg he]

theorem path_cont (q R : ℕ) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) :
    AdalyFormal.D1Literal.ContFam (pathU q R V f ε) := by
  classical
  intro e
  by_cases he : e ∈ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0)
  · simp only [pathU, maskedU, if_pos he]
    exact hV e
  · simp only [pathU, maskedU, if_neg he]
    exact continuous_const

/-- Continuity of the actual carrier in the path parameter (the proof of round 5's
`twistA_continuous`, through the exterior path identity). -/
theorem pathA_continuous {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a : ℝ) :
    Continuous (pathA q R V f ε a) := by
  let G := geomOf 2 1 (dilTower q R)
  let U := pathU q R V f ε
  have h : pathA q R V f ε a = fun t => pathA q R V f ε a 0 +
      (pE G).comp (((ContinuousLinearMap.adjoint (Wop G (U 0) a)).comp
        (((AdalyFormal.StatementLaneR6.deltaKLocCLM (U t) Set.univ) -
          (AdalyFormal.StatementLaneR6.deltaKLocCLM (U 0) Set.univ)).comp
          (Wop G (U 0) a))).comp (iE G)) := by
    funext t
    exact exterior_carrier_path (by norm_num) (dil_admissible hq hR) (by norm_num) hroom
      a (dilLam q R) U (fun s e he => path_agrees q R V f ε s 0 e he) selAll t
  rw [h]
  have hd : Continuous fun t => AdalyFormal.StatementLaneR6.deltaKLocCLM (U t)
      (Set.univ : Set (PeriodicLatticePlaquette (scaleUp 2 1 (dilLu q R)))) :=
    AdalyFormal.D1Literal.cont_deltaKLocCLM (path_cont q R hV f ε) _
  refine continuous_const.add
    (Continuous.clm_comp continuous_const (Continuous.clm_comp ?_ continuous_const))
  exact Continuous.clm_comp continuous_const
    (Continuous.clm_comp (hd.sub continuous_const) continuous_const)

/-- The localized data do not see the exterior. -/
theorem path_data_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    dataS selIn selIn (pathP q R V f ε a t) = dataS selIn selIn (pathP q R V f ε a 0) := by
  change (pathP q R V f ε a t).data = (pathP q R V f ε a 0).data
  exact AdalyFormal.M1IMS.data_congr_U (by norm_num) (dil_admissible hq hR)
    (by norm_num) hroom (pathU q R V f ε 0) (pathU q R V f ε t) a (dilLam q R)
    (fun e he => path_agrees q R V f ε 0 t e (fun hz => hz.1 he.1))

theorem pathD_constant {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V f ε a t = pathD q R V f ε a 0 := by
  have hd := path_data_constant hq hR hroom V f ε a t
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- At zero curvature the correction vanishes, for every exterior path and profile (the
proof of round 6's `twistD_zero_amplitude`, `AHP/round6/limits-r2/Attempt.lean:2421`). -/
theorem pathD_zero {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (a t : ℝ) : pathD q R V f 0 a t = 0 := by
  classical
  let P := pathP q R V f 0 a t
  have hflat : ∀ e : Bond P.Lf, e.1 ∈ P.S.Om 0 → P.U e = 1 := by
    intro e he
    have hz : e ∉ AdalyFormal.D1Literal.Zb ((dilTower q R).Om 0) :=
      fun h => h.1 he
    change pathU q R V f 0 t e = 1
    simp only [pathU, maskedU, zero_mul, AdalyFormal.StatementLane2.Ug_zero, ite_eq_right_iff]
    intro h
    exact (hz h).elim
  have hg := AdalyFormal.D1Guarded.G1invS_eq_Ginv_base
    selIn P selIn (dil_admissible hq hR) (by norm_num [P, pathP, gparams]) h3 hflat
  have hid := (dataS selIn selIn P).G1inv_unique
    (AdalyFormal.D1Literal.G1invS_spec selIn selIn P)
    ((dataS selIn selIn P).isG1inv_sub (dataS_laws selIn selIn P))
  have hh : (dataS selIn selIn P).Ginv -
      (dataS selIn selIn P).Delta2 (dataS_laws selIn selIn P) =
      (dataS selIn selIn P).Ginv := hid.symm.trans hg
  exact sub_eq_self.mp hh

/-- The frozen exterior twist as a path. -/
noncomputable def uthPath (q R : ℕ) : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)) :=
  fun t => AdalyFormal.D1Literal.Uth ((dilTower q R).Om 0) t

theorem uthPath_cont (q R : ℕ) : AdalyFormal.D1Literal.ContFam (uthPath q R) :=
  AdalyFormal.D1Literal.contFam_Uth _

open Classical in
/-- The round-4 single defect line, as a profile. -/
noncomputable def dilMask (q R : ℕ) : Bond (scaleUp 2 1 (dilLu q R)) → ℝ :=
  fun e => if dilPattern q R e then 1 else 0

theorem dilMask_bound (q R : ℕ) (e : Bond (scaleUp 2 1 (dilLu q R))) : |dilMask q R e| ≤ 1 := by
  simp only [dilMask]
  split_ifs <;> simp

/-- The round-4/5 curved twist family is the case `V = Uth`, `f = dilMask`. -/
theorem twistU_eq_path (q R : ℕ) (ε t : ℝ) :
    twistU q R ε t = pathU q R (uthPath q R) (dilMask q R) ε t := by
  classical
  funext e
  simp only [twistU, dilU, pathU, maskedU, uthPath, dilMask]
  split_ifs <;> simp

theorem twistA_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistA q R ε a t = pathA q R (uthPath q R) (dilMask q R) ε a t := by
  unfold twistA twistP pathA pathP
  rw [twistU_eq_path]

theorem twistD_eq_path (q R : ℕ) (ε a t : ℝ) :
    twistD q R ε a t = pathD q R (uthPath q R) (dilMask q R) ε a t := by
  have hd : dataS selIn selIn (twistP q R ε a t) =
      dataS selIn selIn (pathP q R (uthPath q R) (dilMask q R) ε a t) := by
    unfold twistP pathP
    rw [twistU_eq_path]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-! ### Separation in a path family refutes the guarded reading -/

/-- Some path parameter has a unit carrier and a non-unit corrected carrier (mass `1`). -/
def PathSeparation (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, IsUnit (pathA q R V f ε 1 t) ∧ ¬ IsUnit (pathA q R V f ε 1 t - pathD q R V f ε 1 t)

/-- The cofinal premise with, for each scale and radius, a free continuous exterior path
and a free bounded interior profile (both chosen before the cap; only the amplitude `ε`
goes to zero).  NOT proved here. -/
def CofinalPathSeparation : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ PathSeparation (2^j) R V f ε

/-- Bridge: the cofinal bookkeeping of round 8, with `masked_regular` in place of
`dil_regular` (the exterior is unconstrained by the class). -/
theorem goalNeg2_of_cofinalPathSeparation (h : CofinalPathSeparation) : GoalNeg2 := by
  apply cofinalPencilFailure_implies_goalNeg2
  refine ⟨2, by norm_num, 1, by norm_num, ?_⟩
  intro m₀
  obtain ⟨j, hj, hRs⟩ := h m₀
  refine ⟨j+1, by omega, by omega, ?_⟩
  intro R₀
  obtain ⟨R, hRR, hR, hR18, V, -, f, hf1, hsep⟩ := hRs R₀
  refine ⟨R, hRR, ?_⟩
  intro a₀ ha₀
  let q := 2^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : 2^(j+1) = 2*q := by dsimp [q]; rw [pow_succ]; omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := min (a₀/(3840*q)) 1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨ε, hε0, hεδ, t, hu, hnu⟩ := hsep δ hδ
  let α : ℝ := 160*ε
  have hα : 0 < α := by dsimp [α]; positivity
  have hcap : (12 : ℝ)*(2*q : ℕ)*α ≤ a₀ := by
    have he : ε < a₀/(3840*q) := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3840*q)).mp he
    dsimp [α]; push_cast; nlinarith
  have hmask : ∀ e, |ε * f e| ≤ α/80 := by
    intro e
    rw [abs_mul, abs_of_pos hε0]
    have h1 := hf1 e
    have h2 : ε * |f e| ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε0.le
    dsimp [α]
    linarith
  have hclass : ClassCoupled 2 (2*q) 12 1 (dilTower q R) α ((2 : ℝ)^1)⁻¹
      (pathU q R V f ε t) :=
    ⟨dil_coverage hq hR (by omega), masked_regular hq hR hα (fun e => ε * f e) hmask _⟩
  obtain ⟨hBt1, hBt2, hE⟩ := dil_competitor hq hR
  rw [hpow]
  exact ⟨1, by norm_num, dilLu q R, α, hα, hcap, dil_torus hq R,
    dilTower q R, dil_admissible hq hR, dilLam q R, dil_lambda hq hR,
    pathU q R V f ε t, hclass, dilBt hq R, hBt1, hBt2, hE, hu, hnu⟩

/-- Sign-free interval premise for a path family. -/
def PathSignChange (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε : ℝ) : Prop :=
  ∃ t₀ t₁ : ℝ, t₀ ≤ t₁ ∧
    (∀ t, t₀ ≤ t → t ≤ t₁ → IsUnit (pathA q R V f ε 1 t)) ∧
    PSD (pathA q R V f ε 1 t₀ - pathD q R V f ε 1 0) ∧
    ∃ w : ↥(bondSupp (geomOf 2 1 (dilTower q R))),
      ⟪w, (pathA q R V f ε 1 t₁ - pathD q R V f ε 1 0) w⟫ < 0

theorem pathSeparation_of_signChange {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V)
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ} {ε : ℝ}
    (h : PathSignChange q R V f ε) : PathSeparation q R V f ε := by
  obtain ⟨t₀, t₁, h01, hguard, h₀, w, h₁⟩ := h
  have hsA : ∀ t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  obtain ⟨t, -, -, hu, hnu⟩ := separation_of_sign_change (pathA q R V f ε 1)
    (pathD q R V f ε 1 0) (pathA_continuous hq hR hroom hV f ε 1) hsA hsD t₀ t₁ h01 hguard
    h₀ w h₁
  refine ⟨t, hu, ?_⟩
  rwa [pathD_constant hq hR hroom V f ε 1 t]

/-! ### Vacuum nondegeneracy: the remaining premise, at zero curvature only -/

/-- **Vacuum nondegeneracy of a path family at `(q,R)`** (mass `1`).  Spectral content only
at zero curvature: the vacuum carrier `pathA q R V f 0 1 ts` (flat interior) vanishes on a
nonzero subspace `K` and is `≥ g > 0` on `Kᗮ` (a first crossing of the path).
Regularity: `(ε,t) ↦ pathA` is Fréchet differentiable at `(0,ts)` and `ε ↦ pathD` is
differentiable at `0`, with derivatives `At`, `Ae`, `De` acting on `K` as scalars
`σ < 0`, `α`, `c`.  Nondegeneracy: `c ≠ 0` (no sign, no size).  NOT proved here. -/
def PathVacuumNondegeneracy (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts : ℝ) (K : Submodule ℝ ↥(bondSupp (geomOf 2 1 (dilTower q R)))) (g σ α c : ℝ)
    (At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ u ∈ K, pathA q R V f 0 1 ts u = 0) ∧ 0 < g ∧
    (∀ y ∈ Kᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    (∃ u ∈ K, u ≠ 0) ∧ σ < 0 ∧ c ≠ 0 ∧
    (∀ u ∈ K, ⟪u, At u⟫ = σ * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, Ae u⟫ = α * ‖u‖ ^ 2) ∧
    (∀ u ∈ K, ⟪u, De u⟫ = c * ‖u‖ ^ 2) ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

/-- Vacuum nondegeneracy gives the sign-free interval premise at EVERY small curvature. -/
theorem pathSignChange_of_vacuum {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R) (h3 : 3 ≤ R * (2*q))
    {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))} {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracy q R V f) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSignChange q R V f ε := by
  obtain ⟨ts, K, g, σ, α, c, At, Ae, De, hker, hg, hgap, hne, hσ, hc, hAt, hAe, hDe,
    hA, hD⟩ := h
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  exact perturbative_sign_change (fun ε t => pathA q R V f ε 1 t) (fun ε => pathD q R V f ε 1 0)
    hsA hsD ts K g σ α c At Ae De hker hg hgap hne hσ hc hAt hAe hDe
    (expansion_of_hasFDerivAt (fun ε t => pathA q R V f ε 1 t) ts Ae At hA)
    (expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De (pathD_zero hq hR h3 V f 1 0) hD)

/-- The cofinal vacuum premise: infinitely many dyadic scales, for each infinitely many
even radii `R ≥ 18`, each with SOME continuous exterior path and SOME bounded interior
profile whose first-order correction is visible on a first vacuum crossing kernel.
NOT proved here. -/
def CofinalPathVacuum : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracy (2^j) R V f

theorem cofinalPathSeparation_of_cofinalPathVacuum (h : CofinalPathVacuum) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, V, hV, f, hf, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  exact pathSeparation_of_signChange hq hR hroom hV
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))

/-- **Main reduction of this route.**  Cofinal vacuum nondegeneracy (zero-curvature data,
first-order regularity and `c ≠ 0` for some exterior path and bounded interior profile)
refutes the guarded all-plaquette reading. -/
theorem goalNeg2_of_cofinalPathVacuum (h : CofinalPathVacuum) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalPathVacuum h)

/-- The positive reading forbids it. -/
theorem not_cofinalPathVacuum_of_goalPos1 (h : GoalPos1) : ¬ CofinalPathVacuum :=
  fun h' => goalNeg2_of_cofinalPathVacuum h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, EVERY continuous exterior path and EVERY bounded interior profile fail vacuum
nondegeneracy (the first-order correction is invisible on the first vacuum crossing
kernel, or a regularity, gap or scalar clause fails). -/
theorem goalPos1_forces_vacuum_degeneracy (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ PathVacuumNondegeneracy (2^j) R V f := by
  have h' := not_cofinalPathVacuum_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-! ### Special cases: the frozen twist, and the round-4 defect line -/

/-- Vacuum nondegeneracy of the round-4/5 single-defect twist family itself. -/
def VacuumNondegeneracy (q R : ℕ) : Prop :=
  PathVacuumNondegeneracy q R (uthPath q R) (dilMask q R)

def CofinalVacuumNondegeneracy : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumNondegeneracy (2^j) R

theorem cofinalPathVacuum_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalPathVacuum := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalVacuumNondegeneracy (h : CofinalVacuumNondegeneracy) : GoalNeg2 :=
  goalNeg2_of_cofinalPathVacuum (cofinalPathVacuum_of_cofinalVacuum h)

/-- The round-8 separation premise for the round-4 family follows from its vacuum data. -/
theorem cofinalTwistSeparation_of_cofinalVacuum (h : CofinalVacuumNondegeneracy) :
    CofinalTwistSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  refine ⟨R, hRR, hR, hR18, fun δ hδ => ?_⟩
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have h3 : 3 ≤ R * (2 * 2^j) := by nlinarith
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨ε₀, hε₀, hall⟩ := pathSignChange_of_vacuum hq hR h3 hv
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  refine ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀], ?_⟩
  obtain ⟨t, hu, hnu⟩ := pathSeparation_of_signChange hq hR hroom (uthPath_cont (2^j) R)
    (hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀]))
  refine ⟨t, ?_, ?_⟩
  · rw [twistA_eq_path]; exact hu
  · rw [twistA_eq_path, twistD_eq_path]; exact hnu

/-- The same vacuum data with the scalar clauses supplied by a `U(1)` symmetry: the
crossing kernel is the complex line spanned by `u₀` and `J u₀`, where `J` is orthogonal
with `J (J u₀) = -u₀` and the three first-order operators are symmetric and commute with
`J` (for the diagonal families here, `J` is conjugation by `exp(π/4 · E₁)`, a quarter
turn of the charged components).  NOT proved here. -/
def PathVacuumNondegeneracyU1 (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts g : ℝ) (u₀ : ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (J At Ae De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    u₀ ≠ 0 ∧ J (J u₀) = -u₀ ∧ (∀ x y, ⟪J x, J y⟫ = ⟪x, y⟫) ∧
    (∀ x y, ⟪At x, y⟫ = ⟪x, At y⟫) ∧ (∀ x y, ⟪Ae x, y⟫ = ⟪x, Ae y⟫) ∧
    (∀ x y, ⟪De x, y⟫ = ⟪x, De y⟫) ∧
    (∀ x, At (J x) = J (At x)) ∧ (∀ x, Ae (J x) = J (Ae x)) ∧ (∀ x, De (J x) = J (De x)) ∧
    pathA q R V f 0 1 ts u₀ = 0 ∧ pathA q R V f 0 1 ts (J u₀) = 0 ∧ 0 < g ∧
    (∀ y ∈ (Submodule.span ℝ {u₀, J u₀})ᗮ, g * ‖y‖ ^ 2 ≤ ⟪y, pathA q R V f 0 1 ts y⟫) ∧
    ⟪u₀, At u₀⟫ < 0 ∧ ⟪u₀, De u₀⟫ ≠ 0 ∧
    HasFDerivAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Ae +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight At) ((0 : ℝ), ts) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0

theorem pathVacuum_of_U1 {q R : ℕ} {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : PathVacuumNondegeneracyU1 q R V f) : PathVacuumNondegeneracy q R V f := by
  obtain ⟨ts, g, u₀, J, At, Ae, De, hu₀, hJJ, hJ, hAts, hAes, hDes, hAtJ, hAeJ, hDeJ,
    hk1, hk2, hg, hgap, hσ, hc, hA, hD⟩ := h
  obtain ⟨σ, hσK⟩ := scalar_on_complex_line At J hAts hJ hAtJ u₀ hu₀ hJJ
  obtain ⟨α, hαK⟩ := scalar_on_complex_line Ae J hAes hJ hAeJ u₀ hu₀ hJJ
  obtain ⟨c, hcK⟩ := scalar_on_complex_line De J hDes hJ hDeJ u₀ hu₀ hJJ
  have hmem : u₀ ∈ Submodule.span ℝ {u₀, J u₀} := Submodule.subset_span (by simp)
  have hn : 0 < ‖u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu₀) 2
  have hσ' : σ < 0 := by
    have h1 := hσK u₀ hmem
    rw [h1] at hσ
    by_contra hcon
    have := mul_nonneg (not_lt.mp hcon) hn.le
    linarith
  have hc' : c ≠ 0 := by
    intro hc0
    apply hc
    rw [hcK u₀ hmem, hc0, zero_mul]
  refine ⟨ts, Submodule.span ℝ {u₀, J u₀}, g, σ, α, c, At, Ae, De, ?_, hg, hgap,
    ⟨u₀, hmem, hu₀⟩, hσ', hc', hσK, hαK, hcK, hA, hD⟩
  intro u hu
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, hk1, hk2, smul_zero, smul_zero, add_zero]

def CofinalPathVacuumU1 : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      PathVacuumNondegeneracyU1 (2^j) R V f

theorem goalNeg2_of_cofinalPathVacuumU1 (h : CofinalPathVacuumU1) : GoalNeg2 := by
  apply goalNeg2_of_cofinalPathVacuum
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, V, hV, f, hf, pathVacuum_of_U1 hv⟩

#print axioms pathU
#print axioms pathP
#print axioms pathA
#print axioms pathD
#print axioms path_agrees
#print axioms path_cont
#print axioms pathA_continuous
#print axioms path_data_constant
#print axioms pathD_constant
#print axioms pathD_zero
#print axioms uthPath
#print axioms uthPath_cont
#print axioms dilMask
#print axioms dilMask_bound
#print axioms twistU_eq_path
#print axioms twistA_eq_path
#print axioms twistD_eq_path
#print axioms PathSeparation
#print axioms CofinalPathSeparation
#print axioms goalNeg2_of_cofinalPathSeparation
#print axioms PathSignChange
#print axioms pathSeparation_of_signChange
#print axioms PathVacuumNondegeneracy
#print axioms pathSignChange_of_vacuum
#print axioms CofinalPathVacuum
#print axioms cofinalPathSeparation_of_cofinalPathVacuum
#print axioms goalNeg2_of_cofinalPathVacuum
#print axioms not_cofinalPathVacuum_of_goalPos1
#print axioms goalPos1_forces_vacuum_degeneracy
#print axioms VacuumNondegeneracy
#print axioms CofinalVacuumNondegeneracy
#print axioms cofinalPathVacuum_of_cofinalVacuum
#print axioms goalNeg2_of_cofinalVacuumNondegeneracy
#print axioms cofinalTwistSeparation_of_cofinalVacuum
#print axioms PathVacuumNondegeneracyU1
#print axioms pathVacuum_of_U1
#print axioms CofinalPathVacuumU1
#print axioms goalNeg2_of_cofinalPathVacuumU1

end AdalyFormal.Round9.Guarded.Qualitative

/-! ## The weakest vacuum premise: first-order coupling on a vacuum crossing

At zero curvature the interior is flat whatever the profile is, so all path families
with the same exterior path share one vacuum carrier `vacA`.  Reflecting the profile
`f ↦ -f` reflects the curvature `ε ↦ -ε`, hence the sign of the first-order coupling;
so only the pre-crossing sign has to be treated (`first_order_separation`). -/
namespace AdalyFormal.Round9.Guarded.Qualitative

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.StatementLane
open AdalyFormal.StatementLane2
open AdalyFormal.StatementLaneG
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Round2.Guarded.Pin
open AdalyFormal.Round4.Guarded.RefuteR1
open AdalyFormal.Round5.Guarded.IVTR1
open AdalyFormal.Round5.Guarded.IVTR2
open AdalyFormal.Round8.Guarded.SignFree
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.Balaban.CoercUMainDesigned (LinkCfg)
open AdalyFormal.D1Literal (PSD)

/-- The vacuum carrier along an exterior path (flat interior, mass `a`). -/
noncomputable def vacA (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))) (a t : ℝ) :
    ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ] ↥(bondSupp (geomOf 2 1 (dilTower q R))) :=
  pathA q R V (fun _ => 0) 0 a t

theorem pathU_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (t : ℝ) :
    pathU q R V f 0 t = pathU q R V (fun _ => 0) 0 t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- At zero curvature every profile has the vacuum carrier. -/
theorem pathA_zero (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (a t : ℝ) :
    pathA q R V f 0 a t = vacA q R V a t := by
  unfold vacA pathA pathP
  rw [pathU_zero]

theorem pathU_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε t : ℝ) :
    pathU q R V (fun e => -f e) ε t = pathU q R V f (-ε) t := by
  unfold pathU
  congr 1
  funext e
  simp

/-- Reflecting the profile reflects the curvature. -/
theorem pathA_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathA q R V (fun e => -f e) ε a t = pathA q R V f (-ε) a t := by
  unfold pathA pathP
  rw [pathU_neg]

theorem pathD_neg (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) (ε a t : ℝ) :
    pathD q R V (fun e => -f e) ε a t = pathD q R V f (-ε) a t := by
  have hd : dataS selIn selIn (pathP q R V (fun e => -f e) ε a t) =
      dataS selIn selIn (pathP q R V f (-ε) a t) := by
    unfold pathP
    rw [pathU_neg]
  have heq : ∀ (d d' : BaseDataS
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))
      (SiteL2 (scaleUp 2 1 (dilLu q R))) (FSp (geomOf 2 1 (dilTower q R))))
      (h : d = d') (hl : d.Laws) (hl' : d'.Laws), d.Delta2 hl = d'.Delta2 hl' := by
    intro d d' h hl hl'
    cases h
    rfl
  exact heq _ _ hd _ _

/-- **Vacuum coupling at `(q,R)`** for an exterior path `V` and an interior profile `f`
(mass `1`).  NOT proved here.
* Vacuum crossing (zero curvature, the same for every profile): the vacuum carrier is
  positive definite at angles arbitrarily close before `ts` and has a negative direction
  at angles arbitrarily close after `ts`.
* Regularity: the carrier is jointly continuous in curvature and angle at zero curvature,
  for angles near `ts`, and the correction is differentiable in the curvature at zero, with
  derivative `De`.
* Nondegeneracy: `De` is definite, of EITHER sign, on the kernel of the vacuum carrier at
  `ts`, with constant `c > 0`.
No derivative in the angle, no spectral gap and no scalar action on the kernel are
required. -/
def VacuumCoupling (q R : ℕ) (V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R)))
    (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ) : Prop :=
  ∃ (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R)))),
    (∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫) ∧
    (∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0) ∧
    (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ →
      ContinuousAt (fun p : ℝ × ℝ => pathA q R V f p.1 1 p.2) (0, t)) ∧
    HasDerivAt (fun ε : ℝ => pathD q R V f ε 1 0) De 0 ∧
    0 < c ∧ ((∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) ∨
      (∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ -⟪u, De u⟫))

/-- The pre-crossing step on the actual operators, for any profile with the given data. -/
theorem eventually_pathSeparation_pos {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) (f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ)
    (ts c : ℝ) (De : ↥(bondSupp (geomOf 2 1 (dilTower q R))) →L[ℝ]
      ↥(bondSupp (geomOf 2 1 (dilTower q R))))
    (hbef : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, vacA q R V 1 t₀ x⟫)
    (haft : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧ ∃ w, ⟪w, vacA q R V 1 t₁ w⟫ < 0)
    (hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ)
    (hDx : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
      ‖pathD q R V f ε 1 0 - ε • De‖ ≤ μ * ε)
    (hc : 0 < c) (hpos : ∀ u, vacA q R V 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f ε := by
  have hsA : ∀ ε t x y, ⟪pathA q R V f ε 1 t x, y⟫ = ⟪x, pathA q R V f ε 1 t y⟫ := by
    intro ε t x y
    exact (dataS selAll selAll (pathP q R V f ε 1 t)).Ginv_symm (dataS_laws selAll selAll _) x y
  have hsD : ∀ ε x y, ⟪pathD q R V f ε 1 0 x, y⟫ = ⟪x, pathD q R V f ε 1 0 y⟫ := by
    intro ε x y
    exact ((dataS selIn selIn (pathP q R V f ε 1 0)).Delta2_spec (dataS_laws selIn selIn _)).1 x y
  have hbef' : ∀ η : ℝ, 0 < η → ∃ t₀ : ℝ, ts - η < t₀ ∧ t₀ < ts ∧
      ∀ x, x ≠ 0 → 0 < ⟪x, pathA q R V f 0 1 t₀ x⟫ := by
    intro η hη
    obtain ⟨t₀, h1, h2, h3⟩ := hbef η hη
    exact ⟨t₀, h1, h2, fun x hx => by rw [pathA_zero]; exact h3 x hx⟩
  have haft' : ∀ η : ℝ, 0 < η → ∃ t₁ : ℝ, ts < t₁ ∧ t₁ < ts + η ∧
      ∃ w, ⟪w, pathA q R V f 0 1 t₁ w⟫ < 0 := by
    intro η hη
    obtain ⟨t₁, h1, h2, w, hw⟩ := haft η hη
    exact ⟨t₁, h1, h2, w, by rw [pathA_zero]; exact hw⟩
  have hpos' : ∀ u, pathA q R V f 0 1 ts u = 0 → c * ‖u‖ ^ 2 ≤ ⟪u, De u⟫ := by
    intro u hu
    rw [pathA_zero] at hu
    exact hpos u hu
  obtain ⟨ε₀, hε₀, hall⟩ := first_order_separation (fun ε t => pathA q R V f ε 1 t)
    (fun ε => pathD q R V f ε 1 0) hsA hsD (fun ε => pathA_continuous hq hR hroom hV f ε 1)
    ts hj hbef' haft' c De hc hpos' hDx
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨t, hu, hnu⟩ := hall ε hε hεε
  exact ⟨t, hu, by rwa [pathD_constant hq hR hroom V f ε 1 t]⟩

/-- Vacuum coupling gives a guarded separation at EVERY small curvature, for the profile
`f` itself or for its reflection `-f` (according to the sign of the coupling). -/
theorem eventually_pathSeparation_of_coupling {q R : ℕ} (hq : 0 < q) (hR : 2 ∣ R)
    (hroom : 17*2 ≤ R*(2*q)) {V : ℝ → LinkCfg (scaleUp 2 1 (dilLu q R))}
    (hV : AdalyFormal.D1Literal.ContFam V) {f : Bond (scaleUp 2 1 (dilLu q R)) → ℝ}
    (h : VacuumCoupling q R V f) :
    ∃ f' : Bond (scaleUp 2 1 (dilLu q R)) → ℝ, (∀ e, |f' e| = |f e|) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → PathSeparation q R V f' ε := by
  obtain ⟨ts, c, De, hbef, haft, ⟨η₀, hη₀, hjoint⟩, hD, hc, hsign⟩ := h
  have h3 : 3 ≤ R * (2*q) := by omega
  have hj : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
      ∀ ε s : ℝ, |ε| < r → |s - t| < r → ‖pathA q R V f ε 1 s - pathA q R V f 0 1 t‖ < δ :=
    ⟨η₀, hη₀, fun t ht => metric_of_continuousAt (fun ε t => pathA q R V f ε 1 t) t (hjoint t ht)⟩
  have hDx := expansion_of_hasDerivAt (fun ε => pathD q R V f ε 1 0) De
    (pathD_zero hq hR h3 V f 1 0) hD
  rcases hsign with hpos | hneg
  · refine ⟨f, fun e => rfl, ?_⟩
    refine eventually_pathSeparation_pos hq hR hroom hV f ts c De hbef haft hj ?_ hc hpos
    intro μ hμ
    obtain ⟨r, hr, hb⟩ := hDx μ hμ
    refine ⟨r, hr, fun ε hε hεr => ?_⟩
    have h1 := hb ε (by rw [abs_of_pos hε]; exact hεr)
    rw [abs_of_pos hε] at h1
    exact h1
  · refine ⟨fun e => -f e, fun e => abs_neg (f e), ?_⟩
    have hj' : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ t : ℝ, |t - ts| < η₀ → ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧
        ∀ ε s : ℝ, |ε| < r → |s - t| < r →
        ‖pathA q R V (fun e => -f e) ε 1 s - pathA q R V (fun e => -f e) 0 1 t‖ < δ := by
      obtain ⟨η₁, hη₁, hj1⟩ := hj
      refine ⟨η₁, hη₁, fun t ht δ hδ => ?_⟩
      obtain ⟨r, hr, hb⟩ := hj1 t ht δ hδ
      refine ⟨r, hr, fun ε s hε hs => ?_⟩
      rw [pathA_neg, pathA_neg, neg_zero]
      exact hb (-ε) s (by rwa [abs_neg]) hs
    have hDx' : ∀ μ : ℝ, 0 < μ → ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε < r →
        ‖pathD q R V (fun e => -f e) ε 1 0 - ε • (-De)‖ ≤ μ * ε := by
      intro μ hμ
      obtain ⟨r, hr, hb⟩ := hDx μ hμ
      refine ⟨r, hr, fun ε hε hεr => ?_⟩
      have h1 := hb (-ε) (by rw [abs_neg, abs_of_pos hε]; exact hεr)
      rw [abs_neg, abs_of_pos hε] at h1
      have e2 : ε • (-De) = (-ε) • De := by
        rw [smul_neg]
        exact (neg_smul ε De).symm
      rw [pathD_neg, e2]
      exact h1
    refine eventually_pathSeparation_pos hq hR hroom hV (fun e => -f e) ts c (-De) hbef haft
      hj' hDx' hc ?_
    intro u hu
    have h1 := hneg u hu
    have e : ⟪u, (-De) u⟫ = -⟪u, De u⟫ := by
      show ⟪u, -(De u)⟫ = -⟪u, De u⟫
      exact inner_neg_right u (De u)
    rw [e]
    exact h1

/-- **The weakest cofinal premise of this route.**  Infinitely many dyadic scales, for
each infinitely many even radii `R ≥ 18`, each with SOME continuous exterior path and SOME
bounded interior profile having vacuum coupling.  NOT proved here. -/
def CofinalVacuumCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    ∃ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V ∧
    ∃ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) ∧
      VacuumCoupling (2^j) R V f

theorem cofinalPathSeparation_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) :
    CofinalPathSeparation := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, V, hV, f, hf, hv⟩ := hRs R₀
  have hq : 0 < 2^j := by positivity
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  have hroom : 17*2 ≤ R*(2*2^j) := by nlinarith
  obtain ⟨f', hf', ε₀, hε₀, hall⟩ := eventually_pathSeparation_of_coupling hq hR hroom hV hv
  refine ⟨R, hRR, hR, hR18, V, hV, f', fun e => by rw [hf']; exact hf e, fun δ hδ => ?_⟩
  have hm : 0 < min δ ε₀ := lt_min hδ hε₀
  exact ⟨min δ ε₀ / 2, by positivity, by linarith [min_le_left δ ε₀],
    hall (min δ ε₀ / 2) (by positivity) (by linarith [min_le_right δ ε₀])⟩

/-- **Main reduction of this round.**  Cofinal vacuum coupling refutes the guarded
all-plaquette reading. -/
theorem goalNeg2_of_cofinalVacuumCoupling (h : CofinalVacuumCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalPathSeparation (cofinalPathSeparation_of_cofinalVacuumCoupling h)

/-- The positive reading forbids it. -/
theorem not_cofinalVacuumCoupling_of_goalPos1 (h : GoalPos1) : ¬ CofinalVacuumCoupling :=
  fun h' => goalNeg2_of_cofinalVacuumCoupling h' (goalPos2_iff_goalPos1.mpr h)

/-- What the positive reading demands, stated directly: from some scale on, for all large
even radii, NO continuous exterior path and NO bounded interior profile has vacuum
coupling. -/
theorem goalPos1_forces_no_vacuum_coupling (h : GoalPos1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 2 ∣ R → 18 ≤ R →
      ∀ V : ℝ → LinkCfg (scaleUp 2 1 (dilLu (2^j) R)), AdalyFormal.D1Literal.ContFam V →
      ∀ f : Bond (scaleUp 2 1 (dilLu (2^j) R)) → ℝ, (∀ e, |f e| ≤ 1) →
        ¬ VacuumCoupling (2^j) R V f := by
  have h' := not_cofinalVacuumCoupling_of_goalPos1 h
  by_contra hcon
  apply h'
  intro j₀
  obtain ⟨j, hj⟩ := not_forall.mp (not_exists.mp hcon j₀)
  obtain ⟨hjj, hj2⟩ := Classical.not_imp.mp hj
  refine ⟨j, hjj, fun R₀ => ?_⟩
  obtain ⟨R, hR⟩ := not_forall.mp (not_exists.mp hj2 R₀)
  obtain ⟨hRR, hR1⟩ := Classical.not_imp.mp hR
  obtain ⟨hR2, hR3⟩ := Classical.not_imp.mp hR1
  obtain ⟨hR18, hR4⟩ := Classical.not_imp.mp hR3
  obtain ⟨V, hV⟩ := not_forall.mp hR4
  obtain ⟨hVc, hV1⟩ := Classical.not_imp.mp hV
  obtain ⟨f, hf⟩ := not_forall.mp hV1
  obtain ⟨hfb, hf1⟩ := Classical.not_imp.mp hf
  exact ⟨R, hRR, hR2, hR18, V, hVc, f, hfb, not_not.mp hf1⟩

/-- The same premise for the round-4/5 family itself: the frozen exterior twist and the single
defect line.  Its coupling is the round-8 vacuum coefficient `c1(q,R)` (numerically negative
at `q = 2, 4`); the reflection then separates with the reversed defect.  NOT proved here. -/
def CofinalDefectLineCoupling : Prop :=
  ∀ j₀ : ℕ, ∃ j : ℕ, j₀ ≤ j ∧ ∀ R₀ : ℕ, ∃ R : ℕ, R₀ ≤ R ∧ 2 ∣ R ∧ 18 ≤ R ∧
    VacuumCoupling (2^j) R (uthPath (2^j) R) (dilMask (2^j) R)

theorem cofinalVacuumCoupling_of_defectLine (h : CofinalDefectLineCoupling) :
    CofinalVacuumCoupling := by
  intro j₀
  obtain ⟨j, hj, hRs⟩ := h j₀
  refine ⟨j, hj, fun R₀ => ?_⟩
  obtain ⟨R, hRR, hR, hR18, hv⟩ := hRs R₀
  exact ⟨R, hRR, hR, hR18, uthPath (2^j) R, uthPath_cont (2^j) R, dilMask (2^j) R,
    dilMask_bound (2^j) R, hv⟩

theorem goalNeg2_of_cofinalDefectLineCoupling (h : CofinalDefectLineCoupling) : GoalNeg2 :=
  goalNeg2_of_cofinalVacuumCoupling (cofinalVacuumCoupling_of_defectLine h)

#print axioms vacA
#print axioms pathU_zero
#print axioms pathA_zero
#print axioms pathU_neg
#print axioms pathA_neg
#print axioms pathD_neg
#print axioms VacuumCoupling
#print axioms eventually_pathSeparation_pos
#print axioms eventually_pathSeparation_of_coupling
#print axioms CofinalVacuumCoupling
#print axioms cofinalPathSeparation_of_cofinalVacuumCoupling
#print axioms goalNeg2_of_cofinalVacuumCoupling
#print axioms not_cofinalVacuumCoupling_of_goalPos1
#print axioms goalPos1_forces_no_vacuum_coupling
#print axioms CofinalDefectLineCoupling
#print axioms cofinalVacuumCoupling_of_defectLine
#print axioms goalNeg2_of_cofinalDefectLineCoupling

end AdalyFormal.Round9.Guarded.Qualitative

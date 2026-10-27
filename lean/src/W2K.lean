import W2H

/-!
# W2K -- the decay input reduced to a statement about constrained-harmonic fields only (M1 lane W2, 2026-10-13)

For `V ≤ W`: `P_W f − P_V f = P_{W ⊓ V^⊥} f` (`proj_sub_eq`).  Hence the decay defect is
`defK = ‖P_{H_K} D* A‖²`, `H_K = RImage ⊓ (VK)^⊥` = the fields `h = Δ_U μ` (`μ ∈ N(Q')`) orthogonal to `Δ_U N_K`, i.e. the
"constrained-harmonic" fields of `K` (`defK_eq`).  Since `⟪D* A, h⟫ = ⟪A, D h⟫` only reads `D h` on the bonds of `A`:
* `HarmDecayAt ell L U ε d` : on every two-stratum patch tower (torus sides multiples of `ell^{i+1}`), every `h ∈ H_K` (`K = Ball w (s + d ell^i)`) has
  `Σ_{b touching Ball w s} ‖(D_U h)(b)‖² ≤ ε · ell^{-2(i+1)} · ‖h‖²`
  (a gradient bound at the scale of the upper stratum, `d` lower-stratum blocks inside `K`);
* **`optDecay_of_harm`** : `HarmDecayAt ε d → OptDecayAt ε d`.
No sorry / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace AdalyFormal.M1W2

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.StatementLane (Tower BlockClosed)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond)
open AdalyFormal.StatementLaneR8 (Ball)
open AdalyFormal.M1Patch (patchTower om_le om_succ om_gt)
open AdalyFormal.M1 (wnormSq)

section abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem proj_sub_eq (V W : Submodule ℝ E) (h : V ≤ W) (f : E) :
    W.starProjection f - V.starProjection f = (W ⊓ Vᗮ).starProjection f := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine ⟨Submodule.sub_mem _ (Submodule.starProjection_apply_mem W f)
      (h (Submodule.starProjection_apply_mem V f)), ?_⟩
    refine (Submodule.mem_orthogonal V _).mpr ?_
    intro v hv
    rw [inner_sub_right]
    have h1 : ⟪v, W.starProjection f⟫ = ⟪v, f⟫ := by
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr (h hv)]
    have h2 : ⟪v, V.starProjection f⟫ = ⟪v, f⟫ := by
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hv]
    rw [h1, h2, sub_self]
  · intro w hw
    obtain ⟨hwW, hwV⟩ := Submodule.mem_inf.mp hw
    have e : f - (W.starProjection f - V.starProjection f) = (f - W.starProjection f) + V.starProjection f := by abel
    rw [e, inner_add_left]
    have h1 : ⟪f - W.starProjection f, w⟫ = 0 :=
      (Submodule.mem_orthogonal' W _).mp (Submodule.sub_starProjection_mem_orthogonal f) w hwW
    have h2 : ⟪V.starProjection f, w⟫ = 0 := by
      exact (Submodule.mem_orthogonal V w).mp hwV _ (Submodule.starProjection_apply_mem V f)
    rw [h1, h2, add_zero]

end abstract

variable {L : PeriodicLatticeExtent}

/-- the constrained-harmonic fields of `K`. -/
noncomputable def HK (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) : Submodule ℝ (SiteL2 L) :=
  RImage G U ⊓ (VK G U K)ᗮ

theorem defK_eq (G : TowerGeom L) (U : Cfg L) (K : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) :
    defK G U K A = ‖(HK G U K).starProjection (gradAdj U A)‖ ^ 2 := by
  unfold defK HK Rproj
  rw [proj_sub_eq (VK G U K) (RImage G U) (VK_le_RImage G U K)]

open Classical in
/-- the squared gradient of `h` on the bonds touching `X`. -/
noncomputable def gradOn (U : Cfg L) (X : Set (PeriodicLatticeSite L)) (h : SiteL2 L) : ℝ :=
  ∑ b : Bond L, if (b.1 ∈ X ∨ periodicLatticeShift b.1 b.2 ∈ X) then ‖(WithLp.ofLp (gradL2 U h)) b‖ ^ 2 else 0

/-- **constrained-harmonic fields have small gradients `d` blocks inside `K`** (the decay residual, stated without `A`). -/
def HarmDecayAt (ell : ℕ) (L : PeriodicLatticeExtent) (U : Cfg L) (ε : ℝ) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (Rg : Set (PeriodicLatticeSite L)), BlockClosed (ell ^ (i + 1)) Rg → (∀ μ : Fin 3, ell ^ (i + 1) ∣ L μ + 1) →
    ∀ (w : PeriodicLatticeSite L) (s : ℕ) (h : SiteL2 L),
      h ∈ HK (geomOf ell (i + 1) (patchTower i Rg)) U (Ball w (s + d * ell ^ i)) →
      gradOn U (Ball w s) h ≤ ε * (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖h‖ ^ 2

open Classical in
theorem inner_le_gradOn (U : Cfg L) (X : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) (h : SiteL2 L)
    (hA : ∀ b : Bond L, (WithLp.ofLp A) b ≠ 0 → b.1 ∈ X ∨ periodicLatticeShift b.1 b.2 ∈ X) :
    ⟪gradAdj U A, h⟫ ≤ ‖A‖ * Real.sqrt (gradOn U X h) := by
  have e : ⟪gradAdj U A, h⟫ = ⟪A, gradL2 U h⟫ := by
    rw [gradAdj, ContinuousLinearMap.adjoint_inner_left]
  rw [e, PiLp.inner_apply]
  set P : Bond L → Prop := fun b => b.1 ∈ X ∨ periodicLatticeShift b.1 b.2 ∈ X
  have h1 : ∑ b : Bond L, ⟪(WithLp.ofLp A) b, (WithLp.ofLp (gradL2 U h)) b⟫
      = ∑ b : Bond L, ⟪(WithLp.ofLp A) b, if P b then (WithLp.ofLp (gradL2 U h)) b else 0⟫ := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : P b
    · rw [if_pos hb]
    · rw [if_neg hb]
      have : (WithLp.ofLp A) b = 0 := by by_contra hne; exact hb (hA b hne)
      rw [this, inner_zero_left, inner_zero_left]
  rw [h1]
  set g : BondFnL2 L := WithLp.toLp 2 (fun b => if P b then (WithLp.ofLp (gradL2 U h)) b else 0) with hg
  have h2 : ∑ b : Bond L, ⟪(WithLp.ofLp A) b, if P b then (WithLp.ofLp (gradL2 U h)) b else 0⟫ = ⟪A, g⟫ := by
    rw [PiLp.inner_apply]
  have h3 : ‖g‖ ^ 2 = gradOn U X h := by
    rw [PiLp.norm_sq_eq_of_L2]
    unfold gradOn
    refine Finset.sum_congr rfl (fun b _ => ?_)
    show ‖(if P b then (WithLp.ofLp (gradL2 U h)) b else 0)‖ ^ 2 = _
    split_ifs <;> simp
  rw [h2]
  have h4 : ‖g‖ = Real.sqrt (gradOn U X h) := by rw [← h3, Real.sqrt_sq (norm_nonneg _)]
  rw [← h4]
  exact real_inner_le_norm A g

theorem wnorm_ge_patch (ell i : ℕ) (hell : 0 < ell) (Rg : Set (PeriodicLatticeSite L)) (A : BondFnL2 L) :
    (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 * ‖A‖ ^ 2 ≤ wnormSq (patchTower i Rg) ell (i + 1) A := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  unfold wnormSq
  refine Finset.sum_le_sum (fun b _ => ?_)
  have hb : AdalyFormal.M1.bstrat (patchTower i Rg) (i + 1) b ≤ i + 1 := AdalyFormal.M1.bstrat_le _ _ _
  have h1 : (ell : ℝ) ^ AdalyFormal.M1.bstrat (patchTower i Rg) (i + 1) b ≤ (ell : ℝ) ^ (i + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hell) hb
  have h0 : (0 : ℝ) < (ell : ℝ) ^ AdalyFormal.M1.bstrat (patchTower i Rg) (i + 1) b := by positivity
  have h2 : ((ell : ℝ) ^ (i + 1))⁻¹ ≤ ((ell : ℝ) ^ AdalyFormal.M1.bstrat (patchTower i Rg) (i + 1) b)⁻¹ :=
    inv_anti₀ h0 h1
  have h3 : 0 ≤ ((ell : ℝ) ^ (i + 1))⁻¹ := by positivity
  have h4 := pow_le_pow_left₀ h3 h2 2
  exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

/-- **the decay input from the harmonic-gradient statement.** -/
theorem optDecay_of_harm (ell : ℕ) (hell : 0 < ell) (L : PeriodicLatticeExtent) (U : Cfg L) (ε : ℝ) (hε : 0 ≤ ε) (d : ℕ)
    (h : HarmDecayAt ell L U ε d) : OptDecayAt ell L U ε d := by
  intro i Rg hRg hdiv w s A hA
  rw [defK_eq]
  set G := geomOf ell (i + 1) (patchTower i Rg)
  set K := Ball w (s + d * ell ^ i)
  set p := (HK G U K).starProjection (gradAdj U A) with hp
  have hmem : p ∈ HK G U K := Submodule.starProjection_apply_mem _ _
  have hgrad := h i Rg hRg hdiv w s p hmem
  have hpp : ‖p‖ ^ 2 = ⟪gradAdj U A, p⟫ := by
    have horth : gradAdj U A - p ∈ (HK G U K)ᗮ := Submodule.sub_starProjection_mem_orthogonal _
    have h0 : ⟪gradAdj U A - p, p⟫ = 0 := by
      rw [real_inner_comm]; exact (Submodule.mem_orthogonal (HK G U K) _).mp horth p hmem
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
    linarith
  have hin := inner_le_gradOn U (Ball w s) A p hA
  set c := (((ell : ℝ) ^ (i + 1))⁻¹) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hw := wnorm_ge_patch ell i hell Rg A
  rw [← hc] at hw
  -- ‖p‖² ≤ ‖A‖ √(ε c ‖p‖²) = ‖A‖ √(ε c) ‖p‖
  have hs : Real.sqrt (gradOn U (Ball w s) p) ≤ Real.sqrt (ε * c) * ‖p‖ := by
    rw [← Real.sqrt_sq (norm_nonneg p), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : ‖p‖ ^ 2 ≤ ‖A‖ * (Real.sqrt (ε * c) * ‖p‖) := by
    rw [hpp]; exact hin.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  have h2 : ‖p‖ ≤ ‖A‖ * Real.sqrt (ε * c) := by
    rcases (norm_nonneg p).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have : ‖p‖ * ‖p‖ ≤ (‖A‖ * Real.sqrt (ε * c)) * ‖p‖ := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have h3 : ‖p‖ ^ 2 ≤ ‖A‖ ^ 2 * (ε * c) := by
    have := pow_le_pow_left₀ (norm_nonneg p) h2 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at this
    exact this
  calc ‖p‖ ^ 2 ≤ ‖A‖ ^ 2 * (ε * c) := h3
    _ = ε * (c * ‖A‖ ^ 2) := by ring
    _ ≤ ε * wnormSq (patchTower i Rg) ell (i + 1) A := mul_le_mul_of_nonneg_left hw hε

end AdalyFormal.M1W2

#print axioms AdalyFormal.M1W2.proj_sub_eq
#print axioms AdalyFormal.M1W2.HK
#print axioms AdalyFormal.M1W2.defK_eq
#print axioms AdalyFormal.M1W2.gradOn
#print axioms AdalyFormal.M1W2.HarmDecayAt
#print axioms AdalyFormal.M1W2.inner_le_gradOn
#print axioms AdalyFormal.M1W2.wnorm_ge_patch
#print axioms AdalyFormal.M1W2.optDecay_of_harm

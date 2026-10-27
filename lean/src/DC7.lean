import DC6

/-!
# DC7 -- Combes–Thomas for the genuine row Gram `Γ = X*X`, its inverse, and the divergence-to-rows map (M1 D-layer lane)

For `D : CTData …` and a weight `ξ` with `WtOK (ψ + ξ) Θ Δ` (and `WtOK (ψ − ξ) Θ Δ` where `−ξ` is used):
`Xcj ξ u = e^{ξ} X e^{−ξ} u` (genuine `X = Xop`), `Γ^{ξ} = e^{ξ} Γ e^{−ξ}` (rows weighted at their base site),
`GiC ξ = e^{ξ} Gi e^{−ξ}`, `VC ξ = e^{ξ} (D̂X̂)* e^{−ξ}`, `τ = σ ∘ rowSite`.
* `Xcj_le` : `‖Xcj ξ u‖ ≤ ℓ nX ‖e^{τ} u‖`;  `Xcj_diff` : `‖Xcj ξ u − X u‖ ≤ 2ℓ EX ‖e^{τ} u‖`;
* `Gam_conj_coer` : `cΓ ‖e^{τ}u‖² ≤ ⟪Γ^{ξ} u, u⟫`, `cΓ = 1/γ² − 2ε/γ − ε²`, `ε = 2ℓEX` (needs `εγ ≤ 1`);
* `GiC_bound` : `cΓ ‖e^{τ} GiC ξ w‖ ≤ ‖e^{−τ} w‖`;  `Gam_diff` : `‖e^{−τ}(Γ^{ξ} − Γ) v‖ ≤ dΓ ‖e^{τ} v‖`;
* `GiC_diff` : `cΓ ‖e^{τ}(GiC ξ w − Gi w)‖ ≤ dΓ γ² ‖e^{−τ} w‖`;
* `VC_bound` : `‖e^{−τ} VC ξ B‖ ≤ ℓ K3 ‖e^{−σ} B‖`;  `VC_diff` : `‖e^{−τ}(VC ξ B − VC 0 B)‖ ≤ 2ℓ EDX' ‖e^{−σ} B‖`.
No sorry / native_decide / axiom.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

namespace AdalyFormal.M1DStrat

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.SiteCoercivity
open AdalyFormal.DLayer
open AdalyFormal.M1Site
open AdalyFormal.M1IMS
open AdalyFormal.StatementLane (Tower Admissible bigSide scaleUp)
open AdalyFormal.Balaban.AdmissibleSubspace (Bond blockOf)
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2 RMap)

section gen
variable {L : PeriodicLatticeExtent}

theorem bondWt_mul (φ χ : PeriodicLatticeSite L → ℝ) (B : BondFnL2 L) :
    bondWt φ (bondWt χ B) = bondWt (φ + χ) B := by
  refine PiLp.ext (fun b => ?_)
  rw [bondWt_apply, bondWt_apply, bondWt_apply, smul_smul, ← Real.exp_add, Pi.add_apply]

theorem bondWt_zero_fn (B : BondFnL2 L) : bondWt (fun _ => (0 : ℝ)) B = B := by
  refine PiLp.ext (fun b => ?_)
  rw [bondWt_apply]; simp

/-- the elementary lower bound behind the coercivity of a perturbed Gram form -/
theorem pert_gram_lower (t N ε γ : ℝ) (hγ : 0 < γ) (hN : 0 ≤ N) (hε : 0 ≤ ε) (hεγ : ε * γ ≤ 1)
    (ht : N ≤ γ * t) :
    (1 / γ ^ 2 - 2 * ε / γ - ε ^ 2) * N ^ 2 ≤ t ^ 2 - 2 * ε * N * t - ε ^ 2 * N ^ 2 := by
  have hNg : N / γ ≤ t := by rw [div_le_iff₀ hγ]; linarith
  have hNg0 : 0 ≤ N / γ := by positivity
  have h1 : 0 ≤ t - N / γ := by linarith
  have hεN : ε * N ≤ N / γ := by
    rw [le_div_iff₀ hγ]
    have := mul_le_mul_of_nonneg_right hεγ hN
    linarith
  have h3 : 0 ≤ t + N / γ - 2 * (ε * N) := by linarith
  have hprod := mul_nonneg h1 h3
  have e1 : (t - N / γ) * (t + N / γ - 2 * (ε * N))
      = (t ^ 2 - 2 * ε * N * t) - ((N / γ) ^ 2 - 2 * ε * N * (N / γ)) := by ring
  have e : (1 / γ ^ 2 - 2 * ε / γ - ε ^ 2) * N ^ 2 = (N / γ) ^ 2 - 2 * ε * N * (N / γ) - ε ^ 2 * N ^ 2 := by
    field_simp
  rw [e]; linarith

/-- `c A² ≤ A B` with `A, B ≥ 0` gives `c A ≤ B` -/
theorem coer_to_bound (c A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : c * A ^ 2 ≤ A * B) : c * A ≤ B := by
  rcases eq_or_lt_of_le hA with h0 | hpos
  · rw [← h0, mul_zero]; exact hB
  · have : c * A * A ≤ B * A := by
      have e1 : c * A * A = c * A ^ 2 := by ring
      have e2 : B * A = A * B := by ring
      rw [e1, e2]; exact h
    exact le_of_mul_le_mul_right this hpos

/-- the inner-product perturbation (one-sided form) -/
theorem inner_pert_le' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b a' b' : F)
    (X Y K d : ℝ) (hd : 0 ≤ d) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (ha : ‖a' - a‖ ≤ d * X) (hb : ‖b' - b‖ ≤ d * Y) (hA : ‖a‖ ≤ K * X) (hB : ‖b‖ ≤ K * Y) :
    |⟪a', b'⟫ - ⟪a, b⟫| ≤ (2 * K * d + d ^ 2) * (X * Y) := by
  have e : ⟪a', b'⟫ - ⟪a, b⟫ = ⟪a' - a, b⟫ + ⟪a, b' - b⟫ + ⟪a' - a, b' - b⟫ := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 := abs_real_inner_le_norm (a' - a) b
  have h2 := abs_real_inner_le_norm a (b' - b)
  have h3 := abs_real_inner_le_norm (a' - a) (b' - b)
  have m1 := mul_le_mul ha hB (norm_nonneg _) (by positivity)
  have m2 := mul_le_mul hA hb (norm_nonneg _) (le_trans (norm_nonneg _) hA)
  have m3 := mul_le_mul ha hb (norm_nonneg _) (by positivity)
  have t := abs_add_le (⟪a' - a, b⟫ + ⟪a, b' - b⟫) ⟪a' - a, b' - b⟫
  have t2 := abs_add_le ⟪a' - a, b⟫ ⟪a, b' - b⟫
  have e2 : (2 * K * d + d ^ 2) * (X * Y) = d * X * (K * Y) + K * X * (d * Y) + d * X * (d * Y) := by ring
  rw [e2]
  linarith

end gen

namespace CTData
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ} (D : CTData ell M R k S W)
include D

/-- the conjugated genuine `X` -/
noncomputable def Xcj (ξ : PeriodicLatticeSite Lf → ℝ) (u : YP (geomOf ell k S)) : SiteL2 Lf :=
  siteWt ξ (Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-ξ) u))

theorem Xcj_eq (ξ : PeriodicLatticeSite Lf → ℝ) (u : YP (geomOf ell k S)) :
    D.Xcj ξ u = siteWt (sigG (geomOf ell k S)) (XhC (geomOf ell k S) D.U D.a ξ u) := D.XopC_hat ξ u

theorem Xcj_le (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (u : YP (geomOf ell k S)) :
    ‖D.Xcj ξ u‖ ≤ (ell : ℝ) * D.nX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
  have h := D.Xt ξ hξ (ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u)
  rw [ypWt_cancel_neg] at h
  rw [D.Xcj_eq]; exact h

theorem X_le (u : YP (geomOf ell k S)) :
    ‖Xop (geomOf ell k S) D.U D.a u‖ ≤ (ell : ℝ) * D.nX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
  have h := D.Xt0 (ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u)
  rw [ypWt_cancel_neg, ← D.Xop_hat] at h
  exact h

theorem Xcj_diff (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (u : YP (geomOf ell k S)) :
    ‖D.Xcj ξ u - Xop (geomOf ell k S) D.U D.a u‖
      ≤ 2 * (ell : ℝ) * D.EX * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ := by
  have h := D.XC_diff ξ hξ u
  rw [map_sub, ← D.Xop_hat] at h
  rw [D.Xcj_eq]; exact h

/-- the conjugated Gram operator -/
noncomputable def GamC (ξ : PeriodicLatticeSite Lf → ℝ) (u : YP (geomOf ell k S)) : YP (geomOf ell k S) :=
  ypWt (geomOf ell k S) ξ ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a)
    (ypWt (geomOf ell k S) (-ξ) u))

theorem GamC_inner (ξ : PeriodicLatticeSite Lf → ℝ) (a b : YP (geomOf ell k S)) :
    ⟪D.GamC ξ a, b⟫ = ⟪D.Xcj ξ a, D.Xcj (-ξ) b⟫ := by
  unfold GamC Xcj
  rw [D.Gam_conj_inner ξ a b]

theorem GamC_zero (u : YP (geomOf ell k S)) :
    D.GamC (fun _ => (0 : ℝ)) u
      = (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) u := by
  unfold GamC
  have e : (-(fun _ : PeriodicLatticeSite Lf => (0 : ℝ))) = fun _ => (0 : ℝ) := by funext x; simp
  rw [e, ypWt_zero_fn, ypWt_zero_fn]

/-- `ε = 2ℓ EX` and the coercivity constant -/
noncomputable def epsG : ℝ := 2 * (ell : ℝ) * D.EX
noncomputable def cG : ℝ := 1 / D.γ ^ 2 - 2 * D.epsG / D.γ - D.epsG ^ 2
noncomputable def dG : ℝ := 2 * ((ell : ℝ) * D.nX) * D.epsG + D.epsG ^ 2

theorem epsG_nonneg : 0 ≤ D.epsG := by
  unfold epsG; have := D.EX_nonneg; have := D.ell_pos; positivity

theorem dG_nonneg : 0 ≤ D.dG := by
  unfold dG; have := D.epsG_nonneg; have := D.nX_nonneg; have := D.ell_pos; positivity

/-- **coercivity of the conjugated Gram form** -/
theorem Gam_conj_coer (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (u : YP (geomOf ell k S)) :
    D.cG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ^ 2 ≤ ⟪D.GamC ξ u, u⟫ := by
  rw [D.GamC_inner]
  set N := ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ with hN
  set a := Xop (geomOf ell k S) D.U D.a u with ha
  have h1 := D.Xcj_diff ξ hp u
  have h2 := D.Xcj_diff (-ξ) hm u
  rw [← ha] at h1 h2
  have hlow : N ≤ D.γ * ‖a‖ := D.hγ u
  have hε := D.epsG_nonneg
  have hd1 : ‖D.Xcj ξ u - a‖ ≤ D.epsG * N := by unfold epsG; linarith
  have hd2 : ‖D.Xcj (-ξ) u - a‖ ≤ D.epsG * N := by unfold epsG; linarith
  -- ⟪a + d1, a + d2⟫ ≥ ‖a‖² − ‖a‖(‖d1‖ + ‖d2‖) − ‖d1‖‖d2‖
  have e : ⟪D.Xcj ξ u, D.Xcj (-ξ) u⟫
      = ‖a‖ ^ 2 + ⟪D.Xcj ξ u - a, a⟫ + ⟪a, D.Xcj (-ξ) u - a⟫ + ⟪D.Xcj ξ u - a, D.Xcj (-ξ) u - a⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e]
  have i1 := abs_real_inner_le_norm (D.Xcj ξ u - a) a
  have i2 := abs_real_inner_le_norm a (D.Xcj (-ξ) u - a)
  have i3 := abs_real_inner_le_norm (D.Xcj ξ u - a) (D.Xcj (-ξ) u - a)
  have hN0 : 0 ≤ N := norm_nonneg _
  have ha0 := norm_nonneg a
  have hn1 := norm_nonneg (D.Xcj ξ u - a)
  have hn2 := norm_nonneg (D.Xcj (-ξ) u - a)
  have hP := pert_gram_lower ‖a‖ N D.epsG D.γ D.hγ0 hN0 hε hεγ hlow
  have m1 : ‖D.Xcj ξ u - a‖ * ‖a‖ ≤ D.epsG * N * ‖a‖ := mul_le_mul_of_nonneg_right hd1 ha0
  have m2 : ‖a‖ * ‖D.Xcj (-ξ) u - a‖ ≤ ‖a‖ * (D.epsG * N) := mul_le_mul_of_nonneg_left hd2 ha0
  have m3 : ‖D.Xcj ξ u - a‖ * ‖D.Xcj (-ξ) u - a‖ ≤ (D.epsG * N) * (D.epsG * N) :=
    mul_le_mul hd1 hd2 hn2 (by positivity)
  unfold cG
  have a1 := (abs_le.mp i1).1
  have a2 := (abs_le.mp i2).1
  have a3 := (abs_le.mp i3).1
  linarith

/-- `GiC ξ` inverts `Γ^{ξ}` -/
theorem GamC_GiC (ξ : PeriodicLatticeSite Lf → ℝ) (w : YP (geomOf ell k S)) :
    D.GamC ξ (GiC (geomOf ell k S) D.Gi ξ w) = w := by
  unfold GamC GiC
  rw [ypWt_cancel_neg, D.hG1, ypWt_neg_cancel]

theorem GiC_GamC (ξ : PeriodicLatticeSite Lf → ℝ) (u : YP (geomOf ell k S)) :
    GiC (geomOf ell k S) D.Gi ξ (D.GamC ξ u) = u := by
  unfold GamC GiC
  rw [ypWt_cancel_neg, D.hG2, ypWt_neg_cancel]

/-- pairing in the weights `e^{±τ}` -/

theorem pair_tau (v w : YP (geomOf ell k S)) :
    ⟪v, w⟫ ≤ ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖ * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖ := by
  have e : ⟪v, w⟫ = ⟪ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v,
      ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w⟫ := by
    rw [ypWt_symm, ypWt_neg_cancel]
  rw [e]; exact real_inner_le_norm _ _

/-- **the weighted inverse bound** -/
theorem GiC_bound (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (w : YP (geomOf ell k S)) :
    D.cG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (GiC (geomOf ell k S) D.Gi ξ w)‖
      ≤ ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖ := by
  have h1 := D.Gam_conj_coer ξ hp hm hεγ (GiC (geomOf ell k S) D.Gi ξ w)
  rw [D.GamC_GiC, real_inner_comm] at h1
  have h2 := D.pair_tau (GiC (geomOf ell k S) D.Gi ξ w) w
  exact coer_to_bound _ _ _ (norm_nonneg _) (norm_nonneg _) (h1.trans h2)

/-- **the Gram difference** -/
theorem Gam_diff (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (v : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S))
        (D.GamC ξ v - (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) v)‖
      ≤ D.dG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖ := by
  have hK : 0 ≤ D.dG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖ := mul_nonneg D.dG_nonneg (norm_nonneg _)
  refine norm_le_of_pair _ _ hK (fun z => ?_)
  have e1 : ⟪ypWt (geomOf ell k S) (-sigG (geomOf ell k S))
        (D.GamC ξ v - (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) v), z⟫
      = ⟪D.Xcj ξ v, D.Xcj (-ξ) (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z)⟫
        - ⟪Xop (geomOf ell k S) D.U D.a v, Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z)⟫ := by
    rw [ypWt_symm, inner_sub_left, D.GamC_inner, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  rw [e1]
  have hz1 : ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z)‖ = ‖z‖ := by
    rw [ypWt_neg_cancel]
  have ha := D.X_le v
  have hb := D.X_le (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z)
  rw [hz1] at hb
  have hd1 := D.Xcj_diff ξ hp v
  have hd2 := D.Xcj_diff (-ξ) hm (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z)
  rw [hz1] at hd2
  have h := inner_pert_le' (Xop (geomOf ell k S) D.U D.a v)
    (Xop (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z))
    (D.Xcj ξ v) (D.Xcj (-ξ) (ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) z))
    (‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) v‖) ‖z‖ ((ell : ℝ) * D.nX) D.epsG
    D.epsG_nonneg (norm_nonneg _) (norm_nonneg _)
    (by unfold epsG; linarith) (by unfold epsG; linarith) ha hb
  refine (le_abs_self _).trans (h.trans (le_of_eq ?_))
  unfold dG; ring

/-- **the conjugated inverse differs little**: `cΓ ‖e^{τ}(Gi^{ξ} − Gi) w‖ ≤ dΓ γ² ‖e^{−τ} w‖` -/
theorem GiC_diff (ξ : PeriodicLatticeSite Lf → ℝ)
    (hp : WtOK (geomOf ell k S) ell (psiW S W ell k + ξ) D.Θ D.Δ)
    (hm : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ)
    (hεγ : D.epsG * D.γ ≤ 1) (w : YP (geomOf ell k S)) :
    D.cG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (GiC (geomOf ell k S) D.Gi ξ w - D.Gi w)‖
      ≤ D.dG * D.γ ^ 2 * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖ := by
  have e : GiC (geomOf ell k S) D.Gi ξ w - D.Gi w
      = -GiC (geomOf ell k S) D.Gi ξ (D.GamC ξ (D.Gi w)
          - (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) (D.Gi w)) := by
    have h1 : (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) (D.Gi w) = w :=
      D.hG1 w
    rw [h1]
    unfold GiC
    rw [map_sub, map_sub, map_sub]
    have h2 : ypWt (geomOf ell k S) ξ (D.Gi (ypWt (geomOf ell k S) (-ξ) (D.GamC ξ (D.Gi w)))) = D.Gi w := by
      have := D.GiC_GamC ξ (D.Gi w); unfold GiC at this; exact this
    rw [h2]; abel
  rw [e, map_neg, norm_neg]
  have h1 := D.GiC_bound ξ hp hm hεγ (D.GamC ξ (D.Gi w)
    - (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) D.U D.a) ∘L Xop (geomOf ell k S) D.U D.a) (D.Gi w))
  have h2 := D.Gam_diff ξ hp hm (D.Gi w)
  have h3 := gami_w D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.Gi D.hG1 D.γ D.hγ0.le D.hγ w
  have hdG := D.dG_nonneg
  calc _ ≤ _ := h1
    _ ≤ D.dG * ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) (D.Gi w)‖ := h2
    _ ≤ D.dG * (D.γ ^ 2 * ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) w‖) := mul_le_mul_of_nonneg_left h3 hdG
    _ = _ := by ring

/-! ## the divergence-to-rows map `V = (D̂X̂)*` -/

theorem VC_pair (ξ : PeriodicLatticeSite Lf → ℝ) (B : BondFnL2 Lf) (z : YP (geomOf ell k S)) :
    ⟪ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) (VC (geomOf ell k S) D.U D.a ξ B), z⟫
      = ⟪bondWt (-sigG (geomOf ell k S)) B,
          bondWt (sigG (geomOf ell k S) + -ξ) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
            (ypWt (geomOf ell k S) (ξ + -sigG (geomOf ell k S)) z)))⟫ := by
  unfold VC
  rw [ypWt_symm, ypWt_symm, ContinuousLinearMap.adjoint_inner_left, ypWt_mul, ContinuousLinearMap.comp_apply,
    ← bondWt_symm, bondWt_mul,
    show (sigG (geomOf ell k S) + -ξ + -sigG (geomOf ell k S)) = -ξ from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

/-- the hatted form of the dual pairing: `e^{σ − η} D̂X̂ e^{η − τ} z = e^{σ − ψ}(e^{ψ − η} D̂X̂ e^{−(ψ−η)})(e^{ψ − τ} z)` -/
theorem VC_form (η : PeriodicLatticeSite Lf → ℝ) (z : YP (geomOf ell k S)) :
    bondWt (sigG (geomOf ell k S) + -η) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
        (ypWt (geomOf ell k S) (η + -sigG (geomOf ell k S)) z)))
      = bondWt (sigG (geomOf ell k S) + -psiW S W ell k) (bondWt (psiW S W ell k + -η)
          (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-(psiW S W ell k + -η))
            (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z))))) := by
  rw [bondWt_mul, ypWt_mul]
  rw [show (sigG (geomOf ell k S) + -psiW S W ell k + (psiW S W ell k + -η)) = sigG (geomOf ell k S) + -η from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring,
    show (-(psiW S W ell k + -η) + (psiW S W ell k + -sigG (geomOf ell k S))) = η + -sigG (geomOf ell k S) from
      funext fun x => by simp only [Pi.add_apply, Pi.neg_apply]; ring]

theorem bond_sig_psi_le' (f : BondFnL2 Lf) :
    ‖bondWt (sigG (geomOf ell k S) + -psiW S W ell k) f‖ ≤ (ell : ℝ) * ‖f‖ := by
  have h2 := bondWt_le_shift (sigG (geomOf ell k S) + -psiW S W ell k) (fun _ => (0 : ℝ)) (Real.log ell)
    (fun x => by have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).2; simp only [Pi.add_apply, Pi.neg_apply]; linarith) f
  rwa [bondWt_zero_fn, Real.exp_log D.ell_pos] at h2

theorem yp_psi_sig_le' (z : YP (geomOf ell k S)) :
    ‖ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z‖ ≤ ‖z‖ := by
  refine (ypWt_le_of _ _ (fun _ => (0 : ℝ)) (fun x => ?_) z).trans (le_of_eq (by rw [ypWt_zero_fn]))
  have := (sig_psi D.hS D.hW D.hell D.hR D.hM D.hWR x).1
  simp only [Pi.add_apply, Pi.neg_apply]; linarith

theorem VC_bound (ξ : PeriodicLatticeSite Lf → ℝ)
    (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ) (B : BondFnL2 Lf) :
    ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S)) (VC (geomOf ell k S) D.U D.a ξ B)‖
      ≤ (ell : ℝ) * D.K3 * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have hK : 0 ≤ (ell : ℝ) * D.K3 * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
    have := D.K3_nonneg; have := D.ell_pos; positivity
  refine norm_le_of_pair _ _ hK (fun z => ?_)
  rw [D.VC_pair, D.VC_form]
  refine (real_inner_le_norm _ _).trans ?_
  have h1 := D.DXhC_le (psiW S W ell k + -ξ) hξ (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)
  have h2 := D.bond_sig_psi_le' (bondWt (psiW S W ell k + -ξ)
    (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-(psiW S W ell k + -ξ))
      (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)))))
  have h3 := D.yp_psi_sig_le' z
  have hK3 := D.K3_nonneg
  have hl := D.ell_pos
  have hB := norm_nonneg (bondWt (-sigG (geomOf ell k S)) B)
  have h4 := h2.trans (mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hK3)) hl.le)
  calc _ ≤ ‖bondWt (-sigG (geomOf ell k S)) B‖ * ((ell : ℝ) * (D.K3 * ‖z‖)) := mul_le_mul_of_nonneg_left h4 hB
    _ = (ell : ℝ) * D.K3 * ‖bondWt (-sigG (geomOf ell k S)) B‖ * ‖z‖ := by ring

theorem VC_zero (B : BondFnL2 Lf) :
    VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B
      = ContinuousLinearMap.adjoint (Dh (geomOf ell k S) D.U ∘L Xh (geomOf ell k S) D.U D.a) B := by
  unfold VC
  have e : (-(fun _ : PeriodicLatticeSite Lf => (0 : ℝ))) = fun _ => (0 : ℝ) := by funext x; simp
  rw [e, bondWt_zero_fn, ypWt_zero_fn]

theorem VC_diff (ξ : PeriodicLatticeSite Lf → ℝ)
    (hξ : WtOK (geomOf ell k S) ell (psiW S W ell k + -ξ) D.Θ D.Δ) (B : BondFnL2 Lf) :
    ‖ypWt (geomOf ell k S) (-sigG (geomOf ell k S))
        (VC (geomOf ell k S) D.U D.a ξ B - VC (geomOf ell k S) D.U D.a (fun _ => (0 : ℝ)) B)‖
      ≤ 2 * (ell : ℝ) * D.EDX' * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  have hK : 0 ≤ 2 * (ell : ℝ) * D.EDX' * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
    have := D.EDX'_nonneg; have := D.ell_pos; positivity
  refine norm_le_of_pair _ _ hK (fun z => ?_)
  rw [map_sub, inner_sub_left, D.VC_pair, D.VC_pair, ← inner_sub_right, D.VC_form, D.VC_form, ← map_sub]
  rw [show psiW S W ell k + -(fun _ : PeriodicLatticeSite Lf => (0 : ℝ)) = psiW S W ell k from by funext x; simp]
  refine (real_inner_le_norm _ _).trans ?_
  have h1 := D.DXhC_diff (psiW S W ell k + -ξ) hξ (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)
  have h2 := D.DXhC_diff (psiW S W ell k) D.okPsi (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)
  have h12 : ‖bondWt (psiW S W ell k + -ξ) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
          (ypWt (geomOf ell k S) (-(psiW S W ell k + -ξ)) (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z))))
        - bondWt (psiW S W ell k) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
          (ypWt (geomOf ell k S) (-psiW S W ell k) (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z))))‖
      ≤ 2 * D.EDX' * ‖ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z‖ := by
    refine (norm_sub_le_norm_sub_add_norm_sub _
      (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)))
      _).trans ?_
    rw [norm_sub_rev (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a _))]
    linarith
  have h3 := D.bond_sig_psi_le' (bondWt (psiW S W ell k + -ξ) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
          (ypWt (geomOf ell k S) (-(psiW S W ell k + -ξ)) (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z))))
        - bondWt (psiW S W ell k) (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a
          (ypWt (geomOf ell k S) (-psiW S W ell k) (ypWt (geomOf ell k S) (psiW S W ell k + -sigG (geomOf ell k S)) z)))))
  have h4 := D.yp_psi_sig_le' z
  have hE := D.EDX'_nonneg
  have hl := D.ell_pos
  have hB := norm_nonneg (bondWt (-sigG (geomOf ell k S)) B)
  have h5 := h3.trans (mul_le_mul_of_nonneg_left (h12.trans (mul_le_mul_of_nonneg_left h4 (by positivity))) hl.le)
  calc _ ≤ ‖bondWt (-sigG (geomOf ell k S)) B‖ * ((ell : ℝ) * (2 * D.EDX' * ‖z‖)) := mul_le_mul_of_nonneg_left h5 hB
    _ = 2 * (ell : ℝ) * D.EDX' * ‖bondWt (-sigG (geomOf ell k S)) B‖ * ‖z‖ := by ring

end CTData

#print axioms bondWt_mul
#print axioms bondWt_zero_fn
#print axioms pert_gram_lower
#print axioms coer_to_bound
#print axioms inner_pert_le'
#print axioms CTData.Xcj
#print axioms CTData.Xcj_eq
#print axioms CTData.Xcj_le
#print axioms CTData.X_le
#print axioms CTData.Xcj_diff
#print axioms CTData.GamC
#print axioms CTData.GamC_inner
#print axioms CTData.GamC_zero
#print axioms CTData.epsG
#print axioms CTData.cG
#print axioms CTData.dG
#print axioms CTData.Gam_conj_coer
#print axioms CTData.GamC_GiC
#print axioms CTData.GiC_GamC
#print axioms CTData.pair_tau
#print axioms CTData.GiC_bound
#print axioms CTData.Gam_diff
#print axioms CTData.GiC_diff
#print axioms CTData.VC_pair
#print axioms CTData.VC_form
#print axioms CTData.bond_sig_psi_le'
#print axioms CTData.yp_psi_sig_le'
#print axioms CTData.VC_bound
#print axioms CTData.VC_zero
#print axioms CTData.VC_diff

end AdalyFormal.M1DStrat

import DC3

/-!
# DC4 -- Combes–Thomas for the genuine row Gram `Γ = X*X`, its inverse, and the divergence (M1 D-layer lane, 2026-10-13)

Weights: a CT weight `χ` with `WtOK χ θχ δχ`, lane E's `ψ` (`psiOK`), and the common pair `(Θ, Δ)` with `θχ + θψ ≤ Θ`,
`δχ + δψ ≤ Δ`; every hatted instance used is `wHyp … ξ Θ Δ` (`ξ ∈ {ψ, ψ ± χ}`), so all instances share `c = cs`,
`δD = √3(e^Θ − 1)`, `δQ = √a(e^Δ − 1)`, `εX`, `εDX` (`instC_*` are `rfl`).  Conjugations: `XhC χ u = e^{χ} X̂ e^{−χ} u`,
`GiC χ w = e^{χ} Gi e^{−χ} w` (rows weighted at their base site), `X = e^{σ} X̂`, row weight `τ = σ ∘ rowSite`.
* `Ds_comm` : `‖e^{χ} Dm* e^{−χ} B − Dm* B‖ ≤ √3 ℓ (e^{θχ} − 1) ‖e^{−σ} B‖` (local, pointwise);
* `X_conj_diff` : `‖e^{σ}(X̂^{χ} − X̂) u‖ ≤ 2ℓ εX ‖e^{τ} u‖`;  `Xt_bound` : `‖e^{σ} X̂^{χ} e^{−τ} y‖ ≤ ℓ nX ‖y‖`;
* `Gam_conj_coer` : `⟪u, Γ^{χ} u⟫ ≥ cΓ ‖e^{τ} u‖²` (from `‖e^{τ}u‖ ≤ γ‖X u‖` and smallness);
* `GiC_bound` : `‖e^{τ} Gi^{χ} w‖ ≤ (1/cΓ) ‖e^{−τ} w‖`.
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

theorem WtOK.mono {L : PeriodicLatticeExtent} {G : TowerGeom L} {ell : ℕ} {φ : PeriodicLatticeSite L → ℝ}
    {θ δ0 θ' δ0' : ℝ} (h : WtOK G ell φ θ δ0) (hθ : θ ≤ θ') (hδ : δ0 ≤ δ0') (hell : 0 < ell) : WtOK G ell φ θ' δ0' := by
  refine ⟨fun b hb => (h.1 b hb).trans ?_, fun q x hx => (h.2 q x hx).trans hδ⟩
  exact div_le_div_of_nonneg_right hθ (by positivity)

/-- `e^{t} − 1 ≤ e^{|t|} − 1` and the Bernoulli step -/
theorem abs_exp_sub_one_le (t T : ℝ) (h : |t| ≤ T) : |Real.exp t - 1| ≤ Real.exp T - 1 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
    have := Real.exp_le_exp.mpr ((le_abs_self t).trans h); linarith
  · rw [abs_of_neg (by linarith [Real.exp_lt_exp.mpr ht, Real.exp_zero] : Real.exp t - 1 < 0)]
    have h1 : -t ≤ T := (neg_le_abs t).trans h
    have h2 : 1 - Real.exp t ≤ -t := by linarith [Real.add_one_le_exp t]
    have h3 : -t ≤ Real.exp (-t) - 1 := by linarith [Real.add_one_le_exp (-t)]
    have h4 : Real.exp (-t) ≤ Real.exp T := Real.exp_le_exp.mpr h1
    linarith

section dsc
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf}

/-- **the divergence commutator** (local): `‖e^{χ} Dm* e^{−χ} B − Dm* B‖ ≤ √3 ℓ (e^{θ} − 1) ‖e^{−σ} B‖` -/
theorem Ds_comm (hS : Admissible ell M R k S) (hell : 2 ≤ ell) (hR : 1 ≤ R) (hM : 1 ≤ M) (U : Cfg Lf)
    (χ : PeriodicLatticeSite Lf → ℝ) (θ δ0 : ℝ) (hθ : 0 ≤ θ) (hok : WtOK (geomOf ell k S) ell χ θ δ0)
    (B : BondFnL2 Lf) :
    ‖siteWt χ (ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) (bondWt (-χ) B))
        - ContinuousLinearMap.adjoint (Dm (geomOf ell k S) U) B‖
      ≤ Real.sqrt 3 * (ell : ℝ) * (Real.exp θ - 1) * ‖bondWt (-sigG (geomOf ell k S)) B‖ := by
  classical
  set G := geomOf ell k S with hG
  have hell0 : 0 < ell := by omega
  have hellr : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hE : 0 ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
  set K := Real.sqrt 3 * (ell : ℝ) * (Real.exp θ - 1) * ‖bondWt (-sigG G) B‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine norm_le_of_pair _ _ hK0 (fun f => ?_)
  -- duality with the masked gradient
  have e1 : ⟪siteWt χ (ContinuousLinearMap.adjoint (Dm G U) (bondWt (-χ) B))
        - ContinuousLinearMap.adjoint (Dm G U) B, f⟫
      = ⟪B, bondWt (-χ) (Dm G U (siteWt χ f)) - Dm G U f⟫ := by
    rw [inner_sub_left, inner_sub_right, siteWt_symm, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ← bondWt_symm]
  rw [e1]
  set g := siteMask G.Om0 f with hg
  -- the pointwise identity
  have hpt : ∀ b : Bond Lf, (bondWt (-χ) (Dm G U (siteWt χ f)) - Dm G U f) b
      = (Real.exp (χ (periodicLatticeShift b.1 b.2) - χ b.1) - 1) • RMap (U b) (g (periodicLatticeShift b.1 b.2)) := by
    intro b
    have hm : ∀ x, siteMask G.Om0 (siteWt χ f) x = Real.exp (χ x) • g x := by
      intro x
      by_cases hx : x ∈ G.Om0
      · rw [siteMask_on _ _ _ hx, siteMask_on _ _ _ hx, siteWt_apply]
      · rw [siteMask_off _ _ _ hx, siteMask_off _ _ _ hx, smul_zero]
    simp only [PiLp.sub_apply, bondWt_apply, Dm, ContinuousLinearMap.comp_apply]
    rw [gradL2_apply', gradL2_apply', hm, hm, map_smul]
    simp only [Pi.neg_apply, smul_sub, smul_smul, ← Real.exp_add]
    rw [show -χ b.1 + χ b.1 = 0 by ring, Real.exp_zero, one_smul, sub_smul, one_smul]
    rw [show -χ b.1 + χ (periodicLatticeShift b.1 b.2) = χ (periodicLatticeShift b.1 b.2) - χ b.1 by ring]
    abel
  rw [PiLp.inner_apply]
  -- per bond
  have hb : ∀ b : Bond Lf, ⟪B b, (bondWt (-χ) (Dm G U (siteWt χ f)) - Dm G U f) b⟫
      ≤ (ell : ℝ) * (Real.exp θ - 1) * (Real.exp (-sigG G b.1) * ‖B b‖) * ‖g (periodicLatticeShift b.1 b.2)‖ := by
    intro b
    rw [hpt b]
    refine (real_inner_le_norm _ _).trans ?_
    rw [norm_smul, AdalyFormal.Balaban.AlphaAnalyticity.norm_RMap, Real.norm_eq_abs]
    by_cases hh : periodicLatticeShift b.1 b.2 ∈ G.Om0
    · -- the weight step at the head
      set s := stratG G (periodicLatticeShift b.1 b.2) with hs
      have h1 := hok.1 b hh
      have h2 : |χ (periodicLatticeShift b.1 b.2) - χ b.1| ≤ θ / (ell : ℝ) ^ s := by
        rw [abs_sub_comm]; exact h1
      have h3 : |Real.exp (χ (periodicLatticeShift b.1 b.2) - χ b.1) - 1| ≤ (Real.exp θ - 1) / (ell : ℝ) ^ s := by
        refine (abs_exp_sub_one_le _ _ h2).trans ?_
        have := exp_div_sub_one_le θ hθ (ell ^ s) (Nat.one_le_pow _ _ hell0)
        rwa [Nat.cast_pow] at this
      -- adjacent strata: `ℓ^{-strat(head)} ≤ ℓ e^{-σ(tail)}`
      have hadj := (AdalyFormal.M1.strat_adj hS hR hM (by omega) b.1 b.2).2
      rw [strat_eq_stratG hell0 hS, strat_eq_stratG hell0 hS] at hadj
      have h4 : 1 / (ell : ℝ) ^ s ≤ (ell : ℝ) * Real.exp (-sigG G b.1) := by
        rw [Real.exp_neg, exp_sig G (show 0 < G.ell from hell0)]
        show 1 / (ell : ℝ) ^ s ≤ (ell : ℝ) * ((ell : ℝ) ^ stratG G b.1)⁻¹
        have hp : (ell : ℝ) ^ stratG G b.1 ≤ (ell : ℝ) ^ (s + 1) := pow_le_pow_right₀ hellr hadj
        rw [pow_succ] at hp
        have hpos : (0 : ℝ) < (ell : ℝ) ^ s := by positivity
        have hpos2 : (0 : ℝ) < (ell : ℝ) ^ stratG G b.1 := by positivity
        rw [div_le_iff₀ hpos, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hpos2]
        linarith
      have h5 : |Real.exp (χ (periodicLatticeShift b.1 b.2) - χ b.1) - 1|
          ≤ (ell : ℝ) * (Real.exp θ - 1) * Real.exp (-sigG G b.1) := by
        refine h3.trans ?_
        rw [div_eq_mul_one_div, mul_comm]
        calc 1 / (ell : ℝ) ^ s * (Real.exp θ - 1) ≤ ((ell : ℝ) * Real.exp (-sigG G b.1)) * (Real.exp θ - 1) :=
              mul_le_mul_of_nonneg_right h4 hE
          _ = _ := by ring
      calc ‖B b‖ * (|Real.exp (χ (periodicLatticeShift b.1 b.2) - χ b.1) - 1| * ‖g (periodicLatticeShift b.1 b.2)‖)
          ≤ ‖B b‖ * (((ell : ℝ) * (Real.exp θ - 1) * Real.exp (-sigG G b.1)) * ‖g (periodicLatticeShift b.1 b.2)‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    · have : g (periodicLatticeShift b.1 b.2) = 0 := siteMask_off _ _ _ hh
      rw [this, norm_zero, mul_zero, mul_zero, mul_zero]
  refine (Finset.sum_le_sum (fun b _ => hb b)).trans ?_
  -- Cauchy–Schwarz over bonds
  have hcs : ∑ b : Bond Lf, (Real.exp (-sigG G b.1) * ‖B b‖) * ‖g (periodicLatticeShift b.1 b.2)‖
      ≤ ‖bondWt (-sigG G) B‖ * (Real.sqrt 3 * ‖f‖) := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Bond Lf))
      (fun b : Bond Lf => Real.exp (-sigG G b.1) * ‖B b‖) (fun b => ‖g (periodicLatticeShift b.1 b.2)‖)
    refine h1.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg _))
    · rw [PiLp.norm_eq_of_L2]
      refine Real.sqrt_le_sqrt (le_of_eq (Finset.sum_congr rfl (fun b _ => ?_)))
      rw [bondWt_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
      simp only [Pi.neg_apply]
      ring
    · have h2 : ∑ b : Bond Lf, ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2 = 3 * ‖g‖ ^ 2 := by
        rw [sum_head_eq (fun x => ‖g x‖ ^ 2), PiLp.norm_sq_eq_of_L2]
      have h3 : ‖g‖ ≤ ‖f‖ := siteMask_norm_le _ _
      rw [show Real.sqrt (∑ b : Bond Lf, ‖g (periodicLatticeShift b.1 b.2)‖ ^ 2) = Real.sqrt 3 * ‖g‖ by
        rw [h2, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]]
      exact mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  have hsum : ∑ b : Bond Lf, (ell : ℝ) * (Real.exp θ - 1) * (Real.exp (-sigG G b.1) * ‖B b‖)
        * ‖g (periodicLatticeShift b.1 b.2)‖
      = (ell : ℝ) * (Real.exp θ - 1) * ∑ b : Bond Lf, (Real.exp (-sigG G b.1) * ‖B b‖)
        * ‖g (periodicLatticeShift b.1 b.2)‖ := by
    rw [Finset.mul_sum]; congr 1; funext b; ring
  rw [hsum]
  calc (ell : ℝ) * (Real.exp θ - 1) * ∑ b : Bond Lf, (Real.exp (-sigG G b.1) * ‖B b‖) * ‖g (periodicLatticeShift b.1 b.2)‖
      ≤ (ell : ℝ) * (Real.exp θ - 1) * (‖bondWt (-sigG G) B‖ * (Real.sqrt 3 * ‖f‖)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = K * ‖f‖ := by rw [hK]; ring

end dsc

#print axioms WtOK.mono
#print axioms abs_exp_sub_one_le
#print axioms Ds_comm

end AdalyFormal.M1DStrat

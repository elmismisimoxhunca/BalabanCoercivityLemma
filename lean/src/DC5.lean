import DC4

/-!
# DC5 -- Combes–Thomas for the genuine `Γ = X*X`, `Γ⁻¹`, and the gauge-fixing divergence `T` (M1 D-layer lane, 2026-10-13)

Setting (`CTSet`): an admissible tower, lane E's `HatPack U a cs`, the CT weight `χ` (`WtOK χ θχ δχ`, `θχ, δχ ≥ 0`), lane E's
`ψ`, a common pair `(Θ, Δ) ≥ (θχ + θψ, δχ + δψ)` with the hatted smallness at `(Θ, Δ)`; all hatted instances are
`inst ξ := wHyp … ξ Θ Δ` (`ξ ∈ {ψ, ψ+χ, ψ−χ}`) and share `c = cs`, `δD`, `δQ`, `εX`, `εDX`.
Genuine objects: `X = Xop = LinvP QpP*` (`= e^{σ} X̂`), `Γ = X*X` with two-sided inverse `Gi`, the row bound
`‖e^{τ} u‖ ≤ γ ‖X u‖` (`τ = σ ∘ rowSite`), `T = Tfull = R D*`.
* `X_conj_diff` : `‖e^{σ}(X̂^{χ} − X̂) u‖ ≤ 2ℓ εX ‖e^{τ} u‖`;  `Xt_bound` : `‖e^{σ} X̂^{ξ} e^{−τ} y‖ ≤ ℓ nX ‖y‖` (`ξ = 0, χ`);
* `Gam_conj_coer` : `⟪u, Γ^{χ} u⟫ ≥ cΓ ‖e^{τ} u‖²`;  `GiC_bound` : `‖e^{τ} Gi^{χ} w‖ ≤ ‖e^{−τ} w‖ / cΓ`;
* `GiC_diff` : `‖e^{τ}(Gi^{χ} − Gi) w‖ ≤ (dΓ γ² / cΓ) ‖e^{−τ} w‖`, `dΓ = 4 ℓ² εX nX`;
* `V_bound`, `V_diff` : the divergence-to-rows map `V = (D̂ X̂)*` and its CT difference, `e^{−τ}`-weighted, by duality;
* **`T_conj_diff`** : `‖e^{χ} T e^{−χ} B − T B‖ ≤ δT ‖e^{−σ} B‖` with an explicit `δT` (k-free).
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

/-- conjugations by a site weight -/
noncomputable def XhC (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ξ : PeriodicLatticeSite L → ℝ) (u : YP G) : SiteL2 L :=
  siteWt ξ (Xh G U a (ypWt G (-ξ) u))

noncomputable def GiC (G : TowerGeom L) (Gi : YP G →L[ℝ] YP G) (ξ : PeriodicLatticeSite L → ℝ) (w : YP G) : YP G :=
  ypWt G ξ (Gi (ypWt G (-ξ) w))

noncomputable def VC (G : TowerGeom L) (U : Cfg L) (a : ℝ) (ξ : PeriodicLatticeSite L → ℝ) (B : BondFnL2 L) : YP G :=
  ypWt G ξ (ContinuousLinearMap.adjoint (Dh G U ∘L Xh G U a) (bondWt (-ξ) B))

theorem ypWt_neg_add (G : TowerGeom L) (φ χ : PeriodicLatticeSite L → ℝ) (u : YP G) :
    ypWt G (-(φ + χ)) (ypWt G φ u) = ypWt G (-χ) u := by
  have e : (-(φ + χ) + φ) = -χ := by funext x; simp only [Pi.add_apply, Pi.neg_apply]; ring
  rw [ypWt_mul, e]

theorem XhC_shift (G : TowerGeom L) (U : Cfg L) (a : ℝ) (φ χ : PeriodicLatticeSite L → ℝ) (u : YP G) :
    siteWt φ (XhC G U a χ u) = XhC G U a (φ + χ) (ypWt G φ u) := by
  unfold XhC
  rw [siteWt_mul, ypWt_neg_add]

theorem XhC_zero (G : TowerGeom L) (U : Cfg L) (a : ℝ) (u : YP G) : XhC G U a (fun _ => (0 : ℝ)) u = Xh G U a u := by
  unfold XhC
  have e : (-(fun _ : PeriodicLatticeSite L => (0 : ℝ))) = fun _ => (0 : ℝ) := by funext x; simp
  rw [e, ypWt_zero_fn, siteWt_zero_fn]

end gen

#print axioms XhC
#print axioms GiC
#print axioms VC
#print axioms ypWt_neg_add
#print axioms XhC_shift
#print axioms XhC_zero

/-- **the Combes–Thomas data** at one configuration (all hypotheses gauge-invariant or about the tower) -/
structure CTData {Lf : PeriodicLatticeExtent} (ell M R k : ℕ) (S : Tower Lf) (W : ℕ) where
  hS : Admissible ell M R k S
  hW : 1 ≤ W
  hell : 2 ≤ ell
  hR : 1 ≤ R
  hM : 1 ≤ M
  hWR : W ≤ R * M * ell
  U : Cfg Lf
  a : ℝ
  cs : ℝ
  hp : HatPack (ell := ell) (k := k) (S := S) (W := W) U a cs
  χ : PeriodicLatticeSite Lf → ℝ
  θχ : ℝ
  δχ : ℝ
  hθχ : 0 ≤ θχ
  hδχ : 0 ≤ δχ
  hχ : WtOK (geomOf ell k S) ell χ θχ δχ
  Θ : ℝ
  Δ : ℝ
  hΘ : θχ + 2 * (ell : ℝ) ^ 2 * Real.log ell / W ≤ Θ
  hΔ : δχ + 3 * (ell : ℝ) * Real.log ell / W ≤ Δ
  hsm : 24 * ((Real.sqrt 3 * (Real.exp Θ - 1)) ^ 2 + 1 * (Real.sqrt a * (Real.exp Δ - 1)) ^ 2) ≤ cs
  hsmD : 4 * (Real.sqrt 3 * (Real.exp Θ - 1)) ^ 2 ≤ cs
  Gi : YP (geomOf ell k S) →L[ℝ] YP (geomOf ell k S)
  hG1 : ∀ u, (ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) (Gi u) = u
  hG2 : ∀ u, Gi ((ContinuousLinearMap.adjoint (Xop (geomOf ell k S) U a) ∘L Xop (geomOf ell k S) U a) u) = u
  γ : ℝ
  hγ0 : 0 < γ
  hγ : ∀ u, ‖ypWt (geomOf ell k S) (sigG (geomOf ell k S)) u‖ ≤ γ * ‖Xop (geomOf ell k S) U a u‖

namespace CTData
variable {Lf : PeriodicLatticeExtent} {ell M R k : ℕ} {S : Tower Lf} {W : ℕ} (D : CTData ell M R k S W)
include D

theorem θψ_nonneg : 0 ≤ 2 * (ell : ℝ) ^ 2 * Real.log ell / W := theta_nonneg D.hS D.hW D.hell D.hR D.hM D.hWR
theorem δψ_nonneg : 0 ≤ 3 * (ell : ℝ) * Real.log ell / W := delta0_nonneg D.hS D.hW D.hell D.hR D.hM D.hWR
theorem Θ0 : 0 ≤ D.Θ := by linarith [D.θψ_nonneg, D.hΘ, D.hθχ]
theorem Δ0 : 0 ≤ D.Δ := by linarith [D.δψ_nonneg, D.hΔ, D.hδχ]

theorem okPsi : WtOK (geomOf ell k S) ell (psiW S W ell k) D.Θ D.Δ :=
  (psiOK D.hS D.hW D.hell D.hR D.hM D.hWR).mono (by linarith [D.hΘ, D.hθχ]) (by linarith [D.hΔ, D.hδχ])
    (by have := D.hell; omega)

theorem okPlus : WtOK (geomOf ell k S) ell (psiW S W ell k + D.χ) D.Θ D.Δ :=
  ((psiOK D.hS D.hW D.hell D.hR D.hM D.hWR).add D.hχ).mono (by linarith [D.hΘ]) (by linarith [D.hΔ])
    (by have := D.hell; omega)

theorem okMinus : WtOK (geomOf ell k S) ell (psiW S W ell k - D.χ) D.Θ D.Δ :=
  ((psiOK D.hS D.hW D.hell D.hR D.hM D.hWR).sub D.hχ).mono (by linarith [D.hΘ]) (by linarith [D.hΔ])
    (by have := D.hell; omega)

/-- the hatted instance at a weight satisfying `WtOK … Θ Δ` -/
noncomputable def iW (ξ : PeriodicLatticeSite Lf → ℝ) (hξ : WtOK (geomOf ell k S) ell ξ D.Θ D.Δ) :
    SiteHyp (SiteL2 Lf) (BondFnL2 Lf) (YP (geomOf ell k S)) :=
  wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD

/-- the common constants -/
noncomputable def q : ℝ := Real.sqrt (max D.a 1)
noncomputable def dD : ℝ := Real.sqrt 3 * (Real.exp D.Θ - 1)
noncomputable def dQ : ℝ := Real.sqrt D.a * (Real.exp D.Δ - 1)
noncomputable def nX : ℝ := (4 / D.cs) * (D.q + D.dQ)
noncomputable def K3 : ℝ := (Real.sqrt (12 / D.cs) + D.dD * (4 / D.cs)) * (D.q + D.dQ)
noncomputable def EX : ℝ :=
  (4 / D.cs) * D.dQ + (4 / D.cs) * D.dD * (D.q / Real.sqrt D.cs)
    + (Real.sqrt (48 / D.cs) * D.dD + (8 / D.cs) * D.dD ^ 2 + (4 / D.cs) * 1 * (2 * D.q * D.dQ + D.dQ ^ 2)) * (D.q / D.cs)
noncomputable def EDX : ℝ :=
  Real.sqrt (12 / D.cs) * D.dQ + Real.sqrt (12 / D.cs) * D.dD * (D.q / Real.sqrt D.cs)
    + (Real.sqrt 24 * D.dD + 2 * Real.sqrt (12 / D.cs) * D.dD ^ 2
      + Real.sqrt (12 / D.cs) * 1 * (2 * D.q * D.dQ + D.dQ ^ 2)) * (D.q / D.cs)
noncomputable def EDX' : ℝ := D.dD * D.nX + D.EDX

theorem iW_c (ξ) (hξ) : (D.iW ξ hξ).c = D.cs := rfl
theorem iW_δD (ξ) (hξ) : (D.iW ξ hξ).δD = D.dD := rfl
theorem iW_δQ (ξ) (hξ) : (D.iW ξ hξ).δQ = D.dQ := rfl
theorem iW_m (ξ) (hξ) : (D.iW ξ hξ).m = 1 := rfl
theorem iW_epsX (ξ) (hξ) : (D.iW ξ hξ).epsX D.q = D.EX := by
  unfold SiteHyp.epsX SiteHyp.K0
  rw [D.iW_c, D.iW_δD, D.iW_δQ, D.iW_m]; rfl
theorem iW_epsDX (ξ) (hξ) : (D.iW ξ hξ).epsDX D.q = D.EDX := by
  unfold SiteHyp.epsDX SiteHyp.K1
  rw [D.iW_c, D.iW_δD, D.iW_δQ, D.iW_m]; rfl

theorem q_nonneg : 0 ≤ D.q := Real.sqrt_nonneg _
theorem hq : ‖Qh (geomOf ell k S) D.U D.a‖ ≤ D.q := Qh_opnorm D.hS D.hell D.U D.a D.hp.ha
theorem cs_pos : 0 < D.cs := D.hp.hcs
theorem dD_nonneg : 0 ≤ D.dD := mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp D.Θ, D.Θ0])
theorem dQ_nonneg : 0 ≤ D.dQ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [Real.add_one_le_exp D.Δ, D.Δ0])
theorem nX_nonneg : 0 ≤ D.nX := mul_nonneg (div_nonneg (by norm_num) D.cs_pos.le) (add_nonneg D.q_nonneg D.dQ_nonneg)
theorem K3_nonneg : 0 ≤ D.K3 :=
  mul_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg D.dD_nonneg (div_nonneg (by norm_num) D.cs_pos.le)))
    (add_nonneg D.q_nonneg D.dQ_nonneg)
theorem EX_nonneg : 0 ≤ D.EX := by
  have := D.cs_pos; have := D.dD_nonneg; have := D.dQ_nonneg; have := D.q_nonneg
  unfold EX; positivity
theorem EDX_nonneg : 0 ≤ D.EDX := by
  have := D.cs_pos; have := D.dD_nonneg; have := D.dQ_nonneg; have := D.q_nonneg
  unfold EDX; positivity
theorem EDX'_nonneg : 0 ≤ D.EDX' := add_nonneg (mul_nonneg D.dD_nonneg D.nX_nonneg) D.EDX_nonneg

/-! ## conjugated `X̂` -/

/-- `‖e^{ξ} X̂ e^{−ξ} u‖ ≤ nX ‖u‖` for any admissible weight -/
theorem XhC_le (ξ) (hξ : WtOK (geomOf ell k S) ell ξ D.Θ D.Δ) (u : YP (geomOf ell k S)) :
    ‖XhC (geomOf ell k S) D.U D.a ξ u‖ ≤ D.nX * ‖u‖ := by
  have h := g_X D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD D.q D.hq u
  have hc : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).c = D.cs := rfl
  have hQ : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).δQ = D.dQ := rfl
  rw [hc, hQ] at h
  refine h.trans (le_of_eq ?_)
  unfold nX; ring

theorem XhC_diff (ξ) (hξ : WtOK (geomOf ell k S) ell ξ D.Θ D.Δ) (u : YP (geomOf ell k S)) :
    ‖XhC (geomOf ell k S) D.U D.a ξ u - Xh (geomOf ell k S) D.U D.a u‖ ≤ D.EX * ‖u‖ := by
  have h := (g_Xd D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD D.q
    D.q_nonneg D.hq u).1
  have he := D.iW_epsX ξ hξ
  unfold iW at he
  rw [he] at h
  exact h

theorem DXhC_le (ξ) (hξ : WtOK (geomOf ell k S) ell ξ D.Θ D.Δ) (u : YP (geomOf ell k S)) :
    ‖bondWt ξ (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-ξ) u)))‖ ≤ D.K3 * ‖u‖ := by
  have h := g_DX D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD D.q D.hq u
  have hc : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).c = D.cs := rfl
  have hQ : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).δQ = D.dQ := rfl
  have hD : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).δD = D.dD := rfl
  rw [hc, hQ, hD] at h
  exact h

theorem DXhC_diff (ξ) (hξ : WtOK (geomOf ell k S) ell ξ D.Θ D.Δ) (u : YP (geomOf ell k S)) :
    ‖bondWt ξ (Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a (ypWt (geomOf ell k S) (-ξ) u)))
        - Dh (geomOf ell k S) D.U (Xh (geomOf ell k S) D.U D.a u)‖ ≤ D.EDX' * ‖u‖ := by
  have h := g_DXd D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD D.q
    D.q_nonneg D.hq u
  have hc : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).c = D.cs := rfl
  have hQ : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).δQ = D.dQ := rfl
  have hD : (wHyp D.hS D.hW D.hell D.hR D.hM D.hWR D.U D.a D.cs D.hp ξ D.Θ D.Δ D.Θ0 D.Δ0 hξ D.hsm D.hsmD).δD = D.dD := rfl
  have he := D.iW_epsDX ξ hξ
  unfold iW at he
  rw [hc, hQ, hD, he] at h
  refine h.trans (le_of_eq ?_)
  unfold EDX' nX; ring

end CTData

end AdalyFormal.M1DStrat

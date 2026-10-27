import DLR31

/-!
# DL32 -- the genuine `G⁻¹` (full tower) as an instance of the abstract `GinvHyp`, and the operator identity

* `ginvHypOf` : from any `GamHyp G0` carrying the genuine site operators (`G0.D = D_U`, `G0.ωE = bondWP φ`, `G0.ωS = siteWP φ`),
  the genuine bond-level data `C = curlC U`, `Δ' = DpOp U`, `Qb = QfullOf`, `M = a ℓ^k`, weights `plaqWP φ`, `fspWP φ`, and the
  commutator constants of DL25/DL26/DL31.
* `MassFull_eq` : `Q* a Q = (a ℓ^k) Qb* Qb` on the full tower (every `BIdx` index sits at level `k`).
* **`Ginv_eq_full`** : `(ginvHypOf ..).Ginv = GinvFull := Δ_π + Tfull*Tfull + MassFull` — the abstract `G⁻¹` of DL16 IS the
  genuine operator (via `Wop_eq_W`, `Tfull_eq_T`, `Delta_decomp`, `MassFull_eq`).
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace AdalyFormal.DLayer

open scoped RealInnerProductSpace
open AdalyFormal.Target.ClayStatement
open AdalyFormal.IngredientFamilyR2
open AdalyFormal.Balaban.CovariantOperators (SuTwo BondFnL2)
open AdalyFormal.Balaban.CovariantHjMinimizer (PlaqFnL2)
open AdalyFormal.SliceCoerc (coarseC Qtop GF)
open AdalyFormal.StatementLane (scaleUp)
open AdalyFormal.NonflatJet (rhoOf)
open AdalyFormal.BondComposite (TowerClass bidx_level)

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

/-- the multiplicity constant of the bond footprint -/
noncomputable def multB : ℝ := Real.sqrt ((3 * (Rfoot ell k / ell ^ k + 1) ^ 3 : ℕ))

/-- **the genuine `G⁻¹` data as a `GinvHyp`** -/
noncomputable def ginvHypOf (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a)
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ)
    (G0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
    (hD : G0.D = gradL2 U) (hωE : G0.ωE = bondWP φ) (hωS : G0.ωS = siteWP φ)
    (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2) :
    GinvHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu))
      (PlaqFnL2 (scaleUp ell k Lu)) (FSp (GF ell k Lu)) where
  toGamHyp := G0
  C := curlC U
  Dp := DpOp U
  Qb := (bondSectorOf (GF ell k Lu) U).Qfull
  M := a * (ell : ℝ) ^ k
  ωP := plaqWP φ
  ωB := fspWP ell k Lu φ
  δC := 6 * (Real.exp θ' - 1)
  κ := 6 * q0
  δK := 6 * q0 * (Real.exp (2 * θ') - 1)
  ν := 816 * α₀
  δν := 816 * α₀ * (Real.exp (2 * θ') - 1)
  δB := qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * multB ell k
  hM := by positivity
  hδC := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp θ' - 1 := by linarith [Real.add_one_le_exp θ']
    positivity
  hκ := by positivity
  hδK := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
    positivity
  hν := by positivity
  hδν := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ Real.exp (2 * θ') - 1 := by linarith [Real.add_one_le_exp (2 * θ')]
    positivity
  hδB := by
    have hθ : 0 ≤ θ' := le_trans (abs_nonneg _) (hφ (fun _ => 0) 0)
    have : 0 ≤ (Rfoot ell k : ℝ) * θ' := by positivity
    have : 0 ≤ Real.exp (Rfoot ell k * θ') - 1 := by linarith [Real.add_one_le_exp ((Rfoot ell k : ℝ) * θ')]
    have := qbM_nonneg ell k ε
    have : 0 ≤ multB ell k := Real.sqrt_nonneg _
    positivity
  hCp := by rw [hωE]; exact curl_cjp_norm U φ θ' hφ
  hCm := by rw [hωE]; exact curl_cjm_norm U φ θ' hφ
  hKn := by rw [hD]; exact curv_norm U q0 hq0 hplaq
  hKp := by rw [hωS, hD]; exact curv_cjp_norm U φ θ' hφ q0 hq0 hplaq
  hKm := by rw [hωS, hD]; exact curv_cjm_norm U φ θ' hφ q0 hq0 hplaq
  hDpn := DpOp_norm U hα₀ hpl
  hDpp := by rw [hωE]; exact DpOp_cjp_norm U hα₀ hpl φ θ' hφ
  hDpm := by rw [hωE]; exact DpOp_cjm_norm U hα₀ hpl φ θ' hφ
  hDps := DpOp_symm U
  hBp := by rw [hωE]; exact Qfull_cjp_norm ell k Lu hell U ε hreg hcl hε0 hsm φ θ' hφ
  hBm := by rw [hωE]; exact Qfull_cjm_norm ell k Lu hell U ε hreg hcl hε0 hsm φ θ' hφ

/-- the mass weights are constant on the full tower -/
theorem diagW_massW (a : ℝ) (u : FSp (GF ell k Lu)) :
    diagW (GF ell k Lu) (massW (GF ell k Lu) a) u = (a * (ell : ℝ) ^ k) • u := by
  refine PiLp.ext (fun p => ?_)
  have hk := bidx_level ell k Lu p
  show (massW (GF ell k Lu) a p) • u p = (a * (ell : ℝ) ^ k) • u p
  unfold massW
  have e : ((GF ell k Lu).ell : ℝ) ^ (p.1 : ℕ) = (ell : ℝ) ^ k := by
    show (ell : ℝ) ^ (p.1 : ℕ) = (ell : ℝ) ^ k
    rw [hk]
  rw [e]

theorem MassFull_eq (U : Cfg (scaleUp ell k Lu)) (a : ℝ) :
    MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) U)
      = (a * (ell : ℝ) ^ k) • (ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull
          ∘L (bondSectorOf (GF ell k Lu) U).Qfull) := by
  ext1 x
  simp only [MassFull, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, diagW_massW, map_smul]

/-- the genuine `G⁻¹` on all fine bonds -/
noncomputable def GinvFull (U : Cfg (scaleUp ell k Lu)) (a : ℝ) :
    BondFnL2 (scaleUp ell k Lu) →L[ℝ] BondFnL2 (scaleUp ell k Lu) :=
  DpiFull (GF ell k Lu) U a + ContinuousLinearMap.adjoint (Tfull (GF ell k Lu) U) ∘L Tfull (GF ell k Lu) U
    + MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) U)

/-- **the abstract `G⁻¹` of DL16 IS the genuine operator** -/
theorem Ginv_eq_full (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ)
    (G0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
    (hD : G0.D = gradL2 U) (hQ : G0.Qp = Qtop (GF ell k Lu) U) (hL : G0.Linv = Gp (GF ell k Lu) U a)
    (hωE : G0.ωE = bondWP φ) (hωS : G0.ωS = siteWP φ)
    (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2) :
    (ginvHypOf ell k Lu hell U a ha φ θ' hφ G0 hD hωE hωS q0 hq0 hplaq α₀ hα₀ hpl ε hreg hcl hε0 hsm).Ginv
      = GinvFull ell k Lu U a := by
  have hW := Wop_eq_W ell k Lu U a hu G0 hD hQ hL
  have hT := Tfull_eq_T ell k Lu U a hu G0 hD hQ hL
  unfold GinvHyp.Ginv GinvFull DpiFull
  rw [MassFull_eq, Delta_decomp]
  show ContinuousLinearMap.adjoint G0.W ∘L (ContinuousLinearMap.adjoint (curlC U) ∘L curlC U + DpOp U) ∘L G0.W
      + ContinuousLinearMap.adjoint G0.T ∘L G0.T
      + (a * (ell : ℝ) ^ k) • (ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull
          ∘L (bondSectorOf (GF ell k Lu) U).Qfull) = _
  rw [← hW, ← hT]

end

#print axioms ginvHypOf
#print axioms diagW_massW
#print axioms MassFull_eq
#print axioms Ginv_eq_full

end AdalyFormal.DLayer

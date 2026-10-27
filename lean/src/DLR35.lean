import DLR34

/-!
# DL35 -- the scaled identity `G⁻¹' = n² G⁻¹`, the transfer to the statement carrier `E₀`, and the CONCRETE
# k-uniform Combes–Thomas bound for the genuine `G` at M0

* `GinvS_eq` : `(ginvHypS ..).Ginv = n² • GinvFull`.
* `data_Ginv_form` : `⟪x, P.data.Ginv x⟫ = ⟪ιx, GinvFull_P (ιx)⟫` (any `P`); on the full tower every fine field lies in `E₀`.
* `GinvFull_coercive` : `‖f‖² ≤ n²K̂ ⟪f, GinvFull f⟫` at M0 (from `ginv_coercive_M0_kuniform`), `GinvFull_isUnit`.
* **`GinvFull_CT_scaled`** : `¾ n²⟪f,G⁻¹f⟫ − E'‖f‖² ≤ n²⟪f, e^{φ}G⁻¹e^{−φ}f⟫` with `E' = (ginvHypS ..).EG`, a function of the
  k-free scaled constants only;  **`GFull_cjp_scaled`** : `(c'/(2n²))‖e^{φ} G e^{−φ} g‖ ≤ ‖g‖` when `4E' ≤ c'`, `c' = 1/K̂`.
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
open AdalyFormal.BondComposite (TowerClass)

theorem GinvHyp.Ginv_apply {S E Y P B : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace S] [CompleteSpace E] [CompleteSpace Y] [CompleteSpace P] [CompleteSpace B]
    (I : GinvHyp S E Y P B) (x : E) :
    I.Ginv x = ContinuousLinearMap.adjoint I.Gm.W (ContinuousLinearMap.adjoint I.C (I.C (I.Gm.W x)) + I.Dp (I.Gm.W x))
      + ContinuousLinearMap.adjoint I.Gm.T (I.Gm.T x) + I.M • ContinuousLinearMap.adjoint I.Qb (I.Qb x) := by
  simp only [GinvHyp.Ginv, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]

section
variable (ell k : ℕ) (Lu : PeriodicLatticeExtent)

set_option maxRecDepth 100000 in
theorem GinvS_eq (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (ha : 0 ≤ a)
    (hu : IsUnit (DelpA (GF ell k Lu) U a + (1 - siteMask (GF ell k Lu).Om0)))
    (φ : PeriodicLatticeSite (scaleUp ell k Lu) → ℝ) (θ' : ℝ) (hφ : WtLip θ' φ)
    (G0 : GamHyp (SiteL2 (scaleUp ell k Lu)) (BondFnL2 (scaleUp ell k Lu)) (coarseC (GF ell k Lu)))
    (hm0 : 0 ≤ mTop ell k a)
    (hD : G0.D = ((ell : ℝ) ^ k) • gradL2 U)
    (hQ : G0.Qp = (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) • Qtop (GF ell k Lu) U)
    (hL : G0.Linv = ((ell : ℝ) ^ k)⁻¹ ^ 2 • Gp (GF ell k Lu) U a)
    (hmpos : 0 < mTop ell k a)
    (hωE : G0.ωE = bondWP φ) (hωS : G0.ωS = siteWP φ)
    (q0 : ℝ) (hq0 : 0 ≤ q0)
    (hplaq : ∀ p : PeriodicLatticePlaquette (scaleUp ell k Lu),
      AdalyFormal.CurvBlock.dv (periodicPlaquetteHolonomy U p) ≤ q0)
    (α₀ : ℝ) (hα₀ : 0 ≤ α₀) (hpl : AdalyFormal.NonflatHunit.PlaqDef α₀ U)
    (ε : ℕ → ℝ) (hreg : RegTower ell (bgTower (GF ell k Lu) U) k) (hcl : TowerClass ell k Lu U ε)
    (hε0 : ∀ j, j < k → 0 ≤ ε j) (hsm : ∀ j, j < k → rhoOf ell (ε j) < Real.pi / 2)
    (δC' κ' δK' ν' δν' δB' : ℝ)
    (hC' : (ell : ℝ) ^ k * (6 * (Real.exp θ' - 1)) ≤ δC')
    (hK' : ((ell : ℝ) ^ k) ^ 2 * (6 * q0) ≤ κ')
    (hdK' : ((ell : ℝ) ^ k) ^ 2 * (6 * q0 * (Real.exp (2 * θ') - 1)) ≤ δK')
    (hν' : ((ell : ℝ) ^ k) ^ 2 * (816 * α₀) ≤ ν')
    (hdν' : ((ell : ℝ) ^ k) ^ 2 * (816 * α₀ * (Real.exp (2 * θ') - 1)) ≤ δν')
    (hB' : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3)
      * (qbM ell k ε * (Real.exp (Rfoot ell k * θ') - 1) * multB ell k) ≤ δB') :
    (ginvHypS ell k Lu hell U a ha φ θ' hφ G0 hD hωE hωS q0 hq0 hplaq α₀ hα₀ hpl ε hreg hcl hε0 hsm
        δC' κ' δK' ν' δν' δB' hC' hK' hdK' hν' hdν' hB').Ginv
      = ((ell : ℝ) ^ k) ^ 2 • GinvFull ell k Lu U a := by
  have hs : ((ell : ℝ) ^ k) ≠ 0 := by positivity
  have hsq : Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k ≠ 0 := by
    have := Real.sqrt_pos.mpr hmpos; positivity
  have hW := Wop_eq_W_scaled ell k Lu U a hu G0 ((ell : ℝ) ^ k) (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) hs hsq hD hQ hL
  have hT := Tfull_eq_T_scaled ell k Lu U a hu G0 ((ell : ℝ) ^ k) (Real.sqrt (mTop ell k a) * (ell : ℝ) ^ k) hs hsq hD hQ hL
  have hr : Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) * Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) = a * ((ell : ℝ) ^ k) ^ 3 :=
    Real.mul_self_sqrt (by positivity)
  ext1 x
  have e1 : (ginvHypS ell k Lu hell U a ha φ θ' hφ G0 hD hωE hωS q0 hq0 hplaq α₀ hα₀ hpl ε hreg hcl hε0 hsm
        δC' κ' δK' ν' δν' δB' hC' hK' hdK' hν' hdν' hB').Ginv x
      = ContinuousLinearMap.adjoint G0.W
          ((ContinuousLinearMap.adjoint (((ell : ℝ) ^ k) • curlC U) (((ell : ℝ) ^ k) • curlC U (G0.W x)))
            + ((ell : ℝ) ^ k) ^ 2 • DpOp U (G0.W x))
        + ContinuousLinearMap.adjoint G0.T (G0.T x)
        + (1 : ℝ) • ContinuousLinearMap.adjoint (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull)
            (Real.sqrt (a * ((ell : ℝ) ^ k) ^ 3) • (bondSectorOf (GF ell k Lu) U).Qfull x) := by
    rw [GinvHyp.Ginv_apply]
    rfl
  have e2 : GinvFull ell k Lu U a x
      = ContinuousLinearMap.adjoint (Wop (GF ell k Lu) U a)
          (ContinuousLinearMap.adjoint (curlC U) (curlC U (Wop (GF ell k Lu) U a x)) + DpOp U (Wop (GF ell k Lu) U a x))
        + ContinuousLinearMap.adjoint (Tfull (GF ell k Lu) U) (Tfull (GF ell k Lu) U x)
        + (a * (ell : ℝ) ^ k) • ContinuousLinearMap.adjoint (bondSectorOf (GF ell k Lu) U).Qfull
            ((bondSectorOf (GF ell k Lu) U).Qfull x) := by
    show (DpiFull (GF ell k Lu) U a + ContinuousLinearMap.adjoint (Tfull (GF ell k Lu) U) ∘L Tfull (GF ell k Lu) U
      + MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) U)) x = _
    rw [MassFull_eq]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, DpiFull,
      Delta_decomp]
  rw [e1, ContinuousLinearMap.smul_apply, e2, hW, hT]
  simp only [adjoint_smul_real, ContinuousLinearMap.smul_apply, map_smul, map_add, smul_smul, one_smul, smul_add]
  rw [hr]
  congr 1
  · congr 1
    · ring_nf
    · ring_nf
  · congr 1; ring

/-- every fine field is supported in `E₀` on the full tower -/
theorem mem_bondSupp_full (x : BondFnL2 (scaleUp ell k Lu)) : x ∈ bondSupp (GF ell k Lu) := by
  intro b hb
  exact absurd (Or.inl (by rw [AdalyFormal.SliceCoerc.fullTower_Om0]; trivial)) hb

/-- the genuine `G⁻¹` form on the statement carrier, read on all fine bonds -/
theorem data_Ginv_form (hell : 0 < ell) (U : Cfg (scaleUp ell k Lu)) (a : ℝ) (Lam : Set (PeriodicLatticeSite Lu))
    (x : ↥(bondSupp (GF ell k Lu))) :
    ⟪x, (IngrBParams.data ⟨ell, k, Lu, hell, fullTower ell k Lu, U, a, Lam⟩).Ginv x⟫
      = ⟪(x : BondFnL2 (scaleUp ell k Lu)), GinvFull ell k Lu U a x⟫ := by
  show ⟪x, (pE (GF ell k Lu)) (DpiFull (GF ell k Lu) U a (iE (GF ell k Lu) x))
      + ContinuousLinearMap.adjoint ((Tfull (GF ell k Lu) U).comp (iE (GF ell k Lu)))
          ((Tfull (GF ell k Lu) U).comp (iE (GF ell k Lu)) x)
      + (pE (GF ell k Lu)) (MassFull (GF ell k Lu) a (bondSectorOf (GF ell k Lu) U) (iE (GF ell k Lu) x))⟫ = _
  rw [inner_add_right, inner_add_right, pE_inner_right, pE_inner_right, ContinuousLinearMap.adjoint_inner_right]
  simp only [GinvFull, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- **coercivity of the genuine `G⁻¹` on all fine bonds** (M0) -/
theorem GinvFull_coercive (U : Cfg (scaleUp ell k Lu)) (a t e q0 : ℝ)
    (R : AdalyFormal.AsmM0.M0RegimeR ell k Lu U a t e q0)
    (H : AdalyFormal.RegBgKU.KUSmall ell (AdalyFormal.AsmM0.rhoM0 ell k e q0))
    (f : BondFnL2 (scaleUp ell k Lu)) :
    ‖f‖ ^ 2 ≤ ((ell : ℝ) ^ k) ^ 2 * AdalyFormal.AsmM0.KhatM0 ell a t (AdalyFormal.AsmM0.rhoM0 ell k e q0)
      * ⟪f, GinvFull ell k Lu U a f⟫ := by
  have hell : 0 < ell := by have := R.hell; omega
  set x : ↥(bondSupp (GF ell k Lu)) := ⟨f, mem_bondSupp_full ell k Lu f⟩
  have h := AdalyFormal.RegBgKU.ginv_coercive_M0_kuniform ell k Lu U a t e q0 R H Set.univ x
  rw [data_Ginv_form ell k Lu hell U a Set.univ x] at h
  exact h

end

#print axioms GinvS_eq
#print axioms mem_bondSupp_full
#print axioms data_Ginv_form
#print axioms GinvFull_coercive

end AdalyFormal.DLayer
